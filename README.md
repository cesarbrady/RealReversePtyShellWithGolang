# RealReversePtyShellWithGolang

I have seen many projects, such as the dashboard of kubernetes, and gotty, they can use a web browser to connect to the emulation terminal of the server, just like connecting to the server through the ssh service.

Out of curiosity, I wrote a demo in golang to achieve a similar function.

Its characteristics are

1. Use udp connection instead of tcp
2. udp data is all encrypted
3. The reversed shell is a real pty shell. For example, the experience of using vim on it is the same as operating locally
4. The window size of pty that reversed can be dynamically change

```go
package main

import (
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"runtime"
	"runtime/debug"
	"strconv"
	"syscall"
	"time"

	"github.com/creack/pty"
	terminal "github.com/wayneashleyberry/terminal-dimensions"
	"golang.org/x/term"
)

func client() {
	// define the program to run
	c := exec.Command("bash")

	// make it run inside pty
	ptmx, err := pty.Start(c)
	if err != nil {
		_, fn, line, _ := runtime.Caller(0)
		panic(filepath.Base(fn) + ":" + strconv.Itoa(line-2) + " >> " + err.Error() + " >> " + fmtDebugStack(string(debug.Stack())))
	}
	defer func() { _ = ptmx.Close() }()

	// Set the window size of an initial pty
	pty.Setsize(ptmx, &pty.Winsize{
		Rows: 30,
		Cols: 120,
	})

	// Connect to the server
	k := kcpConnect("127.0.0.1", 12345, "demo key", "demo salt")

	var ptmxExit bool

  // Read the output of pty and send it to the server. If there is an error in reading, the command execution is considered to be over
	go func() {
		for {
			buf := make([]byte, 4096)
			n, err := ptmx.Read(buf)
			if err != nil {
				lg.debug("read error:", err.Error(), err)
				ptmxExit = true
				break
			}
			if try(func() {
				k.send(map[string]string{"data": string(buf[:n])})
			}).Error != nil {
				break
			}
		}
	}()

	// read input from the server, and then write them to pty
	for {
		var buf map[string]string
		if try(func() {
			buf = k.recv(1)
			lg.debug("read from kcp:", buf)
		}).Error != nil {
			break
		}

		if ptmxExit {
			break
		}

		//  If the window size needs to be reset, set it
		if !keyInMap("Rows", buf) {
			_, err := ptmx.Write([]byte(buf["data"]))
			if err != nil {
				break
			}
		} else {
			lg.debug("resize windows size to ", buf)
			pty.Setsize(ptmx, &pty.Winsize{
				Rows: toUint16(buf["Rows"]),
				Cols: toUint16(buf["Cols"]),
			})
		}

	}

	k.send(map[string]string{"end": "true"})
	k.recv(3)
	lg.trace("end")
}

func server() {
	// On the server side, the listening port
	k := <-kcpListen("0.0.0.0", 12345, "demo key", "demo salt").accept()

	// Set the current pty mode to raw mode
	oldState, err := term.MakeRaw(int(os.Stdin.Fd()))
	if err != nil {
		panic(err)
	}
	// Restore the current pty to the previous mode when exiting the function
	defer func() { _ = term.Restore(int(os.Stdin.Fd()), oldState) }()

	stdinBufChan := make(chan []byte)
	var ptmxExit bool

	// In order not to block while read from stdin, chan is used here
	go func() {
		for {
			buf := make([]byte, 4096)
			n, err := os.Stdin.Read(buf)
			if err != nil {
				break
			}
			stdinBufChan <- buf[:n]
			if ptmxExit {
				break
			}
		}
	}()

	// Read input from stdin and send it to the client
	go func() {
		for {
			select {
			case i := <-stdinBufChan:
				if try(func() {
					k.send(map[string]string{"data": string(i)})
				}).Error != nil {
					break
				}
			case <-time.After(1000 * time.Millisecond):
			}
			if ptmxExit {
				break
			}
		}
	}()

	// Listen to the signal of the current pty size change, if it changes, send it to the client
	ch := make(chan os.Signal, 1)
	signal.Notify(ch, syscall.SIGWINCH)
	go func() {
		for range ch {
			x, _ := terminal.Width()
			y, _ := terminal.Height()

			k.send(map[string]string{
				"Rows": toString(y),
				"Cols": toString(x),
			})
		}
	}()
	ch <- syscall.SIGWINCH

	//  Read the message from the client and print it to the standard output of the current pty
	for {
		var buf map[string]string
		if try(func() {
			buf = k.recv()
		}).Error != nil {
			break
		}

		if keyInMap("end", buf) {
			break
		}

		_, err := os.Stdout.Write([]byte(buf["data"]))
		if err != nil {
			break
		}
	}
}

func main() {
	if os.Args[1] == "s" {
		server()
	} else if os.Args[1] == "c" {
		client()
	}
}
```