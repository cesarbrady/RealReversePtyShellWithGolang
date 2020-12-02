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
	// 定义要开启的程序
	c := exec.Command("bash")

	// 让它在pty当中运行
	ptmx, err := pty.Start(c)
	if err != nil {
		_, fn, line, _ := runtime.Caller(0)
		panic(filepath.Base(fn) + ":" + strconv.Itoa(line-2) + " >> " + err.Error() + " >> " + fmtDebugStack(string(debug.Stack())))
	}
	defer func() { _ = ptmx.Close() }()

	// 设置一个初始的pty的窗口大小
	pty.Setsize(ptmx, &pty.Winsize{
		Rows: 30,
		Cols: 120,
	})

	// 连接到服务器
	k := kcpConnect("127.0.0.1", 12345, "demo key", "demo salt")

	var ptmxExit bool

	// 一直循环读取pty的输出，并把输出发送给服务器，如果读取出错，则认为命令执行结束了
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

	// 循环从服务器读取输入，然后输出到pty当中
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

		// 如果是需要重新设定仿真终端的窗口大小，则设置它
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
	// 在服务端，监听端口
	k := <-kcpListen("0.0.0.0", 12345, "demo key", "demo salt").accept()

	// 设置当前pty的模式为raw模式
	oldState, err := term.MakeRaw(int(os.Stdin.Fd()))
	if err != nil {
		panic(err)
	}
	// 在退出函数的时候把当前pty恢复为之前的模式
	defer func() { _ = term.Restore(int(os.Stdin.Fd()), oldState) }()

	stdinBufChan := make(chan []byte)
	var ptmxExit bool

	// 为了能从stdin不阻塞，所以这里使用了chan来实现
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

	// 从stdin读取键盘输入，发送给客户端
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

	// 监听当前pty大小改变的信号，如果发生改变，发送给客户端
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

	// 循环读取从客户端发来的消息，打印到当前pty的标准输出
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
