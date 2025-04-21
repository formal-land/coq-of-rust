from subprocess import Popen, PIPE
import threading
import sys

global lines
lines = []
global errorlines
errorlines = []
global lock
lock = 0

p = Popen("make", stdout=PIPE, stderr=PIPE, shell=True)


class tout(threading.Thread):
    def __init__(self, thread_name, thread_ID):
        threading.Thread.__init__(self)
        self.thread_name = thread_name
        self.thread_ID = thread_ID

    def run(self):
        global lines
        global lock
        while True:
            l = p.stdout.readline()
            if not l:
                break
            line = l.decode("utf-8")[:-1]
            lines += [line]
            print(line)
        lock += 1
        check_warnings()


class terr(threading.Thread):
    def __init__(self, thread_name, thread_ID):
        threading.Thread.__init__(self)
        self.thread_name = thread_name
        self.thread_ID = thread_ID

    def run(self):
        global lines
        global errorlines
        global lock
        while True:
            l = p.stderr.readline()
            if not l:
                break
            line = l.decode("utf-8")[:-1]
            lines += [line]
            errorlines += [line]
            print(line)
        lock += 1
        check_warnings()


ttout = tout("ttout", 1000)
tterr = terr("tterr", 2000)
ttout.start()
tterr.start()


def check_warnings():
    if lock < 2:
        return
    else:
        print("Checking warnings...")
        for line in errorlines:
            if line.startswith("Warning: "):
                print("Warnings detected from coqc. Abort.", file=sys.stderr)
                exit(1)
        print("Check complete, no warnings detected")


while p.wait(timeout=7200):
    exit(p.returncode)
