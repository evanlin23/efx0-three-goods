"""Python wrapper for the C brute force bf.c."""
import subprocess, os
BF = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bf")
def bf_output(inst, s, o, conv):
    base, pick, marked = s
    lines = [f"{inst.n} {inst.m}"] + [" ".join(map(str, row)) for row in inst.v]
    lines += [" ".join(map(str, base)), " ".join(map(str, pick)), " ".join(str(int(x)) for x in marked)]
    lines += [f"{-1 if o is None else o} {1 if conv == 'bundle' else 0}"]
    out = subprocess.run([BF], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout.split("\n")
    return out[0].startswith("SAT"), int(out[1])
