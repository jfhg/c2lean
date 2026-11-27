#!/usr/bin/env python3
"""Ground truth for the call/recursion programs: fact, addtwice, and quickSort (void, in-place)."""
import ctypes, os, subprocess, sys, tempfile
from llvmlite import binding as llvm

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

llvm.initialize_all_targets(); llvm.initialize_native_asmprinter()
tm = llvm.Target.from_default_triple().create_target_machine()
_tmp = tempfile.TemporaryDirectory(prefix="jit-")
def _ll(c):   # compile C -> ephemeral IR (C is the committed input)
    c = os.path.join(ROOT, c)
    out = os.path.join(_tmp.name, os.path.basename(c)[:-2] + ".ll")
    subprocess.run(["clang", "-O0", "-emit-llvm", "-S", c, "-o", out],
                   check=True)
    return out
mods = [llvm.parse_assembly(open(_ll(c)).read()) for c in
        ("examples/fact.c", "examples/twice.c", "examples/qsort.c")]
for m in mods: m.verify()
ee = llvm.create_mcjit_compiler(mods[0], tm)
for m in mods[1:]: ee.add_module(m)
ee.finalize_object(); ee.run_static_constructors()

fact = ctypes.CFUNCTYPE(ctypes.c_int32, ctypes.c_int32)(ee.get_function_address("fact"))
print("-- fact:", {n: fact(n) for n in range(13)})

addtwice = ctypes.CFUNCTYPE(ctypes.c_int32, ctypes.c_int32, ctypes.c_int32)(
    ee.get_function_address("addtwice"))
print("-- addtwice:", {(a,b): addtwice(a,b) for a,b in [(0,0),(3,4),(100,200),(1000000,1)]})

qs = ctypes.CFUNCTYPE(None, ctypes.POINTER(ctypes.c_int32), ctypes.c_int32, ctypes.c_int32)(
    ee.get_function_address("quickSort"))
CASES = [[5,3,8,1,2],[42],[3,3,3],[9,7,5,3,1,8,6,4,2,0],[1,5],[2,1]]
for arr in CASES:
    buf = (ctypes.c_int32 * len(arr))(*arr)
    qs(buf, 0, len(arr)-1)
    print(f"-- quickSort {arr} -> {list(buf)}")
