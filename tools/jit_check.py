#!/usr/bin/env python3
"""jit_check.py — ground truth from real LLVM (MCJIT).

Usage:  python tools/jit_check.py some.ll ...
(.ll paths are cwd-relative; this is the manual ad-hoc tool —
 jit_gen.py is the automated corpus cross-check.)

JIT-compiles the given modules, calls every defined function with a
standard signed-int32 test vector, and prints the machine-code results as
Lean `example` lines (fuel left as a `FUEL` placeholder — measure it in
Lean, it is program-specific).  These become the cross-check theorems in
C2Lean/LlSpecs.lean: our Lean interpreter must agree with LLVM's compiled
machine code.
"""
import ctypes
import sys
from llvmlite import binding as llvm

M = 2**32

VECS = {
    1: [0, 1, 5, 1000, 100000, 2147483647, 2147483648, 4294967295, 4294967293],
    2: [(0, 5), (5, 0), (7, 7), (4294967295, 0), (0, 4294967295),
        (2147483648, 2147483647), (2147483647, 2147483648)],
    3: [(5, 3, 9), (0, 0, 0), (4294967295, 0, 4294967295),
        (2147483647, 2147483648, 0), (1, 2, 0)],
}

# Per-function overrides: inputs where the C program has no signed-overflow
# UB (e.g. log2ish's `p * 2` overflows for n > 2^30 — UB means the compiled
# code may spin forever, so we must not feed it to MCJIT).
VEC_OVERRIDE = {
    "log2ish": [0, 1, 2, 3, 5, 1000, 1024, 1048576, 1073741824],
    # localarr indexes a[8]: only in-bounds reads are defined behavior
    "localarr": [0, 1, 2, 3, 4, 5, 6, 7],
}

# Functions taking a pointer: (name → array contents). The Lean side seeds
# the SAME contents as initial memory cells at address 0 (see C2Lean/LlMem.lean).
ARRAYS = {
    "arrsum": [3 * i + 1 for i in range(8)],
}
ARRAY_VEC = {
    "arrsum": [(0,), (1,), (3,), (8,)],   # values of n
}

paths = sys.argv[1:] or sys.exit("usage: python tools/jit_check.py FILE.ll ...")
llvm.initialize_all_targets()
llvm.initialize_native_asmprinter()
tm = llvm.Target.from_default_triple().create_target_machine()
mods = []
for i, p in enumerate(paths):
    m = llvm.parse_assembly(open(p).read())
    m.verify()
    if i == 0:
        ee = llvm.create_mcjit_compiler(m, tm)
    else:
        ee.add_module(m)
    mods.append(m)
ee.finalize_object()
ee.run_static_constructors()

def word(x):
    return x & (M - 1)

def signed(x):
    return x - M if x >= 2**31 else x

for m in mods:
  for f in m.functions:
    if f.is_declaration:
        continue
    name = f.name
    nargs = len(list(f.arguments))
    if name in ARRAYS:
        arr = ARRAYS[name]
        buf = (ctypes.c_int32 * len(arr))(*arr)
        cargs = [ctypes.POINTER(ctypes.c_int32)] + [ctypes.c_int32] * (nargs - 1)
        cf = ctypes.CFUNCTYPE(*([ctypes.c_int32] + cargs))(
            ee.get_function_address(name))
        cells = ", ".join(f"({4 * i}, {v})" for i, v in enumerate(arr))
        print(f"-- {name}   (memory: {{{{ cells := [{cells}], next := 1024 }}}})")
        for (n,) in ARRAY_VEC[name]:
            r = cf(buf, n) & (M - 1)
            print(f"example : runFuncM {name}F [0, {n}] FUEL"
                  f" {{ cells := [{cells}], next := 1024 }} = Result.val {r}"
                  f" := by native_decide")
        continue
    vec = VEC_OVERRIDE.get(name)
    if vec is None:
        vec = VECS.get(nargs)
    if vec is None:
        print(f"-- {name}: skipped (no test vector for arity {nargs})")
        continue
    cf = ctypes.CFUNCTYPE(*([ctypes.c_int32] + [ctypes.c_int32] * nargs))(
        ee.get_function_address(name))
    print(f"-- {name}")
    for v in vec:
        args = v if isinstance(v, tuple) else (v,)
        r = cf(*[signed(a) for a in args]) & (M - 1)
        al = ", ".join(str(a) for a in args)
        print(f"example : runFunc {name}F [{al}] FUEL = Result.val {r} := by native_decide")
