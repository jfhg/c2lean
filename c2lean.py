#!/usr/bin/env python3
"""c2lean.py — the C/LLVM frontend: translate C (or LLVM IR) into Lean.

The unit of translation is a LINKED PROJECT: pass every file that must
be seen together (cross-file calls, shared globals) and get exactly one
Lean file.  A single file is a project of one.

    c2lean.py -o combined.lean a.c b.c              # two-file project
    c2lean.py -o fact.lean fact.c                   # project of one
    c2lean.py examples/*.c -o build/C2Lean/Programs.lean   # what `make` does

The output file contains:
  * one `Func` AST per defined function, one `Module` per input file;
  * `projectM` — the static link of all modules (the interpreter's
    universe: cross-file calls resolve through it);
  * `projectG` — initial memory with linker-assigned global addresses;
  * one `def <fn>_cspec_type : Prop` per `//@` spec in the sources.

Inputs are `.c` files (compiled internally with clang — the C source is
the input of record, IR is ephemeral) and/or `.ll` files (hand-written
IR).

Options:
    -o FILE     output file (default: C2Lean/Programs.lean); `-o -`
                writes to a fresh temp dir and prints the path on
                stdout (status messages go to stderr)
    --check     linter mode: validate inputs + verify generated files
                are fresh; write nothing.  Exit 0 = clean, non-zero =
                bad input or stale output.
    -h, --help  show this help

Behavior contract (a trusted translator):
  * Deterministic: same inputs -> byte-identical outputs.
  * Fail-closed: anything outside the supported subset aborts with a
    message on stderr and a non-zero exit code; nothing is guessed.
  * All-or-nothing: either the output is written, or nothing is.

llvmlite gives structured access to functions, blocks, opcodes and
operands; a few things (icmp predicates, branch/phi labels, global
initializers) are only in the instruction text, so those are extracted
by regex from LLVM's own printing of the instruction — never guessed.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
from llvmlite import binding as llvm

OPS = {"add": "add", "sub": "sub", "mul": "mul",
       "and": "and", "or": "or", "xor": "xor",
       "shl": "shl", "lshr": "lshr"}
RELS = {"ult": "ult", "ule": "ule", "ugt": "ugt", "uge": "uge",
        "slt": "slt", "sle": "sle", "sgt": "sgt", "sge": "sge",
        "eq": "eq", "ne": "ne"}

def is_i32(tref):
    return str(tref) == "i32"

def is_i64(tref):
    return str(tref) == "i64"

# i64 arithmetic is tracked mod 2^32: add/sub/mul/and/or/xor are ring
# homomorphisms mod 2^32, so those are ALWAYS faithful; i64 icmp is
# faithful while the compared values are < 2^32 (loop counters below
# 2^31 — and MCJIT cross-checks catch any divergence empirically).
I64_OK = {"add", "sub", "mul", "and", "or", "xor"}

# textual forms (LLVM's own printing — never guessed):
#   %d = alloca i32, align 4          |  %d = alloca [8 x i32], align 4
RE_ALLOCA = re.compile(r"^(%[-\w.]+) = alloca (?:\[([0-9]+) x i32\]|i32|ptr|i[0-9]+\*)(?=[,\s]|$)")
#   %d = load i32, ptr %p, align 4 [, !tbaa ...]
RE_LOAD = re.compile(r"^(%[-\w.]+) = load (?:i32|ptr), ptr (%[-\w.]+|@[-\w.]+|-?\d+)(?=[,\s]|$)")
#   store i32 %v, ptr %p, align 4 [, ...]
RE_STORE = re.compile(r"^store (?:i32|ptr) (%[-\w.]+|@[-\w.]+|-?\d+), ptr (%[-\w.]+|@[-\w.]+|-?\d+)(?=[,\s]|$)")
#   %d = getelementptr [inbounds] [nuw] (i32 | [N x i32]), ptr %base,
#        i64 %idx  |  i64 0, i64 %idx
RE_GEP = re.compile(
    r"^(%[-\w.]+) = getelementptr(?: (?:inbounds|nuw|exact))*"
    r" (?:\[([0-9]+) x i32\]|i32), ptr (%[-\w.]+|@[-\w.]+|-?\d+), "
    r"i(?:32|64) (%[-\w.]+|@[-\w.]+|-?\d+)(?:, i(?:32|64) (%[-\w.]+|@[-\w.]+|-?\d+))?"
    r"(?=[,\s]|$)")
#   %d = sext|zext [nneg] i32 %x to i64  |  %d = trunc [nuw] i64 %x to i32
RE_CAST = re.compile(
    r"^(%[-\w.]+) = (sext|zext|trunc)(?: (?:nuw|nsw|nneg))*"
    r" i(32|64) (%[-\w.]+|@[-\w.]+|-?\d+) to i(32|64)(?=[,\s]|$)")
#   %d = [tail] call i32 @llvm.smin.i32(i32 %a, i32 %b)  (also smax)
#   lowered to icmp + select — semantically identical
RE_SMINMAX = re.compile(
    r"^(%[-\w.]+) = (?:tail )?call i32 @llvm\.s(min|max)\.i32\("
    r"i32 (%[-\w.]+|@[-\w.]+|-?\d+), i32 (%[-\w.]+|@[-\w.]+|-?\d+)\)$")

# Global variables: name -> address, assigned in the pre-pass over all
# files (like a linker laying out .data).  Region: >= 1048576, safely
# above caller arrays (< 1024) and alloca frames (>= 1024).
GLOBALS = {}          # name -> address
GVALUES = []          # (addr, value) for projectG
GLOBAL_BASE = 1048576

RE_GDEF = re.compile(
    r"^@(\w+) = (?:private |dso_local |internal |weak |common |thread_local )*"
    r"global (i32|\[([0-9]+) x i32\]) (.+?)(?:, align [0-9]+)?$", re.M)

def globals_prepass(path, text):
    """Collect global DEFINITIONS across the whole project (pass 1)."""
    global GVALUES
    for m in RE_GDEF.finditer(text):
        name, ty, n, init = m.group(1), m.group(2), m.group(3), m.group(4).strip()
        if name in GLOBALS:
            sys.exit(f"{path}: global `{name}` defined twice (duplicate symbol)")
        if name in {"at", "in", "do", "let", "match", "with", "end", "fun",
                    "have", "show", "where", "then", "forall", "exists",
                    "def", "theorem", "axiom", "instance", "open", "by",
                    "Type", "Prop", "Nat", "Bool", "Mem", "some", "none",
                    "true", "false", "result", "fuel", "m", "cur", "old",
                    "projectM", "projectG"}:
            sys.exit(f"{path}: global name `{name}` collides with a reserved "
                     f"name; rename it in C")
        if ty == "i32":
            if not re.fullmatch(r"-?\d+", init):
                sys.exit(f"{path}: unsupported initializer for @{name}: {init}")
            vals = [int(init)]
        elif init == "zeroinitializer":
            vals = [0] * int(n)
        elif init.startswith("["):
            vals = [int(v) for v in re.findall(r"i32 (-?\d+)", init)]
            if len(vals) != int(n):
                sys.exit(f"{path}: array initializer length mismatch for @{name}")
        else:
            sys.exit(f"{path}: unsupported global initializer for @{name}: {init}")
        addr = GLOBAL_BASE + 4 * len(GVALUES)
        GLOBALS[name] = addr
        GVALUES.extend((addr + 4 * i, v % 2**32) for i, v in enumerate(vals))

def global_ref(tok):
    if tok not in GLOBALS:
        sys.exit(f"reference to undefined global @{tok} "
                 f"(defined in another TU without a linked definition?)")
    return f"(Ll.Operand.imm {GLOBALS[tok]})"

def val_name(o):
    """Name of a non-constant value; clang often emits nameless `%0`-style
    names that llvmlite's `.name` reports as empty — recover from the
    printed form (LLVM's own output, never guessed)."""
    n = o.name
    if n:
        return n
    m = re.search(r"%(\S+?)(?:\s|$)", str(o))
    if not m:
        sys.exit(f"unsupported operand: {o}")
    return m.group(1)

def operand(o):
    if not o.is_constant and str(o).startswith("@"):
        return global_ref(str(o)[1:].split()[0].rstrip(","))
    if o.is_constant:
        v = o.get_constant_value()
        if isinstance(v, str):
            if v in ("null", "zeroinitializer"):
                return "(Ll.Operand.imm 0)"
            sys.exit(f"unsupported constant: {v}")
        return f"(Ll.Operand.imm {v % 2**32})"
    return f'(Ll.Operand.reg "{val_name(o)}")'

def tok_operand(t):
    """Operand from a textual token (used where llvmlite hides structure)."""
    if t.startswith("@"):
        return global_ref(t[1:])
    if t.startswith("%"):
        return f'(Ll.Operand.reg "{t[1:]}")'
    if t == "true":
        return "(Ll.Operand.imm 1)"
    if t == "false":
        return "(Ll.Operand.imm 0)"
    return f"(Ll.Operand.imm {int(t) % 2**32})"

def block_name(b):
    """Block label; numeric names like `1:` come back empty from llvmlite."""
    n = b.name
    if n:
        return n
    m = re.match(r"([-\w.]+):", str(b))
    if not m:
        sys.exit(f"cannot name block: {b}")
    return m.group(1)

def block_names(f):
    """Block labels in order.  llvmlite reports numeric names (`1:`) as
    empty, and `str(block)` omits the label — recover from the printed
    function, where every label starts a line (`LLVM's own output`)."""
    blocks = list(f.blocks)
    if all(b.name for b in blocks):
        return [b.name for b in blocks]
    names = re.findall(r"(?m)^([-\w.]+):", str(f))
    if len(names) == len(blocks) - 1:
        # Anonymous entry block: recover its name from a reference to it
        # (labels appear in `br ... label %X` and phi `[..., %X ]`).
        refs = set(re.findall(r"label %([-\w.]+)", str(f)))
        refs |= set(re.findall(r"\[[^,\]]+, %([-\w.]+) \]", str(f)))
        missing = sorted(r for r in refs if r not in names)
        if not missing:
            names = ["0"] + names  # truly anonymous, never referenced
        elif len(missing) == 1:
            names = [missing[0]] + names
        else:
            sys.exit(f"cannot name entry block of {f.name}")
    if len(names) != len(blocks):
        sys.exit(f"cannot name blocks of {f.name}")
    return names

def convert_function(f):
    params = [val_name(p) for p in f.arguments]
    blocks = []
    for bname, b in zip(block_names(f), f.blocks):
        instrs = []
        term = None
        insts = list(b.instructions)
        for i in insts:
            txt = str(i).strip()
            if i.opcode == "call" and "llvm.lifetime." in txt:
                continue  # lifetime intrinsics: semantically no-ops
            if i.opcode == "ret" and len(list(i.operands)) == 1:
                ops = list(i.operands)
                term = f"(Ll.Term.ret {operand(ops[0])})"
            elif i.opcode == "br":
                labels = re.findall(r"label %([-\w.]+)", txt)
                if txt.startswith("br label"):
                    if len(labels) != 1:
                        sys.exit(f"bad jump: {txt}")
                    term = f"(Ll.Term.jump \"{labels[0]}\")"
                else:
                    cond = list(i.operands)[0]
                    if len(labels) != 2:
                        sys.exit(f"bad conditional br: {txt}")
                    term = (f"(Ll.Term.br {operand(cond)} "
                            f"\"{labels[0]}\" \"{labels[1]}\")")
            elif i.opcode == "br" or i.opcode == "unreachable":
                sys.exit(f"unsupported terminator: {txt}")
            elif i.opcode == "icmp":
                m = re.match(r"%\S+ = icmp (\w+) i(?:32|64)", txt)
                if not m or m.group(1) not in RELS:
                    sys.exit(f"unsupported icmp: {txt}")
                ops = list(i.operands)
                instrs.append(f"  Ll.Instr.icmp Rel.{RELS[m.group(1)]} "
                              f"\"{val_name(i)}\" {operand(ops[0])} {operand(ops[1])}")
            elif i.opcode == "select":
                m = re.match(r"%(?P<d>[\w.]+) = select i1 (?P<c>%[\w.]+|-?\d+|true|false), "
                             r"i32 (?P<a>%[\w.]+|-?\d+), i32 (?P<b>%[\w.]+|-?\d+)$", txt)
                if not m:
                    sys.exit(f"unsupported select: {txt}")
                instrs.append(f'  Ll.Instr.select "{m["d"]}" {tok_operand(m["c"])} '
                              f'{tok_operand(m["a"])} {tok_operand(m["b"])}')
            elif i.opcode == "phi":
                if not re.search(r"= phi (?:i(?:1|32|64)|ptr) ", txt):
                    sys.exit(f"unsupported phi type: {txt}")
                labels = re.findall(r"\[[^,]+, %([-.\w]+) \]", txt)
                ops = list(i.operands)
                if len(labels) != len(ops) or not ops:
                    sys.exit(f"phi parse mismatch: {txt}")
                pairs = ", ".join(f"({operand(o)}, \"{l}\")"
                                  for o, l in zip(ops, labels))
                instrs.append(f"  Ll.Instr.phi \"{val_name(i)}\" [{pairs}]")
            elif i.opcode in OPS:
                if not (is_i32(i.type) or (is_i64(i.type) and i.opcode in I64_OK)):
                    sys.exit(f"{i.opcode} on type {i.type} (only i32, or i64 add/sub/mul/and/or/xor)")
                ops = list(i.operands)
                if len(ops) != 2:
                    sys.exit(f"{i.opcode} with {len(ops)} operands")
                instrs.append(f"  Ll.Instr.bin BinOp.{OPS[i.opcode]} "
                              f"\"{val_name(i)}\" {operand(ops[0])} {operand(ops[1])}")
            elif i.opcode == "alloca":
                m = RE_ALLOCA.match(txt)
                if not m:
                    sys.exit(f"unsupported alloca: {txt}")
                n = int(m.group(2)) if m.group(2) else 1
                instrs.append(f'  Ll.Instr.alloca "{m.group(1)[1:]}" {4 * n}')
            elif i.opcode == "load":
                m = RE_LOAD.match(txt)
                if not m:
                    sys.exit(f"unsupported load: {txt}")
                instrs.append(f'  Ll.Instr.load "{m.group(1)[1:]}" '
                              f'{tok_operand(m.group(2))}')
            elif i.opcode == "store":
                m = RE_STORE.match(txt)
                if not m:
                    sys.exit(f"unsupported store: {txt}")
                instrs.append(f"  Ll.Instr.store {tok_operand(m.group(1))} "
                              f"{tok_operand(m.group(2))}")
            elif i.opcode == "getelementptr":
                m = RE_GEP.match(txt)
                if not m:
                    sys.exit(f"unsupported gep: {txt}")
                if m.group(2) is not None:
                    # array form `gep [N x i32], ptr %p, i64 0, i64 %i`:
                    # first index must be the constant 0
                    if m.group(4) != "0":
                        sys.exit(f"unsupported gep: {txt}")
                    idx = m.group(5)
                else:
                    idx = m.group(4)
                instrs.append(f'  Ll.Instr.gep "{m.group(1)[1:]}" '
                              f'{tok_operand(m.group(3))} {tok_operand(idx)}')
            elif i.opcode in ("sext", "zext", "trunc"):
                m = RE_CAST.match(txt)
                if not m:
                    sys.exit(f"unsupported cast: {txt}")
                d, op, ty, v, ty2 = (m.group(1)[1:], m.group(2), m.group(3),
                                     m.group(4), m.group(5))
                ok = ((op in ("sext", "zext") and ty == "32" and ty2 == "64")
                      or (op == "trunc" and ty == "64" and ty2 == "32"))
                if not ok:
                    sys.exit(f"unsupported cast: {txt}")
                # identity on i32 bit patterns
                instrs.append(f'  Ll.Instr.bin BinOp.add "{d}" '
                              f'{tok_operand(v)} (Ll.Operand.imm 0)')
            elif i.opcode == "call" and RE_SMINMAX.match(txt):
                m = RE_SMINMAX.match(txt)
                d = m.group(1)[1:]
                rel = "slt" if m.group(2) == "min" else "sgt"
                a, b = tok_operand(m.group(3)), tok_operand(m.group(4))
                tmp = f"{d}!cmp"
                instrs.append(f'  Ll.Instr.icmp Rel.{rel} "{tmp}" {a} {b}')
                instrs.append(f'  Ll.Instr.select "{d}" (Ll.Operand.reg "{tmp}")'
                              f' {a} {b}')
            elif i.opcode == "ret":
                term = "(Ll.Term.retv)"   # `ret void`
            elif i.opcode == "call":
                callee = list(i.operands)[-1].name
                if callee.startswith("llvm."):
                    sys.exit(f"unsupported intrinsic call: {txt}")
                args = ", ".join(operand(o) for o in list(i.operands)[:-1])
                if str(i.type) == "void":
                    instrs.append(f'  Ll.Instr.callv "{callee}" [{args}]')
                elif str(i.type) in ("i32", "i64"):
                    instrs.append(f'  Ll.Instr.call "{val_name(i)}" "{callee}" [{args}]')
                else:
                    sys.exit(f"call returning {i.type}: {txt}")
            else:
                sys.exit(f"unsupported instruction: {i.opcode}  ({txt})")
        if term is None:
            sys.exit(f"block {b.name} has no terminator")
        blocks.append((bname, instrs, term))
    return params, blocks

# ---------------------------------------------------------------------------
# Spec extraction: `//@` comments in the matching c/<stem>.c (if present).
# Spec text is spliced VERBATIM into Lean skeletons — no translation to trust.
# ---------------------------------------------------------------------------

RE_SPEC = re.compile(r"//@\s*(requires|ensures|modifies)\s+(.*?)\s*;?\s*$")
RE_FUNC = re.compile(r"^([A-Za-z_]\w*\s+)+\*?\s*(\w+)\s*\(([^)]*)\)\s*\{")

# Spec-language discipline: C variables/params are written `c:<name>` in
# spec text and bound as `c_<name>` in Lean.  Bare names are reserved for
# the spec vocabulary (result, cur, old, library defs).  Consequence:
# binders are never Lean keywords and never shadow the skeleton.

def param_names(arglist, fname):
    arglist = arglist.strip()
    if arglist in ("", "void"):     # `f()` or `f(void)`: no parameters
        return []
    names = []
    for arg in arglist.split(","):
        arg = arg.strip()
        if not arg:
            continue
        if "(" in arg:
            sys.exit(f"{fname}: function-pointer parameter `{arg}` not supported")
        arg = re.sub(r"\[.*?\]", "", arg)   # `int a[10]` -> `int a`
        m = re.findall(r"(\w+)", arg)
        if not m:
            sys.exit(f"{fname}: cannot parse parameter `{arg}`")
        names.append(m[-1])   # last identifier: `int *a`, `int arr[]`
    return names

def parse_c(path):
    """Collect (fname, params, {requires|ensures|modifies}) in source order."""
    specs, pending = [], {}
    for line in open(path):
        m = RE_SPEC.search(line)
        if m:
            key, val = m.group(1), m.group(2)
            pending[key] = (pending.get(key, "") + " " + val).strip()
            continue
        m = RE_FUNC.match(line)
        if m and pending:
            specs.append((m.group(2), param_names(m.group(3), m.group(2)), dict(pending)))
            pending = {}
    if pending:
        sys.exit(f"{path}: spec comment not followed by a parseable function "
                 f"definition (unsupported signature?): {pending}")
    return specs

def emit_specs(out, cpath, mod, specs):
    import os
    names = []
    for fname, params, sp in specs:
        req = sp.get("requires", "True")
        ens = sp.get("ensures", "True")
        # `c:<name>` is the ONLY way spec text refers to C variables:
        for text in (req, ens):
            for p in re.findall(r"c:(\w+)", text):
                if p not in params:
                    sys.exit(f"{fname}: spec refers to `c:{p}` but `{p}` is not a parameter")
        def scope(text):
            return re.sub(r"c:(\w+)", r"c_\1", text)
        req, ens = scope(req), scope(ens)
        # bare C param names are now illegal (they were the ambiguity);
        # spec-vocabulary words stay bare-meaning-vocabulary even when a
        # C parameter shares the name (the parameter is `c:<name>`).
        SPEC_VOCAB = {"result", "fuel", "m", "cur", "old"}
        for p in params:
            if p in SPEC_VOCAB:
                continue
            for name, text in (("requires", req), ("ensures", ens)):
                if re.search(rf"\b{p}\b", text):
                    sys.exit(f"{fname}: {name} uses bare `{p}`; C variables "
                             f"must be written `c:{p}`")
        pl = " ".join("c_" + p for p in params)
        if pl:
            pl = pl + " : Nat"
        args = ", ".join("c_" + p for p in params)
        modif = sp.get("modifies")
        out.append(f"/-- GENERATED from {cpath} by c2lean.py — do not edit"
                   " (regenerate + review). -/")
        out.append("/-@")
        out.append(f"  spec for `{fname}` in {os.path.basename(cpath)}:")
        out.append(f"    requires  {req}")
        out.append(f"    ensures   {ens}")
        if modif:
            out.append(f"    modifies  {modif}   (frame condition: TODO in conclusion)")
        out.append("-/")
        binders = f"({pl}) (m\u2080 : Mem)" if pl else f"(m\u2080 : Mem)"
        # The WHOLE proposition is emitted as a named Prop constant, no
        # proof and no sorry: external proof files state
        # `theorem {fname}_cspec : {fname}_cspec_type := ...`, so the
        # kernel itself guarantees the proof matches the generated
        # statement (drift is impossible, not merely detected).
        out.append(f"def {fname}_cspec_type : Prop :=")
        out.append(f"  \u2200 {binders},")
        pre_binds = ("let old : WordAt := fun p => Mem.get m\u2080 p;"
                     if re.search(r"\bold\b", req) else "")
        out.append(f"    (({pre_binds} {req} : Bool) : Prop) \u2192")
        out.append("    \u2203 (fuel result : Nat) (m : Mem),")
        out.append(f"      runModule projectM \"{fname}\" [{args}] fuel m\u2080"
                   f" = Res.val result m")
        cur_b = ("let cur : WordAt := fun p => Mem.get m p;\n          "
                 if re.search(r"\bcur\b", ens) else "")
        old_b = ("let old : WordAt := fun p => Mem.get m\u2080 p;\n          "
                 if re.search(r"\bold\b", ens) else "")
        out.append(f"      \u2227 (({cur_b}{old_b}({ens} : Bool)) : Prop)")
        out.append("")
        names.append(f"{fname}_cspec")
    return names

# The corpus IR (and therefore every Lean proof about IR shapes) was
# produced by clang 21.x.  IR shapes change between major versions,
# so a mismatch is an error, not a warning.
CLANG_MAJOR = 21

def check_clang():
    exe = shutil.which("clang")
    if exe is None:
        sys.exit("c2lean: clang not found on PATH — install clang "
                 f"{CLANG_MAJOR}.x, or pass pre-compiled .ll files instead")
    try:
        out = subprocess.run([exe, "--version"], capture_output=True,
                             text=True).stdout
        major = int(re.search(r"version (\d+)", out).group(1))
    except Exception:
        sys.exit("c2lean: could not determine the clang version; need "
                 f"clang {CLANG_MAJOR}.x (`{exe} --version` failed)")
    if major != CLANG_MAJOR:
        sys.exit(f"c2lean: found clang {major}.x, but this tool is calibrated "
                 f"for clang {CLANG_MAJOR}.x — IR shapes (and therefore proofs) "
                 f"differ between versions; use clang-{CLANG_MAJOR} or pass "
                 "matching .ll files directly")

def compile_c(p, tmpdir):
    # A C file may pin its own optimization level with a `//@ optimize O1`
    # comment (the IR shape a proof was written against is part of the
    # example, and the C source is the single place to record that).
    opt = "O0"
    src = open(p, errors="replace").read()
    m = re.search(r"//@\s*optimize\s+(O[0-3sz])\b", src)
    if m:
        opt = m.group(1)
    stem = os.path.splitext(os.path.basename(p))[0]
    ll = os.path.join(tmpdir, stem + ".ll")
    r = subprocess.run(["clang", "-" + opt, "-emit-llvm", "-S", p, "-o", ll],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"c2lean: clang failed on {p} (exit {r.returncode}):\n"
                 + r.stderr.strip())
    return ll

def main():
    import argparse
    ap = argparse.ArgumentParser(
        prog="c2lean.py",
        description="Translate C (via clang) or LLVM IR into Lean: ASTs + spec skeletons.",
        epilog="Deterministic, fail-closed, all-or-nothing; see the module "
               "docstring for the full behavior contract.",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="+", metavar="FILE.c|FILE.ll",
                    help="C sources (compiled with clang -O0) and/or LLVM IR "
                         "files — the whole linked project")
    ap.add_argument("-o", metavar="FILE", default=None, dest="out",
                    help="output file (default: C2Lean/Programs.lean)")
    ap.add_argument("--check", action="store_true",
                    help="linter mode: validate inputs + verify generated "
                         "files are fresh; write nothing, exit non-zero on "
                         "any problem")
    args = ap.parse_args()
    check, paths = args.check, args.paths
    import os.path
    # early validation: fail with messages, never tracebacks
    for p in paths:
        if not os.path.isfile(p):
            sys.exit(f"c2lean: no such file: {p}")
        if not p.endswith((".c", ".ll")):
            sys.exit(f"c2lean: unsupported input (want .c or .ll): {p}")
    out = args.out or os.path.join("C2Lean", "Programs.lean")
    tmp_out = False
    if out == "-":                      # fresh, collision-free temp target
        stem = os.path.splitext(os.path.basename(paths[0]))[0]
        out = os.path.join(tempfile.mkdtemp(prefix="c2lean-"), stem + ".lean")
        tmp_out = True
    for p in paths:
        if os.path.exists(out) and os.path.samefile(p, out):
            sys.exit(f"c2lean: refusing to write {out}: it is also an input")
    d = os.path.dirname(out)
    if d and not os.path.isdir(d):
        sys.exit(f"c2lean: no such directory: {d} (output: {out})")
    if any(p.endswith(".c") for p in paths):
        check_clang()
    tmpdir = tempfile.TemporaryDirectory(prefix="c2lean-")
    inputs = []                          # (ll_path, explicit_spec_c, label)
    for p in paths:
        if p.endswith(".c"):
            inputs.append((compile_c(p, tmpdir.name), p, p))
        else:
            inputs.append((p, None, p))
    prog, spec_out = [], []
    nspecs = 0
    audit_names = []
    defined, module_names = {}, []
    texts = {ll: open(ll).read() for ll, _, _ in inputs}
    for ll, _, label in inputs:         # pass 1: lay out globals
        globals_prepass(label, texts[ll])
    for path, spec_c, label in inputs:
        mod = llvm.parse_assembly(texts[path])
        mod.verify()  # LLVM itself checks the IR — free static analysis
        stem = os.path.splitext(os.path.basename(path))[0]
        for f in mod.functions:
            if f.is_declaration:
                continue
            params, blocks = convert_function(f)
            pl = ", ".join(f'"{p}"' for p in params)
            prog.append(f"def {f.name}F : Func where")
            prog.append(f"  params := [{pl}]")
            prog.append("  blocks :=")
            rows = []
            for name, instrs, term in blocks:
                indented = ",\n".join("      " + s.strip() for s in instrs)
                if instrs:
                    rows.append(f"  (\"{name}\",\n    ([\n{indented}],\n     {term}))")
                else:
                    rows.append(f"  (\"{name}\", ([], {term}))")
            prog.append("  [" + ",\n".join(rows) + "]")
            prog.append("")
        funcs = [f.name for f in mod.functions if not f.is_declaration]
        for n in funcs:
            if n in defined:
                sys.exit(f"{label}: function `{n}` already defined in "
                         f"{defined[n]} — duplicate symbol (the C linker "
                         f"would reject this too)")
            defined[n] = label
        entries = ", ".join(f'("{n}", {n}F)' for n in funcs)
        prog.append(f"def {stem}M : Module := [{entries}]")
        prog.append("")
        module_names.append(f"{stem}M")
        # spec side: c/<stem-minus-_cl>.c, if it exists
        base = stem[:-3] if stem.endswith("_cl") else stem
        # spec source: the .c given on the command line (if any), else
        # <stem>.c next to the .ll, else c/<stem>.c
        cpath = spec_c or next(
            (c for c in (os.path.join(os.path.dirname(path), base + ".c"),
                         os.path.join("examples", base + ".c"))
             if os.path.exists(c)), None)
        if cpath:
            specs = parse_c(cpath)
            nspecs += len(specs)
            audit_names += emit_specs(spec_out, cpath, f"{stem}M", specs)

    if GLOBALS:
        prog.append("/-- Global variable addresses (linker layout). -/")
        for name, addr in sorted(GLOBALS.items()):
            prog.append(f"def {name} : Nat := {addr}")
        cells = ", ".join(f"({a}, {v})" for a, v in GVALUES)
        prog.append(f"def projectG : Mem := {{ cells := [{cells}],"
                    " next := 1024 }")
        prog.append("")
    # the linked program: every module concatenated (like a static linker).
    # Cross-file calls resolve here; spec skeletons run against projectM.
    if module_names:
        prog.append("def projectM : Module := " + " ++ ".join(module_names))
        prog.append("")
    progtxt = ("-- GENERATED by c2lean.py from " + ", ".join(paths)
               + " -- do not edit\n"
               "import C2Lean.Semantics.Flat32\nimport C2Lean.SpecLib\n\n"
               "namespace C2Lean\nopen Ll Spec\n\n"
               + "\n".join(prog) + "\n"
               + "\n".join(spec_out) + "\nend C2Lean\n")
    # Axiom audit: one `#print axioms`-style check per spec proof, run in a
    # single elaboration.  `lake env lean examples/build/C2Lean/Audit.lean` prints one AUDIT
    # line per proof; `make check` fails the build on `sorryAx` and reports
    # unproven specs as AUDIT-MISSING.
    audtxt = ("-- GENERATED axiom audit -- do not edit; run: "
              "lake env lean examples/build/C2Lean/Audit.lean\n"
              "import Lean\nimport Proofs\n\n"
              "open Lean Elab Command in\n"
              "#eval show CommandElabM Unit from do\n"
              "  let specs : Array Name := #[" +
              ", ".join(f"`C2Lean.{n}" for n in audit_names) + "]\n"
              "  for nm in specs do\n"
              "    match (\u2190 getEnv).find? nm with\n"
              "    | none => logInfo s!\"AUDIT-MISSING {nm} (no proof yet)\"\n"
              "    | some _ =>\n"
              "        let ax \u2190 liftCoreM (Lean.collectAxioms nm)\n"
              "        logInfo s!\"AUDIT {nm}: {ax.toList}\"\n")
    auditpath = os.path.join(os.path.dirname(out) or ".", "Audit.lean")
    targets = [(out, progtxt), (auditpath, audtxt)]
    if check:
        stale = []
        for path, want in targets:
            try:
                if open(path).read() != want:
                    stale.append(path)
            except FileNotFoundError:
                stale.append(path)
        if stale:
            sys.exit("c2lean: STALE: " + ", ".join(stale)
                     + " (rerun without --check)")
        print(f"c2lean: fresh ({len(paths)} modules, {nspecs} specs)")
        return
    for path, want in targets:
        try:
            with open(path, "w") as fh:
                fh.write(want)
        except OSError as e:
            sys.exit(f"c2lean: cannot write {path}: {e.strerror}")
    print(f"c2lean: wrote {out} ({len(paths)} modules, {nspecs} specs)",
          file=sys.stderr)
    if tmp_out:                         # stdout carries ONLY the path
        print(out)

if __name__ == "__main__":
    main()
