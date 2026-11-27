# c2lean — verified Lean copies of compiled C programs

`c2lean.py` translates C (via clang's LLVM IR) into a deep embedding in
Lean 4: a small, faithful fragment of LLVM IR (SSA, `icmp`/`br`/`phi`,
`alloca`/`load`/`store`/`gep`, calls, recursion, globals) plus a
fuel-bounded abstract machine that executes it. Every `//@` spec comment
in the C source becomes a Lean proposition; proofs are checked by the
kernel and audited for honesty.

```
C source + //@ specs  ──c2lean.py──  Lean statements  ──kernel──  proofs
        make check:   regen + lake build + axiom audit
```

## Layout

```
c2lean.py            the frontend: C → Lean ASTs, spec statements, audit
tools/jit_gen.py     MCJIT cross-check as generated ground-truth theorems
tools/jit_qsort.py   MCJIT driver for the call/recursion corpus
tools/jit_check.py   MCJIT ground truth for a single ad-hoc .ll
C2Lean.lean                  root import file (handwritten library only)
C2Lean/
  Semantics/Flat32.lean      THE MACHINE: flat word-addressed memory, 32-bit
                             words, stepOne/runM/runModule + API lemmas
  SpecLib.lean               spec vocabulary (getAt, SortedAt, PermAt, ...)
examples/
  *.c                the committed inputs, with //@ spec comments
  Proofs/            the expensive artifacts: one .lean per proof area,
                     proving specs about the .c files one level up
  Proofs.lean        [generated] aggregator (lake library root for the proofs)
  Makefile           THE entry point — see "Using it"
  build/     [generated, gitignored] everything derived from the .c inputs:
     <name>.lean              per-example standalone Lean (one per .c)
     C2Lean/Programs.lean     ASTs + spec statements (lake lib `Generated`)
     C2Lean/Audit.lean        axiom audit of all proofs
     C2Lean/McjitCheck.lean   MCJIT ground-truth theorems (make calibrate)
```

## Using it

The tools are interpreted — there is nothing to build at the repo root.
Everything happens in `examples/`:

```
cd examples
make                 convert every .c to Lean and run the full acceptance gate
make gen             per-example Lean files only (into build/)
make check PROG=fact generate + elaborate one example standalone
make lint            validate inputs without writing anything
make calibrate       MCJIT cross-check against real machine code
```

Requires: `elan`/`lake` (toolchain pinned in `lean-toolchain`), clang 21.x
(hard-gated — IR shapes are calibrated to it), and a `python` on PATH with
`llvmlite` (`pip install llvmlite`). LLVM IR is compiled internally and never touches
disk: the `.c` files are the only committed program input, and the clang
gate is what keeps the proofs' assumed IR shapes honest.

## The trust chain

1. **statement ↔ source**: `make` regenerates the Lean statements from the
   committed C; any drift in the C or its `//@` specs changes the statement.
2. **proof ↔ statement**: specs are emitted as `def <fn>_cspec_type : Prop`
   (statement only, no proof). A proof file states
   `theorem <fn>_cspec : <fn>_cspec_type := ...` — the kernel makes it
   impossible for a proof to be about a different statement (see
   `examples/Proofs/Swap.lean` for a completed one).
3. **honesty**: the generated `Audit.lean` collects the axiom set of every
   proof; `sorryAx` fails the build, and `make STRICT=1` additionally
   demands that every spec has a proof.

Committed inputs are exactly: `examples/*.c`, the proof files, and the
machinery (`c2lean.py`, semantics). Everything generated is ephemeral.

## Handing a spec to a prover

Four files suffice: `C2Lean/Semantics/Flat32.lean`, `C2Lean/SpecLib.lean`,
the generated `examples/build/C2Lean/Programs.lean` (or a standalone single-program file
via `examples/Makefile`), and `lean-toolchain`.
The prover returns one Lean file proving `<fn>_cspec_type`; acceptance is
`cp` + one `import` line + `make check`.

## What is verified today

- `log2ish_spec`, `arrsum_spec`: fully symbolic theorems (all inputs in a
  bound) by induction — no `native_decide`.
- `swap_cspec`: memory-level spec, both aliasing cases.
- Concrete cross-checks against MCJIT-compiled machine code throughout.
- `sort_cspec` (quicksort: sorted + permutation for all arrays ≤ 8):
  statement proved sound and ready for an external prover.

## Known model boundaries

- Memory is total: unallocated reads return 0 (LLVM calls them poison);
  no `free`, no UB detection. Safety is a precondition of each spec.
- Frame disjointness is explicit in specs (`ptr < m₀.next`): C gives it
  for free, the model cannot.
- IR shapes are calibrated to clang 21.x (opaque pointers since 15);
  the frontend fails closed on anything it does not understand.
