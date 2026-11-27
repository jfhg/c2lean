# TODO

- Auto-discover spec statements in the audit (scan the environment for
  `*_cspec_type` instead of the hardcoded name list) — attempted and parked.
- Spec `c:` scoping discipline: live with it, decide later (history in the
  bflean repo's git log).
- i64/i8 + casts (trunc/sext/zext); byte-granularity memory for strings.
- Pointer initializers and int-only struct globals (frontend work).
- Per-block Hoare rules / loop-invariant framework to make big proofs
  less hand-built.  (`Proofs/Reach.lean` is the current substrate: a
  step-indexed reachability relation + `runI`/`brn` stepping tactics.)

## arrsum_cspec — WIP state (proof parked, ~95% done)

The whole proof is generated per-case (`c_n ≤ 8` → 9 concrete cases, each
fully stepped through `Reach`); it lives at `/tmp/Arrsum-wip.lean` and
fails ONLY at the last step of each case: converting the post beq to a
Prop equality for `omega`.  The tail

    rw [hS]
    simp only [Nat.beq_eq, decide_eq_true_eq, Nat.add_zero]
    omega

fails because `Nat.beq_eq` is not a core lemma ("simp made no progress",
9x).  Fix: find the right beq→decide conversion (candidates: `Nat.beq_eq`
under another name, `beq_iff_eq`, or a per-case `show decide (X = Y) =
true`), or prove the tiny bridge `theorem beq_true {x y : Nat} (h : x = y)
: (x == y) = true := h ▸ rfl` once in `Reach.lean` and `rw [beq_true]`
before `omega`.  Everything BEFORE that tail closes: all 9 Reach chains,
the `w32` chain resolution (bounded by the `SumAt < 2^32` precondition
via `omega` discharges), and the `runModule ↔ blkCfg` defeq bridge.

Hard-won facts baked into the WIP (keep them):
- `runModule`/`runM`/`stepOne` terms DIVERGE under kernel whnf (`rfl`,
  plain `simp`) once a loop is involved; `maxRecDepth` does not help.
  All symbolic runs MUST go through `Reach.runM` (rewrites only).
- Fuel witnesses must be written `1 + n`, not `n + 1` (`Nat.add` recurses
  on the second arg; `1 + n` is stuck and therefore matches `hrun 1`).
- `nrm` needed `Int.reduceLT, Nat.reduceLT, Nat.reduceBEq, decide_eq_true_eq`
  added (arrsum branches on Int comparisons from `sgt`; qsort never did).
- `List.range` unfolds to `List.range.loop` in Lean 4.36; unfolding
  `SumAt` needs `simp [List.range, List.range.loop, List.foldl]`.

## Semantics selector in spec comments (parked until 2nd semantics exists)

Idea: `//@ semantics Flat32;` per file (or per function), so the C author
chooses which interpreter the propositions quantify over.

Why it's a real axis (evidence: qsort): the program's `icmp` is signed,
`SortedAt` is `Nat` — the original spec was FALSE for words >= 2^31.  We
patched with a bridge hypothesis (`SmallAt`); a `semantics signed` choice
would instead bind `SortedAt` to the signed order and need no bridge.

Where the seam already is: the spec vocabulary (`getAt/SortedAt/PermAt`)
is semantics-neutral (`WordAt = Nat → Nat`); each generated spec touches
the machine in exactly ONE clause, `runModule projectM "f" args fuel m₀ =
Res.val result m`.  A selector would swap that clause's interpreter and
import the chosen model's vocabulary namespace.  Precedent for per-file
generator directives: `//@ optimize O1`.

Natural first consumers: Flat64 (i64), byte-granularity memory (i8/
strings), the idealized-Nat + refinement style from the bflean era.

Design rule if/when built: the selector MUST bind both the interpreter
AND the spec-vocabulary meanings together.  Same spec text silently
meaning different things under different runners is exactly the qsort
trap; switching one without the other reintroduces it.
