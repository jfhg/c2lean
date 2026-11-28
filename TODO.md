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
