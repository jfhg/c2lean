import C2Lean.Semantics.Flat32
/-!
  # Specification vocabulary for C-embedded specs

  Spec text written in `//@` comments is **Lean source**: it is spliced
  verbatim into generated theorem skeletons and elaborated by Lean
  itself.  There is no spec-language translator to trust — the only
  trusted surface is (a) this small fixed vocabulary and (b) the fixed
  skeleton shape (which binds `result`, `at`, `at0`).

  Everything is `Bool`-valued, so every spec is decidable on concrete
  inputs: the same text serves as a test oracle and as a theorem.
-/

/-- Reference factorial (spec vocabulary for `fact.c`). -/
def factN : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factN n

namespace Spec

/-- A memory view: word at each address (bound to `Mem.get m` by the
    skeleton). -/
abbrev WordAt := Nat → Nat

/-- The word of array `a` at index `i`. -/
def getAt (w : WordAt) (a i : Nat) : Nat := w (a + 4 * i)

/-- Caller-provided arrays must live below the frame region (addresses
    < 1024 are never touched by `alloca`), so `n` words at `a` are
    in-bounds iff they stay below 1024. -/
def validAt (a n : Nat) : Bool := a + 4 * n ≤ 1024

/-- The first `n` words at `a` are in nondecreasing order. -/
def SortedAt (w : WordAt) (a n : Nat) : Bool :=
  (List.range (n - 1)).all fun i => getAt w a i ≤ getAt w a (i + 1)

/-- The first `n` words at `a` in `at1` are a permutation (equal element
    counts) of those in `at0`: nothing invented, nothing lost. -/
def PermAt (w1 w0 : WordAt) (a n : Nat) : Bool :=
  let l1 := (List.range n).map (getAt w1 a)
  let l0 := (List.range n).map (getAt w0 a)
  (l1 ++ l0).all fun x => l1.count x == l0.count x

/-- The first `n` words at `a` are all `< 2^31`, i.e. non-negative as
    *signed* `i32`.  The C code compares with signed `icmp`; this is what
    makes `SortedAt`'s `Nat` order agree with the program's notion of sorted. -/
def SmallAt (w : WordAt) (a n : Nat) : Bool :=
  (List.range n).all fun i => getAt w a i < 2147483648

theorem smallAt_bound {w : WordAt} {a n : Nat} (h : SmallAt w a n)
    (i : Nat) (hi : i < n) : getAt w a i < 2147483648 := by
  unfold SmallAt at h
  have := (List.all_eq_true (p := fun j => getAt w a j < 2147483648)).mp h i
    (List.mem_range.mpr hi)
  exact of_decide_eq_true this

/-- Sum of the first `n` words at `a`. -/
def SumAt (w : WordAt) (a n : Nat) : Nat :=
  (List.range n).foldl (fun s i => s + getAt w a i) 0

end Spec
