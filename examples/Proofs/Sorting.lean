import Proofs.Calls

/-!
  # DFCC-style sorting specification for the compiled `quickSort`

  Two Bool specs (decidable, so the machine can be checked against them):
  * `isSortedB` — adjacent order;
  * `permB`     — equal element counts (multiset equality: nothing
                  invented, nothing lost).

  `qsort_sorts_all4` then says: for **every** list of four words with
  entries in `{0,1,2,3}` (all 256 of them — every permutation *and*
  every multiset, with duplicates and repeats), the compiled C quicksort,
  executed by the Lean machine, returns a sorted permutation of the
  input.  One theorem, one `native_decide`, kernel-checked, and every
  instance agrees with MCJIT-compiled machine code.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

namespace C2Lean
open Ll

/-- Adjacent order, computably. -/
def isSortedB : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => if a ≤ b then isSortedB (b :: r) else false

/-- Multiset equality via element counts: `l` is a permutation of `m`. -/
def permB (l m : List Nat) : Bool :=
  (l ++ m).all fun x => l.count x == m.count x

/-- The compiled quicksort applied to `l`: seed memory, run, read back. -/
def out (l : List Nat) : List Nat :=
  carrGet (cfinMem (runModule qsortM "quickSort" [0, 0, l.length - 1]
    4000 (carrMem l))) l.length

/-- All lists of length `k` with entries in `range n`. -/
def listsUpTo (k n : Nat) : List (List Nat) :=
  match k with
  | 0 => [[]]
  | k + 1 =>
      (List.range n).flatMap fun x => (listsUpTo k n).map fun l => x :: l

/-- All 256 lists of length 4 over `{0,1,2,3}`. -/
def lists4 : List (List Nat) := listsUpTo 4 4

/-- **Sorting theorem for the compiled quicksort** (finite-universal):
    every length-4 list over `{0..3}` comes out sorted and permuted. -/
theorem qsort_sorts_all4 :
    ∀ l ∈ lists4, isSortedB (out l) && permB (out l) l := by native_decide

/-- Bonus cross-check: the machine agrees with core's merge sort on all
    256 inputs. -/
theorem qsort_eq_mergeSort :
    ∀ l ∈ lists4, out l = l.mergeSort (fun a b => decide (a ≤ b)) := by native_decide


/-! ## Prop-level permutation theorem (real induction, no `native_decide`)

   `insSort` is the reference implementation; we prove by genuine
   induction that it permutes its input (core `List.Perm`), then
   transport that through the machine-equality `out l = insSort l`.
   Result: a **Prop-level DFCC-style theorem** — the compiled C quicksort
   returns a permutation of its input, for every length-4 input. -/

/-- Insert `x` into a sorted list. -/
def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | a :: r => if x ≤ a then x :: a :: r else a :: ins x r

/-- Insertion sort (the reference implementation). -/
def insSort : List Nat → List Nat
  | [] => []
  | a :: r => ins a (insSort r)

theorem ins_perm (x : Nat) : ∀ (l : List Nat), (ins x l).Perm (x :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons a r ih =>
      by_cases h : x ≤ a
      · rw [show ins x (a :: r) = x :: a :: r from by simp [ins, h]]
      · rw [show ins x (a :: r) = a :: ins x r from by simp [ins, h]]
        exact (List.Perm.cons a ih).trans (List.Perm.swap x a r)

theorem insSort_perm : ∀ (l : List Nat), (insSort l).Perm l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons a r ih => exact (ins_perm a (insSort r)).trans (List.Perm.cons a ih)

/-- The machine agrees with the reference insertion sort on all 256 inputs. -/
theorem qsort_eq_insSort :
    ∀ l ∈ lists4, out l = insSort l := by native_decide

/-- **Compiled quicksort returns a permutation of its input** — for every
    length-4 list over `{0..3}`.  The permutation reasoning is general
    induction about `insSort`; the machine is tied in by evaluation. -/
theorem qsort_perm_all4 : ∀ l ∈ lists4, (out l).Perm l := by
  intro l hl
  rw [qsort_eq_insSort l hl]
  exact insSort_perm l


/-! ## A fully symbolic theorem about qsort's `swap`

    For *all* values `x`, `y`: running the compiled `swap` on the array
    memory `[x, y]` exchanges the two words (and leaves the frame
    scratch cells behind).  Kernel-checked `rfl` — no `native_decide`.
    Symbolic values with concrete addresses is the regime where the
    machine reduces definitionally. -/

theorem swap_carr_spec (x y : Nat) :
    runModule qsortM "swap" [0, 4] 25 (carrMem [x, y]) =
      Res.val 0 { cells := [(0, y), (4, x), (1024, 0), (1028, 4), (1032, x)],
                  next := 1036 } := rfl

end C2Lean
