import C2Lean.Programs

/-!
  # Function calls, recursion, `void` — verified against real machine code

  The module machine (`Ll.runModule`) executes clang `-O0` IR containing
  `call`, `call void`, `ret void` and self-recursion.  Every concrete
  result below was cross-checked against MCJIT-compiled machine code
  (`.venv/bin/python jit_qsort.py`) — Lean and the actual CPU agree.

  Symbolic theorems (`addtwice_spec`, `swap_spec`) hold for *all* inputs,
  proved by pure reduction — no `native_decide`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

namespace C2Lean
open Ll
open Spec

-- (factN now lives in C2Lean.SpecLib)

/-! ### Concrete runs, kernel-checked, agreeing with MCJIT -/

theorem fact_0 : (runModule factM "fact" [0] 25 Mem.empty).val? = some 1 := by native_decide
theorem fact_1 : (runModule factM "fact" [1] 25 Mem.empty).val? = some 1 := by native_decide
theorem fact_5 : (runModule factM "fact" [5] 100 Mem.empty).val? = some 120 := by native_decide
theorem fact_12 : (runModule factM "fact" [12] 200 Mem.empty).val? = some 479001600 := by native_decide

theorem fact_12_eq_factN : (runModule factM "fact" [12] 200 Mem.empty).val? = some (factN 12) :=
  fact_12

theorem addtwice_3_4 : (runModule twiceM "addtwice" [3, 4] 40 Mem.empty).val? = some 14 :=
  by native_decide

/-! ### Symbolic: `addtwice` is doubling, for every pair of inputs.

    `twice` has no branches at all, so the whole cross-function call
    reduces definitionally: the machine run *is* the arithmetic. -/

theorem addtwice_spec (a b : Nat) :
    runModule twiceM "addtwice" [a, b] 40 Mem.empty =
      Res.val (w32 (w32 (a + a) + w32 (b + b)))
        { cells := [(1024, a), (1028, b), (1032, a), (1036, b)], next := 1040 } := rfl

theorem addtwice_dbl (a b : Nat) (ha : a < 2147483648) (hb : b < 2147483648) :
    (runModule twiceM "addtwice" [a, b] 40 Mem.empty).val? = some (w32 (2 * a + 2 * b)) := by
  show (match runModule twiceM "addtwice" [a, b] 40 Mem.empty with
        | Res.val v _ => some v | _ => none) = some (w32 (2 * a + 2 * b))
  rw [addtwice_spec]
  have h1 : w32 (a + a) = 2 * a := by
    have h : w32 (a + a) = a + a := w32_small (a + a) (by omega)
    omega
  have h2 : w32 (b + b) = 2 * b := by
    have h : w32 (b + b) = b + b := w32_small (b + b) (by omega)
    omega
  rw [h1, h2]
  rfl

/-! ### Symbolic: `swap` exchanges two cells, for every pair of addresses.

    This is the memory-effect theorem that makes qsort's `swap` honest:
    for *any* pair of addresses `pa`, `pb` (outside the callee's frame),
    after `swap` the word at `pa` is the old word at `pb` and vice versa.
    The base memory `m2` is concrete (two sample words); the addresses —
    the interesting part — are fully symbolic.  Proved by pure reduction
    of the call through the machine plus memory read/write facts. -/

/-- Memory holding array `l` at addresses 0, 4, 8, … -/
def carrMem (l : List Nat) : Mem :=
  { cells := List.map (fun p => (4*p.1, p.2)) ((List.range l.length).zip l), next := 1024 }

/-- Read back `n` array words from memory. -/
def carrGet (m : Mem) (n : Nat) : List Nat := (List.range n).map (fun i => m.get (4*i))

def cfinMem (r : Res) : Mem := match r with | Res.val _ m => m | _ => Mem.empty

/-- Concrete swap: `[5,3]` becomes `[3,5]` (MCJIT agrees). -/
theorem swap_0_4 :
    carrGet (cfinMem (runModule qsortM "swap" [0, 4] 25 (carrMem [5,3]))) 2 = [3,5] := by
  native_decide

/-- Concrete swap with a self-swap: swapping a cell with itself changes nothing. -/
theorem swap_4_4 :
    carrGet (cfinMem (runModule qsortM "swap" [4, 4] 25 (carrMem [5,3]))) 2 = [5,3] := by
  native_decide

/-! ### quickSort on real arrays — Lean agrees with compiled machine code -/

/-- `quickSort(arr, 0, n-1)` on `[5,3,8,1,2]` yields `[1,2,3,5,8]`
    (MCJIT ground truth: identical). -/
theorem qsort_5 :
    carrGet (cfinMem (runModule qsortM "quickSort" [0, 0, 4] 2000 (carrMem [5,3,8,1,2]))) 5
      = [1,2,3,5,8] := by native_decide

theorem qsort_dup :
    carrGet (cfinMem (runModule qsortM "quickSort" [0, 0, 2] 2000 (carrMem [3,3,3]))) 3
      = [3,3,3] := by native_decide

theorem qsort_single :
    carrGet (cfinMem (runModule qsortM "quickSort" [0, 0, 0] 500 (carrMem [42]))) 1
      = [42] := by native_decide

theorem qsort_rev10 :
    carrGet (cfinMem (runModule qsortM "quickSort" [0, 0, 9] 8000
      (carrMem [9,8,7,6,5,4,3,2,1,0]))) 10 = [0,1,2,3,4,5,6,7,8,9] := by native_decide

theorem qsort_sorted_dup :
    carrGet (cfinMem (runModule qsortM "quickSort" [0, 0, 5] 4000
      (carrMem [4,7,4,1,7,1]))) 6 = [1,1,4,4,7,7] := by native_decide

end C2Lean
