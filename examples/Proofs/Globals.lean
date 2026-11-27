import C2Lean.Programs

/-!
  Specs for `globals.c`.  Globals are ordinary memory (linker-laid-out
  cells in `projectG`), and the specs quantify over *every* initial
  memory `m₀` — global reads are then direct `m₀.get` terms, the runs
  reduce by `rfl`, and the proofs are read/write rewrites.

  Note the `bump` precondition `old counter < 4294967295`: without it
  the spec is FALSE in this model (a counter at `2^32 - 1` wraps to 0).
  C "knows" counters are small; the model hands over arbitrary memory,
  so the bound must be stated.
-/

namespace C2Lean
open Ll Spec

theorem get_cspec : get_cspec_type := by
  intro c_i m₀ hpre
  simp at hpre                      -- decide(...) = true  ==>  the conjunction
  obtain ⟨hlt, hb⟩ := hpre          -- c_i < 4 ; m₀.next < 2^20
  refine ⟨100, _, _, rfl, ?_⟩
  have hz : w32 (c_i : Int) = c_i := by
    rw [w32_eq _ (by omega) (by omega)]; omega
  have hw : w32 ((4 : Int) * c_i + 1048580) = 4 * c_i + 1048580 := by
    rw [w32_eq _ (by omega) (by omega)]; omega
  -- the frame slot cannot alias the table: frames live below 2^20
  have hne : ¬(4 * c_i + 1048580 = m₀.next) := by omega
  simp [getF, Env.set, List.zip, evOperand, roundup4, getAt, table, evBin,
        hz, hw, hne, Mem.get_set_same, Mem.get_set_other,
        Mem.get_of_next_update]
  rw [show (4 : Nat) * c_i + 1048580 = 1048580 + 4 * c_i by omega]

theorem bump_cspec : bump_cspec_type := by
  intro m₀ hpre
  simp at hpre
  refine ⟨100, 0, _, rfl, ?_⟩
  simp [bumpF, Env.set, List.zip, evOperand, evBin, counter,
        Mem.get_set_same]
  have h1 : m₀.get 1048576 < 4294967295 := hpre  -- `counter` = 1048576
  have hw : w32 ((m₀.get 1048576 : Int) + 1) = m₀.get 1048576 + 1 :=
    w32_add (m₀.get 1048576) 1 (by omega)
  rw [hw]

theorem read_counter_cspec : read_counter_cspec_type := by
  intro m₀ _
  refine ⟨100, _, _, rfl, ?_⟩
  simp [read_counterF, Env.set, List.zip, evOperand, counter]

end C2Lean
