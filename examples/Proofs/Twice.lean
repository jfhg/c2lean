import C2Lean.Programs
set_option maxRecDepth 400000

/-!
  Specs for `twice.c`: pure functions, so the machine run reduces by
  `rfl` even for a symbolic initial memory `m₀` — nothing branches on a
  memory load.  The real work is collapsing frame-slot indirections
  (`Mem.get_set_same`; frame-address inequalities must be stated because
  `simp` cannot call `omega` for side conditions) and resolving the
  signed-`Int` `w32` redexes under the no-overflow preconditions.
-/

namespace C2Lean
open Ll Spec

theorem twice_cspec : twice_cspec_type := by
  intro c_x m₀ hpre
  simp at hpre
  refine ⟨7, _, _, rfl, ?_⟩
  simp [twiceF, Env.set, List.zip, evOperand, roundup4, evBin, Mem.get_set_same]
  rw [w32_add c_x c_x (by omega)]
  omega  -- c_x + c_x = 2 * c_x

-- `h3` is consumed discharging a `get_set_other` side condition, but the
-- unused-simp-args linter cannot see through `simp`'s rewrite scheduling.
set_option linter.unusedSimpArgs false in
theorem addtwice_cspec : addtwice_cspec_type := by
  intro c_a c_b m₀ hpre
  simp at hpre
  refine ⟨40, _, _, rfl, ?_⟩
  simp [addtwiceF, twiceF, Env.set, List.zip, evOperand, roundup4]
  have h3 : ¬(m₀.next = m₀.next + 4 + 4) := by omega
  simp [evBin, h3, Mem.next_set, Mem.get_set_same, Mem.get_set_other,
        Mem.get_of_next_update]
  rw [w32_add c_a c_a (by omega), w32_add c_b c_b (by omega),
      w32_add (c_a + c_a) (c_b + c_b) (by omega)]
  omega

end C2Lean
