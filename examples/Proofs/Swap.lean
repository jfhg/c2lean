import C2Lean.Programs
set_option maxRecDepth 400000

/-!
  Spec proof for `swap` (from `c/qsort.c`) — the acceptance-pipeline demo.

  The precondition `c_a, c_b < m₀.next` is load-bearing: the machine places
  `alloca` frames starting at `m₀.next`, so without it the swapped cells
  could alias the program's own slots (`a`, `b`, `temp`) — and then the
  program is not a swap.  In real C this disjointness is free (caller
  objects and callee frames never overlap); a model with arbitrary `m₀`
  must state it explicitly.

  Proof shape (both cases): `rfl` for the run, `simp` to reduce the
  environment/address chains, then the memory read/write lemmas
  (`Mem.get_set_same`, `Mem.get_set_other`) with pre-proved address
  inequalities as side-condition facts.
-/

namespace C2Lean
open Ll Spec

theorem swap_cspec : swap_cspec_type := by
  intro c_a c_b m₀ hpre
  simp at hpre                      -- decide(...) = true  ==>  the conjunction
  obtain ⟨ha, hb⟩ := hpre
  refine ⟨25, 0, _, rfl, ?_⟩
  simp [swapF, Env.set, List.zip, evOperand, roundup4]
  by_cases he : c_a = c_b
  · -- aliased pointers: swapping a cell with itself leaves it unchanged
    subst he
    have h1 : ¬(c_a = m₀.next) := by omega
    have h2 : ¬(c_a = m₀.next + 4) := by omega
    have h3 : ¬(c_a = m₀.next + 4 + 4) := by omega
    have h12 : ¬(m₀.next = m₀.next + 4 + 4) := by omega
    have h13 : ¬(m₀.next + 4 = c_a) := by omega
    have h17 : ¬(m₀.next + 4 + 4 = c_a) := by omega
    simp [h1, h2, h3, h12, h13, h17,
         Mem.get_set_same, Mem.get_set_other]
    exact rfl   -- aliased case: both conjuncts are identical, `&&` collapsed
  · -- distinct pointers: the two cells exchange contents
    have hne : ¬(c_a = c_b) := he
    have h1 : ¬(c_a = m₀.next) := by omega
    have h2 : ¬(c_a = m₀.next + 4) := by omega
    have h4 : ¬(c_a = c_b) := hne
    have h5 : ¬(c_b = m₀.next) := by omega
    have h6 : ¬(c_b = m₀.next + 4) := by omega
    have h7 : ¬(c_b = m₀.next + 4 + 4) := by omega
    have h12 : ¬(m₀.next = m₀.next + 4 + 4) := by omega
    have h13 : ¬(m₀.next + 4 = c_a) := by omega
    have h17 : ¬(m₀.next + 4 + 4 = c_a) := by omega
    simp [h1, h2, h4, h5, h6, h7, h12, h13, h17,
         Mem.get_set_same, Mem.get_set_other]
    exact ⟨rfl, rfl⟩

end C2Lean
