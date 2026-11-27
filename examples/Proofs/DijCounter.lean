import Proofs.DijFinal
/-! The uploaded `dijkstra_correct_type` is false: `m₀.next` is unconstrained. -/
namespace Dijkstra
open Ll C2Lean

theorem runModule_mono_val' (mod : Module) (fn : String) (args : List Nat)
    (fuel v : Nat) (m₀ m : Mem) (h : runModule mod fn args fuel m₀ = Res.val v m)
    (k : Nat) : runModule mod fn args (fuel + k) m₀ = Res.val v m := by
  unfold runModule at *
  split at h
  · cases h
  · split at h
    · cases h
    · exact runM_mono_val _ _ _ _ _ h k

theorem runModule_val_unique' (mod : Module) (fn : String) (args : List Nat)
    (f₁ f₂ v₁ v₂ : Nat) (m₀ m₁ m₂ : Mem)
    (h₁ : runModule mod fn args f₁ m₀ = Res.val v₁ m₁)
    (h₂ : runModule mod fn args f₂ m₀ = Res.val v₂ m₂) : v₁ = v₂ ∧ m₁ = m₂ := by
  have a := runModule_mono_val' _ _ _ _ _ _ _ h₁ f₂
  have b := runModule_mono_val' _ _ _ _ _ _ _ h₂ f₁
  rw [Nat.add_comm] at b
  rw [a] at b
  cases b
  exact ⟨rfl, rfl⟩

/-- `V = 2`, one edge `0 → 1` of weight 5, frames start at address 4. -/
def mB : Mem := { cells := [(4, 5)], next := 4 }

def checkB : Bool :=
  match runModule projectM "dijkstra" [0, 16, 24, 0, 2] 100000 mB with
  | Res.val _ m => m.get 16 == 2147483647
  | _ => false

theorem checkB_true : checkB = true := by decide +kernel

theorem Wm_mB (u v : Nat) : Wm mB 2 u v = if 2 * u + v = 1 then 5 else 0 := by
  simp only [Wm, mB, Mem.get, Mem.cellsGet_cons, Mem.cellsGet_nil, beq_iff_eq]
  by_cases h : 2 * u + v = 1
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

def ψ (v : Nat) : Nat := if v = 0 then 0 else 5

theorem lowerB (vs : List Nat) (hw : Walk (Wm mB 2) 0 vs) :
    ∀ v, vs.head? = some v → ψ v ≤ walkWeight (Wm mB 2) vs := by
  induction hw with
  | single => intro v hv; simp at hv; subst hv; simp [ψ]
  | @extend u v vs h huv ih =>
    intro v' hv
    have hv' : v' = v := by simp at hv; exact hv.symm
    subst hv'
    have := ih u rfl
    rw [Wm_mB] at huv
    rw [walkWeight_cons2, Wm_mB]
    unfold ψ at *
    split at huv <;> split <;> split at this <;> omega

theorem graphAt_mB : GraphAt 2 mB := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv; rw [Wm_mB]; split <;> omega
  · intro u v h; rw [Wm_mB, ite_eq_right (by omega)]
  · intro v hv
    refine ⟨ψ v, ?_, fun vs hw hh => lowerB vs hw v hh⟩
    by_cases h0 : v = 0
    · subst h0; exact ⟨[0], Walk.single _ 0, rfl, rfl⟩
    · have e1 : v = 1 := by omega
      subst e1
      refine ⟨[1, 0], Walk.extend (Walk.single _ 0) (by rw [Wm_mB]; decide), rfl, ?_⟩
      rw [walkWeight_cons2, Wm_mB]; rfl

theorem dijkstra_correct_false : ¬ dijkstra_correct_type := by
  intro h
  obtain ⟨fuel, r, m, hrun, -, hdist⟩ := h 2 mB (by omega) (by omega) graphAt_mB
  have hc := checkB_true
  unfold checkB at hc
  split at hc
  · rename_i r' m' hr
    have hm : m.get 16 = 2147483647 := by
      obtain ⟨-, rfl⟩ := runModule_val_unique' _ _ _ _ _ _ _ _ _ _ hrun hr
      simpa using hc
    have := (hdist 0 (by omega)).2 [0] (Walk.single _ 0) rfl
    simp only [show 4 * 2 * 2 + 4 * 0 = 16 from rfl, hm] at this
    revert this; decide
  · cases hc

end Dijkstra
