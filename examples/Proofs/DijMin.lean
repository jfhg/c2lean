import Proofs.DijInfra
namespace DijP
open Ll C2Lean

/-! `minDistance(dist, sptSet, V)` for a runtime vertex count `V`. -/

def MEnv (E : Env) (N : Nat) : Prop :=
  Env.get E "4" = N ∧ Env.get E "5" = N + 4 ∧ Env.get E "6" = N + 8 ∧
  Env.get E "7" = N + 12 ∧ Env.get E "8" = N + 16 ∧ Env.get E "9" = N + 20

def MInv (m0 : Mem) (V D0 S0 v mn idx : Nat) : Prop :=
  v ≤ V ∧ mn ≤ 2147483647 ∧
  (((∀ w, w < v → m0.get (4 * w + S0) ≠ 0) ∧ mn = 2147483647 ∧ idx = 0) ∨
   (idx < v ∧ m0.get (4 * idx + S0) = 0 ∧ mn = m0.get (4 * idx + D0) ∧
    ∀ w, w < v → m0.get (4 * w + S0) = 0 → m0.get (4 * idx + D0) ≤ m0.get (4 * w + D0)))

theorem md_loop {N V D0 S0 : Nat} {m0 : Mem} {k : Cont} {D : Config → Prop} (hN : 1024 ≤ N)
    (hV : V ≤ 15) (hDS : D0 + 4 * V ≤ S0) (hS0 : S0 + 4 * V ≤ 1024)
    (hD : ∀ w, w < V → m0.get (4 * w + D0) ≤ 2147483647) :
    ∀ n v mn idx E M prev, V - v = n → MEnv E N →
      M.get N = D0 → M.get (N + 4) = S0 → M.get (N + 8) = V → M.get (N + 12) = mn →
      M.get (N + 16) = idx → M.get (N + 20) = v → M.next = N + 24 →
      (∀ p, p < N → M.get p = m0.get p) →
      MInv m0 V D0 S0 v mn idx →
      (∀ E' M' mn' idx', MEnv E' N → M'.get (N + 16) = idx' → M'.next = N + 24 →
        (∀ p, p < N → M'.get p = m0.get p) → MInv m0 V D0 S0 V mn' idx' →
        Reach projectM (blkCfg "minDistance" minDistanceF "40" (some "10") E' M' k) D) →
      Reach projectM (blkCfg "minDistance" minDistanceF "10" prev E M k) D := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro v mn idx E M prev hn hE s4 s5 s6 s7 s8 s9 sN hfr hI hk
  obtain ⟨e4, e5, e6, e7, e8, e9⟩ := hE
  obtain ⟨hvV, hmn, hI⟩ := hI
  drunI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
  by_cases hc : v < V
  · dbrn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
    have hDv := hD v hc
    have fS : M.get (4 * v + S0) = m0.get (4 * v + S0) := hfr _ (by omega)
    have fD : M.get (4 * v + D0) = m0.get (4 * v + D0) := hfr _ (by omega)
    drunI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, fS, fD]
    by_cases hs : m0.get (4 * v + S0) = 0
    · dbrn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, fS, fD, hs]
      drunI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, fS, fD, hs]
      by_cases hle : m0.get (4 * v + D0) ≤ mn
      · dbrn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, fS, fD, hs, hle]
        drunI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, fS, fD, hs, hle]
        dstp; dstp
        drunI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, fS, fD, hs, hle]
        dstp
        refine ih (V - (v + 1)) (by omega) (v + 1) (m0.get (4 * v + D0)) v _ _ _ rfl ?_
          (by dnrm [s4]) (by dnrm [s5]) (by dnrm [s6]) (by dnrm []) (by dnrm []) (by dnrm []) (by dnrm [sN])
          (fun p hp => by dnrm []; exact hfr p hp) ?_ hk
        · simp only [MEnv]; dnrm [e4, e5, e6, e7, e8, e9, and_self]
        · refine ⟨by omega, hDv, Or.inr ⟨by omega, hs, rfl, ?_⟩⟩
          intro w hw hsw
          by_cases hwv : w = v
          · subst hwv; exact Nat.le_refl _
          · rcases hI with ⟨hall, _, _⟩ | ⟨_, _, hmi, hmin⟩
            · exact absurd hsw (hall w (by omega))
            · have := hmin w (by omega) hsw; omega
      · dbrn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, fS, fD, hs, hle]
        dstp
        drunI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
        dstp
        refine ih (V - (v + 1)) (by omega) (v + 1) mn idx _ _ _ rfl ?_
          (by dnrm [s4]) (by dnrm [s5]) (by dnrm [s6]) (by dnrm [s7]) (by dnrm [s8]) (by dnrm [])
          (by dnrm [sN]) (fun p hp => by dnrm []; exact hfr p hp) ?_ hk
        · simp only [MEnv]; dnrm [e4, e5, e6, e7, e8, e9, and_self]
        · refine ⟨by omega, hmn, ?_⟩
          rcases hI with ⟨_, hm, _⟩ | ⟨hi, hsi, hmi, hmin⟩
          · omega
          · refine Or.inr ⟨by omega, hsi, hmi, ?_⟩
            intro w hw hsw
            by_cases hwv : w = v
            · subst hwv; omega
            · exact hmin w (by omega) hsw
    · dbrn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, fS, fD, hs]
      dstp
      drunI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
      dstp
      refine ih (V - (v + 1)) (by omega) (v + 1) mn idx _ _ _ rfl ?_
        (by dnrm [s4]) (by dnrm [s5]) (by dnrm [s6]) (by dnrm [s7]) (by dnrm [s8]) (by dnrm [])
        (by dnrm [sN]) (fun p hp => by dnrm []; exact hfr p hp) ?_ hk
      · simp only [MEnv]; dnrm [e4, e5, e6, e7, e8, e9, and_self]
      · refine ⟨by omega, hmn, ?_⟩
        rcases hI with ⟨hall, hm, hid⟩ | ⟨hi, hsi, hmi, hmin⟩
        · refine Or.inl ⟨?_, hm, hid⟩
          intro w hw
          by_cases hwv : w = v
          · subst hwv; exact hs
          · exact hall w (by omega)
        · refine Or.inr ⟨by omega, hsi, hmi, ?_⟩
          intro w hw hsw
          by_cases hwv : w = v
          · subst hwv; exact absurd hsw hs
          · exact hmin w (by omega) hsw
  · dbrn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
    have eV : v = V := by omega
    subst eV
    exact hk _ M mn idx (by simp only [MEnv]; dnrm [e4, e5, e6, e7, e8, e9, and_self]) s8 sN hfr
      ⟨hvV, hmn, hI⟩

theorem md_call {fn lbl : String} {prev : Option String} {d : String} {o0 o1 o2 : Operand}
    {r : List Instr} {tm : Term} {e : Env} {m : Mem} {k : Cont} {D : Config → Prop}
    {V D0 S0 : Nat}
    (h0 : evOperand e o0 = D0) (h1 : evOperand e o1 = S0) (h2 : evOperand e o2 = V)
    (hN : 1024 ≤ m.next) (hV : V ≤ 15) (hDS : D0 + 4 * V ≤ S0) (hS0 : S0 + 4 * V ≤ 1024)
    (hD : ∀ w, w < V → m.get (4 * w + D0) ≤ 2147483647)
    (hex : ∃ w, w < V ∧ m.get (4 * w + S0) = 0)
    (h : ∀ m' u, m'.next = m.next + 24 → (∀ p, p < m.next → m'.get p = m.get p) → u < V →
      m.get (4 * u + S0) = 0 →
      (∀ w, w < V → m.get (4 * w + S0) = 0 → m.get (4 * u + D0) ≤ m.get (4 * w + D0)) →
      Reach projectM ⟨fn, lbl, prev, r, tm, Env.set e d u, m', k⟩ D) :
    Reach projectM ⟨fn, lbl, prev, Instr.call d "minDistance" [o0, o1, o2] :: r, tm, e, m, k⟩ D := by
  apply Reach.step'
  · rfl
  simp only [List.map, h0, h1, h2]
  dnrm []
  drunI []
  dstp
  refine md_loop (m0 := m) hN hV hDS hS0 hD (V - 0) 0 2147483647 0 _ _ (some "0") rfl ?_
    (by dnrm []) (by dnrm []) (by dnrm []) (by dnrm []) (by dnrm []) (by dnrm []) (by dnrm [])
    (fun p hp => by dnrm [])
    ⟨by omega, Nat.le_refl _, Or.inl ⟨fun w hw => by omega, rfl, rfl⟩⟩ ?_
  · simp only [MEnv]; dnrm [and_self]
  intro E' M' mn idx hE' s8 sN hfr hI
  obtain ⟨e4, e5, e6, e7, e8, e9⟩ := hE'
  drunI [e8, s8]
  apply Reach.step'
  · rfl
  simp only [evOperand]
  rw [Env.get_set', ite_eq_left rfl]
  obtain ⟨_, _, hI⟩ := hI
  obtain ⟨w, hw, hsw⟩ := hex
  rcases hI with ⟨hall, _, _⟩ | ⟨hi, hsi, _, hmin⟩
  · exact absurd hsw (hall w hw)
  · exact h M' idx (by rw [sN]) hfr hi hsi hmin

end DijP
