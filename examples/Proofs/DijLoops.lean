import Proofs.DijMin
namespace DijP
open Ll C2Lean

/-! `dijkstra(graph, dist, sptSet, src, V)` loops, for runtime `V` (graph at 0,
    `dist` at `D0 = 4·Q`, `sptSet` at `S0 = D0 + 4·V`, `Q = V·V`). -/

theorem gidx {u v V Q : Nat} (hu : u < V) (hv : v < V) (hQ : V * V = Q) : u * V + v < Q := by
  have : (u + 1) * V ≤ V * V := Nat.mul_le_mul_right V (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this; omega

def DEnv (E : Env) (N : Nat) : Prop :=
  Env.get E "6" = N ∧ Env.get E "7" = N + 4 ∧ Env.get E "8" = N + 8 ∧ Env.get E "9" = N + 12 ∧
  Env.get E "10" = N + 16 ∧ Env.get E "11" = N + 20 ∧ Env.get E "12" = N + 24 ∧
  Env.get E "13" = N + 28 ∧ Env.get E "14" = N + 32

def DS (M : Mem) (N V D0 S0 : Nat) : Prop :=
  M.get N = 0 ∧ M.get (N + 4) = D0 ∧ M.get (N + 8) = S0 ∧ M.get (N + 12) = 0 ∧
  M.get (N + 16) = V

set_option maxHeartbeats 2000000 in
theorem init_loop {N V Q D0 S0 : Nat} {m0 : Mem} {k : Cont} {D : Config → Prop} (hN : 1024 ≤ N) (hV1 : 1 ≤ V) (hV : V ≤ 15) (hQ : Q ≤ 225) (hVQ : V ≤ Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) :
    ∀ n i E M prev, V - i = n → DEnv E N → DS M N V D0 S0 → M.get (N + 20) = i → i ≤ V →
      M.next = N + 36 →
      (∀ w, w < i → M.get (4 * w + D0) = 2147483647 ∧ M.get (4 * w + S0) = 0) →
      (∀ p, p < N → (∀ w, w < i → p ≠ 4 * w + D0 ∧ p ≠ 4 * w + S0) → M.get p = m0.get p) →
      (∀ E' M', DEnv E' N → DS M' N V D0 S0 → M'.next = N + 36 →
        (∀ w, w < V → M'.get (4 * w + D0) = 2147483647 ∧ M'.get (4 * w + S0) = 0) →
        (∀ p, p < N → (∀ w, w < V → p ≠ 4 * w + D0 ∧ p ≠ 4 * w + S0) → M'.get p = m0.get p) →
        Reach projectM (blkCfg "dijkstra" dijkstraF "31" (some "15") E' M' k) D) →
      Reach projectM (blkCfg "dijkstra" dijkstraF "15" prev E M k) D := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro i E M prev hn hE hS s11 hiV sN hdone hfr hk
  obtain ⟨e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := hE
  obtain ⟨s6, s7, s8, s9, s10⟩ := hS
  drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s11]
  by_cases hc : i < V
  · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s11, hc]
    drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s11, hc]
    dstp
    drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s11, hc]
    dstp
    refine ih (V - (i + 1)) (by omega) (i + 1) _ _ _ rfl ?_ ?_ (by dnrm []) (by omega)
      (by dnrm [sN]) ?_ ?_ hk
    · simp only [DEnv]; dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dnrm [s6, s7, s8, s9, s10]
    · intro w hw
      by_cases hwi : w = i
      · subst hwi; constructor <;> dnrm []
      · have := hdone w (by omega)
        constructor <;> dnrm [this.1, this.2]
    · intro p hp hpw
      have := hpw i (by omega)
      dnrm []
      exact hfr p hp (fun w hw => hpw w (by omega))
  · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s11, hc]
    have eV : i = V := by omega
    subst eV
    exact hk _ M (by simp only [DEnv]; dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]) ⟨s6, s7, s8, s9, s10⟩ sN hdone hfr

/-- New value of `dist[w]` after relaxing the edges out of `u`. -/
def relaxV (M0 : Mem) (V D0 S0 u w : Nat) : Nat :=
  if M0.get (4 * w + S0) = 0 ∧ M0.get (4 * (u * V + w)) ≠ 0 ∧ M0.get (4 * u + D0) ≠ 2147483647 ∧
      M0.get (4 * u + D0) + M0.get (4 * (u * V + w)) < M0.get (4 * w + D0)
  then M0.get (4 * u + D0) + M0.get (4 * (u * V + w)) else M0.get (4 * w + D0)

/-- Blocks 121/122: `v++`, back to the loop head. -/
theorem at121 {N v : Nat} {k : Cont} {D : Config → Prop} {E : Env} {M : Mem}
    {pr : Option String}
    (_hN : 1024 ≤ N) (hE : DEnv E N) (s14 : M.get (N + 32) = v) (hv : v < 16)
    (hk : ∀ E', DEnv E' N → Reach projectM
      (blkCfg "dijkstra" dijkstraF "50" (some "122") E' (Mem.set M (N + 32) (v + 1)) k) D) :
    Reach projectM (blkCfg "dijkstra" dijkstraF "121" pr E M k) D := by
  obtain ⟨e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := hE
  dnrm []
  dstp
  drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s14]
  dstp
  exact hk _ (by simp only [DEnv]; dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self])

-- One relaxation iteration, blocks 54 … 101.
set_option maxHeartbeats 1000000 in
theorem rl_iter {N V Q D0 S0 u v c : Nat} {k : Cont} {D : Config → Prop} {E : Env} {M : Mem}
    (hN : 1024 ≤ N) (hV1 : 1 ≤ V) (hV : V ≤ 15) (hQ : Q ≤ 225) (_hVQ : V ≤ Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) (hVQ' : V * V = Q)
    (hu : u < V) (hc : v < V) (hE : DEnv E N) (hS : DS M N V D0 S0)
    (_s12 : M.get (N + 24) = c) (s13 : M.get (N + 28) = u) (s14 : M.get (N + 32) = v)
    (hGv : M.get (4 * (u * V + v)) ≤ 1000) (hDv : M.get (4 * v + D0) ≤ 2147483647)
    (hdu : M.get (4 * u + D0) ≠ 2147483647 → M.get (4 * u + D0) ≤ 1073741824)
    (hk : ∀ M1, ((M1 = M ∧ ¬ (M.get (4 * v + S0) = 0 ∧ M.get (4 * (u * V + v)) ≠ 0 ∧
          M.get (4 * u + D0) ≠ 2147483647 ∧
          M.get (4 * u + D0) + M.get (4 * (u * V + v)) < M.get (4 * v + D0))) ∨
        ((M.get (4 * v + S0) = 0 ∧ M.get (4 * (u * V + v)) ≠ 0 ∧
          M.get (4 * u + D0) ≠ 2147483647 ∧
          M.get (4 * u + D0) + M.get (4 * (u * V + v)) < M.get (4 * v + D0)) ∧
          M1 = Mem.set M (4 * v + D0) (M.get (4 * u + D0) + M.get (4 * (u * V + v))))) →
      M1.get (N + 32) = v → ∀ pr E1, DEnv E1 N →
      Reach projectM (blkCfg "dijkstra" dijkstraF "121" pr E1 M1 k) D) :
    Reach projectM (blkCfg "dijkstra" dijkstraF "54" (some "50") E M k) D := by
  obtain ⟨e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := hE
  obtain ⟨s6, s7, s8, s9, s10⟩ := hS
  have hgi := gidx hu hc hVQ'
  have huV : u * V < Q := by omega
  have penv : ∀ E1 : Env, (Env.get E1 "6" = N ∧ Env.get E1 "7" = N + 4 ∧ Env.get E1 "8" = N + 8 ∧
      Env.get E1 "9" = N + 12 ∧ Env.get E1 "10" = N + 16 ∧ Env.get E1 "11" = N + 20 ∧
      Env.get E1 "12" = N + 24 ∧ Env.get E1 "13" = N + 28 ∧ Env.get E1 "14" = N + 32) →
      DEnv E1 N := fun _ h => h
  drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc]
  by_cases hs : M.get (4 * v + S0) = 0
  · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs]
    drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs]
    by_cases hg : M.get (4 * (u * V + v)) = 0
    · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg]
      exact hk M (Or.inl ⟨rfl, fun h => h.2.1 hg⟩) s14 _ _ (penv _ (by dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]))
    · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg]
      drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg]
      by_cases hd : M.get (4 * u + D0) = 2147483647
      · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg, hd]
        exact hk M (Or.inl ⟨rfl, fun h => h.2.2.1 hd⟩) s14 _ _ (penv _ (by dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]))
      · have hdu' := hdu hd
        dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg, hd]
        drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg, hd]
        by_cases hlt : M.get (4 * u + D0) + M.get (4 * (u * V + v)) < M.get (4 * v + D0)
        · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg, hd, hlt]
          drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg, hd, hlt]
          dstp
          exact hk _ (Or.inr ⟨⟨hs, hg, hd, hlt⟩, rfl⟩) (by dnrm [s14]) _ _
            (penv _ (by dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]))
        · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs, hg, hd, hlt]
          exact hk M (Or.inl ⟨rfl, fun h => hlt h.2.2.2⟩) s14 _ _
            (penv _ (by dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]))
  · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s13, s14, hc, hs]
    exact hk M (Or.inl ⟨rfl, fun h => hs h.1⟩) s14 _ _ (penv _ (by dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]))

theorem relax_loop {N V Q D0 S0 u c : Nat} {M0 : Mem} {k : Cont} {D : Config → Prop}
    (hN : 1024 ≤ N) (hV1 : 1 ≤ V) (hV : V ≤ 15) (hQ : Q ≤ 225) (hVQ : V ≤ Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) (hVQ' : V * V = Q)
    (hu : u < V) (hSu : M0.get (4 * u + S0) ≠ 0)
    (hDb : ∀ w, w < V → M0.get (4 * w + D0) ≤ 2147483647)
    (hdu : M0.get (4 * u + D0) ≠ 2147483647 → M0.get (4 * u + D0) ≤ 1073741824)
    (hG : ∀ w, w < V → M0.get (4 * (u * V + w)) ≤ 1000) :
    ∀ n v E M prev, V - v = n → DEnv E N → DS M N V D0 S0 → M.get (N + 24) = c →
      M.get (N + 28) = u → M.get (N + 32) = v → v ≤ V → M.next = M0.next →
      (∀ w, w < v → M.get (4 * w + D0) = relaxV M0 V D0 S0 u w) →
      (∀ p, p < N → (∀ w, w < v → p ≠ 4 * w + D0) → M.get p = M0.get p) →
      (∀ E' M', DEnv E' N → DS M' N V D0 S0 → M'.get (N + 24) = c → M'.get (N + 28) = u →
        M'.next = M0.next →
        (∀ w, w < V → M'.get (4 * w + D0) = relaxV M0 V D0 S0 u w) →
        (∀ p, p < N → (∀ w, w < V → p ≠ 4 * w + D0) → M'.get p = M0.get p) →
        Reach projectM (blkCfg "dijkstra" dijkstraF "125" (some "50") E' M' k) D) →
      Reach projectM (blkCfg "dijkstra" dijkstraF "50" prev E M k) D := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro v E M prev hn hE hS s12 s13 s14 hvV sN hdone hfr hk
  have hS0' := hS
  obtain ⟨e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := hE
  obtain ⟨s6, s7, s8, s9, s10⟩ := hS
  drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s14]
  by_cases hc : v < V
  · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s14, hc]
    have hgi := gidx hu hc hVQ'
    have fS : M.get (4 * v + S0) = M0.get (4 * v + S0) := hfr _ (by omega) (fun w _ => by omega)
    have fG : M.get (4 * (u * V + v)) = M0.get (4 * (u * V + v)) :=
      hfr _ (by omega) (fun w _ => by omega)
    have fDv : M.get (4 * v + D0) = M0.get (4 * v + D0) :=
      hfr _ (by omega) (fun w hw => by omega)
    have fDu : M.get (4 * u + D0) = M0.get (4 * u + D0) := by
      by_cases huv : u < v
      · rw [hdone u huv]; unfold relaxV; rw [ite_eq_right (fun h => hSu h.1)]
      · exact hfr _ (by omega) (fun w hw => by omega)
    refine rl_iter hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu hc ?_ hS0' s12 s13 s14 (by rw [fG]; exact hG v hc)
      (by rw [fDv]; exact hDb v hc) (by rw [fDu]; exact hdu) ?_
    · simp only [DEnv]; dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]
    intro M1 hM1 t14 pr E1 hE1
    have hM1v : M1.get (4 * v + D0) = relaxV M0 V D0 S0 u v := by
      unfold relaxV; rw [← fS, ← fG, ← fDu, ← fDv]
      rcases hM1 with ⟨rfl, hno⟩ | ⟨hyes, rfl⟩
      · rw [ite_eq_right hno]
      · rw [ite_eq_left hyes]; exact Mem.get_set_same _ _ _
    have hM1o : ∀ p, p ≠ 4 * v + D0 → M1.get p = M.get p := by
      intro p hp
      rcases hM1 with ⟨rfl, _⟩ | ⟨_, rfl⟩
      · rfl
      · exact Mem.get_set_other _ _ _ _ hp
    have hM1n : M1.next = M.next := by rcases hM1 with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> rfl
    refine at121 hN hE1 t14 (by omega) ?_
    intro E' hE'
    refine ih (V - (v + 1)) (by omega) (v + 1) E' _ (some "122") rfl hE' ?_ ?_ ?_ ?_ (by omega)
      ?_ ?_ ?_ hk
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (rw [Mem.get_set_other _ _ _ _ (by omega), hM1o _ (by omega)]; assumption)
    · rw [Mem.get_set_other _ _ _ _ (by omega), hM1o _ (by omega)]; exact s12
    · rw [Mem.get_set_other _ _ _ _ (by omega), hM1o _ (by omega)]; exact s13
    · exact Mem.get_set_same _ _ _
    · show (Mem.set M1 (N + 32) (v + 1)).next = _
      rw [Mem.next_set, hM1n, sN]
    · intro w hw
      rw [Mem.get_set_other _ _ _ _ (by omega)]
      by_cases hwv : w = v
      · subst hwv; exact hM1v
      · rw [hM1o _ (by omega)]; exact hdone w (by omega)
    · intro p hp hpw
      rw [Mem.get_set_other _ _ _ _ (by omega), hM1o _ (hpw v (by omega))]
      exact hfr p hp (fun w hw => hpw w (by omega))
  · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s14, hc]
    have eV : v = V := by omega
    subst eV
    exact hk _ M (by simp only [DEnv]; dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]) hS0' s12 s13 sN hdone hfr

end DijP
