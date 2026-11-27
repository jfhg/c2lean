import Proofs.DijLoops
import Proofs.DijGraph
namespace DijP
open Ll C2Lean Dijkstra

/-- The graph restricted to the `V` real vertices. -/
def Wv (m₀ : Mem) (V : Nat) : Dijkstra.W :=
  fun u v => if u < V ∧ v < V then m₀.get (4 * (V * u + v)) else 0

theorem Wv_pos {m₀ : Mem} {V u v : Nat} (h : Wv m₀ V u v > 0) : u < V ∧ v < V := by
  unfold Wv at h; split at h
  · assumption
  · omega

/-- Memory at the start of the relaxation loop. -/
def M0r (M1 : Mem) (N S0 u : Nat) : Mem :=
  Mem.set (Mem.set (Mem.set M1 (N + 28) u) (4 * u + S0) 1) (N + 32) 0

theorem m0r_reads {M M1 : Mem} {N V Q D0 S0 u : Nat} (hN : 1024 ≤ N) (hV1 : 1 ≤ V) (hV : V ≤ 15) (hQ : Q ≤ 225) (_hVQ : V ≤ Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) (hVQ' : V * V = Q) (hu : u < V)
    (g : ∀ p, p < N + 36 → M1.get p = M.get p) :
    (∀ w, w < V → (M0r M1 N S0 u).get (4 * w + S0) = if w = u then 1 else M.get (4 * w + S0)) ∧
    (∀ w, w < V → (M0r M1 N S0 u).get (4 * w + D0) = M.get (4 * w + D0)) ∧
    (∀ a b, a < V → b < V → (M0r M1 N S0 u).get (4 * (a * V + b)) = M.get (4 * (a * V + b))) := by
  unfold M0r
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    by_cases hwu : w = u
    · subst hwu; dnrm []
    · rw [ite_eq_right hwu]; dnrm []; exact g (4 * w + S0) (by omega)
  · intro w hw; dnrm []; exact g (4 * w + D0) (by omega)
  · intro a b ha hb
    have := gidx ha hb hVQ'
    dnrm []; exact g (4 * (a * V + b)) (by omega)

theorem relaxV_eq {M M1 : Mem} {N V Q D0 S0 u : Nat} (hN : 1024 ≤ N) (hV1 : 1 ≤ V) (hV : V ≤ 15) (hQ : Q ≤ 225) (hVQ : V ≤ Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) (hVQ' : V * V = Q) (hu : u < V)
    (g : ∀ p, p < N + 36 → M1.get p = M.get p) (w : Nat) (hw : w < V) :
    relaxV (M0r M1 N S0 u) V D0 S0 u w = relaxF (fun a b => M.get (4 * (a * V + b)))
      (fun v => M.get (4 * v + D0)) (fun w => if w = u then 1 else M.get (4 * w + S0)) u w := by
  obtain ⟨r1, r2, r3⟩ := m0r_reads hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu g
  unfold relaxV relaxF
  rw [r1 w hw, r2 w hw, r2 u hu, r3 u w hu hw]

theorem round_facts {M M1 M' : Mem} {N V Q D0 S0 u c : Nat} (hN : 1024 ≤ N) (hV1 : 1 ≤ V) (hV : V ≤ 15) (hQ : Q ≤ 225) (hVQ : V ≤ Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) (hVQ' : V * V = Q) (hu : u < V)
    (g : ∀ p, p < N + 36 → M1.get p = M.get p) (hn1 : M1.next = M.next + 24)
    (hn' : M'.next = (M0r M1 N S0 u).next)
    (hrel : ∀ w, w < V → M'.get (4 * w + D0) = relaxV (M0r M1 N S0 u) V D0 S0 u w)
    (hfr' : ∀ p, p < N → (∀ w, w < V → p ≠ 4 * w + D0) → M'.get p = (M0r M1 N S0 u).get p) :
    M.next ≤ (Mem.set M' (N + 24) (c + 1)).next ∧
    (∀ w, w < V → (Mem.set M' (N + 24) (c + 1)).get (4 * w + S0) =
      if w = u then 1 else M.get (4 * w + S0)) ∧
    (∀ w, w < V → (Mem.set M' (N + 24) (c + 1)).get (4 * w + D0) =
      relaxF (fun a b => M.get (4 * (a * V + b))) (fun v => M.get (4 * v + D0))
        (fun w => if w = u then 1 else M.get (4 * w + S0)) u w) ∧
    (∀ a b, a < V → b < V →
      (Mem.set M' (N + 24) (c + 1)).get (4 * (a * V + b)) = M.get (4 * (a * V + b))) := by
  obtain ⟨r1, r2, r3⟩ := m0r_reads hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu g
  have h0 : (M0r M1 N S0 u).next = M1.next := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Mem.next_set, hn', h0]; omega
  · intro w hw
    rw [Mem.get_set_other M' (N + 24) (4 * w + S0) (c + 1) (by omega),
      hfr' (4 * w + S0) (by omega) (fun x _ => by omega)]
    exact r1 w hw
  · intro w hw
    rw [Mem.get_set_other M' (N + 24) (4 * w + D0) (c + 1) (by omega), hrel w hw]
    exact relaxV_eq hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu g w hw
  · intro a b ha hb
    have := gidx ha hb hVQ'
    rw [Mem.get_set_other M' (N + 24) (4 * (a * V + b)) (c + 1) (by omega),
      hfr' (4 * (a * V + b)) (by omega) (fun x _ => by omega)]
    exact r3 a b ha hb

set_option maxHeartbeats 2000000 in
/-- One round of the `count` loop: blocks 41 … 126. -/
theorem at41 {N V Q D0 S0 c : Nat} {k : Cont} {D : Config → Prop} {E : Env} {M : Mem}
    (hN : 1024 ≤ N) (hV1 : 1 ≤ V) (hV : V ≤ 15) (hQ : Q ≤ 225) (hVQ : V ≤ Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) (hVQ' : V * V = Q) (hc : c < V) (hE : DEnv E N) (hS : DS M N V D0 S0) (s12 : M.get (N + 24) = c)
    (sN : N + 36 ≤ M.next)
    (hDb : ∀ w, w < V → M.get (4 * w + D0) ≤ 2147483647)
    (hex : ∃ w, w < V ∧ M.get (4 * w + S0) = 0)
    (hdu : ∀ u, u < V → M.get (4 * u + D0) ≠ 2147483647 → M.get (4 * u + D0) ≤ 1073741824)
    (hG : ∀ a b, a < V → b < V → M.get (4 * (a * V + b)) ≤ 1000)
    (hk : ∀ u E' M', u < V → M.get (4 * u + S0) = 0 →
      (∀ w, w < V → M.get (4 * w + S0) = 0 → M.get (4 * u + D0) ≤ M.get (4 * w + D0)) →
      DEnv E' N → DS M' N V D0 S0 → M'.get (N + 24) = c + 1 → N + 36 ≤ M'.next →
      (∀ w, w < V → M'.get (4 * w + S0) = if w = u then 1 else M.get (4 * w + S0)) →
      (∀ w, w < V → M'.get (4 * w + D0) = relaxF (fun a b => M.get (4 * (a * V + b)))
        (fun v => M.get (4 * v + D0)) (fun w => if w = u then 1 else M.get (4 * w + S0)) u w) →
      (∀ a b, a < V → b < V → M'.get (4 * (a * V + b)) = M.get (4 * (a * V + b))) →
      Reach projectM (blkCfg "dijkstra" dijkstraF "36" (some "126") E' M' k) D) :
    Reach projectM (blkCfg "dijkstra" dijkstraF "41" (some "36") E M k) D := by
  obtain ⟨e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := hE
  obtain ⟨s6, s7, s8, s9, s10⟩ := hS
  drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s12]
  apply md_call (by dnrm [e7, s7]) (by dnrm [e8, s8]) (by dnrm [e10, s10]) (by omega) hV
    (by omega) (by omega) hDb hex
  intro M1 u hn1 hfr1 hu hSu hmin
  have g : ∀ p, p < N + 36 → M1.get p = M.get p := fun p hp => hfr1 p (by omega)
  have t6 := g N (by omega); have t7 := g (N + 4) (by omega); have t8 := g (N + 8) (by omega)
  have t9 := g (N + 12) (by omega); have t10 := g (N + 16) (by omega)
  have t12 := g (N + 24) (by omega)
  rw [s6] at t6; rw [s7] at t7; rw [s8] at t8; rw [s9] at t9; rw [s10] at t10; rw [s12] at t12
  drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, t6, t7, t8, t9, t10, t12]
  dstp
  dsimp only
  obtain ⟨r1, r2, r3⟩ := m0r_reads hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu g
  refine relax_loop (c := c) (M0 := M0r M1 N S0 u)
    hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu (by rw [r1 u hu, ite_eq_left rfl]; omega)
    (fun w hw => by rw [r2 w hw]; exact hDb w hw)
    (by rw [r2 u hu]; exact hdu u hu) (fun w hw => by rw [r3 u w hu hw]; exact hG u w hu hw)
    (V - 0) 0 _ _ (some "41") rfl ?_ ?_ ?_ ?_ ?_ (by omega) rfl
    (fun w hw => by omega) (fun p _ _ => rfl) ?_
  · simp only [DEnv]; dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (dnrm [M0r, t6, t7, t8, t9, t10])
  · dnrm [M0r, t12]
  · dnrm [M0r]
  · dnrm [M0r]
  intro E' M' hE' hS' s12' s13' hn' hrel hfr'
  obtain ⟨f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ := hE'
  obtain ⟨u6, u7, u8, u9, u10⟩ := hS'
  dstp
  drunI [f6, f7, f8, f9, f10, f11, f12, f13, f14, u6, u7, u8, u9, u10, s12']
  dstp
  dsimp only
  refine hk u _ (Mem.set M' (N + 24) (c + 1)) hu hSu hmin ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [DEnv]; dnrm [f6, f7, f8, f9, f10, f11, f12, f13, f14, and_self]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dnrm [u6, u7, u8, u9, u10]
  · exact Mem.get_set_same _ _ _
  · exact Nat.le_trans sN (round_facts hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu g hn1 hn' hrel hfr').1
  · exact (round_facts hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu g hn1 hn' hrel hfr').2.1
  · exact (round_facts hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu g hn1 hn' hrel hfr').2.2.1
  · exact (round_facts hN hV1 hV hQ hVQ hD0 hS0 hVQ' hu g hn1 hn' hrel hfr').2.2.2

theorem main_loop {N V Q D0 S0 : Nat} {m₀ : Mem} {δ : Nat → Nat} {k : Cont} {D : Config → Prop}
    (hN : 1024 ≤ N) (hV1 : 1 ≤ V) (hV : V ≤ 15) (hQ : Q ≤ 225) (hVQ : V ≤ Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) (hVQ' : V * V = Q)
    (hW0 : ∀ u v, Wv m₀ V u v > 0 → u < V ∧ v < V) (hW1 : ∀ u v, Wv m₀ V u v ≤ 1000)
    (hδ : ∀ v, v < V → IsDist (Wv m₀ V) 0 v (δ v)) :
    ∀ n c E M prev, (V - 1) - c = n → c ≤ V - 1 → DEnv E N → DS M N V D0 S0 →
      M.get (N + 24) = c → N + 36 ≤ M.next →
      (∀ u v, u < V → v < V → M.get (4 * (u * V + v)) = m₀.get (4 * (V * u + v))) →
      DInv (Wv m₀ V) δ V (fun v => M.get (4 * v + D0)) (fun v => M.get (4 * v + S0)) c →
      (∀ E' M', DInv (Wv m₀ V) δ V (fun v => M'.get (4 * v + D0)) (fun v => M'.get (4 * v + S0))
          (V - 1) →
        Reach projectM (blkCfg "dijkstra" dijkstraF "129" (some "36") E' M' k) D) →
      Reach projectM (blkCfg "dijkstra" dijkstraF "36" prev E M k) D := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c E M prev hn hcV E0 hS s12 sN hgr hI hk
  have hE0 := E0
  have hS0' := hS
  obtain ⟨e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := E0
  obtain ⟨s6, s7, s8, s9, s10⟩ := hS
  have J2 := hI.2.1
  have J6 := hI.2.2.2.2.2.1
  have hgW : ∀ a b, a < V → b < V → M.get (4 * (a * V + b)) = Wv m₀ V a b := by
    intro a b ha hb; rw [hgr a b ha hb]; unfold Wv; rw [ite_eq_left ⟨ha, hb⟩]
  drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s12]
  by_cases hc : c < V - 1
  · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s12, hc]
    refine at41 hN hV1 hV hQ hVQ hD0 hS0 hVQ' (by omega) ?_ hS0' s12 sN ?_ ?_ ?_ ?_ ?_
    · simp only [DEnv]; dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]
    · intro w hw; rcases J6 w hw with h | h
      · simp only at h; omega
      · simp only at h; omega
    · obtain ⟨w, hw, hpw⟩ := countP_exists (fun v => M.get (4 * v + S0) != 0) V
        (by simp only at J2; omega)
      exact ⟨w, hw, by simpa using hpw⟩
    · intro u hu h; rcases J6 u hu with h' | h'
      · exact absurd h' h
      · simp only at h'; omega
    · intro a b ha hb; rw [hgW a b ha hb]; exact hW1 a b
    intro u E' M' hu hSu hmin hE' hS' s12' sN' hSp hDp hgr'
    refine ih ((V - 1) - (c + 1)) (by omega) (c + 1) E' M' (some "126") rfl (by omega) hE' hS' s12'
      sN' (fun a b ha hb => by rw [hgr' a b ha hb]; exact hgr a b ha hb) ?_ hk
    refine dinv_congr (by omega) (dinv_step ⟨hV1, hV⟩ hW0 hW1 hδ hI hu hSu hmin) ?_
      (fun v hv => hSp v hv)
    intro v hv
    show M'.get (4 * v + D0) = _
    rw [hDp v hv]
    unfold relaxF
    simp only
    rw [hgW u v hu hv]
  · dbrn [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, s12, hc]
    have : c = V - 1 := by omega
    subst this
    exact hk _ M hI

end DijP
