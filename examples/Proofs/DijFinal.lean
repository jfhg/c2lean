import Proofs.DijMain
namespace DijP
open Ll C2Lean Dijkstra

set_option maxHeartbeats 2000000 in
theorem dijkstra_reach (V Q D0 S0 : Nat) (m₀ : Mem) (hN : 1024 ≤ m₀.next) (hV1 : 1 ≤ V)
    (hV : V ≤ 15) (hVQ' : V * V = Q) (hD0 : D0 = 4 * Q) (hS0 : S0 = D0 + 4 * V) {δ : Nat → Nat}
    (hW0 : ∀ u v, Wv m₀ V u v > 0 → u < V ∧ v < V) (hW1 : ∀ u v, Wv m₀ V u v ≤ 1000)
    (hδ : ∀ v, v < V → IsDist (Wv m₀ V) 0 v (δ v)) :
    Reach projectM (blkCfg "dijkstra" dijkstraF "0" none
      [("0", 0), ("1", D0), ("2", S0), ("3", 0), ("4", V)] m₀ Cont.top)
      (fun d => ∃ m', stepOne projectM d = StepR.fin 0 m' ∧
        ∀ v, v < V → m'.get (4 * v + D0) = δ v) := by
  have hQ : Q ≤ 225 := by
    have := Nat.mul_le_mul hV hV; omega
  have hVQ : V ≤ Q := by
    have := Nat.mul_le_mul_right V hV1; omega
  drunI []
  dstp
  refine init_loop (m0 := m₀) hN hV1 hV hQ hVQ hD0 hS0 (V - 0) 0 _ _ (some "0") rfl ?_ ?_
    (by dnrm []) (by omega) (by dnrm []) (fun w hw => by omega) (fun p hp _ => by dnrm []) ?_
  · simp only [DEnv]; dnrm [and_self]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dnrm []
  intro E' M' hE' hS' sN' hdone hfr
  obtain ⟨e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := hE'
  obtain ⟨s6, s7, s8, s9, s10⟩ := hS'
  drunI [e6, e7, e8, e9, e10, e11, e12, e13, e14, s6, s7, s8, s9, s10, Nat.mul_zero, Nat.zero_add]
  dstp
  dsimp only
  refine main_loop (m₀ := m₀) hN hV1 hV hQ hVQ hD0 hS0 hVQ' hW0 hW1 hδ ((V - 1) - 0) 0 _ _ (some "31")
    rfl (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [DEnv]; dnrm [e6, e7, e8, e9, e10, e11, e12, e13, e14, and_self]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dnrm [s6, s7, s8, s9, s10]
  · exact Mem.get_set_same _ _ _
  · simp only [Mem.next_set]; omega
  · intro u v hu hv
    have := gidx hu hv hVQ'
    rw [Mem.get_set_other _ (m₀.next + 24) (4 * (u * V + v)) 0 (by omega),
      Mem.get_set_other _ D0 (4 * (u * V + v)) 0 (by omega),
      hfr (4 * (u * V + v)) (by omega) (fun w _ => ⟨by omega, by omega⟩), Nat.mul_comm u V]
  · apply dinv_init ⟨hV1, hV⟩ hW0 hW1 hδ
    · intro v hv
      show (Mem.set (Mem.set M' D0 0) (m₀.next + 24) 0).get (4 * v + S0) = 0
      rw [Mem.get_set_other _ _ _ _ (by omega), Mem.get_set_other _ _ _ _ (by omega)]
      exact (hdone v hv).2
    · intro v hv
      show (Mem.set (Mem.set M' D0 0) (m₀.next + 24) 0).get (4 * v + D0) = _
      rw [Mem.get_set_other _ _ _ _ (by omega)]
      by_cases h0 : v = 0
      · subst h0; rw [ite_eq_left rfl, show 4 * 0 + D0 = D0 by omega]; exact Mem.get_set_same _ _ _
      · rw [ite_eq_right h0, Mem.get_set_other _ _ _ _ (by omega)]; exact (hdone v hv).1
  intro E2 M2 hI
  dnrm []
  apply Reach.done
  exact ⟨M2, rfl, dinv_final ⟨hV1, hV⟩ hW0 hW1 hδ hV1 hI⟩

end DijP

namespace Dijkstra
open Ll C2Lean DijP

/-- Admissible inputs, stated for the graph restricted to the `V` real vertices
    (no phantom-edge clause needed: `Wv` has no phantom edges by construction). -/
def GraphAtV (V : Nat) (m₀ : Mem) : Prop :=
  (∀ u v, u < V → v < V → Wv m₀ V u v ≤ 1000) ∧
  (∀ v, v < V → ∃ d, IsDist (Wv m₀ V) 0 v d)

/-- **Correctness for every `1 ≤ V ≤ 15`.**  Changes w.r.t. `dijkstra_correct_type`:
    the weight function is `Wv` (= `Wm` guarded by `u, v < V`) and
    `1024 ≤ m₀.next` (frames above the caller's arrays). -/
theorem dijkstra_correct_fixed : ∀ (V : Nat) (m₀ : Mem), 1 ≤ V → V ≤ 15 → GraphAtV V m₀ →
    1024 ≤ m₀.next →
    ∃ (fuel result : Nat) (m : Mem),
      runModule projectM "dijkstra" [0, 4 * V * V, 4 * V * V + 4 * V, 0, V] fuel m₀ =
        Res.val result m ∧
      result = 0 ∧
      (∀ v, v < V → IsDist (Wv m₀ V) 0 v (m.get (4 * V * V + 4 * v))) := by
  intro V m₀ hV1 hV ⟨hW, hreach⟩ hN
  let δ : Nat → Nat := fun v => if h : v < V then Classical.choose (hreach v h) else 0
  have hδ : ∀ v, v < V → IsDist (Wv m₀ V) 0 v (δ v) := by
    intro v hv
    show IsDist (Wv m₀ V) 0 v (if h : v < V then Classical.choose (hreach v h) else 0)
    rw [dite_eq_left hv]; exact Classical.choose_spec (hreach v hv)
  have hW0 : ∀ u v, Wv m₀ V u v > 0 → u < V ∧ v < V := fun u v h => Wv_pos h
  have hW1 : ∀ u v, Wv m₀ V u v ≤ 1000 := by
    intro u v
    by_cases h : u < V ∧ v < V
    · exact hW u v h.1 h.2
    · unfold Wv; rw [ite_eq_right h]; omega
  obtain ⟨n, d, ⟨m', hfin, hdist⟩, hrun⟩ :=
    (dijkstra_reach V (V * V) (4 * V * V) (4 * V * V + 4 * V) m₀ hN hV1 hV rfl
      (Nat.mul_assoc 4 V V) rfl hW0 hW1 hδ).runM
  refine ⟨1 + n, 0, m', ?_, rfl, ?_⟩
  · have h1 := hrun 1
    have h2 : Ll.runM 1 projectM d = Res.val 0 m' := by rw [runM_succ, hfin]
    exact h1.trans h2
  · intro v hv
    rw [Nat.add_comm, hdist v hv]
    exact hδ v hv

/-- Under the uploaded `GraphAt` (whose phantom-edge clause makes `Wm = Wv`),
    the uploaded statement holds once `1024 ≤ m₀.next` is added. -/
theorem dijkstra_correct_with_next : ∀ (V : Nat) (m₀ : Mem), 1 ≤ V → V ≤ 15 → GraphAt V m₀ →
    1024 ≤ m₀.next →
    ∃ (fuel result : Nat) (m : Mem),
      runModule projectM "dijkstra" [0, 4 * V * V, 4 * V * V + 4 * V, 0, V] fuel m₀ =
        Res.val result m ∧
      result = 0 ∧
      (∀ v, v < V → IsDist (Wm m₀ V) 0 v (m.get (4 * V * V + 4 * v))) := by
  intro V m₀ hV1 hV ⟨hW, hph, hreach⟩ hN
  have e : Wm m₀ V = Wv m₀ V := by
    funext u v
    unfold Wv
    split
    · rfl
    · exact hph u v (by omega)
  rw [e] at hW hreach ⊢
  exact dijkstra_correct_fixed V m₀ hV1 hV ⟨hW, hreach⟩ hN

/-- The phantom-edge clause of `GraphAt` is much stronger than intended: it
    forces every word at an address `4·a` with `a ≥ V` to be zero — in
    particular every graph row except row 0 (only edges `0 → v` survive). -/
theorem graphAt_forces_zero (V : Nat) (m₀ : Mem) (h : GraphAt V m₀) :
    ∀ a, V ≤ a → m₀.get (4 * a) = 0 := by
  intro a ha
  have := h.2.1 0 a (Or.inr ha)
  simpa [Wm] using this

theorem graphAt_star (V : Nat) (m₀ : Mem) (h : GraphAt V m₀) :
    ∀ u v, 1 ≤ u → Wm m₀ V u v = 0 := by
  intro u v hu
  have : V ≤ V * u + v := by
    have := Nat.mul_le_mul_left V hu; omega
  exact graphAt_forces_zero V m₀ h _ this

end Dijkstra
