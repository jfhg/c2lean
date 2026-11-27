import Proofs.DijkstraSpec
/-! Pure (machine-free) Dijkstra correctness argument. -/
namespace Dijkstra

theorem walkWeight_cons2 (W : W) (a b : Nat) (t : List Nat) :
    walkWeight W (a :: b :: t) = W b a + walkWeight W (b :: t) := rfl

theorem walk_ne_nil {W : W} {s : Nat} {vs : List Nat} (h : Walk W s vs) : vs ≠ [] := by
  cases h <;> simp

/-- First vertex outside a set containing the source, on any walk ending outside it. -/
theorem first_outside (W : W) (S : Nat → Prop) (δ : Nat → Nat)
    (hδ : ∀ y, S y → ∀ vs, Walk W 0 vs → vs.head? = some y → δ y ≤ walkWeight W vs)
    (h0 : S 0) :
    ∀ vs, Walk W 0 vs → ∀ v, vs.head? = some v → ¬ S v →
      ∃ x y, ¬ S x ∧ S y ∧ W y x > 0 ∧ δ y + W y x ≤ walkWeight W vs := by
  intro vs hw
  induction hw with
  | single =>
    intro v hv hS
    simp at hv; subst hv; exact absurd h0 hS
  | @extend u v vs h huv ih =>
    intro v' hv hS
    have hv' : v' = v := by simp at hv; exact hv.symm
    rw [hv'] at hS
    by_cases hu : S u
    · refine ⟨v, u, hS, hu, huv, ?_⟩
      rw [walkWeight_cons2]
      have := hδ u hu _ h rfl
      omega
    · obtain ⟨x, y, hx, hy, hxy, hle⟩ := ih u rfl hu
      refine ⟨x, y, hx, hy, hxy, ?_⟩
      rw [walkWeight_cons2]; omega

/-! counting -/

theorem countP_update (p : Nat → Bool) (u : Nat) (hu : p u = false) :
    ∀ n, u < n → (List.range n).countP (fun v => p v || v == u) = (List.range n).countP p + 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    rw [List.range_succ, List.countP_append, List.countP_append]
    by_cases hun : u = n
    · subst hun
      have : (List.range u).countP (fun v => p v || v == u) = (List.range u).countP p := by
        apply List.countP_congr
        intro x hx
        rw [List.mem_range] at hx
        have : (x == u) = false := by simp; omega
        simp [this]
      rw [this]; simp [hu]
    · rw [ih (by omega)]
      have : (n == u) = false := by simp; omega
      simp [this]; omega

theorem countP_le (p : Nat → Bool) (n : Nat) : (List.range n).countP p ≤ n := by
  have := List.countP_le_length (p := p) (l := List.range n); simpa using this

theorem countP_exists (p : Nat → Bool) (n : Nat) (h : (List.range n).countP p < n) :
    ∃ v, v < n ∧ p v = false := by
  apply Classical.byContradiction
  intro hc
  have : (List.range n).countP p = n := by
    rw [List.countP_eq_length.mpr]
    · simp
    · intro x hx
      rw [List.mem_range] at hx
      cases hpx : p x
      · exact absurd ⟨x, hx, hpx⟩ hc
      · rfl
  omega

theorem countP_lt_of (p : Nat → Bool) (n z : Nat) (hz : z < n) (hpz : p z = false) :
    (List.range n).countP p + 1 ≤ n := by
  have h1 := countP_le p n
  apply Classical.byContradiction
  intro hc
  have hall : (List.range n).countP p = n := by omega
  have h2 : (List.range n).countP p = (List.range n).length := by simp [hall]
  rw [List.countP_eq_length] at h2
  have := h2 z (List.mem_range.mpr hz)
  simp [hpz] at this

theorem countP_two (p : Nat → Bool) (x z : Nat) (hxz : x ≠ z) (hx : p x = false) (hz : p z = false) :
    ∀ n, x < n → z < n → (List.range n).countP p + 2 ≤ n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h1 h2
    rw [List.range_succ, List.countP_append]
    by_cases hxn : x = n
    · subst hxn
      have := countP_lt_of p x z (by omega) hz
      simp [hx]; omega
    · by_cases hzn : z = n
      · subst hzn
        have := countP_lt_of p z x (by omega) hx
        simp [hz]; omega
      · have := ih (by omega) (by omega)
        have : (List.countP p [n]) ≤ 1 := by simp; split <;> omega
        omega

/-! ## The Dijkstra invariant -/

def DInv (W : W) (δ : Nat → Nat) (V : Nat) (Df Sf : Nat → Nat) (c : Nat) : Prop :=
  (∀ v, v < V → Sf v = 0 ∨ Sf v = 1) ∧
  (List.range V).countP (fun v => Sf v != 0) = c ∧
  (∀ v, v < V → Sf v ≠ 0 → Df v = δ v) ∧
  (∀ v, v < V → Df v ≠ 2147483647 →
    ∃ vs, Walk W 0 vs ∧ vs.head? = some v ∧ walkWeight W vs = Df v) ∧
  (∀ v, v < V → Sf v = 0 → ∀ y, y < V → Sf y ≠ 0 → W y v > 0 → Df v ≤ δ y + W y v) ∧
  (∀ v, v < V → Df v = 2147483647 ∨ Df v ≤ 1000 * c) ∧
  Df 0 = 0 ∧
  (∀ v, v < V → Sf v ≠ 0 → Df v ≠ 2147483647)

/-- one Dijkstra round: settle `u`, relax its edges. -/
def relaxF (W : W) (Df Sf : Nat → Nat) (u w : Nat) : Nat :=
  if Sf w = 0 ∧ W u w ≠ 0 ∧ Df u ≠ 2147483647 ∧ Df u + W u w < Df w then Df u + W u w else Df w

theorem relaxF_le {W : W} (Df Sf : Nat → Nat) (u w : Nat) : relaxF W Df Sf u w ≤ Df w := by
  unfold relaxF; split <;> omega

theorem dinv_congr {W : W} {δ : Nat → Nat} {V : Nat} {Df Sf Df' Sf' : Nat → Nat} {c : Nat}
    (h0V : 0 < V) (hI : DInv W δ V Df Sf c) (hD : ∀ v, v < V → Df' v = Df v) (hS : ∀ v, v < V → Sf' v = Sf v) :
    DInv W δ V Df' Sf' c := by
  obtain ⟨J1, J2, J3, J4, J5, J6, J8, J9⟩ := hI
  refine ⟨fun v hv => by rw [hS v hv]; exact J1 v hv, ?_, fun v hv h => by
      rw [hD v hv]; exact J3 v hv (by rwa [← hS v hv]),
    fun v hv h => by rw [hD v hv] at h ⊢; exact J4 v hv h,
    fun v hv h y hy hy' hyv => by
      rw [hD v hv]; exact J5 v hv (by rwa [← hS v hv]) y hy (by rwa [← hS y hy]) hyv,
    fun v hv => by rw [hD v hv]; exact J6 v hv, by rw [hD 0 (by omega)]; exact J8,
    fun v hv h => by rw [hD v hv]; exact J9 v hv (by rwa [← hS v hv])⟩
  rw [← J2]
  apply List.countP_congr
  intro x hx; rw [List.mem_range] at hx; rw [hS x hx]

section
variable {W : W} {δ : Nat → Nat} {V : Nat}
  (hV : 1 ≤ V ∧ V ≤ 15) (hW0 : ∀ u v, W u v > 0 → u < V ∧ v < V) (hW1 : ∀ u v, W u v ≤ 1000)
  (hδ : ∀ v, v < V → IsDist W 0 v (δ v))
include hV hW0 hW1 hδ

omit hW0 hW1 in theorem delta_zero : δ 0 = 0 := by
  have := (hδ 0 (by omega)).2 [0] (Walk.single W 0) rfl
  simp [walkWeight] at this; omega

set_option linter.unusedSectionVars false in
theorem dinv_init (Df Sf : Nat → Nat) (hS : ∀ v, v < V → Sf v = 0)
    (hD : ∀ v, v < V → Df v = if v = 0 then 0 else 2147483647) :
    DInv W δ V Df Sf 0 := by
  refine ⟨fun v hv => Or.inl (hS v hv), ?_, fun v hv h => absurd (hS v hv) h, ?_,
    fun v _ _ y hy h => absurd (hS y hy) h, ?_, ?_, fun v hv h => absurd (hS v hv) h⟩
  · rw [List.countP_eq_zero]
    intro v hv; rw [List.mem_range] at hv; simp [hS v hv]
  · intro v hv hne
    rw [hD v hv] at hne ⊢
    by_cases h0 : v = 0
    · subst h0; exact ⟨[0], Walk.single W 0, rfl, rfl⟩
    · simp [h0] at hne
  · intro v hv; rw [hD v hv]; split <;> simp
  · rw [hD 0 (by omega)]; simp

theorem dinv_select {Df Sf : Nat → Nat} {c : Nat} (hI : DInv W δ V Df Sf c)
    {u : Nat} (hu : u < V) (hSu : Sf u = 0)
    (hmin : ∀ w, w < V → Sf w = 0 → Df u ≤ Df w) :
    Df u = δ u ∧ Df u ≠ 2147483647 ∧ Df u ≤ 1000 * c := by
  obtain ⟨J1, J2, J3, J4, J5, J6, J8, J9⟩ := hI
  have key : Df u ≤ 16000 ∧ Df u ≤ δ u := by
    by_cases h0 : Sf 0 = 0
    · have := hmin 0 (by omega) h0
      rw [J8] at this
      exact ⟨by omega, by omega⟩
    · obtain ⟨vs, hw, hh, hwt⟩ := (hδ u hu).1
      obtain ⟨x, y, hx, hy, hxy, hle⟩ := first_outside W (fun y => y < V ∧ Sf y ≠ 0) δ
        (fun y hy vs hw hh => (hδ y hy.1).2 vs hw hh) ⟨by omega, h0⟩ vs hw u hh
        (fun h => h.2 hSu)
      have hxy9 := hW0 y x hxy
      have hSx : Sf x = 0 := by
        rcases J1 x hxy9.2 with h | h
        · exact h
        · exact absurd ⟨hxy9.2, by omega⟩ hx
      have h5 := J5 x hxy9.2 hSx y hy.1 hy.2 hxy
      have hux := hmin x hxy9.2 hSx
      have h3 := J3 y hy.1 hy.2
      have h9 := J9 y hy.1 hy.2
      have h6 := J6 y hy.1
      have hc9 : c ≤ V := by have := countP_le (fun v => Sf v != 0) V; omega
      have := hW1 y x
      rcases h6 with h6 | h6
      · exact absurd h6 h9
      · exact ⟨by rw [h3] at h6; have : 1000 * c ≤ 15000 := by omega
                  omega, by omega⟩
  have hne : Df u ≠ 2147483647 := by omega
  obtain ⟨vs, hw, hh, hwt⟩ := J4 u hu hne
  have := (hδ u hu).2 vs hw hh
  refine ⟨by omega, hne, ?_⟩
  rcases J6 u hu with h | h
  · exact absurd h hne
  · exact h

theorem dinv_step {Df Sf : Nat → Nat} {c : Nat} (hI : DInv W δ V Df Sf c)
    {u : Nat} (hu : u < V) (hSu : Sf u = 0)
    (hmin : ∀ w, w < V → Sf w = 0 → Df u ≤ Df w) :
    DInv W δ V (relaxF W Df (fun w => if w = u then 1 else Sf w) u)
      (fun w => if w = u then 1 else Sf w) (c + 1) := by
  obtain ⟨hdu, hduI, hduc⟩ := dinv_select hV hW0 hW1 hδ hI hu hSu hmin
  obtain ⟨J1, J2, J3, J4, J5, J6, J8, J9⟩ := hI
  have hunch : ∀ w, ((fun w => if w = u then 1 else Sf w) w) ≠ 0 →
      relaxF W Df (fun w => if w = u then 1 else Sf w) u w = Df w := by
    intro w hw; unfold relaxF; rw [ite_eq_right (fun h => hw h.1)]
  have hDu' : relaxF W Df (fun w => if w = u then 1 else Sf w) u u = Df u := hunch u (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp only; split
    · exact Or.inr rfl
    · exact J1 v hv
  · rw [← J2]
    have := countP_update (fun v => Sf v != 0) u (by simp [hSu]) V hu
    rw [← this]
    apply List.countP_congr
    intro x _
    by_cases hx : x = u
    · subst hx; simp
    · simp [hx]
  · intro v hv hne
    rw [hunch v hne]
    by_cases hvu : v = u
    · subst hvu; exact hdu
    · simp only [hvu, ite_false] at hne; exact J3 v hv hne
  · intro v hv hne
    unfold relaxF at hne ⊢
    split
    · rename_i hcond
      obtain ⟨vs, hw, hh, hwt⟩ := J4 u hu hduI
      have hvs : vs = u :: vs.tail := by
        cases vs with
        | nil => simp at hh
        | cons a t => simp at hh; subst hh; rfl
      refine ⟨v :: vs, ?_, rfl, ?_⟩
      · rw [hvs]; rw [hvs] at hw; exact Walk.extend hw (by omega)
      · rw [hvs, walkWeight_cons2, ← hvs, hwt]; omega
    · rename_i hcond
      rw [ite_eq_right hcond] at hne
      exact J4 v hv hne
  · intro v hv hSv y hy hSy hyv
    have hvu : v ≠ u := by intro h; subst h; simp at hSv
    have hSv' : Sf v = 0 := by simpa [hvu] using hSv
    by_cases hyu : y = u
    · subst hyu
      rw [← hdu]
      unfold relaxF
      split
      · omega
      · rename_i hcond
        apply Classical.byContradiction
        intro hlt
        exact hcond ⟨hSv, by omega, hduI, by omega⟩
    · have hSy' : Sf y ≠ 0 := by simpa [hyu] using hSy
      have := relaxF_le (W := W) Df (fun w => if w = u then 1 else Sf w) u v
      have := J5 v hv hSv' y hy hSy' hyv
      omega
  · intro v hv
    unfold relaxF
    split
    · have := hW1 u v; right; omega
    · rcases J6 v hv with h | h
      · exact Or.inl h
      · right; omega
  · unfold relaxF
    rw [ite_eq_right (fun h => by omega)]; exact J8
  · intro v hv hne
    rw [hunch v hne]
    by_cases hvu : v = u
    · subst hvu; exact hduI
    · simp only [hvu, ite_false] at hne; exact J9 v hv hne

theorem dinv_final {Df Sf : Nat → Nat} (_hV1 : 1 ≤ V) (hI : DInv W δ V Df Sf (V - 1)) :
    ∀ v, v < V → Df v = δ v := by
  obtain ⟨J1, J2, J3, J4, J5, J6, J8, J9⟩ := hI
  intro v hv
  by_cases hSv : Sf v ≠ 0
  · exact J3 v hv hSv
  have hSv : Sf v = 0 := by omega
  have uniq : ∀ x, x < V → Sf x = 0 → x = v := by
    intro x hx hSx
    apply Classical.byContradiction
    intro hne
    have := countP_two (fun v => Sf v != 0) x v hne (by simp [hSx]) (by simp [hSv]) V hx hv
    omega
  by_cases h0 : Sf 0 = 0
  · have := uniq 0 (by omega) h0
    subst this
    rw [J8, delta_zero hV hδ]
  · obtain ⟨vs, hw, hh, hwt⟩ := (hδ v hv).1
    obtain ⟨x, y, hx, hy, hxy, hle⟩ := first_outside W (fun y => y < V ∧ Sf y ≠ 0) δ
      (fun y hy vs hw hh => (hδ y hy.1).2 vs hw hh) ⟨by omega, h0⟩ vs hw v hh
      (fun h => h.2 hSv)
    have hxy9 := hW0 y x hxy
    have hSx : Sf x = 0 := by
      rcases J1 x hxy9.2 with h | h
      · exact h
      · exact absurd ⟨hxy9.2, by omega⟩ hx
    have hxv := uniq x hxy9.2 hSx
    subst hxv
    have h5 := J5 x hv hSv y hy.1 hy.2 hxy
    have h3 := J3 y hy.1 hy.2
    have h9 := J9 y hy.1 hy.2
    have := hW1 y x
    rcases J6 y hy.1 with h6 | h6
    · exact absurd h6 h9
    · have hne : Df x ≠ 2147483647 := by omega
      obtain ⟨vs', hw', hh', hwt'⟩ := J4 x hv hne
      have := (hδ x hv).2 vs' hw' hh'
      omega

end

end Dijkstra
