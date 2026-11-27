import C2Lean.Programs
import Proofs.Reach
/-!
# `sort_cspec` for qsort.c — refutation and corrected proof

The ORIGINAL generated `sort_cspec` was **false** (§1, reproduced verbatim
as `SortCSpec` with two machine-checked counterexamples):
* values ≥ 2^31: the C code compares with *signed* `icmp`, `SortedAt` uses `Nat` `≤`;
* `m₀.next < 1024`: the `alloca` frame overlaps the caller's array.

Both hypotheses (`1024 <= m₀.next`, `SmallAt old c:a c:n`) now live in the
`qsort.c` spec comment, so the *generated* `sort_cspec_type` is the corrected
statement; §2–§5 prove it.
-/

namespace C2Lean
open Ll Spec


/-- The statement of `sort_cspec`, verbatim. -/
def SortCSpec : Prop :=
  ∀ (c_a c_n : Nat) (m₀ : Mem),
    ((let _old : WordAt := fun p => Mem.get m₀ p; validAt c_a c_n && c_n <= 8 : Bool) : Prop) →
    ∃ (fuel result : Nat) (m : Mem),
      runModule projectM "sort" [c_a, c_n] fuel m₀ = Res.val result m
      ∧ ((let cur : WordAt := fun p => Mem.get m p;
          let old : WordAt := fun p => Mem.get m₀ p;
          (SortedAt cur c_a c_n && PermAt cur old c_a c_n : Bool)) : Prop)

/-- Counterexample 1: a word ≥ 2^31.  The C code compares with *signed*
    `icmp`, so 2^31 counts as −2^31 and is moved in front of 1, but
    `SortedAt` compares as `Nat`. -/
def mBig : Mem := { cells := [(0, 1), (4, 2147483648)], next := 1024 }

/-- Bool-valued witness check, evaluated by the kernel. -/
def badSorted (m₀ : Mem) (fuel : Nat) : Bool :=
  match runModule projectM "sort" [0, 2] fuel m₀ with
  | Res.val _ m => !SortedAt (fun p => Mem.get m p) 0 2
  | _ => false

def badPerm (m₀ : Mem) (fuel : Nat) : Bool :=
  match runModule projectM "sort" [0, 2] fuel m₀ with
  | Res.val _ m => !PermAt (fun p => Mem.get m p) (fun p => Mem.get m₀ p) 0 2
  | _ => false

theorem badSorted_mBig : badSorted mBig 171 = true := by decide +kernel

theorem run_mBig : ∃ v m, runModule projectM "sort" [0, 2] 171 mBig = Res.val v m
    ∧ SortedAt (fun p => Mem.get m p) 0 2 = false := by
  have h := badSorted_mBig
  unfold badSorted at h
  split at h
  · rename_i v m hr
    exact ⟨v, m, hr, by simpa using h⟩
  · cases h

/-- Counterexample 2: `m₀.next` below the array.  The `alloca` frame
    slots then overlap the caller's array and clobber it. -/
def mLowNext : Mem := { cells := [(0, 2), (4, 1)], next := 0 }

theorem badPerm_mLowNext : badPerm mLowNext 185 = true := by decide +kernel

theorem run_mLowNext : ∃ v m, runModule projectM "sort" [0, 2] 185 mLowNext = Res.val v m
    ∧ PermAt (fun p => Mem.get m p) (fun p => Mem.get mLowNext p) 0 2 = false := by
  have h := badPerm_mLowNext
  unfold badPerm at h
  split at h
  · rename_i v m hr
    exact ⟨v, m, hr, by simpa using h⟩
  · cases h

theorem sort_cspec_false : ¬ SortCSpec := by
  intro h
  obtain ⟨fuel, r, m, hrun, hpost⟩ := h 0 2 mBig (by decide)
  obtain ⟨v, m', hrun', hbad⟩ := run_mBig
  obtain ⟨-, rfl⟩ := runModule_val_unique _ _ _ _ _ _ _ _ _ _ hrun hrun'
  simp only [hbad, Bool.false_and] at hpost
  exact Bool.false_ne_true hpost

end C2Lean

namespace C2Lean
open Ll Spec
/-- Second, independent refutation (frame overlaps the array). -/
theorem sort_cspec_false' : ¬ SortCSpec := by
  intro h
  obtain ⟨fuel, r, m, hrun, hpost⟩ := h 0 2 mLowNext (by decide)
  obtain ⟨v, m', hrun', hbad⟩ := run_mLowNext
  obtain ⟨-, rfl⟩ := runModule_val_unique _ _ _ _ _ _ _ _ _ _ hrun hrun'
  simp only [hbad, Bool.and_false] at hpost
  exact Bool.false_ne_true hpost
end C2Lean

namespace C2Lean
open Ll Spec


/-! ## List lemmas -/

/-- transposition of indices -/
def tau (i j k : Nat) : Nat := if k = j then i else if k = i then j else k

theorem tau_tau (i j k : Nat) : tau i j (tau i j k) = k := by
  unfold tau; by_cases h1 : k = j <;> by_cases h2 : k = i <;> simp_all <;> omega

theorem perm_map_tau (l : List Nat) (hl : l.Nodup) (i j : Nat) (hi : i ∈ l) (hj : j ∈ l) :
    (l.map (tau i j)).Perm l := by
  have hn : (l.map (tau i j)).Nodup := by
    unfold List.Nodup at *
    rw [List.pairwise_map]
    refine hl.imp ?_
    intro a b hab h
    apply hab
    have := congrArg (tau i j) h
    rwa [tau_tau, tau_tau] at this
  rw [List.perm_ext_iff_of_nodup hn hl]
  intro x
  rw [List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    unfold tau; split
    · exact hi
    · split
      · exact hj
      · exact hy
  · intro hx
    refine ⟨tau i j x, ?_, tau_tau _ _ _⟩
    unfold tau; split
    · exact hi
    · split
      · exact hj
      · exact hx

theorem perm_swap_range (f g : Nat → Nat) (lo n i j : Nat)
    (hi1 : lo ≤ i) (hi2 : i < lo + n) (hj1 : lo ≤ j) (hj2 : j < lo + n)
    (hg : ∀ k, lo ≤ k → k < lo + n → g k = f (tau i j k)) :
    ((List.range' lo n).map g).Perm ((List.range' lo n).map f) := by
  have e : (List.range' lo n).map g = ((List.range' lo n).map (tau i j)).map f := by
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range'] at hk
    obtain ⟨t, ht, rfl⟩ := hk
    simp only [Function.comp]
    exact hg _ (by omega) (by omega)
  rw [e]
  apply List.Perm.map
  apply perm_map_tau _ (List.nodup_range' _ (by omega))
  · rw [List.mem_range']; exact ⟨i - lo, by omega, by omega⟩
  · rw [List.mem_range']; exact ⟨j - lo, by omega, by omega⟩

/-- split a range at index p -/
theorem range'_split (lo p hi : Nat) (h1 : lo ≤ p) (h2 : p ≤ hi) :
    List.range' lo (hi + 1 - lo) =
      List.range' lo (p - lo) ++ p :: List.range' (p + 1) (hi - p) := by
  rw [← List.range'_succ]
  have := @List.range'_append lo (p - lo) (hi - p + 1) 1
  rw [show lo + 1 * (p - lo) = p by omega, show p - lo + (hi - p + 1) = hi + 1 - lo by omega] at this
  exact this.symm


theorem swap_spec (x y : Nat) (m : Mem) (k : Cont) (hx : x < m.next) (hy : y < m.next) :
    ∃ e' m', Reach projectM (blkCfg "swap" swapF "0" none [("0",x),("1",y)] m k)
      (· = ⟨"swap","0",none,[],Term.retv,e',m',k⟩) ∧ m'.next = m.next + 12 ∧
      ∀ p, p < m.next → Mem.get m' p =
        if p = y then Mem.get m x else if p = x then Mem.get m y else Mem.get m p := by
  refine ⟨?e, ?mm, ?r, ?n, ?p⟩
  case r =>
      norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      stp; norm
      apply Reach.done; rfl
  case n => rfl
  case p =>
    intro p hp
    have h1 : p ≠ m.next + 8 := by omega
    have h2 : p ≠ m.next + 4 := by omega
    have h3 : p ≠ m.next := by omega
    simp only [Mem.get_set_ite, Mem.get_withNext, h1, h2, h3, ite_false]
end C2Lean

namespace C2Lean
open Ll Spec


def PEnv (E : Env) (N : Nat) : Prop :=
  Env.get E "4" = N ∧ Env.get E "5" = N + 4 ∧ Env.get E "6" = N + 8 ∧
  Env.get E "7" = N + 12 ∧ Env.get E "8" = N + 16 ∧ Env.get E "9" = N + 20

def PSlots (M : Mem) (N a lo hi pv i j : Nat) : Prop :=
  M.get N = a ∧ M.get (N+4) = lo ∧ M.get (N+8) = hi ∧ M.get (N+12) = pv ∧
  M.get (N+16) = i ∧ M.get (N+20) = j ∧ N + 24 ≤ M.next

theorem inner1 {N a lo hi pv j : Nat} {k : Cont} {D : Config → Prop}
    (hlh : lo < hi) (ha : 4 * (hi + 1) + a ≤ 1024) (hN : 1024 ≤ N) (hpv : pv < 2147483648) :
    ∀ n i E M prev, hi - i = n → PEnv E N → PSlots M N a lo hi pv i j → lo ≤ i → i ≤ hi →
      (∀ t, lo ≤ t → t ≤ hi → M.get (4 * t + a) < 2147483648) →
      (∀ i' E' M', PEnv E' N → PSlots M' N a lo hi pv i' j → M'.next = M.next →
        (∀ p, p ≠ N + 16 → M'.get p = M.get p) → i ≤ i' → i' ≤ hi →
        (∀ t, i ≤ t → t < i' → M.get (4 * t + a) ≤ pv) → (i' < hi → pv < M.get (4 * i' + a)) →
        Reach projectM (blkCfg "partition" partitionF "40" (some "35") E' M' k) D) →
      Reach projectM (blkCfg "partition" partitionF "22" prev E M k) D := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i E M prev hn hE hS hli hih hb hk
    obtain ⟨e4, e5, e6, e7, e8, e9⟩ := hE
    obtain ⟨s4, s5, s6, s7, s8, s9, sN⟩ := hS
    have hbi := hb i hli hih
    run [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
    by_cases hc : M.get (4 * i + a) ≤ pv
    · run [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
      stp
      by_cases hc2 : i ≤ hi - 1
      · run [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, hc2]
        stp
        refine ih (hi - (i + 1)) (by omega) (i + 1) _ _ _ rfl ?_ ?_ (by omega) (by omega) ?_ ?_
        · simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9] <;> omega
        · intro t h1 h2; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; exact hb t h1 h2
        · intro i' E' M' hE' hS' hn' hfr' h1 h2 hle hex
          refine hk i' E' M' hE' hS' (by rw [hn']; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]) ?_ (by omega) h2 ?_ ?_
          · intro p hp; rw [hfr' p hp]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
          · intro t ht1 ht2
            by_cases hti : t = i
            · subst hti; exact hc
            · have := hle t (by omega) ht2
              revert this; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; exact id
          · intro hlt; have := hex hlt; revert this; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; exact id
      · run [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, hc2]
        refine hk i _ M ?_ ⟨s4, s5, s6, s7, s8, s9, sN⟩ rfl (fun _ _ => rfl) (Nat.le_refl _) hih
          (fun t h1 h2 => by omega) (fun h => by omega)
        simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]
    · run [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
      refine hk i _ M ?_ ⟨s4, s5, s6, s7, s8, s9, sN⟩ rfl (fun _ _ => rfl) (Nat.le_refl _) hih
        (fun t h1 h2 => by omega) (fun _ => by omega)
      simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]

theorem inner2 {N a lo hi pv i : Nat} {k : Cont} {D : Config → Prop}
    (hlh : lo < hi) (ha : 4 * (hi + 1) + a ≤ 1024) (hN : 1024 ≤ N) (hpv : pv < 2147483648) :
    ∀ n j E M prev, j - lo = n → PEnv E N → PSlots M N a lo hi pv i j → lo ≤ j → j ≤ hi →
      (∀ t, lo ≤ t → t ≤ hi → M.get (4 * t + a) < 2147483648) →
      (∀ j' E' M', PEnv E' N → PSlots M' N a lo hi pv i j' → M'.next = M.next →
        (∀ p, p ≠ N + 20 → M'.get p = M.get p) → lo ≤ j' → j' ≤ j →
        (∀ t, j' < t → t ≤ j → pv < M.get (4 * t + a)) → (lo < j' → M.get (4 * j' + a) ≤ pv) →
        Reach projectM (blkCfg "partition" partitionF "59" (some "54") E' M' k) D) →
      Reach projectM (blkCfg "partition" partitionF "41" prev E M k) D := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j E M prev hn hE hS hlj hjh hb hk
    obtain ⟨e4, e5, e6, e7, e8, e9⟩ := hE
    obtain ⟨s4, s5, s6, s7, s8, s9, sN⟩ := hS
    have hbj := hb j hlj hjh
    run [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
    by_cases hc : pv < M.get (4 * j + a)
    · run [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
      stp
      by_cases hc2 : lo + 1 ≤ j
      · run [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, hc2]
        stp
        refine ih (j - 1 - lo) (by omega) (j - 1) _ _ _ rfl ?_ ?_ (by omega) (by omega) ?_ ?_
        · simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9] <;> omega
        · intro t h1 h2; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; exact hb t h1 h2
        · intro j' E' M' hE' hS' hn' hfr' h1 h2 hgt hex
          refine hk j' E' M' hE' hS' (by rw [hn']; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]) ?_ h1 (by omega) ?_ ?_
          · intro p hp; rw [hfr' p hp]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
          · intro t ht1 ht2
            by_cases htj : t = j
            · subst htj; exact hc
            · have := hgt t ht1 (by omega)
              revert this; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; exact id
          · intro hlt; have := hex hlt; revert this; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; exact id
      · runI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, hc2]
        brn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc, hc2]
        refine hk j _ M ?_ ⟨s4, s5, s6, s7, s8, s9, sN⟩ rfl (fun _ _ => rfl) hlj (Nat.le_refl _)
          (fun t h1 h2 => by omega) (fun h => by omega)
        simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]
    · runI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
      brn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
      runI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
      brn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
      refine hk j _ M ?_ ⟨s4, s5, s6, s7, s8, s9, sN⟩ rfl (fun _ _ => rfl) hlj (Nat.le_refl _)
        (fun t h1 h2 => by omega) (fun _ => by omega)
      simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]

theorem swap_call {fn lbl : String} {prev : Option String} {o1 o2 : Operand} {r : List Instr}
    {tm : Term} {e : Env} {m : Mem} {k : Cont} {D : Config → Prop}
    (hx : evOperand e o1 < m.next) (hy : evOperand e o2 < m.next)
    (h : ∀ m' : Mem, m'.next = m.next + 12 →
      (∀ p, p < m.next → m'.get p = if p = evOperand e o2 then m.get (evOperand e o1)
          else if p = evOperand e o1 then m.get (evOperand e o2) else m.get p) →
      Reach projectM ⟨fn, lbl, prev, r, tm, e, m', k⟩ D) :
    Reach projectM ⟨fn, lbl, prev, Instr.callv "swap" [o1, o2] :: r, tm, e, m, k⟩ D := by
  obtain ⟨e', m', hR, hn, hm⟩ :=
    swap_spec (evOperand e o1) (evOperand e o2) m (Cont.retTo fn lbl prev r tm e "void" k) hx hy
  refine Reach.step _ _ _ rfl (Reach.trans hR ?_)
  exact Reach.step _ _ _ rfl (h m' hn hm)

def segL (m : Mem) (a lo hi : Nat) : List Nat :=
  (List.range' lo (hi + 1 - lo)).map (fun t => m.get (4 * t + a))

theorem segL_congr (M M' : Mem) (a lo hi : Nat)
    (h : ∀ t, lo ≤ t → t ≤ hi → M'.get (4 * t + a) = M.get (4 * t + a)) :
    segL M' a lo hi = segL M a lo hi := by
  unfold segL
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range'] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact h _ (by omega) (by omega)

theorem segL_swap (M2 M3 : Mem) (a lo hi x y : Nat) (hx1 : lo ≤ x) (hx2 : x ≤ hi)
    (hy1 : lo ≤ y) (hy2 : y ≤ hi) (hn : 4 * (hi + 1) + a ≤ M2.next)
    (hm : ∀ p, p < M2.next → M3.get p = if p = 4 * y + a then M2.get (4 * x + a)
          else if p = 4 * x + a then M2.get (4 * y + a) else M2.get p) :
    (segL M3 a lo hi).Perm (segL M2 a lo hi) := by
  unfold segL
  apply perm_swap_range (fun t => M2.get (4 * t + a)) (fun t => M3.get (4 * t + a)) lo
    (hi + 1 - lo) x y hx1 (by omega) hy1 (by omega)
  intro t h1 h2
  show M3.get (4 * t + a) = M2.get (4 * tau x y t + a)
  rw [hm _ (by omega)]
  unfold tau
  by_cases h3 : t = y
  · subst h3; simp
  · by_cases h4 : t = x
    · subst h4; simp [h3]; omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h3, ite_eq_right h4]

def OInv (M m0 : Mem) (N a lo hi pv i j : Nat) : Prop :=
  lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi ∧ M.get (4 * lo + a) = pv ∧
  (∀ t, lo ≤ t → t < i → M.get (4 * t + a) ≤ pv) ∧
  (∀ t, j < t → t ≤ hi → pv < M.get (4 * t + a)) ∧
  (i < j → M.get (4 * i + a) ≤ pv) ∧ (j ≤ i → M.get (4 * j + a) ≤ pv) ∧
  (segL M a lo hi).Perm (segL m0 a lo hi) ∧
  (∀ q, q < N → (∀ t, lo ≤ t → t ≤ hi → q ≠ 4 * t + a) → M.get q = m0.get q) ∧
  (∀ t, lo ≤ t → t ≤ hi → M.get (4 * t + a) < 2147483648)

def PartPost (M m0 : Mem) (a lo hi p : Nat) : Prop :=
  lo ≤ p ∧ p ≤ hi ∧ m0.next ≤ M.next ∧
  (∀ q, q < m0.next → (∀ t, lo ≤ t → t ≤ hi → q ≠ 4 * t + a) → M.get q = m0.get q) ∧
  (segL M a lo hi).Perm (segL m0 a lo hi) ∧
  (∀ t, lo ≤ t → t < p → M.get (4 * t + a) ≤ M.get (4 * p + a)) ∧
  (∀ t, p < t → t ≤ hi → M.get (4 * p + a) < M.get (4 * t + a)) ∧
  (∀ t, lo ≤ t → t ≤ hi → M.get (4 * t + a) < 2147483648)

/-- Final block 73: `swap(&a[low], &a[j]); return j`. -/
theorem at73 {N a lo hi pv i j : Nat} {k : Cont} {D : Config → Prop} {E : Env} {M : Mem}
    (ha : 4 * (hi + 1) + a ≤ 1024) (hN : 1024 ≤ N)
    (hE : PEnv E N) (hS : PSlots M N a lo hi pv i j) (hjh : j ≤ hi) (hlh : lo ≤ hi)
    (hk : ∀ E' M', Env.get E' "82" = j → M'.next = M.next + 12 →
      (∀ p, p < M.next → M'.get p = if p = 4 * j + a then M.get (4 * lo + a)
          else if p = 4 * lo + a then M.get (4 * j + a) else M.get p) →
      Reach projectM ⟨"partition", "73", some "17", [], Term.ret (Operand.reg "82"), E', M', k⟩ D) :
    Reach projectM (blkCfg "partition" partitionF "73" (some "17") E M k) D := by
  obtain ⟨e4, e5, e6, e7, e8, e9⟩ := hE
  obtain ⟨s4, s5, s6, s7, s8, s9, sN⟩ := hS
  runI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
  apply swap_call
  · nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; omega
  · nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; omega
  intro M3 hn3 hm3
  have hm3' : ∀ p, p < M.next → M3.get p = if p = 4 * j + a then M.get (4 * lo + a)
      else if p = 4 * lo + a then M.get (4 * j + a) else M.get p := by
    intro p hp; rw [hm3 p hp]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
  have h20 : M3.get (N + 20) = j := by rw [hm3' _ (by omega)]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
  runI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, h20]
  exact hk _ M3 (by nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, h20]) hn3 hm3'

/-- Block 59: `if (i < j) swap(&a[i], &a[j]);` then back to the loop head. -/
theorem at59 {N a lo hi pv i j : Nat} {k : Cont} {D : Config → Prop} {E : Env} {M : Mem}
    (ha : 4 * (hi + 1) + a ≤ 1024) (hN : 1024 ≤ N)
    (hE : PEnv E N) (hS : PSlots M N a lo hi pv i j) (hih : i ≤ hi) (hjh : j ≤ hi)
    (hsw : i < j → ∀ E' M', PEnv E' N → PSlots M' N a lo hi pv i j → M'.next = M.next + 12 →
      (∀ p, p < M.next → M'.get p = if p = 4 * j + a then M.get (4 * i + a)
          else if p = 4 * i + a then M.get (4 * j + a) else M.get p) →
      Reach projectM (blkCfg "partition" partitionF "17" (some "72") E' M' k) D)
    (hno : ¬ i < j → ∀ E', PEnv E' N →
      Reach projectM (blkCfg "partition" partitionF "17" (some "72") E' M k) D) :
    Reach projectM (blkCfg "partition" partitionF "59" (some "54") E M k) D := by
  obtain ⟨e4, e5, e6, e7, e8, e9⟩ := hE
  obtain ⟨s4, s5, s6, s7, s8, s9, sN⟩ := hS
  runI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
  by_cases hc : i < j
  · brn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
    runI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
    apply swap_call
    · nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; omega
    · nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]; omega
    intro M3 hn3 hm3
    have hm3' : ∀ p, p < M.next → M3.get p = if p = 4 * j + a then M.get (4 * i + a)
        else if p = 4 * i + a then M.get (4 * j + a) else M.get p := by
      intro p hp; rw [hm3 p hp]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
    have hsl : ∀ q, N ≤ q → q < N + 24 → M3.get q = M.get q := by
      intro q h1 h2; rw [hm3' q (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    stp
    stp
    refine hsw hc _ M3 ?_ ?_ hn3 hm3'
    · simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · rw [hsl _ (by omega) (by omega)]; exact s4
      · rw [hsl _ (by omega) (by omega)]; exact s5
      · rw [hsl _ (by omega) (by omega)]; exact s6
      · rw [hsl _ (by omega) (by omega)]; exact s7
      · rw [hsl _ (by omega) (by omega)]; exact s8
      · rw [hsl _ (by omega) (by omega)]; exact s9
  · brn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
    stp
    refine hno hc _ ?_
    simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]

/-- Loop head 17 up to the inner loops' exit (blocks 17, 21, inner1, 40, inner2). -/
theorem at17 {N a lo hi pv i j : Nat} {k : Cont} {D : Config → Prop} {E : Env} {M : Mem}
    {prev : Option String}
    (hlh : lo < hi) (ha : 4 * (hi + 1) + a ≤ 1024) (hN : 1024 ≤ N) (hpv : pv < 2147483648)
    (hE : PEnv E N) (hS : PSlots M N a lo hi pv i j) (hli : lo ≤ i) (hih : i ≤ hi)
    (hlj : lo ≤ j) (hjh : j ≤ hi)
    (hb : ∀ t, lo ≤ t → t ≤ hi → M.get (4 * t + a) < 2147483648)
    (hexit : ¬ i < j → ∀ E', PEnv E' N →
      Reach projectM (blkCfg "partition" partitionF "73" (some "17") E' M k) D)
    (hbody : i < j → ∀ i1 j1 E2 M2, PEnv E2 N → PSlots M2 N a lo hi pv i1 j1 → M2.next = M.next →
      (∀ p, p ≠ N + 16 → p ≠ N + 20 → M2.get p = M.get p) → i ≤ i1 → i1 ≤ hi →
      (∀ t, i ≤ t → t < i1 → M.get (4 * t + a) ≤ pv) → (i1 < hi → pv < M.get (4 * i1 + a)) →
      lo ≤ j1 → j1 ≤ j →
      (∀ t, j1 < t → t ≤ j → pv < M.get (4 * t + a)) → (lo < j1 → M.get (4 * j1 + a) ≤ pv) →
      Reach projectM (blkCfg "partition" partitionF "59" (some "54") E2 M2 k) D) :
    Reach projectM (blkCfg "partition" partitionF "17" prev E M k) D := by
  have hS0 := hS
  obtain ⟨e4, e5, e6, e7, e8, e9⟩ := hE
  obtain ⟨s4, s5, s6, s7, s8, s9, sN⟩ := hS
  runI [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9]
  by_cases hc : i < j
  · brn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
    stp
    refine inner1 hlh ha hN hpv (hi - i) i _ M (some "21") rfl ?_ hS0 hli hih hb ?_
    · simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self]
    intro i1 E1 M1 hE1 hS1 hn1 hfr1 hii1 hi1h hle1 hex1
    obtain ⟨g4, g5, g6, g7, g8, g9⟩ := hE1
    have hS1' := hS1
    obtain ⟨u4, u5, u6, u7, u8, u9, uN⟩ := hS1
    nrm [g4, g5, g6, g7, g8, g9, u4, u5, u6, u7, u8, u9]
    stp
    refine inner2 hlh ha hN hpv (j - lo) j _ M1 (some "40") rfl ?_ hS1' hlj hjh ?_ ?_
    · simp only [PEnv]; nrm [g4, g5, g6, g7, g8, g9, u4, u5, u6, u7, u8, u9, and_self]
    · intro t h1 h2; rw [hfr1 (4 * t + a) (by omega)]; exact hb t h1 h2
    intro j1 E2 M2 hE2 hS2 hn2 hfr2 hlj1 hj1j hgt2 hex2
    refine hbody hc i1 j1 E2 M2 hE2 hS2 (by rw [hn2, hn1]) ?_ hii1 hi1h hle1 hex1 hlj1 hj1j ?_ ?_
    · intro p hp1 hp2; rw [hfr2 p hp2, hfr1 p hp1]
    · intro t h1 h2; have := hgt2 t h1 h2; rwa [hfr1 (4 * t + a) (by omega)] at this
    · intro h; have := hex2 h; rwa [hfr1 (4 * j1 + a) (by omega)] at this
  · brn [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, hc]
    exact hexit hc _ (by simp only [PEnv]; nrm [e4, e5, e6, e7, e8, e9, s4, s5, s6, s7, s8, s9, and_self])

theorem outer {N a lo hi pv : Nat} {m0 : Mem} {k : Cont} {D : Config → Prop}
    (hlh : lo < hi) (ha : 4 * (hi + 1) + a ≤ 1024) (hN : 1024 ≤ N) (hN0 : m0.next = N)
    (hpv : pv < 2147483648)
    (hk : ∀ E' M' p, Env.get E' "82" = p → PartPost M' m0 a lo hi p →
      Reach projectM ⟨"partition", "73", some "17", [], Term.ret (Operand.reg "82"), E', M', k⟩ D) :
    ∀ n i j E M prev, j - i = n → PEnv E N → PSlots M N a lo hi pv i j → OInv M m0 N a lo hi pv i j →
      Reach projectM (blkCfg "partition" partitionF "17" prev E M k) D := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i j E M prev hn hE hS hI
    have hS0 := hS
    obtain ⟨s4, s5, s6, s7, s8, s9, sN⟩ := hS
    obtain ⟨hli, hih, hlj, hjh, hlo, hlt, hgt, hij, hji, hperm, hfr, hb⟩ := hI
    refine at17 hlh ha hN hpv hE hS0 hli hih hlj hjh hb ?_ ?_
    · -- loop exit
      intro hc E' hE'
      refine at73 ha hN hE' hS0 hjh (by omega) ?_
      intro E3 M3 h82 hn3 hm3'
      have hA : ∀ t, t ≤ hi → M3.get (4 * t + a) = if t = j then M.get (4 * lo + a)
          else if t = lo then M.get (4 * j + a) else M.get (4 * t + a) := by
        intro t ht; rw [hm3' _ (by omega)]
        by_cases h1 : t = j
        · subst h1; simp
        · by_cases h2 : t = lo
          · subst h2; simp [h1]; omega
          · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2]
      have hji' := hji (by omega)
      refine hk _ M3 j h82 ⟨hlj, hjh, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq hq2
        rw [hm3' q (by omega), ite_eq_right (hq2 j hlj hjh), ite_eq_right (hq2 lo (Nat.le_refl _) (by omega))]
        exact hfr q (by omega) hq2
      · exact (segL_swap M M3 a lo hi lo j (Nat.le_refl _) (by omega) hlj hjh (by omega) hm3').trans hperm
      · intro t h1 h2
        rw [hA t (by omega), hA j hjh, ite_eq_right (by omega)]
        simp only [ite_true]
        by_cases h3 : t = lo
        · rw [ite_eq_left h3]; omega
        · rw [ite_eq_right h3]; have := hlt t h1 (by omega); omega
      · intro t h1 h2
        have n1 : t ≠ j := by omega
        have n2 : t ≠ lo := by omega
        rw [hA t h2, hA j hjh]
        simp only [n1, n2, ite_true, ite_false]
        have := hgt t h1 h2; omega
      · intro t h1 h2
        rw [hA t h2]
        have := hb t h1 h2; have := hb lo (Nat.le_refl _) (by omega); have := hb j hlj hjh
        split <;> (try split) <;> omega
    · -- loop body
      intro hc i1 j1 E2 M2 hE2 hS2 hn2 hfr2 hii1 hi1h hle1 hex1 hlj1 hj1j hgt2 hex2
      have hii : i < i1 := by
        rcases Nat.lt_or_ge i i1 with h | h
        · exact h
        · have := hex1 (by omega); have := hij hc
          have e : i1 = i := by omega
          subst e; omega
      have hM2 : ∀ t, t ≤ hi → M2.get (4 * t + a) = M.get (4 * t + a) := by
        intro t ht; exact hfr2 (4 * t + a) (by omega) (by omega)
      have hM2q : ∀ q, q < N → M2.get q = M.get q := by
        intro q hq; exact hfr2 q (by omega) (by omega)
      have hS2' := hS2
      obtain ⟨t4, t5, t6, t7, t8, t9, tN⟩ := hS2
      refine at59 ha hN hE2 hS2' hi1h (by omega) ?_ ?_
      · intro hc2 E3 M3 hE3 hS3 hn3 hm3'
        have hA : ∀ t, t ≤ hi → M3.get (4 * t + a) = if t = j1 then M.get (4 * i1 + a)
            else if t = i1 then M.get (4 * j1 + a) else M.get (4 * t + a) := by
          intro t ht; rw [hm3' (4 * t + a) (by omega), hM2 i1 (by omega), hM2 j1 (by omega)]
          by_cases h1 : t = j1
          · subst h1; simp
          · by_cases h2 : t = i1
            · subst h2; simp [h1]; omega
            · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2, hM2 t ht]
        refine ih (j1 - i1) (by omega) i1 j1 E3 M3 (some "72") rfl hE3 hS3 ?_
        have hbj1 := hex2 (by omega)
        refine ⟨by omega, hi1h, hlj1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hA lo (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; exact hlo
        · intro t h1 h2
          rw [hA t (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
          by_cases h3 : t < i
          · exact hlt t h1 h3
          · exact hle1 t (by omega) h2
        · intro t h1 h2
          rw [hA t h2, ite_eq_right (by omega), ite_eq_right (by omega)]
          by_cases h3 : t ≤ j
          · exact hgt2 t h1 h3
          · exact hgt t (by omega) h2
        · intro _
          rw [hA i1 (by omega), ite_eq_right (by omega), ite_eq_left rfl]
          exact hbj1
        · intro h; omega
        · refine (segL_swap M2 M3 a lo hi i1 j1 (by omega) (by omega) (by omega) (by omega)
            (by omega) hm3').trans ?_
          rw [segL_congr M M2 a lo hi (fun t _ h2 => hM2 t h2)]
          exact hperm
        · intro q hq hq2
          rw [hm3' q (by omega), ite_eq_right (hq2 j1 hlj1 (by omega)),
            ite_eq_right (hq2 i1 (by omega) (by omega)), hM2q q hq]
          exact hfr q hq hq2
        · intro t h1 h2
          rw [hA t h2]
          have := hb t h1 h2; have := hb i1 (by omega) (by omega); have := hb j1 hlj1 (by omega)
          split <;> (try split) <;> omega
      · intro hc2 E3 hE3
        refine ih (j1 - i1) (by omega) i1 j1 E3 M2 (some "72") rfl hE3 ⟨t4, t5, t6, t7, t8, t9, tN⟩ ?_
        refine ⟨by omega, hi1h, hlj1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hM2 lo (by omega)]; exact hlo
        · intro t h1 h2
          rw [hM2 t (by omega)]
          by_cases h3 : t < i
          · exact hlt t h1 h3
          · exact hle1 t (by omega) h2
        · intro t h1 h2
          rw [hM2 t h2]
          by_cases h3 : t ≤ j
          · exact hgt2 t h1 h3
          · exact hgt t (by omega) h2
        · intro h; omega
        · intro _
          rw [hM2 j1 (by omega)]
          by_cases h3 : lo < j1
          · exact hex2 h3
          · have e : j1 = lo := by omega
            rw [e, hlo]; exact Nat.le_refl _
        · rw [segL_congr M M2 a lo hi (fun t _ h2 => hM2 t h2)]; exact hperm
        · intro q hq hq2; rw [hM2q q hq]; exact hfr q hq hq2
        · intro t h1 h2; rw [hM2 t h2]; exact hb t h1 h2

end C2Lean

namespace C2Lean
open Ll Spec

set_option maxHeartbeats 4000000 in
theorem partition_call {fn lbl : String} {prev : Option String} {d x0 x1 x2 : String}
    {r : List Instr} {tm : Term} {e : Env} {m : Mem} {k : Cont} {D : Config → Prop} {a lo hi : Nat}
    (h0 : Env.get e x0 = a) (h1 : Env.get e x1 = lo) (h2 : Env.get e x2 = hi)
    (hlh : lo < hi) (ha : 4 * (hi + 1) + a ≤ 1024) (hN : 1024 ≤ m.next)
    (hb : ∀ t, lo ≤ t → t ≤ hi → m.get (4 * t + a) < 2147483648)
    (h : ∀ m' p, PartPost m' m a lo hi p → Reach projectM ⟨fn, lbl, prev, r, tm, Env.set e d p, m', k⟩ D) :
    Reach projectM ⟨fn, lbl, prev, Instr.call d "partition" [Operand.reg x0, Operand.reg x1, Operand.reg x2] :: r, tm, e, m, k⟩ D := by
  apply Reach.step'
  · rfl
  have hpv := hb lo (Nat.le_refl _) (by omega)
  nrm [h0, h1, h2]
  run [h0, h1, h2]
  stp
  refine outer hlh ha hN rfl hpv ?_ (hi - lo) lo hi _ _ (some "0") rfl ?_ ?_ ?_
  · intro E' M' p h82 hpost
    apply Reach.step'
    · rfl
    simp only [evOperand, h82]
    exact h M' p hpost
  · simp only [PEnv]; nrm [and_self]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nrm [] <;> omega
  · refine ⟨Nat.le_refl _, by omega, by omega, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · nrm []
    · intro t h1 h2; omega
    · intro t h1 h2; omega
    · intro _; nrm []; exact Nat.le_refl _
    · intro h; omega
    · rw [segL_congr m _ a lo hi]
      · intro t h1 h2; nrm []
    · intro q hq _; nrm []
    · intro t h1 h2; nrm []; exact hb t h1 h2

/-- `quickSort` on a range where `low < high` (signed) fails: only the frame changes. -/
theorem qs_short {fn lbl : String} {prev : Option String} {o0 o1 o2 : Operand}
    {r : List Instr} {tm : Term} {e : Env} {m : Mem} {k : Cont} {D : Config → Prop} {a lo hiW : Nat}
    (h0 : evOperand e o0 = a) (h1 : evOperand e o1 = lo) (h2 : evOperand e o2 = hiW)
    (hc : ¬ sgn lo < sgn hiW)
    (h : ∀ m', m'.next = m.next + 16 → (∀ q, q < m.next → m'.get q = m.get q) →
      Reach projectM ⟨fn, lbl, prev, r, tm, e, m', k⟩ D) :
    Reach projectM ⟨fn, lbl, prev,
      Instr.callv "quickSort" [o0, o1, o2] :: r, tm, e, m, k⟩ D := by
  apply Reach.step'
  · rfl
  simp only [List.map, h0, h1, h2]
  nrm []
  runI [hc]
  brn [hc]
  apply Reach.step'
  · rfl
  refine h _ (by nrm []) ?_
  intro q hq; nrm []

def segN (m : Mem) (a lo len : Nat) : List Nat :=
  (List.range' lo len).map (fun t => m.get (4 * t + a))

theorem segN_congr (M M' : Mem) (a lo len : Nat)
    (h : ∀ t, lo ≤ t → t < lo + len → M'.get (4 * t + a) = M.get (4 * t + a)) :
    segN M' a lo len = segN M a lo len := by
  unfold segN
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range'] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact h _ (by omega) (by omega)

theorem mem_segN {m : Mem} {a lo len y : Nat} :
    y ∈ segN m a lo len ↔ ∃ t, lo ≤ t ∧ t < lo + len ∧ y = m.get (4 * t + a) := by
  unfold segN
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_range'] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact ⟨lo + 1 * u, by omega, by omega, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, by rw [List.mem_range']; exact ⟨t - lo, by omega, by omega⟩, rfl⟩

theorem segN_split (m : Mem) (a lo len p : Nat) (h1 : lo ≤ p) (h2 : p < lo + len) :
    segN m a lo len = segN m a lo (p - lo) ++ m.get (4 * p + a) :: segN m a (p + 1) (lo + len - 1 - p) := by
  unfold segN
  have := range'_split lo p (lo + len - 1) h1 (by omega)
  rw [show lo + len - 1 + 1 - lo = len by omega] at this
  rw [this, List.map_append, List.map_cons]

theorem segN_short_sorted (m : Mem) (a lo len : Nat) (h : len ≤ 1) :
    (segN m a lo len).Pairwise (· ≤ ·) := by
  unfold segN
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h <;> subst h <;> simp [List.range']

def QSPost (m m' : Mem) (a lo len : Nat) : Prop :=
  m.next ≤ m'.next ∧
  (∀ q, q < m.next → (∀ t, lo ≤ t → t < lo + len → q ≠ 4 * t + a) → m'.get q = m.get q) ∧
  (segN m' a lo len).Perm (segN m a lo len) ∧ (segN m' a lo len).Pairwise (· ≤ ·)

theorem sgn_max : sgn 4294967295 = -1 := by decide

theorem hiW_pos (lo len : Nat) (h : 1 ≤ lo + len) (h2 : lo + len < 4294967296) :
    w32 (((lo + len : Nat) : Int) - 1) = lo + len - 1 := by
  rw [w32_eq _ (by omega) (by omega)]; omega

theorem hiW_zero : w32 (((0 : Nat) : Int) - 1) = 4294967295 := by decide

theorem qs_call : ∀ n len, len = n → ∀ {fn lbl : String} {prev : Option String} {o0 o1 o2 : Operand}
    {r : List Instr} {tm : Term} {e : Env} {m : Mem} {k : Cont} {D : Config → Prop} {a lo hiW : Nat},
    evOperand e o0 = a → evOperand e o1 = lo → evOperand e o2 = hiW →
    hiW = w32 (((lo + len : Nat) : Int) - 1) →
    4 * (lo + len) + a ≤ 1024 → 1024 ≤ m.next →
    (∀ t, lo ≤ t → t < lo + len → m.get (4 * t + a) < 2147483648) →
    (∀ m', QSPost m m' a lo len → Reach projectM ⟨fn, lbl, prev, r, tm, e, m', k⟩ D) →
    Reach projectM ⟨fn, lbl, prev,
      Instr.callv "quickSort" [o0, o1, o2] :: r, tm, e, m, k⟩ D := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro len hlen fn lbl prev o0 o1 o2 r tm e m k D a lo hiW h0 h1 h2 hW ha hN hb h
  by_cases hl2 : 2 ≤ len
  · have hW' : hiW = lo + len - 1 := by rw [hW, hiW_pos lo len (by omega) (by omega)]
    have hc : lo < lo + len - 1 := by omega
    apply Reach.step'
    · rfl
    simp only [List.map, h0, h1, h2, hW']
    nrm []
    runI [hc]
    brn [hc]
    runI [hc]
    apply partition_call (a := a) (lo := lo) (hi := lo + len - 1)
    · nrm []
    · nrm []
    · nrm []
    · omega
    · omega
    · nrm []; omega
    · intro t h1 h2; nrm []; exact hb t h1 (by omega)
    intro m1 p hp
    obtain ⟨hp1, hp2, hpn, hpfr, hpperm, hpl, hpr, hpb⟩ := hp
    have hM0 : ∀ q, q < m.next → (((({ cells := m.cells, next := m.next + 16 } : Mem).set m.next a).set
        (m.next + 4) lo).set (m.next + 8) (lo + len - 1)).get q = m.get q := by
      intro q hq; nrm []
    have hfr1 : ∀ q, q < m.next + 16 → (∀ t, lo ≤ t → t ≤ lo + len - 1 → q ≠ 4 * t + a) →
        m1.get q = (((({ cells := m.cells, next := m.next + 16 } : Mem).set m.next a).set
        (m.next + 4) lo).set (m.next + 8) (lo + len - 1)).get q := hpfr
    have f4 : m1.get m.next = a := by
      rw [hfr1 _ (by omega) (fun t _ _ => by omega)]; nrm []
    have f5 : m1.get (m.next + 4) = lo := by
      rw [hfr1 _ (by omega) (fun t _ _ => by omega)]; nrm []
    have f6 : m1.get (m.next + 8) = lo + len - 1 := by
      rw [hfr1 _ (by omega) (fun t _ _ => by omega)]; nrm []
    have hpn' : m.next + 16 ≤ m1.next := by simpa using hpn
    runI [f4, f5, f6]
    refine ih (p - lo) (by omega) (p - lo) rfl (a := a) (lo := lo) (hiW := w32 (↑p - ↑(1 : Nat)))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · nrm [f4]
    · nrm [f5]
    · nrm []
    · rw [show lo + (p - lo) = p by omega]; rfl
    · omega
    · nrm []; omega
    · intro t h1 h2; nrm []; exact hpb t h1 (by omega)
    intro m2 hq2
    obtain ⟨hq2n, hq2fr, hq2perm, hq2sort⟩ := hq2
    have hq2n' : m1.next ≤ m2.next := by simpa using hq2n
    have hfr2 : ∀ q, q < m1.next → (∀ t, lo ≤ t → t < p → q ≠ 4 * t + a) → q ≠ m.next + 12 →
        m2.get q = m1.get q := by
      intro q hq hq' hq12
      rw [hq2fr q (by simpa using hq) (fun t h1 h2 => hq' t h1 (by omega))]; nrm []
    have g4 : m2.get m.next = a := by rw [hfr2 _ (by omega) (fun t _ _ => by omega) (by omega)]; exact f4
    have g6 : m2.get (m.next + 8) = lo + len - 1 := by
      rw [hfr2 _ (by omega) (fun t _ _ => by omega) (by omega)]; exact f6
    have g7 : m2.get (m.next + 12) = p := by
      rw [hq2fr _ (by simp; omega) (fun t _ _ => by omega)]; nrm []
    runI [g4, g6, g7]
    refine ih (lo + len - 1 - p) (by omega) _ rfl (a := a) (lo := p + 1) (hiW := lo + len - 1)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · nrm [g4]
    · nrm [g7]
    · nrm [g6]
    · rw [show p + 1 + (lo + len - 1 - p) = lo + len by omega, hiW_pos lo len (by omega) (by omega)]
    · omega
    · omega
    · intro t h1 h2
      rw [hfr2 _ (by omega) (fun u _ _ => by omega) (by omega)]; exact hpb t (by omega) (by omega)
    intro m3 hq3
    obtain ⟨hq3n, hq3fr, hq3perm, hq3sort⟩ := hq3
    stp
    stp
    -- array facts
    have hL : segN m3 a lo (p - lo) = segN m2 a lo (p - lo) :=
      segN_congr _ _ _ _ _ (fun t h1 h2 => hq3fr _ (by omega) (fun u _ _ => by omega))
    have hR : segN m2 a (p + 1) (lo + len - 1 - p) = segN m1 a (p + 1) (lo + len - 1 - p) :=
      segN_congr _ _ _ _ _ (fun t h1 h2 => hfr2 _ (by omega) (fun u _ _ => by omega) (by omega))
    have hX : m3.get (4 * p + a) = m1.get (4 * p + a) := by
      rw [hq3fr _ (by omega) (fun u _ _ => by omega), hfr2 _ (by omega) (fun u _ _ => by omega) (by omega)]
    have hL1 : segN (Mem.set m1 (m.next + 12) p) a lo (p - lo) = segN m1 a lo (p - lo) :=
      segN_congr _ _ _ _ _ (fun t h1 h2 => by nrm [])
    have hsplit3 := segN_split m3 a lo len p hp1 (by omega)
    have hsplit1 := segN_split m1 a lo len p hp1 (by omega)
    have hseg1 : segN m1 a lo len = segL m1 a lo (lo + len - 1) := by
      unfold segN segL; rw [show lo + len - 1 + 1 - lo = len by omega]
    have hseg0 : segL (((({ cells := m.cells, next := m.next + 16 } : Mem).set m.next a).set
        (m.next + 4) lo).set (m.next + 8) (lo + len - 1)) a lo (lo + len - 1) = segN m a lo len := by
      unfold segN segL; rw [show lo + len - 1 + 1 - lo = len by omega]
      apply List.map_congr_left
      intro t ht; rw [List.mem_range'] at ht; nrm []
    have hLp : (segN m3 a lo (p - lo)).Perm (segN m1 a lo (p - lo)) := by
      rw [hL, ← hL1]; exact hq2perm
    have hRp : (segN m3 a (p + 1) (lo + len - 1 - p)).Perm (segN m1 a (p + 1) (lo + len - 1 - p)) := by
      rw [← hR]; exact hq3perm
    refine h m3 ⟨by omega, ?_, ?_, ?_⟩
    · intro q hq hq2
      rw [hq3fr q (by omega) (fun u h1 h2 => hq2 u (by omega) (by omega)),
        hfr2 q (by omega) (fun u h1 h2 => hq2 u h1 (by omega)) (by omega),
        hfr1 q (by omega) (fun u h1 h2 => hq2 u h1 (by omega)), hM0 q hq]
    · rw [hsplit3, hX]
      refine (List.Perm.append hLp (List.Perm.cons _ hRp)).trans ?_
      rw [← hsplit1, hseg1, ← hseg0]; exact hpperm
    · rw [hsplit3, List.pairwise_append, List.pairwise_cons]
      refine ⟨by rw [hL]; exact hq2sort, ⟨?_, hq3sort⟩, ?_⟩
      · intro z hz
        rw [hX]
        obtain ⟨t, h1, h2, rfl⟩ := mem_segN.mp (hRp.mem_iff.mp hz)
        exact Nat.le_of_lt (hpr t (by omega) (by omega))
      · intro y hy z hz
        rw [hX] at hz
        obtain ⟨t, h1, h2, rfl⟩ := mem_segN.mp (hLp.mem_iff.mp hy)
        have hyx := hpl t h1 (by omega)
        rcases List.mem_cons.mp hz with hz | hz
        · rw [hz]; exact hyx
        · obtain ⟨u, h3, h4, rfl⟩ := mem_segN.mp (hRp.mem_iff.mp hz)
          have := hpr u (by omega) (by omega)
          omega
  · -- segment of length ≤ 1: nothing to do
    have hc : ¬ sgn lo < sgn hiW := by
      by_cases hz : lo + len = 0
      · have e1 : lo = 0 := by omega
        have e2 : len = 0 := by omega
        subst e1 e2
        rw [hW, hiW_zero, sgn_max, sgn_small 0 (by omega)]; decide
      · rw [hW, hiW_pos lo len (by omega) (by omega), sgn_small _ (by omega), sgn_small _ (by omega)]
        omega
    refine qs_short h0 h1 h2 hc ?_
    intro m' hn' hm'
    refine h m' ⟨by omega, fun q hq _ => hm' q hq, ?_, segN_short_sorted _ _ _ _ (by omega)⟩
    rw [segN_congr m m' a lo len (fun t _ h2 => hm' _ (by omega))]

/-! ## From list facts to the Bool-valued spec -/

theorem segN_getAt (m : Mem) (a n : Nat) :
    (List.range n).map (getAt (fun p => Mem.get m p) a) = segN m a 0 n := by
  unfold segN getAt
  rw [List.range_eq_range']
  apply List.map_congr_left
  intro t _
  rw [Nat.add_comm]

theorem sortedAt_of_pairwise (m : Mem) (a n : Nat) (h : (segN m a 0 n).Pairwise (· ≤ ·)) :
    SortedAt (fun p => Mem.get m p) a n = true := by
  unfold SortedAt
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [List.pairwise_iff_getElem] at h
  have hl : (segN m a 0 n).length = n := by simp [segN]
  have := h i (i + 1) (by omega) (by omega) (by omega)
  simp only [segN, List.getElem_map, List.getElem_range'] at this
  apply decide_eq_true
  simp only [getAt]
  rw [Nat.add_comm a (4 * i), Nat.add_comm a (4 * (i + 1))]
  simpa using this

theorem permAt_of_perm (m m₀ : Mem) (a n : Nat) (h : (segN m a 0 n).Perm (segN m₀ a 0 n)) :
    PermAt (fun p => Mem.get m p) (fun p => Mem.get m₀ p) a n = true := by
  unfold PermAt
  simp only
  rw [segN_getAt, segN_getAt, List.all_eq_true]
  intro x _
  rw [h.count_eq]
  exact beq_self_eq_true _

/-! ## The corrected top-level theorem -/

/-- `sort_cspec`, with the two hypotheses the original statement is missing:
    * `hnext`: the frame allocator starts above the caller's array
      (the doc comment of `validAt` assumes this, but `m₀` is arbitrary);
    * `hsmall`: every input word is `< 2^31`, so the C code's *signed*
      comparisons agree with `SortedAt`'s `Nat` order. -/
theorem sort_cspec : sort_cspec_type := by
  intro c_a c_n m₀ hpre
  -- §1 showed the original precondition was missing hypotheses; the spec
  -- comment in qsort.c now carries all four.  Extract them with term-mode
  -- Bool lemmas (`&&` is left-associative: ((A && B) && C) && D).
  have hall : (validAt c_a c_n && c_n ≤ 8 && 1024 ≤ m₀.next &&
               SmallAt (fun p => Mem.get m₀ p) c_a c_n) = true := by
    simpa using hpre
  obtain ⟨h1, hsmallb⟩ := Bool.and_eq_true_iff.mp hall
  obtain ⟨h2, hnextd⟩ := Bool.and_eq_true_iff.mp h1
  obtain ⟨hva, hn8d⟩ := Bool.and_eq_true_iff.mp h2
  have hnext : 1024 ≤ m₀.next := of_decide_eq_true hnextd
  have hn8 : c_n ≤ 8 := of_decide_eq_true hn8d
  have hv : c_a + 4 * c_n ≤ 1024 ∧ c_n ≤ 8 := by
    constructor
    · simpa [validAt] using hva
    · exact hn8
  have hsmall : ∀ i, i < c_n → getAt (fun p => Mem.get m₀ p) c_a i < 2147483648 :=
    fun i hi => Spec.smallAt_bound hsmallb i hi
  let P : Config → Prop := fun d => ∃ m', stepOne projectM d = StepR.fin 0 m' ∧
    (segN m' c_a 0 c_n).Perm (segN m₀ c_a 0 c_n) ∧ (segN m' c_a 0 c_n).Pairwise (· ≤ ·)
  have hR : Reach projectM (blkCfg "sort" sortF "0" none [("0", c_a), ("1", c_n)] m₀ Cont.top) P := by
    have hn8 : c_n < 2147483648 := by omega
    runI []
    by_cases hc : 0 < c_n
    · brn [hc]
      runI [hc]
      apply qs_call c_n c_n rfl (a := c_a) (lo := 0) (hiW := w32 (↑c_n - ↑(1 : Nat)))
      · nrm []
      · rfl
      · nrm []
      · rw [Nat.zero_add]; rfl
      · omega
      · nrm []; omega
      · intro t _ h2
        have := hsmall t (by omega)
        simp only [getAt] at this
        nrm []; rw [Nat.add_comm]; exact this
      intro m' hq
      obtain ⟨_, _, hperm, hsort⟩ := hq
      stp
      apply Reach.done
      refine ⟨m', rfl, ?_, ?_⟩
      · refine hperm.trans ?_
        rw [segN_congr m₀ _ c_a 0 c_n]
        intro t _ h2; nrm []
      · exact hsort
    · brn [hc]
      apply Reach.done
      have e : c_n = 0 := by omega
      subst e
      exact ⟨_, rfl, by simp [segN], by simp [segN]⟩
  obtain ⟨n, d, ⟨m', hfin, hperm, hsort⟩, hrun⟩ := hR.runM
  refine ⟨1 + n, 0, m', ?_, ?_⟩
  · have h1 := hrun 1
    have h2 : Ll.runM 1 projectM d = Res.val 0 m' := by rw [runM_succ, hfin]
    exact h1.trans h2
  · simp only [sortedAt_of_pairwise m' c_a c_n hsort, permAt_of_perm m' m₀ c_a c_n hperm, Bool.and_self]

end C2Lean
