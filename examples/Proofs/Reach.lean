import C2Lean.Programs
/-!
# Shared stepping machinery for symbolic whole-run proofs

`Reach mod c P` = "configuration `c` reaches some configuration satisfying `P`".
`Reach.runM` converts a finite step chain into a `runM` equation WITHOUT the
kernel ever whnf-ing a whole run: direct `rfl`/whnf on `runModule` terms for
loop-heavy functions diverges (mystery `maxRecDepth` even at 10^6), so every
symbolic run proof in this repo goes through this interface instead.

`nrm` normalizes one machine step (simp, side conditions to `omega`);
`runI` steps a block's instructions, `brn`/`brt`/`brf` take a branch,
`stp` steps one instruction by hand, `run` mixes all three.

Extracted verbatim from `Proofs/Qsort.lean` (the sorting proof was the
first consumer); `Proofs/Arrsum.lean` is the second.
-/

namespace C2Lean
open Ll Spec

/-- `runModule` inherits fuel monotonicity from `runM`. -/
theorem runModule_mono_val (mod : Module) (fn : String) (args : List Nat)
    (fuel v : Nat) (m₀ m : Mem) (h : runModule mod fn args fuel m₀ = Res.val v m)
    (k : Nat) : runModule mod fn args (fuel + k) m₀ = Res.val v m := by
  unfold runModule at *
  split at h
  · cases h
  · split at h
    · cases h
    · exact runM_mono_val _ _ _ _ _ h k

/-- Determinism across fuel: two successful runs agree. -/
theorem runModule_val_unique (mod : Module) (fn : String) (args : List Nat)
    (f₁ f₂ v₁ v₂ : Nat) (m₀ m₁ m₂ : Mem)
    (h₁ : runModule mod fn args f₁ m₀ = Res.val v₁ m₁)
    (h₂ : runModule mod fn args f₂ m₀ = Res.val v₂ m₂) : v₁ = v₂ ∧ m₁ = m₂ := by
  have a := runModule_mono_val _ _ _ _ _ _ _ h₁ f₂
  have b := runModule_mono_val _ _ _ _ _ _ _ h₂ f₁
  rw [Nat.add_comm] at b
  rw [a] at b
  cases b
  exact ⟨rfl, rfl⟩

/-! ## Reachability in the module machine -/

inductive Reach (mod : Module) : Config → (Config → Prop) → Prop
  | done (c : Config) (P : Config → Prop) : P c → Reach mod c P
  | step (c c' : Config) (P : Config → Prop) :
      stepOne mod c = StepR.cont c' → Reach mod c' P → Reach mod c P

theorem Reach.bind {mod : Module} {a : Config} {Q P : Config → Prop}
    (h1 : Reach mod a Q) (h2 : ∀ b, Q b → Reach mod b P) : Reach mod a P := by
  induction h1 with
  | done c _ h => exact h2 c h
  | step c c' _ hs _ ih => exact Reach.step _ _ _ hs (ih h2)

theorem Reach.trans {mod : Module} {a b : Config} {P : Config → Prop}
    (h1 : Reach mod a (· = b)) (h2 : Reach mod b P) : Reach mod a P :=
  Reach.bind h1 (fun _ h => h ▸ h2)

theorem Reach.runM {mod : Module} {c : Config} {P : Config → Prop} (h : Reach mod c P) :
    ∃ n d, P d ∧ ∀ F, Ll.runM (F + n) mod c = Ll.runM F mod d := by
  induction h with
  | done c _ h => exact ⟨0, c, h, fun F => rfl⟩
  | step c c' _ hs _ ih =>
    obtain ⟨n, d, hd, hn⟩ := ih
    refine ⟨n + 1, d, hd, fun F => ?_⟩
    rw [show F + (n + 1) = (F + n) + 1 by omega, runM_succ, hs]
    exact hn F

/-! ## Simp API -/

theorem Env.get_set' (e : Env) (n m : String) (v : Nat) :
    Env.get (Env.set e n v) m = if m = n then v else Env.get e m := by
  by_cases h : m = n
  · subst h; simp [Env.set_same]
  · simp only [h, ite_false]; rw [Env.set_other]; simpa using h

theorem Mem.get_set_eq' (m : Mem) (a b v : Nat) (h : b = a) :
    Mem.get (Mem.set m a v) b = v := by subst h; exact Mem.get_set_same _ _ _

theorem Mem.get_set_ne' (m : Mem) (a b v : Nat) (h : b ≠ a) :
    Mem.get (Mem.set m a v) b = Mem.get m b := Mem.get_set_other _ _ _ _ h

@[simp] theorem Mem.get_withNext (m : Mem) (n b : Nat) :
    Mem.get { m with next := n } b = Mem.get m b := rfl

@[simp] theorem Mem.set_next (m : Mem) (a v : Nat) : (Mem.set m a v).next = m.next := rfl

theorem w32_nat (n : Nat) (h : n < 4294967296) : w32 (n : Int) = n := by
  rw [w32_eq _ (by omega) (by omega)]; simp

theorem w32_add (a b : Nat) (h : a + b < 4294967296) : w32 ((a : Int) + (b : Int)) = a + b := by
  rw [w32_eq _ (by omega) (by omega)]; omega

theorem w32_sub (a b : Nat) (h : b ≤ a) (h2 : a < 4294967296) :
    w32 ((a : Int) - (b : Int)) = a - b := by
  rw [w32_eq _ (by omega) (by omega)]; omega

theorem w32_dec (a : Nat) (h : 1 ≤ a) (h2 : a < 4294967296) :
    w32 ((a : Int) + ((4294967295 : Nat) : Int)) = a - 1 := by
  have e : (a : Int) + ((4294967295 : Nat) : Int) = ((a - 1 : Nat) : Int) + (MOD : Int) := by
    simp only [MOD]; omega
  unfold w32
  rw [e, Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by simp only [MOD]; omega)]
  simp

theorem sgn_small (x : Nat) (h : x < 2147483648) : sgn x = (x : Int) := sgn_id x h

theorem roundup4_4 : roundup4 4 = 4 := rfl

/-! ## Configs and stepping -/

def blkCfg (fn : String) (g : Func) (lbl : String) (prev : Option String) (e : Env) (m : Mem)
    (k : Cont) : Config :=
  match g.blocks.lookup lbl with
  | some (is, t) => ⟨fn, lbl, prev, is, t, e, m, k⟩
  | none => ⟨fn, lbl, prev, [], Term.retv, e, m, k⟩

theorem Mem.get_set_ite (m : Mem) (a b v : Nat) :
    Mem.get (Mem.set m a v) b = if b = a then v else Mem.get m b := by
  split
  · subst_vars; exact Mem.get_set_same _ _ _
  · exact Mem.get_set_other _ _ _ _ (by assumption)

theorem Reach.step' {mod : Module} {c c' : Config} {d : Config → Prop} (hs : stepOne mod c = StepR.cont c')
  (h : Reach mod c' d) : Reach mod c d := Reach.step _ _ _ hs h

macro "norm" : tactic => `(tactic| simp (disch := omega) only [Mem.get_set_eq', Mem.get_set_ne', blkCfg, swapF, partitionF, quickSortF, sortF, List.lookup, evOperand, Env.get_set', Env.get_cons, Env.get_nil, roundup4_4, Nat.add_assoc, Nat.reduceAdd, reduceIte, String.reduceEq, String.reduceBEq, beq_self_eq_true, Bool.false_eq_true, ite_true, ite_false, Mem.get_withNext, Mem.set_next, List.zip, List.zipWith, List.map] )
macro "stp" : tactic => `(tactic| (apply Reach.step'; · rfl))

theorem w32_gep (x y : Nat) (h : 4 * x + y < 4294967296) :
    w32 (4 * (x : Int) + (y : Int)) = 4 * x + y := by
  rw [w32_eq _ (by omega) (by omega)]; omega

theorem nat_eq_false {x y : Nat} (h : x ≠ y) : (x = y) = False := by simp [h]

syntax "nrm" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| nrm $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| simp (disch := omega) only [Mem.get_set_eq', Mem.get_set_ne', blkCfg, swapF, partitionF, quickSortF, sortF, List.lookup, evOperand, Env.get_set', Env.get_cons, Env.get_nil, roundup4_4, Nat.add_assoc, Nat.reduceAdd, reduceIte, String.reduceEq, String.reduceBEq, beq_self_eq_true, Bool.false_eq_true, ite_true, ite_false, Mem.get_withNext, Mem.set_next, List.zip, List.zipWith, List.map, evBin, evRel, w32_nat, w32_add, w32_sub, w32_dec, w32_gep, sgn_small, Int.ofNat_lt, Int.ofNat_le, Nat.add_zero, gt_iff_lt, ge_iff_le, ne_eq, Nat.reduceEqDiff, not_false_eq_true, nat_eq_false, Int.reduceLT, Nat.reduceLT, Nat.reduceBEq, decide_eq_true_eq, $xs,*])

theorem Reach.br_t {mod : Module} {fn lbl : String} {prev : Option String} {c : Operand}
    {t fl : String} {e : Env} {m : Mem} {k : Cont} {is : List Instr} {tm : Term} {D : Config → Prop}
    (hc : evOperand e c ≠ 0) (hl : (mod.lookup fn).bind (fun g => g.blocks.lookup t) = some (is, tm))
    (h : Reach mod ⟨fn, t, some lbl, is, tm, e, m, k⟩ D) :
    Reach mod ⟨fn, lbl, prev, [], Term.br c t fl, e, m, k⟩ D := by
  refine Reach.step _ _ _ ?_ h
  have : (evOperand e c == 0) = false := by simpa using hc
  simp only [stepOne, this, Bool.false_eq_true, ite_false, hl]

theorem Reach.br_f {mod : Module} {fn lbl : String} {prev : Option String} {c : Operand}
    {t fl : String} {e : Env} {m : Mem} {k : Cont} {is : List Instr} {tm : Term} {D : Config → Prop}
    (hc : evOperand e c = 0) (hl : (mod.lookup fn).bind (fun g => g.blocks.lookup fl) = some (is, tm))
    (h : Reach mod ⟨fn, fl, some lbl, is, tm, e, m, k⟩ D) :
    Reach mod ⟨fn, lbl, prev, [], Term.br c t fl, e, m, k⟩ D := by
  refine Reach.step _ _ _ ?_ h
  simp only [stepOne, hc, beq_self_eq_true, ite_true, hl]

def _root_.Ll.Instr.isCall : Instr → Bool
  | Instr.call _ _ _ => true
  | Instr.callv _ _ => true
  | _ => false

theorem Reach.step_i {mod : Module} {fn lbl : String} {prev : Option String} {i : Instr}
    {r : List Instr} {tm : Term} {e : Env} {m : Mem} {k : Cont} {c' : Config} {D : Config → Prop}
    (_hnc : i.isCall = false)
    (hs : stepOne mod ⟨fn, lbl, prev, i :: r, tm, e, m, k⟩ = StepR.cont c')
    (h : Reach mod c' D) : Reach mod ⟨fn, lbl, prev, i :: r, tm, e, m, k⟩ D :=
  Reach.step _ _ _ hs h

syntax "brt" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brt $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| (apply Reach.br_t; (focus (nrm [$xs,*]; done)); (focus rfl)))

syntax "runI" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| runI $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| ((try nrm [$xs,*]); repeat ((apply Reach.step_i rfl; · rfl); try nrm [$xs,*])))

syntax "brn" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brn $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| ((first | (apply Reach.br_t; (focus (nrm [$xs,*]; done)); (focus rfl)) | (apply Reach.br_f; (focus (nrm [$xs,*]; done)); (focus rfl))); try nrm [$xs,*]))

syntax "run" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| run $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| ((try nrm [$xs,*]); repeat ((first | (apply Reach.br_t; (focus (nrm [$xs,*]; done)); (focus rfl)) | (apply Reach.br_f; (focus (nrm [$xs,*]; done)); (focus rfl)) | (apply Reach.step_i rfl; · rfl)); try nrm [$xs,*])))

end C2Lean
