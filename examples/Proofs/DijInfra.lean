import Proofs.DijkstraSpec
import Proofs.Reach
/-! Machine-stepping infrastructure (ported from the qsort proof).
    Tactics carry a `d` prefix (`dnrm`, `dbrt`, ...) because `Proofs/Reach.lean`
    defines the same names with the qsort simp set; the sets differ, the
    proofs below are calibrated to this one. `Ll.Instr.isCall` is shared. -/
namespace DijP
open Ll C2Lean

theorem w32_mul (a b : Nat) (h : a * b < 4294967296) : w32 ((a : Int) * (b : Int)) = a * b := by
  have e : ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) := by push_cast; rfl
  rw [e, w32_eq _ (by omega) (by omega), Int.toNat_natCast]

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

theorem w32_add' (a b : Nat) (h : a + b < 4294967296) : w32 ((a : Int) + (b : Int)) = a + b := by
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
theorem w32_gep (x y : Nat) (h : 4 * x + y < 4294967296) :
    w32 (4 * (x : Int) + (y : Int)) = 4 * x + y := by
  rw [w32_eq _ (by omega) (by omega)]; omega

theorem nat_eq_false {x y : Nat} (h : x ≠ y) : (x = y) = False := by simp [h]

syntax "dnrm" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| dnrm $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| simp (disch := omega) only [Mem.get_set_eq', Mem.get_set_ne', blkCfg, minDistanceF, dijkstraF, List.lookup, evOperand, Env.get_set', Env.get_cons, Env.get_nil, roundup4_4, Nat.add_assoc, Nat.reduceAdd, reduceIte, String.reduceEq, String.reduceBEq, beq_self_eq_true, Bool.false_eq_true, ite_true, ite_false, Mem.get_withNext, Mem.set_next, List.zip, List.zipWith, List.map, evBin, evRel, w32_nat, w32_add', w32_mul, w32_sub, w32_dec, w32_gep, sgn_small, Int.ofNat_lt, Int.ofNat_le, Nat.add_zero, gt_iff_lt, ge_iff_le, ne_eq, Nat.reduceEqDiff, not_false_eq_true, nat_eq_false, beq_iff_eq, $xs,*])

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

theorem Reach.step_i {mod : Module} {fn lbl : String} {prev : Option String} {i : Instr}
    {r : List Instr} {tm : Term} {e : Env} {m : Mem} {k : Cont} {c' : Config} {D : Config → Prop}
    (_hnc : i.isCall = false)
    (hs : stepOne mod ⟨fn, lbl, prev, i :: r, tm, e, m, k⟩ = StepR.cont c')
    (h : Reach mod c' D) : Reach mod ⟨fn, lbl, prev, i :: r, tm, e, m, k⟩ D :=
  Reach.step _ _ _ hs h

syntax "dbrt" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| dbrt $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| (apply Reach.br_t; (focus (dnrm [$xs,*]; done)); (focus rfl)))

syntax "drunI" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| drunI $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| ((try dnrm [$xs,*]); repeat ((apply Reach.step_i rfl; · rfl); try dnrm [$xs,*])))

syntax "dbrn" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| dbrn $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| ((first | (apply Reach.br_t; (focus (dnrm [$xs,*]; done)); (focus rfl)) | (apply Reach.br_f; (focus (dnrm [$xs,*]; done)); (focus rfl))); try dnrm [$xs,*]))

syntax "drun" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| drun $[[$xs,*]]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| ((try dnrm [$xs,*]); repeat ((first | (apply Reach.br_t; (focus (dnrm [$xs,*]; done)); (focus rfl)) | (apply Reach.br_f; (focus (dnrm [$xs,*]; done)); (focus rfl)) | (apply Reach.step_i rfl; · rfl)); try dnrm [$xs,*])))

macro "dstp" : tactic => `(tactic| (apply Reach.step'; · rfl))

end DijP
