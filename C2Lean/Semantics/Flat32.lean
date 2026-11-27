/-!
  # A (tiny) faithful LLVM subset, embedded in Lean

  This file embeds a small but faithful fragment of LLVM IR: basic blocks,
  `icmp`, conditional branches and `phi` (i.e. *loops*), **memory**
  (`alloca`, `load`, `store`, `getelementptr`), and function calls with
  recursion. Consequences of honesty:

  * `runFunc` now takes **fuel** and can return `Result.stuck` ("ran out of
    fuel") — nontermination is now expressible, so fuel is load-bearing.
  * `phi` needs the **predecessor block**, so the interpreter threads
    `prev : Option String` exactly like LLVM's SSA semantics demands.
  * memory is byte-addressed with word granularity; in this subset every
    pointer comes from `alloca` or `gep` at word-aligned offsets, so
    misaligned access is unreachable (a real machine would trap; here
    alignment holds *by construction* — see `lean/C2Lean/Proofs/Memory.lean`).

  Design:
  * words are `Nat < 2^32`, every `bin` reduces with `w32`;
  * SSA environments are functions `String → Nat`;
  * malformed programs yield `err`, never a silent wrong answer;
  * memory is a flat byte-addressed word array (`Mem.cells`) plus a bump
    pointer (`Mem.next`) for `alloca`. Unallocated reads return 0 —
    a modeling choice ("zero-initialized memory"); LLVM calls them poison.

  Section map: 1 words/env · 2 memory · 3 syntax · 4 single-function
  interpreter · 5 module machine · 6 machine API lemmas.
-/

namespace Ll

/-! ────────────────────────────────────────────────────────────
    ## 1. Words and SSA environments

    32-bit word model (`w32`) and the register environment, with its
          read/write lemmas (`Env.get_cons`, `set_same`, `set_other`).
    ──────────────────────────────────────────────────────────── -/

/-- 32-bit word universe. -/
def MOD : Nat := 4294967296

/-- Reduce an integer to its 32-bit representative. -/
def w32 (z : Int) : Nat := Int.toNat (z % (MOD : Int))

/-- SSA environment: an association list of register bindings.
    Deliberately a *bounded* representation (updates replace, never grow):
    a function-type env makes each read O(#steps-so-far), making whole
    runs quadratic — both to evaluate and to prove about.
    `@[reducible]` so that `rw` can unify `Env` with its representation. -/
@[reducible] def Env : Type := List (String × Nat)

/-- Read a register; unbound reads as 0 (malformed-program discipline
    turns real misuses into `err` at the use site, e.g. phi).
    Direct structural recursion — the `lookup.getD` formulation whnf'd
    catastrophically badly in the kernel (mystery `maxRecDepth` on `rfl`). -/
def Env.get : Env → String → Nat
  | [], _ => 0
  | (m, v) :: r, n => if n == m then v else Env.get r n

@[simp] theorem Env.get_nil (n : String) : Env.get ([] : Env) n = 0 := rfl

@[simp]
theorem Env.get_cons (e : Env) (a m : String) (b : Nat) :
    Env.get ((a, b) :: e) m = if m == a then b else Env.get e m := rfl

/-- `Env.set e n v` binds register `n` to `v`, replacing any old binding
    so the list never contains duplicates (bounded register file). -/
def Env.set : Env → String → Nat → Env
  | [], n, v => [(n, v)]
  | (m, w) :: rest, n, v =>
      if m == n then (n, v) :: rest else (m, w) :: Env.set rest n v

theorem Env.set_nil (n : String) (v : Nat) : Env.set ([] : Env) n v = [(n, v)] := rfl

theorem Env.set_cons (m : String) (w : Nat) (rest : Env) (n : String) (v : Nat) :
    Env.set ((m, w) :: rest) n v =
      if m == n then (n, v) :: rest else (m, w) :: Env.set rest n v := rfl

theorem Env.set_same (e : Env) (n : String) (v : Nat) :
    Env.get (Env.set e n v) n = v := by
  induction e with
  | nil => simp [Env.set_nil]
  | cons p rest ih =>
      rcases p with ⟨a, b⟩
      by_cases h : a = n
      · subst n
        rw [Env.set_cons, ite_eq_left (by simp), Env.get_cons, ite_eq_left (by simp)]
      · rw [Env.set_cons, ite_eq_right (by simp [h]), Env.get_cons,
            ite_eq_right (by
              intro hh
              have hn : n = a := by simpa using hh
              exact h hn.symm), ih]

theorem Env.set_other (e : Env) (n m : String) (v : Nat) (h : ¬(m == n)) :
    Env.get (Env.set e n v) m = Env.get e m := by
  induction e with
  | nil => rw [Env.set_nil]; simp [h]
  | cons p rest ih =>
      rcases p with ⟨a, b⟩
      by_cases han : a = n
      · subst n
        rw [Env.set_cons, ite_eq_left (by simp), Env.get_cons, Env.get_cons]
        by_cases ham : m = a
        · subst m
          exact absurd (by simp) h
        · rw [ite_eq_right (by simp [ham]), ite_eq_right (by simp [ham])]
      · rw [Env.set_cons, ite_eq_right (by simp [han]), Env.get_cons, Env.get_cons]
        by_cases ham : m = a
        · subst m
          rw [ite_eq_left (by simp), ite_eq_left (by simp)]
        · rw [ite_eq_right (by simp [ham]), ite_eq_right (by simp [ham])]
          exact ih

/-! ────────────────────────────────────────────────────────────
    ## 2. Memory

    Operands, the flat word-addressed store `Mem` with its read/write
          API (`get_set_same`, `get_set_other`), and allocation sizing.
    ──────────────────────────────────────────────────────────── -/

/-- LLVM operands: an SSA register or an integer immediate. -/
inductive Operand : Type where
  | reg : String → Operand
  | imm : Nat → Operand

/-- Flat memory: byte-addressed cells (each holding one `i32` word at a
    4-aligned address) plus a bump pointer used by `alloca`. -/
structure Mem where
  cells : List (Nat × Nat)
  next  : Nat
deriving DecidableEq, Repr

/-- Fresh frame: empty memory, frame starts at byte 1024. -/
def Mem.empty : Mem := { cells := [], next := 1024 }

def Mem.cellsGet : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (k, v) :: r, a => if a == k then v else Mem.cellsGet r a

def Mem.cellsSet : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], a, v => [(a, v)]
  | (k, w) :: r, a, v =>
      if k == a then (a, v) :: r else (k, w) :: Mem.cellsSet r a v

def Mem.get (m : Mem) (a : Nat) : Nat := Mem.cellsGet m.cells a

def Mem.set (m : Mem) (a : Nat) (v : Nat) : Mem :=
  { m with cells := Mem.cellsSet m.cells a v }

@[simp] theorem Mem.cellsGet_nil (a : Nat)
    : Mem.cellsGet ([] : List (Nat × Nat)) a = 0 := rfl

@[simp] theorem Mem.cellsGet_cons (r : List (Nat × Nat)) (k v a : Nat) :
    Mem.cellsGet ((k, v) :: r) a = if a == k then v else Mem.cellsGet r a := rfl

theorem Mem.cellsGet_cellsSet (l : List (Nat × Nat)) (a v : Nat) :
    Mem.cellsGet (Mem.cellsSet l a v) a = v := by
  induction l with
  | nil => simp [Mem.cellsSet]
  | cons p rest ih =>
      rcases p with ⟨k, w⟩
      by_cases hk : k = a
      · subst hk
        simp [Mem.cellsSet]
      · simp [Mem.cellsSet, hk, ih]
        omega

theorem Mem.cellsGet_cellsSet_other (l : List (Nat × Nat)) (a b v : Nat)
    (h : ¬(b = a)) : Mem.cellsGet (Mem.cellsSet l a v) b = Mem.cellsGet l b := by
  induction l with
  | nil => simp [Mem.cellsSet, Mem.cellsGet, h]
  | cons p rest ih =>
      rcases p with ⟨k, w⟩
      by_cases hka : k = a
      · subst hka
        simp [Mem.cellsGet_cons, Mem.cellsSet, Mem.cellsGet, h]
      · simp only [Mem.cellsSet, Mem.cellsGet_cons]
        rw [ite_eq_right (by simp [hka])]
        by_cases hb : b == k
        · simp [hb]
        · simp [hb, ih]

theorem Mem.get_set_same (m : Mem) (a : Nat) (v : Nat) :
    Mem.get (Mem.set m a v) a = v :=
  Mem.cellsGet_cellsSet m.cells a v

theorem Mem.get_set_other (m : Mem) (a b : Nat) (v : Nat) (h : ¬(b = a)) :
    Mem.get (Mem.set m a v) b = Mem.get m b :=
  Mem.cellsGet_cellsSet_other m.cells a b v h

/-- Round up an allocation size to a multiple of 4. -/
def roundup4 (n : Nat) : Nat := (n + 3) / 4 * 4

-- Frame-allocation bookkeeping: `store` leaves `next` alone, and
-- `alloca` grows `next` via a record update that leaves cells alone.
-- These projections keep the `get_set_*` lemmas matching when the
-- machine reads a frame base back after allocation.
theorem Mem.next_set (m : Mem) (a v : Nat) : (m.set a v).next = m.next := rfl

theorem Mem.get_of_next_update (m : Mem) (n a : Nat) :
    ({ m with next := n }.get a) = m.get a := rfl

/-! ────────────────────────────────────────────────────────────
    ## 3. Program syntax

    The instruction/term algebra: `BinOp`, `Rel`, `Instr`, `Term`,
          `Block`, `Func`, `Result`, and the signed view `sgn`.
    ──────────────────────────────────────────────────────────── -/

/-- The binary operations of this fragment (all `i32`). -/
inductive BinOp : Type where
  | add | sub | mul | and | or | xor | shl | lshr

/-- Comparison predicates of `icmp` (unsigned, signed, equality). -/
inductive Rel : Type where
  | ult | ule | ugt | uge
  | slt | sle | sgt | sge
  | eq  | ne

/-- Signed view of a word: `x ≥ 2^31` reads as `x - 2^32`. -/
def sgn (x : Nat) : Int := if (x : Int) < 2147483648 then x else (x : Int) - 4294967296

/-- Below `2^31` the signed view is the identity. -/
theorem sgn_id (x : Nat) (h : x < 2147483648) : sgn x = (x : Int) := by
  unfold sgn
  exact ite_eq_left (by omega)

/-- One non-terminating instruction. -/
inductive Instr : Type where
  | bin  : BinOp → String → Operand → Operand → Instr
  | icmp : Rel → String → Operand → Operand → Instr
  | select : String → Operand → Operand → Operand → Instr
  /-- `%d = phi [(v₀, lbl₀), (v₁, lbl₁), …]` — value depends on where
      we came from. -/
  | phi  : String → List (Operand × String) → Instr
  /-- `%d = alloca i32` (`nbytes` bytes): fresh frame slot, pointer in `d`. -/
  | alloca : String → Nat → Instr
  /-- `%d = load i32, ptr %p`. -/
  | load   : String → Operand → Instr
  /-- `store i32 %v, ptr %p`. -/
  | store  : Operand → Operand → Instr
  /-- `%d = getelementptr i32, ptr %base, i32 %idx` → `base + 4*idx`. -/
  | gep    : String → Operand → Operand → Instr
  /-- `%d = call i32 @fn(args…)` — call with a result. -/
  | call   : String → String → List Operand → Instr
  /-- `call void @fn(args…)` — call for its side effects only. -/
  | callv  : String → List Operand → Instr

/-- A block terminator. -/
inductive Term : Type where
  | ret  : Operand → Term
  | retv : Term                       -- `ret void` (side-effect-only return)
  | br   : Operand → String → String → Term   -- cond, true-label, false-label
  | jump : String → Term

/-- A basic block: instructions + terminator. -/
@[reducible] def Block : Type := List Instr × Term

/-- A function: parameters and a label-keyed block table (`entry` first). -/
structure Func : Type where
  params : List String
  blocks : List (String × Block)

/-- The observable outcome of running a function. -/
inductive Result : Type where
  | val   (n : Nat)
  | err   (msg : String)
  | stuck            -- fuel exhausted (the program may not terminate)
  deriving DecidableEq, Repr

/-! ────────────────────────────────────────────────────────────
    ## 4. The single-function interpreter

    Operand/binary/relation evaluation, block execution, `runFunc`.
          Its API lemmas (`runBlock_succ`, `w32_eq`) sit right below it.
    ──────────────────────────────────────────────────────────── -/

/-- Evaluate an operand in an environment. -/
def evOperand (e : Env) (o : Operand) : Nat :=
  match o with
  | Operand.reg n => Env.get e n
  | Operand.imm k => k

/-- Evaluate a binary operation, always reducing to a 32-bit word. -/
def evBin (op : BinOp) (a b : Nat) : Nat :=
  match op with
  | BinOp.add  => w32 (a + b)
  | BinOp.sub  => w32 ((a : Int) - b)
  | BinOp.mul  => w32 (a * b)
  | BinOp.and  => Nat.land a b
  | BinOp.or   => Nat.lor a b
  | BinOp.xor  => Nat.xor a b
  | BinOp.shl  => w32 (Nat.shiftLeft a (b % 32))
  | BinOp.lshr => Nat.shiftRight a (b % 32)

/-- `icmp` yields 0/1. -/
def evRel : Rel → Nat → Nat → Nat
  | Rel.ult, a, b => if a < b then 1 else 0
  | Rel.ule, a, b => if a ≤ b then 1 else 0
  | Rel.ugt, a, b => if b < a then 1 else 0
  | Rel.uge, a, b => if b ≤ a then 1 else 0
  | Rel.slt, a, b => if sgn a < sgn b then 1 else 0
  | Rel.sle, a, b => if sgn a ≤ sgn b then 1 else 0
  | Rel.sgt, a, b => if sgn a > sgn b then 1 else 0
  | Rel.sge, a, b => if sgn a ≥ sgn b then 1 else 0
  | Rel.eq,  a, b => if a == b then 1 else 0
  | Rel.ne,  a, b => if a == b then 0 else 1

/-- The value a `phi` takes when arriving from block `prev`. -/
def evPhi (prev : Option String) (e : Env) (cs : List (Operand × String)) :
    Option Nat :=
  match prev with
  | none => none
  | some p =>
      match cs.find? (fun (_, l) => l == p) with
      | some (o, _) => some (evOperand e o)
      | none => none

/-- Run the straight-line instructions of one block, threading memory. -/
inductive Step : Type where
  | ok  (e : Env) (m : Mem)
  | err (msg : String)

def execInstrs (prev : Option String) : List Instr → Env → Mem → Step
  | [], e, m => Step.ok e m
  | Instr.bin op d a b :: r, e, m =>
      execInstrs prev r (Env.set e d (evBin op (evOperand e a) (evOperand e b))) m
  | Instr.icmp rel d a b :: r, e, m =>
      execInstrs prev r (Env.set e d (evRel rel (evOperand e a) (evOperand e b))) m
  | Instr.select d c a b :: r, e, m =>
      execInstrs prev r
        (Env.set e d (if evOperand e c == 0 then evOperand e b else evOperand e a)) m
  | Instr.phi d cs :: r, e, m =>
      match evPhi prev e cs with
      | some v => execInstrs prev r (Env.set e d v) m
      | none => Step.err "phi with unknown predecessor"
  | Instr.alloca d nbytes :: r, e, m =>
      execInstrs prev r (Env.set e d m.next)
        { m with next := m.next + roundup4 nbytes }
  | Instr.load d p :: r, e, m =>
      execInstrs prev r (Env.set e d (Mem.get m (evOperand e p))) m
  | Instr.store v p :: r, e, m =>
      execInstrs prev r e (Mem.set m (evOperand e p) (evOperand e v))
  | Instr.gep d b i :: r, e, m =>
      -- `4*idx + base` (not `base + 4*idx`): with `base = 0` the addition
      -- reduces definitionally (`Nat.add` recurses on its second argument).
      execInstrs prev r
        (Env.set e d (w32 (4 * evOperand e i + evOperand e b))) m
  | Instr.call _ _ _ :: _, _, _ => Step.err "call: not supported by the call-free interpreter"
  | Instr.callv _ _ :: _, _, _ => Step.err "call: not supported by the call-free interpreter"

/-- Run a function body with fuel; one unit of fuel per block entry. -/
def runBlock : Nat → Func → String → Option String → Env → Mem → Result
  | 0, _, _, _, _, _ => Result.stuck
  | fuel + 1, f, lbl, prev, e, m =>
      match f.blocks.lookup lbl with
      | none => Result.err "missing block"
      | some (instrs, term) =>
          match execInstrs prev instrs e m with
          | Step.err msg => Result.err msg
          | Step.ok e' m' =>
              match term with
              | Term.ret o => Result.val (evOperand e' o)
              | Term.retv => Result.err "ret void (needs the module interpreter)"
              | Term.jump l => runBlock fuel f l (some lbl) e' m'
              | Term.br c t fl =>
                  runBlock fuel f (if evOperand e' c == 0 then fl else t)
                    (some lbl) e' m'

/-- Run a function on arguments with a fuel budget and initial memory. -/
def runFuncM (f : Func) (args : List Nat) (fuel : Nat) (m : Mem) : Result :=
  match f.blocks with
  | [] => Result.err "no blocks"
  | (lbl, _) :: _ => runBlock fuel f lbl none (f.params.zip args) m

/-- Run a function on arguments with a fuel budget; fresh empty frame. -/
def runFunc (f : Func) (args : List Nat) (fuel : Nat) : Result :=
  runFuncM f args fuel Mem.empty

/-- One-step unfolding at a successor fuel, in a clean `rfl`-provable form
    (the auto-generated equation lemmas are too folded-up for `simp`). -/
theorem runBlock_succ (f : Func) (lbl : String) (prev : Option String) (e : Env)
    (m : Mem) (fuel : Nat) :
    runBlock (fuel + 1) f lbl prev e m =
      match f.blocks.lookup lbl with
      | none => Result.err "missing block"
      | some (instrs, term) =>
          match execInstrs prev instrs e m with
          | Step.err msg => Result.err msg
          | Step.ok e' m' =>
              match term with
              | Term.ret o => Result.val (evOperand e' o)
              | Term.retv => Result.err "ret void (needs the module interpreter)"
              | Term.jump l => runBlock fuel f l (some lbl) e' m'
              | Term.br c t fl =>
                  runBlock fuel f (if evOperand e' c == 0 then fl else t)
                    (some lbl) e' m' := rfl

/-- Exact (non-wrapping) value of a word: if `0 ≤ z < 2^32`, `w32` is the identity. -/
theorem w32_eq (z : Int) (h0 : 0 ≤ z) (h1 : z < (4294967296 : Int)) :
    w32 z = Int.toNat z := by
  unfold w32
  have hz : z % (MOD : Int) = z := Int.emod_eq_of_lt h0 h1
  rw [hz]

/-- `w32` of a natural value that cannot overflow. -/
theorem w32_small (x : Nat) (hx : x < 4294967296) : w32 x = x := by
  rw [w32_eq (z := (x : Int)) (by omega) (by omega)]
  omega

theorem w32_add (a b : Nat) (h : a + b < 4294967296) : w32 ((a : Int) + b) = a + b := by
  rw [w32_eq ((a : Int) + b) (by omega) (by omega)]
  omega

/-! ────────────────────────────────────────────────────────────
    ## 5. The module machine (calls, recursion, void)

    Small-step abstract machine over whole configurations: `stepOne`
          executes one instruction, `runM` burns fuel, `runModule` starts.
    ──────────────────────────────────────────────────────────── -/

/-
## Function calls, `void`, recursion — a module-level machine

The single-`Func` interpreter above cannot express calls (its `Result`
discards the callee's memory, and mutual recursion defeats naive fuel
recursion). This machine is a **small-step abstract machine**: one
`step` relation over whole configurations, and `runM` that simply
executes `fuel` steps. Every step — instruction, block entry, call,
return — consumes exactly one unit of fuel, so `runM` is structurally
terminating with no mutual recursion at all.

Calls *transfer* memory to the callee and back (that is what makes
`swap` work). The caller's continuation lives in a `Cont` stack.
-/
/-- A module: named functions (first match wins). -/
@[reducible] def Module : Type := List (String × Func)

/-- What to do with the value/memory a call returns to. -/
inductive Cont : Type where
  | top : Cont
  | retTo (fn : String) (lbl : String) (prev : Option String)
      (rest : List Instr) (tm : Term) (e : Env) (d : String) (cont : Cont) : Cont

/-- Machine configuration: current function/block, remaining
    instructions, terminator, env, memory, return continuation. -/
structure Config where
  fn   : String
  lbl  : String
  prev : Option String
  rest : List Instr
  tm   : Term
  e    : Env
  m    : Mem
  cont : Cont

/-- Observable outcome of a module run: value **and final memory**
    (calls mutate memory; discarding it would make `swap` meaningless). -/
inductive Res : Type where
  | val   (n : Nat) (m : Mem)
  | err   (msg : String)
  | stuck
  deriving DecidableEq, Repr

/-- The returned value, if the run returned. -/
def Res.val? : Res → Option Nat
  | Res.val v _ => some v
  | _ => none

/-- One machine step: `some cfg` continue, `none cfg` normal return
    (value + memory in the config), `err` malformed program. -/
inductive StepR : Type where
  | cont (c : Config)
  | fin (v : Nat) (m : Mem)
  | err  (msg : String)

/-- Look up the entry block (first label + its instructions/terminator). -/
def Module.entry? (mod : Module) (fn : String) :
    Option (String × List Instr × Term) :=
  match mod.lookup fn with
  | some g => match g.blocks with
    | (l, (is, t)) :: _ => some (l, is, t)
    | [] => none
  | none => none

/-- Execute one instruction or terminator. -/
def stepOne (mod : Module) (c : Config) : StepR :=
  match c.rest with
  | i :: r =>
      match i with
      | Instr.bin op d a b =>
          StepR.cont { c with rest := r, e := Env.set c.e d (evBin op (evOperand c.e a) (evOperand c.e b)) }
      | Instr.icmp rl d a b =>
          StepR.cont { c with rest := r, e := Env.set c.e d (evRel rl (evOperand c.e a) (evOperand c.e b)) }
      | Instr.select d cc a b =>
          StepR.cont { c with rest := r, e := Env.set c.e d (if evOperand c.e cc == 0 then evOperand c.e b else evOperand c.e a) }
      | Instr.phi d cs =>
          match evPhi c.prev c.e cs with
          | some v => StepR.cont { c with rest := r, e := Env.set c.e d v }
          | none => StepR.err "phi with unknown predecessor"
      | Instr.alloca d nbytes =>
          StepR.cont { c with rest := r, e := Env.set c.e d c.m.next, m := { c.m with next := c.m.next + roundup4 nbytes } }
      | Instr.load d p =>
          StepR.cont { c with rest := r, e := Env.set c.e d (Mem.get c.m (evOperand c.e p)) }
      | Instr.store v p =>
          StepR.cont { c with rest := r, m := Mem.set c.m (evOperand c.e p) (evOperand c.e v) }
      | Instr.gep d b idx =>
          StepR.cont { c with rest := r, e := Env.set c.e d (w32 (4 * evOperand c.e idx + evOperand c.e b)) }
      | Instr.call d fn args =>
          match mod.lookup fn with
          | some g =>
              match g.blocks with
              | (l0, (is0, t0)) :: _ =>
                  StepR.cont { fn := fn, lbl := l0, prev := none, rest := is0, tm := t0, e := g.params.zip (args.map (evOperand c.e)), m := c.m, cont := Cont.retTo c.fn c.lbl c.prev r c.tm c.e d c.cont }
              | [] => StepR.err ("function " ++ fn ++ " has no blocks")
          | none => StepR.err ("unknown function " ++ fn)
      | Instr.callv fn args =>
          match mod.lookup fn with
          | some g =>
              match g.blocks with
              | (l0, (is0, t0)) :: _ =>
                  StepR.cont { fn := fn, lbl := l0, prev := none, rest := is0, tm := t0, e := g.params.zip (args.map (evOperand c.e)), m := c.m, cont := Cont.retTo c.fn c.lbl c.prev r c.tm c.e "void" c.cont }
              | [] => StepR.err ("function " ++ fn ++ " has no blocks")
          | none => StepR.err ("unknown function " ++ fn)
  | [] =>
      match c.tm with
      | Term.ret o =>
          let v := evOperand c.e o
          match c.cont with
          | Cont.top => StepR.fin v c.m
          | Cont.retTo fn lbl prev rest tm e d cont =>
              StepR.cont { fn := fn, lbl := lbl, prev := prev, rest := rest, tm := tm, e := Env.set e d v, m := c.m, cont := cont }
      | Term.retv =>
          match c.cont with
          | Cont.top => StepR.fin 0 c.m
          | Cont.retTo fn lbl prev rest tm e _ cont =>
              StepR.cont { fn := fn, lbl := lbl, prev := prev, rest := rest, tm := tm, e := e, m := c.m, cont := cont }
      | Term.jump l =>
          match (mod.lookup c.fn).bind (fun g => g.blocks.lookup l) with
          | some (is, t) => StepR.cont { c with lbl := l, prev := some c.lbl, rest := is, tm := t }
          | none => StepR.err "missing block"
      | Term.br cc t fl =>
          let l := if evOperand c.e cc == 0 then fl else t
          match (mod.lookup c.fn).bind (fun g => g.blocks.lookup l) with
          | some (is, t) => StepR.cont { c with lbl := l, prev := some c.lbl, rest := is, tm := t }
          | none => StepR.err "missing block"

/-- Run at most `fuel` steps. -/
def runM : Nat → Module → Config → Res
  | 0, _, _ => Res.stuck
  | fuel + 1, mod, c =>
      match stepOne mod c with
      | StepR.fin v m => Res.val v m
      | StepR.err msg => Res.err msg
      | StepR.cont c' => runM fuel mod c'

/-- Enter a module function with arguments, fuel and initial memory. -/
def runModule (mod : Module) (fn : String) (args : List Nat)
    (fuel : Nat) (m : Mem) : Res :=
  match mod.lookup fn with
  | none => Res.err ("unknown function " ++ fn)
  | some g =>
      match g.blocks with
      | [] => Res.err "function has no blocks"
      | (l0, (is0, t0)) :: _ =>
          runM fuel mod { fn := fn, lbl := l0, prev := none, rest := is0, tm := t0, e := g.params.zip args, m := m, cont := Cont.top }

end Ll

namespace Ll

/-! ────────────────────────────────────────────────────────────
    ## 6. Module-machine API lemmas

    Facts true of *every* program: fuel monotonicity (`runM_mono_val`),
          step unfolding (`runM_succ`), exact-subtraction (`evBin_sub`).
          Program-specific theorems live in LlLog2/LlMem/LlCall/LlSort.
    ──────────────────────────────────────────────────────────── -/

/-- One-step unfolding at successor fuel, in `rfl` form. -/
theorem runM_succ (mod : Module) (c : Config) (fuel : Nat) :
    runM (fuel + 1) mod c =
      match stepOne mod c with
      | StepR.fin v m => Res.val v m
      | StepR.err msg => Res.err msg
      | StepR.cont c' => runM fuel mod c' := rfl

/-- Generic monotonicity: if `runM fuel` returns `v, m`, so does
    `runM (fuel + k)`. -/
theorem runM_mono_val (mod : Module) (fuel v : Nat) (m : Mem) :
    ∀ (c : Config), runM fuel mod c = Res.val v m →
      ∀ k : Nat, runM (fuel + k) mod c = Res.val v m := by
  induction fuel with
  | zero => intro c h k; cases h
  | succ f ih =>
      intro c h k
      cases hstep : stepOne mod c with
      | cont c' =>
          rw [runM_succ] at h
          rw [hstep] at h
          simp at h
          have key : runM (f + 1 + k) mod c = runM (f + k) mod c' := by
            rw [show (f + 1 + k : Nat) = (f + k) + 1 by omega, runM_succ, hstep]
            <;> simp
          rw [key]
          exact ih c' h k
      | fin v' m' =>
          have h1 : runM (f + 1) mod c = Res.val v' m' := by
            rw [runM_succ, hstep]
          rw [show (f + 1 + k : Nat) = (f + k) + 1 by omega, runM_succ, hstep]
          exact h1.symm.trans h
      | err msg =>
          have h1 : runM (f + 1) mod c = Res.err msg := by
            rw [runM_succ, hstep]
          cases h1.symm.trans h

/-- Subtraction that does not wrap: exact when the result is nonnegative. -/
theorem evBin_sub (a b : Nat) (h : b ≤ a) (ha : a < 4294967296) :
    evBin BinOp.sub a b = a - b := by
  show w32 ((a : Int) - (b : Int)) = a - b
  have hz : w32 ((a : Int) - (b : Int)) = Int.toNat ((a : Int) - (b : Int)) :=
    w32_eq _ (by omega) (by omega)
  rw [hz]
  omega

end Ll
