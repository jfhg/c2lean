import C2Lean.Programs
/-!
# Dijkstra correctness — vocabulary + (retired) naive statement

`V` is a runtime parameter of the compiled code.  Layout (caller region,
all `< 1024`, so `V <= 15`):

  * graph: `V*V` words at address 0, row-major, `0` = no edge
  * `dist` output: `V` words at address `4*V*V`
  * `sptSet`: `V` words at address `4*V*V + 4*V`
  * source vertex: `0`

The machine call is
`runModule projectM "dijkstra" [0, 4*V*V, 4*V*V + 4*V, 0, V]`.

`GraphAt V m₀` states what the C code silently assumes:
  * weights ≤ 1000 (so `dist[u] + w` cannot overflow `INT_MAX` — C would
    have UB there; the model must state it);
  * no edges touching vertices `>= V` (cells outside the graph region are
    arbitrary memory; forbidding phantom edges keeps the walk semantics
    confined to the `V`-vertex graph);
  * every vertex reachable from the source (so no `INT_MAX` sentinel
    bookkeeping in the postcondition).

The postcondition says: the final `dist` cells are exactly the
shortest-path distances — characterized by walks, independent of the
algorithm.
-/

namespace Dijkstra
open C2Lean Ll

/-- Edge weight matrix: `W u v = 0` means no edge `u → v`. -/
abbrev W := Nat → Nat → Nat

/-- `Walk W src vs` — `vs` is a walk from `src`, stored in reverse:
    `vs = [v, ..., src]`, consecutive `u :: vs` carrying edge `u → v`. -/
inductive Walk : W → Nat → List Nat → Prop where
  | single (W : W) (s : Nat) : Walk W s [s]
  | extend {W : W} {s u v : Nat} {vs : List Nat}
      (h : Walk W s (u :: vs)) (huv : W u v > 0) : Walk W s (v :: u :: vs)

/-- Total weight of a reversed walk. -/
def walkWeight (W : W) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => W b a + walkWeight W (b :: t)

/-- `d` is the shortest-path distance from `src` to `v`: attained by some
    walk and a lower bound for all walks. -/
def IsDist (W : W) (src v d : Nat) : Prop :=
  (∃ vs : List Nat, Walk W src vs ∧ vs.head? = some v ∧ walkWeight W vs = d) ∧
  (∀ vs : List Nat, Walk W src vs → vs.head? = some v → d ≤ walkWeight W vs)

/-- The graph encoded in memory, as a matrix. -/
def Wm (m₀ : Mem) (V : Nat) : W := fun u v => m₀.get (4 * (V * u + v))

/-- Admissible inputs for `V` vertices. -/
def GraphAt (V : Nat) (m₀ : Mem) : Prop :=
  (∀ u v, u < V → v < V → Wm m₀ V u v ≤ 1000) ∧
  (∀ u v, V ≤ u ∨ V ≤ v → Wm m₀ V u v = 0) ∧
  (∀ v, v < V → ∃ d, IsDist (Wm m₀ V) 0 v d)

-- NOTE (superseded): the statement below was retired once a proof existed.
-- It (a) omitted `1024 ≤ m₀.next` — with a lower `next`, alloca frames
-- clobber the caller arrays, making the claim FALSE (see DijCounter:
-- `¬ dijkstra_correct_type` is PROVED there) — and (b) its
-- phantom-edge clause `V ≤ u ∨ V ≤ v → Wm = 0` also zeroes REAL graph
-- cells (flat index V·0 + a = a ≥ V), degenerating every admissible
-- graph to a star.  See DijFinal.lean: `graphAt_forces_zero` documents
-- the degeneracy; `dijkstra_correct_fixed` (guarded weights `Wv`, plus
-- `1024 ≤ m₀.next`) and `dijkstra_correct_with_next` are the theorems.

def dijkstra_correct_type : Prop :=
  ∀ (V : Nat) (m₀ : Mem), 1 ≤ V → V ≤ 15 → GraphAt V m₀ →
    ∃ (fuel result : Nat) (m : Mem),
      runModule projectM "dijkstra" [0, 4 * V * V, 4 * V * V + 4 * V, 0, V]
        fuel m₀ = Res.val result m ∧
      result = 0 ∧
      (∀ v, v < V → IsDist (Wm m₀ V) 0 v (m.get (4 * V * V + 4 * v)))

end Dijkstra
