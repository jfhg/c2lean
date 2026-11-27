import C2Lean.Programs

/-!
  # Dijkstra shortest paths — end-to-end calibration

  A real algorithm (textbook adjacency-matrix Dijkstra) executed by the
  module machine: `minDistance` + `dijkstra` contain nested loops whose
  bounds are RUNTIME values (`V` is a parameter), a cross-function call
  and pointer-parameter arrays.

  Memory layout (caller region, all `< 1024`; valid for `V <= 15`):

    graph   4·V² bytes at 0            (`0` = no edge)
    dist     4·V bytes at 4·V²
    sptSet   4·V bytes at 4·V² + 4·V

  The theorems below are kernel-checked (`native_decide`) facts about the
  embedded semantics: the machine's own output equals the textbook
  shortest-path distances — at several vertex counts, with the same
  compiled code.  The `-O0` slot-machine run of the 9-vertex example
  takes ~50k steps (fuel 100000 suffices for every `V <= 15`).

  The *general* correctness theorem (for every `1 <= V <= 15` and every
  admissible graph, via a walk-minimum characterization) is proved in
  `Proofs/Dij*.lean` (statement vocabulary in `DijkstraSpec.lean`);
  `DijkstraSpec.lean` also documents, with a proved counterexample in
  `DijCounter.lean`, why the naive statement is false.
-/

set_option maxRecDepth 400000
set_option maxHeartbeats 800000000

namespace C2Lean
open Ll

/-- `V` vertices, `V*V` edge weights (row-major, `0` = no edge).
    Layout: graph at 0, dist at 4·V², sptSet at 4·V² + 4·V. -/
def dijMem (V : Nat) (flat : List Nat) : Mem :=
  { cells := (List.range (V * V)).zip flat |>.map fun (i, w) => (4 * i, w),
    next := 1024 }

def dijRun (V : Nat) (flat : List Nat) : Res :=
  runModule projectM "dijkstra" [0, 4 * V * V, 4 * V * V + 4 * V, 0, V]
    100000 (dijMem V flat)

/-- The machine's `dist` output, as a list. -/
def dijDist (V : Nat) (flat : List Nat) : List Nat :=
  match dijRun V flat with
  | Res.val _ m => (List.range V).map fun i => m.get (4 * V * V + 4 * i)
  | _ => []

/-- Vertices finalized (`sptSet == 1`) after the run. -/
def dijSptCount (V : Nat) (flat : List Nat) : Nat :=
  match dijRun V flat with
  | Res.val _ m => ((List.range V).map fun i => m.get (4 * V * V + 4 * V + 4 * i)).count 1
  | _ => 0

/-! ### The textbook 9-vertex example -/

def g9 : List Nat :=
  [0,4,0,0,0,0,0,8,0, 4,0,8,0,0,0,0,11,0, 0,8,0,7,0,4,0,0,2,
   0,0,7,0,9,14,0,0,0, 0,0,0,9,0,10,0,0,0, 0,0,4,14,10,0,2,0,0,
   0,0,0,0,0,2,0,1,6, 8,11,0,0,0,0,1,0,7, 0,0,2,0,0,0,6,7,0]

theorem dijkstra_runs_9 : (dijRun 9 g9).val? = some 0 := by
  native_decide

theorem dist_correct_9 : dijDist 9 g9 = [0, 4, 12, 19, 21, 11, 9, 8, 14] := by
  native_decide

/-- The outer loop runs `V-1` rounds: 8 of 9 vertices get finalized. -/
theorem spt_correct_9 : dijSptCount 9 g9 = 8 := by native_decide

/-! ### A 4-vertex example through the SAME compiled code -/

/-- Edges 0-1 (1), 1-2 (2), 2-3 (1), 0-3 (9): the long direct edge loses. -/
def g4 : List Nat := [0,1,0,9, 1,0,2,0, 0,2,0,1, 9,0,1,0]

theorem dist_correct_4 : dijDist 4 g4 = [0, 1, 3, 4] := by native_decide

theorem spt_correct_4 : dijSptCount 4 g4 = 3 := by native_decide

end C2Lean
