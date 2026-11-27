import C2Lean.Programs

/-!
  # Dijkstra shortest paths — end-to-end calibration

  A real algorithm (textbook 9-vertex adjacency-matrix Dijkstra) executed
  by the module machine: `minDistance` + `dijkstra` contain nested loops,
  cross-function calls and pointer-parameter arrays.  The memory layout
  lives in the caller region (`< 1024`):

    graph   81 words at 0     (row-major, `0` = no edge)
    dist     9 words at 324
    sptSet   9 words at 360

  The theorems below are kernel-checked (`native_decide`) facts about the
  embedded semantics: the machine's own output equals the textbook
  shortest-path distances.  The `-O0` slot-machine run takes ~50k steps
  (fuel 4000 is not enough; 100000 is).

  The *general* correctness statement (dist = shortest-path distance for
  every admissible graph, via a walk-minimum characterization) is the
  stretch mountain; a self-contained statement kit lives outside the
  repo for a prover to attack.
-/

set_option maxRecDepth 400000
set_option maxHeartbeats 800000000

namespace C2Lean
open Ll

/-- The GeeksforGeeks example graph, flattened row-major. -/
def dijFlat : List Nat :=
  [0,4,0,0,0,0,0,8,0, 4,0,8,0,0,0,0,11,0, 0,8,0,7,0,4,0,0,2,
   0,0,7,0,9,14,0,0,0, 0,0,0,9,0,10,0,0,0, 0,0,4,14,10,0,2,0,0,
   0,0,0,0,0,2,0,1,6, 8,11,0,0,0,0,1,0,7, 0,0,2,0,0,0,6,7,0]

def dijMem : Mem :=
  { cells := (List.range 81).zip dijFlat |>.map fun (i, w) => (4*i, w)
    next := 1024 }

def dijRun : Res := runModule projectM "dijkstra" [0, 324, 360, 0] 100000 dijMem

theorem dijkstra_runs : dijRun.val? = some 0 := by native_decide

/-- The machine's `dist` output is the textbook distance vector. -/
def dijDistVec : List Nat :=
  match dijRun with
  | Res.val _ m => [m.get 324, m.get 328, m.get 332, m.get 336, m.get 340,
                    m.get 344, m.get 348, m.get 352, m.get 356]
  | _ => []

theorem dist_correct : dijDistVec = [0, 4, 12, 19, 21, 11, 9, 8, 14] := by
  native_decide

/-- The outer loop runs `V-1` rounds, so exactly 8 vertices are finalized. -/
def dijSptCount : Nat :=
  match dijRun with
  | Res.val _ m => ((List.range 9).map (fun i => m.get (360 + 4*i))).count 1
  | _ => 0

theorem spt_correct : dijSptCount = 8 := by native_decide

end C2Lean
