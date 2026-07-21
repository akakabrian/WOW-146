/-
Copyright 2026 The WOW-146 Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.WrittenOnTheWallII.GraphConjecture146
import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture142Proof

/-!
# Written on the Wall II — Conjecture 146

Standalone proof harness for the exact current Formal Conjectures statement.
The declarations below are deliberately restricted to APIs already confirmed
against the pinned dependency. New lemmas should be added in named modules and
kept warning-free.
-/

open Classical
open SimpleGraph

namespace WOW146

#check WrittenOnTheWallII.GraphConjecture146.conjecture146
#check WrittenOnTheWallII.GraphConjecture146.graphSquareRadius

-- Reusable, sorry-free infrastructure from the completed WOWII 142 proof.
#check SimpleGraph.diam_add_one_le_largestInducedTreeSize_splice
#check SimpleGraph.eccSet_maxEccentricityVertices_add_one_le_diam_splice
#check SimpleGraph.maxEccentricityVertices_nonempty_splice
#check SimpleGraph.exists_eccSet_witness_splice
#check SimpleGraph.IsTree.induce_insert_of_unique_adj

-- Metric and walk APIs confirmed at the pinned revision.
#check SimpleGraph.exists_dist_eq_diam
#check SimpleGraph.exists_eccent_eq_radius
#check SimpleGraph.ediam_le_two_mul_radius
#check SimpleGraph.radius_ne_top_iff
#check SimpleGraph.Connected.exists_walk_length_eq_dist
#check SimpleGraph.exists_walk_of_dist_ne_zero
#check SimpleGraph.dist_le
#check SimpleGraph.dist_eq_one_iff_adj
#check SimpleGraph.Walk.IsPath
#check SimpleGraph.Walk.support

end WOW146
