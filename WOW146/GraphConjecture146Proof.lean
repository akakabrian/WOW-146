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
-/

open Classical
open SimpleGraph

namespace WOW146

#check WrittenOnTheWallII.GraphConjecture146.conjecture146
#check WrittenOnTheWallII.GraphConjecture146.graphSquareRadius
#check SimpleGraph.diam_add_one_le_largestInducedTreeSize_splice
#check SimpleGraph.eccSet_maxEccentricityVertices_add_one_le_diam_splice
#check SimpleGraph.maxEccentricityVertices_nonempty_splice
#check SimpleGraph.exists_eccSet_witness_splice
#check SimpleGraph.IsTree.induce_insert_of_unique_adj
#check SimpleGraph.distToSet_le_dist_of_mem_public
#check SimpleGraph.connected_iff_ediam_ne_top
#check SimpleGraph.Connected.mono
#check SimpleGraph.Preconnected.mono
#check SimpleGraph.Connected.pos_dist_of_ne
#check SimpleGraph.Connected.dist_triangle
#check SimpleGraph.Connected.coe_dist_eq_edist
#check SimpleGraph.Preconnected.coe_dist_eq_edist
#check SimpleGraph.edist_le_eccent
#check SimpleGraph.eccent_le_ediam
#check SimpleGraph.radius_le_eccent
#check SimpleGraph.exists_eccent_eq_radius
#check SimpleGraph.radius_ne_top_iff
#check ENat.toNat_le_toNat
#check ENat.coe_toNat
#check ENat.coe_toNat_eq_self
#check ENat.toNat_eq_iff
#check SimpleGraph.dist_eq_one_iff_adj
#check SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable
#check SimpleGraph.Walk.IsPath.induce_isTree
#check SimpleGraph.Walk.IsPath.induce_support_isTree
#check SimpleGraph.Walk.IsPath.induce_support_toFinset_isTree
#check SimpleGraph.finset_card_le_largestInducedTreeSize_splice
#check SimpleGraph.card_le_largestInducedTreeSize_splice
#check Nat.le_csSup
#check Nat.le_sSup

end WOW146
