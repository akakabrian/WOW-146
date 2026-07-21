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

import WOW146.Reduction

/-!
# Written on the Wall II — Conjecture 146

Standalone proof harness for the exact current Formal Conjectures statement.
Issues #2 and #3 supply all metric and global bounds.  The complete arithmetic
integration is now kernel-checked in `conjecture146_of_exceptional_case`; the
only remaining input is the exceptional induced-tree theorem from issue #4.
-/

open Classical
open SimpleGraph

namespace WOW146

#check WrittenOnTheWallII.GraphConjecture146.conjecture146
#check WrittenOnTheWallII.GraphConjecture146.graphSquareRadius
#check SimpleGraph.graphSquare_dist
#check SimpleGraph.graphSquareRadius_eq

-- Global bounds established for Conjecture 146.
#check SimpleGraph.Walk.induce_support_toFinset_isTree_of_length_eq_dist
#check SimpleGraph.finset_card_le_largestInducedTreeSize
#check SimpleGraph.diam_succ_le_largestInducedTreeSize
#check SimpleGraph.eccSet_periphery_add_one_le_diam
#check SimpleGraph.radius_toNat_le_diam
#check SimpleGraph.diam_le_two_mul_radius_toNat

-- Complete integration, parameterized only by the pending issue #4 theorem.
#check WOW146.conjecture146_of_exceptional_case

end WOW146
