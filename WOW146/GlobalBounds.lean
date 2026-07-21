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

import WOW146.GraphSquareRadius
import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture142Proof

/-!
# Global bounds for WOWII Conjecture 146

This module packages the induced-geodesic, periphery, and radius/diameter
estimates used in the arithmetic reduction of Conjecture 146.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

/-- A diametral geodesic supplies an induced tree on `diam + 1` vertices. -/
lemma diam_succ_le_largestInducedTreeSize (hG : G.Connected) :
    G.diam + 1 ≤ largestInducedTreeSize G :=
  diam_add_one_le_largestInducedTreeSize_splice hG

/-- The eccentricity of the peripheral set is strictly below the diameter. -/
lemma eccSet_periphery_add_one_le_diam (hG : G.Connected) :
    eccSet G (maxEccentricityVertices G : Set α) + 1 ≤ G.diam := by
  by_cases hp : eccSet G (maxEccentricityVertices G : Set α) = 0
  · have hd : G.diam ≠ 0 := (connected_iff_diam_ne_zero).mp hG
    omega
  · exact eccSet_maxEccentricityVertices_add_one_le_diam_splice hG
      (Nat.pos_of_ne_zero hp)

/-- In a finite connected graph, the natural-valued radius is at most the diameter. -/
lemma radius_toNat_le_diam (hG : G.Connected) :
    G.radius.toNat ≤ G.diam := by
  have hed : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hG
  unfold diam
  exact ENat.toNat_le_toNat radius_le_ediam hed

/-- In a finite connected graph, the diameter is at most twice the natural-valued radius. -/
lemma diam_le_two_mul_radius_toNat (hG : G.Connected) :
    G.diam ≤ 2 * G.radius.toNat := by
  have hr : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hG
  have h := ENat.toNat_le_toNat (ediam_le_two_mul_radius (G := G)) (by simp [hr])
  simpa [diam] using h

#check Walk.chordless_of_length_eq_dist
#check Walk.IsPath.induce_support_isTree
#check Walk.IsPath.induce_support_toFinset_isTree
#check Walk.IsPath.induce_isTree
#check IsTree.card_le_largestInducedTreeSize_splice

#print axioms diam_succ_le_largestInducedTreeSize
#print axioms eccSet_periphery_add_one_le_diam
#print axioms radius_toNat_le_diam
#print axioms diam_le_two_mul_radius_toNat

end SimpleGraph
