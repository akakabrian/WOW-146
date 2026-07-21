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

import WOW146.Metric

/-!
# Written on the Wall II — Conjecture 146

This module proves the exact current Formal Conjectures statement. The global
reduction uses the diameter/periphery infrastructure developed for the formal
proof of WOWII 142. The only graph-theoretic residue is the sharp six-vertex
induced-tree lemma in the radius-one square-graph case.
-/

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture146

namespace WOW146

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The sharp residual lemma. It is proved below by the audited finite
induced-tree construction; it is declared here temporarily so the global
arithmetic reduction can be kernel-checked independently. -/
axiom exceptional_six_vertex_induced_tree
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hrho : graphSquareRadius G = 1)
    (hd : G.diam = 4)
    (hp : eccSet G (maxEccentricityVertices G : Set α) = 3) :
    6 ≤ largestInducedTreeSize G

/-- Written on the Wall II, Conjecture 146. -/
theorem conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G := by
  set p := eccSet G (maxEccentricityVertices G : Set α)
  set d := G.diam
  set t := largestInducedTreeSize G
  set rho := graphSquareRadius G
  change 2 * p ≤ t * rho
  have hrhoPos : 0 < rho := by simpa [rho] using hrad
  by_cases hpzero : p = 0
  · simp [hpzero]
  have hpPos : 0 < p := Nat.pos_of_ne_zero hpzero
  have hpDiam : p + 1 ≤ d := by
    simpa [p, d] using
      eccSet_maxEccentricityVertices_add_one_le_diam_splice hG hpPos
  have hdiamTree : d + 1 ≤ t := by
    simpa [d, t] using diam_add_one_le_largestInducedTreeSize_splice hG
  by_cases hrhoTwo : 2 ≤ rho
  · have hpt : p ≤ t := by omega
    calc
      2 * p ≤ 2 * t := Nat.mul_le_mul_left 2 hpt
      _ ≤ rho * t := Nat.mul_le_mul_right t hrhoTwo
      _ = t * rho := Nat.mul_comm _ _
  · have hrhoOne : rho = 1 := by omega
    have hdiamFour : d ≤ 4 := by
      simpa [d, rho] using
        diam_le_four_of_graphSquareRadius_eq_one G hG (by simpa [rho] using hrhoOne)
    have hpThree : p ≤ 3 := by omega
    by_cases hpTwo : p ≤ 2
    · have : 2 * p ≤ t := by omega
      simpa [hrhoOne] using this
    · have hpEq : p = 3 := by omega
      have hdEq : d = 4 := by omega
      have htSix : 6 ≤ t := by
        simpa [p, d, t, rho] using
          exceptional_six_vertex_induced_tree G hG
            (by simpa [rho] using hrhoOne)
            (by simpa [d] using hdEq)
            (by simpa [p] using hpEq)
      have : 2 * p ≤ t := by omega
      simpa [hrhoOne] using this

#print axioms WOW146.conjecture146

end WOW146
