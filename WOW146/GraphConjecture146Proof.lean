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
import WOW146.ExceptionalTheorem

/-!
# Written on the Wall II — Conjecture 146

This module proves a theorem with the exact hypotheses and conclusion of the
current Formal Conjectures declaration.  The proof combines the general
arithmetic reduction with the kernel-checked exceptional induced-tree theorem.
-/

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture146

namespace WOW146

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Written on the Wall II, Conjecture 146, with the exact upstream signature. -/
theorem conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G := by
  exact conjecture146_of_exceptional_case G h hrad (exceptional_case G h)

#check WrittenOnTheWallII.GraphConjecture146.conjecture146
#check WOW146.conjecture146
#print axioms WOW146.conjecture146

end WOW146
