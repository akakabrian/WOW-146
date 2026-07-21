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
import WOW146.ExceptionalCase

/-!
# Written on the Wall II — Conjecture 146 (complete)

This module assembles the exact Formal Conjectures statement from two
kernel-checked inputs:

* the metric and arithmetic integration `conjecture146_of_exceptional_case`
  (issues #2, #3 and the reduction of issue #5), and
* the sharp radius-two exceptional induced-tree bound
  `SimpleGraph.exceptional_case` (issue #4).

The resulting theorem has the exact signature of
`WrittenOnTheWallII.GraphConjecture146.conjecture146` and is `sorry`-free.
-/

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture146

namespace WOW146

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- **Written on the Wall II, Conjecture 146.**  For a finite, nontrivial,
connected simple graph `G`,
`2 · ecc(periphery) ≤ tree(G) · rad(G²)`.

This matches the exact upstream Formal Conjectures declaration
`WrittenOnTheWallII.GraphConjecture146.conjecture146` and is proved with no
`sorry`, `admit` or `native_decide`. -/
theorem conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G :=
  conjecture146_of_exceptional_case G h hrad
    (fun hr hd hp => SimpleGraph.exceptional_case h hr hd hp)

#print axioms WOW146.conjecture146

end WOW146
