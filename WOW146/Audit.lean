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

import WOW146

/-!
# Independent audit surface for WOWII Conjecture 146

This module does not contribute to the proof. It restates the current upstream
signature verbatim and asks the kernel for the axioms of the final theorem and
the exceptional regression witness.
-/

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture146

namespace WOW146.Audit

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

example (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G :=
  WOW146.conjecture146 G h hrad

#check WrittenOnTheWallII.GraphConjecture146.conjecture146
#check WOW146.conjecture146
#print axioms WOW146.conjecture146
#print axioms WOW146.exceptional_case
#print axioms WOW146.Regression.reg_exceptional

end WOW146.Audit
