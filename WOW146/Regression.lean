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

import WOW146.ExceptionalCase

/-!
# Regression witness for the exceptional radius-2 case

The hypotheses of `SimpleGraph.exceptional_case` (radius `2`, diameter `4`,
periphery eccentricity `3`) are not vacuous.  This file exhibits the smallest
witness: the six-vertex "spider" tree, a path `0-1-2-3-4` with a pendant edge
`2-5`.  Labelling `x = 0`, `u = 1`, `c = 2`, `v = 3`, `y = 4`, `z = 5`, this is
exactly the `dist c z = 1` configuration of the audited proof.

We verify computationally (no `native_decide`) that this graph is connected with
radius `2`, diameter `4`, periphery `{0, 4}` and periphery eccentricity `3`, then
feed those facts to `exceptional_case` to conclude `6 ≤ t`.
-/

open SimpleGraph

/-- Edge relation of the witness graph: path `0-1-2-3-4` plus pendant `2-5`. -/
def regRel : Fin 6 → Fin 6 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 4) ∨ (a = 2 ∧ b = 5)

instance : DecidableRel regRel := fun a b => by unfold regRel; infer_instance

/-- The witness graph on `Fin 6`. -/
def regGraph : SimpleGraph (Fin 6) := SimpleGraph.fromRel regRel

instance : DecidableRel regGraph.Adj :=
  fun a b => decidable_of_iff _ (SimpleGraph.fromRel_adj regRel a b).symm

theorem reg_connected : regGraph.Connected := by decide

set_option maxRecDepth 4000 in
theorem reg_radius : regGraph.radius.toNat = 2 := by
  rw [radius_eq_computable regGraph reg_connected, ENat.toNat_coe]; decide

set_option maxRecDepth 4000 in
theorem reg_diam : regGraph.diam = 4 := by
  show regGraph.ediam.toNat = 4
  rw [ediam_eq_computable regGraph reg_connected, ENat.toNat_coe]; decide

set_option maxRecDepth 8000 in
theorem reg_periphery : regGraph.maxEccentricityVertices = ({0, 4} : Set (Fin 6)) := by
  ext v
  rw [SimpleGraph.maxEccentricityVertices, Set.mem_setOf_eq,
      eccent_eq_computable regGraph reg_connected,
      ediam_eq_computable regGraph reg_connected, Nat.cast_inj]
  fin_cases v <;> decide

set_option maxRecDepth 8000 in
theorem reg_eccSet : regGraph.eccSet (regGraph.maxEccentricityVertices) = 3 := by
  rw [reg_periphery]
  simp only [SimpleGraph.eccSet, SimpleGraph.distToSet, dist_eq_computable,
    Set.toFinset_insert, Set.toFinset_singleton]
  decide

/-- The witness graph satisfies every hypothesis of `exceptional_case`, so the
lemma is non-vacuous and yields `6 ≤ t` for this concrete graph. -/
theorem reg_exceptional : 6 ≤ regGraph.largestInducedTreeSize :=
  exceptional_case reg_connected reg_radius reg_diam reg_eccSet
