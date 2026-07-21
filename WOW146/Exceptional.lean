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
# Exceptional radius-one-square case for WOWII Conjecture 146

The global reduction leaves the sharp case in which the square graph has
radius one, the original diameter is four, and the eccentricity of the
periphery is three.  The proof constructs a six-vertex induced tree.
-/

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture146

namespace WOW146

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

/-- A four-edge geodesic together with a vertex having exactly one neighbor on
that geodesic supplies an induced tree on six vertices. -/
lemma Walk.six_le_largestInducedTreeSize_of_geodesic_four_add_unique_leaf
    {a e z c : α} (p : G.Walk a e)
    (hp : p.length = G.dist a e) (hlen : p.length = 4)
    (hc : c ∈ p.support) (hz : z ∉ p.support)
    (hzc : G.Adj z c)
    (huniq : ∀ ⦃q : α⦄, q ∈ p.support → G.Adj z q → q = c) :
    6 ≤ largestInducedTreeSize G := by
  have hpPath : p.IsPath := p.isPath_of_length_eq_dist hp
  have htree : (G.induce (p.support.toFinset : Set α)).IsTree :=
    p.induce_support_isTree_of_length_eq_dist hp
  have htree' :
      (G.induce ((insert z p.support.toFinset : Finset α) : Set α)).IsTree := by
    apply htree.induce_insert_of_unique_adj
    · simpa using hz
    · simpa using hc
    · exact hzc
    · intro q hq hsq
      exact huniq (by simpa using hq) hsq
  have hcardSupport : p.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, p.length_support, hlen]
  have hcard : (insert z p.support.toFinset).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simpa using hz), hcardSupport]
  have hbound := htree'.card_le_largestInducedTreeSize_splice
  omega

/-- Three successive unique leaf attachments to a three-vertex induced tree
produce an induced tree on six vertices. -/
lemma six_le_largestInducedTreeSize_of_three_unique_insertions
    {s : Finset α} (hT : (G.induce (s : Set α)).IsTree) (hcard : s.card = 3)
    {z₁ a₁ z₂ a₂ z₃ a₃ : α}
    (hz₁ : z₁ ∉ s) (ha₁ : a₁ ∈ s) (hza₁ : G.Adj z₁ a₁)
    (hu₁ : ∀ ⦃q : α⦄, q ∈ s → G.Adj z₁ q → q = a₁)
    (hz₂ : z₂ ∉ insert z₁ s) (ha₂ : a₂ ∈ insert z₁ s) (hza₂ : G.Adj z₂ a₂)
    (hu₂ : ∀ ⦃q : α⦄, q ∈ insert z₁ s → G.Adj z₂ q → q = a₂)
    (hz₃ : z₃ ∉ insert z₂ (insert z₁ s))
    (ha₃ : a₃ ∈ insert z₂ (insert z₁ s)) (hza₃ : G.Adj z₃ a₃)
    (hu₃ : ∀ ⦃q : α⦄, q ∈ insert z₂ (insert z₁ s) → G.Adj z₃ q → q = a₃) :
    6 ≤ largestInducedTreeSize G := by
  have hT₁ := hT.induce_insert_of_unique_adj hz₁ ha₁ hza₁ hu₁
  have hT₂ := hT₁.induce_insert_of_unique_adj hz₂ ha₂ hza₂ hu₂
  have hT₃ := hT₂.induce_insert_of_unique_adj hz₃ ha₃ hza₃ hu₃
  have hcard₁ : (insert z₁ s).card = 4 := by
    rw [Finset.card_insert_of_notMem hz₁, hcard]
  have hcard₂ : (insert z₂ (insert z₁ s)).card = 5 := by
    rw [Finset.card_insert_of_notMem hz₂, hcard₁]
  have hcard₃ : (insert z₃ (insert z₂ (insert z₁ s))).card = 6 := by
    rw [Finset.card_insert_of_notMem hz₃, hcard₂]
  have hbound := hT₃.card_le_largestInducedTreeSize_splice
  omega

end WOW146
