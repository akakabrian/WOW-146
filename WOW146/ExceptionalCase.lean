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
# The exceptional radius-2 case of WOWII Conjecture 146

This module formalizes the only non-arithmetic graph-theoretic corner of the
audited proof: a finite connected graph with radius `2`, diameter `4` and
periphery eccentricity `3` has a largest induced tree of order at least `6`.

The development is split into:

* a small reusable API for certifying that an explicit finite vertex set induces
  a tree by attaching leaves one at a time (`IsTree.induce_insert_leaf`), with
  non-adjacency supplied as a distance bound;
* the witness extraction and the distance table of the audited proof; and
* named lemmas for each case and subcase of the construction.

All proofs avoid `native_decide`, `sorry` and `admit`.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

/- ## Distance and eccentricity glue -/

omit [DecidableEq α] in
/-- In a connected finite graph every vertex has finite eccentricity. -/
lemma eccent_ne_top_of_connected (h : G.Connected) (u : α) : G.eccent u ≠ ⊤ := by
  haveI : Nonempty α := h.nonempty
  have hed : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp h
  intro hu
  exact hed (top_unique (hu ▸ eccent_le_ediam))

omit [DecidableEq α] in
/-- Distance to any vertex is bounded by the (natural-valued) eccentricity. -/
lemma dist_le_eccent_toNat (h : G.Connected) (u v : α) :
    G.dist u v ≤ (G.eccent u).toNat := by
  unfold dist
  exact ENat.toNat_le_toNat edist_le_eccent (eccent_ne_top_of_connected h u)

omit [Fintype α] [DecidableEq α] in
/-- Two vertices at positive distance are distinct. -/
lemma ne_of_dist_pos {a b : α} (hab : 0 < G.dist a b) : a ≠ b := by
  rintro rfl
  simp [dist_self] at hab

omit [Fintype α] [DecidableEq α] in
/-- Vertices at distance at least two are non-adjacent. -/
lemma not_adj_of_two_le_dist {a b : α} (hab : 2 ≤ G.dist a b) : ¬ G.Adj a b := by
  intro hadj
  have h1 : G.dist a b = 1 := dist_eq_one_iff_adj.mpr hadj
  omega

omit [Fintype α] [DecidableEq α] in
/-- In a connected graph, distinct non-adjacent vertices are at distance at least two. -/
lemma two_le_dist_of_ne_of_not_adj (h : G.Connected) {a b : α} (hne : a ≠ b)
    (hnadj : ¬ G.Adj a b) : 2 ≤ G.dist a b := by
  have h1 : G.dist a b ≠ 1 := fun he => hnadj (dist_eq_one_iff_adj.mp he)
  have h0 : 0 < G.dist a b := (h.preconnected a b).pos_dist_of_ne hne
  omega

omit [Fintype α] [DecidableEq α] in
/-- If `dist a b = 2` then `a` and `b` have a common neighbour. -/
lemma exists_midpoint (h : G.Connected) {a b : α} (hab : G.dist a b = 2) :
    ∃ m, G.Adj a m ∧ G.Adj m b := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist a b
  rw [hab] at hp
  refine ⟨p.getVert 1, ?_, ?_⟩
  · have hadj := p.adj_getVert_succ (i := 0) (by omega)
    rwa [p.getVert_zero] at hadj
  · have hadj := p.adj_getVert_succ (i := 1) (by omega)
    have h2 : p.getVert 2 = b := by rw [← hp]; exact p.getVert_length
    rwa [show (1 : ℕ) + 1 = 2 from rfl, h2] at hadj

omit [Fintype α] [DecidableEq α] in
/-- Along a geodesic `p`, the prefix and suffix distances are exactly `i` and
`length - i`. -/
lemma dist_getVert_of_geodesic (h : G.Connected) {s t : α} (p : G.Walk s t)
    (hp : p.length = G.dist s t) {i : ℕ} (hi : i ≤ p.length) :
    G.dist s (p.getVert i) = i ∧ G.dist (p.getVert i) t = p.length - i := by
  have h1 : G.dist s (p.getVert i) ≤ i := by
    have hb := G.dist_le (p.take i)
    rw [Walk.take_length, min_eq_left hi] at hb
    exact hb
  have h2 : G.dist (p.getVert i) t ≤ p.length - i := by
    have hb := G.dist_le (p.drop i)
    rw [Walk.drop_length] at hb
    exact hb
  have htri := h.dist_triangle (u := s) (v := p.getVert i) (w := t)
  constructor <;> omega

/- ## Reusable induced-tree witness API

`IsTree.induce_insert_leaf` grows an induced tree by a single leaf: the new
vertex `z` is attached to `a` and is forced to be non-adjacent to every other
current vertex by the distance bound `hfar`.  Chaining it from a singleton
(`IsTree.of_subsingleton`) certifies any explicit induced tree, and
`IsTree.card_le_largestInducedTreeSize_splice` then bounds
`largestInducedTreeSize`. -/

omit [Fintype α] [DecidableEq α] in
/-- A single vertex induces a tree. -/
lemma isTree_induce_singleton (c : α) :
    (G.induce (({c} : Finset α) : Set α)).IsTree := by
  have hset : ((({c} : Finset α) : Set α)) = {c} := by simp
  rw [hset]
  letI : Nonempty ↥({c} : Set α) := ⟨⟨c, by simp⟩⟩
  letI : Subsingleton ↥({c} : Set α) := ⟨fun a b => by
    apply Subtype.ext
    simpa only [Set.mem_singleton_iff] using a.property.trans b.property.symm⟩
  exact IsTree.of_subsingleton

omit [Fintype α] in
/-- Attach a new leaf `z` to an induced tree on `s`: `z` is adjacent to `a ∈ s`
and every other vertex of `s` is at distance at least two from `z`. -/
lemma IsTree.induce_insert_leaf {s : Finset α} {z a : α}
    (hT : (G.induce (s : Set α)).IsTree) (hz : z ∉ s) (ha : a ∈ s)
    (hadj : G.Adj z a) (hfar : ∀ b ∈ s, b ≠ a → 2 ≤ G.dist z b) :
    (G.induce ((insert z s : Finset α) : Set α)).IsTree := by
  refine hT.induce_insert_of_unique_adj hz ha hadj ?_
  intro b hb hzb
  by_contra hne
  exact not_adj_of_two_le_dist (hfar b hb hne) hzb

/-- **Exactly-one chord subcase** (oriented so the `u`–`w` edge is present).
From the geodesic `x-u-w-z` and a `z`–`y` geodesic `z-b-a-y`, every chord
configuration produces an explicit induced tree of order at least `6`. -/
lemma exceptional_exactly_one_aux (h : G.Connected) {x u w z y : α}
    (hAxu : G.Adj x u) (hAuw : G.Adj u w) (hAwz : G.Adj w z)
    (hxy4 : G.dist x y = 4) (hzx : G.dist z x = 3) (hzy : G.dist z y = 3) :
    6 ≤ G.largestInducedTreeSize := by
  classical
  have hxu1 : G.dist x u = 1 := dist_eq_one_iff_adj.mpr hAxu
  have huw1 : G.dist u w = 1 := dist_eq_one_iff_adj.mpr hAuw
  have hwz1 : G.dist w z = 1 := dist_eq_one_iff_adj.mpr hAwz
  have hux1 : G.dist u x = 1 := by rw [dist_comm]; exact hxu1
  have hzw1 : G.dist z w = 1 := by rw [dist_comm]; exact hwz1
  have huy : 3 ≤ G.dist u y := by
    have t := h.dist_triangle (u := x) (v := u) (w := y); omega
  have hwy : 2 ≤ G.dist w y := by
    have t := h.dist_triangle (u := z) (v := w) (w := y); omega
  have hwx : 2 ≤ G.dist w x := by
    have t := h.dist_triangle (u := z) (v := w) (w := x); omega
  have hzu : 2 ≤ G.dist z u := by
    have t := h.dist_triangle (u := z) (v := u) (w := x); omega
  -- a `z`–`y` geodesic `z-b-a-y`.
  obtain ⟨p, hpath, hplen⟩ := h.exists_path_of_dist z y
  have hpl3 : p.length = 3 := by rw [hplen]; exact hzy
  obtain ⟨hzb_eq, hby_eq⟩ := dist_getVert_of_geodesic h p hplen (i := 1) (by omega)
  obtain ⟨hza_eq, hay_eq⟩ := dist_getVert_of_geodesic h p hplen (i := 2) (by omega)
  have hAzb0 : G.Adj z (p.getVert 1) := by
    have hh := p.adj_getVert_succ (i := 0) (by omega); rwa [p.getVert_zero] at hh
  have hAba0 : G.Adj (p.getVert 1) (p.getVert 2) := by
    have hh := p.adj_getVert_succ (i := 1) (by omega); simpa using hh
  have hAay0 : G.Adj (p.getVert 2) y := by
    have h3 : p.getVert (2 + 1) = y := by
      rw [show (2 : ℕ) + 1 = 3 from rfl, ← hpl3]; exact p.getVert_length
    have hh := p.adj_getVert_succ (i := 2) (by omega); rwa [h3] at hh
  rw [hpl3] at hby_eq hay_eq
  set b := p.getVert 1 with hbdef
  set a := p.getVert 2 with hadef
  clear_value b a
  have hAzb : G.Adj z b := hAzb0
  have hAba : G.Adj b a := hAba0
  have hAay : G.Adj a y := hAay0
  have hba1 : G.dist b a = 1 := dist_eq_one_iff_adj.mpr hAba
  -- derived non-adjacency distances.
  have hxb : 2 ≤ G.dist x b := by
    have t := h.dist_triangle (u := x) (v := b) (w := y); omega
  have hxa : 3 ≤ G.dist x a := by
    have t := h.dist_triangle (u := x) (v := a) (w := y); omega
  have hua : 2 ≤ G.dist u a := by
    have t := h.dist_triangle (u := u) (v := a) (w := y); omega
  -- pairwise distinctness.
  have neXU : x ≠ u := ne_of_dist_pos (by omega : 0 < G.dist x u)
  have neUW : u ≠ w := ne_of_dist_pos (by omega : 0 < G.dist u w)
  have neWZ : w ≠ z := ne_of_dist_pos (by omega : 0 < G.dist w z)
  have neWX : w ≠ x := ne_of_dist_pos (by omega : 0 < G.dist w x)
  have neZX : z ≠ x := ne_of_dist_pos (by omega : 0 < G.dist z x)
  have neZU : z ≠ u := ne_of_dist_pos (by omega : 0 < G.dist z u)
  have neZB : z ≠ b := ne_of_dist_pos (by omega : 0 < G.dist z b)
  have neZA : z ≠ a := ne_of_dist_pos (by omega : 0 < G.dist z a)
  have neAY : a ≠ y := ne_of_dist_pos (by omega : 0 < G.dist a y)
  have neBY : b ≠ y := ne_of_dist_pos (by omega : 0 < G.dist b y)
  have neBA : b ≠ a := ne_of_dist_pos (by omega : 0 < G.dist b a)
  have neXB : x ≠ b := ne_of_dist_pos (by omega : 0 < G.dist x b)
  have neXA : x ≠ a := ne_of_dist_pos (by omega : 0 < G.dist x a)
  have neUA : u ≠ a := ne_of_dist_pos (by omega : 0 < G.dist u a)
  have neXY : x ≠ y := ne_of_dist_pos (by omega : 0 < G.dist x y)
  have neZY : z ≠ y := ne_of_dist_pos (by omega : 0 < G.dist z y)
  have neWY : w ≠ y := ne_of_dist_pos (by omega : 0 < G.dist w y)
  have neUY : u ≠ y := ne_of_dist_pos (by omega : 0 < G.dist u y)
  have neUB : u ≠ b := by intro he; rw [← he] at hzb_eq; omega
  have neAW : a ≠ w := by intro he; rw [he] at hza_eq; omega
  by_cases hbw : b = w
  · -- **(A) `b = w`.**  Tree `{x,u,w,z,a,y}`.
    have hAwa : G.Adj w a := hbw ▸ hAba
    have T0 := isTree_induce_singleton (G := G) w
    have T1 := T0.induce_insert_leaf (by simp only [Finset.mem_singleton]; exact neUW)
      (by simp) hAuw (by
        intro d hd hne; rw [Finset.mem_singleton] at hd; exact absurd hd hne)
    have T2 := T1.induce_insert_leaf
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neXU, neWX.symm⟩)
      (by simp) hAxu (by
        intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
    have T3 := T2.induce_insert_leaf
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
          exact ⟨neZX, neZU, neWZ.symm⟩)
      (by simp) hAwz.symm (by
        intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl <;> first | exact absurd rfl hne | omega)
    have T4 := T3.induce_insert_leaf
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
          exact ⟨neZA.symm, neXA.symm, neUA.symm, neAW⟩)
      (by simp) hAwa.symm (by
        intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
    have T5 := T4.induce_insert_leaf
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
          exact ⟨neAY.symm, neZY.symm, neXY.symm, neUY.symm, neWY.symm⟩)
      (by simp) hAay.symm (by
        intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
    have hcard :
        (insert y (insert a (insert z (insert x (insert u ({w} : Finset α))))) ).card = 6 := by
      rw [Finset.card_insert_of_notMem
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neAY.symm, neZY.symm, neXY.symm, neUY.symm, neWY.symm⟩),
          Finset.card_insert_of_notMem
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neZA.symm, neXA.symm, neUA.symm, neAW⟩),
          Finset.card_insert_of_notMem
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neZX, neZU, neWZ.symm⟩),
          Finset.card_insert_of_notMem
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neXU, neWX.symm⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact neUW),
          Finset.card_singleton]
    have hle := T5.card_le_largestInducedTreeSize_splice
    rw [hcard] at hle; omega
  · by_cases hub : G.Adj u b
    · -- **(B1) `u–b` chord.**  Tree `{x,u,b,z,a,y}`.
      have T0 := isTree_induce_singleton (G := G) b
      have T1 := T0.induce_insert_leaf (by simp only [Finset.mem_singleton]; exact neUB)
        (by simp) hub (by
          intro d hd hne; rw [Finset.mem_singleton] at hd; exact absurd hd hne)
      have T2 := T1.induce_insert_leaf
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neXU, neXB⟩)
        (by simp) hAxu (by
          intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl <;> first | exact absurd rfl hne | omega)
      have T3 := T2.induce_insert_leaf
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨neZX, neZU, neZB⟩)
        (by simp) hAzb (by
          intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl <;> first | exact absurd rfl hne | omega)
      have T4 := T3.induce_insert_leaf
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨neZA.symm, neXA.symm, neUA.symm, neBA.symm⟩)
        (by simp) hAba.symm (by
          intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
      have T5 := T4.induce_insert_leaf
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨neAY.symm, neZY.symm, neXY.symm, neUY.symm, neBY.symm⟩)
        (by simp) hAay.symm (by
          intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
      have hcard :
          (insert y (insert a (insert z (insert x (insert u ({b} : Finset α))))) ).card = 6 := by
        rw [Finset.card_insert_of_notMem
              (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                  exact ⟨neAY.symm, neZY.symm, neXY.symm, neUY.symm, neBY.symm⟩),
            Finset.card_insert_of_notMem
              (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                  exact ⟨neZA.symm, neXA.symm, neUA.symm, neBA.symm⟩),
            Finset.card_insert_of_notMem
              (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                  exact ⟨neZX, neZU, neZB⟩),
            Finset.card_insert_of_notMem
              (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neXU, neXB⟩),
            Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact neUB),
            Finset.card_singleton]
      have hle := T5.card_le_largestInducedTreeSize_splice
      rw [hcard] at hle; omega
    · by_cases hwa : G.Adj w a
      · -- **(B2) `w–a` chord.**  Tree `{x,u,w,z,a,y}`.
        have T0 := isTree_induce_singleton (G := G) w
        have T1 := T0.induce_insert_leaf (by simp only [Finset.mem_singleton]; exact neUW)
          (by simp) hAuw (by
            intro d hd hne; rw [Finset.mem_singleton] at hd; exact absurd hd hne)
        have T2 := T1.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neXU, neWX.symm⟩)
          (by simp) hAxu (by
            intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
        have T3 := T2.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨neZX, neZU, neWZ.symm⟩)
          (by simp) hAwz.symm (by
            intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with rfl | rfl | rfl <;> first | exact absurd rfl hne | omega)
        have T4 := T3.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨neZA.symm, neXA.symm, neUA.symm, neAW⟩)
          (by simp) hwa.symm (by
            intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
        have T5 := T4.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨neAY.symm, neZY.symm, neXY.symm, neUY.symm, neWY.symm⟩)
          (by simp) hAay.symm (by
            intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
        have hcard :
            (insert y (insert a (insert z (insert x (insert u ({w} : Finset α))))) ).card = 6 := by
          rw [Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨neAY.symm, neZY.symm, neXY.symm, neUY.symm, neWY.symm⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨neZA.symm, neXA.symm, neUA.symm, neAW⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨neZX, neZU, neWZ.symm⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neXU, neWX.symm⟩),
              Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact neUW),
              Finset.card_singleton]
        have hle := T5.card_le_largestInducedTreeSize_splice
        rw [hcard] at hle; omega
      · by_cases hwb : G.Adj w b
        · -- **(B3) `w–b` chord.**  Induced path `x-u-w-b-a-y`.
          have haw2 : 2 ≤ G.dist a w := two_le_dist_of_ne_of_not_adj h neAW (fun ha => hwa ha.symm)
          have hub2 : 2 ≤ G.dist u b := two_le_dist_of_ne_of_not_adj h neUB hub
          have T0 := isTree_induce_singleton (G := G) x
          have T1 := T0.induce_insert_leaf (by simp only [Finset.mem_singleton]; exact neXU.symm)
            (by simp) hAxu.symm (by
              intro d hd hne; rw [Finset.mem_singleton] at hd; exact absurd hd hne)
          have T2 := T1.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neUW.symm, neWX⟩)
            (by simp) hAuw.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl <;> first | exact absurd rfl hne | omega)
          have T3 := T2.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨hbw, neUB.symm, neXB.symm⟩)
            (by simp) hwb.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
          have T4 := T3.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neBA.symm, neAW, neUA.symm, neXA.symm⟩)
            (by simp) hAba.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
          have T5 := T4.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neAY.symm, neBY.symm, neWY.symm, neUY.symm, neXY.symm⟩)
            (by simp) hAay.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
          have hcard :
              (insert y (insert a (insert b (insert w (insert u ({x} : Finset α))))) ).card = 6 := by
            rw [Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                      exact ⟨neAY.symm, neBY.symm, neWY.symm, neUY.symm, neXY.symm⟩),
                Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                      exact ⟨neBA.symm, neAW, neUA.symm, neXA.symm⟩),
                Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                      exact ⟨hbw, neUB.symm, neXB.symm⟩),
                Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neUW.symm, neWX⟩),
                Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact neXU.symm),
                Finset.card_singleton]
          have hle := T5.card_le_largestInducedTreeSize_splice
          rw [hcard] at hle; omega
        · -- **(B4) no chord.**  Induced 7-path `x-u-w-z-b-a-y`.
          have haw2 : 2 ≤ G.dist a w := two_le_dist_of_ne_of_not_adj h neAW (fun ha => hwa ha.symm)
          have hub2 : 2 ≤ G.dist u b := two_le_dist_of_ne_of_not_adj h neUB hub
          have hwb2 : 2 ≤ G.dist w b := two_le_dist_of_ne_of_not_adj h (Ne.symm hbw) hwb
          have T0 := isTree_induce_singleton (G := G) x
          have T1 := T0.induce_insert_leaf (by simp only [Finset.mem_singleton]; exact neXU.symm)
            (by simp) hAxu.symm (by
              intro d hd hne; rw [Finset.mem_singleton] at hd; exact absurd hd hne)
          have T2 := T1.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neUW.symm, neWX⟩)
            (by simp) hAuw.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl <;> first | exact absurd rfl hne | omega)
          have T3 := T2.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neWZ.symm, neZU, neZX⟩)
            (by simp) hAwz.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl | rfl <;> first | exact absurd rfl hne | omega)
          have T4 := T3.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neZB.symm, hbw, neUB.symm, neXB.symm⟩)
            (by simp) hAzb.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
          have T5 := T4.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neBA.symm, neZA.symm, neAW, neUA.symm, neXA.symm⟩)
            (by simp) hAba.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
          have T6 := T5.induce_insert_leaf
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨neAY.symm, neBY.symm, neZY.symm, neWY.symm, neUY.symm, neXY.symm⟩)
            (by simp) hAay.symm (by
              intro d hd hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
              rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
          have hcard :
              (insert y (insert a (insert b (insert z (insert w (insert u ({x} : Finset α)))))) ).card
                = 7 := by
            rw [Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                      exact ⟨neAY.symm, neBY.symm, neZY.symm, neWY.symm, neUY.symm, neXY.symm⟩),
                Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                      exact ⟨neBA.symm, neZA.symm, neAW, neUA.symm, neXA.symm⟩),
                Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                      exact ⟨neZB.symm, hbw, neUB.symm, neXB.symm⟩),
                Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                      exact ⟨neWZ.symm, neZU, neZX⟩),
                Finset.card_insert_of_notMem
                  (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨neUW.symm, neWX⟩),
                Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact neXU.symm),
                Finset.card_singleton]
          have hle := T6.card_le_largestInducedTreeSize_splice
          rw [hcard] at hle; omega

/- ## The exceptional case -/

/-- **Exceptional radius-2 case.**  A finite connected graph with radius `2`,
diameter `4` and periphery eccentricity `3` has a largest induced tree of order
at least `6`. -/
theorem exceptional_case
    (h : G.Connected)
    (hr : G.radius.toNat = 2)
    (hd : G.diam = 4)
    (hp : G.eccSet (G.maxEccentricityVertices) = 3) :
    6 ≤ G.largestInducedTreeSize := by
  classical
  haveI : Nonempty α := h.nonempty
  set B : Set α := G.maxEccentricityVertices with hB
  -- `z`: a vertex realizing `eccSet B = 3`.
  obtain ⟨z, hzeq⟩ := exists_eccSet_witness_splice (G := G) B
  rw [hp] at hzeq
  have hzfar : ∀ q ∈ B, 3 ≤ G.dist z q := by
    intro q hq
    have hle := distToSet_le_dist_of_mem_public (G := G) z hq
    omega
  have hzNotB : z ∉ B := by
    intro hzB
    have hle := distToSet_le_dist_of_mem_public (G := G) z hzB
    rw [dist_self] at hle
    omega
  -- diametral pair `x, y`, both peripheral.
  obtain ⟨x, y, hxy⟩ := exists_dist_eq_diam (G := G)
  have hxy4 : G.dist x y = 4 := by rw [hxy]; exact hd
  obtain ⟨hxB, hyB⟩ := diametral_endpoints_mem_maxEccentricityVertices_splice h hxy
  have hzx3 : 3 ≤ G.dist z x := hzfar x hxB
  have hzy3 : 3 ≤ G.dist z y := hzfar y hyB
  -- centre `c`: every distance from `c` is at most `2`.
  obtain ⟨c, hc⟩ := exists_eccent_eq_radius (G := G)
  have hcecc2 : (G.eccent c).toNat = 2 := by rw [hc]; exact hr
  have hcle : ∀ v, G.dist c v ≤ 2 := by
    intro v
    have hb := dist_le_eccent_toNat h c v
    rw [hcecc2] at hb
    exact hb
  -- `ediam = 4` and `eccent z = 3`, forcing `dist z x = dist z y = 3`.
  have hediam_ne_top : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp h
  have hediam_toNat : G.ediam.toNat = 4 := hd
  have hediam4 : G.ediam = 4 := by
    rw [← ENat.coe_toNat hediam_ne_top, hediam_toNat]; rfl
  have hez_ne_top : G.eccent z ≠ ⊤ := eccent_ne_top_of_connected h z
  have hz_ne : G.eccent z ≠ G.ediam := hzNotB
  have hlt : G.eccent z < G.ediam := lt_of_le_of_ne eccent_le_ediam hz_ne
  rw [hediam4, ← ENat.coe_toNat hez_ne_top] at hlt
  have hez4 : (G.eccent z).toNat < 4 := by exact_mod_cast hlt
  have hzx_le : G.dist z x ≤ (G.eccent z).toNat := dist_le_eccent_toNat h z x
  have hzy_le : G.dist z y ≤ (G.eccent z).toNat := dist_le_eccent_toNat h z y
  have hzx : G.dist z x = 3 := by omega
  have hzy : G.dist z y = 3 := by omega
  -- distances from the centre to `x`, `y`, `z`.
  have hxc2 : G.dist x c = 2 := by
    have htri := h.dist_triangle (u := x) (v := c) (w := y)
    have h1 := hcle x
    have h2 := hcle y
    have hcx := dist_comm (G := G) (u := c) (v := x)
    omega
  have hyc2 : G.dist y c = 2 := by
    have htri := h.dist_triangle (u := y) (v := c) (w := x)
    have h1 := hcle x
    have h2 := hcle y
    have hcy := dist_comm (G := G) (u := c) (v := y)
    have hyx := dist_comm (G := G) (u := y) (v := x)
    omega
  have hcz_ne : c ≠ z := by
    intro heq
    rw [heq, dist_comm (G := G) (u := x) (v := z)] at hxc2
    omega
  have hcz_pos : 0 < G.dist c z := (h.preconnected c z).pos_dist_of_ne hcz_ne
  have hcz_le : G.dist c z ≤ 2 := hcle z
  -- midpoints of the two diametral half-geodesics.
  obtain ⟨u, hAxu, hAuc⟩ := exists_midpoint h hxc2
  obtain ⟨v, hAyv, hAvc⟩ := exists_midpoint h hyc2
  have hxu1 : G.dist x u = 1 := dist_eq_one_iff_adj.mpr hAxu
  have huc1 : G.dist u c = 1 := dist_eq_one_iff_adj.mpr hAuc
  have hyv1 : G.dist y v = 1 := dist_eq_one_iff_adj.mpr hAyv
  have hvc1 : G.dist v c = 1 := dist_eq_one_iff_adj.mpr hAvc
  have hux1 : G.dist u x = 1 := by rw [dist_comm]; exact hxu1
  have hvy1 : G.dist v y = 1 := by rw [dist_comm]; exact hyv1
  -- distance-table lower bounds obtained from the triangle inequality.
  have huy : 3 ≤ G.dist u y := by
    have t := h.dist_triangle (u := x) (v := u) (w := y); omega
  have hzu : 2 ≤ G.dist z u := by
    have t := h.dist_triangle (u := z) (v := u) (w := x); omega
  have huv : 2 ≤ G.dist u v := by
    have t1 := h.dist_triangle (u := x) (v := u) (w := y)
    have t2 := h.dist_triangle (u := u) (v := v) (w := y); omega
  have hxv : 3 ≤ G.dist x v := by
    have t := h.dist_triangle (u := x) (v := v) (w := y); omega
  have hzv : 2 ≤ G.dist z v := by
    have t := h.dist_triangle (u := z) (v := v) (w := y); omega
  -- pairwise distinctness of the seven named vertices.
  have hvne_c : v ≠ c := ne_of_dist_pos (by omega : 0 < G.dist v c)
  have hyne_c : y ≠ c := ne_of_dist_pos (by omega : 0 < G.dist y c)
  have hyne_v : y ≠ v := ne_of_dist_pos (by omega : 0 < G.dist y v)
  have hune_c : u ≠ c := ne_of_dist_pos (by omega : 0 < G.dist u c)
  have hune_v : u ≠ v := ne_of_dist_pos (by omega : 0 < G.dist u v)
  have hune_y : u ≠ y := ne_of_dist_pos (by omega : 0 < G.dist u y)
  have hxne_c : x ≠ c := ne_of_dist_pos (by omega : 0 < G.dist x c)
  have hxne_v : x ≠ v := ne_of_dist_pos (by omega : 0 < G.dist x v)
  have hxne_y : x ≠ y := ne_of_dist_pos (by omega : 0 < G.dist x y)
  have hxne_u : x ≠ u := ne_of_dist_pos (by omega : 0 < G.dist x u)
  have hzne_c : z ≠ c := ne_of_dist_pos (by rw [dist_comm]; omega : 0 < G.dist z c)
  have hzne_v : z ≠ v := ne_of_dist_pos (by omega : 0 < G.dist z v)
  have hzne_y : z ≠ y := ne_of_dist_pos (by omega : 0 < G.dist z y)
  have hzne_u : z ≠ u := ne_of_dist_pos (by omega : 0 < G.dist z u)
  have hzne_x : z ≠ x := ne_of_dist_pos (by omega : 0 < G.dist z x)
  -- membership facts for the leaf insertions.
  have hv_notin : v ∉ ({c} : Finset α) := by
    simp only [Finset.mem_singleton]; exact hvne_c
  have hy_notin : y ∉ (insert v {c} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hyne_v, hyne_c⟩
  have hu_notin : u ∉ (insert y (insert v {c}) : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
    exact ⟨hune_y, hune_v, hune_c⟩
  have hx_notin : x ∉ (insert u (insert y (insert v {c})) : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
    exact ⟨hxne_u, hxne_y, hxne_v, hxne_c⟩
  have hz_notin : z ∉ (insert x (insert u (insert y (insert v {c}))) : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
    exact ⟨hzne_x, hzne_u, hzne_y, hzne_v, hzne_c⟩
  rcases (show G.dist c z = 1 ∨ G.dist c z = 2 by omega) with hcz1 | hcz2
  · -- **Case `dist c z = 1`.**  `z` attaches to the centre `c`.
    have hAzc : G.Adj z c := (dist_eq_one_iff_adj.mp hcz1).symm
    have T0 := isTree_induce_singleton (G := G) c
    have T1 := T0.induce_insert_leaf hv_notin (by simp) hAvc (by
      intro b hb hne; rw [Finset.mem_singleton] at hb; exact absurd hb hne)
    have T2 := T1.induce_insert_leaf hy_notin (by simp) hAyv (by
      intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl <;> first | exact absurd rfl hne | omega)
    have T3 := T2.induce_insert_leaf hu_notin (by simp) hAuc (by
      intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl <;> first | exact absurd rfl hne | omega)
    have T4 := T3.induce_insert_leaf hx_notin (by simp) hAxu (by
      intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega)
    have T5 := T4.induce_insert_leaf hz_notin (by simp) hAzc (by
      intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega)
    have hcard :
        (insert z (insert x (insert u (insert y (insert v ({c} : Finset α))))) ).card = 6 := by
      rw [Finset.card_insert_of_notMem hz_notin,
          Finset.card_insert_of_notMem hx_notin,
          Finset.card_insert_of_notMem hu_notin,
          Finset.card_insert_of_notMem hy_notin,
          Finset.card_insert_of_notMem hv_notin,
          Finset.card_singleton]
    calc 6 = _ := hcard.symm
      _ ≤ G.largestInducedTreeSize := T5.card_le_largestInducedTreeSize_splice
  · -- **Case `dist c z = 2`.**  Introduce the midpoint `w` of a `z`–`c` geodesic.
    have hzc2 : G.dist z c = 2 := by rw [dist_comm]; exact hcz2
    obtain ⟨w, hAzw, hAwc⟩ := exists_midpoint h hzc2
    have hzw1 : G.dist z w = 1 := dist_eq_one_iff_adj.mpr hAzw
    have hwc1 : G.dist w c = 1 := dist_eq_one_iff_adj.mpr hAwc
    have hwz1 : G.dist w z = 1 := by rw [dist_comm]; exact hzw1
    have hwx : 2 ≤ G.dist w x := by
      have t := h.dist_triangle (u := z) (v := w) (w := x); omega
    have hwy : 2 ≤ G.dist w y := by
      have t := h.dist_triangle (u := z) (v := w) (w := y); omega
    have hwne_c : w ≠ c := ne_of_dist_pos (by omega : 0 < G.dist w c)
    have hwne_x : w ≠ x := ne_of_dist_pos (by omega : 0 < G.dist w x)
    have hwne_y : w ≠ y := ne_of_dist_pos (by omega : 0 < G.dist w y)
    have hwne_z : w ≠ z := ne_of_dist_pos (by omega : 0 < G.dist w z)
    have hwne_u : w ≠ u := by intro he; rw [he] at hzw1; omega
    have hwne_v : w ≠ v := by intro he; rw [he] at hzw1; omega
    by_cases huw : G.Adj u w
    · by_cases hvw : G.Adj v w
      · -- **Subcase both `uw` and `vw`.**  Delete `c`; hub `w`.
        have T0 := isTree_induce_singleton (G := G) w
        have T1 := T0.induce_insert_leaf (by simp only [Finset.mem_singleton]; exact hwne_u.symm)
          (by simp) huw (by
            intro b hb hne; rw [Finset.mem_singleton] at hb; exact absurd hb hne)
        have T2 := T1.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hxne_u, hwne_x.symm⟩)
          (by simp) hAxu (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl <;>
              first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
        have T3 := T2.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hzne_x, hzne_u, hwne_z.symm⟩)
          (by simp) hAzw (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl <;>
              first | exact absurd rfl hne | omega)
        have T4 := T3.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hzne_v.symm, hxne_v.symm, hune_v.symm, hwne_v.symm⟩)
          (by simp) hvw (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
        have T5 := T4.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hyne_v, hzne_y.symm, hxne_y.symm, hune_y.symm, hwne_y.symm⟩)
          (by simp) hAyv (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
        have hcard :
            (insert y (insert v (insert z (insert x (insert u ({w} : Finset α))))) ).card = 6 := by
          rw [Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hyne_v, hzne_y.symm, hxne_y.symm, hune_y.symm, hwne_y.symm⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hzne_v.symm, hxne_v.symm, hune_v.symm, hwne_v.symm⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hzne_x, hzne_u, hwne_z.symm⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hxne_u, hwne_x.symm⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_singleton]; exact hwne_u.symm),
              Finset.card_singleton]
        have hle := T5.card_le_largestInducedTreeSize_splice
        rw [hcard] at hle; omega
      · -- **Subcase exactly `uw` (not `vw`).**  Use the geodesic `x-u-w-z`.
        exact exceptional_exactly_one_aux h hAxu huw hAzw.symm hxy4 hzx hzy
    · by_cases hvw : G.Adj v w
      · -- **Subcase exactly `vw` (not `uw`).**  Symmetric: geodesic `y-v-w-z`.
        exact exceptional_exactly_one_aux h hAyv hvw hAzw.symm
          (by rw [dist_comm]; exact hxy4) hzy hzx
      · -- **Subcase neither `uw` nor `vw`.**  Seven-vertex star-of-paths, hub `c`.
        have hwu2 : 2 ≤ G.dist w u := two_le_dist_of_ne_of_not_adj h hwne_u (fun ha => huw ha.symm)
        have hwv2 : 2 ≤ G.dist w v := two_le_dist_of_ne_of_not_adj h hwne_v (fun ha => hvw ha.symm)
        have T0 := isTree_induce_singleton (G := G) c
        have T1 := T0.induce_insert_leaf (by simp only [Finset.mem_singleton]; exact hune_c)
          (by simp) hAuc (by
            intro b hb hne; rw [Finset.mem_singleton] at hb; exact absurd hb hne)
        have T2 := T1.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hxne_u, hxne_c⟩)
          (by simp) hAxu (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl <;>
              first | exact absurd rfl hne | omega)
        have T3 := T2.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hxne_v.symm, hune_v.symm, hvne_c⟩)
          (by simp) hAvc (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl <;>
              first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
        have T4 := T3.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hyne_v, hxne_y.symm, hune_y.symm, hyne_c⟩)
          (by simp) hAyv (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hne | omega | (rw [dist_comm]; omega))
        have T5 := T4.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hwne_y, hwne_v, hwne_x, hwne_u, hwne_c⟩)
          (by simp) hAwc (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hne | omega)
        have T6 := T5.induce_insert_leaf
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hwne_z.symm, hzne_y, hzne_v, hzne_x, hzne_u, hzne_c⟩)
          (by simp) hAzw (by
            intro b hb hne; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hne | omega)
        have hcard :
            (insert z (insert w (insert y (insert v (insert x (insert u ({c} : Finset α)))))) ).card
              = 7 := by
          rw [Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hwne_z.symm, hzne_y, hzne_v, hzne_x, hzne_u, hzne_c⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hwne_y, hwne_v, hwne_x, hwne_u, hwne_c⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hyne_v, hxne_y.symm, hune_y.symm, hyne_c⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hxne_v.symm, hune_v.symm, hvne_c⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨hxne_u, hxne_c⟩),
              Finset.card_insert_of_notMem
                (by simp only [Finset.mem_singleton]; exact hune_c),
              Finset.card_singleton]
        have hle := T6.card_le_largestInducedTreeSize_splice
        rw [hcard] at hle; omega

end SimpleGraph
