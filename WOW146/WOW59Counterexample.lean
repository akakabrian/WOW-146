/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Counterexample to Written on the Wall II — Conjecture 59

This file is intentionally separate from the authoritative open-conjecture source.
It defines an explicit connected graph on `Fin 18` and proves that the exact
Conjecture 59 inequality fails.

Construction: take `K_{5,5}` on `{0,...,4}` and `{5,...,9}`, delete
`(0,5)`, `(0,6)`, `(0,7)`, `(1,5)`, add seven isolated vertices
`10,...,16`, and finally add a universal vertex `17`.
-/

namespace WrittenOnTheWallII.GraphConjecture59Counterexample

open Classical SimpleGraph Finset

/-- Directed description of a surviving edge from the left side of the
`K_{5,5}` core to its right side. -/
private def coreForward (u v : Fin 18) : Prop :=
  u.val < 5 ∧ 5 ≤ v.val ∧ v.val < 10 ∧
    ¬ ((u.val = 0 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7)) ∨
       (u.val = 1 ∧ v.val = 5))

/-- The explicit 18-vertex counterexample graph. -/
private def counterG : SimpleGraph (Fin 18) where
  Adj u v :=
    u ≠ v ∧
      (u.val = 17 ∨ v.val = 17 ∨ coreForward u v ∨ coreForward v u)
  symm u v h := by
    rcases h with ⟨hne, hcases⟩
    exact ⟨hne.symm, by tauto⟩
  loopless u h := h.1 rfl

private instance counterG_decidable : DecidableRel counterG.Adj := fun u v => by
  unfold counterG coreForward
  infer_instance

/-- Unfolded adjacency in the concrete graph. -/
private lemma counterG_adj (u v : Fin 18) :
    counterG.Adj u v ↔
      u ≠ v ∧
        (u.val = 17 ∨ v.val = 17 ∨ coreForward u v ∨ coreForward v u) :=
  Iff.rfl

/-- The universal vertex is adjacent to every other vertex. -/
private lemma counterG_center_adj (v : Fin 18) (hv : v ≠ 17) : counterG.Adj 17 v := by
  rw [counterG_adj]
  exact ⟨hv.symm, Or.inl rfl⟩

/-- Every vertex is reachable from the universal vertex. -/
private lemma counterG_reachable_from_center (v : Fin 18) : counterG.Reachable 17 v := by
  by_cases hv : v = 17
  · subst hv
    exact Reachable.refl _
  · exact (counterG_center_adj v hv).reachable

/-- The concrete graph is connected. -/
private lemma counterG_connected : counterG.Connected := by
  constructor
  intro u v
  exact (counterG_reachable_from_center u).symm.trans
    (counterG_reachable_from_center v)

/-- The exact Havel--Hakimi residue of the concrete graph is ten. -/
private lemma counterG_residue : residue counterG = 10 := by
  unfold residue
  decide +kernel

/-- The graph obtained by deleting vertex `17` is bipartite, so `b(counterG) ≥ 17`. -/
private lemma counterG_b_ge : (17 : ℝ) ≤ counterG.b := by
  unfold b
  suffices h : 17 ≤ largestInducedBipartiteSubgraphSize counterG by
    exact_mod_cast h
  apply le_csSup
  · exact ⟨18, fun n ⟨s, _, hs⟩ => hs ▸ s.card_le_univ⟩
  · refine ⟨Finset.univ.erase (17 : Fin 18), ?_, by decide⟩
    refine ⟨SimpleGraph.Coloring.mk
      (fun ⟨v, _⟩ => if v.val < 5 then (0 : Fin 2) else 1) ?_⟩
    intro ⟨u, hu⟩ ⟨v, hv⟩ hadj
    have hu_mem : u ∈ Finset.univ.erase (17 : Fin 18) := Finset.mem_coe.mp hu
    have hv_mem : v ∈ Finset.univ.erase (17 : Fin 18) := Finset.mem_coe.mp hv
    have hu_ne_center : u ≠ 17 := (Finset.mem_erase.mp hu_mem).1
    have hv_ne_center : v ≠ 17 := (Finset.mem_erase.mp hv_mem).1
    have hadj' : counterG.Adj u v := hadj
    rw [counterG_adj] at hadj'
    rcases hadj'.2 with hu17 | hv17 | huv | hvu
    · exact (hu_ne_center (Fin.ext hu17)).elim
    · exact (hv_ne_center (Fin.ext hv17)).elim
    · have hv5 : ¬v.val < 5 := by omega
      simp [huv.1, hv5]
    · have hu5 : ¬u.val < 5 := by omega
      simp [hvu.1, hu5]

/-- Construct a triangle cycle from three pairwise distinct adjacent vertices. -/
private lemma isCycle_triangle {α : Type*} {G : SimpleGraph α} {u v w : α}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwu : G.Adj w u)
    (hne1 : u ≠ v) (hne2 : v ≠ w) (hne3 : w ≠ u) :
    ∃ (p : G.Walk u u), p.IsCycle := by
  let p : G.Walk u u := Walk.cons huv (Walk.cons hvw (Walk.cons hwu Walk.nil))
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · exact Walk.IsPath.nil
      · simp [hne3]
    · simp [hne1.symm, hne2]
  · simp [SimpleGraph.Walk.edges]
    tauto

/-- Construct a 4-cycle from four pairwise distinct vertices around the cycle. -/
private lemma isCycle_quad {α : Type*} {G : SimpleGraph α} {a b c d : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hne_ab : a ≠ b) (hne_bc : b ≠ c) (hne_cd : c ≠ d) (hne_da : d ≠ a)
    (hne_ac : a ≠ c) (hne_bd : b ≠ d) :
    ∃ (p : G.Walk a a), p.IsCycle := by
  let p : G.Walk a a :=
    Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · rw [Walk.cons_isPath_iff]
        constructor
        · exact Walk.IsPath.nil
        · simp [hne_da]
      · simp [hne_cd, hne_ac.symm]
    · simp [hne_bc, hne_bd, hne_ab.symm]
  · simp [SimpleGraph.Walk.edges]
    tauto

/-- The natural inclusion of the ten-vertex core into the full graph. -/
private def coreEmbedding : Fin 10 ↪ Fin 18 where
  toFun v := ⟨v.val, by omega⟩
  inj' u v h := Fin.ext (by simpa using congrArg Fin.val h)

/-- The graph induced by the ten core vertices. -/
private def coreG : SimpleGraph (Fin 10) := counterG.comap coreEmbedding

/-- Core vertices selected by a full-graph vertex set, reindexed by `Fin 10`. -/
private def corePreimage (s : Finset (Fin 18)) : Finset (Fin 10) :=
  Finset.univ.filter fun v => coreEmbedding v ∈ s

private lemma mem_corePreimage {s : Finset (Fin 18)} {v : Fin 10} :
    v ∈ corePreimage s ↔ coreEmbedding v ∈ s := by
  simp [corePreimage]

private lemma map_corePreimage (s : Finset (Fin 18)) :
    (corePreimage s).map coreEmbedding = s.filter fun v => v.val < 10 := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨u, hu, huv⟩
    have hus : coreEmbedding u ∈ s := mem_corePreimage.mp hu
    rw [← huv]
    exact Finset.mem_filter.mpr ⟨hus, u.isLt⟩
  · intro hv
    have hvs : v ∈ s := (Finset.mem_filter.mp hv).1
    have hvlt : v.val < 10 := (Finset.mem_filter.mp hv).2
    let u : Fin 10 := ⟨v.val, hvlt⟩
    apply Finset.mem_map.mpr
    refine ⟨u, ?_, ?_⟩
    · exact mem_corePreimage.mpr (by simpa [u, coreEmbedding] using hvs)
    · apply Fin.ext
      rfl

private lemma card_corePreimage (s : Finset (Fin 18)) :
    (corePreimage s).card = (s.filter fun v => v.val < 10).card := by
  rw [← map_corePreimage s]
  simp

/-- Closed kernel certificate: every independent set in the ten-vertex core has size at most five. -/
private lemma core_independent_le :
    ∀ t : Finset (Fin 10),
      (∀ u ∈ t, ∀ v ∈ t, u ≠ v → ¬coreG.Adj u v) → t.card ≤ 5 := by
  decide +kernel

/-- Closed kernel certificate: every seven selected core vertices contain a 4-cycle. -/
private lemma core_seven_has_quad :
    ∀ t : Finset (Fin 10), 7 ≤ t.card →
      ∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t, ∃ d ∈ t,
        a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
          coreG.Adj a b ∧ coreG.Adj b c ∧ coreG.Adj c d ∧ coreG.Adj d a := by
  decide +kernel

/-- Every induced forest in the concrete graph has at most thirteen vertices. -/
private lemma counterG_forest_le : counterG.largestInducedForestSize ≤ 13 := by
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro ⟨v, hv⟩
    simp at hv
  · intro n ⟨s, hacyclic, hcard⟩
    let C := s.filter fun v => v.val < 10
    let L := s.filter fun v => 10 ≤ v.val ∧ v.val < 17
    let Z := s.filter fun v => v.val = 17
    let T := corePreimage s
    have hTcard : T.card = C.card := by
      simpa [T, C] using card_corePreimage s
    have hLsub : L ⊆ ({10, 11, 12, 13, 14, 15, 16} : Finset (Fin 18)) := by
      intro v hv
      simp only [L, Finset.mem_filter] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases v with ⟨v, hvlt⟩
      dsimp at hv ⊢
      omega
    have hLcard : L.card ≤ 7 :=
      le_trans (Finset.card_le_card hLsub) (by decide)
    have hZsub : Z ⊆ ({17} : Finset (Fin 18)) := by
      intro v hv
      simp only [Z, Finset.mem_filter] at hv
      simp only [Finset.mem_singleton]
      exact Fin.ext hv.2
    have hZcard : Z.card ≤ 1 :=
      le_trans (Finset.card_le_card hZsub) (by decide)
    have hsSub : s ⊆ (C ∪ L) ∪ Z := by
      intro v hv
      simp only [Finset.mem_union, C, L, Z, Finset.mem_filter]
      rcases Nat.lt_or_ge v.val 10 with hv10 | hv10
      · exact Or.inl (Or.inl ⟨hv, hv10⟩)
      · by_cases hv17 : v.val < 17
        · exact Or.inl (Or.inr ⟨hv, hv10, hv17⟩)
        · exact Or.inr ⟨hv, by omega⟩
    have hCL : (C ∪ L).card ≤ C.card + L.card := Finset.card_union_le
    have hsCard : s.card ≤ C.card + L.card + Z.card := by
      calc
        s.card ≤ ((C ∪ L) ∪ Z).card := Finset.card_le_card hsSub
        _ ≤ (C ∪ L).card + Z.card := Finset.card_union_le
        _ ≤ C.card + L.card + Z.card := by omega
    by_cases hc : (17 : Fin 18) ∈ s
    · have hTindep :
          ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬coreG.Adj u v := by
        intro u hu v hv huv hadj
        have hus : coreEmbedding u ∈ s := by
          exact mem_corePreimage.mp (by simpa [T] using hu)
        have hvs : coreEmbedding v ∈ s := by
          exact mem_corePreimage.mp (by simpa [T] using hv)
        have hu17 : coreEmbedding u ≠ (17 : Fin 18) := by
          intro h
          have hval := congrArg Fin.val h
          change u.val = 17 at hval
          omega
        have hv17 : coreEmbedding v ≠ (17 : Fin 18) := by
          intro h
          have hval := congrArg Fin.val h
          change v.val = 17 at hval
          omega
        let vc : s := ⟨17, hc⟩
        let vu : s := ⟨coreEmbedding u, hus⟩
        let vv : s := ⟨coreEmbedding v, hvs⟩
        have hcu : (counterG.induce s).Adj vc vu := counterG_center_adj _ hu17
        have huv' : (counterG.induce s).Adj vu vv := by
          simpa [coreG] using hadj
        have hvc : (counterG.induce s).Adj vv vc :=
          (counterG_center_adj _ hv17).symm
        have hc_ne_u : vc ≠ vu := by
          intro h
          exact hu17 (Subtype.ext_iff.mp h).symm
        have hu_ne_v : vu ≠ vv := by
          intro h
          exact huv (coreEmbedding.injective (Subtype.ext_iff.mp h))
        have hv_ne_c : vv ≠ vc := by
          intro h
          exact hv17 (Subtype.ext_iff.mp h)
        obtain ⟨p, hp⟩ := isCycle_triangle hcu huv' hvc hc_ne_u hu_ne_v hv_ne_c
        exact hacyclic p hp
      have hTle : T.card ≤ 5 := core_independent_le T hTindep
      have hCle : C.card ≤ 5 := by omega
      rw [← hcard]
      omega
    · have hZempty : Z = ∅ := by
        ext v
        constructor
        · intro hv
          have hv' := Finset.mem_filter.mp (by simpa [Z] using hv)
          have hvcenter : v = (17 : Fin 18) := Fin.ext hv'.2
          subst v
          exact (hc hv'.1).elim
        · simp
      have hZzero : Z.card = 0 := by simp [hZempty]
      have hCle : C.card ≤ 6 := by
        by_contra hnot
        have hTseven : 7 ≤ T.card := by omega
        obtain ⟨a, ha, b, hb, c, hc', d, hd,
            hab_ne, hbc_ne, hcd_ne, hda_ne, hac_ne, hbd_ne,
            hab, hbc, hcd, hda⟩ := core_seven_has_quad T hTseven
        have has : coreEmbedding a ∈ s :=
          mem_corePreimage.mp (by simpa [T] using ha)
        have hbs : coreEmbedding b ∈ s :=
          mem_corePreimage.mp (by simpa [T] using hb)
        have hcs : coreEmbedding c ∈ s :=
          mem_corePreimage.mp (by simpa [T] using hc')
        have hds : coreEmbedding d ∈ s :=
          mem_corePreimage.mp (by simpa [T] using hd)
        let va : s := ⟨coreEmbedding a, has⟩
        let vb : s := ⟨coreEmbedding b, hbs⟩
        let vc : s := ⟨coreEmbedding c, hcs⟩
        let vd : s := ⟨coreEmbedding d, hds⟩
        have hab' : (counterG.induce s).Adj va vb := by simpa [coreG] using hab
        have hbc' : (counterG.induce s).Adj vb vc := by simpa [coreG] using hbc
        have hcd' : (counterG.induce s).Adj vc vd := by simpa [coreG] using hcd
        have hda' : (counterG.induce s).Adj vd va := by simpa [coreG] using hda
        have hab_ne' : va ≠ vb := by
          intro h
          exact hab_ne (coreEmbedding.injective (Subtype.ext_iff.mp h))
        have hbc_ne' : vb ≠ vc := by
          intro h
          exact hbc_ne (coreEmbedding.injective (Subtype.ext_iff.mp h))
        have hcd_ne' : vc ≠ vd := by
          intro h
          exact hcd_ne (coreEmbedding.injective (Subtype.ext_iff.mp h))
        have hda_ne' : vd ≠ va := by
          intro h
          exact hda_ne (coreEmbedding.injective (Subtype.ext_iff.mp h))
        have hac_ne' : va ≠ vc := by
          intro h
          exact hac_ne (coreEmbedding.injective (Subtype.ext_iff.mp h))
        have hbd_ne' : vb ≠ vd := by
          intro h
          exact hbd_ne (coreEmbedding.injective (Subtype.ext_iff.mp h))
        obtain ⟨p, hp⟩ :=
          isCycle_quad hab' hbc' hcd' hda'
            hab_ne' hbc_ne' hcd_ne' hda_ne' hac_ne' hbd_ne'
        exact hacyclic p hp
      rw [← hcard]
      omega

/-- The exact Conjecture 59 inequality fails on `counterG`. -/
@[category test, AMS 5]
theorem counterexample_conjecture59 :
    ¬ (⌈Real.sqrt ((residue counterG : ℝ) * b counterG)⌉ ≤
         (counterG.largestInducedForestSize : ℝ)) := by
  intro hconj
  have hprod :
      (169 : ℝ) < (residue counterG : ℝ) * b counterG := by
    rw [counterG_residue]
    nlinarith [counterG_b_ge]
  have hsqrt :
      (13 : ℝ) < Real.sqrt ((residue counterG : ℝ) * b counterG) := by
    calc
      (13 : ℝ) = Real.sqrt 169 := by norm_num
      _ < Real.sqrt ((residue counterG : ℝ) * b counterG) :=
        Real.sqrt_lt_sqrt (by norm_num) hprod
  have hsqrt_le_ceil :
      Real.sqrt ((residue counterG : ℝ) * b counterG) ≤
        (⌈Real.sqrt ((residue counterG : ℝ) * b counterG)⌉ : ℝ) := by
    exact Int.le_ceil _
  have hforest : (counterG.largestInducedForestSize : ℝ) ≤ 13 := by
    exact_mod_cast counterG_forest_le
  linarith

/-- Repository-style classification of the universal statement as false. -/
@[category research solved, AMS 5]
theorem conjecture59_false : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected),
      ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ ≤
        (G.largestInducedForestSize : ℝ) := by
  constructor
  · intro h
    exact h.elim
  · intro hP
    exact counterexample_conjecture59 (hP (Fin 18) counterG counterG_connected)

end WrittenOnTheWallII.GraphConjecture59Counterexample
