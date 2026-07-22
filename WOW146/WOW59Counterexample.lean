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

private def coreForward (u v : Fin 18) : Prop :=
  u.val < 5 ∧ 5 ≤ v.val ∧ v.val < 10 ∧
    ¬ ((u.val = 0 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7)) ∨
       (u.val = 1 ∧ v.val = 5))

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

private lemma counterG_adj (u v : Fin 18) :
    counterG.Adj u v ↔
      u ≠ v ∧
        (u.val = 17 ∨ v.val = 17 ∨ coreForward u v ∨ coreForward v u) :=
  Iff.rfl

private lemma counterG_center_adj (v : Fin 18) (hv : v ≠ 17) : counterG.Adj 17 v := by
  rw [counterG_adj]
  exact ⟨hv.symm, Or.inl rfl⟩

private lemma counterG_reachable_from_center (v : Fin 18) : counterG.Reachable 17 v := by
  by_cases hv : v = 17
  · subst hv
    exact Reachable.refl _
  · exact (counterG_center_adj v hv).reachable

private lemma counterG_connected : counterG.Connected := by
  constructor
  intro u v
  exact (counterG_reachable_from_center u).symm.trans
    (counterG_reachable_from_center v)

private lemma counterG_residue : residue counterG = 10 := by
  unfold residue
  decide +native

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

private lemma large_with_center_has_edge :
    ∀ s : Finset (Fin 18), (17 : Fin 18) ∈ s → 14 ≤ s.card →
      ∃ u ∈ s, ∃ v ∈ s,
        u ≠ v ∧ u ≠ 17 ∧ v ≠ 17 ∧ counterG.Adj u v := by
  decide +native

private lemma large_without_center_has_quad :
    ∀ s : Finset (Fin 18), (17 : Fin 18) ∉ s → 14 ≤ s.card →
      ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s,
        a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
          counterG.Adj a b ∧ counterG.Adj b c ∧
          counterG.Adj c d ∧ counterG.Adj d a := by
  decide +native

private lemma counterG_forest_le : counterG.largestInducedForestSize ≤ 13 := by
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro ⟨v, hv⟩
    simp at hv
  · intro n ⟨s, hacyclic, hcard⟩
    by_contra hnot
    have hs14 : 14 ≤ s.card := by omega
    by_cases hc : (17 : Fin 18) ∈ s
    · obtain ⟨u, hu, v, hv, huv, hu17, hv17, hadj⟩ :=
        large_with_center_has_edge s hc hs14
      let vc : s := ⟨17, hc⟩
      let vu : s := ⟨u, hu⟩
      let vv : s := ⟨v, hv⟩
      have hcu : (counterG.induce s).Adj vc vu := counterG_center_adj u hu17
      have huv' : (counterG.induce s).Adj vu vv := hadj
      have hvc : (counterG.induce s).Adj vv vc := (counterG_center_adj v hv17).symm
      have hc_ne_u : vc ≠ vu := by
        intro h
        exact hu17 (Subtype.ext_iff.mp h).symm
      have hu_ne_v : vu ≠ vv := fun h => huv (Subtype.ext_iff.mp h)
      have hv_ne_c : vv ≠ vc := by
        intro h
        exact hv17 (Subtype.ext_iff.mp h)
      obtain ⟨p, hp⟩ := isCycle_triangle hcu huv' hvc hc_ne_u hu_ne_v hv_ne_c
      exact hacyclic p hp
    · obtain ⟨a, ha, b, hb, c, hc', d, hd,
          hab_ne, hbc_ne, hcd_ne, hda_ne, hac_ne, hbd_ne,
          hab, hbc, hcd, hda⟩ := large_without_center_has_quad s hc hs14
      let va : s := ⟨a, ha⟩
      let vb : s := ⟨b, hb⟩
      let vc : s := ⟨c, hc'⟩
      let vd : s := ⟨d, hd⟩
      have hab' : (counterG.induce s).Adj va vb := hab
      have hbc' : (counterG.induce s).Adj vb vc := hbc
      have hcd' : (counterG.induce s).Adj vc vd := hcd
      have hda' : (counterG.induce s).Adj vd va := hda
      have hab_ne' : va ≠ vb := fun h => hab_ne (Subtype.ext_iff.mp h)
      have hbc_ne' : vb ≠ vc := fun h => hbc_ne (Subtype.ext_iff.mp h)
      have hcd_ne' : vc ≠ vd := fun h => hcd_ne (Subtype.ext_iff.mp h)
      have hda_ne' : vd ≠ va := fun h => hda_ne (Subtype.ext_iff.mp h)
      have hac_ne' : va ≠ vc := fun h => hac_ne (Subtype.ext_iff.mp h)
      have hbd_ne' : vb ≠ vd := fun h => hbd_ne (Subtype.ext_iff.mp h)
      obtain ⟨p, hp⟩ :=
        isCycle_quad hab' hbc' hcd' hda'
          hab_ne' hbc_ne' hcd_ne' hda_ne' hac_ne' hbd_ne'
      exact hacyclic p hp

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
