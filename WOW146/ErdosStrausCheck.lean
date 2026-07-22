import Mathlib

namespace ErdosStrausCheck

def HasDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ 0 < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z)

def HasDistinctDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    1 ≤ x ∧ x < y ∧ y < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z)

theorem HasDistinctDecomposition.hasDecomposition
    {n : ℕ} (h : HasDistinctDecomposition n) :
    HasDecomposition n := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, hEq⟩
  exact ⟨x, y, z, by omega, by omega, by omega, hEq⟩

theorem HasDistinctDecomposition.toRational
    {n : ℕ} (hn : 0 < n) (h : HasDistinctDecomposition n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, hEq⟩
  refine ⟨x, y, z, hx, hxy, hyz, ?_⟩
  have hnx : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hxx : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < x))
  have hyx : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < y))
  have hzx : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < z))
  have hEqQ :
      (4 : ℚ) * x * y * z = n * (x * y + x * z + y * z) := by
    exact_mod_cast hEq
  field_simp [hnx, hxx, hyx, hzx]
  ring_nf at hEqQ ⊢
  exact hEqQ

theorem even_family (m : ℕ) (hm : 2 ≤ m) :
    HasDistinctDecomposition (2 * m) := by
  refine ⟨m, m + 1, m * (m + 1), by omega, by omega, ?_, ?_⟩
  · nlinarith
  · ring

theorem mod_three_two_family (k : ℕ) (hk : 1 ≤ k) :
    HasDistinctDecomposition (3 * k + 2) := by
  refine ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1),
    by omega, by omega, ?_, ?_⟩
  · nlinarith
  · ring

theorem mod_four_three_family (k : ℕ) :
    HasDistinctDecomposition (4 * k + 3) := by
  let M := (4 * k + 3) * (k + 1)
  have hM : 1 < M := by
    dsimp [M]
    nlinarith
  have hMpos : 0 < M + 1 := by omega
  refine ⟨k + 1, M + 1, M * (M + 1), by omega, ?_, ?_, ?_⟩
  · dsimp [M]
    nlinarith
  · calc
      M + 1 = (M + 1) * 1 := by simp
      _ < (M + 1) * M := Nat.mul_lt_mul_of_pos_left hM hMpos
      _ = M * (M + 1) := by ring
  · dsimp [M]
    ring

theorem mod_eight_five_family (k : ℕ) :
    HasDistinctDecomposition (8 * k + 5) := by
  refine ⟨2 * (k + 1), (8 * k + 5) * (k + 1),
    2 * (8 * k + 5) * (k + 1), by omega, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · ring

theorem HasDecomposition.scale {n m : ℕ}
    (h : HasDecomposition n) (hm : 0 < m) :
    HasDecomposition (m * n) := by
  rcases h with ⟨x, y, z, hx, hy, hz, hEq⟩
  refine ⟨m * x, m * y, m * z, by positivity, by positivity, by positivity, ?_⟩
  calc
    4 * (m * x) * (m * y) * (m * z)
        = m ^ 3 * (4 * x * y * z) := by ring
    _ = m ^ 3 * (n * (x * y + x * z + y * z)) := by rw [hEq]
    _ = (m * n) * ((m * x) * (m * y) + (m * x) * (m * z) + (m * y) * (m * z)) := by
      ring

theorem HasDistinctDecomposition.scale {n m : ℕ}
    (h : HasDistinctDecomposition n) (hm : 0 < m) :
    HasDistinctDecomposition (m * n) := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, hEq⟩
  have hmx : 0 < m * x := by positivity
  refine ⟨m * x, m * y, m * z, by omega, ?_, ?_, ?_⟩
  · exact (Nat.mul_lt_mul_left hm).2 hxy
  · exact (Nat.mul_lt_mul_left hm).2 hyz
  · calc
      4 * (m * x) * (m * y) * (m * z)
          = m ^ 3 * (4 * x * y * z) := by ring
      _ = m ^ 3 * (n * (x * y + x * z + y * z)) := by rw [hEq]
      _ = (m * n) * ((m * x) * (m * y) + (m * x) * (m * z) + (m * y) * (m * z)) := by
        ring

theorem hasDistinctDecomposition_of_mod_twenty_four_ne_one
    (n : ℕ) (hn : 2 < n) (hmod : n % 24 ≠ 1) :
    HasDistinctDecomposition n := by
  have hdiv24 := Nat.mod_add_div n 24
  have hdiv2 := Nat.mod_add_div n 2
  have hdiv3 := Nat.mod_add_div n 3
  have hdiv4 := Nat.mod_add_div n 4
  have hdiv8 := Nat.mod_add_div n 8
  have hclasses :
      n % 2 = 0 ∨ n % 3 = 0 ∨ n % 3 = 2 ∨ n % 4 = 3 ∨ n % 8 = 5 := by
    omega
  rcases hclasses with h2 | h3 | h32 | h43 | h85
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = 2 * m := by
      exact ⟨n / 2, by omega⟩
    subst n
    exact even_family m (by omega)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m * 3 := by
      exact ⟨n / 3, by omega⟩
    subst n
    exact (mod_four_three_family 0).scale (by omega)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 3 * k + 2 := by
      exact ⟨n / 3, by omega⟩
    subst n
    exact mod_three_two_family k (by omega)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 3 := by
      exact ⟨n / 4, by omega⟩
    subst n
    exact mod_four_three_family k
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 8 * k + 5 := by
      exact ⟨n / 8, by omega⟩
    subst n
    exact mod_eight_five_family k

theorem counterexample_mod_twenty_four_eq_one
    (n : ℕ) (hn : 2 < n) (hnot : ¬ HasDistinctDecomposition n) :
    n % 24 = 1 := by
  by_contra hmod
  exact hnot (hasDistinctDecomposition_of_mod_twenty_four_ne_one n hn hmod)

theorem typeII_factor_pair_identity
    (p a b c s d : ℕ)
    (hab : a + b = d * s)
    (hpd : p + d = 4 * (a * b * c)) :
    4 * (a * b * c) * (p * a * c * s) * (p * b * c * s) =
      p * ((a * b * c) * (p * a * c * s) +
        (a * b * c) * (p * b * c * s) +
        (p * a * c * s) * (p * b * c * s)) := by
  calc
    4 * (a * b * c) * (p * a * c * s) * (p * b * c * s)
        = 4 * p ^ 2 * a ^ 2 * b ^ 2 * c ^ 3 * s ^ 2 := by ring
    _ = p ^ 2 * a * b * c ^ 2 * s * ((p + d) * s) := by
      rw [hpd]
      ring
    _ = p ^ 2 * a * b * c ^ 2 * s * (p * s + (a + b)) := by
      rw [hab]
      ring
    _ = p * ((a * b * c) * (p * a * c * s) +
        (a * b * c) * (p * b * c * s) +
        (p * a * c * s) * (p * b * c * s)) := by ring

theorem typeII_factor_pair_hasDistinctDecomposition
    (p a b c s d : ℕ)
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 < s)
    (ha_lt_b : a < b) (hb_lt_ps : b < p * s)
    (hab : a + b = d * s)
    (hpd : p + d = 4 * (a * b * c)) :
    HasDistinctDecomposition p := by
  have habc : 0 < a * b * c := by positivity
  have hac : 0 < a * c := by positivity
  have hpcs : 0 < p * c * s := by positivity
  refine ⟨a * b * c, p * a * c * s, p * b * c * s, ?_, ?_, ?_, ?_⟩
  · omega
  · calc
      a * b * c = (a * c) * b := by ring
      _ < (a * c) * (p * s) := Nat.mul_lt_mul_of_pos_left hb_lt_ps hac
      _ = p * a * c * s := by ring
  · calc
      p * a * c * s = (p * c * s) * a := by ring
      _ < (p * c * s) * b := Nat.mul_lt_mul_of_pos_left ha_lt_b hpcs
      _ = p * b * c * s := by ring
  · exact typeII_factor_pair_identity p a b c s d hab hpd

def HasOppositeCoprimeDivisors (x d : ℕ) : Prop :=
  ∃ a b : ℕ,
    0 < a ∧ a < b ∧ Nat.Coprime a b ∧ a ∣ x ∧ b ∣ x ∧ d ∣ a + b

theorem oppositeCoprimeDivisors_hasDistinctDecomposition
    (p d x : ℕ)
    (hp : 0 < p) (hx : 0 < x) (hdp : d < p)
    (hpd : p + d = 4 * x)
    (h : HasOppositeCoprimeDivisors x d) :
    HasDistinctDecomposition p := by
  rcases h with ⟨a, b, ha, hab, hcop, hax, hbx, hdab⟩
  have habx : a * b ∣ x := hcop.mul_dvd_of_dvd_of_dvd hax hbx
  rcases habx with ⟨c, hxc⟩
  have hc : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    simp at hxc
    omega
  rcases hdab with ⟨s, habs⟩
  have hs : 0 < s := by
    by_contra hs
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    simp at habs
    omega
  have hps : d * s < p * s := (Nat.mul_lt_mul_right hs).2 hdp
  have hbds : b < d * s := by omega
  have hb_lt_ps : b < p * s := lt_trans hbds hps
  apply typeII_factor_pair_hasDistinctDecomposition p a b c s d hp ha
    (lt_trans ha hab) hc hs hab hb_lt_ps
  · exact habs
  · calc
      p + d = 4 * x := hpd
      _ = 4 * (a * b * c) := by rw [hxc]

def IsCounterexample (n : ℕ) : Prop :=
  2 < n ∧ ¬ HasDistinctDecomposition n

theorem exists_prime_counterexample_one_mod_twenty_four
    (h : ∃ n : ℕ, IsCounterexample n) :
    ∃ p : ℕ, p.Prime ∧ p % 24 = 1 ∧ ¬ HasDistinctDecomposition p := by
  classical
  let p := @Nat.find IsCounterexample (Classical.decPred _) h
  have hpCounter : IsCounterexample p := by
    dsimp [p]
    exact @Nat.find_spec IsCounterexample (Classical.decPred _) h
  have hpMin : ∀ {m : ℕ}, m < p → ¬ IsCounterexample m := by
    intro m hm
    dsimp [p] at hm ⊢
    exact @Nat.find_min IsCounterexample (Classical.decPred _) h m hm
  have hpmod : p % 24 = 1 :=
    counterexample_mod_twenty_four_eq_one p hpCounter.1 hpCounter.2
  have hpPrime : p.Prime := by
    rw [Nat.prime_iff_not_exists_mul_eq]
    refine ⟨by omega, ?_⟩
    rintro ⟨a, b, ha, hb, hab⟩
    have ha0 : a ≠ 0 := by
      intro hzero
      subst a
      simp at hab
      omega
    have ha1 : a ≠ 1 := by
      intro hone
      subst a
      simp at hab
      omega
    have ha2 : a ≠ 2 := by
      intro htwo
      subst a
      omega
    have ha_gt_two : 2 < a := by omega
    have hbpos : 0 < b := by
      by_contra hnot
      have hbzero : b = 0 := Nat.eq_zero_of_not_pos hnot
      subst b
      simp at hab
      omega
    have haNotCounter : ¬ IsCounterexample a := hpMin ha
    have haDecomp : HasDistinctDecomposition a := by
      by_contra hnot
      exact haNotCounter ⟨ha_gt_two, hnot⟩
    have hscaled : HasDistinctDecomposition (b * a) := haDecomp.scale hbpos
    have hba : b * a = p := by simpa [Nat.mul_comm] using hab
    exact hpCounter.2 (by simpa [hba] using hscaled)
  exact ⟨p, hpPrime, hpmod, hpCounter.2⟩

theorem oppositeCoprimeDivisors_three_of_divisor_mod_three_two
    (x q : ℕ) (hq : q ∣ x) (hqmod : q % 3 = 2) :
    HasOppositeCoprimeDivisors x 3 := by
  have hqdiv := Nat.mod_add_div q 3
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 3 * k + 2 := by
    exact ⟨q / 3, by omega⟩
  refine ⟨1, q, by omega, by omega, by simp, by simp, hq, ?_⟩
  refine ⟨k + 1, ?_⟩
  omega

theorem dThree_gate_hasDistinctDecomposition
    (p x q : ℕ) (hp : 3 < p) (hx : 0 < x)
    (hpd : p + 3 = 4 * x) (hq : q ∣ x) (hqmod : q % 3 = 2) :
    HasDistinctDecomposition p := by
  apply oppositeCoprimeDivisors_hasDistinctDecomposition p 3 x (by omega) hx hp hpd
  exact oppositeCoprimeDivisors_three_of_divisor_mod_three_two x q hq hqmod

end ErdosStrausCheck
