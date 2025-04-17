/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.Tactic.NormNum.Prime
import SolvabilityLt60.Basic
import SolvabilityLt60.Lemmas
import SolvabilityLt60.SimplicityLt60.Order30
import SolvabilityLt60.SimplicityLt60.Order36
import SolvabilityLt60.SimplicityLt60.Order48
import SolvabilityLt60.SimplicityLt60.Order56
import SolvabilityLt60.OrderLe24

variable {G : Type*} [Group G] [Finite G]

/-- Group of order $40$ is solvable. -/
lemma isSolvable_of_card_40 (hcard : Nat.card G = 40) : IsSolvable G := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have mod5_eq_one := card_sylow_modEq_one 5 G
  have dvd_index := Sylow.card_dvd_index (default : Sylow 5 G)
  rw [index_sylow_eq_ord_compl, hcard, show Nat.factorization 40 5 = 1 by decide +native, pow_one,
    show 40 / 5 = 8 by omega] at dvd_index
  have mem_divisors8 : Nat.card (Sylow 5 G) ∈ Nat.divisors 8 := by rw [Nat.mem_divisors]; simpa
  simp [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at mem_divisors8
  rcases mem_divisors8 with h | h | h | h <;> norm_num [h, Nat.ModEq] at mod5_eq_one
  have sylow_normal : ((default : Sylow 5 G) : Subgroup G).Normal := by
    exact sylow_normal_of_card_eq_one h ..
  have : IsSolvable (G ⧸ ((default : Sylow 5 G) : Subgroup G)) := by
    apply isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 2) (n := 3)
    rw [card_quot_eq_card_div_card, Sylow.card_eq_multiplicity, hcard,
      show Nat.factorization 40 5 = 1 by decide +native]
    rfl
  exact isSolvable_of_subgroup_of_quot sylow_normal

/-- Group of order $42$ is solvable. -/
lemma isSolvable_of_card_42 (hcard : Nat.card G = 42) : IsSolvable G := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have mod7_eq_one := card_sylow_modEq_one 7 G
  have dvd_index := Sylow.card_dvd_index (default : Sylow 7 G)
  rw [index_sylow_eq_ord_compl, hcard, show Nat.factorization 42 7 = 1 by decide +native, pow_one,
    show 42 / 7 = 6 by omega] at dvd_index
  have mem_divisors8 : Nat.card (Sylow 7 G) ∈ Nat.divisors 6 := by rw [Nat.mem_divisors]; simpa
  simp [show Nat.divisors 6 = {1, 2, 3, 6} by decide] at mem_divisors8
  rcases mem_divisors8 with h | h | h | h <;> rw [h] at mod7_eq_one <;> norm_num [Nat.ModEq] at mod7_eq_one
  have sylow_normal : ((default : Sylow 7 G) : Subgroup G).Normal := by
    exact sylow_normal_of_card_eq_one h ..
  have : IsSolvable (G ⧸ ((default : Sylow 7 G) : Subgroup G)) := by
    apply isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num)
    rw [card_quot_eq_card_div_card, Sylow.card_eq_multiplicity, hcard,
      show Nat.factorization 42 7 = 1 by decide +native]
    rfl
  exact isSolvable_of_subgroup_of_quot sylow_normal

/-- Group of order $45$ is solvable. -/
lemma isSolvable_of_card_45 (hcard : Nat.card G = 45) : IsSolvable G := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have mod3_eq_one := card_sylow_modEq_one 3 G
  have dvd_index := Sylow.card_dvd_index (default : Sylow 3 G)
  rw [index_sylow_eq_ord_compl, hcard, show Nat.factorization 45 3 = 2 by decide +native,
    show 45 / 3 ^ 2 = 5 by rfl, Nat.dvd_prime (by norm_num)] at dvd_index
  rcases dvd_index with h | h <;> norm_num [h, Nat.ModEq] at mod3_eq_one
  have sylow_normal : ((default : Sylow 3 G) : Subgroup G).Normal := by
    exact sylow_normal_of_card_eq_one h ..
  have : IsSolvable (G ⧸ ((default : Sylow 3 G) : Subgroup G)) := by
    apply isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 5) (n := 1)
    rw [card_quot_eq_card_div_card, Sylow.card_eq_multiplicity, hcard,
      show Nat.factorization 45 3 = 2 by decide +native]
    rfl
  exact isSolvable_of_subgroup_of_quot sylow_normal

/-- Group of order $30$ is solvable. -/
lemma isSolvable_of_card_30 (hcard : Nat.card G = 30) : IsSolvable G := by
  have : Nontrivial G := by rw [← Finite.one_lt_card_iff_nontrivial, hcard]; omega
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨H, Hnormal, Hgt, Hlt⟩ := exists_lt_lt_of_not_isSimpleGroup (not_isSimpleGroup_of_card_30 hcard)
  have : IsSolvable H := by
    apply isSolvable_of_card_le_24
    calc
      _ ≤ Nat.card G / 2 := by exact card_le_card_div_two Hlt
      _ ≤ _ := by rw [hcard]; omega
  have : IsSolvable (G ⧸ H) := by
    apply isSolvable_of_card_le_24
    calc
      _ ≤ Nat.card G / 2 := by exact card_quot_le_card_div_two Hgt
      _ ≤ _ := by rw [hcard]; omega
  exact isSolvable_of_subgroup_of_quot Hnormal

/-- Group of order $36$ is solvable. -/
lemma isSolvable_of_card_36 (hcard : Nat.card G = 36) : IsSolvable G := by
  have : Nontrivial G := by rw [← Finite.one_lt_card_iff_nontrivial, hcard]; omega
  obtain ⟨H, Hnormal, Hgt, Hlt⟩ := exists_lt_lt_of_not_isSimpleGroup (not_isSimpleGroup_of_card_36 hcard)
  have : IsSolvable H := by
    apply isSolvable_of_card_le_24
    calc
      _ ≤ Nat.card G / 2 := by exact card_le_card_div_two Hlt
      _ ≤ _ := by simp [hcard]
  have : IsSolvable (G ⧸ H) := by
    apply isSolvable_of_card_le_24
    calc
      _ ≤ Nat.card G / 2 := by exact card_quot_le_card_div_two Hgt
      _ ≤ _ := by simp [hcard]
  exact isSolvable_of_subgroup_of_quot Hnormal

/-- Group of order $48$ is solvable. -/
lemma isSolvable_of_card_48 (hcard : Nat.card G = 48) : IsSolvable G := by
  have : Nontrivial G := by rw [← Finite.one_lt_card_iff_nontrivial, hcard]; omega
  obtain ⟨H, Hnormal, Hgt, Hlt⟩ := exists_lt_lt_of_not_isSimpleGroup (not_isSimpleGroup_of_card_48 hcard)
  have : IsSolvable H := by
    apply isSolvable_of_card_le_24
    calc
      _ ≤ Nat.card G / 2 := by exact card_le_card_div_two Hlt
      _ ≤ _ := by simp [hcard]
  have : IsSolvable (G ⧸ H) := by
    apply isSolvable_of_card_le_24
    calc
      _ ≤ Nat.card G / 2 := by exact card_quot_le_card_div_two Hgt
      _ ≤ _ := by simp [hcard]
  exact isSolvable_of_subgroup_of_quot Hnormal

/-- Let $G$ be a finite group. If $|G| \leq 28$ then $G$ is solvable. -/
lemma isSolvable_of_card_le_28 (hcard : Nat.card G ≤ 28) : IsSolvable G := by
  rcases le_or_lt (Nat.card G) 24 with hle24 | hgt24
  . exact isSolvable_of_card_le_24 hle24
  interval_cases h : Nat.card G
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 5) (n := 2) (by simp [h])
  . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 13) (by norm_num) (by simp [h])
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 3) (n := 3) (by simp [h])
  . exact isSolvable_of_lt_of_card_p2q Nat.prime_two (by norm_num : Nat.Prime 7) (by omega) (by simp [h])

/-- Group of order $56$ is solvable. -/
lemma isSolvable_of_card_56 (hcard : Nat.card G = 56) : IsSolvable G := by
  have : Nontrivial G := by rw [← Finite.one_lt_card_iff_nontrivial, hcard]; omega
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨H, Hnormal, Hgt, Hlt⟩ := exists_lt_lt_of_not_isSimpleGroup (not_isSimpleGroup_of_card_56 hcard)
  have : IsSolvable H := by
    apply isSolvable_of_card_le_28
    calc
      _ ≤ Nat.card G / 2 := by exact card_le_card_div_two Hlt
      _ ≤ _ := by rw [hcard]
  have : IsSolvable (G ⧸ H) := by
    apply isSolvable_of_card_le_28
    calc
      _ ≤ Nat.card G / 2 := by exact card_quot_le_card_div_two Hgt
      _ ≤ _ := by rw [hcard]
  exact isSolvable_of_subgroup_of_quot Hnormal
