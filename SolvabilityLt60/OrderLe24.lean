/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.Tactic.NormNum.Prime
import SolvabilityLt60.Lemmas
import SolvabilityLt60.OrderLe12
import SolvabilityLt60.SimplicityLt60.Order24

variable {G : Type*} [Group G] [Finite G]

/-- Group of order $24$ is solvable. -/
lemma isSolvable_of_card_24 (hcard : Nat.card G = 24) : IsSolvable G := by
  have : Nontrivial G := by rw [← Finite.one_lt_card_iff_nontrivial, hcard]; omega
  obtain ⟨H, Hnormal, Hgt, Hlt⟩ := exists_lt_lt_of_not_isSimpleGroup (not_isSimpleGroup_of_card_24 hcard)
  have : IsSolvable H := by
    apply isSolvable_of_card_le_12
    calc
      _ ≤ Nat.card G / 2 := by exact card_le_card_div_two Hlt
      _ ≤ _ := by simp [hcard]
  have : IsSolvable (G ⧸ H) := by
    apply isSolvable_of_card_le_12
    calc
      _ ≤ Nat.card G / 2 := by exact card_quot_le_card_div_two Hgt
      _ ≤ _ := by simp [hcard]
  exact isSolvable_of_subgroup_of_quot Hnormal

/-- Let $G$ be a finite group. If $|G| \leq 24$ then $G$ is solvable. -/
lemma isSolvable_of_card_le_24 (hcard : Nat.card G ≤ 24) : IsSolvable G := by
  rcases le_or_lt (Nat.card G) 12 with hle12 | hgt12
  . exact isSolvable_of_card_le_12 hle12
  interval_cases h : Nat.card G
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 13) (n := 1) (by simp [h])
  . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 7) (by norm_num) (by simp [h])
  . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 3) (by norm_num : Nat.Prime 5) (by norm_num) (by simp [h])
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 2) (n := 4) (by simp [h])
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 17) (n := 1) (by simp [h])
  . exact isSolvable_of_card_2pn (n := 2) Nat.prime_three (by omega) (by simp [h])
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 19) (n := 1) (by simp [h])
  . exact isSolvable_of_lt_of_card_p2q Nat.prime_two (by norm_num : Nat.Prime 5) (by omega) (by simp [h])
  . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 3) (by norm_num : Nat.Prime 7) (by norm_num) (by simp [h])
  . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 11) (by norm_num) (by simp [h])
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 23) (n := 1) (by simp [h])
  . exact isSolvable_of_card_24 h
