/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.Tactic.NormNum.Prime
import SolvabilityLt60.Lemmas
import SolvabilityLt60.SpecialCases

variable {G : Type*} [Group G] [Finite G]

/-- Split into $5$ cases. -/
lemma cases_card_lt_60_gt_28 (hlt : Nat.card G < 60) (hgt : 28 < Nat.card G) :
    Nat.card G ∈ ({29, 31, 32, 37, 41, 43, 47, 49, 53, 59} : Finset ℕ) ∨
    Nat.card G ∈ ({33, 34, 35, 38, 39, 46, 51, 55, 57, 58} : Finset ℕ) ∨
    Nat.card G ∈ ({50, 54} : Finset ℕ) ∨
    Nat.card G ∈ ({44, 52} : Finset ℕ) ∨
    Nat.card G ∈ ({30, 36, 40, 42, 45, 48, 56} : Finset ℕ) := by
  have : 0 < Nat.card G := Nat.card_pos
  interval_cases Nat.card G <;> decide

/-- Group of order less than 60 is solvable. -/
theorem isSolvable_of_card_lt_60 (hcard : Nat.card G < 60) : IsSolvable G := by
  rcases le_or_lt (Nat.card G) 28 with h | h
  . exact isSolvable_of_card_le_28 h
  rcases cases_card_lt_60_gt_28 hcard h with h1 | h2 | h3 | h4 | h5
  . simp at h1
    casesm* _ ∨ _
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 29) (n := 1) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 31) (n := 1) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 2) (n := 5) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 37) (n := 1) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 41) (n := 1) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 43) (n := 1) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 47) (n := 1) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 7) (n := 2) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 53) (n := 1) (by simp [h1])
    . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 59) (n := 1) (by simp [h1])
  . simp at h2
    casesm* _ ∨ _
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 3) (by norm_num : Nat.Prime 11) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 17) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 5) (by norm_num : Nat.Prime 7) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 19) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 3) (by norm_num : Nat.Prime 13) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 23) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 3) (by norm_num : Nat.Prime 17) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 5) (by norm_num : Nat.Prime 11) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 3) (by norm_num : Nat.Prime 19) (by norm_num) (by simp [h2])
    . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 29) (by norm_num) (by simp [h2])
  . simp at h3
    casesm* _ ∨ _
    . exact isSolvable_of_card_2pn (n := 2) (by norm_num : Nat.Prime 5) (by norm_num) (by simp [h3])
    . exact isSolvable_of_card_2pn (n := 3) (by norm_num : Nat.Prime 3) (by norm_num) (by simp [h3])
  . simp at h4
    casesm* _ ∨ _
    . exact isSolvable_of_lt_of_card_p2q (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 11) (by norm_num) (by simp [h4])
    . exact isSolvable_of_lt_of_card_p2q (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 13) (by norm_num) (by simp [h4])
  . simp at h5
    casesm* _ ∨ _
    . exact isSolvable_of_card_30 h5
    . exact isSolvable_of_card_36 h5
    . exact isSolvable_of_card_40 h5
    . exact isSolvable_of_card_42 h5
    . exact isSolvable_of_card_45 h5
    . exact isSolvable_of_card_48 h5
    . exact isSolvable_of_card_56 h5
