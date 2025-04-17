/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.Tactic.NormNum.Prime
import SolvabilityLt60.Lemmas

variable {G : Type*} [Group G] [Finite G]

/-- Let $G$ be a finite group. If $|G| \leq 6$ then $G$ is solvable. -/
lemma isSolvable_of_card_le_6 (hcard : Nat.card G ≤ 6) : IsSolvable G := by
  -- Since $G$ is finite we have $0 < |G|$.
  have : 0 < Nat.card G := Nat.card_pos
  interval_cases h : Nat.card G
  . have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h).1
    apply isSolvable_of_subsingleton
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 2) (n := 1) (by simp [h])
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 3) (n := 1) (by simp [h])
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 2) (n := 2) (by simp [h])
  . exact isSolvable_of_card_prime_pow (by norm_num : Nat.Prime 5) (n := 1) (by simp [h])
  . exact isSolvable_of_card_pq (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3) (by omega) (by simp [h])
