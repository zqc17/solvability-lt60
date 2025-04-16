/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import SolvabilityLt60.SimplicityLt60.Basic

variable {G : Type*} [Group G] [Finite G]

/-- Group of order $24$ is not simple. -/
lemma not_isSimpleGroup_of_card_24 (hcard : Nat.card G = 24) : ¬IsSimpleGroup G := by
  intro _
  have card_sylow2 : Nat.card (default : Sylow 2 G) = 8 := by
    rw [Sylow.card_eq_multiplicity, hcard]; decide +native
  have dvd_index := Sylow.card_dvd_index (default : Sylow 2 G)
  rw [index_sylow_eq_ord_compl, hcard, show Nat.factorization 24 2 = 3 by decide +native,
    show 24 / 2 ^ 3 = 3 by omega, Nat.dvd_prime Nat.prime_three] at dvd_index
  have card_sylow_ne_one : Nat.card (default : Sylow 2 G) ≠ 1 := by simp [card_sylow2]
  have card_sylow_ne_card : Nat.card (default : Sylow 2 G) ≠ Nat.card G := by simp [card_sylow2, hcard]
  rcases dvd_index with h | h
  . apply not_normal_of_isSimpleGroup_of_card card_sylow_ne_one card_sylow_ne_card
    exact sylow_normal_of_card_eq_one h ..
  suffices 24 ∣ 6 by omega
  calc
    _ = Nat.card G := by rw [hcard]
    _ ∣ (Nat.card (Sylow 2 G)).factorial :=
      card_dvd_factorial_of_isSimpleGroup_of_card Nat.prime_two card_sylow_ne_one card_sylow_ne_card
    _ = _ := by rw [h]; decide
