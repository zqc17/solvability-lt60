/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import SolvabilityLt60.SimplicityLt60.Basic

variable {G : Type*} [Group G] [Finite G]

/-- Group of order $36$ is not simple. -/
lemma not_isSimpleGroup_of_card_36 (hcard : Nat.card G = 36) : ¬IsSimpleGroup G := by
  intro h
  have card_sylow3 : Nat.card (default : Sylow 3 G) = 9 := by
    rw [Sylow.card_eq_multiplicity, hcard]; decide +native
  have mod3_eq_one := card_sylow_modEq_one 3 G
  have dvd_index := Sylow.card_dvd_index (default : Sylow 3 G)
  rw [index_sylow_eq_ord_compl, hcard, show Nat.factorization 36 3 = 2 by decide +native,
    show 36 / 3 ^ 2 = 4 by omega] at dvd_index
  have mem_divisors : Nat.card (Sylow 3 G) ∈ Nat.divisors 4 := by rw [Nat.mem_divisors]; simpa
  simp [show Nat.divisors 4 = {1, 2, 4} by decide] at mem_divisors
  have card_sylow_ne_one : Nat.card (default : Sylow 3 G) ≠ 1 := by simp [card_sylow3]
  have card_sylow_ne_card : Nat.card (default : Sylow 3 G) ≠ Nat.card G := by simp [card_sylow3, hcard]
  rcases mem_divisors with H | H | H <;> norm_num [H, Nat.ModEq] at mod3_eq_one
  . apply not_normal_of_isSimpleGroup_of_card card_sylow_ne_one card_sylow_ne_card
    exact sylow_normal_of_card_eq_one H ..
  suffices 36 ∣ 24 by omega
  calc
    _ = Nat.card G := by rw [hcard]
    _ ∣ (Nat.card (Sylow 3 G)).factorial :=
      card_dvd_factorial_of_isSimpleGroup_of_card Nat.prime_three card_sylow_ne_one card_sylow_ne_card
    _ = _ := by rw [H]; decide
