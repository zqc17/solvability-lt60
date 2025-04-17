/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.Tactic.NormNum.Prime
import SolvabilityLt60.SimplicityLt60.Basic
import SolvabilityLt60.SimplicityLt60.Card

variable {G : Type*} [Group G] [Fintype G]

open Classical

/-- Group of order $56$ is not simple. -/
lemma not_isSimpleGroup_of_card_56 (hcard : Nat.card G = 56) : ¬IsSimpleGroup G := by
  intro _
  -- Step(1): Show $|Syl_7(G)| = 8$.
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have card_sylow7 : Nat.card (default : Sylow 7 G) = 7 := by
    rw [Sylow.card_eq_multiplicity, hcard]; decide +native
  have mod7_eq_one := card_sylow_modEq_one 7 G
  have syl7_dvd_index := Sylow.card_dvd_index (default : Sylow 7 G)
  rw [index_sylow_eq_ord_compl, hcard, show Nat.factorization 56 7 = 1 by decide +native,
    show 56 / 7 ^ 1 = 8 by omega] at syl7_dvd_index
  have mem_divisors8 : Nat.card (Sylow 7 G) ∈ Nat.divisors 8 := by
    rw [Nat.mem_divisors]; exact ⟨syl7_dvd_index, by norm_num⟩
  simp [show Nat.divisors 8 = {1, 2, 4, 8} by decide, -Nat.card_eq_fintype_card] at mem_divisors8
  have card_sylow7_ne_one : Nat.card (default : Sylow 7 G) ≠ 1 := by rw [card_sylow7]; norm_num
  have card_sylow7_ne_card : Nat.card (default : Sylow 7 G) ≠ Nat.card G := by rw [card_sylow7, hcard]; norm_num
  rcases mem_divisors8 with h | h | h | h <;> rw [h] at mod7_eq_one <;> norm_num [Nat.ModEq] at mod7_eq_one
  . apply not_normal_of_isSimpleGroup_of_card card_sylow7_ne_one card_sylow7_ne_card
    exact sylow_normal_of_card_eq_one h ..
  -- Step(2): Show $|Syl_2(G)| \geq 2$.
  have card_sylow2 : Nat.card (default : Sylow 2 G) = 8 := by
    rw [Sylow.card_eq_multiplicity, hcard]; decide +native
  have card_sylow2_ne_one : Nat.card (default : Sylow 2 G) ≠ 1 := by rw [card_sylow2]; norm_num
  have card_sylow2_ne_card : Nat.card (default : Sylow 2 G) ≠ Nat.card G := by rw [card_sylow2, hcard]; norm_num
  rcases eq_or_ne (Nat.card (Sylow 2 G)) 1 with H | H
  . apply not_normal_of_isSimpleGroup_of_card card_sylow2_ne_one card_sylow2_ne_card
    exact sylow_normal_of_card_eq_one H ..
  have : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
  have : 2 ≤ Nat.card (Sylow 2 G) := by omega
  obtain ⟨P, Q, hne⟩ : ∃ P Q : Sylow 2 G, P ≠ Q := by
    by_contra! h
    have : Subsingleton (Sylow 2 G) := by exact { allEq := h }
    have : Nat.card (Sylow 2 G) ≤ 1 := by exact Finite.card_le_one_iff_subsingleton.mpr this
    linarith
  obtain ⟨g, hgmem, hgnotmem⟩ : ∃ g : G, g ∈ Q ∧ g ∉ P := by
    by_contra! h
    change Q ≤ P at h
    absurd hne
    symm
    rw [Sylow.ext_iff]
    apply (card_eq_iff_of_le h).mp
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  -- Step(3): Deduce contradiction by showing
  -- $|⋃_{P\in Syl_7(G)},P-\{1\}| + |P ∪ Q| > |G|$ where $P,Q$ are Sylow 2-group of $G$.
  suffices 57 ≤ 56 by omega
  calc
    _ = 48 + 9 := by norm_num
    _ ≤ 48 + Finset.card {g | g ∈ P ∨ g ∈ Q} := by
      gcongr
      calc
        _ = 8 + 1 := by norm_num
        _ = Finset.card {g | g ∈ P} + 1 := by
          congr 1
          rw [show ({g | g ∈ P} : Finset G).card = Nat.card P by simp [← Finset.card_subtype]; rfl,
            Sylow.card_eq_multiplicity, hcard]
          decide +native
        _ = (insert g ((Finset.univ : Finset G).filter fun g => g ∈ P)).card := by
          rw [Finset.card_insert_of_not_mem]; simpa
        _ ≤ ((Finset.univ : Finset G).filter fun g => g ∈ P ∨ g ∈ Q).card := by
          apply Finset.card_le_card
          intro x hx
          simp at hx ⊢
          rcases hx with hx | hx
          . right; rw [hx]; exact hgmem
          . left; exact hx
    _ = Nat.card (Sylow 7 G) • (7 - 1) + Finset.card {g | g ∈ P ∨ g ∈ Q} := by rw [h]; simp
    _ = ∑ P : Sylow 7 G, (Finset.erase {g | g ∈ P} 1).card +
        Finset.card {g | g ∈ P ∨ g ∈ Q} := by
      congr
      rw [show Nat.card (Sylow 7 G) = (Finset.univ : Finset (Sylow 7 G)).card by simp,
        ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro P hP
      symm
      rw [← Nat.add_right_cancel_iff (n := 1),  Nat.sub_add_cancel (by norm_num),
        Finset.card_erase_add_one (by simpa using one_mem P),
        show ({g | g ∈ P} : Finset G).card = Nat.card P by simp [← Finset.card_subtype]; rfl,
        Sylow.card_eq_multiplicity, hcard]
      decide +native
    _ = ((Finset.disjiUnion _ _ (sylow_disjioint_of_cylclic (Fact.out : Nat.Prime 7) (by rw [hcard]; decide +native))) ∪
        ({g | g ∈ P ∨ g ∈ Q} : Finset G)).card := by
      rw [Finset.card_union_eq_card_add_card.mpr]
      congr
      . rw [Finset.card_disjiUnion _ _ (sylow_disjioint_of_cylclic Fact.out (by rw [hcard]; decide +native))]
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp
      intro hxne R hR
      have orderOf_ne_one : orderOf x ≠ 1 := by rwa [ne_eq, orderOf_eq_one_iff]
      by_contra hx
      rw [not_and_or, not_not, not_not] at hx
      suffices 7 ∣ 8 by omega
      calc
        _ = orderOf x := by
          symm
          refine Or.resolve_left ?_ orderOf_ne_one
          have cardR : Nat.card R = 7 := by
            rw [Sylow.card_eq_multiplicity, hcard]; decide +native
          rw [← Nat.dvd_prime Fact.out, ← cardR]
          exact Subgroup.orderOf_dvd_natCard _ (by simpa)
        _ ∣ _ := by
          rcases hx with hx | hx
          . rw [← show Nat.card P = 8 by rw [Sylow.card_eq_multiplicity, hcard]; decide +native]
            exact Subgroup.orderOf_dvd_natCard _ (by simpa)
          . rw [← show Nat.card Q = 8 by rw [Sylow.card_eq_multiplicity, hcard]; decide +native]
            exact Subgroup.orderOf_dvd_natCard _ (by simpa)
    _ ≤ (Finset.univ : Finset G).card := by apply Finset.card_le_card; simp
    _ = _ := by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
