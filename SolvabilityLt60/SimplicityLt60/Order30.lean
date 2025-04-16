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

/-- If $p,q$ are different prime numbers then $⋃_{P\in Syl_p(G)},P-\{1\}$ and $⋃_{Q\in Syl_q(G)},Q-\{1\}$ are disjoint. -/
lemma disjoint_of_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp' : (Nat.card G).factorization p = 1) (hq' : (Nat.card G).factorization q = 1) :
    Disjoint (Finset.disjiUnion _ _ (sylow_disjioint_of_cylclic hp hp'))
      (Finset.disjiUnion _ _ (sylow_disjioint_of_cylclic hq hq')) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext g
  simp
  intro hgne P hgmemp _ Q hgmemq
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have cardP : Nat.card P = p := by rw [Sylow.card_eq_multiplicity, hp', pow_one]
  have cardQ : Nat.card Q = q := by rw [Sylow.card_eq_multiplicity, hq', pow_one]
  have orderOf_ne_one : orderOf g ≠ 1 := by rwa [ne_eq, orderOf_eq_one_iff]
  absurd hpq
  trans orderOf g
  . symm
    refine Or.resolve_left ?_ orderOf_ne_one
    rw [← Nat.dvd_prime hp, ← cardP]
    exact Subgroup.orderOf_dvd_natCard _ (by simpa)
  . refine Or.resolve_left ?_ orderOf_ne_one
    rw [← Nat.dvd_prime hq, ← cardQ]
    exact Subgroup.orderOf_dvd_natCard _ (by simpa)

/-- Group of order $30$ is not simple. -/
theorem not_isSimpleGroup_of_card_30 (hcard : Nat.card G = 30) : ¬IsSimpleGroup G := by
  intro h
  -- Step(1): Show $|Syl_3(G)| = 10$.
  have card_sylow3 : Nat.card ((default : Sylow 3 G)) = 3 := by
    rw [Sylow.card_eq_multiplicity, hcard]; decide +native
  have mod3_eq_one := card_sylow_modEq_one 3 G
  have syl3_dvd_index := Sylow.card_dvd_index (default : Sylow 3 G)
  rw [index_sylow_eq_ord_compl, hcard, show Nat.factorization 30 3 = 1 by decide +native,
    show 30 / 3 ^ 1 = 10 by omega] at syl3_dvd_index
  have mem_divisors10 : Nat.card (Sylow 3 G) ∈ Nat.divisors 10 := by
    rw [Nat.mem_divisors]; exact ⟨syl3_dvd_index, by norm_num⟩
  simp [show Nat.divisors 10 = {1, 2, 5, 10} by decide, -Nat.card_eq_fintype_card] at mem_divisors10
  have card_sylow3_ne_one : Nat.card (default : Sylow 3 G) ≠ 1 := by rw [card_sylow3]; norm_num
  have card_sylow3_ne_card : Nat.card (default : Sylow 3 G) ≠ Nat.card G := by rw [card_sylow3, hcard]; omega
  rcases mem_divisors10 with h | h | h | h <;> rw [h] at mod3_eq_one <;> norm_num [Nat.ModEq] at mod3_eq_one
  . apply not_normal_of_isSimpleGroup_of_card card_sylow3_ne_one card_sylow3_ne_card
    exact sylow_normal_of_card_eq_one h ..
  -- Step(2): Show $|Syl_5(G)| = 6$.
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have card_sylow5 : Nat.card ((default : Sylow 5 G)) = 5 := by
    rw [Sylow.card_eq_multiplicity, hcard]; decide +native
  have mod5_eq_one := card_sylow_modEq_one 5 G
  have syl5_dvd_index := Sylow.card_dvd_index (default : Sylow 5 G)
  rw [index_sylow_eq_ord_compl, hcard, show Nat.factorization 30 5 = 1 by decide +native,
    show 30 / 5 ^ 1 = 6 by omega] at syl5_dvd_index
  have mem_divisors6 : Nat.card (Sylow 5 G) ∈ Nat.divisors 6 := by
    rw [Nat.mem_divisors]; exact ⟨syl5_dvd_index, by norm_num⟩
  simp [show Nat.divisors 6 = {1, 2, 3, 6} by decide, -Nat.card_eq_fintype_card] at mem_divisors6
  have card_sylow5_ne_one : Nat.card (default : Sylow 5 G) ≠ 1 := by rw [card_sylow5]; norm_num
  have card_sylow5_ne_card : Nat.card (default : Sylow 5 G) ≠ Nat.card G := by rw [card_sylow5, hcard]; norm_num
  rcases mem_divisors6 with H | H | H | H <;> rw [H] at mod5_eq_one <;> norm_num [Nat.ModEq] at mod5_eq_one
  . apply not_normal_of_isSimpleGroup_of_card card_sylow5_ne_one card_sylow5_ne_card
    exact sylow_normal_of_card_eq_one H ..
  -- Step(3): Deduce contradiction by showing
  -- $|⋃_{P\in Syl_p(G)},P-\{1\}| + |⋃_{Q\in Syl_q(G)},Q-\{1\}| > |G|$.
  have h1 : (Nat.card G).factorization 3 = 1 := by rw [hcard]; decide +native
  have h2 : (Nat.card G).factorization 5 = 1 := by rw [hcard]; decide +native
  suffices 10 * (3 - 1) + 6 * (5 - 1) ≤ 30 by omega
  calc
    _ = Nat.card (Sylow 3 G) • (3 - 1) + Nat.card (Sylow 5 G) • (5 - 1) := by rw [h, H]; simp
    _ = ∑ a : Sylow 3 G, (((Finset.univ : Finset G).filter fun g => g ∈ a).erase 1).card +
        ∑ a : Sylow 5 G, (((Finset.univ : Finset G).filter fun g => g ∈ a).erase 1).card := by
      congr
      . rw [sum_card_sylow_erase_one_eq Fact.out, Sylow.card_eq_multiplicity, hcard]
        congr 2
        decide +native
      . rw [sum_card_sylow_erase_one_eq Fact.out, Sylow.card_eq_multiplicity, hcard]
        congr 2
        decide +native
    _ = ((Finset.disjiUnion _ _ (sylow_disjioint_of_cylclic Fact.out h1)) ∪
        (Finset.disjiUnion _ _ (sylow_disjioint_of_cylclic Fact.out h2))).card := by
      rw [Finset.card_union_eq_card_add_card.mpr, Finset.card_disjiUnion, Finset.card_disjiUnion]
      exact disjoint_of_prime_ne Nat.prime_three Fact.out (by norm_num)
        (by rw [hcard]; decide +native) (by rw [hcard]; decide +native)
    _ ≤ (Finset.univ : Finset G).card := by apply Finset.card_le_card; simp
    _ = _ := by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
