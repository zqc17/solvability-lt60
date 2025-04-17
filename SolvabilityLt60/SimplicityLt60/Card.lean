/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.GroupTheory.Sylow

variable {G : Type*} [Group G]

/-- $H = K$ if and only if $|H| = |K|$ where $H$ is a subgroup of $K$ and $K$ is finite. -/
lemma card_eq_iff_of_le {H K : Subgroup G} [Finite (H.subgroupOf K)] (hle : H ≤ K) :
    Nat.card H = Nat.card K ↔ H = K := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  apply le_antisymm hle
  rwa [← Subgroup.subgroupOf_eq_top, ← Subgroup.card_eq_iff_eq_top,
    Nat.card_congr <| (Subgroup.subgroupOfEquivOfLe hle).1]

/-- $|G/H| = |G| / |H|$ -/
lemma card_quot_eq_card_div_card (H : Subgroup G) [Finite H] : Nat.card (G ⧸ H) = Nat.card G / Nat.card H := by
  symm
  apply Nat.div_eq_of_eq_mul_left (by simp)
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

variable [Fintype G]

open Classical

/-- If $P,Q$ are different Sylow p-group of order $p$ of $G$ then $P-\{1\}$ and $Q-\{1\}$ are disjoint. -/
lemma sylow_disjioint_of_cylclic {p : ℕ} (hp : p.Prime) (h : (Nat.card G).factorization p = 1) :
    Set.PairwiseDisjoint ↑(Finset.univ : Finset (Sylow p G))
      (fun P : Sylow p G => Finset.erase {g | g ∈ P} 1) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro P hP Q hQ ⟨g, hg⟩
  rw [Finset.mem_inter, Finset.mem_erase, Finset.mem_filter, Finset.mem_erase, Finset.mem_filter] at hg
  rcases hg with ⟨⟨hgne, -, hgmemp⟩, ⟨-, -, hgmemq⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have cardP : Nat.card P = p := by rw [Sylow.card_eq_multiplicity, h, pow_one]
  have cardQ : Nat.card Q = p := by rw [Sylow.card_eq_multiplicity, h, pow_one]
  have card_zpowers_ne : Nat.card (Subgroup.zpowers g) ≠ 1 := by
    rwa [ne_eq, Subgroup.card_eq_one, Subgroup.zpowers_eq_bot, ← ne_eq]
  have card_zpowers : Nat.card (Subgroup.zpowers g) = p := by
    refine Or.resolve_left ?_ card_zpowers_ne
    rw [← Nat.dvd_prime hp, ← cardP]
    exact Subgroup.card_dvd_of_le (by simpa)
  rw [Sylow.ext_iff]
  trans Subgroup.zpowers g
  . rw [eq_comm, ← card_eq_iff_of_le (by simpa), card_zpowers, cardP]
  . rw [← card_eq_iff_of_le (by simpa), card_zpowers, cardQ]

/-- $\sum_{P\in Syl_p(G)} |P-\{1\}| = |Syl_p(G)|*(|P|-1)$ -/
lemma sum_card_sylow_erase_one_eq {p : ℕ} (hp : p.Prime) :
    ∑ P : Sylow p G, (Finset.erase {g | g ∈ P} 1).card = Nat.card (Sylow p G) • (Nat.card (default : Sylow p G) - 1) := by
  rw [show Nat.card (Sylow p G) = (Finset.univ : Finset (Sylow p G)).card by simp, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro P hP
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.add_right_cancel_iff (n := 1), Nat.sub_add_cancel Nat.card_pos,
    Finset.card_erase_add_one (by simpa using one_mem P),
    show ({g | g ∈ P} : Finset G).card = Nat.card P by simp [← Finset.card_subtype]; rfl,
    Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
