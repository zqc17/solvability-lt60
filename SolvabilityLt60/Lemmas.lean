/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import SolvabilityLt60.SimplicityLt60.Basic
import SolvabilityLt60.SimplicityLt60.Card
import SolvabilityLt60.Nat

variable {G : Type*} [Group G]

/-- If $N ⊴ G$ and $G / N$ are solvable, then $G$ is solvable. -/
lemma isSolvable_of_subgroup_of_quot {N : Subgroup G} (h : N.Normal)
    [IsSolvable N] [IsSolvable (G ⧸ N)] : IsSolvable G := by
  exact solvable_of_ker_le_range (Subgroup.subtype N) (QuotientGroup.mk' N) (by simp)

variable [Finite G]

/-- p-groups are solvable. -/
lemma isSolvable_of_card_prime_pow {p n : ℕ} (hp : p.Prime) (hcard : Nat.card G = p ^ n) :
    IsSolvable G := by
  have : Fact p.Prime := ⟨hp⟩
  have : 0 < p := hp.pos
  have : Group.IsNilpotent G := IsPGroup.isNilpotent (IsPGroup.of_card hcard)
  infer_instance

/-- Sylow p-group $P$ of finite group $G$ is solvable since it is p-group. -/
instance {p : ℕ} [Fact p.Prime] (P : Sylow p G) : IsSolvable (P : Subgroup G) :=
  isSolvable_of_card_prime_pow (Fact.out : p.Prime) (Sylow.card_eq_multiplicity P)

/-- Group of order $pq$ is solvable. -/
lemma isSolvable_of_card_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hcard : Nat.card G = p * q) :
    IsSolvable G := by
  wlog h : p < q
  . exact this hq hp hpq.symm (by rw [hcard, mul_comm]) (by rw [lt_iff_le_and_ne]; exact ⟨by linarith, hpq.symm⟩)
  have : Fact q.Prime := ⟨hq⟩
  have modq_eq_one := card_sylow_modEq_one q G
  have dvd_index := Sylow.card_dvd_index (default : Sylow q G)
  rw [index_sylow_eq_ord_compl, hcard, factorization_q_pq hp hq hpq, pow_one, Nat.mul_div_cancel _ (by omega),
    Nat.dvd_prime hp] at dvd_index
  rcases dvd_index with h | h
  . have sylow_normal := sylow_normal_of_card_eq_one h default
    have : IsSolvable (G ⧸ ((default : Sylow q G) : Subgroup G)) := by
      apply isSolvable_of_card_prime_pow hp (n := 1)
      rw [card_quot_eq_card_div_card, pow_one, Sylow.card_eq_multiplicity, hcard,
        factorization_q_pq hp hq hpq, pow_one, Nat.mul_div_cancel _ (by omega)]
    exact isSolvable_of_subgroup_of_quot sylow_normal
  . have : 2 ≤ p := Nat.Prime.two_le hp
    rw [h, Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hq.one_lt] at modq_eq_one
    omega
