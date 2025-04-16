/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Finite.Perm

variable {G : Type*} [Group G]

/-- Identity acts trivially. -/
lemma toPermHom_one_eq_one {X : Type*} [MulAction G X] : MulAction.toPerm (1 : G) = (1 : Equiv.Perm X) := by
  unfold MulAction.toPerm; ext; simp

variable [Finite G]

/-- Index of Sylow p-group is $|G|/p^k$. -/
lemma index_sylow_eq_ord_compl {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    P.index = Nat.card G / p ^ (Nat.card G).factorization p := by
  apply Nat.eq_div_of_mul_eq_left
  . exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  . rw [mul_comm]
    convert Subgroup.card_mul_index (P : Subgroup G)
    exact (Sylow.card_eq_multiplicity P).symm

/-- If there is only one Slyow p-group then it is normal. -/
lemma sylow_normal_of_card_eq_one {p : ℕ} [Fact p.Prime] (h : Nat.card (Sylow p G) = 1)
    (P : Sylow p G) : (P : Sylow p G).Normal := by
  rwa [← Subgroup.normalizer_eq_top_iff, ← Subgroup.index_eq_one, ← Sylow.card_eq_index_normalizer]

variable [IsSimpleGroup G]

omit [Finite G] in
/-- Nontrivial proper subgroup of simple group is not normal. -/
lemma not_normal_of_isSimpleGroup_of_card {P : Subgroup G} (card_ne : Nat.card P ≠ 1)
    (card_ne' : Nat.card P ≠ Nat.card G) : ¬P.Normal := by
  intro hnormal
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  . absurd card_ne; rw [hbot, Subgroup.card_bot]
  . absurd card_ne'; rw [htop, Subgroup.card_top]

/-- If $G$ is simple then $|G|$ divides factorial of $|Syl_p(G)|$. -/
lemma card_dvd_factorial_of_isSimpleGroup_of_card {p : ℕ} (hp : p.Prime) {P : Sylow p G}
    (card_ne : Nat.card P ≠ 1) (card_ne' : Nat.card P ≠ Nat.card G) :
    Nat.card G ∣ (Nat.card (Sylow p G)).factorial := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_perm]
  apply Subgroup.card_dvd_of_injective Sylow.mulAction.toPermHom
  rw [injective_iff_map_eq_one']
  intro g
  refine ⟨fun h => ?_, fun h => h ▸ toPermHom_one_eq_one⟩
  have : (MulAction.toPermHom G (Sylow p G)).ker.Normal := inferInstance
  rcases this.eq_bot_or_eq_top with hbot | htop
  . rwa [← Subgroup.mem_bot, ← hbot]
  . absurd not_normal_of_isSimpleGroup_of_card card_ne card_ne'
    rw [← Subgroup.normalizer_eq_top_iff, ← Sylow.stabilizer_eq_normalizer]
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
    change (MulAction.toPerm g) P = (1 : Equiv.Perm (Sylow p G)) P
    congr
    change g ∈ (MulAction.toPermHom G (Sylow p G)).ker
    simp [htop]
