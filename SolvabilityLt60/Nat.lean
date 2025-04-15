/-
Copyright (c) 2025 Zhang Qinchuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang Qinchuan
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Defs

/-- If $a < n$ and $a$ divides $n$ then $a \leq n/2$. -/
lemma le_div_two_of_lt_of_dvd {a n : ℕ} (hlt : a < n) (hdvd : a ∣ n) : a ≤ n / 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  . exact Nat.zero_le ..
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases hdvd with ⟨k, rfl⟩
  rw [Nat.mul_le_mul_left_iff (by omega)]
  show 1 < k
  rwa [← mul_lt_mul_left ha.bot_lt, mul_one]

/-- If $1 < a$ then $n/a \leq n/2$. -/
lemma div_le_div_two_of_one_lt {a n : ℕ} (one_lt : 1 < a) : n / a ≤ n / 2 := by
  exact Nat.div_le_div_left one_lt (by norm_num)

/-- If prime numbers $p,q$ are not equal then `padicValNat q p = 0`. -/
lemma padicValNat_eq_zero_of_ne_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    padicValNat q p = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  rwa [Nat.prime_dvd_prime_iff_eq hq hp, eq_comm, ← ne_eq]

/-- If prime numbers $p,q$ are not equal then `(p * q).factorization q = 1`. -/
lemma factorization_q_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    (p * q).factorization q = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  rw [Nat.factorization_def _ hq, padicValNat.mul hp.ne_zero hq.ne_zero, padicValNat.self hq.one_lt,
    padicValNat_eq_zero_of_ne_of_prime hp hq h, zero_add]

/-- If prime number $p$ is greater than $2$ then `(2 * p ^ 2).factorization p = 2`. -/
lemma factorization_p_2p2 {p : ℕ} (hp : p.Prime) (hpgt : 2 < p) :
    (2 * p ^ 2).factorization p = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, padicValNat.mul (by norm_num) (by positivity), padicValNat.pow _ hp.ne_zero,
    padicValNat.self hp.one_lt, padicValNat_eq_zero_of_ne_of_prime Nat.prime_two hp hpgt.ne]

/-- If prime numbers $p,q$ are not equal then `(p ^ 2 * q).factorization q = 1`. -/
lemma factorization_q_p2q {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    (p ^ 2 * q).factorization q = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  rw [Nat.factorization_def _ hq, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hq.ne_zero,
    padicValNat.pow _ hp.ne_zero, padicValNat_eq_zero_of_ne_of_prime hp hq h, mul_zero,
    padicValNat.self hq.one_lt]
