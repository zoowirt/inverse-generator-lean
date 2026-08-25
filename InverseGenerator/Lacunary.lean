/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The distinguished lacunary tower `(y_k)`

The doubly exponential sequence `y₀ = 2`, `y_{k+1} = y_k² + 1` of §2 of the paper
(there indexed from `y₁ = 2`).  Two properties matter.

*Parity alternates*, `Even (y k) ↔ Even k`.  This is the engine of the identity
`e^{π A_n⁻¹} = -e^{-π} Δ_±` of §2: since `e^{π b_k} = e^{-π} (-1)^{y_k}` and
`(-1)^{y_k} = (-1)^k`,
the exponential of the inverse generator at time `π` is exactly `e^{-π}` times the
*alternating* sign multiplier — no spectral approximation anywhere.

*It is lacunary*, `y_k² ≤ y_{k+1}` and `2^{k+1} ≤ y_k`, which gives the summability
`∑ 1/y_k ≤ 1` of `eq:lacunary-variation`.

## Implementation notes

The parity fact is proved by **induction**, never by `decide` or `norm_num`.  The
tower grows doubly exponentially — `y₁₅` already has 19 728 digits — so evaluating
any `y k` for `k ≥ 6` is not an option: `y₄₀` alone would have some `2·10¹¹`
digits.
-/

namespace InverseGenerator

open Finset

/-- The lacunary tower `y₀ = 2`, `y_{k+1} = y_k² + 1` of §2. -/
def tower : ℕ → ℕ
  | 0 => 2
  | (k + 1) => (tower k) ^ 2 + 1

@[simp] theorem tower_zero : tower 0 = 2 := rfl

@[simp] theorem tower_succ (k : ℕ) : tower (k + 1) = (tower k) ^ 2 + 1 := rfl

theorem two_le_tower (k : ℕ) : 2 ≤ tower k := by
  induction k with
  | zero => simp
  | succ k ih => rw [tower_succ]; nlinarith

theorem tower_pos (k : ℕ) : 0 < tower k := lt_of_lt_of_le two_pos (two_le_tower k)

/-- Lacunarity: `y_k² ≤ y_{k+1}`, the hypothesis of Lemma 2.2. -/
theorem tower_sq_le_tower_succ (k : ℕ) : (tower k) ^ 2 ≤ tower (k + 1) := by
  rw [tower_succ]; omega

/-- `2 y_k ≤ y_{k+1}`, since `y_k² + 1 - 2 y_k = (y_k - 1)² ≥ 0`. -/
theorem two_mul_tower_le_tower_succ (k : ℕ) : 2 * tower k ≤ tower (k + 1) := by
  have h := two_le_tower k
  rw [tower_succ]; nlinarith

/-- `2^{k+1} ≤ y_k`: the tower dominates the geometric sequence, which is what
makes `∑ 1/y_k` summable. -/
theorem two_pow_le_tower (k : ℕ) : 2 ^ (k + 1) ≤ tower k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
      _ ≤ 2 * tower k := by omega
      _ ≤ tower (k + 1) := two_mul_tower_le_tower_succ k

/-- Double-exponential lower bound `2^{2^k} ≤ tower k` (paper: `2^{2^{k-1}} ≤ y_k`,
in the 1-based indexing `y_k = tower (k-1)`). -/
theorem two_pow_two_pow_le_tower (k : ℕ) : 2 ^ 2 ^ k ≤ tower k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [tower_succ, pow_succ, pow_mul]
    have h := Nat.pow_le_pow_left ih 2
    omega

/-- Double-exponential upper bound `tower k ≤ 2^{2^{k+1} - 1}` (paper:
`y_k ≤ 2^{2^k - 1}`). -/
theorem tower_le_two_pow_two_pow (k : ℕ) : tower k ≤ 2 ^ (2 ^ (k + 1) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [tower_succ]
    change tower k ^ 2 + 1 ≤ 2 ^ (2 ^ (k + 2) - 1)
    have h1 : tower k ^ 2 ≤ (2 ^ (2 ^ (k + 1) - 1)) ^ 2 := Nat.pow_le_pow_left ih 2
    have hone : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have h2 : (2 ^ (2 ^ (k + 1) - 1)) ^ 2 = 2 ^ (2 ^ (k + 2) - 2) := by
      rw [← pow_mul]
      congr 1
      have hp : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
      omega
    have h3 : 2 ^ (2 ^ (k + 2) - 1) = 2 ^ (2 ^ (k + 2) - 2) * 2 := by
      rw [← pow_succ]
      congr 1
      have hone2 : 2 ≤ 2 ^ (k + 2) := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 1 ≤ 2 ^ (2 ^ (k + 2) - 2) := Nat.one_le_two_pow
    omega

/-- **Parity alternates**: `Even (y k) ↔ Even k`.  Equivalently `(-1)^{y_k} = (-1)^k`,
which is the parity alternation used in §2. -/
theorem tower_even_iff (k : ℕ) : Even (tower k) ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [tower_succ, Nat.even_add_one, Nat.even_pow, Nat.even_add_one]
    constructor
    · intro h
      exact fun hk => h ⟨ih.mpr hk, two_ne_zero⟩
    · intro h hp
      exact h (ih.mp hp.1)

/-- The sign form of the parity alternation: `(-1)^{y_k} = (-1)^k`. -/
theorem neg_one_pow_tower {M : Type*} [Monoid M] [HasDistribNeg M] (k : ℕ) :
    (-1 : M) ^ tower k = (-1) ^ k := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [((tower_even_iff k).mpr hk).neg_one_pow, hk.neg_one_pow]
  · have hodd : Odd (tower k) :=
      Nat.not_even_iff_odd.mp fun h => (Nat.not_even_iff_odd.mpr hk) ((tower_even_iff k).mp h)
    rw [hodd.neg_one_pow, hk.neg_one_pow]

/-- Auxiliary geometric sum: `∑_{k<N} (1/2)^{k+1} = 1 - (1/2)^N`. -/
theorem sum_half_pow_succ (N : ℕ) :
    ∑ k ∈ range N, (1 / 2 : ℝ) ^ (k + 1) = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; ring

/-- `eq:lacunary-variation`: `∑_{k<N} 1/y_k ≤ 1`, uniformly in `N`.

This is what bounds the total variation of the spectrum `(λ_k)`
(`eq:lacunary-variation`), and hence gives `‖A_n‖ ≤ 1 + 5α/(1-α)`. -/
theorem sum_inv_tower_le_one (N : ℕ) : ∑ k ∈ range N, (1 : ℝ) / tower k ≤ 1 := by
  have hterm : ∀ k ∈ range N, (1 : ℝ) / tower k ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    intro k _
    have h1 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    have h2 : (2 : ℝ) ^ (k + 1) ≤ (tower k : ℝ) := by exact_mod_cast two_pow_le_tower k
    rw [show (1 / 2 : ℝ) ^ (k + 1) = 1 / 2 ^ (k + 1) from by rw [div_pow, one_pow]]
    exact one_div_le_one_div_of_le h1 h2
  calc ∑ k ∈ range N, (1 : ℝ) / tower k
      ≤ ∑ k ∈ range N, (1 / 2 : ℝ) ^ (k + 1) := sum_le_sum hterm
    _ = 1 - (1 / 2 : ℝ) ^ N := sum_half_pow_succ N
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
        linarith

end InverseGenerator
