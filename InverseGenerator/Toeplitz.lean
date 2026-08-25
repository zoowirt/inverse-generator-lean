/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.Coefficients
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Fractional lower-triangular Toeplitz matrices

The matrices `T_n(θ) = (I - L_n)^{-θ}` of the paper's Appendix A, defined
directly by their entries
```
T_n(θ) i j = if j ≤ i then a (i - j) θ else 0
```
where `a = binomCoeff` is the fractional binomial coefficient of
`InverseGenerator.Coefficients`.  Since `L_n` is nilpotent, Appendix A is a
finite polynomial identity with no convergence question, so taking the entries as
the *definition* loses nothing.

## Main results

* `toeplitz_mul` : the group law `T_n(θ) * T_n(η) = T_n(θ + η)`, from Lemma A.1.
* `toeplitz_zero` : `T_n(0) = 1`.
* `toeplitz_mul_neg`, `toeplitz_neg_mul` : `T_n(θ) T_n(-θ) = T_n(-θ) T_n(θ) = 1`,
  so `T_n(-θ)` is a two-sided inverse of `T_n(θ)`.

## Implementation notes

The group law is proved entrywise.  On the `j ≤ i` branch the matrix product is
a sum over `k` constrained by `j ≤ k ≤ i`; that support is extracted with
`Finset.sum_subset`, and `Icc j i = Ico j (i+1)` is reindexed by
`Finset.sum_Ico_eq_sum_range` to land exactly on `vandermonde`.

This is preferred over defining `T_n(θ) = ∑ r, a r θ • L_n ^ r` and multiplying
out, which would need a Cauchy-product rearrangement *and* nilpotency bookkeeping
for the `r + s ≥ n` terms.  Entries are also what Lemma A.4 needs downstream, so
this definition is used there directly.
-/

namespace InverseGenerator

open Finset Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The fractional lower-triangular Toeplitz matrix `T_n(θ) = (I - L_n)^{-θ}`,
given by its entries as in Appendix A. -/
noncomputable def toeplitz (n : ℕ) (θ : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if (j : ℕ) ≤ (i : ℕ) then binomCoeff ((i : ℕ) - (j : ℕ)) θ else 0

omit [CharZero K] in
@[simp]
theorem toeplitz_apply {n : ℕ} (θ : K) (i j : Fin n) :
    toeplitz n θ i j = if (j : ℕ) ≤ (i : ℕ) then binomCoeff ((i : ℕ) - (j : ℕ)) θ else 0 :=
  rfl

omit [CharZero K] in
/-- `T_n(θ)` is lower triangular. -/
theorem toeplitz_apply_of_lt {n : ℕ} (θ : K) {i j : Fin n} (h : (i : ℕ) < (j : ℕ)) :
    toeplitz n θ i j = 0 := by
  rw [toeplitz_apply, if_neg (Nat.not_le.mpr h)]

/-- The diagonal of `T_n(θ)` is `1`. -/
@[simp]
theorem toeplitz_apply_self {n : ℕ} (θ : K) (i : Fin n) : toeplitz n θ i i = 1 := by
  simp [toeplitz]

/-- `T_n(0) = 1`: the coefficients `a r 0` vanish for `r ≥ 1`. -/
@[simp]
theorem toeplitz_zero (n : ℕ) : toeplitz n (0 : K) = 1 := by
  ext i j
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · rw [toeplitz_apply_of_lt _ h, Matrix.one_apply_ne]
    exact fun e => absurd (congrArg (Fin.val) e) (Nat.ne_of_lt h)
  · have : i = j := Fin.ext h
    subst this
    simp
  · -- `i > j`, so `i - j ≥ 1` and `a (i-j) 0 = 0`.
    rw [toeplitz_apply, if_pos (Nat.le_of_lt h),
      binomCoeff_eq_zero_of_arg_zero (by omega : 1 ≤ (i : ℕ) - (j : ℕ)),
      Matrix.one_apply_ne (fun e => absurd (congrArg (Fin.val) e).symm (Nat.ne_of_lt h))]

/-- **The group law** of Lemma A.1: `T_n(θ) * T_n(η) = T_n(θ + η)`. -/
theorem toeplitz_mul {n : ℕ} (θ η : K) :
    toeplitz n θ * toeplitz n η = toeplitz n (θ + η) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [toeplitz_apply]
  -- Pass from `Fin n` to `range n`: the summand depends on `k` only via `(k : ℕ)`.
  rw [Fin.sum_univ_eq_sum_range (fun k =>
    (if k ≤ (i : ℕ) then binomCoeff ((i : ℕ) - k) θ else 0)
      * (if (j : ℕ) ≤ k then binomCoeff (k - (j : ℕ)) η else 0)) n]
  by_cases hji : (j : ℕ) ≤ (i : ℕ)
  · rw [if_pos hji]
    -- The support of the summand inside `range n` is `Icc j i`.
    have hsub : Icc (j : ℕ) (i : ℕ) ⊆ range n := fun k hk =>
      mem_range.mpr (lt_of_le_of_lt (mem_Icc.mp hk).2 i.isLt)
    rw [← Finset.sum_subset hsub (by
      intro k _ hk
      rw [mem_Icc, not_and_or, not_le, not_le] at hk
      rcases hk with hk | hk
      · rw [if_neg (by omega : ¬ (j : ℕ) ≤ k), mul_zero]
      · rw [if_neg (by omega : ¬ k ≤ (i : ℕ)), zero_mul])]
    -- On `Icc j i` both guards hold; then `Icc j i = Ico j (i+1)` and reindex `k = j + r`.
    rw [Finset.sum_congr rfl (fun k hk => by
      obtain ⟨h1, h2⟩ := mem_Icc.mp hk
      rw [if_pos h2, if_pos h1]), ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range,
      show (i : ℕ) + 1 - (j : ℕ) = ((i : ℕ) - (j : ℕ)) + 1 from by omega]
    -- Now it is exactly `vandermonde`, up to commuting the factors and `θ + η`.
    calc ∑ r ∈ range (((i : ℕ) - (j : ℕ)) + 1),
            binomCoeff ((i : ℕ) - ((j : ℕ) + r)) θ * binomCoeff ((j : ℕ) + r - (j : ℕ)) η
        = ∑ r ∈ range (((i : ℕ) - (j : ℕ)) + 1),
            binomCoeff r η * binomCoeff (((i : ℕ) - (j : ℕ)) - r) θ := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Nat.add_sub_cancel_left, ← Nat.sub_sub, mul_comm]
      _ = binomCoeff ((i : ℕ) - (j : ℕ)) (η + θ) := vandermonde _ η θ
      _ = binomCoeff ((i : ℕ) - (j : ℕ)) (θ + η) := by rw [add_comm]
  · rw [if_neg hji]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k ≤ (i : ℕ)
    · rw [if_neg (by omega : ¬ (j : ℕ) ≤ k), mul_zero]
    · rw [if_neg hki, zero_mul]

/-- `T_n(θ) * T_n(-θ) = 1`, the second half of Lemma A.1. -/
@[simp]
theorem toeplitz_mul_neg {n : ℕ} (θ : K) : toeplitz n θ * toeplitz n (-θ) = 1 := by
  rw [toeplitz_mul, add_neg_cancel, toeplitz_zero]

theorem toeplitz_neg_mul {n : ℕ} (θ : K) : toeplitz n (-θ) * toeplitz n θ = 1 := by
  rw [toeplitz_mul, neg_add_cancel, toeplitz_zero]

/-! ### The definition really is `(I - L_n)^{-θ}`

`T_n(θ)` is *defined* by its entries, so nothing so far justifies the paper's
notation `(I - L_n)^{-θ}`.  Evaluating at `θ = -1` does: the coefficients
`a r (-1)` are `1, -1, 0, 0, …`, so `T_n(-1)` is literally `I - L_n`.  Combined
with the group law this pins down the whole family, and anchors the definition to
Appendix A rather than merely being consistent with it.
-/

end InverseGenerator
