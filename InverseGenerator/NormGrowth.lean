/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.CoeffBounds
import InverseGenerator.Rotation
import InverseGenerator.SchurTest

/-!
# Norm growth of the sign multiplier `Δ_n`

The two-sided `ℓ²`-operator-norm estimate

  `n^α / 2 ≤ ‖Δ_n‖ ≤ 2 n^α`,

which is what Theorem 1.1 — `n^α/C ≤ ‖e^{π A_n⁻¹}‖ ≤ n^α` — is read off from,
since `e^{π A_n⁻¹} = e^{-π} Δ_n` exactly.  The explicit constants `1/2` and `2` are
what Theorem 1.1 requires; a `≍_α` statement would not do.

## Implementation notes

**The upper bound comes from the Schur test with `u = v = 1`.**  For a lower-triangular
Toeplitz matrix every row and column `ℓ¹` sum is bounded by `∑_{r<n} |a_r(θ)|`, so
`l2_opNorm_le_of_schur` applies with constant weights.  This is the cheapest possible
use of the Schur test and needs none of the weighted machinery Lemma A.4 requires.

**`Δ_n` is handled directly, not via block-norm lemmas.**  Bounding
`‖fromBlocks 0 B C 0‖` by `max ‖B‖ ‖C‖` would need isometry lemmas for the block
inclusions.  Instead the Schur test is applied to `Δ_n` itself: each of its rows is a
row of `T_n(α)` or of `T_n(-α)`, so one constant dominating both `ℓ¹` sums suffices.

**The lower bound is one explicit test vector.**  Applying `Δ_n` to `x = (0, 1_n)`
turns `‖Δ_n x‖² / ‖x‖²` into `(∑_{i<n} P_i(α)²) / n`, where `P_i(α) = ∑_{r ≤ i} a_r(α)`
is the `i`-th row sum of `T_n(α)`.  Since `P_i(α) ≥ (i+1)^α` termwise
(`rpow_succ_le_coeffProd`), the lower `p`-series bound `rpow_div_le_sum_range_rpow`
gives `n^{2α+1}/(2α+1)` for the numerator, hence `n^α/√(2α+1) ≥ n^α/2`.  No spectral
argument and no Cauchy–Schwarz loss is involved.
-/

namespace InverseGenerator

open Finset Matrix
open scoped Matrix.Norms.L2Operator

/-- `binomCoeff` commutes with the coercion `ℝ → ℂ`. -/
theorem binomCoeff_ofReal (r : ℕ) (θ : ℝ) :
    ((binomCoeff r θ : ℝ) : ℂ) = binomCoeff r ((θ : ℂ)) := by
  rw [binomCoeff, binomCoeff]
  push_cast
  rfl

/-- The norm of a Toeplitz entry, in terms of the real coefficients. -/
theorem norm_toeplitz_apply (θ : ℝ) {n : ℕ} (i j : Fin n) :
    ‖toeplitz n ((θ : ℂ)) i j‖
      = if (j : ℕ) ≤ (i : ℕ) then |binomCoeff ((i : ℕ) - (j : ℕ)) θ| else 0 := by
  rw [toeplitz_apply]
  split_ifs with h
  · rw [← binomCoeff_ofReal, Complex.norm_real, Real.norm_eq_abs]
  · exact norm_zero

/-- Every row `ℓ¹` sum of `T_n(θ)` is bounded by `∑_{r<n} |a_r(θ)|`. -/
theorem toeplitz_row_l1_le (θ : ℝ) {n : ℕ} (i : Fin n) :
    ∑ j : Fin n, ‖toeplitz n ((θ : ℂ)) i j‖ ≤ ∑ r ∈ range n, |binomCoeff r θ| := by
  have hin : (i : ℕ) < n := i.isLt
  set f : ℕ → ℝ := fun j => if j ≤ (i : ℕ) then |binomCoeff ((i : ℕ) - j) θ| else 0 with hf
  have hsub : range ((i : ℕ) + 1) ⊆ range n := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hvanish : ∀ j ∈ range n, j ∉ range ((i : ℕ) + 1) → f j = 0 := by
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    simp only [hf]
    rw [if_neg (by omega)]
  calc ∑ j : Fin n, ‖toeplitz n ((θ : ℂ)) i j‖
      = ∑ j ∈ range n, f j := by
        rw [← Fin.sum_univ_eq_sum_range f n]
        exact Finset.sum_congr rfl fun j _ => norm_toeplitz_apply θ i j
    _ = ∑ j ∈ range ((i : ℕ) + 1), f j := (Finset.sum_subset hsub hvanish).symm
    _ = ∑ j ∈ range ((i : ℕ) + 1), |binomCoeff ((i : ℕ) - j) θ| := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        simp only [hf]
        rw [if_pos (by omega)]
    _ = ∑ j ∈ range ((i : ℕ) + 1), |binomCoeff j θ| := by
        have h := Finset.sum_range_reflect (fun j => |binomCoeff j θ|) ((i : ℕ) + 1)
        simpa using h
    _ ≤ ∑ r ∈ range n, |binomCoeff r θ| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _

/-- Every column `ℓ¹` sum of `T_n(θ)` is bounded by `∑_{r<n} |a_r(θ)|`. -/
theorem toeplitz_col_l1_le (θ : ℝ) {n : ℕ} (j : Fin n) :
    ∑ i : Fin n, ‖toeplitz n ((θ : ℂ)) i j‖ ≤ ∑ r ∈ range n, |binomCoeff r θ| := by
  have hjn : (j : ℕ) < n := j.isLt
  set g : ℕ → ℝ := fun i => if (j : ℕ) ≤ i then |binomCoeff (i - (j : ℕ)) θ| else 0 with hg
  have hsub : Finset.Ico (j : ℕ) n ⊆ range n := fun i hi =>
    Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
  have hvanish : ∀ i ∈ range n, i ∉ Finset.Ico (j : ℕ) n → g i = 0 := by
    intro i hi hinot
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hinot
    rcases hinot with h | h
    · simp only [hg]; rw [if_neg (by omega)]
    · exact absurd hi (Nat.not_lt.mpr h)
  calc ∑ i : Fin n, ‖toeplitz n ((θ : ℂ)) i j‖
      = ∑ i ∈ range n, g i := by
        rw [← Fin.sum_univ_eq_sum_range g n]
        exact Finset.sum_congr rfl fun i _ => norm_toeplitz_apply θ i j
    _ = ∑ i ∈ Finset.Ico (j : ℕ) n, g i := (Finset.sum_subset hsub hvanish).symm
    _ = ∑ r ∈ range (n - (j : ℕ)), |binomCoeff r θ| := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [hg]
        rw [if_pos (by omega), Nat.add_sub_cancel_left]
    _ ≤ ∑ r ∈ range n, |binomCoeff r θ| :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega)
          fun _ _ _ => abs_nonneg _

/-- **Row sums telescope**: `∑_j T_n(θ) i j = a_i(θ+1) = coeffProd θ i`, by the hockey
stick `sum_binomCoeff`.  This is the `1_n` test vector of Lemma A.3's lower bound. -/
theorem toeplitz_row_sum (θ : ℝ) {n : ℕ} (i : Fin n) :
    ∑ j : Fin n, toeplitz n ((θ : ℂ)) i j = ((coeffProd θ (i : ℕ) : ℝ) : ℂ) := by
  have hin : (i : ℕ) < n := i.isLt
  set f : ℕ → ℂ :=
    fun j => if j ≤ (i : ℕ) then binomCoeff ((i : ℕ) - j) ((θ : ℂ)) else 0 with hf
  have hsub : range ((i : ℕ) + 1) ⊆ range n := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hvanish : ∀ j ∈ range n, j ∉ range ((i : ℕ) + 1) → f j = 0 := by
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    simp only [hf]
    rw [if_neg (by omega)]
  calc ∑ j : Fin n, toeplitz n ((θ : ℂ)) i j
      = ∑ j ∈ range n, f j := by
        rw [← Fin.sum_univ_eq_sum_range f n]
        exact Finset.sum_congr rfl fun j _ => toeplitz_apply _ i j
    _ = ∑ j ∈ range ((i : ℕ) + 1), f j := (Finset.sum_subset hsub hvanish).symm
    _ = ∑ j ∈ range ((i : ℕ) + 1), binomCoeff ((i : ℕ) - j) ((θ : ℂ)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        simp only [hf]
        rw [if_pos (by omega)]
    _ = ∑ j ∈ range ((i : ℕ) + 1), binomCoeff j ((θ : ℂ)) := by
        have h := Finset.sum_range_reflect
          (fun j => binomCoeff j ((θ : ℂ))) ((i : ℕ) + 1)
        simpa using h
    _ = binomCoeff (i : ℕ) ((θ : ℂ) + 1) := sum_binomCoeff _ _
    _ = ((coeffProd θ (i : ℕ) : ℝ) : ℂ) := by
        rw [← binomCoeff_add_one_eq_coeffProd, binomCoeff_ofReal]
        push_cast
        ring_nf

/-! ## `‖Δ_n‖` and Lemma A.3

`Δ_n = signMult n α = fromBlocks 0 T(α) T(-α) 0`.  Its rows are the rows of `T_n(α)`
(padded with zeros) or of `T_n(-α)`, so the Schur test with `u = v = 1` applies with
any constant dominating both `ℓ¹` sums.
-/

/-- The `α/2 + α/2` produced by Proposition 2.1, Step 1 is just `α`. -/
theorem signMult_ofReal (n : ℕ) (α : ℝ) :
    signMult n (((α / 2 : ℝ) : ℂ) + ((α / 2 : ℝ) : ℂ)) = signMult n ((α : ℂ)) := by
  congr 1
  push_cast
  ring

theorem toeplitz_neg_ofReal (n : ℕ) (α : ℝ) :
    toeplitz n (-((α : ℝ) : ℂ)) = toeplitz n (((-α : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

/-! ## The two-sided bound `n^α/2 ≤ ‖Δ_±‖ ≤ 2 n^α`

Theorem 1.1 pins the exponential of the inverse generator between `n^α/C` and `n^α`
with `C = 50`, which needs `‖Δ_±‖ ≤ 2n^α` (so that
`‖e^{πA_n⁻¹}‖ = e^{-π}‖Δ_±‖ ≤ 2e^{-π} n^α ≤ n^α`) and `‖Δ_±‖ ≥ n^α/2` (so that
`‖e^{πA_n⁻¹}‖ ≥ e^{-π} n^α/2 ≥ n^α/50`, using `2e^π < 50`).

*Upper bound.*  The Schur test with `u = v = 1` again, but now with the single
constant `2n^α`: each row and column `ℓ¹` sum of `Δ_±` is a row or column sum of
`T_n(α)` (`≤ 2n^α` by `sum_abs_binomCoeff_le_two_rpow`) or of `T_n(-α)` (`≤ 2 ≤ 2n^α`
by `sum_abs_binomCoeff_neg_le_two`).  Taking the *maximum* rather than the sum of the
two — which is what the block structure permits — is exactly what buys the constant.

*Lower bound.*  The test vector `(0, 1_n)`, with no intermediate Cauchy–Schwarz
step: the entries of `Δ_±(0,1_n)` are the row sums
`a_i(α+1) = coeffProd α i ≥ (i+1)^α`, and the lower `p`-series
`rpow_div_le_sum_range_rpow` gives `∑_i (i+1)^{2α} ≥ n^{2α+1}/(2α+1)` directly, hence
`‖Δ_±‖ ≥ n^α/√(2α+1) ≥ n^α/2`.
-/

/-- **Proposition 2.1, sharp upper half**: `‖Δ_±‖ ≤ 2 n^α`. -/
theorem l2_opNorm_signMult_le' {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖signMult n ((α : ℂ))‖ ≤ 2 * (n : ℝ) ^ α := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast hn) hα0
  have hC : (0 : ℝ) ≤ 2 * (n : ℝ) ^ α := by positivity
  have hpos := sum_abs_binomCoeff_le_two_rpow hα0 hα1.le hn
  have hneg : ∑ r ∈ range n, |binomCoeff r (-α)| ≤ 2 * (n : ℝ) ^ α := by
    have h := sum_abs_binomCoeff_neg_le_two hα0 (by linarith) n
    linarith
  refine l2_opNorm_le_of_schur (u := fun _ => (1 : ℝ)) (v := fun _ => (1 : ℝ))
    (fun _ => one_pos) hC ?_ ?_
  · intro s
    simp only [mul_one]
    rw [Fintype.sum_sum_type]
    cases s with
    | inl i =>
      simp only [signMult, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, norm_zero, Finset.sum_const_zero, zero_add]
      exact (toeplitz_row_l1_le α i).trans hpos
    | inr i =>
      simp only [signMult, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, norm_zero, Finset.sum_const_zero, add_zero]
      rw [toeplitz_neg_ofReal]
      exact (toeplitz_row_l1_le (-α) i).trans hneg
  · intro t
    simp only [mul_one]
    rw [Fintype.sum_sum_type]
    cases t with
    | inl j =>
      simp only [signMult, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, norm_zero, Finset.sum_const_zero, zero_add]
      rw [toeplitz_neg_ofReal]
      exact (toeplitz_col_l1_le (-α) j).trans hneg
    | inr j =>
      simp only [signMult, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, norm_zero, Finset.sum_const_zero, add_zero]
      exact (toeplitz_col_l1_le α j).trans hpos

/-- **Proposition 2.1, sharp lower half**: `n^α/2 ≤ ‖Δ_±‖`. -/
theorem le_l2_opNorm_signMult' {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ α / 2 ≤ ‖signMult n ((α : ℂ))‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set x : (Fin n ⊕ Fin n) → ℂ := Sum.elim (fun _ => 0) (fun _ => 1) with hxdef
  -- the action of `Δ_±` on the test vector `(0, 1_n)`
  have hAx : ∀ s : Fin n ⊕ Fin n, (∑ t, signMult n ((α : ℂ)) s t * x t)
      = Sum.elim (fun i : Fin n => ((coeffProd α (i : ℕ) : ℝ) : ℂ))
          (fun _ => (0 : ℂ)) s := by
    intro s
    rw [Fintype.sum_sum_type]
    cases s with
    | inl i =>
      simp only [signMult, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, Finset.sum_const_zero, zero_add, hxdef,
        Sum.elim_inl, Sum.elim_inr, mul_one, mul_zero]
      exact toeplitz_row_sum α i
    | inr i =>
      simp only [signMult, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, Finset.sum_const_zero, add_zero, hxdef,
        Sum.elim_inl, Sum.elim_inr, mul_one, mul_zero]
  have hcpnn : ∀ i : ℕ, (0 : ℝ) ≤ coeffProd α i := fun i =>
    (coeffProd_pos (by linarith) i).le
  have hlhs : ∑ s : Fin n ⊕ Fin n, ‖∑ t, signMult n ((α : ℂ)) s t * x t‖ ^ 2
      = ∑ i : Fin n, (coeffProd α (i : ℕ)) ^ 2 := by
    rw [Fintype.sum_sum_type]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [hAx (Sum.inl i)]
      simp [abs_of_nonneg (hcpnn (i : ℕ))] :
      ∀ i ∈ Finset.univ, ‖∑ t, signMult n ((α : ℂ)) (Sum.inl i) t * x t‖ ^ 2
        = (coeffProd α (i : ℕ)) ^ 2)]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hAx (Sum.inr i)]; simp :
      ∀ i ∈ Finset.univ, ‖∑ t, signMult n ((α : ℂ)) (Sum.inr i) t * x t‖ ^ 2 = 0)]
    simp
  have hrhs : ∑ t : Fin n ⊕ Fin n, ‖x t‖ ^ 2 = (n : ℝ) := by
    rw [Fintype.sum_sum_type]
    simp [hxdef]
  -- the `p`-series lower bound on the row sums, with no Cauchy–Schwarz loss
  have hlow : (n : ℝ) ^ (2 * α + 1) / (2 * α + 1)
      ≤ ∑ i : Fin n, (coeffProd α (i : ℕ)) ^ 2 := by
    have hterm : ∀ i ∈ range n, ((i : ℝ) + 1) ^ (2 * α) ≤ (coeffProd α i) ^ 2 := by
      intro i _
      have h1 : ((i : ℝ) + 1) ^ α ≤ coeffProd α i := rpow_succ_le_coeffProd hα0 hα1 i
      have h2 : (0 : ℝ) ≤ ((i : ℝ) + 1) ^ α := Real.rpow_nonneg (by positivity) _
      have hsq : (((i : ℝ) + 1) ^ α) ^ 2 ≤ (coeffProd α i) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
      refine le_trans (le_of_eq ?_) hsq
      rw [← Real.rpow_natCast (((i : ℝ) + 1) ^ α) 2, ← Real.rpow_mul (by positivity)]
      norm_num
      ring_nf
    have hp := rpow_div_le_sum_range_rpow (s := 2 * α) (by linarith) n
    rw [show 2 * α + 1 = 2 * α + 1 from rfl] at hp
    calc (n : ℝ) ^ (2 * α + 1) / (2 * α + 1)
        ≤ ∑ i ∈ range n, ((i : ℝ) + 1) ^ (2 * α) := hp
      _ ≤ ∑ i ∈ range n, (coeffProd α i) ^ 2 := Finset.sum_le_sum hterm
      _ = ∑ i : Fin n, (coeffProd α (i : ℕ)) ^ 2 :=
          (Fin.sum_univ_eq_sum_range (fun i => (coeffProd α i) ^ 2) n).symm
  -- feed into the operator-norm inequality
  have hop := sqrt_sum_sq_mulVec_le (A := signMult n ((α : ℂ))) x
  rw [hlhs, hrhs] at hop
  have hsqrt_low : Real.sqrt ((n : ℝ) ^ (2 * α + 1) / (2 * α + 1))
      ≤ Real.sqrt (∑ i : Fin n, (coeffProd α (i : ℕ)) ^ 2) := Real.sqrt_le_sqrt hlow
  -- `√(n^{2α+1}/(2α+1)) = n^α √n/√(2α+1) ≥ (n^α/2)·√n`
  have hsplit : (n : ℝ) ^ (2 * α + 1) / (2 * α + 1)
      = ((n : ℝ) ^ α / 2) ^ 2 * (n : ℝ) * (4 / (2 * α + 1)) := by
    rw [Real.rpow_add hnR, Real.rpow_one, div_pow,
      ← Real.rpow_natCast ((n : ℝ) ^ α) 2, ← Real.rpow_mul hnR.le]
    push_cast
    rw [show α * 2 = 2 * α from by ring]
    field_simp
    ring
  have hfac : (1 : ℝ) ≤ 4 / (2 * α + 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hkey : ((n : ℝ) ^ α / 2) * Real.sqrt n
      ≤ Real.sqrt (∑ i : Fin n, (coeffProd α (i : ℕ)) ^ 2) := by
    calc ((n : ℝ) ^ α / 2) * Real.sqrt n
        = Real.sqrt (((n : ℝ) ^ α / 2) ^ 2 * (n : ℝ)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt ((n : ℝ) ^ (2 * α + 1) / (2 * α + 1)) := by
          refine Real.sqrt_le_sqrt ?_
          rw [hsplit]
          nlinarith [mul_nonneg (sq_nonneg ((n : ℝ) ^ α / 2)) hnR.le, hfac]
      _ ≤ Real.sqrt (∑ i : Fin n, (coeffProd α (i : ℕ)) ^ 2) := hsqrt_low
  -- divide by `√n`
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  exact le_of_mul_le_mul_right (hkey.trans hop) hsn

end InverseGenerator
