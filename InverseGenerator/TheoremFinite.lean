/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.FlowVariation
import InverseGenerator.NormGrowth
import InverseGenerator.RotatedPrefix
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Theorem 1.1 (`thm:intro-finite`)

The finite-dimensional theorem, with the paper's explicit absolute constant
`C = 50`.  For `α ∈ (0,1)` and `ω_n = 1/y_{2n+1}`:

* `A_n` is invertible and diagonalizable;
* `‖A_n‖ ≤ 1 + Cα/(1-α)`;
* `‖A_n⁻¹‖ ≤ ω_n^{-1/2}(1 + Cα/(1-α))`;
* `‖e^{tA_n}‖ ≤ (1 + Cα/(1-α)) e^{-ω_n t}` — exponential *decay*, `t ≥ 0`;
* `n^α/C ≤ ‖e^{π A_n⁻¹}‖ ≤ n^α`;
* `n ≤ log log (ω_n⁻¹) ≤ 2n`, and `(ω_n)` is decreasing in `(0,1)`;
* `σ(A_n) ⊆ {Re z ≤ -ω_n, |z| ≥ ω_n^{1/2}}` and
  `σ(A_n⁻¹) ⊆ {Re z = -1, |z| ≤ ω_n^{-1/2}}`.

## Indexing

The paper's `y_k` (`y_1 = 2`) is the repo's `tower (k-1)` (`tower 0 = 2`), so the
paper's `λ_1, …, λ_{2n}` are `towerSpec 0, …, towerSpec (2n-1)` — exactly the values
`blockGen` assigns through `zIndex` — and

    ω_n = 1/y_{2n+1} = (tower (2n))⁻¹ .

## Where `C = 50` comes from

The multiplier bound (`l2_opNorm_multiplier_le`) is
`‖Δ_ξ‖ ≤ max|ξ| + (5α/(1-α)) · Var(ξ)`.  With `ξ_k = e^{t(λ_k + ω_n)}` the variation
is at most `10` (`shifted_flow_variation_le_ten`), giving `1 + 50α/(1-α)`; every other
estimate in the theorem is bounded by that same constant.  The two halves of
`n^α/C ≤ ‖e^{π A_n⁻¹}‖ ≤ n^α` need `2e^{-π} ≤ 1` and `2e^{π} ≤ 50`, i.e.
`e^π ≤ 25`.
-/

namespace InverseGenerator

open Finset Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

/-! ## The decay rate `ω_n` -/

/-- `ω_n = 1/y_{2n+1} = (tower (2n))⁻¹`, the exponential decay rate of `e^{tA_n}`. -/
noncomputable def omegaSeq (n : ℕ) : ℝ := ((tower (2 * n) : ℝ))⁻¹

theorem tower_two_mul_pos (n : ℕ) : (0 : ℝ) < (tower (2 * n) : ℝ) := by
  exact_mod_cast tower_pos (2 * n)

theorem omegaSeq_pos (n : ℕ) : 0 < omegaSeq n := by
  rw [omegaSeq]
  exact inv_pos.mpr (tower_two_mul_pos n)

theorem omegaSeq_lt_one (n : ℕ) : omegaSeq n < 1 := by
  rw [omegaSeq, inv_lt_one_iff₀]
  right
  have h : (2 : ℝ) ≤ (tower (2 * n) : ℝ) := by exact_mod_cast two_le_tower (2 * n)
  linarith

/-- `(ω_n)` is decreasing. -/
theorem omegaSeq_antitone (n : ℕ) : omegaSeq (n + 1) ≤ omegaSeq n := by
  rw [omegaSeq, omegaSeq, inv_eq_one_div, inv_eq_one_div]
  refine one_div_le_one_div_of_le (tower_two_mul_pos n) ?_
  exact_mod_cast tower_le_tower (by omega)

theorem omegaSeq_inv (n : ℕ) : (omegaSeq n)⁻¹ = (tower (2 * n) : ℝ) := by
  rw [omegaSeq, inv_inv]

/-- `ω_n^{-1/2} = √(y_{2n+1})`. -/
theorem one_div_sqrt_omegaSeq (n : ℕ) :
    1 / Real.sqrt (omegaSeq n) = Real.sqrt (tower (2 * n)) := by
  rw [omegaSeq, Real.sqrt_inv, one_div, inv_inv]

/-! ## Diagonalizability and the spectrum -/

/-- `A_n` is diagonalizable, with the explicit diagonalizing matrix `𝒱_n`. -/
theorem blockGen_diagonalizable (n : ℕ) (α : ℝ) :
    ∃ (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (d : (Fin n ⊕ Fin n) → ℂ),
      IsUnit W ∧ blockGen n α = W * Matrix.diagonal d * W⁻¹ :=
  ⟨blockSynth n α, fun s => towerSpec (zIndex s), blockSynth_isUnit n α, rfl⟩

/-- The spectrum of `A_n` is exactly `{λ_1, …, λ_{2n}}`. -/
theorem spectrum_blockGen (n : ℕ) (α : ℝ) :
    spectrum ℂ (blockGen n α)
      = Set.range (fun s : Fin n ⊕ Fin n => towerSpec (zIndex s)) := by
  obtain ⟨u, hu⟩ := blockSynth_isUnit n α
  have h : blockGen n α = (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) * blockDiag n
      * ((u⁻¹ : (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ˣ) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    rw [Matrix.coe_units_inv, hu, blockGen]
  rw [h, spectrum.units_conjugate, blockDiag, _root_.spectrum_diagonal]

/-- The spectrum of `A_n⁻¹` is exactly `{μ_1, …, μ_{2n}}`, on the line `Re z = -1`. -/
theorem spectrum_blockGen_inv (n : ℕ) (α : ℝ) :
    spectrum ℂ ((blockGen n α)⁻¹)
      = Set.range (fun s : Fin n ⊕ Fin n => towerPoint (zIndex s)) := by
  obtain ⟨u, hu⟩ := blockSynth_isUnit n α
  have h : (blockGen n α)⁻¹ = (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
      * (blockDiag n)⁻¹ * ((u⁻¹ : (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ˣ) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    rw [Matrix.coe_units_inv, hu, blockGen_inv]
  rw [h, spectrum.units_conjugate, blockDiag_inv, _root_.spectrum_diagonal]

/-- Every spectral point of `A_n` satisfies `Re z ≤ -ω_n` and `|z| ≥ ω_n^{1/2}`. -/
theorem spectrum_blockGen_mem {n : ℕ} (α : ℝ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (blockGen n α)) :
    z.re ≤ -omegaSeq n ∧ Real.sqrt (omegaSeq n) ≤ ‖z‖ := by
  rw [spectrum_blockGen] at hz
  obtain ⟨s, rfl⟩ := hz
  have hlt : zIndex s + 1 ≤ 2 * n := by
    have := zIndex_lt s
    omega
  have hmono : (tower (zIndex s + 1) : ℝ) ≤ (tower (2 * n) : ℝ) := by
    exact_mod_cast tower_le_tower hlt
  have hpos1 : (0 : ℝ) < (tower (zIndex s + 1) : ℝ) := by
    exact_mod_cast tower_pos (zIndex s + 1)
  refine ⟨?_, ?_⟩
  · -- `Re λ = -1/y_{j+2} ≤ -ω_n`
    rw [towerSpec_re, omegaSeq, neg_le_neg_iff, inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos1 hmono
  · -- `|λ| = 1/√y_{j+2} ≥ √ω_n`
    have hnorm : ‖towerSpec (zIndex s)‖ = 1 / Real.sqrt (tower (zIndex s + 1)) := by
      rw [towerSpec, norm_inv, inv_eq_one_div,
        show ‖towerPoint (zIndex s)‖ = Real.sqrt (tower (zIndex s + 1)) from by
          rw [← Real.sqrt_sq (norm_nonneg _), norm_towerPoint_sq]]
    rw [hnorm, omegaSeq, Real.sqrt_inv, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos1) (Real.sqrt_le_sqrt hmono)

/-- Every spectral point of `A_n⁻¹` lies on `Re z = -1` with `|z| ≤ ω_n^{-1/2}`. -/
theorem spectrum_blockGen_inv_mem {n : ℕ} (α : ℝ) {z : ℂ}
    (hz : z ∈ spectrum ℂ ((blockGen n α)⁻¹)) :
    z.re = -1 ∧ ‖z‖ ≤ 1 / Real.sqrt (omegaSeq n) := by
  rw [spectrum_blockGen_inv] at hz
  obtain ⟨s, rfl⟩ := hz
  have hlt : zIndex s + 1 ≤ 2 * n := by
    have := zIndex_lt s
    omega
  refine ⟨towerPoint_re _, ?_⟩
  rw [one_div_sqrt_omegaSeq]
  exact norm_towerPoint_le_sqrt hlt

/-! ## The four norm estimates

All four come from the single multiplier bound
`‖Δ_ξ‖ ≤ max|ξ| + (5α/(1-α))·Var(ξ)` (`l2_opNorm_multiplier_le`), applied with
`ξ = λ`, `ξ = μ`, and `ξ = e^{t(λ + ω_n)}` respectively.
-/

/-- `A_n` as a multiplier: `A_n = ∑_k λ_k ℰ_{n,k}` (§2). -/
theorem blockGen_eq_sum (n : ℕ) (α : ℝ) :
    blockGen n α = ∑ k ∈ range (2 * n), towerSpec k • coordProjZ n α k := by
  rw [blockGen, blockDiag]
  exact conj_diagonal_zIndex_eq_sum n α towerSpec

/-- The flow as a multiplier: `e^{tA_n} = ∑_k e^{tλ_k} ℰ_{n,k}`. -/
theorem exp_smul_blockGen (n : ℕ) (α : ℝ) (t : ℝ) :
    exp ((t : ℂ) • blockGen n α)
      = ∑ k ∈ range (2 * n),
          Complex.exp ((t : ℂ) * towerSpec k) • coordProjZ n α k := by
  have hW := blockSynth_isUnit n α
  have hsmul : (t : ℂ) • blockGen n α
      = blockSynth n α * ((t : ℂ) • blockDiag n) * (blockSynth n α)⁻¹ := by
    rw [blockGen, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsmul, Matrix.exp_conj _ _ hW, blockDiag, ← Matrix.diagonal_smul,
    Matrix.exp_diagonal]
  have hdiag : (exp ((t : ℂ) • fun s : Fin n ⊕ Fin n => towerSpec (zIndex s)))
      = fun s : Fin n ⊕ Fin n => Complex.exp ((t : ℂ) * towerSpec (zIndex s)) := by
    funext s
    rw [Pi.exp_def]
    simp only [Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  rw [hdiag]
  exact conj_diagonal_zIndex_eq_sum n α fun k => Complex.exp ((t : ℂ) * towerSpec k)

/-- `A_n⁻¹` as a multiplier: `A_n⁻¹ = ∑_k μ_k ℰ_{n,k}`. -/
theorem blockGen_inv_eq_sum (n : ℕ) (α : ℝ) :
    (blockGen n α)⁻¹ = ∑ k ∈ range (2 * n), towerPoint k • coordProjZ n α k := by
  rw [blockGen_inv, blockDiag_inv]
  exact conj_diagonal_zIndex_eq_sum n α towerPoint

/-- **`‖A_n‖ ≤ 1 + 5α/(1-α)`**: the symbol `λ` has sup at most `1` and total
variation at most `1`. -/
theorem l2_opNorm_blockGen_le_v2 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    ‖blockGen n α‖ ≤ 1 + 5 * α / (1 - α) := by
  have hs : (0 : ℝ) < 1 - α := by linarith
  have hK : (0 : ℝ) ≤ 5 * α / (1 - α) := by positivity
  rw [blockGen_eq_sum]
  have hbd : ∀ s : Fin n ⊕ Fin n, ‖towerSpec (zIndex s)‖ ≤ 1 := by
    intro s
    refine (norm_towerSpec_le _).trans ?_
    have h2 : (2 : ℝ) ≤ (tower (zIndex s) : ℝ) := by exact_mod_cast two_le_tower _
    rw [div_le_one (by linarith)]
    linarith
  have h := l2_opNorm_multiplier_le hα0 hα1 n towerSpec zero_le_one hbd
  have hvar := sum_norm_towerSpec_sub_le_one (2 * n - 1)
  nlinarith [h, hvar, hK]

/-- **`‖A_n⁻¹‖ ≤ ω_n^{-1/2}(1 + 5α/(1-α))`**: the symbol `μ` has sup and total
variation both at most `√y_{2n+1} = ω_n^{-1/2}` (the variation telescopes to
`y_{2n} - y_1 ≤ y_{2n} ≤ √y_{2n+1}`). -/
theorem l2_opNorm_blockGen_inv_le_v2 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖(blockGen n α)⁻¹‖ ≤ Real.sqrt (tower (2 * n)) * (1 + 5 * α / (1 - α)) := by
  have hs : (0 : ℝ) < 1 - α := by linarith
  have hK : (0 : ℝ) ≤ 5 * α / (1 - α) := by positivity
  have hBnn : (0 : ℝ) ≤ Real.sqrt (tower (2 * n)) := Real.sqrt_nonneg _
  rw [blockGen_inv_eq_sum]
  have hbd : ∀ s : Fin n ⊕ Fin n,
      ‖towerPoint (zIndex s)‖ ≤ Real.sqrt (tower (2 * n)) := by
    intro s
    refine norm_towerPoint_le_sqrt ?_
    have := zIndex_lt s
    omega
  have h := l2_opNorm_multiplier_le hα0 hα1 n towerPoint hBnn hbd
  have hvar : ∑ k ∈ range (2 * n - 1), ‖towerPoint (k + 1) - towerPoint k‖
      ≤ Real.sqrt (tower (2 * n)) := by
    refine (sum_norm_towerPoint_sub_le (2 * n - 1)).trans ?_
    have hsq : ((tower (2 * n - 1) : ℝ)) ^ 2 ≤ (tower (2 * n) : ℝ) := by
      have h := tower_sq_le_tower_succ (2 * n - 1)
      rw [show 2 * n - 1 + 1 = 2 * n from by omega] at h
      exact_mod_cast h
    calc (tower (2 * n - 1) : ℝ)
        = Real.sqrt (((tower (2 * n - 1) : ℝ)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (tower (2 * n)) := Real.sqrt_le_sqrt hsq
  nlinarith [h, hvar, hK, hBnn]

/-- **`‖e^{tA_n}‖ ≤ (1 + 50α/(1-α)) e^{-ω_n t}`** — the exponentially decaying flow
bound.  This is the one place where the factor `10` of
`shifted_flow_variation_le_ten` enters, and hence the source of `C = 50`. -/
theorem l2_opNorm_exp_blockGen_le_v2 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ}
    (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp ((t : ℂ) • blockGen n α)‖
      ≤ (1 + 50 * α / (1 - α)) * Real.exp (-(omegaSeq n * t)) := by
  have hs : (0 : ℝ) < 1 - α := by linarith
  have hK : (0 : ℝ) ≤ 5 * α / (1 - α) := by positivity
  set ω : ℝ := omegaSeq n with hω
  have hMn : 2 * n - 1 + 1 = 2 * n := by omega
  have hωval : ω = ((tower (2 * n - 1 + 1) : ℝ))⁻¹ := by rw [hω, omegaSeq, hMn]
  set f : ℕ → ℂ := fun k => Complex.exp ((t : ℂ) * (towerSpec k + ((ω : ℝ) : ℂ)))
    with hf
  -- the shifted symbol factors out the scalar `e^{tω}`
  have hfac : ∀ k, f k = Complex.exp ((t : ℂ) * ((ω : ℝ) : ℂ))
      * Complex.exp ((t : ℂ) * towerSpec k) := by
    intro k
    rw [hf, ← Complex.exp_add,
      show (t : ℂ) * ((ω : ℝ) : ℂ) + (t : ℂ) * towerSpec k
        = (t : ℂ) * (towerSpec k + ((ω : ℝ) : ℂ)) from by ring]
  have hsum : ∑ k ∈ range (2 * n), f k • coordProjZ n α k
      = Complex.exp ((t : ℂ) * ((ω : ℝ) : ℂ)) • exp ((t : ℂ) • blockGen n α) := by
    rw [exp_smul_blockGen, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfac k, smul_smul]
  -- the symbol is a contraction: `Re λ_k + ω ≤ 0`
  have hbd : ∀ s : Fin n ⊕ Fin n, ‖f (zIndex s)‖ ≤ 1 := by
    intro s
    have hlt : zIndex s + 1 ≤ 2 * n := by
      have := zIndex_lt s
      omega
    have hmono : (tower (zIndex s + 1) : ℝ) ≤ (tower (2 * n) : ℝ) := by
      exact_mod_cast tower_le_tower hlt
    have hpos1 : (0 : ℝ) < (tower (zIndex s + 1) : ℝ) := by
      exact_mod_cast tower_pos (zIndex s + 1)
    have hre : ((t : ℂ) * (towerSpec (zIndex s) + ((ω : ℝ) : ℂ))).re
        = t * (-(1 / (tower (zIndex s + 1) : ℝ)) + ω) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.add_re, Complex.ofReal_re, towerSpec_re]
    rw [hf, Complex.norm_exp, hre]
    refine Real.exp_le_one_iff.mpr ?_
    have hωle : ω ≤ 1 / (tower (zIndex s + 1) : ℝ) := by
      rw [hω, omegaSeq, inv_eq_one_div]
      exact one_div_le_one_div_of_le hpos1 hmono
    have hneg : -(1 / (tower (zIndex s + 1) : ℝ)) + ω ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos ht hneg
  -- the shifted variation is at most `10`
  have hvar : ∑ k ∈ range (2 * n - 1), ‖f (k + 1) - f k‖ ≤ 10 := by
    have h := shifted_flow_variation_le_ten ht (2 * n - 1)
    rw [hf]
    simpa [hωval] using h
  have hmul := l2_opNorm_multiplier_le hα0 hα1 n f zero_le_one hbd
  rw [hsum, norm_smul] at hmul
  -- `‖e^{tω}‖ = e^{tω}` (real argument)
  have hnorm : ‖Complex.exp ((t : ℂ) * ((ω : ℝ) : ℂ))‖ = Real.exp (t * ω) := by
    rw [← Complex.ofReal_mul, Complex.norm_exp, Complex.ofReal_re]
  rw [hnorm] at hmul
  have hkey : Real.exp (t * ω) * ‖exp ((t : ℂ) • blockGen n α)‖ ≤ 1 + 50 * α / (1 - α) := by
    have hstep := mul_le_mul_of_nonneg_left hvar hK
    have heq : 5 * α / (1 - α) * 10 = 50 * α / (1 - α) := by ring
    linarith [hmul, hstep, heq]
  -- divide by `e^{tω}`
  have hepos : (0 : ℝ) < Real.exp (t * ω) := Real.exp_pos _
  refine le_of_mul_le_mul_left ?_ hepos
  calc Real.exp (t * ω) * ‖exp ((t : ℂ) • blockGen n α)‖
      ≤ 1 + 50 * α / (1 - α) := hkey
    _ = Real.exp (t * ω) * ((1 + 50 * α / (1 - α)) * Real.exp (-(ω * t))) := by
        rw [show Real.exp (t * ω) * ((1 + 50 * α / (1 - α)) * Real.exp (-(ω * t)))
            = (1 + 50 * α / (1 - α)) * (Real.exp (t * ω) * Real.exp (-(ω * t)))
            from by ring, ← Real.exp_add,
          show t * ω + -(ω * t) = 0 from by ring, Real.exp_zero, mul_one]

/-! ## Theorem 1.1 with the sharp constants `1/C` and `1` -/

/-- `‖e^{-π}‖ = e^{-π}` — the scalar in front of `Δ_n` in §2. -/
theorem norm_cexp_neg_pi : ‖Complex.exp (-(Real.pi : ℂ))‖ = Real.exp (-Real.pi) := by
  rw [Complex.norm_exp]
  norm_num

/-- **`‖e^{π A_n⁻¹}‖ ≤ n^α`**: from `‖Δ_±‖ ≤ 2n^α` and `2e^{-π} ≤ 1`. -/
theorem norm_exp_pi_blockGen_inv_le_v2 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖exp ((Real.pi : ℂ) • (blockGen n α)⁻¹)‖ ≤ (n : ℝ) ^ α := by
  rw [exp_pi_blockGen_inv, signMult_ofReal, norm_smul, norm_cexp_neg_pi]
  have h := l2_opNorm_signMult_le' hα0.le hα1 hn
  have hnα : (0 : ℝ) ≤ (n : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg n) α
  have hπ := two_le_exp_pi
  have hepos : (0 : ℝ) < Real.exp Real.pi := Real.exp_pos _
  have hinv : Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
  have hhalf : 2 * Real.exp (-Real.pi) ≤ 1 := by
    rw [hinv, mul_inv_le_iff₀ hepos, one_mul]
    linarith
  calc Real.exp (-Real.pi) * ‖signMult n ((α : ℂ))‖
      ≤ Real.exp (-Real.pi) * (2 * (n : ℝ) ^ α) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = (2 * Real.exp (-Real.pi)) * (n : ℝ) ^ α := by ring
    _ ≤ 1 * (n : ℝ) ^ α := mul_le_mul_of_nonneg_right hhalf hnα
    _ = (n : ℝ) ^ α := one_mul _

/-- **`n^α/50 ≤ ‖e^{π A_n⁻¹}‖`**: from `‖Δ_±‖ ≥ n^α/2` and `2e^π ≤ 50`, i.e.
`e^π ≤ 25`. -/
theorem le_norm_exp_pi_blockGen_inv_v2 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ}
    (hn : 1 ≤ n) :
    1 / 50 * (n : ℝ) ^ α ≤ ‖exp ((Real.pi : ℂ) • (blockGen n α)⁻¹)‖ := by
  rw [exp_pi_blockGen_inv, signMult_ofReal, norm_smul, norm_cexp_neg_pi]
  have h := le_l2_opNorm_signMult' hα0.le hα1.le hn
  have hnα : (0 : ℝ) ≤ (n : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg n) α
  have hepos : (0 : ℝ) < Real.exp Real.pi := Real.exp_pos _
  have hinv : Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
  have h25 := exp_pi_le_25
  have hfac : 1 / 50 ≤ Real.exp (-Real.pi) * (1 / 2) := by
    rw [hinv]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 50)] at *
    have hstep : (1 : ℝ) / 25 ≤ (Real.exp Real.pi)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hepos]
      linarith
    linarith
  calc 1 / 50 * (n : ℝ) ^ α
      ≤ (Real.exp (-Real.pi) * (1 / 2)) * (n : ℝ) ^ α :=
        mul_le_mul_of_nonneg_right hfac hnα
    _ = Real.exp (-Real.pi) * ((n : ℝ) ^ α / 2) := by ring
    _ ≤ Real.exp (-Real.pi) * ‖signMult n ((α : ℂ))‖ :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-! ## The doubly exponential rate: `n ≤ log log (ω_n⁻¹) ≤ 2n` -/

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- `2 log 2 + log log 2 ≥ 1`, i.e. `log (4 log 2) ≥ 1`, i.e. `4 log 2 ≥ e`.
This is the *tight* inequality behind `n ≤ log log (ω_n⁻¹)` at `n = 1`. -/
theorem one_le_two_mul_log_two_add : 1 ≤ 2 * Real.log 2 + Real.log (Real.log 2) := by
  have h4 : Real.log (4 * Real.log 2) = 2 * Real.log 2 + Real.log (Real.log 2) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt log_two_pos)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) from by norm_num, Real.log_pow]
    push_cast
    ring
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (4 * Real.log 2) :=
        Real.log_le_log (Real.exp_pos 1) exp_one_le_four_mul_log_two
    _ = 2 * Real.log 2 + Real.log (Real.log 2) := h4

/-- `log log 2 ≤ -1/4`, from `log 2 ≤ 3/4` and `log x ≤ x - 1`. -/
theorem log_log_two_le : Real.log (Real.log 2) ≤ -(1 / 4) := by
  have hlt : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have h1 : Real.log (Real.log 2) ≤ Real.log (3 / 4) := Real.log_le_log log_two_pos hlt
  have h2 : Real.log (3 / 4 : ℝ) ≤ -(1 / 4) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    linarith
  linarith

theorem log_tower_pos (n : ℕ) : (0 : ℝ) < Real.log (tower (2 * n)) := by
  refine Real.log_pos ?_
  have h : (2 : ℝ) ≤ (tower (2 * n) : ℝ) := by exact_mod_cast two_le_tower (2 * n)
  linarith

/-- **`n ≤ log log (ω_n⁻¹)`** — the lower half of the doubly exponential rate. -/
theorem le_log_log_omegaSeq_inv {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ Real.log (Real.log ((omegaSeq n)⁻¹)) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [omegaSeq_inv]
  -- `log y_{2n+1} ≥ 2^{2n} log 2`
  have hlow : (2 : ℝ) ^ (2 * n) * Real.log 2 ≤ Real.log (tower (2 * n)) := by
    have hle : ((2 : ℝ) ^ (2 ^ (2 * n)) : ℝ) ≤ (tower (2 * n) : ℝ) := by
      have h := two_pow_two_pow_le_tower (2 * n)
      exact_mod_cast h
    have hmono := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at hmono
    refine le_trans (le_of_eq ?_) hmono
    push_cast
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * n) * Real.log 2 := by positivity
  -- take logs again
  have hstep : Real.log ((2 : ℝ) ^ (2 * n) * Real.log 2)
      ≤ Real.log (Real.log (tower (2 * n))) := Real.log_le_log hpos hlow
  have hval : Real.log ((2 : ℝ) ^ (2 * n) * Real.log 2)
      = 2 * (n : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
    rw [Real.log_mul (by positivity) (ne_of_gt log_two_pos), Real.log_pow]
    push_cast
    ring
  rw [hval] at hstep
  -- `2n log 2 + log log 2 ≥ n` for `n ≥ 1`, tight at `n = 1`
  have hL := one_le_two_mul_log_two_add
  have h2 : (1 : ℝ) < 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [hstep, hL, h2, hnR]

/-- **`log log (ω_n⁻¹) ≤ 2n`** — the upper half. -/
theorem log_log_omegaSeq_inv_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Real.log ((omegaSeq n)⁻¹)) ≤ 2 * n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [omegaSeq_inv]
  -- `log y_{2n+1} ≤ 2^{2n+1} log 2`
  have hup : Real.log (tower (2 * n)) ≤ (2 : ℝ) ^ (2 * n + 1) * Real.log 2 := by
    have hle : ((tower (2 * n) : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (2 ^ (2 * n + 1)) : ℝ) := by
      have h := tower_le_two_pow_two_pow (2 * n)
      have h2 : (tower (2 * n) : ℕ) ≤ 2 ^ (2 ^ (2 * n + 1)) := by
        exact h.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
      exact_mod_cast h2
    have hmono := Real.log_le_log (tower_two_mul_pos n) hle
    rw [Real.log_pow] at hmono
    refine hmono.trans (le_of_eq ?_)
    push_cast
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * n + 1) * Real.log 2 := by positivity
  have hstep : Real.log (Real.log (tower (2 * n)))
      ≤ Real.log ((2 : ℝ) ^ (2 * n + 1) * Real.log 2) :=
    Real.log_le_log (log_tower_pos n) hup
  have hval : Real.log ((2 : ℝ) ^ (2 * n + 1) * Real.log 2)
      = (2 * (n : ℝ) + 1) * Real.log 2 + Real.log (Real.log 2) := by
    rw [Real.log_mul (by positivity) (ne_of_gt log_two_pos), Real.log_pow]
    push_cast
    ring
  rw [hval] at hstep
  -- `(2n+1) log 2 + log log 2 ≤ 2n`, using `log 2 < 0.694` and `log log 2 ≤ -1/4`
  have hll := log_log_two_le
  have hL2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  nlinarith [hstep, hll, hL2, hnR,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ 1 - Real.log 2)]

/-! ## The statement, and its proof -/

/-- **Theorem 1.1 of arXiv:2608.06272v2** (`thm:intro-finite`), *statement only*.

For `α ∈ (0,1)`, with `A_n = blockGen n α ∈ M_{2n}(ℂ)`, `ω_n = omegaSeq n` and the
paper's absolute constant `C = 50`.  All norms are `ℓ²`-operator norms
(see the faithfulness notes in `Blocks.lean`).

The paper's `sup_{n≥1}` and `sup_{t≥0}` are rendered as universally quantified
inequalities, and the two set inclusions `σ(·) ⊆ …` as membership implications;
both are equivalent and avoid `sSup`/`Set` side conditions. -/
def TheoremFinite : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ n : ℕ, 1 ≤ n →
    -- invertible, and diagonalizable by an explicit similarity
    IsUnit (blockGen n α)
    ∧ (∃ (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (d : Fin n ⊕ Fin n → ℂ),
        IsUnit W ∧ blockGen n α = W * Matrix.diagonal d * W⁻¹)
    -- ‖A_n‖ ≤ 1 + Cα/(1-α)
    ∧ ‖blockGen n α‖ ≤ 1 + 50 * α / (1 - α)
    -- ‖A_n⁻¹‖ ≤ ω_n^{-1/2} (1 + Cα/(1-α))
    ∧ ‖(blockGen n α)⁻¹‖ ≤ (1 / Real.sqrt (omegaSeq n)) * (1 + 50 * α / (1 - α))
    -- ‖e^{tA_n}‖ ≤ (1 + Cα/(1-α)) e^{-ω_n t}
    ∧ (∀ t : ℝ, 0 ≤ t →
        ‖exp ((t : ℂ) • blockGen n α)‖
          ≤ (1 + 50 * α / (1 - α)) * Real.exp (-(omegaSeq n * t)))
    -- n^α/C ≤ ‖e^{π A_n⁻¹}‖ ≤ n^α
    ∧ 1 / 50 * (n : ℝ) ^ α ≤ ‖exp ((Real.pi : ℂ) • (blockGen n α)⁻¹)‖
    ∧ ‖exp ((Real.pi : ℂ) • (blockGen n α)⁻¹)‖ ≤ (n : ℝ) ^ α
    -- (ω_n) is a decreasing sequence in (0,1) with n ≤ log log (ω_n⁻¹) ≤ 2n
    ∧ 0 < omegaSeq n ∧ omegaSeq n < 1 ∧ omegaSeq (n + 1) ≤ omegaSeq n
    ∧ (n : ℝ) ≤ Real.log (Real.log ((omegaSeq n)⁻¹))
    ∧ Real.log (Real.log ((omegaSeq n)⁻¹)) ≤ 2 * n
    -- σ(A_n) ⊆ {Re z ≤ -ω_n, |z| ≥ ω_n^{1/2}}
    ∧ (∀ z ∈ spectrum ℂ (blockGen n α),
        z.re ≤ -omegaSeq n ∧ Real.sqrt (omegaSeq n) ≤ ‖z‖)
    -- σ(A_n⁻¹) ⊆ {Re z = -1, |z| ≤ ω_n^{-1/2}}
    ∧ (∀ z ∈ spectrum ℂ ((blockGen n α)⁻¹),
        z.re = -1 ∧ ‖z‖ ≤ 1 / Real.sqrt (omegaSeq n))

/-- **Theorem 1.1**, proved, with the paper's `C = 50`.

The two estimates that actually consume the constant are the flow bound
(`1 + 5·10·α/(1-α)`, from the multiplier bound and the shifted variation `≤ 10`)
and the lower half of `n^α/C ≤ ‖e^{π A_n⁻¹}‖` (`2e^π < 50`); every other bound holds
with the smaller constant `5`. -/
theorem theorem_finite : TheoremFinite := by
  intro α hα0 hα1 n hn
  have hs : (0 : ℝ) < 1 - α := by linarith
  have hK : (0 : ℝ) < α / (1 - α) := by positivity
  have h5_50 : 1 + 5 * α / (1 - α) ≤ 1 + 50 * α / (1 - α) := by
    have h1 : 5 * α / (1 - α) = 5 * (α / (1 - α)) := by ring
    have h2 : 50 * α / (1 - α) = 50 * (α / (1 - α)) := by ring
    rw [h1, h2]
    linarith
  refine ⟨blockGen_isUnit n α, blockGen_diagonalizable n α, ?_, ?_, ?_, ?_, ?_,
    omegaSeq_pos n, omegaSeq_lt_one n, omegaSeq_antitone n,
    le_log_log_omegaSeq_inv hn, log_log_omegaSeq_inv_le hn,
    fun z hz => spectrum_blockGen_mem α hz, fun z hz => spectrum_blockGen_inv_mem α hz⟩
  · -- ‖A_n‖
    exact (l2_opNorm_blockGen_le_v2 hα0 hα1 n).trans h5_50
  · -- ‖A_n⁻¹‖
    rw [one_div_sqrt_omegaSeq]
    refine (l2_opNorm_blockGen_inv_le_v2 hα0 hα1 hn).trans ?_
    exact mul_le_mul_of_nonneg_left h5_50 (Real.sqrt_nonneg _)
  · -- the flow
    exact fun t ht => l2_opNorm_exp_blockGen_le_v2 hα0 hα1 hn ht
  · -- lower half of eq:finiteinverse
    exact le_norm_exp_pi_blockGen_inv_v2 hα0 hα1 hn
  · -- upper half of eq:finiteinverse
    exact norm_exp_pi_blockGen_inv_le_v2 hα0 hα1 hn

/-! ## Axiom audit

`theorem_finite` is checked, at build time, to depend on nothing beyond the three
standard axioms of classical mathematics in Lean: `propext`, `Classical.choice` and
`Quot.sound`.  In particular it uses no `sorry`, no `native_decide`, and no extra
hypothesis.  If the dependency set ever changes, `#guard_msgs` turns this into a
build error rather than a silent regression.
-/

/--
info: 'InverseGenerator.theorem_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms theorem_finite

end InverseGenerator
