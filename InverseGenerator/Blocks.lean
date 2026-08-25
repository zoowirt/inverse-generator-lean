/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.Lacunary
import InverseGenerator.Rotation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The explicit generator blocks `A_n`

The matrices `A_n` of §2,
```
A_n = 𝒱_n diag(λ₁, …, λ_{2n}) 𝒱_n⁻¹,     λ_k = (-1 + i y_k)⁻¹,
```
the operators Theorem 1.1 is about.

## Main definitions

* `towerPoint k = -1 + i y_k`, `towerSpec k = (towerPoint k)⁻¹` — the spectrum
  `(λ_k)` of §2.
* `zIndex` — the interleaving `inl j ↦ 2j`, `inr j ↦ 2j+1`.
* `blockGen n α` — the matrix `A_n`.

## Faithfulness notes

These matter for auditing the statement; a misstated Theorem 1.1 would invalidate
everything built on top of it.

**Dimension.** The paper has `A_n ∈ M_{2n}(ℂ)`.  Here the index type is
`Fin n ⊕ Fin n`, and `card_blockIndex` records that its cardinality is `2 * n`.

**Norm.** The paper states (line 87) "All matrix norms are Euclidean operator
norms".  This file therefore opens `Matrix.Norms.L2Operator`, so every `‖·‖` below
is the `ℓ²`-operator norm, *not* the Frobenius or `ℓ^∞`-operator norm (Mathlib has
instances for all three, and they disagree).

**Which `λ` indexing.**  `blockGen n α` uses the **block-local** indexing
`λ₀, …, λ_{2n-1}`, matching the paper's `λ₁, …, λ_{2n}` in §2: the `n`-th matrix
restarts the tower at `y₁`, it does not continue a single global sequence.  This is
what keeps `ω_n = 1/y_{2n+1}` rather than a tower in `n² + n`.

**Interleaving is real here.**  Unlike Step 1 of Proposition 2.1 — where the sign
pattern
`±1` happens to coincide with `inl`/`inr` and the permutation could be dropped — `A_n`
assigns the *`k`-th* eigenvalue to the *`k`-th* `z`-vector, so the interleaving
`zIndex` must be carried explicitly.  Consistency check: `(-1)^{y_k} = (-1)^k` gives
`+1` on `zIndex (inl j) = 2j` and `-1` on `zIndex (inr j) = 2j+1`, which is exactly
`signCoeff = diag(1, -1)`.  So the parity of `(y_k)` does line up with the
grouped block form used in `Rotation.lean`.

**`sup` versus `∀`.**  The paper writes `sup_{n≥1} ‖A_n‖ ≤ a_α` and
`sup_{n≥1} sup_{t≥0} ‖e^{tA_n}‖ ≤ M_α`; these are stated below as universally
quantified inequalities, which is equivalent and avoids `sSup` side conditions.
-/

namespace InverseGenerator

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

/-- The `z`-basis index (0-based) of a coefficient slot: `inl j ↦ 2j`,
`inr j ↦ 2j + 1`.  This is the interleaving of `eq:rotated-basis`. -/
def zIndex {n : ℕ} : Fin n ⊕ Fin n → ℕ
  | .inl j => 2 * (j : ℕ)
  | .inr j => 2 * (j : ℕ) + 1

/-- The index type of `A_n` has `2n` elements, matching `A_n ∈ M_{2n}(ℂ)`. -/
theorem card_blockIndex (n : ℕ) : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
  simp [two_mul]

/-- `b_k = -1 + i y_k` of §2. -/
noncomputable def towerPoint (k : ℕ) : ℂ := -1 + Complex.I * (tower k : ℂ)

/-- `λ_k = b_k⁻¹`, the spectrum of `A_n`. -/
noncomputable def towerSpec (k : ℕ) : ℂ := (towerPoint k)⁻¹

@[simp] theorem towerPoint_re (k : ℕ) : (towerPoint k).re = -1 := by
  simp [towerPoint]

/-- `b_k ≠ 0`, since `Re b_k = -1`.  This is what makes `A_n` invertible and puts
the spectrum of `B_n = A_n⁻¹` on the line `Re z = -1`. -/
theorem towerPoint_ne_zero (k : ℕ) : towerPoint k ≠ 0 := by
  intro h
  have := towerPoint_re k
  rw [h] at this
  norm_num at this

theorem towerSpec_ne_zero (k : ℕ) : towerSpec k ≠ 0 :=
  inv_ne_zero (towerPoint_ne_zero k)

/-- The synthesis matrix at the paper's split `β = γ = α/2` (`eq:rotated-basis`). -/
noncomputable def blockSynth (n : ℕ) (α : ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  rotSynth n ((α / 2 : ℝ) : ℂ) ((α / 2 : ℝ) : ℂ)

theorem blockSynth_isUnit (n : ℕ) (α : ℝ) : IsUnit (blockSynth n α) :=
  rotSynth_isUnit _ _ _

/-- The diagonal of eigenvalues, in the interleaved `z`-ordering. -/
noncomputable def blockDiag (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.diagonal fun s => towerSpec (zIndex s)

theorem blockDiag_isUnit (n : ℕ) : IsUnit (blockDiag n) := by
  refine ⟨⟨blockDiag n, Matrix.diagonal fun s => (towerSpec (zIndex s))⁻¹, ?_, ?_⟩, rfl⟩ <;>
    · rw [blockDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      refine congrArg _ (funext fun s => ?_)
      first
        | exact mul_inv_cancel₀ (towerSpec_ne_zero _)
        | exact inv_mul_cancel₀ (towerSpec_ne_zero _)

/-- **`A_n`** of §2: the explicit `2n × 2n` generator
`𝒱_n diag(λ₁, …, λ_{2n}) 𝒱_n⁻¹`, in the block-local `λ` indexing. -/
noncomputable def blockGen (n : ℕ) (α : ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  blockSynth n α * blockDiag n * (blockSynth n α)⁻¹

/-- `A_n` is invertible: it is a conjugate of a diagonal matrix with nonzero
entries.  This is the first conjunct of Theorem 1.1. -/
theorem blockGen_isUnit (n : ℕ) (α : ℝ) : IsUnit (blockGen n α) := by
  rw [blockGen]
  exact ((blockSynth_isUnit n α).mul (blockDiag_isUnit n)).mul
    (isUnit_nonsing_inv_iff.mpr (blockSynth_isUnit n α))

/-! ### `e^{π A_n⁻¹} = e^{-π} Δ_n`

The identity of §2, and the reason the inverse-generator growth is *exact* rather
than asymptotic.  It is **not** an independent analytic fact: it is Step 1 of
Proposition 2.1 composed with the parity alternation of `(y_k)`.

    e^{π b_k} = e^{-π} (-1)^{y_k}      [b_k = -1 + i y_k]
    (-1)^{y_k} = (-1)^k                [`neg_one_pow_tower`]
    ⇒ diag(e^{π b_k}) = e^{-π} • diag(1,-1) = e^{-π} • signCoeff
    ⇒ e^{π B_n} = e^{-π} • (W · signCoeff · W⁻¹) = e^{-π} • Δ_n   [`signMult_eq_conj`]

So the only analytic input is `Complex.exp_pi_mul_I`; everything else is the parity
induction plus the group law.  Note that the identity cannot be checked numerically:
`e^{iπ y_k}` is beyond floating point for `k ≥ 6`, since `y_k` already has thousands
of digits.
-/

/-- `B_n = A_n⁻¹` has spectrum `b_k = -1 + i y_k` on the line `Re z = -1`. -/
theorem blockDiag_inv (n : ℕ) :
    (blockDiag n)⁻¹ = Matrix.diagonal fun s => towerPoint (zIndex s) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [blockDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  refine congrArg _ (funext fun s => ?_)
  exact inv_mul_cancel₀ (towerPoint_ne_zero _)

theorem blockGen_inv (n : ℕ) (α : ℝ) :
    (blockGen n α)⁻¹ = blockSynth n α * (blockDiag n)⁻¹ * (blockSynth n α)⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  have hWdet := (Matrix.isUnit_iff_isUnit_det _).mp (blockSynth_isUnit n α)
  have hDdet := (Matrix.isUnit_iff_isUnit_det _).mp (blockDiag_isUnit n)
  rw [blockGen]
  calc blockSynth n α * blockDiag n * (blockSynth n α)⁻¹ *
        (blockSynth n α * (blockDiag n)⁻¹ * (blockSynth n α)⁻¹)
      = blockSynth n α * blockDiag n * ((blockSynth n α)⁻¹ * blockSynth n α) *
          ((blockDiag n)⁻¹ * (blockSynth n α)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.nonsing_inv_mul _ hWdet, Matrix.mul_one]
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (blockDiag n),
          Matrix.mul_nonsing_inv _ hDdet, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ hWdet]

/-- `e^{π b_k} = e^{-π} · (-1)^k`, the scalar heart of the identity. -/
theorem cexp_pi_mul_towerPoint (k : ℕ) :
    Complex.exp ((Real.pi : ℂ) * towerPoint k) = Complex.exp (-(Real.pi : ℂ)) * (-1) ^ k := by
  have hsplit : (Real.pi : ℂ) * towerPoint k
      = -(Real.pi : ℂ) + (tower k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    rw [towerPoint]
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I,
    neg_one_pow_tower k]

set_option linter.flexible false in
set_option linter.unnecessarySeqFocus false in
/-- **The identity of §2**: `e^{π A_n⁻¹} = e^{-π} · Δ_n`, where `Δ_n = signMult n α`
is the antidiagonal Toeplitz block of Proposition 2.1, Step 1. -/
theorem exp_pi_blockGen_inv (n : ℕ) (α : ℝ) :
    exp ((Real.pi : ℂ) • (blockGen n α)⁻¹)
      = Complex.exp (-(Real.pi : ℂ)) • signMult n (((α / 2 : ℝ) : ℂ) + ((α / 2 : ℝ) : ℂ)) := by
  have hW := blockSynth_isUnit n α
  -- push the scalar inside the conjugation
  have hsmul : (Real.pi : ℂ) • (blockGen n α)⁻¹
      = blockSynth n α * ((Real.pi : ℂ) • (blockDiag n)⁻¹) * (blockSynth n α)⁻¹ := by
    rw [blockGen_inv, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsmul, Matrix.exp_conj _ _ hW, blockDiag_inv, ← Matrix.diagonal_smul,
    Matrix.exp_diagonal]
  -- the diagonal is `e^{-π}` times the `±1` pattern of `signCoeff`
  have hdiag : (exp ((Real.pi : ℂ) • fun s : Fin n ⊕ Fin n => towerPoint (zIndex s)))
      = Complex.exp (-(Real.pi : ℂ)) • fun s : Fin n ⊕ Fin n => ((-1 : ℂ)) ^ zIndex s := by
    funext s
    rw [Pi.exp_def]
    simp only [Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
    exact cexp_pi_mul_towerPoint (zIndex s)
  rw [hdiag, Matrix.diagonal_smul, signMult_eq_conj]
  -- `(-1)^{zIndex s}` is exactly `signCoeff`
  have heven : ∀ j : Fin n, ((-1 : ℂ)) ^ zIndex (Sum.inl j : Fin n ⊕ Fin n) = 1 := by
    intro j; simp [zIndex, pow_mul]
  have hodd : ∀ j : Fin n, ((-1 : ℂ)) ^ zIndex (Sum.inr j : Fin n ⊕ Fin n) = -1 := by
    intro j; simp [zIndex, pow_succ, pow_mul]
  have hsign : (Matrix.diagonal fun s : Fin n ⊕ Fin n => ((-1 : ℂ)) ^ zIndex s)
      = signCoeff n := by
    rw [signCoeff]
    ext s t
    -- `simp` then `split_ifs` is flagged by the flexible-tactic linter; the four
    -- block cases genuinely need `simp` to expose the `ite`s before splitting them.
    cases s <;> cases t <;>
      simp [Matrix.diagonal, heven, hodd, Matrix.one_apply] <;>
      (split_ifs <;> simp)
  rw [hsign, Matrix.mul_smul, Matrix.smul_mul, blockSynth]

end InverseGenerator
