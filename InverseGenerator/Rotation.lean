/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.Toeplitz

/-!
# The rotated basis and the sign multiplier (Proposition 2.1, Step 1)

Fix `0 < α < 1` and split `α = β + γ` with `β = γ = α/2 < 1/2`.  In two orthogonal
copies `X_n = Y_n = ℂ^n` the paper sets `x_j = T_n(β) e_j`, `y_j = T_n(-γ) e_j` and
rotates:
```
z_{2j-1} = (x_j,  y_j)/√2,      z_{2j} = (x_j, -y_j)/√2.
```
The alternating sign multiplier `Δ_n` (`+1` on odd `z`, `-1` on even `z`) then has
the strikingly simple block form of Proposition 2.1, Step 1,
```
Δ_n = [[0, T_n(α)], [T_n(-α), 0]],
```
which is Proposition 2.1, Step 1 and the crux of the whole construction: it converts two
*sub-`1/2`* fractional losses into a single loss of any order `α < 1`.

## Main results

* `signMult_mul_rotSynth` : `Δ_n * W = W * D`, that block form in
  conjugation-free form.  **This is Proposition 2.1, Step 1.**
* `rotSynth_isUnit`, `signMult_eq_conj` : the same statement as
  `Δ_n = W * D * W⁻¹`.

## Implementation notes

Two simplifications relative to the paper.

*No interleaving permutation.*  The paper works with the interleaved ordering
`z_1, z_2, z_3, …` and notes the block form holds "up to the unitary permutation
that interlaces the coefficients".  Grouping the coefficients instead as
`(odd, even) ∈ ℂ^n ⊕ ℂ^n` removes that permutation entirely: the sign multiplier
becomes `D = diag(1, -1)` in block form and no reindexing is ever needed.  The
interleaved order only matters for `A_n` itself (see `Blocks.lean`), not here.

*No `1/√2`.*  The factor cancels in `W D W⁻¹`, so `rotSynth` is defined as
`√2` times the paper's `𝒱_n`.  This keeps every statement inside the base field
with no square roots — the whole file stays inside an arbitrary characteristic-zero
field.
-/

namespace InverseGenerator

open Matrix

variable {K : Type*} [Field K] [CharZero K]

section

variable (n : ℕ)

/-- The block Hadamard rotation `[[1, 1], [1, -1]]`.  Together with
`diag(T_n(β), T_n(-γ))` it factors the synthesis matrix. -/
noncomputable def rot2 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 1 1 1 (-1)

/-- The synthesis matrix of the rotated basis, scaled by `√2`: this is
`√2 · S_n` of Proposition 2.1, Step 1. -/
noncomputable def rotSynth (β γ : K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks (toeplitz n β) (toeplitz n β) (toeplitz n (-γ)) (-toeplitz n (-γ))

/-- The sign multiplier in *coefficient* coordinates: `(a, b) ↦ (a, -b)`. -/
noncomputable def signCoeff : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 1 0 0 (-1)

/-- The claimed block form of `Δ_±`. -/
noncomputable def signMult (α : K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 0 (toeplitz n α) (toeplitz n (-α)) 0

end

omit [CharZero K] in
/-- `rotSynth` factors as `diag(T_n(β), T_n(-γ)) * rot2`. -/
theorem rotSynth_eq (n : ℕ) (β γ : K) :
    rotSynth n β γ
      = fromBlocks (toeplitz n β) 0 0 (toeplitz n (-γ)) * rot2 n := by
  rw [rot2, rotSynth, fromBlocks_multiply]
  simp

/-- `rot2` is a unit, with inverse `2⁻¹ • rot2`. -/
theorem rot2_isUnit (n : ℕ) : IsUnit (rot2 (K := K) n) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have key : rot2 (K := K) n * ((2 : K)⁻¹ • rot2 n) = 1 := by
    rw [Matrix.mul_smul, rot2, fromBlocks_multiply]
    rw [show (1 : Matrix (Fin n) (Fin n) K) * 1 + 1 * 1 = (2 : K) • 1 by
      simp [two_smul]]
    rw [show (1 : Matrix (Fin n) (Fin n) K) * 1 + 1 * (-1) = 0 by simp]
    rw [show (1 : Matrix (Fin n) (Fin n) K) * 1 + (-1) * 1 = 0 by simp]
    rw [show (1 : Matrix (Fin n) (Fin n) K) * 1 + (-1) * (-1) = (2 : K) • 1 by
      simp [two_smul]]
    rw [← fromBlocks_one (l := Fin n) (m := Fin n) (α := K)]
    rw [fromBlocks_smul, smul_zero]
    congr 1 <;> rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  have key' : ((2 : K)⁻¹ • rot2 n) * rot2 (K := K) n = 1 := by
    rw [Matrix.smul_mul, rot2, fromBlocks_multiply]
    rw [show (1 : Matrix (Fin n) (Fin n) K) * 1 + 1 * 1 = (2 : K) • 1 by
      simp [two_smul]]
    rw [show (1 : Matrix (Fin n) (Fin n) K) * 1 + 1 * (-1) = 0 by simp]
    rw [show (1 : Matrix (Fin n) (Fin n) K) * 1 + (-1) * 1 = 0 by simp]
    rw [show (1 : Matrix (Fin n) (Fin n) K) * 1 + (-1) * (-1) = (2 : K) • 1 by
      simp [two_smul]]
    rw [← fromBlocks_one (l := Fin n) (m := Fin n) (α := K)]
    rw [fromBlocks_smul, smul_zero]
    congr 1 <;> rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  exact ⟨⟨_, _, key, key'⟩, rfl⟩

/-- `diag(T_n(β), T_n(-γ))` is a unit. -/
theorem blockDiag_toeplitz_isUnit (n : ℕ) (β γ : K) :
    IsUnit (fromBlocks (toeplitz n β) 0 0 (toeplitz n (-γ))) := by
  refine ⟨⟨fromBlocks (toeplitz n β) 0 0 (toeplitz n (-γ)),
      fromBlocks (toeplitz n (-β)) 0 0 (toeplitz n γ), ?_, ?_⟩, rfl⟩
  · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      toeplitz_mul_neg, toeplitz_neg_mul, fromBlocks_one]
  · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      toeplitz_mul_neg, toeplitz_neg_mul, fromBlocks_one]

/-- The synthesis matrix is invertible. -/
theorem rotSynth_isUnit (n : ℕ) (β γ : K) : IsUnit (rotSynth n β γ) := by
  rw [rotSynth_eq]
  exact (blockDiag_toeplitz_isUnit n β γ).mul (rot2_isUnit n)

/-- **Proposition 2.1, Step 1**, in conjugation-free form:
```
Δ_n * W = W * D,   Δ_n = [[0, T(β+γ)], [T(-(β+γ)), 0]].
```
The whole content is the group law of Lemma A.1: `T(α) T(-γ) = T(β)` and
`T(-α) T(β) = T(-γ)` when `α = β + γ`. -/
theorem signMult_mul_rotSynth (n : ℕ) (β γ : K) :
    signMult n (β + γ) * rotSynth n β γ = rotSynth n β γ * signCoeff n := by
  rw [signMult, rotSynth, signCoeff, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.mul_neg, neg_zero, neg_neg, toeplitz_mul,
    show β + γ + -γ = β from by ring, show -(β + γ) + β = -γ from by ring]

/-- **Proposition 2.1, Step 1** in conjugated form: the alternating sign multiplier is
similar to `diag(1, -1)` via the synthesis matrix, and equals the antidiagonal
Toeplitz block. -/
theorem signMult_eq_conj (n : ℕ) (β γ : K) :
    signMult n (β + γ) = rotSynth n β γ * signCoeff n * (rotSynth n β γ)⁻¹ := by
  have hU := rotSynth_isUnit (K := K) n β γ
  have hinv : rotSynth n β γ * (rotSynth n β γ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  calc signMult n (β + γ)
      = signMult n (β + γ) * (rotSynth n β γ * (rotSynth n β γ)⁻¹) := by
        rw [hinv, Matrix.mul_one]
    _ = signMult n (β + γ) * rotSynth n β γ * (rotSynth n β γ)⁻¹ := by
        rw [Matrix.mul_assoc]
    _ = rotSynth n β γ * signCoeff n * (rotSynth n β γ)⁻¹ := by
        rw [signMult_mul_rotSynth]

end InverseGenerator
