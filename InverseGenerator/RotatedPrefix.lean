/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.BVMultiplier
import InverseGenerator.Blocks
import InverseGenerator.PrefixNorm

/-!
# The partial-sum projections of the rotated basis (Proposition 2.1, Step 2)

The coordinate projections `𝒬_{n,k}` of the rotated basis `(z_k)` (`eq:rotated-basis`),
in the grouped block coordinates, and the bound
```
sup_{n} sup_{k ≤ 2n} ‖𝒬_{n,k} - P_k‖ ≤ 5α/(1-α)          (eq:rotatedprefix)
```
measured against the orthonormal prefix projection `P_k`
rather than against `0`; the constant then vanishes as `α → 0`, which is what the
explicit `C = 50` of Theorem 1.1 needs.  The file ends with the multiplier bound
`l2_opNorm_multiplier_le` that all four norm estimates of Theorem 1.1 are read off
from.

## Structure, following the paper's proof

* **Even prefixes** (`prefixZ_even`): the indicator diagonal for `zIndex s < 2k`
  commutes with the Hadamard rotation, so `𝒬_{n,2k}` is exactly the block-diagonal
  pair of the two `prefixConj`s of Lemma A.4 — at parameters `α/2` and `-α/2`, which
  is where the split `α = α/2 + α/2 < 1` of `eq:rotated-basis` is consumed.
* **Odd prefixes** (`prefixZ_odd`): `𝒬_{n,2k+1} = 𝒬_{n,2k} + ℰ_{n,2k}`, and the
  rank-one projection `ℰ_{n,2k}` is `vecMulVec` of a column of `𝒱_n` with a row of
  `𝒱_n⁻¹`.  It is compared with the corresponding rank-one projection at `α = 0`,
  whose `ℓ²` tails are `O(α)` because `∑_{r ≥ 1} a_r(θ)² = O(θ²)` for `|θ| < 1/2`
  (`sum_sq_binomCoeff_tail_pos`, `sum_sq_binomCoeff_tail_neg`).

## New generic ingredients

`rotSynth_inv` (the explicit inverse of the synthesis matrix — everything downstream
is then `fromBlocks` algebra with no `⁻¹`), `l2_opNorm_vecMulVec_le` (rank-one norm)
and `l2_opNorm_fromBlocks_diag_le` (block-diagonal norm); Mathlib has neither of the
last two for the `ℓ²`-operator norm.
-/

namespace InverseGenerator

open Finset Matrix

/-! ## The explicit inverse of the synthesis matrix -/

section Generic

variable {K : Type*} [Field K] [CharZero K]

/-- The explicit inverse of the (scaled) synthesis matrix:
`(√2·𝒱_n)⁻¹ = 2⁻¹ · [[T(-β), T(γ)], [T(-β), -T(γ)]]`. -/
theorem rotSynth_inv (n : ℕ) (β γ : K) :
    (rotSynth n β γ)⁻¹
      = (2⁻¹ : K) • fromBlocks (toeplitz n (-β)) (toeplitz n γ)
          (toeplitz n (-β)) (-toeplitz n γ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [rotSynth, Matrix.mul_smul, fromBlocks_multiply]
  rw [show toeplitz n β * toeplitz n (-β) + toeplitz n β * toeplitz n (-β)
      = (2 : K) • (1 : Matrix (Fin n) (Fin n) K) from by rw [toeplitz_mul_neg, two_smul]]
  rw [show toeplitz n β * toeplitz n γ + toeplitz n β * -toeplitz n γ
      = (0 : Matrix (Fin n) (Fin n) K) from by rw [Matrix.mul_neg]; exact add_neg_cancel _]
  rw [show toeplitz n (-γ) * toeplitz n (-β) + -toeplitz n (-γ) * toeplitz n (-β)
      = (0 : Matrix (Fin n) (Fin n) K) from by rw [Matrix.neg_mul]; exact add_neg_cancel _]
  rw [show toeplitz n (-γ) * toeplitz n γ + -toeplitz n (-γ) * -toeplitz n γ
      = (2 : K) • (1 : Matrix (Fin n) (Fin n) K) from by
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, toeplitz_neg_mul, two_smul]]
  rw [show fromBlocks ((2 : K) • (1 : Matrix (Fin n) (Fin n) K)) 0 0
        ((2 : K) • (1 : Matrix (Fin n) (Fin n) K))
      = (2 : K) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) from by
    rw [← fromBlocks_one (l := Fin n) (m := Fin n) (α := K), fromBlocks_smul, smul_zero]]
  rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

end Generic

/-! ## `ℓ²` bounds for rows and columns of the Toeplitz factors -/

section ColRow

open scoped Matrix.Norms.L2Operator

end ColRow

/-! ## Rank-one and block-diagonal `ℓ²`-operator norm bounds -/

section OpNormTools

open scoped Matrix.Norms.L2Operator

variable {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂] [DecidableEq m₁] [DecidableEq m₂]

omit [DecidableEq m₁] in
/-- Squared form of `sqrt_sum_sq_mulVec_le`. -/
theorem sum_sq_mulVec_le (A : Matrix m₁ m₂ ℂ) (x : m₂ → ℂ) :
    ∑ p, ‖∑ q, A p q * x q‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ q, ‖x q‖ ^ 2 := by
  have h := sqrt_sum_sq_mulVec_le (A := A) x
  have h1 : (0 : ℝ) ≤ ∑ p, ‖∑ q, A p q * x q‖ ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ ∑ q, ‖x q‖ ^ 2 := by positivity
  have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt h1, mul_pow, Real.sq_sqrt h2] at h3
  exact h3

omit [DecidableEq m₁] in
/-- **Rank-one norm bound**: `‖x ⊗ y*‖ ≤ ‖x‖₂ ‖y‖₂` in the `ℓ²`-operator norm. -/
theorem l2_opNorm_vecMulVec_le (x : m₁ → ℂ) (y : m₂ → ℂ) :
    ‖Matrix.vecMulVec x y‖
      ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2) := by
  refine l2_opNorm_le_of_mulVec (by positivity) fun z => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  have hterm : ∀ i ∈ Finset.univ (α := m₁),
      ‖(EuclideanSpace.equiv m₁ ℂ).symm (Matrix.mulVec (Matrix.vecMulVec x y) z) i‖ ^ 2
        = ‖x i‖ ^ 2 * ‖∑ q, y q * z q‖ ^ 2 := by
    intro i _
    have h0 : (EuclideanSpace.equiv m₁ ℂ).symm (Matrix.mulVec (Matrix.vecMulVec x y) z) i
        = x i * ∑ q, y q * z q := by
      change ∑ q, Matrix.vecMulVec x y i q * z q = x i * ∑ q, y q * z q
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [Matrix.vecMulVec_apply]; ring
    rw [h0, norm_mul, mul_pow]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hCS : ‖∑ q, y q * z q‖
      ≤ Real.sqrt (∑ q, ‖y q‖ ^ 2) * Real.sqrt (∑ q, ‖z q‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => norm_mul (y q) (z q)]
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun q => ‖y q‖) (fun q => ‖z q‖)
    simpa using h
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) * ‖∑ q, y q * z q‖
      ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2)
          * (Real.sqrt (∑ q, ‖y q‖ ^ 2) * Real.sqrt (∑ q, ‖z q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ j, ‖y j‖ ^ 2)
          * Real.sqrt (∑ q, ‖z q‖ ^ 2) := by ring

/-- **Block-diagonal norm bound**: `‖diag(A, D)‖ ≤ max` (stated with a common
bound `C`). -/
theorem l2_opNorm_fromBlocks_diag_le {A : Matrix m₁ m₁ ℂ} {D : Matrix m₂ m₂ ℂ}
    {C : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) (hD : ‖D‖ ≤ C) :
    ‖Matrix.fromBlocks A 0 0 D‖ ≤ C := by
  refine l2_opNorm_le_of_mulVec hC fun z => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  have hpt : ∀ s : m₁ ⊕ m₂,
      (EuclideanSpace.equiv (m₁ ⊕ m₂) ℂ).symm
        (Matrix.mulVec (Matrix.fromBlocks A 0 0 D) z) s
      = ∑ t, Matrix.fromBlocks A 0 0 D s t * z t := fun _ => rfl
  have hinl : ∀ i : m₁, ∑ t, Matrix.fromBlocks A 0 0 D (Sum.inl i) t * z t
      = ∑ j, A i j * z (Sum.inl j) := by
    intro i
    rw [Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
  have hinr : ∀ i : m₂, ∑ t, Matrix.fromBlocks A 0 0 D (Sum.inr i) t * z t
      = ∑ j, D i j * z (Sum.inr j) := by
    intro i
    rw [Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, zero_add]
  have hsum : ∑ s : m₁ ⊕ m₂, ‖(EuclideanSpace.equiv (m₁ ⊕ m₂) ℂ).symm
        (Matrix.mulVec (Matrix.fromBlocks A 0 0 D) z) s‖ ^ 2
      = (∑ i : m₁, ‖∑ j, A i j * z (Sum.inl j)‖ ^ 2)
        + ∑ i : m₂, ‖∑ j, D i j * z (Sum.inr j)‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => by rw [hpt s] :
      ∀ s ∈ Finset.univ,
        ‖(EuclideanSpace.equiv (m₁ ⊕ m₂) ℂ).symm
          (Matrix.mulVec (Matrix.fromBlocks A 0 0 D) z) s‖ ^ 2
        = ‖∑ t, Matrix.fromBlocks A 0 0 D s t * z t‖ ^ 2)]
    rw [Fintype.sum_sum_type]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [hinl i]
    · exact Finset.sum_congr rfl fun i _ => by rw [hinr i]
  rw [hsum]
  have hz : ∑ s : m₁ ⊕ m₂, ‖z s‖ ^ 2
      = (∑ j : m₁, ‖z (Sum.inl j)‖ ^ 2) + ∑ j : m₂, ‖z (Sum.inr j)‖ ^ 2 :=
    Fintype.sum_sum_type _
  have hA2 := sum_sq_mulVec_le A (fun j => z (Sum.inl j))
  have hD2 := sum_sq_mulVec_le D (fun j => z (Sum.inr j))
  have hAC : ‖A‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hDC : ‖D‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hZ1 : (0 : ℝ) ≤ ∑ j : m₁, ‖z (Sum.inl j)‖ ^ 2 := by positivity
  have hZ2 : (0 : ℝ) ≤ ∑ j : m₂, ‖z (Sum.inr j)‖ ^ 2 := by positivity
  calc Real.sqrt ((∑ i : m₁, ‖∑ j, A i j * z (Sum.inl j)‖ ^ 2)
        + ∑ i : m₂, ‖∑ j, D i j * z (Sum.inr j)‖ ^ 2)
      ≤ Real.sqrt (C ^ 2 * ((∑ j : m₁, ‖z (Sum.inl j)‖ ^ 2)
          + ∑ j : m₂, ‖z (Sum.inr j)‖ ^ 2)) := by
        refine Real.sqrt_le_sqrt ?_
        have b1 : ∑ i : m₁, ‖∑ j, A i j * z (Sum.inl j)‖ ^ 2
            ≤ C ^ 2 * ∑ j : m₁, ‖z (Sum.inl j)‖ ^ 2 :=
          hA2.trans (mul_le_mul_of_nonneg_right hAC hZ1)
        have b2 : ∑ i : m₂, ‖∑ j, D i j * z (Sum.inr j)‖ ^ 2
            ≤ C ^ 2 * ∑ j : m₂, ‖z (Sum.inr j)‖ ^ 2 :=
          hD2.trans (mul_le_mul_of_nonneg_right hDC hZ2)
        nlinarith [b1, b2]
    _ = C * Real.sqrt (∑ s : m₁ ⊕ m₂, ‖z s‖ ^ 2) := by
        rw [hz, Real.sqrt_mul (by positivity), Real.sqrt_sq hC]

end OpNormTools

/-! ## The prefix and coordinate projections of the rotated basis -/

section PrefixZ

open scoped Matrix.Norms.L2Operator

/-- `zIndex` never exceeds `2n - 1`. -/
theorem zIndex_lt {n : ℕ} (s : Fin n ⊕ Fin n) : zIndex s < 2 * n := by
  cases s with
  | inl j => have := j.isLt; simp only [zIndex]; omega
  | inr j => have := j.isLt; simp only [zIndex]; omega

/-- The prefix projection `𝒬_{n,k}` onto the first `k` rotated basis vectors,
in the grouped block coordinates. -/
noncomputable def prefixZ (n : ℕ) (α : ℝ) (k : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  blockSynth n α * Matrix.diagonal (fun s => if zIndex s < k then (1 : ℂ) else 0)
    * (blockSynth n α)⁻¹

/-- The rank-one coordinate projection `ℰ_{n,k}` onto the `k`-th rotated basis
vector (0-based). -/
noncomputable def coordProjZ (n : ℕ) (α : ℝ) (k : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  blockSynth n α * Matrix.diagonal (fun s => if zIndex s = k then (1 : ℂ) else 0)
    * (blockSynth n α)⁻¹

/-- Decomposition of a `zIndex`-diagonal into single-coordinate diagonals. -/
theorem diagonal_zIndex_eq_sum (n : ℕ) (f : ℕ → ℂ) :
    Matrix.diagonal (fun s : Fin n ⊕ Fin n => f (zIndex s))
      = ∑ k ∈ range (2 * n),
          f k • Matrix.diagonal (fun s => if zIndex s = k then (1 : ℂ) else 0) := by
  ext s t
  rw [Matrix.sum_apply]
  by_cases hst : s = t
  · subst hst
    rw [Matrix.diagonal_apply_eq]
    calc f (zIndex s)
        = if zIndex s ∈ range (2 * n) then f (zIndex s) else 0 := by
          rw [if_pos (Finset.mem_range.mpr (zIndex_lt s))]
      _ = ∑ k ∈ range (2 * n), if zIndex s = k then f k else 0 :=
          (Finset.sum_ite_eq (range (2 * n)) (zIndex s) f).symm
      _ = ∑ k ∈ range (2 * n), (f k • Matrix.diagonal
            (fun s' : Fin n ⊕ Fin n => if zIndex s' = k then (1 : ℂ) else 0)) s s := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
          by_cases h : zIndex s = k
          · rw [if_pos h, if_pos h, mul_one]
          · rw [if_neg h, if_neg h, mul_zero]
  · rw [Matrix.diagonal_apply_ne _ hst]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hst, smul_zero]

/-- The conjugated form: any `zIndex`-diagonal multiplier is the sum of its
rank-one coordinate projections.  Applied with `f = λ` it gives `A_n`, with
`f = e^{tλ}` the flow, with `f = 1` the resolution of the identity. -/
theorem conj_diagonal_zIndex_eq_sum (n : ℕ) (α : ℝ) (f : ℕ → ℂ) :
    blockSynth n α * Matrix.diagonal (fun s => f (zIndex s)) * (blockSynth n α)⁻¹
      = ∑ k ∈ range (2 * n), f k • coordProjZ n α k := by
  rw [diagonal_zIndex_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- The coordinate projections sum to the prefix projections. -/
theorem sum_coordProjZ (n : ℕ) (α : ℝ) (K : ℕ) :
    ∑ k ∈ range K, coordProjZ n α k = prefixZ n α K := by
  have hdiag : (∑ k ∈ range K, Matrix.diagonal
        (fun s : Fin n ⊕ Fin n => if zIndex s = k then (1 : ℂ) else 0))
      = Matrix.diagonal (fun s : Fin n ⊕ Fin n => if zIndex s < K then (1 : ℂ) else 0) := by
    ext s t
    rw [Matrix.sum_apply]
    by_cases hst : s = t
    · subst hst
      rw [Matrix.diagonal_apply_eq]
      calc ∑ k ∈ range K, Matrix.diagonal
            (fun s' : Fin n ⊕ Fin n => if zIndex s' = k then (1 : ℂ) else 0) s s
          = ∑ k ∈ range K, if zIndex s = k then (1 : ℂ) else 0 :=
            Finset.sum_congr rfl fun k _ => Matrix.diagonal_apply_eq _ s
        _ = if zIndex s ∈ range K then (1 : ℂ) else 0 :=
            Finset.sum_ite_eq (range K) (zIndex s) fun _ => (1 : ℂ)
        _ = if zIndex s < K then (1 : ℂ) else 0 := by simp only [Finset.mem_range]
    · rw [Matrix.diagonal_apply_ne _ hst]
      exact Finset.sum_eq_zero fun k _ => Matrix.diagonal_apply_ne _ hst
  rw [prefixZ, ← hdiag, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- The full prefix is the identity: `𝒬_{n,2n} = 1`. -/
theorem prefixZ_full (n : ℕ) (α : ℝ) : prefixZ n α (2 * n) = 1 := by
  rw [prefixZ]
  rw [show Matrix.diagonal (fun s : Fin n ⊕ Fin n => if zIndex s < 2 * n then (1 : ℂ) else 0)
      = 1 from by
    rw [← Matrix.diagonal_one]
    congr 1
    funext s
    rw [if_pos (zIndex_lt s)]]
  rw [Matrix.mul_one,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (blockSynth_isUnit n α))]

/-- **Even prefixes are block-diagonal pairs of `prefixConj`s** — the heart of
Proposition 2.1, Step 2.  The indicator diagonal for `zIndex s < 2k` commutes with the Hadamard
rotation, so no interleaving survives. -/
theorem prefixZ_even (n : ℕ) (α : ℝ) (k : ℕ) :
    prefixZ n α (2 * k)
      = Matrix.fromBlocks (prefixConj n k (((α / 2 : ℝ)) : ℂ)) 0 0
          (prefixConj n k (-((α / 2 : ℝ) : ℂ))) := by
  have hfun : (fun s : Fin n ⊕ Fin n => if zIndex s < 2 * k then (1 : ℂ) else 0)
      = Sum.elim (fun j : Fin n => if (j : ℕ) < k then (1 : ℂ) else 0)
          (fun j : Fin n => if (j : ℕ) < k then (1 : ℂ) else 0) := by
    funext s
    cases s with
    | inl j =>
      rw [Sum.elim_inl, show zIndex (Sum.inl j : Fin n ⊕ Fin n) = 2 * (j : ℕ) from rfl]
      by_cases h : (j : ℕ) < k
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    | inr j =>
      rw [Sum.elim_inr, show zIndex (Sum.inr j : Fin n ⊕ Fin n) = 2 * (j : ℕ) + 1 from rfl]
      by_cases h : (j : ℕ) < k
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
  have hdiag : Matrix.diagonal (fun s : Fin n ⊕ Fin n => if zIndex s < 2 * k then (1 : ℂ) else 0)
      = Matrix.fromBlocks (prefixProj n k) 0 0 (prefixProj n k) := by
    rw [hfun, ← Matrix.fromBlocks_diagonal]
    rfl
  have hinv : (blockSynth n α)⁻¹
      = (2⁻¹ : ℂ) • fromBlocks (toeplitz n (-((α / 2 : ℝ) : ℂ))) (toeplitz n ((α / 2 : ℝ) : ℂ))
          (toeplitz n (-((α / 2 : ℝ) : ℂ))) (-toeplitz n ((α / 2 : ℝ) : ℂ)) := by
    rw [blockSynth]
    exact rotSynth_inv n _ _
  rw [prefixZ, hdiag, hinv,
    show blockSynth n α = fromBlocks (toeplitz n ((α / 2 : ℝ) : ℂ)) (toeplitz n ((α / 2 : ℝ) : ℂ))
      (toeplitz n (-((α / 2 : ℝ) : ℂ))) (-toeplitz n (-((α / 2 : ℝ) : ℂ))) from rfl]
  rw [Matrix.mul_smul, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, add_neg_cancel]
  -- pack up: `2⁻¹ • diag(X+X, Z+Z) = diag(X, Z)`
  have hsm : ∀ (c : ℂ) (Q₁' Q₂' : Matrix (Fin n) (Fin n) ℂ),
      c • Matrix.fromBlocks Q₁' 0 0 Q₂' = Matrix.fromBlocks (c • Q₁') 0 0 (c • Q₂') := by
    intro c Q₁' Q₂'
    rw [fromBlocks_smul, smul_zero]
  have hpack : ∀ Q₁' Q₂' : Matrix (Fin n) (Fin n) ℂ,
      (2⁻¹ : ℂ) • Matrix.fromBlocks ((2 : ℂ) • Q₁') 0 0 ((2 : ℂ) • Q₂')
        = Matrix.fromBlocks Q₁' 0 0 Q₂' := by
    intro Q₁' Q₂'
    calc (2⁻¹ : ℂ) • Matrix.fromBlocks ((2 : ℂ) • Q₁') 0 0 ((2 : ℂ) • Q₂')
        = (2⁻¹ : ℂ) • ((2 : ℂ) • Matrix.fromBlocks Q₁' 0 0 Q₂') := by
          rw [hsm 2 Q₁' Q₂']
      _ = Matrix.fromBlocks Q₁' 0 0 Q₂' := by
          rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  rw [show prefixConj n k (((α / 2 : ℝ)) : ℂ)
      = toeplitz n ((α / 2 : ℝ) : ℂ) * prefixProj n k * toeplitz n (-((α / 2 : ℝ) : ℂ))
      from rfl]
  rw [show prefixConj n k (-((α / 2 : ℝ) : ℂ))
      = toeplitz n (-((α / 2 : ℝ) : ℂ)) * prefixProj n k * toeplitz n ((α / 2 : ℝ) : ℂ)
      from by rw [prefixConj, neg_neg]]
  rw [show toeplitz n ((α / 2 : ℝ) : ℂ) * prefixProj n k * toeplitz n (-((α / 2 : ℝ) : ℂ))
        + toeplitz n ((α / 2 : ℝ) : ℂ) * prefixProj n k * toeplitz n (-((α / 2 : ℝ) : ℂ))
      = (2 : ℂ) • (toeplitz n ((α / 2 : ℝ) : ℂ) * prefixProj n k
          * toeplitz n (-((α / 2 : ℝ) : ℂ)))
      from (two_smul ℂ _).symm]
  rw [show toeplitz n (-((α / 2 : ℝ) : ℂ)) * prefixProj n k * toeplitz n ((α / 2 : ℝ) : ℂ)
        + toeplitz n (-((α / 2 : ℝ) : ℂ)) * prefixProj n k * toeplitz n ((α / 2 : ℝ) : ℂ)
      = (2 : ℂ) • (toeplitz n (-((α / 2 : ℝ) : ℂ)) * prefixProj n k
          * toeplitz n ((α / 2 : ℝ) : ℂ))
      from (two_smul ℂ _).symm]
  exact hpack _ _

/-- Odd prefixes add one rank-one coordinate projection. -/
theorem prefixZ_odd (n : ℕ) (α : ℝ) (k : ℕ) :
    prefixZ n α (2 * k + 1) = prefixZ n α (2 * k) + coordProjZ n α (2 * k) := by
  have hfun : (fun s : Fin n ⊕ Fin n => if zIndex s < 2 * k + 1 then (1 : ℂ) else 0)
      = fun s : Fin n ⊕ Fin n => (if zIndex s < 2 * k then (1 : ℂ) else 0)
        + if zIndex s = 2 * k then (1 : ℂ) else 0 := by
    funext s
    by_cases h1 : zIndex s < 2 * k
    · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero]
    · by_cases h2 : zIndex s = 2 * k
      · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add]
      · rw [if_neg (by omega), if_neg h1, if_neg h2, add_zero]
  rw [prefixZ, prefixZ, coordProjZ, hfun, ← Matrix.diagonal_add, Matrix.mul_add,
    Matrix.add_mul]

/-- The even coordinate projection is rank one: a column of `𝒱_n` tensored with a
row of `𝒱_n⁻¹`. -/
theorem coordProjZ_eq_vecMulVec (n : ℕ) (α : ℝ) (k : Fin n) :
    coordProjZ n α (2 * (k : ℕ))
      = Matrix.vecMulVec (fun s => blockSynth n α s (Sum.inl k))
          (fun t => (blockSynth n α)⁻¹ (Sum.inl k) t) := by
  rw [coordProjZ]
  have hfun : (fun s : Fin n ⊕ Fin n => if zIndex s = 2 * (k : ℕ) then (1 : ℂ) else 0)
      = fun s => if s = Sum.inl k then (1 : ℂ) else 0 := by
    funext s
    cases s with
    | inl j =>
      rw [show zIndex (Sum.inl j : Fin n ⊕ Fin n) = 2 * (j : ℕ) from rfl]
      by_cases h : j = k
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun hc => h (Fin.ext (by omega))), if_neg (by simp [h])]
    | inr j =>
      rw [show zIndex (Sum.inr j : Fin n ⊕ Fin n) = 2 * (j : ℕ) + 1 from rfl]
      rw [if_neg (by omega), if_neg (by simp)]
  rw [hfun]
  ext i t
  rw [Matrix.mul_assoc, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hentry : ∀ s, (Matrix.diagonal (fun s' : Fin n ⊕ Fin n =>
        if s' = Sum.inl k then (1 : ℂ) else 0) * (blockSynth n α)⁻¹) s t
      = if s = Sum.inl k then (blockSynth n α)⁻¹ s t else 0 := by
    intro s
    rw [Matrix.diagonal_mul]
    by_cases h : s = Sum.inl k
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  calc ∑ s, blockSynth n α i s * (Matrix.diagonal (fun s' : Fin n ⊕ Fin n =>
        if s' = Sum.inl k then (1 : ℂ) else 0) * (blockSynth n α)⁻¹) s t
      = ∑ s, (if s = Sum.inl k
          then blockSynth n α i s * (blockSynth n α)⁻¹ s t else 0) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hentry s]
        by_cases h : s = Sum.inl k
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, mul_zero]
    _ = blockSynth n α i (Sum.inl k) * (blockSynth n α)⁻¹ (Sum.inl k) t := by
        rw [Finset.sum_ite_eq' Finset.univ (Sum.inl k)
          (fun s => blockSynth n α i s * (blockSynth n α)⁻¹ s t)]
        rw [if_pos (Finset.mem_univ _)]

end PrefixZ

/-! ## The uniform bound `K_α` -/

section BasisConst

open scoped Matrix.Norms.L2Operator

theorem half_abs_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : |α / 2| < 1 / 2 := by
  rw [abs_of_pos (by linarith)]
  linarith

end BasisConst

/-! ## The orthonormal comparison basis and the variation multiplier

The proof of Proposition 2.1 compares the rotated basis against its `α = 0`
degeneration, the orthonormal basis `w_j` — in the grouped coordinates simply the
Hadamard rotation `rot2/√2`.  Three layers:

* `l2_opNorm_conj_rot2_diag_le` — the `α = 0` multiplier is bounded by `max |ξ|`
  (the parallelogram law makes `rot2/√2` an isometry);
* `l2_opNorm_prefixZ_sub_le` — `‖P_{n,k} - Q_{n,k}‖ ≤ 5α/(1-α)`: even indices from
  Lemma A.4 (`3α/(1-α)`), odd indices from the rank-one difference (`2α/(1-α)`);
* `l2_opNorm_multiplier_le` — the multiplier bound
  `‖Δ_ξ‖ ≤ max|ξ| + (5α/(1-α)) Var(ξ)`, by Abel summation against the *differences*
  `P_{n,k} - Q_{n,k}` (which telescope to `0` at `k = 2n`).
-/

section Multiplier

open scoped Matrix.Norms.L2Operator

/-- At `α = 0` the synthesis matrix degenerates to the Hadamard rotation. -/
theorem blockSynth_zero (n : ℕ) : blockSynth n 0 = rot2 n := by
  rw [blockSynth, rotSynth, rot2]
  norm_num [toeplitz_zero]

/-- The inverse of the `α = 0` synthesis matrix is `2⁻¹ • rot2`. -/
theorem blockSynth_zero_inv (n : ℕ) : (blockSynth n 0)⁻¹ = (2⁻¹ : ℂ) • rot2 n := by
  rw [blockSynth, rotSynth_inv, rot2]
  norm_num [toeplitz_zero]

theorem rot2_mulVec_inl {n : ℕ} (y : Fin n ⊕ Fin n → ℂ) (i : Fin n) :
    (rot2 n).mulVec y (Sum.inl i) = y (Sum.inl i) + y (Sum.inr i) := by
  have h : (rot2 n).mulVec y (Sum.inl i) = ∑ t, rot2 n (Sum.inl i) t * y t := rfl
  rw [h, Fintype.sum_sum_type]
  have h1 : ∑ j : Fin n, rot2 n (K := ℂ) (Sum.inl i) (Sum.inl j) * y (Sum.inl j)
      = y (Sum.inl i) := by
    simp [rot2, Matrix.one_apply]
  have h2 : ∑ j : Fin n, rot2 n (K := ℂ) (Sum.inl i) (Sum.inr j) * y (Sum.inr j)
      = y (Sum.inr i) := by
    simp [rot2, Matrix.one_apply]
  rw [h1, h2]

theorem rot2_mulVec_inr {n : ℕ} (y : Fin n ⊕ Fin n → ℂ) (i : Fin n) :
    (rot2 n).mulVec y (Sum.inr i) = y (Sum.inl i) - y (Sum.inr i) := by
  have h : (rot2 n).mulVec y (Sum.inr i) = ∑ t, rot2 n (Sum.inr i) t * y t := rfl
  rw [h, Fintype.sum_sum_type]
  have h1 : ∑ j : Fin n, rot2 n (K := ℂ) (Sum.inr i) (Sum.inl j) * y (Sum.inl j)
      = y (Sum.inl i) := by
    simp [rot2, Matrix.one_apply]
  have h2 : ∑ j : Fin n, rot2 n (K := ℂ) (Sum.inr i) (Sum.inr j) * y (Sum.inr j)
      = -y (Sum.inr i) := by
    simp [rot2, Matrix.one_apply]
  rw [h1, h2]
  ring

/-- **The parallelogram identity for the Hadamard rotation**:
`‖rot2 · y‖² = 2 ‖y‖²` in `ℓ²`. -/
theorem sum_sq_rot2_mulVec {n : ℕ} (y : Fin n ⊕ Fin n → ℂ) :
    ∑ s, ‖(rot2 n).mulVec y s‖ ^ 2 = 2 * ∑ s, ‖y s‖ ^ 2 := by
  rw [Fintype.sum_sum_type (fun s => ‖(rot2 n).mulVec y s‖ ^ 2),
    Fintype.sum_sum_type (fun s => ‖y s‖ ^ 2)]
  have hterm : ∀ i : Fin n,
      ‖(rot2 n).mulVec y (Sum.inl i)‖ ^ 2 + ‖(rot2 n).mulVec y (Sum.inr i)‖ ^ 2
        = 2 * (‖y (Sum.inl i)‖ ^ 2 + ‖y (Sum.inr i)‖ ^ 2) := by
    intro i
    rw [rot2_mulVec_inl, rot2_mulVec_inr]
    exact parallelogram_law_with_norm ℂ _ _
  calc (∑ i : Fin n, ‖(rot2 n).mulVec y (Sum.inl i)‖ ^ 2)
        + ∑ i : Fin n, ‖(rot2 n).mulVec y (Sum.inr i)‖ ^ 2
      = ∑ i : Fin n, (‖(rot2 n).mulVec y (Sum.inl i)‖ ^ 2
          + ‖(rot2 n).mulVec y (Sum.inr i)‖ ^ 2) := Finset.sum_add_distrib.symm
    _ = ∑ i : Fin n, 2 * (‖y (Sum.inl i)‖ ^ 2 + ‖y (Sum.inr i)‖ ^ 2) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = 2 * ((∑ i : Fin n, ‖y (Sum.inl i)‖ ^ 2) + ∑ i : Fin n, ‖y (Sum.inr i)‖ ^ 2) := by
        rw [← Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **The `α = 0` multiplier bound**: in the orthonormal basis `(w_j)`, a coordinate
multiplier is bounded by the sup of its symbol.

The Hadamard rotation scales the `ℓ²` norm by exactly `√2`
(`sum_sq_rot2_mulVec`), and the two factors `√2` and `2⁻¹·√2` cancel, so no
`√2`-normalisation is needed anywhere.  Everything is phrased in bare sums through
`l2_opNorm_le_of_sum_sq`, which keeps `EuclideanSpace` out of the elaboration. -/
theorem l2_opNorm_conj_rot2_diag_le {n : ℕ} (f : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ s : Fin n ⊕ Fin n, ‖f (zIndex s)‖ ≤ B) :
    ‖blockSynth n 0 * Matrix.diagonal (fun s => f (zIndex s)) * (blockSynth n 0)⁻¹‖
      ≤ B := by
  rw [blockSynth_zero_inv, blockSynth_zero]
  refine l2_opNorm_le_of_sum_sq hB fun x => ?_
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    Matrix.diagonal (fun s => f (zIndex s)) with hD
  set y : Fin n ⊕ Fin n → ℂ := ((2⁻¹ : ℂ) • rot2 (K := ℂ) n).mulVec x with hy
  set u : Fin n ⊕ Fin n → ℂ := D.mulVec y with hu
  -- the triple product acts as three successive `mulVec`s
  have hM : ∀ s, (∑ t, (rot2 (K := ℂ) n * D * ((2⁻¹ : ℂ) • rot2 (K := ℂ) n)) s t * x t)
      = (rot2 (K := ℂ) n).mulVec u s := by
    intro s
    have h1 : (rot2 (K := ℂ) n * D * ((2⁻¹ : ℂ) • rot2 (K := ℂ) n)).mulVec x
        = (rot2 (K := ℂ) n).mulVec u := by
      rw [hu, hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact congrFun h1 s
  -- the diagonal step loses at most `B`
  have hstepD : ∑ s, ‖u s‖ ^ 2 ≤ B ^ 2 * ∑ s, ‖y s‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [hu, hD, Matrix.mulVec_diagonal, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hf s) 2) (by positivity)
  -- the `2⁻¹ • rot2` step halves the squared norm
  have hstepY : ∑ s, ‖y s‖ ^ 2 = 1 / 2 * ∑ s, ‖x s‖ ^ 2 := by
    have hsm : y = (2⁻¹ : ℂ) • (rot2 (K := ℂ) n).mulVec x := by
      rw [hy, Matrix.smul_mulVec]
    have hpt : ∀ s, ‖y s‖ ^ 2 = 1 / 4 * ‖(rot2 (K := ℂ) n).mulVec x s‖ ^ 2 := by
      intro s
      rw [hsm]
      simp only [Pi.smul_apply, norm_smul, mul_pow]
      norm_num
    rw [Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) => hpt s, ← Finset.mul_sum,
      sum_sq_rot2_mulVec]
    ring
  calc ∑ s, ‖∑ t, (rot2 (K := ℂ) n * D * ((2⁻¹ : ℂ) • rot2 (K := ℂ) n)) s t * x t‖ ^ 2
      = ∑ s, ‖(rot2 (K := ℂ) n).mulVec u s‖ ^ 2 :=
        Finset.sum_congr rfl fun s _ => by rw [hM s]
    _ = 2 * ∑ s, ‖u s‖ ^ 2 := sum_sq_rot2_mulVec u
    _ ≤ 2 * (B ^ 2 * (1 / 2 * ∑ s, ‖x s‖ ^ 2)) := by
        rw [← hstepY]
        linarith
    _ = B ^ 2 * ∑ s, ‖x s‖ ^ 2 := by ring

/-! ### Entry-wise tails of the Toeplitz factors

`T_n(θ) - I` has entries `a_{i-j}(θ)` strictly below the diagonal, so each of its
columns and rows has squared `ℓ²` norm `∑_{r≥1} a_r(θ)²` — exactly the tails bounded
in `CoeffBounds.lean`.
-/

/-- The entries of `T_n(θ) - I`. -/
theorem toeplitz_sub_one_apply (θ : ℝ) {n : ℕ} (i k : Fin n) :
    toeplitz n ((θ : ℂ)) i k - (1 : Matrix (Fin n) (Fin n) ℂ) i k
      = ((if (k : ℕ) < (i : ℕ) then binomCoeff ((i : ℕ) - (k : ℕ)) θ else 0 : ℝ) : ℂ) := by
  by_cases hik : i = k
  · subst hik
    rw [toeplitz_apply_self, Matrix.one_apply_eq, sub_self, if_neg (lt_irrefl _)]
    norm_num
  · have hne : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    rw [Matrix.one_apply_ne hik, sub_zero, toeplitz_apply]
    by_cases h : (k : ℕ) ≤ (i : ℕ)
    · rw [if_pos h, if_pos (by omega), binomCoeff_ofReal]
    · rw [if_neg h, if_neg (by omega)]
      norm_num

/-- Squared `ℓ²` norm of a column of `T_n(θ) - I`, bounded by any tail bound. -/
theorem sum_sq_toeplitz_col_sub_le {θ C : ℝ}
    (hC : ∀ m : ℕ, ∑ r ∈ Icc 1 m, binomCoeff r θ ^ 2 ≤ C) {n : ℕ} (k : Fin n) :
    ∑ i : Fin n, ‖toeplitz n ((θ : ℂ)) i k - (1 : Matrix (Fin n) (Fin n) ℂ) i k‖ ^ 2
      ≤ C := by
  set g : ℕ → ℝ := fun i => if (k : ℕ) < i then binomCoeff (i - (k : ℕ)) θ ^ 2 else 0
    with hg
  have hsub : Finset.Ico ((k : ℕ) + 1) n ⊆ range n := fun i hi =>
    Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
  have hvanish : ∀ i ∈ range n, i ∉ Finset.Ico ((k : ℕ) + 1) n → g i = 0 := by
    intro i hi hinot
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hinot
    rcases hinot with h | h
    · simp only [hg]
      rw [if_neg (by omega)]
    · exact absurd hi (Nat.not_lt.mpr h)
  calc ∑ i : Fin n, ‖toeplitz n ((θ : ℂ)) i k - (1 : Matrix (Fin n) (Fin n) ℂ) i k‖ ^ 2
      = ∑ i ∈ range n, g i := by
        rw [← Fin.sum_univ_eq_sum_range g n]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [toeplitz_sub_one_apply, Complex.norm_real, Real.norm_eq_abs]
        simp only [hg]
        by_cases h : (k : ℕ) < (i : ℕ)
        · rw [if_pos h, if_pos h, sq_abs]
        · rw [if_neg h, if_neg h]
          norm_num
    _ = ∑ i ∈ Finset.Ico ((k : ℕ) + 1) n, g i := (Finset.sum_subset hsub hvanish).symm
    _ = ∑ r ∈ range (n - ((k : ℕ) + 1)), binomCoeff (r + 1) θ ^ 2 := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [hg]
        rw [if_pos (by omega), show (k : ℕ) + 1 + r - (k : ℕ) = r + 1 from by omega]
    _ = ∑ r ∈ Icc 1 (n - ((k : ℕ) + 1)), binomCoeff r θ ^ 2 :=
        sum_range_add_one_eq_sum_Icc (fun r => binomCoeff r θ ^ 2) _
    _ ≤ C := hC _

/-- Squared `ℓ²` norm of a row of `T_n(θ) - I`, bounded by any tail bound. -/
theorem sum_sq_toeplitz_row_sub_le {θ C : ℝ}
    (hC : ∀ m : ℕ, ∑ r ∈ Icc 1 m, binomCoeff r θ ^ 2 ≤ C) {n : ℕ} (i : Fin n) :
    ∑ j : Fin n, ‖toeplitz n ((θ : ℂ)) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
      ≤ C := by
  set f : ℕ → ℝ := fun j => if j < (i : ℕ) then binomCoeff ((i : ℕ) - j) θ ^ 2 else 0
    with hf
  have hsub : range (i : ℕ) ⊆ range n := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hvanish : ∀ j ∈ range n, j ∉ range (i : ℕ) → f j = 0 := by
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    simp only [hf]
    rw [if_neg (by omega)]
  calc ∑ j : Fin n, ‖toeplitz n ((θ : ℂ)) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
      = ∑ j ∈ range n, f j := by
        rw [← Fin.sum_univ_eq_sum_range f n]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [toeplitz_sub_one_apply, Complex.norm_real, Real.norm_eq_abs]
        simp only [hf]
        by_cases h : (j : ℕ) < (i : ℕ)
        · rw [if_pos h, if_pos h, sq_abs]
        · rw [if_neg h, if_neg h]
          norm_num
    _ = ∑ j ∈ range (i : ℕ), f j := (Finset.sum_subset hsub hvanish).symm
    _ = ∑ r ∈ range (i : ℕ), binomCoeff (r + 1) θ ^ 2 := by
        rw [← Finset.sum_range_reflect (fun r => f r) (i : ℕ)]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        simp only [hf]
        rw [if_pos (by omega), show (i : ℕ) - ((i : ℕ) - 1 - r) = r + 1 from by omega]
    _ = ∑ r ∈ Icc 1 (i : ℕ), binomCoeff r θ ^ 2 :=
        sum_range_add_one_eq_sum_Icc (fun r => binomCoeff r θ ^ 2) _
    _ ≤ C := hC _

/-- Pointwise Pythagoras substitute: when at every index either the reference vector
vanishes or the two vectors agree, the squared norms add up subadditively.  This
replaces the paper's orthogonality argument `‖v‖² = 1 + ‖v - w‖²` and needs no inner
products. -/
theorem sum_sq_le_add_of_support {ι : Type*} [Fintype ι] (b b₀ : ι → ℂ)
    (h : ∀ i, b₀ i = 0 ∨ b i = b₀ i) :
    ∑ i, ‖b i‖ ^ 2 ≤ (∑ i, ‖b₀ i‖ ^ 2) + ∑ i, ‖b i - b₀ i‖ ^ 2 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases h i with h0 | h1
  · rw [h0, sub_zero, norm_zero]
    simp
  · rw [h1, sub_self, norm_zero]
    simp

/-! ### The rotated basis versus the orthonormal one

`t_α` bounds the squared `ℓ²` distance between a column of `𝒱_n` and the
corresponding column of the Hadamard rotation, and likewise for the rows of the
inverse.  Everything is stated for the *scaled* matrices `blockSynth = √2 · 𝒱_n`,
where the two factors `√2` cancel in the rank-one product.
-/

/-- `t_α = 9α²/(8(1-α)) + α²/2`, the squared `ℓ²` tail budget: it bounds
`∑_{r ≥ 1} a_r(θ)²` simultaneously at `θ = α/2` and `θ = -α/2`. -/
noncomputable def tailSq (α : ℝ) : ℝ := 9 * α ^ 2 / (8 * (1 - α)) + α ^ 2 / 2

theorem tailSq_nonneg {α : ℝ} (hα1 : α < 1) : 0 ≤ tailSq α := by
  have h : (0 : ℝ) < 1 - α := by linarith
  rw [tailSq]
  positivity

/-- `t_α ≤ 13α²/(8(1-α))`, the form used in the final numeric estimate. -/
theorem tailSq_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    tailSq α ≤ 13 * α ^ 2 / (8 * (1 - α)) := by
  have h : (0 : ℝ) < 1 - α := by linarith
  have key : 13 * α ^ 2 / (8 * (1 - α)) - (9 * α ^ 2 / (8 * (1 - α)) + α ^ 2 / 2)
      = α ^ 3 / (2 * (1 - α)) := by
    field_simp
    ring
  have hpos : 0 ≤ α ^ 3 / (2 * (1 - α)) := by positivity
  rw [tailSq]
  linarith

theorem tail_half_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (m : ℕ) :
    ∑ r ∈ Icc 1 m, binomCoeff r (α / 2) ^ 2 ≤ 9 * α ^ 2 / (8 * (1 - α)) := by
  have h := sum_sq_binomCoeff_tail_pos (θ := α / 2) (by linarith) (by linarith) m
  have hne : (1 : ℝ) - α ≠ 0 := by
    have : (0 : ℝ) < 1 - α := by linarith
    exact ne_of_gt this
  rwa [show 9 * (α / 2) ^ 2 / (2 * (1 - 2 * (α / 2))) = 9 * α ^ 2 / (8 * (1 - α)) from by
    field_simp
    ring] at h

theorem tail_half_neg {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (m : ℕ) :
    ∑ r ∈ Icc 1 m, binomCoeff r (-(α / 2)) ^ 2 ≤ α ^ 2 / 2 := by
  have h := sum_sq_binomCoeff_tail_neg (θ := -(α / 2)) (by linarith) (by linarith) m
  rwa [show 2 * (-(α / 2)) ^ 2 = α ^ 2 / 2 from by ring] at h

/-- `blockSynth` in explicit block form. -/
theorem blockSynth_eq (n : ℕ) (α : ℝ) :
    blockSynth n α = fromBlocks (toeplitz n ((α / 2 : ℝ) : ℂ))
      (toeplitz n ((α / 2 : ℝ) : ℂ)) (toeplitz n (-((α / 2 : ℝ) : ℂ)))
      (-toeplitz n (-((α / 2 : ℝ) : ℂ))) := rfl

/-- `(blockSynth)⁻¹` in explicit block form. -/
theorem blockSynth_inv_eq (n : ℕ) (α : ℝ) :
    (blockSynth n α)⁻¹ = (2⁻¹ : ℂ) • fromBlocks (toeplitz n (-((α / 2 : ℝ) : ℂ)))
      (toeplitz n ((α / 2 : ℝ) : ℂ)) (toeplitz n (-((α / 2 : ℝ) : ℂ)))
      (-toeplitz n ((α / 2 : ℝ) : ℂ)) := by
  rw [blockSynth]
  exact rotSynth_inv n _ _

/-- The column of `blockSynth` differs from the Hadamard column by at most
`√t_α` in `ℓ²`. -/
theorem sum_sq_synthCol_sub_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (k : Fin n) :
    ∑ s : Fin n ⊕ Fin n,
        ‖blockSynth n α s (Sum.inl k) - blockSynth n 0 s (Sum.inl k)‖ ^ 2
      ≤ tailSq α := by
  rw [blockSynth_eq, blockSynth_zero, rot2, Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
  rw [toeplitz_neg_ofReal]
  have h1 := sum_sq_toeplitz_col_sub_le (θ := α / 2)
    (fun m => tail_half_pos hα0 hα1 m) k
  have h2 := sum_sq_toeplitz_col_sub_le (θ := -(α / 2))
    (fun m => tail_half_neg hα0 hα1 m) k
  rw [tailSq]
  linarith

/-- A column of the identity has squared `ℓ²` norm `1`. -/
theorem sum_sq_one_col {n : ℕ} (k : Fin n) :
    ∑ i : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i k‖ ^ 2 = 1 := by
  have h : ∀ i : Fin n,
      ‖(1 : Matrix (Fin n) (Fin n) ℂ) i k‖ ^ 2 = if i = k then (1 : ℝ) else 0 := by
    intro i
    by_cases hik : i = k
    · rw [if_pos hik, hik, Matrix.one_apply_eq]
      norm_num
    · rw [if_neg hik, Matrix.one_apply_ne hik]
      norm_num
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h i,
    Finset.sum_ite_eq' Finset.univ k (fun _ => (1 : ℝ))]
  simp

/-- A row of the identity has squared `ℓ²` norm `1`. -/
theorem sum_sq_one_row {n : ℕ} (k : Fin n) :
    ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) k j‖ ^ 2 = 1 := by
  have h : ∀ j : Fin n,
      ‖(1 : Matrix (Fin n) (Fin n) ℂ) k j‖ ^ 2 = if k = j then (1 : ℝ) else 0 := by
    intro j
    by_cases hkj : k = j
    · rw [if_pos hkj, hkj, Matrix.one_apply_eq]
      norm_num
    · rw [if_neg hkj, Matrix.one_apply_ne hkj]
      norm_num
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h j,
    Finset.sum_ite_eq Finset.univ k (fun _ => (1 : ℝ))]
  simp

/-- The Hadamard column has squared `ℓ²` norm `2`. -/
theorem sum_sq_synthCol_zero {n : ℕ} (k : Fin n) :
    ∑ s : Fin n ⊕ Fin n, ‖blockSynth n 0 s (Sum.inl k)‖ ^ 2 = 2 := by
  rw [blockSynth_zero, rot2, Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
  rw [sum_sq_one_col k]
  norm_num

/-- The row of `(blockSynth)⁻¹` differs from the Hadamard row by at most
`√(t_α)/2` in `ℓ²`. -/
theorem sum_sq_synthRow_sub_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (k : Fin n) :
    ∑ t : Fin n ⊕ Fin n,
        ‖(blockSynth n α)⁻¹ (Sum.inl k) t - (blockSynth n 0)⁻¹ (Sum.inl k) t‖ ^ 2
      ≤ tailSq α / 4 := by
  rw [blockSynth_inv_eq, blockSynth_zero_inv, rot2, Fintype.sum_sum_type]
  simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    smul_eq_mul, ← mul_sub, norm_mul, mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum, toeplitz_neg_ofReal]
  have h1 := sum_sq_toeplitz_row_sub_le (θ := -(α / 2))
    (fun m => tail_half_neg hα0 hα1 m) k
  have h2 := sum_sq_toeplitz_row_sub_le (θ := α / 2)
    (fun m => tail_half_pos hα0 hα1 m) k
  have hhalf : ‖(2⁻¹ : ℂ)‖ ^ 2 = 1 / 4 := by
    rw [norm_inv]
    norm_num
  rw [hhalf, tailSq]
  nlinarith [h1, h2]

/-- The Hadamard row has squared `ℓ²` norm `1/2`. -/
theorem sum_sq_synthRow_zero {n : ℕ} (k : Fin n) :
    ∑ t : Fin n ⊕ Fin n, ‖(blockSynth n 0)⁻¹ (Sum.inl k) t‖ ^ 2 = 1 / 2 := by
  rw [blockSynth_zero_inv, rot2, Fintype.sum_sum_type]
  simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    smul_eq_mul, norm_mul, mul_pow]
  have hhalf : ‖(2⁻¹ : ℂ)‖ ^ 2 = 1 / 4 := by
    rw [norm_inv]
    norm_num
  -- one `rw` rewrites both (identical) summands at once
  rw [← Finset.mul_sum, sum_sq_one_row k, hhalf]
  norm_num

/-- The row of `(blockSynth)⁻¹` has squared `ℓ²` norm at most `1/(2(1-α))`.

The paper obtains this from the orthogonality relation `‖v‖² = 1 + ‖v - w‖²`, using
`(T_n(θ)^* - I)e_j ⊥ e_j`.  Here the same bound comes from `sum_sq_le_add_of_support`,
which is the coordinatewise form of that step: the difference vanishes at the two
indices where the Hadamard row is supported, so the squared norms add termwise.

The point is not the constant but the *shape*.  The triangle inequality
`‖v‖ ≤ 1 + ‖v - w‖` would leave a cross term `√(t_α/2)`, irrational in `α`, and the
closing inequality would no longer be polynomial; with the squared form the goal
stays a polynomial inequality in `α` that `nlinarith` discharges. -/
theorem sum_sq_synthRow_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (k : Fin n) :
    ∑ t : Fin n ⊕ Fin n, ‖(blockSynth n α)⁻¹ (Sum.inl k) t‖ ^ 2
      ≤ 1 / (2 * (1 - α)) := by
  have hs : (0 : ℝ) < 1 - α := by linarith
  -- the support condition: off the diagonal the Hadamard row vanishes, on it the
  -- two rows agree because `T_n(θ)` is unitriangular
  have hsupp : ∀ t : Fin n ⊕ Fin n,
      (blockSynth n 0)⁻¹ (Sum.inl k) t = 0
        ∨ (blockSynth n α)⁻¹ (Sum.inl k) t = (blockSynth n 0)⁻¹ (Sum.inl k) t := by
    intro t
    cases t with
    | inl j =>
      by_cases h : k = j
      · subst h
        right
        rw [blockSynth_inv_eq, blockSynth_zero_inv, rot2]
        simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, smul_eq_mul]
        rw [toeplitz_apply_self, Matrix.one_apply_eq]
      · left
        rw [blockSynth_zero_inv, rot2]
        simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, smul_eq_mul]
        rw [Matrix.one_apply_ne h, mul_zero]
    | inr j =>
      by_cases h : k = j
      · subst h
        right
        rw [blockSynth_inv_eq, blockSynth_zero_inv, rot2]
        simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₂, smul_eq_mul]
        rw [toeplitz_apply_self, Matrix.one_apply_eq]
      · left
        rw [blockSynth_zero_inv, rot2]
        simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₂, smul_eq_mul]
        rw [Matrix.one_apply_ne h, mul_zero]
  have hsplit := sum_sq_le_add_of_support
    (fun t => (blockSynth n α)⁻¹ (Sum.inl k) t)
    (fun t => (blockSynth n 0)⁻¹ (Sum.inl k) t) hsupp
  have h0 := sum_sq_synthRow_zero (n := n) k
  have hd := sum_sq_synthRow_sub_le hα0 hα1 (n := n) k
  have ht := tailSq_le hα0.le hα1
  -- `1/2 + t_α/4 ≤ 1/(2(1-α))` reduces to `13α²/8 ≤ 2α`, true since `α < 1`
  have hkey : 1 / 2 + tailSq α / 4 ≤ 1 / (2 * (1 - α)) := by
    have hbound : tailSq α / 4 ≤ 13 * α ^ 2 / (32 * (1 - α)) := by
      have heq : 13 * α ^ 2 / (8 * (1 - α)) / 4 = 13 * α ^ 2 / (32 * (1 - α)) := by
        field_simp
        ring
      calc tailSq α / 4 ≤ 13 * α ^ 2 / (8 * (1 - α)) / 4 := by linarith
        _ = 13 * α ^ 2 / (32 * (1 - α)) := heq
    have hfinal : 1 / 2 + 13 * α ^ 2 / (32 * (1 - α)) ≤ 1 / (2 * (1 - α)) := by
      rw [← sub_nonneg]
      have heq : 1 / (2 * (1 - α)) - (1 / 2 + 13 * α ^ 2 / (32 * (1 - α)))
          = (16 * α - 13 * α ^ 2) / (32 * (1 - α)) := by
        field_simp
        ring
      rw [heq]
      refine div_nonneg ?_ (by positivity)
      nlinarith
    linarith
  linarith

/-! ### The rank-one (odd-index) difference -/

/-- Bilinear splitting of a difference of rank-one matrices. -/
theorem vecMulVec_sub_vecMulVec {ι κ : Type*}
    (a a₀ : ι → ℂ) (b b₀ : κ → ℂ) :
    Matrix.vecMulVec a b - Matrix.vecMulVec a₀ b₀
      = Matrix.vecMulVec (a - a₀) b + Matrix.vecMulVec a₀ (b - b₀) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.sub_apply]
  ring

/-- **The odd-index estimate**: the rank-one coordinate projections of
the rotated and the orthonormal basis differ by at most `2α/(1-α)`.

The paper's constant here is `√13/2 ≈ 1.803`.  The rounder `2` is proved instead,
which the budget still allows (even indices `3` plus odd indices `2` is exactly the
`5` of Proposition 2.1), and it is what makes the mechanization cheap: rather than
manipulating the sum of square roots `√t_α · ‖row‖ + √2 · √(t_α)/2`, the bound is
squared through `(P+Q)² ≤ 2(P²+Q²)`, which turns the whole step into the numeric
inequality `13/4 ≤ 4`.  That squaring is *exactly* tight against `√13/2` as `α → 0`
— the two terms become equal there — so it could not prove the paper's constant; it
has comfortable slack against `2`. -/
theorem l2_opNorm_coordProjZ_sub_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ}
    (k : Fin n) :
    ‖coordProjZ n α (2 * (k : ℕ)) - coordProjZ n 0 (2 * (k : ℕ))‖ ≤ 2 * α / (1 - α) := by
  have hs : (0 : ℝ) < 1 - α := by linarith
  set a : Fin n ⊕ Fin n → ℂ := fun s => blockSynth n α s (Sum.inl k) with ha
  set a₀ : Fin n ⊕ Fin n → ℂ := fun s => blockSynth n 0 s (Sum.inl k) with ha0'
  set b : Fin n ⊕ Fin n → ℂ := fun t => (blockSynth n α)⁻¹ (Sum.inl k) t with hb
  set b₀ : Fin n ⊕ Fin n → ℂ := fun t => (blockSynth n 0)⁻¹ (Sum.inl k) t with hb0'
  -- the two rank-one pieces
  have hsplit : coordProjZ n α (2 * (k : ℕ)) - coordProjZ n 0 (2 * (k : ℕ))
      = Matrix.vecMulVec (a - a₀) b + Matrix.vecMulVec a₀ (b - b₀) := by
    rw [coordProjZ_eq_vecMulVec, coordProjZ_eq_vecMulVec]
    exact vecMulVec_sub_vecMulVec a a₀ b b₀
  -- the four squared `ℓ²` quantities
  have hA : ∑ s, ‖(a - a₀) s‖ ^ 2 ≤ tailSq α := by
    have h := sum_sq_synthCol_sub_le hα0 hα1 (n := n) k
    exact h
  have hBd : ∑ t, ‖(b - b₀) t‖ ^ 2 ≤ tailSq α / 4 := by
    have h := sum_sq_synthRow_sub_le hα0 hα1 (n := n) k
    exact h
  have hA0 : ∑ s, ‖a₀ s‖ ^ 2 = 2 := sum_sq_synthCol_zero (n := n) k
  have hB : ∑ t, ‖b t‖ ^ 2 ≤ 1 / (2 * (1 - α)) := sum_sq_synthRow_le hα0 hα1 (n := n) k
  have htnn : 0 ≤ tailSq α := tailSq_nonneg hα1
  -- pass to the two products of square roots
  set P : ℝ := Real.sqrt (∑ s, ‖(a - a₀) s‖ ^ 2) * Real.sqrt (∑ t, ‖b t‖ ^ 2) with hP
  set Q : ℝ := Real.sqrt (∑ s, ‖a₀ s‖ ^ 2) * Real.sqrt (∑ t, ‖(b - b₀) t‖ ^ 2) with hQ
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  have hQnn : 0 ≤ Q := by rw [hQ]; positivity
  have hP2 : P ^ 2 ≤ tailSq α * (1 / (2 * (1 - α))) := by
    rw [hP, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    exact mul_le_mul hA hB (by positivity) htnn
  have hQ2 : Q ^ 2 ≤ 2 * (tailSq α / 4) := by
    rw [hQ, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hA0]
    exact mul_le_mul_of_nonneg_left hBd (by norm_num)
  -- the numeric core: `2(P² + Q²) ≤ (2α/(1-α))²`
  have hd2 : tailSq α ≤ 13 / 8 * (α / (1 - α)) ^ 2 := by
    have h1 := tailSq_le hα0.le hα1
    have heq : 13 * α ^ 2 / (8 * (1 - α)) ≤ 13 / 8 * (α / (1 - α)) ^ 2 := by
      rw [div_pow, ← sub_nonneg]
      have hkey : 13 / 8 * (α ^ 2 / (1 - α) ^ 2) - 13 * α ^ 2 / (8 * (1 - α))
          = 13 * α ^ 3 / (8 * (1 - α) ^ 2) := by
        field_simp
        ring
      rw [hkey]
      positivity
    linarith
  have hds : tailSq α / (1 - α) ≤ 13 / 8 * (α / (1 - α)) ^ 2 := by
    have h1 := tailSq_le hα0.le hα1
    have hstep : tailSq α / (1 - α) ≤ 13 * α ^ 2 / (8 * (1 - α)) / (1 - α) := by
      gcongr
    have heq : 13 * α ^ 2 / (8 * (1 - α)) / (1 - α) = 13 / 8 * (α / (1 - α)) ^ 2 := by
      rw [div_pow]
      field_simp
      try ring
    linarith [hstep, heq]
  have hsq : (P + Q) ^ 2 ≤ (2 * α / (1 - α)) ^ 2 := by
    have hpar : (P + Q) ^ 2 ≤ 2 * (P ^ 2 + Q ^ 2) := by nlinarith [sq_nonneg (P - Q)]
    have hbound : 2 * (P ^ 2 + Q ^ 2) ≤ tailSq α / (1 - α) + tailSq α := by
      have h1 : tailSq α * (1 / (2 * (1 - α))) = tailSq α / (1 - α) / 2 := by
        field_simp
      have h2 : 2 * (tailSq α / 4) = tailSq α / 2 := by ring
      rw [h1] at hP2
      rw [h2] at hQ2
      linarith
    have hfin : tailSq α / (1 - α) + tailSq α ≤ (2 * α / (1 - α)) ^ 2 := by
      have hexp : (2 * α / (1 - α)) ^ 2 = 4 * (α / (1 - α)) ^ 2 := by
        rw [div_pow, div_pow]
        ring
      rw [hexp]
      have hpos : (0 : ℝ) ≤ (α / (1 - α)) ^ 2 := sq_nonneg _
      linarith
    linarith
  -- conclude
  have hgoal : P + Q ≤ 2 * α / (1 - α) := by
    have hrhs : (0 : ℝ) ≤ 2 * α / (1 - α) := by positivity
    calc P + Q = Real.sqrt ((P + Q) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt ((2 * α / (1 - α)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 2 * α / (1 - α) := Real.sqrt_sq hrhs
  calc ‖coordProjZ n α (2 * (k : ℕ)) - coordProjZ n 0 (2 * (k : ℕ))‖
      = ‖Matrix.vecMulVec (a - a₀) b + Matrix.vecMulVec a₀ (b - b₀)‖ := by rw [hsplit]
    _ ≤ ‖Matrix.vecMulVec (a - a₀) b‖ + ‖Matrix.vecMulVec a₀ (b - b₀)‖ := norm_add_le _ _
    _ ≤ P + Q := add_le_add (l2_opNorm_vecMulVec_le _ _) (l2_opNorm_vecMulVec_le _ _)
    _ ≤ 2 * α / (1 - α) := hgoal

/-! ### The prefix difference and the multiplier bound -/

theorem sharpPrefixConst_neg (θ : ℝ) : sharpPrefixConst (-θ) = sharpPrefixConst θ := by
  rw [sharpPrefixConst, sharpPrefixConst, abs_neg]
  congr 1
  ring

theorem fromBlocks_sub_diag {ι κ : Type*}
    (A A' : Matrix ι ι ℂ) (D D' : Matrix κ κ ℂ) :
    Matrix.fromBlocks A 0 0 D - Matrix.fromBlocks A' 0 0 D'
      = Matrix.fromBlocks (A - A') 0 0 (D - D') := by
  ext s t
  cases s <;> cases t <;> simp

/-- `sharpPrefixConst (α/2) = 3α/(1-α²) ≤ 3α/(1-α)`. -/
theorem sharpPrefixConst_half_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    sharpPrefixConst (α / 2) ≤ 3 * α / (1 - α) := by
  have hs : (0 : ℝ) < 1 - α := by linarith
  have hs2 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hval : sharpPrefixConst (α / 2) = 3 * α / (1 - α ^ 2) := by
    rw [sharpPrefixConst, abs_of_pos (by linarith : (0 : ℝ) < α / 2)]
    rw [show (1 : ℝ) - 4 * (α / 2) ^ 2 = 1 - α ^ 2 from by ring]
    field_simp
    ring
  rw [hval, div_le_div_iff₀ hs2 hs]
  nlinarith

/-- **The even-index estimate**: `‖P_{n,2k} - Q_{n,2k}‖ ≤ 3α/(1-α)`, from Lemma A.4
applied in each of the two diagonal blocks at `θ = ±α/2`. -/
theorem l2_opNorm_prefixZ_sub_even_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n k : ℕ}
    (hk : k ≤ n) :
    ‖prefixZ n α (2 * k) - prefixZ n 0 (2 * k)‖ ≤ 3 * α / (1 - α) := by
  have hβ := half_abs_lt hα0 hα1
  have hγ : |(-(α / 2) : ℝ)| < 1 / 2 := by rw [abs_neg]; exact hβ
  -- at `α = 0` the two blocks are the bare prefix projections
  have hzero : prefixZ n 0 (2 * k)
      = Matrix.fromBlocks (prefixProj n k) 0 0 (prefixProj n k) := by
    rw [prefixZ_even]
    congr 1
    · rw [prefixConj]
      norm_num [toeplitz_zero]
    · rw [prefixConj]
      norm_num [toeplitz_zero]
  rw [prefixZ_even, hzero, fromBlocks_sub_diag]
  have h1 := l2_opNorm_prefixConj_sub_le hβ (n := n) (k := k) hk
  have h2 := l2_opNorm_prefixConj_sub_le hγ (n := n) (k := k) hk
  rw [sharpPrefixConst_neg] at h2
  rw [show ((-(α / 2) : ℝ) : ℂ) = -((α / 2 : ℝ) : ℂ) from by push_cast; ring] at h2
  have hle := sharpPrefixConst_half_le hα0 hα1
  exact l2_opNorm_fromBlocks_diag_le (by positivity) (h1.trans hle) (h2.trans hle)

/-- The coordinate-projection differences telescope to the prefix differences. -/
theorem sum_coordProjZ_sub (n : ℕ) (α : ℝ) (K : ℕ) :
    ∑ k ∈ range K, (coordProjZ n α k - coordProjZ n 0 k)
      = prefixZ n α K - prefixZ n 0 K := by
  rw [Finset.sum_sub_distrib, sum_coordProjZ, sum_coordProjZ]

/-- **Proposition 2.1, Step 2**: the rotated basis is uniformly close to the
orthonormal one, `sup_{k ≤ 2n} ‖P_{n,k} - Q_{n,k}‖ ≤ 5α/(1-α)`. -/
theorem l2_opNorm_prefixZ_sub_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {n k : ℕ}
    (hk : k ≤ 2 * n) :
    ‖prefixZ n α k - prefixZ n 0 k‖ ≤ 5 * α / (1 - α) := by
  have hs : (0 : ℝ) < 1 - α := by linarith
  have h3 : (0 : ℝ) ≤ 3 * α / (1 - α) := by positivity
  have h2 : (0 : ℝ) ≤ 2 * α / (1 - α) := by positivity
  have hsum : 3 * α / (1 - α) + 2 * α / (1 - α) = 5 * α / (1 - α) := by ring
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- even
    subst hm
    have hmn : m ≤ n := by omega
    calc ‖prefixZ n α (m + m) - prefixZ n 0 (m + m)‖
        = ‖prefixZ n α (2 * m) - prefixZ n 0 (2 * m)‖ := by rw [two_mul]
      _ ≤ 3 * α / (1 - α) := l2_opNorm_prefixZ_sub_even_le hα0 hα1 hmn
      _ ≤ 5 * α / (1 - α) := by linarith
  · -- odd
    subst hm
    have hmn : m < n := by omega
    have hsplit : prefixZ n α (2 * m + 1) - prefixZ n 0 (2 * m + 1)
        = (prefixZ n α (2 * m) - prefixZ n 0 (2 * m))
          + (coordProjZ n α (2 * m) - coordProjZ n 0 (2 * m)) := by
      rw [prefixZ_odd, prefixZ_odd]
      abel
    rw [hsplit]
    calc ‖(prefixZ n α (2 * m) - prefixZ n 0 (2 * m))
            + (coordProjZ n α (2 * m) - coordProjZ n 0 (2 * m))‖
        ≤ ‖prefixZ n α (2 * m) - prefixZ n 0 (2 * m)‖
          + ‖coordProjZ n α (2 * m) - coordProjZ n 0 (2 * m)‖ := norm_add_le _ _
      _ ≤ 3 * α / (1 - α) + 2 * α / (1 - α) := by
          refine add_le_add (l2_opNorm_prefixZ_sub_even_le hα0 hα1 hmn.le) ?_
          have h := l2_opNorm_coordProjZ_sub_le hα0 hα1 (⟨m, hmn⟩ : Fin n)
          simpa using h
      _ = 5 * α / (1 - α) := hsum

/-- **Proposition 2.1, Step 3 — the multiplier bound.**  For any symbol `f`,
```
‖Δ_f‖ ≤ max_k ‖f k‖ + (5α/(1-α)) · ∑_k ‖f (k+1) - f k‖ .
```
This is Abel summation against the *differences* `P_{n,k} - Q_{n,k}`, which vanish at
both ends, plus the `α = 0` bound `l2_opNorm_conj_rot2_diag_le` for the orthonormal
part.  Taking `f = λ` gives `‖A_n‖ ≤ 1 + 5α/(1-α)`, and `f = e^{t(λ+ω)}` gives the
exponentially decaying flow bound — both with the *same* constant `5`. -/
theorem l2_opNorm_multiplier_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ)
    (f : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hbd : ∀ s : Fin n ⊕ Fin n, ‖f (zIndex s)‖ ≤ B) :
    ‖∑ k ∈ range (2 * n), f k • coordProjZ n α k‖
      ≤ B + 5 * α / (1 - α) * ∑ k ∈ range (2 * n - 1), ‖f (k + 1) - f k‖ := by
  have hs : (0 : ℝ) < 1 - α := by linarith
  set E : ℕ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fun k => coordProjZ n α k - coordProjZ n 0 k with hE
  -- Abel summation against the prefix differences
  have hQ : ∀ k ∈ range (2 * n - 1), ‖∑ j ∈ range (k + 1), E j‖ ≤ 5 * α / (1 - α) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hE, sum_coordProjZ_sub]
    exact l2_opNorm_prefixZ_sub_le hα0 hα1 (by omega)
  have hzero : ∑ j ∈ range (2 * n), E j = 0 := by
    rw [hE, sum_coordProjZ_sub, prefixZ_full, prefixZ_full, sub_self]
  have habel := norm_sum_smul_le (2 * n) f E (5 * α / (1 - α)) hQ
  rw [hzero, norm_zero, mul_zero, zero_add] at habel
  -- the orthonormal part
  have hdiff : ∑ k ∈ range (2 * n), f k • E k
      = (∑ k ∈ range (2 * n), f k • coordProjZ n α k)
        - ∑ k ∈ range (2 * n), f k • coordProjZ n 0 k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hE, smul_sub]
  have hzeropart : ‖∑ k ∈ range (2 * n), f k • coordProjZ n 0 k‖ ≤ B := by
    rw [← conj_diagonal_zIndex_eq_sum n 0 f]
    exact l2_opNorm_conj_rot2_diag_le f hB hbd
  rw [hdiff] at habel
  have htri : ‖∑ k ∈ range (2 * n), f k • coordProjZ n α k‖
      ≤ ‖∑ k ∈ range (2 * n), f k • coordProjZ n 0 k‖
        + ‖(∑ k ∈ range (2 * n), f k • coordProjZ n α k)
            - ∑ k ∈ range (2 * n), f k • coordProjZ n 0 k‖ := by
    have h := norm_add_le (∑ k ∈ range (2 * n), f k • coordProjZ n 0 k)
      ((∑ k ∈ range (2 * n), f k • coordProjZ n α k)
        - ∑ k ∈ range (2 * n), f k • coordProjZ n 0 k)
    rwa [add_sub_cancel] at h
  linarith

end Multiplier

end InverseGenerator
