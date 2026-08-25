/-
Copyright (c) 2026 Emiel Lorist, Martin Meyries, Mark Veraar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, Martin Meyries, Mark Veraar
-/
import InverseGenerator.Toeplitz

/-!
# The partial-convolution identity (Lemma A.1)

The paper's Lemma A.1 (`eq:partial-convolution`) states that for `p ≥ 1`, `q ≥ 0` and
any `θ`,
```
∑ r ∈ range (q+1), a (p+q-r) θ * a r (-θ) = a p θ * (p / (p+q)) * a q (1-θ).
```
This is the key combinatorial step of the whole construction: it is exactly the
closed form of the block `R = C A⁻¹` appearing in the prefix projection
`T_n(θ) Π_{n,k} T_n(-θ)` of Lemma A.4, with `p = i - k` and `q = k - j`.

Note that `a q (1-θ)` appears on the right — the identity trades the *negative*
parameter `-θ` on the left for the *reflected* parameter `1-θ` on the right.
That reflection is what later forces the Schur-test range `|θ| < 1/2`, since the
kernel bound must control `a p θ` and `a q (1-θ)` simultaneously.

## Implementation notes

The identity is proved in the *cleared* form `convolution_mul`, multiplied
through by `(p+q)`, which needs **no** hypothesis on `p` (both sides vanish when
`p = 0`).  The paper's divided form is then `convolution`, which does require
`1 ≤ p` so that `(p+q) ≠ 0`.

The induction is on `q`, generalised over `p`, because the recursion
`R p (q+1) = R (p+1) q + a p θ * a (q+1) (-θ)` *increases* `p` while decreasing
`q`.  The arithmetic core of the step is the scalar identity
`p * (q+1-θ) = (q+1) * (θ+p) - θ * (p+q+1)`, which `linear_combination`
discharges after the three `a (·+1) ·` terms are eliminated by the peel
recursions from `Coefficients.lean`.
-/

namespace InverseGenerator

open Finset

variable {K : Type*} [Field K] [CharZero K]

/-- Lemma A.1 in cleared form: the identity multiplied through by `(p + q)`.

Stated this way it holds for **all** `p`, including `p = 0` where both sides are
zero, so the induction carries no side condition. -/
theorem convolution_mul (θ : K) : ∀ (q p : ℕ),
    ((p : K) + q) * ∑ r ∈ range (q + 1),
        binomCoeff (p + q - r) θ * binomCoeff r (-θ)
      = (p : K) * binomCoeff p θ * binomCoeff q (1 - θ) := by
  intro q
  induction q with
  | zero => intro p; simp
  | succ q ih =>
    intro p
    -- Split off the `r = q+1` term, whose index `p + (q+1) - (q+1)` collapses to `p`.
    rw [sum_range_succ, Nat.add_sub_cancel]
    -- Re-associate the remaining summand indices so they match `ih (p+1)`.
    simp only [show p + (q + 1) = p + 1 + q from by omega]
    have hIH := ih (p + 1)
    push_cast at hIH ⊢
    -- Eliminate the three `binomCoeff (·+1) ·` terms via the peel recursions.
    have h1 : ((p : K) + 1) * binomCoeff (p + 1) θ = binomCoeff p θ * (θ + p) :=
      binomCoeff_succ_mul_right p θ
    have h2 : ((q : K) + 1) * binomCoeff (q + 1) (-θ)
        = -θ * binomCoeff q (1 - θ) := binomCoeff_succ_mul_neg q θ
    have h3 : ((q : K) + 1) * binomCoeff (q + 1) (1 - θ)
        = binomCoeff q (1 - θ) * (1 - θ + q) := binomCoeff_succ_mul_right q (1 - θ)
    -- Multiply the goal by `(q+1)` so that h2 and h3 can be applied.
    refine mul_left_cancel₀ (cast_succ_ne_zero q) ?_
    linear_combination ((q : K) + 1) * hIH
      + ((q : K) + 1) * binomCoeff q (1 - θ) * h1
      + ((p : K) + (q : K) + 1) * binomCoeff p θ * h2
      - (p : K) * binomCoeff p θ * h3

/-- `(p : K) + q ≠ 0` when `1 ≤ p`, in a characteristic-zero field. -/
theorem cast_add_ne_zero {p q : ℕ} (hp : 1 ≤ p) : ((p : K) + q) ≠ 0 := by
  have h : ((p + q : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast at h
  exact h

/-- **Lemma A.1** (`eq:partial-convolution`), in the paper's form:
```
∑ r ∈ range (q+1), a (p+q-r) θ * a r (-θ) = a p θ * (p / (p+q)) * a q (1-θ).
```
This is the closed form of the matrix `R = C A⁻¹` appearing in the proof of
Lemma A.4. -/
theorem convolution (θ : K) (p q : ℕ) (hp : 1 ≤ p) :
    ∑ r ∈ range (q + 1), binomCoeff (p + q - r) θ * binomCoeff r (-θ)
      = binomCoeff p θ * ((p : K) / ((p : K) + q)) * binomCoeff q (1 - θ) := by
  have hne : ((p : K) + q) ≠ 0 := cast_add_ne_zero hp
  have h := convolution_mul θ q p
  field_simp
  linear_combination h

/-! ## The prefix projection in block form

Lemma A.1 is exactly the closed form of the lower-left block of
`T_n(θ) P_k T_n(-θ)`.  Making that identification is what turns the combinatorial
identity into a statement about *operators*, and it is where the Schur test will be
applied.

The three lemmas below cover the three regions of the matrix, giving the block
picture used in the proof of Lemma A.4:
```
T_n(θ) P_k T_n(-θ) = [[I, 0], [R, 0]].
```
-/

open Matrix

/-- The closed form of the lower-left block `R = C A⁻¹`, as a function
of the shifted indices `p = i - k + 1 ≥ 1` and `q = k - j - 1 ≥ 0`. -/
noncomputable def schurKernel (θ : K) (p q : ℕ) : K :=
  binomCoeff p θ * ((p : K) / ((p : K) + q)) * binomCoeff q (1 - θ)

/-- The orthogonal projection onto the first `k` coordinates. -/
noncomputable def prefixProj (n k : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun i => if (i : ℕ) < k then 1 else 0

/-- `T_n(θ) P_k T_n(-θ)`, the prefix projection of the fractional basis
`x_j = T_n(θ) e_j`.  Lemma A.4 bounds its distance to `P_k` uniformly in both `n`
and `k`, which is possible exactly when `|θ| < 1/2`. -/
noncomputable def prefixConj (n k : ℕ) (θ : K) : Matrix (Fin n) (Fin n) K :=
  toeplitz n θ * prefixProj n k * toeplitz n (-θ)

omit [CharZero K] in
/-- Entrywise form: the diagonal projection contributes a single indicator factor. -/
theorem prefixConj_apply {n : ℕ} (k : ℕ) (θ : K) (i j : Fin n) :
    prefixConj n k θ i j
      = ∑ l : Fin n, toeplitz n θ i l * (if (l : ℕ) < k then 1 else 0)
          * toeplitz n (-θ) l j := by
  rw [prefixConj, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by
    simp only [prefixProj, Matrix.mul_diagonal]

omit [CharZero K] in
/-- Right-hand block: columns `j ≥ k` of `T_n(θ) P_k T_n(-θ)` vanish. -/
theorem prefixConj_apply_right {n : ℕ} (k : ℕ) (θ : K) (i j : Fin n)
    (hj : k ≤ (j : ℕ)) :
    prefixConj n k θ i j = 0 := by
  rw [prefixConj_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hlk : (l : ℕ) < k
  · rw [toeplitz_apply_of_lt (-θ) (show (l : ℕ) < (j : ℕ) from by omega), mul_zero]
  · rw [if_neg hlk, mul_zero, zero_mul]

/-- Top-left block: on rows `i < k` the projection acts as the identity.

No hypothesis on `j` is needed.  For `j < k` this is the identity block; for `j ≥ k`
it agrees with `prefixConj_apply_right`, since then `i < k ≤ j` forces `i ≠ j` and
both sides vanish. -/
theorem prefixConj_apply_upper {n : ℕ} (k : ℕ) (θ : K) (i j : Fin n)
    (hi : (i : ℕ) < k) :
    prefixConj n k θ i j = if i = j then 1 else 0 := by
  rw [prefixConj_apply]
  have hstep : ∀ l : Fin n,
      toeplitz n θ i l * (if (l : ℕ) < k then 1 else 0) * toeplitz n (-θ) l j
        = toeplitz n θ i l * toeplitz n (-θ) l j := by
    intro l
    by_cases hli : (l : ℕ) ≤ (i : ℕ)
    · rw [if_pos (show (l : ℕ) < k from by omega), mul_one]
    · rw [toeplitz_apply_of_lt θ (show (i : ℕ) < (l : ℕ) from by omega), zero_mul]
  rw [Finset.sum_congr rfl fun l _ => hstep l, ← Matrix.mul_apply, toeplitz_mul_neg,
    Matrix.one_apply]

/-- **The lower-left block**: on rows `i ≥ k` and columns `j < k`, the prefix
conjugate `T_n(θ) P_k T_n(-θ)` is exactly the closed-form kernel of Lemma A.1, at
`p = i - k + 1` and `q = k - j - 1`. -/
theorem prefixConj_apply_lower {n : ℕ} (k : ℕ) (θ : K) (hk : k ≤ n) (i j : Fin n)
    (hi : k ≤ (i : ℕ)) (hj : (j : ℕ) < k) :
    prefixConj n k θ i j
      = schurKernel θ ((i : ℕ) - k + 1) (k - (j : ℕ) - 1) := by
  rw [prefixConj_apply]
  -- Rewrite the summand as a function of `(l : ℕ)`.
  have hstep : ∀ l : Fin n,
      toeplitz n θ i l * (if (l : ℕ) < k then 1 else 0) * toeplitz n (-θ) l j
        = ((if (l : ℕ) ≤ (i : ℕ) then binomCoeff ((i : ℕ) - (l : ℕ)) θ else 0)
            * (if (l : ℕ) < k then 1 else 0))
          * (if (j : ℕ) ≤ (l : ℕ) then binomCoeff ((l : ℕ) - (j : ℕ)) (-θ) else 0) := by
    intro l
    rw [toeplitz_apply, toeplitz_apply]
  rw [Finset.sum_congr rfl fun l _ => hstep l]
  rw [Fin.sum_univ_eq_sum_range (fun l =>
    ((if l ≤ (i : ℕ) then binomCoeff ((i : ℕ) - l) θ else 0) * (if l < k then 1 else 0))
      * (if (j : ℕ) ≤ l then binomCoeff (l - (j : ℕ)) (-θ) else 0)) n]
  -- The support is `Ico j k`: `l < k` from the projection, `j ≤ l` from `T(-θ)`,
  -- and `l ≤ i` is automatic since `l < k ≤ i`.
  have hsub : Finset.Ico (j : ℕ) k ⊆ Finset.range n := fun l hl =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hl).2 hk)
  rw [← Finset.sum_subset hsub (by
    intro l _ hl
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hl
    rcases hl with hl | hl
    · rw [if_neg (by omega : ¬ (j : ℕ) ≤ l), mul_zero]
    · rw [if_neg (by omega : ¬ l < k), mul_zero, zero_mul])]
  -- On `Ico j k` all three guards resolve.
  rw [Finset.sum_congr rfl (fun l hl => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hl
    rw [if_pos (by omega : l ≤ (i : ℕ)), if_pos h2, if_pos h1, mul_one])]
  -- Abbreviate `p` and `q` *before* reindexing: rewriting `k - j` to `q + 1` would
  -- otherwise also fire inside `k - j - 1` on the right-hand side.
  set p := (i : ℕ) - k + 1 with hpdef
  set q := k - (j : ℕ) - 1 with hqdef
  rw [Finset.sum_Ico_eq_sum_range, show k - (j : ℕ) = q + 1 from by omega]
  -- Now it is `convolution` at `p = i - k + 1`, `q = k - j - 1`.
  rw [schurKernel, ← convolution θ p q (by omega)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Nat.add_sub_cancel_left, show (i : ℕ) - ((j : ℕ) + r) = p + q - r from by omega]

end InverseGenerator
