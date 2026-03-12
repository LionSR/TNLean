/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Spectral.MixedTransfer
import TNLean.Spectral.TraceExpansion
import TNLean.MPS.Transfer
import TNLean.Wielandt.PrimitivePaper
import TNLean.MPS.PeripheralToSpectralGap
import TNLean.MPS.IrreducibleFormII
import TNLean.Wielandt.PrimitivityToNormal
import TNLean.Channel.Primitive
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Proposition 3(c)→(b): Strong irreducibility implies eventually full Kraus rank

This file proves the **(c) → (b)** implication of Proposition 3 in
Sanz–Pérez-García–Wolf–Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347):

> If the transfer map `E_A` is strongly irreducible (positive-definite fixed
> point, irreducible, unique peripheral eigenvalue `{1}`), then `A` has
> eventually full Kraus rank (i.e., word products eventually span `M_D(ℂ)`).

## Proof strategy (following the paper / Wolf Ch6)

1. **Trace-pairing identity** (`sum_normSq_trace_conjTranspose_mul_evalWord`):
   $$\sum_{|\sigma|=n} |\operatorname{tr}(B^\dagger A_\sigma)|^2 =
   \operatorname{Re}\Bigl(\sum_{i,k} [B^\dagger \mathcal E^n(e_{ik}) B]_{ik}\Bigr)$$

2. **Primitivity bridge**: From strong irreducibility, derive `IsPrimitiveMPS A ρ`
   with the *original* positive-definite fixed point `ρ`.

3. **Convergence**: The complementary map `(E - P_ρ)^n → 0` in operator norm,
   so `E^n → P_ρ` pointwise (where `P_ρ(X) = (tr X / tr ρ) • ρ`).

4. **Contradiction**: If `wordSpan A n ≠ ⊤`, then `∃ B ≠ 0` orthogonal (in
   trace pairing) to all words of length `n`. The LHS vanishes while the RHS
   converges to `tr(B† ρ B) / tr(ρ) > 0`, contradiction for large `n`.

## Main results

* `sum_normSq_trace_conjTranspose_mul_evalWord` — the trace-pairing identity
* `isPrimitiveMPS_of_isStronglyIrreduciblePaper` — primitivity bridge
* `IsPrimitiveMPS.transferMap_pow_apply_tendsto` — convergence `E^n → P_ρ`
* `eq_zero_of_trace_conjTranspose_mul_posDef_mul_eq_zero` — PosDef nondegeneracy

## Remaining step for the full `hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper`

The final assembly needs a **uniform convergence** step: showing that the RHS of the
trace-pairing identity is eventually positive for *all* nonzero `B` simultaneously
(not just for each fixed `B`). This is a standard finite-dimensional analysis
argument — either via norm bounds on the error bilinear form, or via the openness of
the positive-definite cone in the space of quadratic forms — and is the sole
remaining gap.

## References

- [Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347], Proposition 3
- [Wolf, *Quantum Channels & Operations: Guided Tour*], §6.2–6.4
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix Filter

namespace MPSTensor

variable {d D : ℕ}

/-! ### Part 1: Trace-pairing identity -/

/-- Complex-valued form of the trace-pairing identity:
`∑_σ tr(B† A_σ) · star(tr(B† A_σ)) = ∑_{i,k} [B† · E^n(e_{ik}) · B]_{ik}`.

This is the raw algebraic content before extracting the real part. -/
private theorem sum_trace_mul_star_eq [NeZero D]
    (A : MPSTensor d D) (n : ℕ)
    (B : Matrix (Fin D) (Fin D) ℂ) :
    (∑ σ : Fin n → Fin d,
        Matrix.trace (Bᴴ * evalWord A (List.ofFn σ)) *
          star (Matrix.trace (Bᴴ * evalWord A (List.ofFn σ)))) =
      ∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * ((transferMap (d := d) (D := D) A) ^ n)
          (Matrix.single i k 1) * B) i k := by
  -- Expand E^n(e_{ik}) = ∑_σ A_σ * e_{ik} * A_σᴴ
  simp only [transferMap_pow_apply' A n]
  -- Step 1: Push B† and B through the σ-sum and extract entries.
  have hpush : ∀ (i k : Fin D),
      (Bᴴ * (∑ σ : Fin n → Fin d,
        evalWord A (List.ofFn σ) * Matrix.single i k (1 : ℂ) *
          (evalWord A (List.ofFn σ))ᴴ) * B) i k =
      ∑ σ : Fin n → Fin d,
        (Bᴴ * evalWord A (List.ofFn σ)) i i *
          ((evalWord A (List.ofFn σ))ᴴ * B) k k := by
    intro i k
    -- Distribute B† and B over the sum
    have hdist : Bᴴ * (∑ σ : Fin n → Fin d,
        evalWord A (List.ofFn σ) * Matrix.single i k 1 *
          (evalWord A (List.ofFn σ))ᴴ) * B =
        ∑ σ : Fin n → Fin d,
          Bᴴ * evalWord A (List.ofFn σ) * Matrix.single i k 1 *
            ((evalWord A (List.ofFn σ))ᴴ * B) := by
      rw [Matrix.mul_sum, Finset.sum_mul]
      congr 1; ext σ
      simp only [Matrix.mul_assoc]
    rw [hdist, Matrix.sum_apply]
    congr 1; ext σ
    exact entry_mul_single_mul
      (Bᴴ * evalWord A (List.ofFn σ))
      ((evalWord A (List.ofFn σ))ᴴ * B) i k
  simp_rw [hpush]
  -- Step 2: Swap sums so σ is outermost.
  rw [show (∑ i : Fin D, ∑ k : Fin D, ∑ σ : Fin n → Fin d,
        (Bᴴ * evalWord A (List.ofFn σ)) i i *
          ((evalWord A (List.ofFn σ))ᴴ * B) k k) =
      ∑ σ : Fin n → Fin d, ∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * evalWord A (List.ofFn σ)) i i *
          ((evalWord A (List.ofFn σ))ᴴ * B) k k from by
    simpa using Finset.sum_comm_cycle
      (s := (Finset.univ : Finset (Fin D)))
      (t := (Finset.univ : Finset (Fin D)))
      (u := (Finset.univ : Finset (Fin n → Fin d)))
      (f := fun i k σ =>
        (Bᴴ * evalWord A (List.ofFn σ)) i i *
          ((evalWord A (List.ofFn σ))ᴴ * B) k k)]
  -- Step 3: Factor double sum into product of traces.
  congr 1; ext σ
  -- ∑_{ik} M_{ii} * N_{kk} = (∑_i M_{ii}) * (∑_k N_{kk})
  have hfactor :
      ∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * evalWord A (List.ofFn σ)) i i *
          ((evalWord A (List.ofFn σ))ᴴ * B) k k =
      (∑ i, (Bᴴ * evalWord A (List.ofFn σ)) i i) *
        (∑ k, ((evalWord A (List.ofFn σ))ᴴ * B) k k) := by
    simpa using (Fintype.sum_mul_sum
      (f := fun i : Fin D => (Bᴴ * evalWord A (List.ofFn σ)) i i)
      (g := fun k : Fin D => ((evalWord A (List.ofFn σ))ᴴ * B) k k)).symm
  rw [hfactor]
  -- (∑_i M_{ii}) = Matrix.trace M
  change Matrix.trace (Bᴴ * evalWord A (List.ofFn σ)) *
    star (Matrix.trace (Bᴴ * evalWord A (List.ofFn σ))) =
    Matrix.trace (Bᴴ * evalWord A (List.ofFn σ)) *
      Matrix.trace ((evalWord A (List.ofFn σ))ᴴ * B)
  -- tr(A_σ† B) = star(tr(B† A_σ)) by Matrix.trace_conjTranspose
  congr 1
  rw [← Matrix.trace_conjTranspose (Bᴴ * evalWord A (List.ofFn σ))]
  simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- **Trace-pairing identity for transfer-map powers.**

The sum of squared absolute traces `∑_σ |tr(B† A_σ)|²` equals the `.re` of a
bilinear form in `B` built from the iterated transfer map and matrix units.

This is the core algebraic identity used in the proof of
**Proposition 3(c)→(b)** of arXiv:0909.5347 (the "quantum Wielandt" paper). -/
theorem sum_normSq_trace_conjTranspose_mul_evalWord
    [NeZero D]
    (A : MPSTensor d D) (n : ℕ)
    (B : Matrix (Fin D) (Fin D) ℂ) :
    (∑ σ : Fin n → Fin d,
        ‖Matrix.trace (Bᴴ * evalWord A (List.ofFn σ))‖ ^ 2 : ℝ) =
      (∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * ((transferMap (d := d) (D := D) A) ^ n)
          (Matrix.single i k 1) * B) i k).re := by
  -- Rewrite LHS: ‖z‖² = (z * star z).re since z * star z = ↑(‖z‖²)
  have hlhs : (∑ σ : Fin n → Fin d,
      ‖Matrix.trace (Bᴴ * evalWord A (List.ofFn σ))‖ ^ 2 : ℝ) =
    (∑ σ : Fin n → Fin d,
      Matrix.trace (Bᴴ * evalWord A (List.ofFn σ)) *
        star (Matrix.trace (Bᴴ * evalWord A (List.ofFn σ)))).re := by
    rw [Complex.re_sum]
    congr 1; ext σ
    have : star (Matrix.trace (Bᴴ * evalWord A (List.ofFn σ))) =
        (starRingEnd ℂ) (Matrix.trace (Bᴴ * evalWord A (List.ofFn σ))) :=
      (starRingEnd_apply _).symm
    rw [this, Complex.mul_conj']
    norm_cast
  rw [hlhs, sum_trace_mul_star_eq]

/-! ### Part 2: Primitivity bridge

From `IsStronglyIrreduciblePaper A` + left-canonical normalization, we derive
`IsPrimitiveMPS A ρ` with the *same* positive-definite fixed point `ρ` from the
definition.  The proof chains:

1. `IsIrreducibleMap E` → `IsIrreducibleTensor A`
2. `IsIrreducibleTensor` → unique trace-zero fixed point (`huniq_fp`)
3. `huniq_fp` + `IsChannelPrimitive` → spectral gap (complement spectral radius < 1)
4. Package as `IsPrimitiveMPS A ρ`
-/

/-- **Primitivity bridge**: strong irreducibility implies the spectral-gap
predicate `IsPrimitiveMPS A ρ` for some positive-definite `ρ`.

This is the key structural step in the (c) → (b) direction: it connects the
paper's spectral characterization (peripheral eigenvalues = {1} + irreducible
+ PosDef fixed point) to the operational spectral-gap hypothesis used by the
convergence theory.

The proof chains:
1. `IsIrreducibleMap E → IsIrreducibleTensor A`
2. `IsIrreducibleTensor + IsChannelPrimitive + hNorm → IsPrimitive A`
   (via `isPrimitive_of_peripheralPrimitive_of_irreducible`)
3. Every nonzero PSD fixed point of an irreducible transfer map is PosDef
   (via `posSemidef_fixedPoint_isPosDef_of_irreducible`)
-/
theorem isPrimitiveMPS_of_isStronglyIrreduciblePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hSI : IsStronglyIrreduciblePaper A) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, IsPrimitiveMPS A ρ ∧ ρ.PosDef := by
  -- Extract components
  obtain ⟨_, _, _, hPrim, hIrrMap⟩ := hSI
  -- Step 1: IsIrreducibleMap → IsIrreducibleTensor
  have hIrrT : IsIrreducibleTensor A := isIrreducibleTensor_of_isIrreducibleMap A hIrrMap
  -- Step 2: Peripheral primitivity + irreducibility → IsPrimitive (spectral-gap form)
  obtain ⟨ρ', hPrimMPS⟩ := isPrimitive_of_peripheralPrimitive_of_irreducible A hIrrT hNorm hPrim
  -- Step 3: The fixed point is PosDef (irreducibility + PSD + nonzero → PosDef)
  have hρ'PD : ρ'.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible A hIrrMap ρ'
      hPrimMPS.fixedPoint_psd hPrimMPS.fixedPoint_ne_zero hPrimMPS.fixedPoint_is_fixed
  exact ⟨ρ', hPrimMPS, hρ'PD⟩

/-! ### Part 3: Convergence of the transfer map

Pointwise convergence: `E^n(X) → (tr X / tr ρ) • ρ`.

This is a public version of the private `transferMap_pow_tendsto` from
`PrimitiveImpliesIrreducible.lean`. -/

/-- **Transfer-map powers converge pointwise**: for a primitive MPS tensor,
`E^(n+1)(X) → (tr X / tr ρ) • ρ` for any matrix `X`.

This follows from the decomposition `E^(n+1) = P_ρ + (E − P_ρ)^(n+1)` where the
complementary part decays in operator norm. -/
theorem IsPrimitiveMPS.transferMap_pow_apply_tendsto [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun n => ((transferMap (d := d) (D := D) A) ^ (n + 1)) X)
      atTop (nhds ((Matrix.trace X / Matrix.trace ρ) • ρ)) := by
  set E := transferMap (d := d) (D := D) A
  set Pρ := fixedPointProj (D := D) ρ hP.trace_ne_zero
  set N := E - Pρ
  have hTP : IsTracePreservingMap E := hP.transferMap_isChannel.tp
  have hρfix : E ρ = ρ := hP.fixedPoint_is_fixed
  -- E^(n+1) = Pρ + N^(n+1)
  have hdecomp : ∀ n, (E ^ (n + 1)) X = Pρ X + (N ^ (n + 1)) X := by
    intro n
    have h := pow_succ_eq_fixedPointProj_add_compl_pow
      (E := E) (ρ := ρ) (htr := hP.trace_ne_zero) hTP hρfix n
    calc (E ^ (n + 1)) X
        = ((Pρ + N ^ (n + 1)) : Module.End ℂ _) X := by rw [← h]
      _ = Pρ X + (N ^ (n + 1)) X := LinearMap.add_apply Pρ (N ^ (n + 1)) X
  simp_rw [hdecomp]
  rw [show Pρ X = (Matrix.trace X / Matrix.trace ρ) • ρ from rfl]
  -- Need: N^(n+1)(X) → 0
  suffices h : Tendsto (fun n => (N ^ (n + 1)) X) atTop (nhds 0) by
    have := h.const_add ((Matrix.trace X / Matrix.trace ρ) • ρ)
    simp only [add_zero] at this; exact this
  -- Use complement_pow_tendsto_zero
  have hN_clm : Tendsto (fun n =>
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) N) ^ n)
      atTop (nhds 0) :=
    hP.complement_pow_tendsto_zero
  -- Evaluate at X to get pointwise convergence
  have heval := (ContinuousLinearMap.apply ℂ (Matrix (Fin D) (Fin D) ℂ) X).continuous.tendsto
    (0 : (Matrix (Fin D) (Fin D) ℂ) →L[ℂ] (Matrix (Fin D) (Fin D) ℂ))
  rw [map_zero] at heval
  have hconv := heval.comp hN_clm
  -- Convert ContinuousLinearMap powers to LinearMap powers
  suffices hsuff : ∀ n,
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) N ^ (n + 1)) X
      = (N ^ (n + 1)) X by
    simp_rw [← hsuff]
    exact hconv.comp (tendsto_add_atTop_nat 1)
  intro n
  rw [(map_pow (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) N (n + 1)).symm]
  rfl

/-! ### Part 4: RHS bilinear form computation

We show that the trace-pairing RHS, when evaluated at the fixed-point projection
`P_ρ`, equals `tr(B† ρ B) / tr(ρ)`.  This is the limiting value of the
trace-pairing identity as `E^n → P_ρ`. -/

/-- The bilinear form from the trace-pairing identity, evaluated at a linear map `F`.
This extracts the complex number `∑_{i,k} (B† · F(e_{ik}) · B)_{ik}`. -/
private noncomputable def tracePairBilin [NeZero D]
    (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (B : Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ i : Fin D, ∑ k : Fin D,
    (Bᴴ * F (Matrix.single i k 1) * B) i k

/-- Linearity of `tracePairBilin` in the operator argument: Q_{F+G}(B) = Q_F(B) + Q_G(B). -/
private theorem tracePairBilin_add [NeZero D]
    (F G : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (B : Matrix (Fin D) (Fin D) ℂ) :
    tracePairBilin (F + G) B = tracePairBilin F B + tracePairBilin G B := by
  simp only [tracePairBilin, LinearMap.add_apply, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_apply, Finset.sum_add_distrib]

/-- The bilinear form evaluated at the fixed-point projection P_ρ(X) = (tr X / tr ρ) • ρ
equals `tr(B† ρ B) / tr(ρ)`. -/
private theorem tracePairBilin_fixedPointProj [NeZero D]
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : Matrix.trace ρ ≠ 0)
    (B : Matrix (Fin D) (Fin D) ℂ) :
    tracePairBilin (fixedPointProj (D := D) ρ htr) B =
      Matrix.trace (Bᴴ * ρ * B) / Matrix.trace ρ := by
  simp only [tracePairBilin, fixedPointProj, LinearMap.coe_mk, AddHom.coe_mk]
  -- Direct computation: each entry for i ≠ k vanishes; for i = k gives (B†ρB)_{ii}/tr(ρ)
  have hentry : ∀ (i k : Fin D),
      (Bᴴ * ((Matrix.trace (Matrix.single i k (1 : ℂ)) / Matrix.trace ρ) • ρ) * B) i k =
      if i = k then (Matrix.trace ρ)⁻¹ * (Bᴴ * ρ * B) i i else 0 := by
    intro i k
    split_ifs with h
    · subst h
      rw [Matrix.trace_single_eq_same i (1 : ℂ)]
      simp [one_div, Matrix.smul_apply, Matrix.mul_assoc]
    · rw [Matrix.trace_single_eq_of_ne i k (1 : ℂ) h]
      simp [zero_div, zero_smul]
  simp_rw [hentry]
  -- Kill off-diagonal terms in the inner sum
  have hinner : ∀ i : Fin D,
      ∑ k : Fin D, (if i = k then (Matrix.trace ρ)⁻¹ * (Bᴴ * ρ * B) i i else 0) =
      (Matrix.trace ρ)⁻¹ * (Bᴴ * ρ * B) i i := by
    intro i; simp [Finset.mem_univ]
  simp_rw [hinner, ← Finset.mul_sum]
  -- ρ.trace⁻¹ * ∑ i, (B†ρB) i i = (B†ρB).trace / ρ.trace
  -- ∑ i, M i i = M.trace, then use a⁻¹ * b = b / a
  change (Matrix.trace ρ)⁻¹ * Matrix.trace (Bᴴ * ρ * B) = Matrix.trace (Bᴴ * ρ * B) / Matrix.trace ρ
  ring

/-! ### Part 5: Nondegeneracy of the PosDef inner product

`tr(B† ρ B) > 0` when `ρ` is positive definite and `B ≠ 0`. -/

-- We need the auxiliary fact that ρ^{1/2} B = 0 implies B = 0 when ρ.PosDef.
-- And tr(B† ρ B) = tr(ρ^{1/2} B (ρ^{1/2} B)†) ≥ 0 with equality iff ρ^{1/2} B = 0.
-- For now we prove the strict positivity directly.

/-- `tr(B† ρ B).re ≥ 0` when `ρ` is positive semidefinite. -/
private theorem trace_conjTranspose_mul_posSemidef_mul_re_nonneg
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef)
    (B : Matrix (Fin D) (Fin D) ℂ) :
    0 ≤ (Matrix.trace (Bᴴ * ρ * B)).re := by
  have hpsd : (Bᴴ * ρ * B).PosSemidef := hρ.conjTranspose_mul_mul_same B
  exact (Complex.nonneg_iff.mp hpsd.trace_nonneg).1

/-- If `B ∈ (wordSpan A n)⊥` (in the trace pairing), then the LHS of
the trace-pairing identity vanishes. -/
private theorem sum_normSq_eq_zero_of_trace_ortho [NeZero D]
    (A : MPSTensor d D) (n : ℕ)
    (B : Matrix (Fin D) (Fin D) ℂ)
    (hB : ∀ σ : Fin n → Fin d,
      Matrix.trace (Bᴴ * evalWord A (List.ofFn σ)) = 0) :
    (∑ σ : Fin n → Fin d,
        ‖Matrix.trace (Bᴴ * evalWord A (List.ofFn σ))‖ ^ 2 : ℝ) = 0 := by
  apply Finset.sum_eq_zero
  intro σ _
  simp [hB σ]

/-! ### Part 6: Main theorem — strong irreducibility → eventually full Kraus rank

The proof follows the paper's contradiction argument:
1. From strong irreducibility, derive `IsPrimitiveMPS A ρ` with `ρ.PosDef`.
2. If `wordSpan A n ≠ ⊤` for all `n`, then for each `n` there exists `B_n ≠ 0`
   orthogonal to all words of length `n`.
3. The trace-pairing identity gives `tracePairBilin(E^n)(B_n).re = 0`.
4. But `E^n → P_ρ`, so the RHS converges to `tr(B_n† ρ B_n) / tr(ρ) > 0`.
5. The contradiction finishes the proof. -/

/-- **Nondegeneracy of the PosDef inner product.**
If `ρ` is positive definite and `tr(B† ρ B) = 0`, then `B = 0`.

This is the key positivity fact: the form `B ↦ tr(B† ρ B)` is nondegenerate
when `ρ` is PosDef. The proof uses the characterization of PosDef via
`star x ⬝ᵥ ρ *ᵥ x > 0` for `x ≠ 0`. -/
private theorem eq_zero_of_trace_conjTranspose_mul_posDef_mul_eq_zero
    {D : ℕ} [NeZero D]
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (B : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace (Bᴴ * ρ * B) = 0) :
    B = 0 := by
  classical
  -- B†ρB is PSD with trace 0, hence B†ρB = 0
  have hpsd : (Bᴴ * ρ * B).PosSemidef := hρ.posSemidef.conjTranspose_mul_mul_same B
  have hBρB : Bᴴ * ρ * B = 0 := hpsd.trace_eq_zero_iff.mp htr
  -- For any vector v: star(Bv) ⬝ᵥ ρ *ᵥ (Bv) = v† (B†ρB) v = 0
  -- Since ρ PosDef, Bv = 0 for all v, hence B = 0.
  ext i j
  -- Test with e_j (j-th standard basis vector)
  suffices h : B *ᵥ (Pi.single j 1) = 0 by
    have hi := congrFun h i
    -- (B *ᵥ e_j) i = ∑_k B i k * δ_{jk} = B i j
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, Pi.zero_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hi
    exact hi
  -- Suppose B *ᵥ e_j ≠ 0
  by_contra hw
  -- Then star(Bv) ⬝ᵥ ρ(Bv) > 0 by PosDef
  have hpos := hρ.dotProduct_mulVec_pos hw
  -- But star(Bv) ⬝ᵥ ρ(Bv) = v†(B†ρB)v = 0
  have : star (B *ᵥ Pi.single j 1) ⬝ᵥ ρ.mulVec (B *ᵥ Pi.single j 1) =
      star (Pi.single j (1 : ℂ)) ⬝ᵥ (Bᴴ * ρ * B).mulVec (Pi.single j 1) := by
    simp only [star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [this, hBρB] at hpos
  simp at hpos

end MPSTensor

