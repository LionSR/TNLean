/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Wielandt.Primitivity.ToNormal

/-!
# Primitive + PosDef ⟹ Irreducible Tensor

This file proves that a primitive MPS tensor with a positive-definite fixed point
has no nontrivial invariant orthogonal projection, i.e., it is an irreducible tensor.

## Main result

* `isIrreducibleTensor_of_isPrimitiveMPS_of_posDef`:
  `IsPrimitiveMPS A ρ → ρ.PosDef → IsIrreducibleTensor A`

This is the irreducibility half of the later primitive-to-normal bridge: the
complementary aperiodicity input is recovered from strong irreducibility
(peripheral spectrum `{1}`) in `ImpliesStronglyIrreducible.lean` /
`StronglyIrreducibleToFullRank.lean`.

## References

- Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Proposition 3
- Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, §2.3
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Filter MPSTensor

namespace MPSTensor

variable {d D : ℕ} [NeZero D]

/-! ## Key lemma: invariant projection blocks the transfer map -/

omit [NeZero D] in
/-- If `(1 - P) * X = 0` and `(1 - P) * A i * P = 0` for all `i`, then
`(1 - P) * transferMap A X = 0`. -/
private theorem one_sub_mul_transferMap_eq_zero
    (A : MPSTensor d D) {P X : Matrix (Fin D) (Fin D) ℂ}
    (hP_inv : ∀ i : Fin d, (1 - P) * A i * P = 0)
    (hX : (1 - P) * X = 0) :
    (1 - P) * transferMap (d := d) (D := D) A X = 0 := by
  classical
  simp only [transferMap_apply, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hPX : P * X = X := by
    have : (P + (1 - P)) * X = X := by simp [add_sub_cancel]
    rwa [add_mul, hX, add_zero] at this
  calc (1 - P) * (A i * X * (A i)ᴴ)
      = (1 - P) * (A i * (P * X) * (A i)ᴴ) := by rw [hPX]
    _ = ((1 - P) * A i * P) * X * (A i)ᴴ := by simp only [Matrix.mul_assoc]
    _ = 0 * X * (A i)ᴴ := by rw [hP_inv i]
    _ = 0 := by simp

omit [NeZero D] in
/-- By induction: `(1 - P) * E^n (P * X * P) = 0` for all `n`. -/
private theorem one_sub_mul_transferMap_pow_eq_zero
    (A : MPSTensor d D) {P : Matrix (Fin D) (Fin D) ℂ}
    (hP_idem : P * P = P)
    (hP_inv : ∀ i : Fin d, (1 - P) * A i * P = 0)
    (X : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    (1 - P) * ((transferMap (d := d) (D := D) A) ^ n) (P * X * P) = 0 := by
  set E := transferMap (d := d) (D := D) A
  induction n with
  | zero =>
    change (1 - P) * (P * X * P) = 0
    have h1P : (1 - P) * P = 0 := by
      have : (1 - P) * P = P - P * P := by noncomm_ring
      rw [this, hP_idem, sub_self]
    calc (1 - P) * (P * X * P) = ((1 - P) * P) * X * P := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1P]; simp
  | succ n ih =>
    -- E^(n+1) = E * E^n, so E^(n+1)(σ) = E(E^n(σ))
    change (1 - P) * (E ^ (n + 1)) (P * X * P) = 0
    rw [show (E ^ (n + 1)) (P * X * P) = E ((E ^ n) (P * X * P)) from by
      rw [pow_succ']; rfl]
    exact one_sub_mul_transferMap_eq_zero A hP_inv ih

/-! ## Convergence: E^n(σ) → (tr σ / tr ρ) • ρ -/

/-- For a primitive MPS tensor, `E^(n+1)(σ) → (tr σ / tr ρ) • ρ` for any `σ`. -/
private theorem transferMap_pow_tendsto
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ)
    (σ : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun n => ((transferMap (d := d) (D := D) A) ^ (n + 1)) σ)
      atTop (nhds ((trace σ / trace ρ) • ρ)) := by
  set E := transferMap (d := d) (D := D) A
  set Pρ := fixedPointProj (D := D) ρ hP.trace_ne_zero
  set N := E - Pρ
  have hTP : IsTracePreservingMap E := hP.transferMap_isChannel.tp
  have hρfix : E ρ = ρ := hP.fixedPoint_is_fixed
  -- E^(n+1) = Pρ + N^(n+1)
  have hdecomp : ∀ n, (E ^ (n + 1)) σ = Pρ σ + (N ^ (n + 1)) σ := by
    intro n
    have h := pow_succ_eq_fixedPointProj_add_compl_pow E hP.trace_ne_zero hTP hρfix n
    calc (E ^ (n + 1)) σ
        = ((Pρ + N ^ (n + 1)) : Module.End ℂ _) σ := by rw [← h]
      _ = Pρ σ + (N ^ (n + 1)) σ := LinearMap.add_apply Pρ (N ^ (n + 1)) σ
  simp_rw [hdecomp]
  rw [show Pρ σ = (trace σ / trace ρ) • ρ from rfl]
  -- Need: N^(n+1)(σ) → 0
  suffices h : Tendsto (fun n => (N ^ (n + 1)) σ) atTop (nhds 0) by
    have := h.const_add ((trace σ / trace ρ) • ρ)
    simp only [add_zero] at this; exact this
  -- Use complement_pow_tendsto_zero: Φ(N)^n → 0 in ContinuousLinearMap
  have hN_clm : Tendsto (fun n =>
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) N) ^ n)
      atTop (nhds 0) :=
    hP.complement_pow_tendsto_zero
  -- Evaluate at σ to get pointwise convergence
  have heval := (ContinuousLinearMap.apply ℂ (Matrix (Fin D) (Fin D) ℂ) σ).continuous.tendsto
    (0 : (Matrix (Fin D) (Fin D) ℂ) →L[ℂ] (Matrix (Fin D) (Fin D) ℂ))
  rw [map_zero] at heval
  have hconv := heval.comp hN_clm
  -- Convert ContinuousLinearMap powers to LinearMap powers
  suffices hsuff : ∀ n,
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) N ^ (n + 1)) σ
      = (N ^ (n + 1)) σ by
    simp_rw [← hsuff]
    exact hconv.comp (tendsto_add_atTop_nat 1)
  intro n
  rw [(map_pow (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) N (n + 1)).symm]
  rfl

/-! ## Trace positivity: tr(PρP) ≠ 0 when ρ.PosDef and P ≠ 0 -/

omit [NeZero D] in
/-- `P * ρ * P ≠ 0` when `P` is a nonzero Hermitian matrix and `ρ` is PosDef. -/
private theorem proj_mul_posDef_mul_proj_ne_zero
    {P ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP_herm : P.IsHermitian) (_hP_idem : P * P = P)
    (hP_ne : P ≠ 0)
    (hρ_pd : ρ.PosDef) :
    P * ρ * P ≠ 0 := by
  intro h0
  apply hP_ne
  -- Show P = 0 by showing P *ᵥ v = 0 for all v
  have hPv_zero : ∀ v : Fin D → ℂ, P *ᵥ v = 0 := by
    intro v
    by_contra hne
    set w := P *ᵥ v
    -- star w ⬝ᵥ (ρ *ᵥ w) > 0 since ρ.PosDef and w ≠ 0
    have hρ_pos : (0 : ℂ) < star w ⬝ᵥ (ρ.mulVec w) :=
      hρ_pd.dotProduct_mulVec_pos hne
    -- star v ⬝ᵥ ((PρP) *ᵥ v) = 0
    have h_zero : star v ⬝ᵥ ((P * ρ * P) *ᵥ v) = 0 := by
      rw [h0]; simp [zero_mulVec, dotProduct_zero]
    -- (PρP) *ᵥ v = P *ᵥ (ρ *ᵥ w)
    have h_expand : (P * ρ * P) *ᵥ v = P *ᵥ (ρ *ᵥ w) := by
      change (P * ρ * P) *ᵥ v = P *ᵥ (ρ *ᵥ (P *ᵥ v))
      rw [mulVec_mulVec, mulVec_mulVec]
    rw [h_expand] at h_zero
    -- Use adjoint: star v ⬝ᵥ (P *ᵥ z) = vecMul (star v) P ⬝ᵥ z
    rw [dotProduct_mulVec] at h_zero
    -- Show: vecMul (star v) P = star w
    -- From star_vecMul: star (vecMul u M) = M^H *ᵥ (star u)
    -- Apply to u = star v, M = P:
    -- star (vecMul (star v) P) = P^H *ᵥ (star (star v)) = P *ᵥ v = w
    have h_key : vecMul (star v) P = star w := by
      apply star_injective
      rw [star_star]
      have := star_vecMul P (star v)
      rw [star_star, hP_herm.eq] at this
      exact this
    rw [h_key] at h_zero
    -- h_zero : star w ⬝ᵥ (ρ *ᵥ w) = 0, contradiction
    linarith
  -- P *ᵥ v = 0 for all v ⟹ P = 0
  ext i j
  have h := congr_fun (hPv_zero (Pi.single j 1)) i
  simp only [mulVec, dotProduct, Pi.single_apply, mul_boole, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  simpa using h

omit [NeZero D] in
/-- `tr(P * ρ * P) ≠ 0` when `P` is a nonzero orthogonal projection and `ρ.PosDef`. -/
private theorem trace_proj_mul_posDef_ne_zero
    {P ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P)
    (hP_ne : P ≠ 0)
    (hρ_pd : ρ.PosDef) :
    trace (P * ρ * P) ≠ 0 := by
  intro h
  have hpsd : (P * ρ * P).PosSemidef := by
    have := hρ_pd.posSemidef.mul_mul_conjTranspose_same (B := P)
    rwa [hP_herm.eq] at this
  exact proj_mul_posDef_mul_proj_ne_zero hP_herm hP_idem hP_ne hρ_pd
    ((Matrix.PosSemidef.trace_eq_zero_iff hpsd).mp h)

/-! ## Main theorem -/

/-- **Primitive + PosDef ⟹ Irreducible Tensor.**

If an MPS tensor has a primitive transfer map with a positive-definite fixed point,
then the tensor is irreducible (has no nontrivial invariant orthogonal projection). -/
theorem isIrreducibleTensor_of_isPrimitiveMPS_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef) :
    IsIrreducibleTensor A := by
  rw [IsIrreducibleTensor]
  intro ⟨P, hP_proj, hP_ne0, hP_ne1, hP_inv⟩
  obtain ⟨hP_herm, hP_idem⟩ := hP_proj
  set E := transferMap (d := d) (D := D) A
  set σ := P * ρ * P
  -- Step 1: (1-P) * E^n(σ) = 0 for all n
  have hblock : ∀ n, (1 - P) * (E ^ n) σ = 0 :=
    one_sub_mul_transferMap_pow_eq_zero A hP_idem hP_inv ρ
  -- Step 2: E^(n+1)(σ) → (tr σ / tr ρ) • ρ
  have hconv := transferMap_pow_tendsto hPrim σ
  -- Step 3: limit is zero
  have hlim_zero : (1 - P) * ((trace σ / trace ρ) • ρ) = 0 := by
    have hseq : ∀ n, (1 - P) * ((E ^ (n + 1)) σ) = 0 := fun n => hblock (n + 1)
    have hmul_cont : Continuous (fun X : Matrix (Fin D) (Fin D) ℂ => (1 - P) * X) :=
      continuous_const.mul continuous_id
    have hmul_tendsto := hmul_cont.continuousAt.tendsto.comp hconv
    have hconst : Tendsto ((fun X => (1 - P) * X) ∘
        (fun n => (E ^ (n + 1)) σ)) atTop (nhds 0) := by
      have : ((fun X => (1 - P) * X) ∘ (fun n => (E ^ (n + 1)) σ))
          = fun _ => (0 : Matrix (Fin D) (Fin D) ℂ) := by
        funext n; exact hseq n
      rw [this]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hmul_tendsto hconst
  -- Step 4: tr(σ) / tr(ρ) ≠ 0
  have htr_ne : trace σ / trace ρ ≠ 0 :=
    div_ne_zero (trace_proj_mul_posDef_ne_zero hP_herm hP_idem hP_ne0 hPD)
      hPrim.trace_ne_zero
  -- Step 5: (1-P) * ρ = 0
  have hPρ : (1 - P) * ρ = 0 := by
    have : (trace σ / trace ρ) • ((1 - P) * ρ) = 0 := by
      rw [mul_smul_comm] at hlim_zero; exact hlim_zero
    exact (smul_eq_zero.mp this).resolve_left htr_ne
  -- Step 6: P = 1
  obtain ⟨u, hu⟩ := hPD.isUnit
  have h1 : (1 - P) * (u : Matrix (Fin D) (Fin D) ℂ) = 0 := hu ▸ hPρ
  have h1P_zero : 1 - P = 0 :=
    calc 1 - P = (1 - P) * 1 := (mul_one _).symm
      _ = (1 - P) * ((u : Matrix (Fin D) (Fin D) ℂ) *
            (↑u⁻¹ : Matrix (Fin D) (Fin D) ℂ)) := by rw [Units.mul_inv]
      _ = ((1 - P) * ↑u) * (↑u⁻¹ : Matrix (Fin D) (Fin D) ℂ) :=
          (Matrix.mul_assoc _ _ _).symm
      _ = 0 * (↑u⁻¹ : Matrix (Fin D) (Fin D) ℂ) := by rw [h1]
      _ = 0 := Matrix.zero_mul _
  exact hP_ne1 (sub_eq_zero.mp h1P_zero).symm

end MPSTensor
