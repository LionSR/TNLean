/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Primitive blocked tensors

This file proves that blocking preserves tensor irreducibility for TP-primitive
irreducible blocks, and derives related structural properties of blocked tensors
in the normal-canonical-form setting.

## Main statements

* `isIrreducibleTensor_blockTensor_of_tp_primitive_irr` — blocking a
  TP-primitive irreducible tensor preserves irreducibility.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, irreducibility, gauge-phase equivalence
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## Blocked blocks are irreducible tensors (for primitive blocks)

For a single block that is TP, has a primitive transfer map, and is irreducible,
the blocked tensor `blockTensor A P` is also irreducible.

The proof strategy avoids the "blocked period" issue entirely by working directly
with the PSD fixed point `ρ` of the original transfer map:

1. From TP + IsPrimitive + IsIrreducibleTensor → `IsPrimitiveMPS A ρ` with `ρ.PosDef`
   (via `hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible` +
    `posDef_of_isIrreducibleTensor_of_isPrimitiveMPS`)
2. `ρ` is also fixed by `transferMap (blockTensor A P)` (since `transferMap (blockTensor A P) = E^P`
   and `E ρ = ρ` implies `E^P ρ = ρ`)
3. Uniqueness of PSD fixed points of `E^P`: if `E^P σ = σ`, set `σ' = σ - c•ρ`.
   From the spectral gap of `IsPrimitiveMPS A ρ`, `E^n → Pρ` exponentially.
   Since `E^{Pk} σ' = Pρ σ' + N^{Pk} σ' = N^{Pk} σ'` (as `Pρ σ' = 0`)
   and `N^{Pk} σ' = σ'` (from `E^P σ' = σ'`), but `N^n → 0`, we get `σ' = 0`.
4. Apply `isIrreducibleMap_of_channel_posDef_fixedPoint_unique` →
   `IsIrreducibleMap (transferMap (blockTensor A P))`
5. Apply `isIrreducibleTensor_of_isIrreducibleMap` →
   `IsIrreducibleTensor (blockTensor A P)`
-/

/-- **Blocked blocks are irreducible tensors** (for originally primitive blocks).

If `A` is TP, has a primitive transfer map, and is an irreducible tensor, then
`blockTensor A P` is also an irreducible tensor for any `P ≥ 1`.

The key insight: the PosDef fixed point `ρ` of the original transfer map is also
a PosDef fixed point of the blocked transfer map `E^P`. Uniqueness of PSD fixed
points for `E^P` follows from the spectral gap of `IsPrimitiveMPS A ρ`: if
`E^P σ = σ` then `N^{Pk} σ' = σ'` (where `σ' = σ - c•ρ`, `N = E - Pρ`), but
`N^n → 0` from the spectral gap, so `σ' = 0`. -/
theorem isIrreducibleTensor_blockTensor_of_tp_primitive_irr [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hIrr : IsIrreducibleTensor A)
    {P : ℕ} (hP : 0 < P) :
    IsIrreducibleTensor (blockTensor A P) := by
  -- Step 1: Obtain IsPrimitiveMPS A ρ with ρ.PosDef.
  obtain ⟨ρ, hPrimMPS⟩ :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hTP hPrim
  have hPD : ρ.PosDef :=
    posDef_of_isIrreducibleTensor_of_isPrimitiveMPS hPrimMPS hIrr
  -- Step 2: Blocked tensor is TP.
  have hTP_blocked : ∑ i : Fin (blockPhysDim d P),
      (blockTensor (d := d) (D := D) A P i)ᴴ * blockTensor (d := d) (D := D) A P i = 1 :=
    leftCanonical_blockTensor A P hTP
  -- Step 3: Blocked transfer map is a channel.
  have hCh : IsChannel (transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P)) :=
    transferMap_isChannel (blockTensor A P) hTP_blocked
  -- Step 4: ρ is fixed by the blocked transfer map.
  have hρ_fix_blocked :
      transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P) ρ = ρ :=
    transferMap_blockTensor_fixedPoint A P ρ hPrimMPS.fixedPoint_is_fixed
  -- Step 5: Uniqueness of PSD fixed points of transferMap(blockTensor A P).
  -- Strategy: if E^P σ = σ, set σ' = σ - c•ρ (c = tr σ / tr ρ).
  -- Show N^{Pk} σ' = σ' for all k ≥ 1, but N^n → 0, hence σ' = 0.
  have huniq : ∀ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosSemidef →
      transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P) σ = σ →
      ∃ c : ℂ, σ = c • ρ := by
    intro σ _hσ_psd hσ_fix
    -- Convert hσ_fix to: (transferMap A)^P σ = σ.
    rw [transferMap_blockTensor] at hσ_fix
    -- Set abbreviations.
    set E := transferMap (d := d) (D := D) A with E_def
    set Pρ := fixedPointProj (D := D) ρ hPrimMPS.trace_ne_zero with Pρ_def
    set N := E - Pρ with N_def
    set c := Matrix.trace σ / Matrix.trace ρ with c_def
    use c
    -- Suffices to show σ - c • ρ = 0.
    suffices h0 : σ - c • ρ = 0 from eq_of_sub_eq_zero h0
    set σ' := σ - c • ρ with σ'_def
    -- tr σ' = 0.
    have htr_σ' : Matrix.trace σ' = 0 := by
      simp [σ'_def, Matrix.trace_sub, Matrix.trace_smul, c_def,
            div_mul_cancel₀ _ hPrimMPS.trace_ne_zero]
    -- E^P ρ = ρ (ρ is fixed by the blocked transfer map, hence by E^P).
    have hE_pow_ρ : (E ^ P) ρ = ρ := by
      simpa [E_def, transferMap_blockTensor_apply (A := A) (L := P) (X := ρ)] using hρ_fix_blocked
    -- E^P σ' = σ'.
    have hEP_σ' : (E ^ P) σ' = σ' := by
      simp only [σ'_def, map_sub, LinearMap.map_smul_of_tower, hσ_fix, hE_pow_ρ]
    -- (E^P)^k σ' = σ' for all k (by induction on k).
    have hEPk_σ' : ∀ k : ℕ, ((E ^ P) ^ k) σ' = σ' := by
      intro k
      induction k with
      | zero => simp
      | succ n ih =>
          simp [pow_succ', ih, hEP_σ']
    -- N^{Pk} σ' = σ' for all k ≥ 1.
    have hN_pow_σ' : ∀ k : ℕ, 0 < k → (N ^ (P * k)) σ' = σ' := by
      intro k hk
      have hPk_pos : 1 ≤ P * k := Nat.mul_pos hP hk
      -- E^{Pk} = Pρ + N^{Pk} (from pow_eq_fixedPointProj_add_compl_pow).
      have hdecomp : (E ^ (P * k)) σ' = Pρ σ' + (N ^ (P * k)) σ' := by
        have h := pow_eq_fixedPointProj_add_compl_pow E hPrimMPS.trace_ne_zero
          hPrimMPS.transferMap_isChannel.tp hPrimMPS.fixedPoint_is_fixed hPk_pos
        have happ := congrArg (fun T => T σ') h
        simpa [Pρ_def, N_def, LinearMap.add_apply] using happ
      -- E^{Pk} σ' = σ' (from hEPk_σ').
      have hEPk : (E ^ (P * k)) σ' = σ' := by
        rw [pow_mul]
        exact hEPk_σ' k
      -- Pρ σ' = 0 (since tr σ' = 0).
      have hPρ_σ' : Pρ σ' = 0 := by
        simp [Pρ_def, fixedPointProj, htr_σ']
      -- Combine: N^{Pk} σ' = E^{Pk} σ' - Pρ σ' = σ'.
      calc
        (N ^ (P * k)) σ'
            = 0 + (N ^ (P * k)) σ' := (zero_add _).symm
        _ = Pρ σ' + (N ^ (P * k)) σ' := by rw [hPρ_σ']
        _ = (E ^ (P * k)) σ' := hdecomp.symm
        _ = σ' := hEPk
    -- N^n σ' → 0 (from complement_pow_tendsto_zero applied to σ').
    have hN_tendsto : Filter.Tendsto (fun n => (N ^ n) σ') Filter.atTop (nhds 0) := by
      let V := Matrix (Fin D) (Fin D) ℂ
      let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
      -- (Φ N)^n → 0 as CLMs.
      have hN_clm : Filter.Tendsto (fun n => (Φ N) ^ n) Filter.atTop (nhds 0) :=
        hPrimMPS.complement_pow_tendsto_zero
      -- Evaluate at σ': (Φ N)^n σ' → 0.
      have heval := (ContinuousLinearMap.apply ℂ V σ').continuous.tendsto
        (0 : V →L[ℂ] V)
      rw [map_zero] at heval
      have hconv := heval.comp hN_clm
      -- Convert CLM powers to LinearMap powers: (Φ N)^n σ' = N^n σ'.
      suffices hsuff : ∀ n, ((Φ N) ^ n) σ' = (N ^ n) σ' by
        simp_rw [← hsuff]
        exact hconv
      intro n
      rw [← map_pow Φ N n]
      rfl
    -- σ' = 0: the subsequence N^{P*(k+1)} σ' = σ' → 0 shows σ' = 0.
    have hg_tendsto : Filter.Tendsto (fun k : ℕ => P * (k + 1)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b =>
        ⟨b, fun k hk => by
          have hk1 : k + 1 ≥ b + 1 := Nat.add_le_add_right hk 1
          have hPk1 : P * (k + 1) ≥ k + 1 := Nat.le_mul_of_pos_left _ hP
          omega⟩
    have hconst_tendsto : Filter.Tendsto (fun _ : ℕ => σ') Filter.atTop (nhds 0) := by
      have hconv2 : Filter.Tendsto (fun k => (N ^ (P * (k + 1))) σ') Filter.atTop (nhds 0) :=
        hN_tendsto.comp hg_tendsto
      have heq : (fun k : ℕ => (N ^ (P * (k + 1))) σ') = fun _ => σ' := by
        funext k
        exact hN_pow_σ' (k + 1) (Nat.succ_pos k)
      rwa [heq] at hconv2
    exact tendsto_nhds_unique tendsto_const_nhds hconst_tendsto
  -- Step 6: Apply isIrreducibleMap_of_channel_posDef_fixedPoint_unique.
  have hIrrMap : IsIrreducibleMap
      (transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P)) :=
    isIrreducibleMap_of_channel_posDef_fixedPoint_unique
      (transferMap (d := blockPhysDim d P) (D := D) (blockTensor A P))
      hCh ρ hPD hρ_fix_blocked huniq
  -- Step 7: IsIrreducibleMap → IsIrreducibleTensor.
  exact isIrreducibleTensor_of_isIrreducibleMap (blockTensor A P) hIrrMap

/-- **Extra blocking after period removal.**

If a cyclic-sector block is already trace-preserving, primitive, and tensor-irreducible,
then any later positive blocking length `k` preserves all three properties. In the
canonical-form reduction, the period-removal length that produces such sector blocks
is a different datum from this later finite blocking length, which is used only for
common refinement or injectivity/Wielandt-span arguments. -/
theorem tp_primitive_irreducible_extra_blocking [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hIrr : IsIrreducibleTensor A)
    {k : ℕ} (hk : 0 < k) :
    (∑ i : Fin (blockPhysDim d k),
      (blockTensor (d := d) (D := D) A k i)ᴴ * blockTensor (d := d) (D := D) A k i = 1) ∧
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d k) (D := D)
        (blockTensor (d := d) (D := D) A k)) ∧
    IsIrreducibleTensor (blockTensor (d := d) (D := D) A k) := by
  refine ⟨?_, ?_, ?_⟩
  · exact leftCanonical_blockTensor (d := d) (D := D) (A := A) (L := k) hTP
  · rw [transferMap_blockTensor]
    exact isPrimitive_pow_of_isPrimitive (D := D)
      (transferMap (d := d) (D := D) A) k hk hPrim
  · exact isIrreducibleTensor_blockTensor_of_tp_primitive_irr
      (d := d) (D := D) A hTP hPrim hIrr hk

namespace IsNormalCanonicalFormBNT

variable {d r : ℕ} {dim : Fin r → ℕ}
variable {μ : Fin r → ℂ}
variable {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-- Positive blocking preserves normal-CF-BNT structure, provided the blocked
BNT separation hypothesis is supplied explicitly.

The structural fields (left-canonical normalization, primitive transfer maps, and
irreducibility) are transported blockwise by
`tp_primitive_irreducible_extra_blocking`; the strict weight ordering is transported by
monotonicity of positive powers on nonnegative norms.  The gauge-phase separation
of the blocked family is deliberately an explicit input. -/
theorem blockTensor_of_notGpe
    (h : IsNormalCanonicalFormBNT (d := d) μ blocks)
    {L : ℕ} (hL : 0 < L)
    (hNotGpe : BlocksNotGaugePhaseEquiv (d := blockPhysDim d L)
      (fun k => blockTensor (d := d) (D := dim k) (blocks k) L)) :
    IsNormalCanonicalFormBNT (d := blockPhysDim d L)
      (fun k => (μ k) ^ L)
      (fun k => blockTensor (d := d) (D := dim k) (blocks k) L) := by
  have hBlocked (k : Fin r) := by
    haveI : NeZero (dim k) := ⟨Nat.ne_of_gt (h.dim_pos k)⟩
    exact tp_primitive_irreducible_extra_blocking
      (d := d) (D := dim k) (A := blocks k)
      (h.leftCanonical k) (h.block_primitive k) (h.block_irreducible k) hL
  refine IsNormalCanonicalFormBNT.ofSeparatedData
    (d := blockPhysDim d L)
    (μ := fun k => (μ k) ^ L)
    (A := fun k => blockTensor (d := d) (D := dim k) (blocks k) L)
    ?_ ?_ ?_ ?_ ?_ hNotGpe ?_
  · exact HasIrreducibleBlocks.ofForall fun k => (hBlocked k).2.2
  · exact IsLeftCanonicalBlockFamily.ofForall fun k => (hBlocked k).1
  · exact HasPrimitiveBlocks.ofForall fun k => (hBlocked k).2.1
  · exact
      { mu_strict_anti := by
          intro j k hjk
          have hbase : ‖μ k‖ < ‖μ j‖ := h.mu_strict_anti hjk
          simpa [norm_pow] using
            pow_lt_pow_left₀ hbase (norm_nonneg (μ k)) (hL.ne')
        mu_ne_zero := fun k => pow_ne_zero L (h.mu_ne_zero k) }
  · exact h.dim_pos
  · intro hr
    simp [norm_pow, h.mu_dom_norm_one hr]

end IsNormalCanonicalFormBNT


end MPSTensor
