/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.NormalityChain

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Primitive blocked tensors and conditional block matching

This file proves two consequences for TP-primitive irreducible blocks after
blocking. First, blocking preserves tensor irreducibility under the primitive
hypothesis. Second, once two separated normal-canonical-form families are in the
TP-primitive setting, proportional MPVs force the usual permutation and
blockwise gauge-phase matching.

## Main statements

* `isIrreducibleTensor_blockTensor_of_tp_primitive_irr` — blocking a
  TP-primitive irreducible tensor preserves irreducibility.
* `weakFundamentalTheorem_conditional` — proportional MPVs imply block matching
  for separated TP-primitive normal canonical form data.

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

/-!
## Conditional Fundamental Theorem: proportional MPVs → block matching

This combines the full reduction data with the block-matching conclusions
of the fundamental theorem.

For two arbitrary tensors A, B with proportional MPVs, the reduction produces
blocked TP-primitive decompositions. Under the additional hypotheses needed
for `IsNormalCanonicalForm` (irreducibility and distinct weight norms), one obtains
permutation + gauge-phase matching of blocks.
-/

/-- **Conditional Fundamental Theorem (irreducibility and distinct weights).**

For two tensor families in TP-primitive normal canonical form with BNT separation,
if their blocked versions have proportional MPVs (with convergent coefficients), then
the block counts match and blocks are pairwise gauge-phase equivalent (up to
permutation). This is the corresponding block-matching statement from `Full.lean`. -/
theorem weakFundamentalTheorem_conditional
    {d' rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d' (dimA j))
    (B : (k : Fin rB) → MPSTensor d' (dimB k))
    (hA_ncf : IsNormalCanonicalForm μA A)
    (hA_blocks : ∀ j k : Fin rA, j ≠ k →
      ∀ (h : dimA j = dimA k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d') h) (A j)) (A k))
    (hB_ncf : IsNormalCanonicalForm μB B)
    (hB_blocks : ∀ j k : Fin rB, j ≠ k →
      ∀ (h : dimB j = dimB k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d') h) (B j)) (B k))
    (A_total : MPSTensor d' DtotA)
    (B_total : MPSTensor d' DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d'),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d'),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d'), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d')
              (cast (congr_arg (MPSTensor d') hdim) (A j))
              (B (perm j)) :=
  MPSTensor.fundamentalTheorem_proportionalMPV_of_separated_normalCFBNT_data A B
    hA_ncf hA_blocks hB_ncf hB_blocks
    A_total B_total aCoeff bCoeff aLim bLim c cLim
    hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne


end MPSTensor
