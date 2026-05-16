/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.PhaseClassSectorData
import TNLean.MPS.FundamentalTheorem.PaperBNT.Basic
import TNLean.MPS.Overlap.PeripheralToSpectralGap

/-!
# Prepared-block PaperBNT constructor

Given a finite family of **already prepared** TP / primitive / irreducible /
injective blocks with nonzero weights satisfying the CPSV16 §II.A line-246
normalization (`|μ_k| ≤ 1` and at least one `|μ_k| = 1`), this file produces a
`SectorDecomposition` `P` together with a proof that

* `P.toTensor` has the same MPV at every length as the original
  `toTensorFromBlocks μ blocks`, and
* `P` satisfies `IsBNTCanonicalForm`.

The route is to quotient the block indices by MPV phase equivalence (the
existing one-sided BNT construction of
`TNLean.MPS.CanonicalForm.PhaseClassSectorData`), and then to discharge the
two paper-line-246 normalization fields (`weight_norm_le_one`,
`weight_unit_exists`) via the unit modulus of the phase-class scalar between
phase-equivalent TP/primitive/irreducible blocks.

## Paper anchor

* `Papers/1606.00608/MPDO-22-12-17-2.tex:271-301` — BNT existence in the
  prepared-data setting (`A^i = ⊕_{j,q} μ_{j,q} A_j^i` with normal `A_j` and
  the §II.A normalization).

## Scout memo

* `audits/2026-05-16_phase_C_feasibility_gpt55.md` §1, §2.3, §2.4 — the
  feasibility analysis that identified this prepared-block constructor as the
  pragmatic Phase C target (with the exact-`SameMPV₂` zero-tail and global
  rescaling issues quarantined behind the prepared-data hypotheses).

## Layering note

This module imports `TNLean.MPS.FundamentalTheorem.PaperBNT.Basic` from the
`CanonicalForm` directory.  This bridges canonical-form prepared data into
the `IsBNTCanonicalForm` contract that lives in the fundamental-theorem layer;
the inversion is intentional and matches the inversion already present at
`TNLean/MPS/CanonicalForm/PhaseCover.lean:6` and
`TNLean/MPS/CanonicalForm/PhaseClassSectorData.lean:8`.  It is to be resolved
in a future SharedInfra reorganization.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Unit modulus of the phase-class scalar -/

/--
**Unit modulus of the phase scalar between phase-equivalent TP / primitive /
irreducible blocks.**

If `MPVBlockPhaseEquiv X Y` holds and both `X` and `Y` are left-canonical,
have primitive transfer maps, and are irreducible tensors, then the
phase scalar `h.choose` has unit norm.

Proof sketch (scout memo §2.4):
1. The phase equivalence supplies the scaling relation
   `mpv Y σ = h.choose ^ N * mpv X σ`.
2. `mpvOverlap_self_scale_of_mpv_eq_pow_mul`
   (`SharedInfra/GaugePhase.lean`) converts this into a scaling
   `mpvOverlap Y Y N = (ζ · conj ζ)^N · mpvOverlap X X N`.
3. Both self-overlaps tend to `1` by
   `overlap_tendsto_one_of_peripheralPrimitive_of_irreducible`
   (`Overlap/PeripheralToSpectralGap.lean`).
4. `norm_eq_one_of_selfOverlap_scale` (`SharedInfra/GaugePhase.lean`)
   concludes `‖ζ‖ = 1`.
-/
lemma norm_choose_MPVBlockPhaseEquiv_eq_one
    {DX DY : ℕ} [NeZero DX] [NeZero DY]
    {X : MPSTensor d DX} {Y : MPSTensor d DY}
    (hTPX : IsLeftCanonical X)
    (hTPY : IsLeftCanonical Y)
    (hPrimX : _root_.IsPrimitive (transferMap (d := d) (D := DX) X))
    (hPrimY : _root_.IsPrimitive (transferMap (d := d) (D := DY) Y))
    (hIrrX : IsIrreducibleTensor X)
    (hIrrY : IsIrreducibleTensor Y)
    (h : MPVBlockPhaseEquiv X Y) :
    ‖h.choose‖ = 1 := by
  classical
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv Y σ = h.choose ^ N * mpv X σ := h.choose_spec.2
  have hScale :
      ∀ N : ℕ,
        mpvOverlap (d := d) Y Y N =
          (h.choose * starRingEnd ℂ h.choose) ^ N * mpvOverlap (d := d) X X N :=
    mpvOverlap_self_scale_of_mpv_eq_pow_mul
      (A := X) (B := Y) (ζ := h.choose) hmpv
  have hXX_c : Tendsto (fun N => mpvOverlap (d := d) X X N) atTop (𝓝 (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (d := d) (D := DX) X hIrrX hTPX hPrimX
  have hYY_c : Tendsto (fun N => mpvOverlap (d := d) Y Y N) atTop (𝓝 (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (d := d) (D := DY) Y hIrrY hTPY hPrimY
  have hXX : Tendsto (fun N => ‖mpvOverlap (d := d) X X N‖) atTop (𝓝 (1 : ℝ)) := by
    have h1 := hXX_c.norm
    simpa using h1
  have hYY : Tendsto (fun N => ‖mpvOverlap (d := d) Y Y N‖) atTop (𝓝 (1 : ℝ)) := by
    have h1 := hYY_c.norm
    simpa using h1
  exact norm_eq_one_of_selfOverlap_scale hXX hYY hScale

/-! ### Prepared-block PaperBNT constructor -/

/--
**Prepared-block PaperBNT constructor.**

Given a finite family of TP, primitive, irreducible, injective blocks with
nonzero weights satisfying the PaperBNT normalization conditions, produce a
`SectorDecomposition P` and a proof that `IsBNTCanonicalForm P` and the
assembled tensor agrees with the original direct sum.

Paper anchor: `Papers/1606.00608/MPDO-22-12-17-2.tex:271-301` (BNT existence
in the prepared-data setting).
-/
theorem exists_isBNTCanonicalForm_of_tp_primitive_irr_injective_blocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hTP : ∀ k, IsLeftCanonical (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (blocks k)))
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hInj : ∀ k, IsInjective (blocks k))
    (hμne : ∀ k, μ k ≠ 0)
    (hμLe : ∀ k, ‖μ k‖ ≤ 1)
    (hμUnit : ∃ k, ‖μ k‖ = 1) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      IsBNTCanonicalForm P := by
  classical
  -- Promote `0 < dim k` to a `NeZero (dim k)` typeclass instance.
  haveI : ∀ k, NeZero (dim k) := fun k => ⟨(hDim k).ne'⟩
  set classes := mpvPhaseClassData (d := d) blocks with hclasses
  -- Concrete sector decomposition from phase-class representatives.
  set P := collapsedBntSectorDecomp (d := d) μ blocks hμne with hP
  -- The phase scalar attached to each phase-class member.
  set ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose with hζFn
  -- Phase-scalar nonvanishing.
  have hζ_ne : ∀ j q, ζFn j q ≠ 0 :=
    fun j q => (classes.enum_phase j q).choose_spec.1
  -- Phase-scalar unit modulus (TP + primitive + irreducible on both blocks).
  have hζ_unit : ∀ j q, ‖ζFn j q‖ = 1 := by
    intro j q
    have hPE :
        MPVBlockPhaseEquiv (blocks (classes.repr j)) (blocks (classes.enum j q)) :=
      classes.enum_phase j q
    exact
      norm_choose_MPVBlockPhaseEquiv_eq_one
        (X := blocks (classes.repr j)) (Y := blocks (classes.enum j q))
        (hTP (classes.repr j)) (hTP (classes.enum j q))
        (hPrim (classes.repr j)) (hPrim (classes.enum j q))
        (hIrr (classes.repr j)) (hIrr (classes.enum j q))
        hPE
  -- Same-MPV with the original direct-sum tensor.
  have hSame : SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) :=
    collapsedBntSectorDecomp_sameMPV₂ (d := d) μ blocks hμne
  -- HasBNTSectorData.
  have hBNT : HasBNTSectorData (d := d) P :=
    collapsedBntSectorDecomp_hasBNT (d := d) μ blocks hTP hIrr hPrim hμne
  -- Per-block fields.
  have h_dim_pos : ∀ j : Fin P.basisCount, 0 < P.basisDim j := by
    intro j
    -- `P.basisDim j` is definitionally `dim (classes.repr j)`.
    change 0 < dim (classes.repr j)
    exact hDim (classes.repr j)
  have h_inj : ∀ j : Fin P.basisCount, IsInjective (P.basis j) := by
    intro j; change IsInjective (blocks (classes.repr j)); exact hInj (classes.repr j)
  have h_irr : ∀ j : Fin P.basisCount, IsIrreducibleTensor (P.basis j) := by
    intro j; change IsIrreducibleTensor (blocks (classes.repr j)); exact hIrr (classes.repr j)
  have h_lc : ∀ j : Fin P.basisCount, IsLeftCanonical (P.basis j) := by
    intro j; change IsLeftCanonical (blocks (classes.repr j)); exact hTP (classes.repr j)
  have h_self_overlap : ∀ j : Fin P.basisCount,
      Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
        atTop (𝓝 (1 : ℂ)) := by
    intro j
    change
      Tendsto (fun N : ℕ => mpvOverlap (d := d) (blocks (classes.repr j))
        (blocks (classes.repr j)) N) atTop (𝓝 (1 : ℂ))
    exact
      overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
        (d := d) (D := dim (classes.repr j))
        (blocks (classes.repr j))
        (hIrr (classes.repr j)) (hTP (classes.repr j)) (hPrim (classes.repr j))
  have h_distinct : ∀ j k : Fin P.basisCount, j ≠ k →
      ∀ h : P.basisDim j = P.basisDim k,
        ¬ GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis j)) (P.basis k) := by
    intro j k hjk hdim
    -- `P.basisDim j = dim (classes.repr j)` definitionally; ditto for basis.
    exact classes.blocks_not_equiv j k hjk hdim
  -- Weight-norm fields (line 246 normalization).
  have h_weight_le : ∀ (j : Fin P.basisCount) (q : Fin (P.copies j)),
      ‖P.weight j q‖ ≤ 1 := by
    intro j q
    -- `P.weight j q` is definitionally `ζFn j q * μ (classes.enum j q)`.
    change ‖ζFn j q * μ (classes.enum j q)‖ ≤ 1
    have := hμLe (classes.enum j q)
    calc ‖ζFn j q * μ (classes.enum j q)‖
        = ‖ζFn j q‖ * ‖μ (classes.enum j q)‖ := norm_mul _ _
      _ = 1 * ‖μ (classes.enum j q)‖ := by rw [hζ_unit j q]
      _ = ‖μ (classes.enum j q)‖ := one_mul _
      _ ≤ 1 := this
  have h_weight_unit : ∃ (j : Fin P.basisCount) (q : Fin (P.copies j)),
      ‖P.weight j q‖ = 1 := by
    obtain ⟨k0, hk0⟩ := hμUnit
    obtain ⟨j, q, hjq⟩ := classes.exists_enum_eq k0
    refine ⟨j, q, ?_⟩
    change ‖ζFn j q * μ (classes.enum j q)‖ = 1
    rw [hjq]
    rw [norm_mul, hζ_unit j q, one_mul, hk0]
  refine ⟨P, hSame, ?_⟩
  exact
    { basis_dim_pos := h_dim_pos
      basis_injective := h_inj
      basis_irreducible := h_irr
      basis_left_canonical := h_lc
      basis_normalized_self_overlap := h_self_overlap
      bnt_data := hBNT
      basis_distinct := h_distinct
      weight_norm_le_one := h_weight_le
      weight_unit_exists := h_weight_unit }

end MPSTensor
