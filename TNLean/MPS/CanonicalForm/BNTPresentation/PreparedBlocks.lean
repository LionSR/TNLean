/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNT.PhaseClassSectorData
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.CommonBlockedCyclicSectorConstruction
import TNLean.MPS.Transfer.Irreducible.PhysicalReindexTransport
import TNLean.MPS.Transfer.Spectrum.GaugePhase
import TNLean.MPS.CanonicalForm.BNTPresentation.LeftCanonical
import TNLean.MPS.Tensor.DirectSum.BlockGauge
import TNLean.MPS.Transfer.Spectrum.PrimitiveOverlap

/-!
# Prepared-block SectorBNT constructor

The suppliers in this file take a finite family of **already prepared**
TP / primitive / irreducible blocks, at least one of them, with nonzero weights,
and produce a `SectorDecomposition` `P` together with a proof that

* `P.toTensor` has the same MPV at every positive length as the original
  `toTensorFromBlocks μ blocks`, and
* `P` satisfies `IsLeftCanonicalBNTPresentation`.

The letterwise exact reconstruction is
`exists_isLeftCanonicalBNTPresentation_exact_of_tp_primitive_irr_blocks` in
`TNLean.MPS.CanonicalForm.BNTPresentation.PreparedReconstruction`.

The route is to quotient the block indices by MPV phase equivalence (the
existing one-sided BNT construction of
`TNLean.MPS.CanonicalForm.PhaseClassSectorData`).  No normalization of the
weights (arXiv:1606.00608, line 246) is needed.

## Paper anchor

* `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 237-246 — the canonical-form
  display labelled eq:II_CF1 and the subsequent weight normalization.
* `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 271-279 and 1135-1148 —
  the BNT characterization labelled prop:char-BNT, its appendix construction,
  and the same-CF uniqueness note.
* `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 283-301 — the two-layer
  expansion in terms of BNT sectors and copy weights.
* `Papers/2011.12127/TN-Review-main.tex`, lines 1827-1839, 1846-1859, and
  1864-1884 — the review-paper canonical-form, BNT, and two-layer display.

## Gap record

* `docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex` —
  records the canonical-form normalization and proportional-comparison analysis.

## Layering

This module consumes both canonical-form data
(`CanonicalForm.BNT.PhaseClassSectorData`) and the presentation in left-canonical
gauge (`CanonicalForm.BNTPresentation.LeftCanonical`).
-/

open MPTensor

open scoped Matrix BigOperators
open Filter Topology
open Kraus (blockPhysDim blockTensor)

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
2. `mpvOverlap_self_scale_of_mpv_eq_pow_mul_pos`
   (`SharedInfra/GaugePhase.lean`) converts this into a scaling
   `mpvOverlap Y Y N = (ζ · conj ζ)^N · mpvOverlap X X N`.
3. Both self-overlaps tend to `1` by
   `overlap_tendsto_one_of_peripheralPrimitive_of_irreducible`
   (`Overlap/PeripheralToTransferMapGap.lean`).
4. `norm_eq_one_of_selfOverlap_scale_pos` (`SharedInfra/GaugePhase.lean`)
   concludes `‖ζ‖ = 1`.
-/
lemma norm_choose_MPVBlockPhaseEquiv_eq_one
    {DX DY : ℕ} [NeZero DX] [NeZero DY]
    {X : MPSTensor d DX} {Y : MPSTensor d DY}
    (hTPX : IsLeftCanonical X)
    (hTPY : IsLeftCanonical Y)
    (hPrimX : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DX) X))
    (hPrimY : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DY) Y))
    (hIrrX : Kraus.IsIrreducibleFamily X)
    (hIrrY : Kraus.IsIrreducibleFamily Y)
    (h : MPVBlockPhaseEquiv X Y) :
    ‖h.choose‖ = 1 := by
  classical
  have hmpv : ∀ (N : ℕ), 0 < N → ∀ σ : Fin N → Fin d,
      mpv Y σ = h.choose ^ N * mpv X σ := h.choose_spec.2
  exact norm_eq_one_of_selfOverlap_scale_pos
    (by
      simpa using
        (overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
          (d := d) (D := DX) X hIrrX hTPX hPrimX).norm)
    (by
      simpa using
        (overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
          (d := d) (D := DY) Y hIrrY hTPY hPrimY).norm)
    (mpvOverlap_self_scale_of_mpv_eq_pow_mul_pos
      (A := X) (B := Y) (ζ := h.choose) hmpv)

/-!
### Bond dimensions inside a prepared phase class

The phase quotient in `CanonicalForm.PhaseClassSectorData` is deliberately
allowed to group blocks of differing bond dimensions: `MPVBlockPhaseEquiv` only
records proportional MPVs, not equality of bond dimensions.  For the prepared
blocks used by the BNT supplier, the rectangular overlap gap forces equality of
bond dimensions inside each phase class.
-/

/--
**Bond dimensions of prepared phase-equivalent blocks agree.**

Source: arXiv:1606.00608, Lemma equalMPS in
`Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 1080-1117, especially
the dimension conclusion at lines 1090 and 1115-1117; the phase-class
quotient is prop:char-BNT, labelled at line 278 with statement at line 279;
the appendix restatement, construction, and same-CF uniqueness note are lines
1135-1148.

If two left-canonical, primitive, irreducible blocks have MPV families related
by a nonzero scalar power, then their bond dimensions are equal.  The proof
uses the self-overlap normalization to show that the scalar has unit modulus;
then a rectangular overlap of the two blocks has norm tending to one, whereas
different bond dimensions would force that overlap to tend to zero.
-/
theorem dim_eq_of_MPVBlockPhaseEquiv_of_tp_primitive_irr
    {DX DY : ℕ} [NeZero DX] [NeZero DY]
    {X : MPSTensor d DX} {Y : MPSTensor d DY}
    (hTPX : IsLeftCanonical X)
    (hTPY : IsLeftCanonical Y)
    (hPrimX : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DX) X))
    (hPrimY : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DY) Y))
    (hIrrX : Kraus.IsIrreducibleFamily X)
    (hIrrY : Kraus.IsIrreducibleFamily Y)
    (h : MPVBlockPhaseEquiv X Y) :
    DX = DY := by
  classical
  have hζ_norm : ‖h.choose‖ = 1 :=
    norm_choose_MPVBlockPhaseEquiv_eq_one
      (X := X) (Y := Y) hTPX hTPY hPrimX hPrimY hIrrX hIrrY h
  have hmpv : ∀ (N : ℕ), 0 < N → ∀ σ : Fin N → Fin d,
      mpv Y σ = h.choose ^ N * mpv X σ := h.choose_spec.2
  have hXX_c : Tendsto (fun N => mpvOverlap (α := Fin d) X X N) atTop (𝓝 (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (d := d) (D := DX) X hIrrX hTPX hPrimX
  have hXX : Tendsto (fun N => ‖mpvOverlap (α := Fin d) X X N‖) atTop (𝓝 (1 : ℝ)) := by
    simpa using hXX_c.norm
  have hYX_eq : ∀ N : ℕ, 0 < N →
      mpvOverlap (α := Fin d) Y X N =
        h.choose ^ N * mpvOverlap (α := Fin d) X X N := by
    intro N hN
    exact mpvOverlap_eq_mul_of_mpv_eq_mul
      (α := Fin d) (A := Y) (B := X) (N := N) (c := h.choose ^ N) (hmpv N hN) X
  have hYX_norm_eq : ∀ N : ℕ, 0 < N →
      ‖mpvOverlap (α := Fin d) Y X N‖ = ‖mpvOverlap (α := Fin d) X X N‖ := by
    intro N hN
    rw [hYX_eq N hN, norm_mul, norm_pow, hζ_norm, one_pow, one_mul]
  have hYX : Tendsto (fun N => ‖mpvOverlap (α := Fin d) Y X N‖) atTop (𝓝 (1 : ℝ)) :=
    hXX.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hYX_norm_eq N hN).symm)
  exact (dim_eq_of_mpvOverlap_norm_tendsto_one_of_irreducible_TP
    Y X hIrrY hIrrX hTPY hTPX hYX).symm

/-- **Gauge-phase realization of prepared phase-equivalent blocks.**

Source: CPSV16, Proposition `prop:char-BNT`, lines 1135–1148.  If two
left-canonical, primitive, irreducible blocks have MPV families related by a
nonzero scalar power, then their bond dimensions agree and, after identifying
the bond spaces, one is an invertible conjugate of the other up to a nonzero
scalar.

This is the gauge realization used in the BNT characterization.  It does not
assert positivity of the scalar or unitarity of the gauge; those conclusions
belong to the later MPDO-specific argument at arXiv:1606.00608, lines
1899–1921. -/
theorem gaugePhaseEquiv_of_MPVBlockPhaseEquiv_of_tp_primitive_irr
    {DX DY : ℕ} [NeZero DX] [NeZero DY]
    {X : MPSTensor d DX} {Y : MPSTensor d DY}
    (hTPX : IsLeftCanonical X)
    (hTPY : IsLeftCanonical Y)
    (hPrimX : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DX) X))
    (hPrimY : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DY) Y))
    (hIrrX : Kraus.IsIrreducibleFamily X)
    (hIrrY : Kraus.IsIrreducibleFamily Y)
    (h : MPVBlockPhaseEquiv X Y) :
    ∃ e : DX = DY,
      GaugePhaseEquiv (cast (congr_arg (MPSTensor d) e) X) Y := by
  classical
  have e : DX = DY :=
    dim_eq_of_MPVBlockPhaseEquiv_of_tp_primitive_irr
      hTPX hTPY hPrimX hPrimY hIrrX hIrrY h
  subst DY
  refine ⟨rfl, ?_⟩
  have hX_self :
      Tendsto (fun N : ℕ => mpvOverlap (α := Fin d) X X N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (d := d) (D := DX) X hIrrX hTPX hPrimX
  have hY_self :
      Tendsto (fun N : ℕ => mpvOverlap (α := Fin d) Y Y N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (d := d) (D := DX) Y hIrrY hTPY hPrimY
  by_contra hNot
  obtain ⟨N, hNpos, hN⟩ :=
    exists_ge_not_forall_mpv_eq_mul_of_not_gaugePhaseEquiv_of_irreducible_TP
      X Y hIrrX hIrrY hTPX hTPY hX_self hY_self hNot 1
  have hSymm : MPVBlockPhaseEquiv Y X := MPVBlockPhaseEquiv.symm h
  apply hN
  refine ⟨hSymm.choose ^ N, ?_⟩
  intro σ
  exact hSymm.choose_spec.2 N hNpos σ

/-- **Letterwise gauge realization with the phase-class scalar.**

For prepared phase-equivalent blocks, the scalar chosen by `MPVBlockPhaseEquiv` is the same
scalar that appears in a letterwise gauge-phase relation. The equality of the two possible
scalars follows by comparing their powers at two consecutive lengths where the representative
MPV is nonzero.

Source: arXiv:1606.00608, Lemma `equalMPS`, lines 1080--1117, and Proposition
`prop:char-BNT`, lines 1135--1148. -/
lemma exists_gauge_choose_MPVBlockPhaseEquiv_of_tp_primitive_irr
    {DX DY : ℕ} [NeZero DX] [NeZero DY]
    {X : MPSTensor d DX} {Y : MPSTensor d DY}
    (hTPX : IsLeftCanonical X)
    (hTPY : IsLeftCanonical Y)
    (hPrimX : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DX) X))
    (hPrimY : _root_.IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin DY) Y))
    (hIrrX : Kraus.IsIrreducibleFamily X)
    (hIrrY : Kraus.IsIrreducibleFamily Y)
    (h : MPVBlockPhaseEquiv X Y) :
    ∃ e : DX = DY, ∃ G : GL (Fin DY) ℂ, ∀ i,
      Y i = h.choose • ((G : Matrix _ _ ℂ) *
        (cast (congr_arg (MPSTensor d) e) X) i *
        (↑(G⁻¹) : Matrix _ _ ℂ)) := by
  classical
  obtain ⟨e, hGauge⟩ := gaugePhaseEquiv_of_MPVBlockPhaseEquiv_of_tp_primitive_irr
    hTPX hTPY hPrimX hPrimY hIrrX hIrrY h
  subst DY
  obtain ⟨G, η, hη, hrel⟩ := hGauge
  have hXX : Tendsto (fun N => mpvOverlap (α := Fin d) X X N) atTop (𝓝 (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible X hIrrX hTPX hPrimX
  have hEventually : ∀ᶠ N in atTop, mpvOverlap (α := Fin d) X X N ≠ 0 :=
    hXX.eventually_ne one_ne_zero
  rw [eventually_atTop] at hEventually
  obtain ⟨N₀, hN₀⟩ := hEventually
  let M := max N₀ 1
  have hM : mpvOverlap (α := Fin d) X X M ≠ 0 :=
    hN₀ M (le_max_left _ _)
  have hM1 : mpvOverlap (α := Fin d) X X (M + 1) ≠ 0 :=
    hN₀ (M + 1) (le_trans (le_max_left _ _) (Nat.le_add_right M 1))
  have exists_coeff (L : ℕ) (hL : mpvOverlap (α := Fin d) X X L ≠ 0) :
      ∃ σ : Fin L → Fin d, mpv X σ ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hL
    rw [mpvOverlap]
    apply Finset.sum_eq_zero
    intro σ _
    rw [hzero σ, zero_mul]
  obtain ⟨σM, hσM⟩ := exists_coeff M hM
  obtain ⟨σM1, hσM1⟩ := exists_coeff (M + 1) hM1
  have hpow (L : ℕ) (hL : 0 < L) (σ : Fin L → Fin d) (hσ : mpv X σ ≠ 0) :
      h.choose ^ L = η ^ L := by
    have hh := h.choose_spec.2 L hL σ
    have hg := mpv_eq_pow_mul_of_gaugePhase X Y G η hrel L σ
    apply mul_right_cancel₀ hσ
    exact hh.symm.trans hg
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N₀ 1)
  have hpM := hpow M hMpos σM hσM
  have hpM1 := hpow (M + 1) (Nat.succ_pos M) σM1 hσM1
  have hphase : h.choose = η := by
    rw [pow_succ, pow_succ, hpM] at hpM1
    exact mul_left_cancel₀ (pow_ne_zero M hη) hpM1
  refine ⟨rfl, G, ?_⟩
  rw [hphase]
  exact hrel

/--
**Prepared phase classes preserve the original bond dimensions.**

Source: arXiv:1606.00608, Lemma equalMPS in
`Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 1080-1117, supplies the
same-dimension conclusion.  The source phase-class quotient is prop:char-BNT,
labelled at line 278 with statement at line 279, and its appendix
restatement/construction plus same-CF uniqueness note are lines 1135-1148.
This comparison is the dimension input for those phase classes.
In a prepared family of left-canonical, primitive, irreducible blocks, every
member of an MPV phase class has the same bond dimension as its chosen
representative.
-/
theorem mpvPhaseClassData_dim_eq_of_tp_primitive_irr
    {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hTP : ∀ k, IsLeftCanonical (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (blocks k)))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (blocks k)) :
    ∀ j q,
      dim ((mpvPhaseClassData blocks).enum j q) =
        dim ((mpvPhaseClassData blocks).repr j) := by
  classical
  have : ∀ k, NeZero (dim k) := fun k => ⟨(hDim k).ne'⟩
  let classes := mpvPhaseClassData (α := Fin d) blocks
  intro j q
  have hEq :
      dim (classes.repr j) = dim (classes.enum j q) :=
    dim_eq_of_MPVBlockPhaseEquiv_of_tp_primitive_irr
      (X := blocks (classes.repr j)) (Y := blocks (classes.enum j q))
      (hTP (classes.repr j)) (hTP (classes.enum j q))
      (hPrim (classes.repr j)) (hPrim (classes.enum j q))
      (hIrr (classes.repr j)) (hIrr (classes.enum j q))
      (classes.enum_phase j q)
  exact hEq.symm

/--
**Total bond dimension of the prepared collapsed BNT decomposition.**

Source: arXiv:1606.00608, eq:II_CF1 at lines 237-246 and prop:char-BNT
labelled at line 278 with statement at line 279.  Appendix A restates and
constructs the BNT quotient at lines 1135-1148.  For prepared blocks, the
phase-class quotient does not change the total bond dimension: quotienting only
groups phase-equivalent copies with the same bond dimension.
-/
theorem collapsedBntSectorDecomp_totalDim_eq_sum_dim_of_tp_primitive_irr
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hTP : ∀ k, IsLeftCanonical (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (blocks k)))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (blocks k))
    (hμne : ∀ k, μ k ≠ 0) :
    (collapsedBntSectorDecomp (d := d) μ blocks hμne).totalDim =
      ∑ k : Fin r, dim k :=
  collapsedBntSectorDecomp_totalDim_eq_sum_dim (d := d) μ blocks hμne
    (mpvPhaseClassData_dim_eq_of_tp_primitive_irr blocks hDim hTP hPrim hIrr)

/-! ### Prepared-block SectorBNT constructor -/

/--
**Prepared-block SectorBNT constructor.**

Given a nonempty finite family of TP, primitive, irreducible blocks with nonzero
weights, the phase-class-collapsed sector decomposition is a presentation of its
assembled tensor in left-canonical gauge.  No normalization of the weights is
needed.

Paper anchor: `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 271-279 and
1135-1148 for prop:char-BNT, and lines 283-301 for the two-layer BNT/copy
expansion.
-/
theorem isLeftCanonicalBNTPresentation_collapsedBntSectorDecomp_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hTP : ∀ k, IsLeftCanonical (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (blocks k)))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (blocks k))
    (hμne : ∀ k, μ k ≠ 0)
    (hr : 0 < r) :
    IsLeftCanonicalBNTPresentation (collapsedBntSectorDecomp (d := d) μ blocks hμne) := by
  classical
  have : ∀ k, NeZero (dim k) := fun k => ⟨(hDim k).ne'⟩
  set classes := mpvPhaseClassData (α := Fin d) blocks with hclasses
  set P := collapsedBntSectorDecomp (d := d) μ blocks hμne with hP
  have hBNT : HasBNTSectorData P :=
    collapsedBntSectorDecomp_hasBNT (d := d) μ blocks hTP hIrr hPrim hμne
  -- `P.basis j` is definitionally `blocks (classes.repr j)`.
  have h_normal : ∀ j : Fin P.basisCount, IsNormalTensor (P.basis j) := fun j =>
    isNormalTensor_of_isIrreducibleFamily_leftCanonical (blocks (classes.repr j))
      (hIrr (classes.repr j)) (hPrim (classes.repr j)) (hTP (classes.repr j))
  exact
    { basisCount_pos := classes.g_pos_of_r_pos hr
      sameMPV₂Pos := fun _ _ _ => rfl
      basis_normal := h_normal
      eventually_li := hBNT
      basis_left_canonical := fun j => hTP (classes.repr j) }

/-- Prepared TP, primitive, irreducible blocks determine a BNT canonical-form sector
decomposition with the same positive-length matrix product vectors.

Source: arXiv:1606.00608, lines 237--301 and 1135--1148; arXiv:2011.12127,
lines 1831--1885. -/
theorem exists_isLeftCanonicalBNTPresentation_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hTP : ∀ k, IsLeftCanonical (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (blocks k)))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (blocks k))
    (hμne : ∀ k, μ k ≠ 0)
    (hr : 0 < r) :
    ∃ P : SectorDecomposition (Fin d),
      SameMPV₂Pos P.toTensor (toTensorFromBlocks (α := Fin d) (μ := μ) blocks) ∧
      IsLeftCanonicalBNTPresentation P := by
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  refine ⟨P, collapsedBntSectorDecomp_sameMPV₂Pos (d := d) μ blocks hμne, ?_⟩
  exact isLeftCanonicalBNTPresentation_collapsedBntSectorDecomp_of_tp_primitive_irr_blocks
    μ blocks hDim hTP hPrim hIrr hμne hr

/-- Prepared TP, primitive, irreducible blocks determine a dimension-preserving BNT
canonical-form sector decomposition.

Source: arXiv:1606.00608, lines 237--301 and 1135--1148; arXiv:2011.12127,
lines 1831--1885. -/
theorem exists_isLeftCanonicalBNTPresentation_of_tp_primitive_irr_blocks_and_totalDim
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hTP : ∀ k, IsLeftCanonical (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (Kraus.transferMap (blocks k)))
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (blocks k))
    (hμne : ∀ k, μ k ≠ 0)
    (hr : 0 < r) :
    ∃ P : SectorDecomposition (Fin d),
      SameMPV₂Pos P.toTensor (toTensorFromBlocks (α := Fin d) (μ := μ) blocks) ∧
      IsLeftCanonicalBNTPresentation P ∧ P.totalDim = ∑ k : Fin r, dim k := by
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  refine ⟨P, collapsedBntSectorDecomp_sameMPV₂Pos (d := d) μ blocks hμne, ?_, ?_⟩
  · exact isLeftCanonicalBNTPresentation_collapsedBntSectorDecomp_of_tp_primitive_irr_blocks
      μ blocks hDim hTP hPrim hIrr hμne hr
  · exact collapsedBntSectorDecomp_totalDim_eq_sum_dim_of_tp_primitive_irr
      μ blocks hDim hTP hPrim hIrr hμne

/-! ### Arbitrary-input prepared-block supplier

This is the arbitrary-input layer of the SectorBNT supplier path.  Starting
from any MPS tensor `A`, after a single positive blocking length `p` we
produce a finite family of prepared blocks that are simultaneously
left-canonical, primitive, irreducible, and one-site injective, with nonzero
weights, and matching the blocked input in positive-length MPVs.

The prepared-block supplier
`exists_isLeftCanonicalBNTPresentation_of_tp_primitive_irr_blocks` turns a nonempty such
family into an `IsLeftCanonicalBNTPresentation` presentation.

Paper anchor: Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608,
lines 237-246 for eq:II_CF1 and the weight normalization, lines 249-251 for
after-blocking canonical-form existence, and lines 271-279 for the BNT
definition and prop:char-BNT statement.
-/

private lemma sameMPV₂Pos_reindexPhysical_aux
    {d₁ d₂ D₁ D₂ : ℕ} (f : Fin d₁ → Fin d₂)
    {A : MPSTensor d₂ D₁} {B : MPSTensor d₂ D₂}
    (hSame : SameMPV₂Pos A B) :
    SameMPV₂Pos (Kraus.reindexPhysical f A) (Kraus.reindexPhysical f B) := by
  intro N hN σ
  rw [mpv_reindexPhysical, mpv_reindexPhysical]
  exact hSame N hN _

/-- **Arbitrary-input prepared-block supplier (positive-length).**

Given an arbitrary MPS tensor `A` of bond dimension `D`, there is a single
positive blocking length `p` and a finite family of prepared blocks
(left-canonical, primitive, irreducible, one-site injective, with nonzero
weights and positive bond dimensions) whose direct-sum tensor matches the
`p`-blocked input `blockTensor A p` at every positive length.

A nonempty family of these blocks feeds the `IsLeftCanonicalBNTPresentation` constructor
`exists_isLeftCanonicalBNTPresentation_of_tp_primitive_irr_blocks`.

Construction steps:

1. `unconditional_commonPrimitiveIrreducibleBlocks A A (fun _ _ _ => rfl)` —
   apply the two-sided arbitrary-input reduction at `B = A` to obtain a
   positive blocking length `p₀`, a left-canonical / primitive / irreducible
   nonzero-weight block family `blocksA`, and the positive-length identity
   `SameMPV₂Pos (blockTensor A p₀) (toTensorFromBlocks μA blocksA)`.
2. `exists_common_injective_blocking_of_tp_primitive_irr_family` produces a
   common positive extra blocking length `L` at which each block becomes
   one-site injective and preserves left-canonical, primitive, and
   irreducible properties.
3. Flattening the iterated blocking back to the direct `p₀ * L` alphabet
   transports each block and the positive-length MPV identity to the direct
   `blockPhysDim d (p₀ * L)` alphabet without changing the relevant
   block-level properties (all of them are invariant under physical
   reindexing by an alphabet equivalence).
-/
theorem exists_prepared_BNT_blocks_afterBlocking_pos
    {d D : ℕ} (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧
    ∃ r : ℕ, ∃ dim : Fin r → ℕ, ∃ μ : Fin r → ℂ,
    ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
      (∀ k, 0 < dim k) ∧
      (∀ k, IsLeftCanonical (blocks k)) ∧
      (∀ k, _root_.IsPrimitive (Kraus.transferMap (blocks k))) ∧
      (∀ k, Kraus.IsIrreducibleFamily (blocks k)) ∧
      (∀ k, Kraus.IsInjective (blocks k)) ∧
      (∀ k, μ k ≠ 0) ∧
      SameMPV₂Pos (blockTensor (d := d) (n := Fin D) A p)
        (toTensorFromBlocks (α := Fin (blockPhysDim d p)) (μ := μ) blocks) := by
  classical
  -- Step 1: arbitrary-input two-sided reduction at `B = A`.
  obtain ⟨p₀, hp₀,
      rA, dimA, μA, blocksA,
      _rB, _dimB, _μB, _blocksB,
      hAPos, _hBPos, _hNonzeroPos,
      hμA, _hμB, hTPA, _hTPB, hPrimA, _hPrimB,
      hIrrA, _hIrrB, hDimA, _hDimB⟩ :=
    unconditional_commonPrimitiveIrreducibleBlocks
      (d := d) (D₁ := D) (D₂ := D) A A (fun _ _ _ => rfl)
  -- Step 2: common positive extra blocking that makes each block injective and
  -- preserves trace-preservation, transfer-map primitivity, and tensor
  -- irreducibility.
  obtain ⟨L, hL, hBlocked⟩ :=
    exists_common_injective_blocking_of_tp_primitive_irr_family
      (d := blockPhysDim d p₀) (r := rA) (dim := dimA)
      (blocks := blocksA) hDimA hTPA hPrimA hIrrA
  -- Step 3: assemble the result.  The final blocks live in the direct
  -- `blockPhysDim d (p₀ * L)` alphabet via `flattenedIteratedBlockTensor`.
  refine ⟨p₀ * L, Nat.mul_pos hp₀ hL, rA, dimA, fun k => (μA k) ^ L,
    fun k => flattenedIteratedBlockTensor
      (d := d) (p := p₀) (D := dimA k) (blocksA k) L, hDimA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- IsLeftCanonical of each flattened-iterated block.
  · intro k
    have hLCBlocked : ∑ i : Fin (blockPhysDim (blockPhysDim d p₀) L),
        (blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k)) (blocksA k) L i)ᴴ *
          blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k)) (blocksA k) L i = 1 :=
      (hBlocked k).2.1
    change IsLeftCanonical
      (flattenedIteratedBlockTensor (d := d) (p := p₀) (D := dimA k)
        (blocksA k) L)
    exact (Kraus.isTP_reindexPhysical_iff
      (directIteratedBlockEquiv d p₀ L)
      (blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k)) (blocksA k) L)).mpr
        hLCBlocked
  -- Transfer-map primitivity of each flattened-iterated block.
  · intro k
    have hPrimBlocked := (hBlocked k).2.2.1
    change _root_.IsPrimitive
      (Kraus.transferMap (ι := Fin (blockPhysDim d (p₀ * L))) (n := Fin (dimA k))
        (flattenedIteratedBlockTensor (d := d) (p := p₀) (D := dimA k)
          (blocksA k) L))
    exact (isPrimitive_transferMap_reindexPhysical_equiv
      (directIteratedBlockEquiv d p₀ L)
      (blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k)) (blocksA k) L)).mpr
        hPrimBlocked
  -- Tensor irreducibility of each flattened-iterated block.
  · intro k
    have hIrrBlocked := (hBlocked k).2.2.2
    change Kraus.IsIrreducibleFamily
      (flattenedIteratedBlockTensor (d := d) (p := p₀) (D := dimA k)
        (blocksA k) L)
    exact (Kraus.isIrreducibleFamily_reindexPhysical_equiv
      (directIteratedBlockEquiv d p₀ L)
      (blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k)) (blocksA k) L)).mpr
        hIrrBlocked
  -- One-site injectivity of each flattened-iterated block.
  · intro k
    have hInjBlocked := (hBlocked k).1
    change Kraus.IsInjective
      (flattenedIteratedBlockTensor (d := d) (p := p₀) (D := dimA k)
        (blocksA k) L)
    exact (isInjective_reindexPhysical_equiv
      (directIteratedBlockEquiv d p₀ L)
      (blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k)) (blocksA k) L)).mpr
        hInjBlocked
  -- Nonzero weights at the power.
  · intro k; exact pow_ne_zero L (hμA k)
  -- Positive-length MPV equality with the blocked input.
  · -- (i) blocked Pos:
    have hBlockPos :
        SameMPV₂Pos
          (blockTensor (d := blockPhysDim d p₀) (n := Fin D)
            (blockTensor (d := d) (n := Fin D) A p₀) L)
          (blockTensor (d := blockPhysDim d p₀) (n := Fin (∑ k : Fin rA, dimA k))
            (toTensorFromBlocks (α := Fin (blockPhysDim d p₀)) (μ := μA) blocksA) L) :=
      sameMPV₂Pos_block
        (d := blockPhysDim d p₀)
        (blockTensor (d := d) (n := Fin D) A p₀)
        (toTensorFromBlocks (α := Fin (blockPhysDim d p₀)) (μ := μA) blocksA)
        hAPos L hL
    -- (ii) blocking distributes over toTensorFromBlocks (full-length SameMPV₂):
    have hDistr : SameMPV₂
        (blockTensor (d := blockPhysDim d p₀) (n := Fin (∑ k : Fin rA, dimA k))
          (toTensorFromBlocks (α := Fin (blockPhysDim d p₀)) (μ := μA) blocksA) L)
        (toTensorFromBlocks
          (α := Fin (blockPhysDim (blockPhysDim d p₀) L))
          (fun k => (μA k) ^ L)
          (fun k => blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k))
            (blocksA k) L)) :=
      sameMPV₂_block_toTensorFromBlocks
        (d := blockPhysDim d p₀) (dim := dimA) μA blocksA L
    -- (iii) combine the two on the iterated phys-dim alphabet:
    have hIter : SameMPV₂Pos
        (blockTensor (d := blockPhysDim d p₀) (n := Fin D)
          (blockTensor (d := d) (n := Fin D) A p₀) L)
        (toTensorFromBlocks
          (α := Fin (blockPhysDim (blockPhysDim d p₀) L))
          (fun k => (μA k) ^ L)
          (fun k => blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k))
            (blocksA k) L)) := by
      intro N hN σ
      exact (hBlockPos N hN σ).trans (hDistr N σ)
    -- (iv) physically reindex both sides to the direct `blockPhysDim d (p₀ * L)`
    -- alphabet via `directIteratedBlockEquiv`.
    have hReindex :
        SameMPV₂Pos
          (Kraus.reindexPhysical (directIteratedBlockEquiv d p₀ L)
            (blockTensor (d := blockPhysDim d p₀) (n := Fin D)
              (blockTensor (d := d) (n := Fin D) A p₀) L))
          (Kraus.reindexPhysical (directIteratedBlockEquiv d p₀ L)
            (toTensorFromBlocks
              (α := Fin (blockPhysDim (blockPhysDim d p₀) L))
              (fun k => (μA k) ^ L)
              (fun k => blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k))
                (blocksA k) L))) :=
      sameMPV₂Pos_reindexPhysical_aux
        (f := (directIteratedBlockEquiv d p₀ L : _ → _)) hIter
    -- (v) rewrite both sides using `flattenedIteratedBlockTensor_blockTensor`
    -- and `toTensorFromBlocks_flattenedIteratedBlockTensor`.
    have hLeft :
        Kraus.reindexPhysical (directIteratedBlockEquiv d p₀ L)
          (blockTensor (d := blockPhysDim d p₀) (n := Fin D)
            (blockTensor (d := d) (n := Fin D) A p₀) L) =
          blockTensor (d := d) (n := Fin D) A (p₀ * L) :=
      flattenedIteratedBlockTensor_blockTensor (d := d) (D := D) A p₀ L
    have hRight :
        Kraus.reindexPhysical (directIteratedBlockEquiv d p₀ L)
          (toTensorFromBlocks
            (α := Fin (blockPhysDim (blockPhysDim d p₀) L))
            (fun k => (μA k) ^ L)
            (fun k => blockTensor (d := blockPhysDim d p₀) (n := Fin (dimA k))
              (blocksA k) L)) =
          toTensorFromBlocks
            (α := Fin (blockPhysDim d (p₀ * L)))
            (μ := fun k => (μA k) ^ L)
            (fun k => flattenedIteratedBlockTensor (d := d) (p := p₀)
              (D := dimA k) (blocksA k) L) :=
      (toTensorFromBlocks_flattenedIteratedBlockTensor (d := d) (p := p₀)
        (r := rA) (L := L) (dim := dimA) (fun k => (μA k) ^ L) blocksA).symm
    rw [hLeft, hRight] at hReindex
    exact hReindex

end MPSTensor
