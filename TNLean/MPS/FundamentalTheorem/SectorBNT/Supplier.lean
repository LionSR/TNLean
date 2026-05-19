/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.PhaseClassSectorData
import TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorTransport
import TNLean.MPS.Core.PhysicalReindexTransport
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.Overlap.PeripheralToSpectralGap

/-!
# Prepared-block SectorBNT constructor

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

## Layering

This module lives in the `FundamentalTheorem.SectorBNT.*` layer because it
consumes both canonical-form data (`CanonicalForm.PhaseClassSectorData`) and
the FT-side `IsBNTCanonicalForm` contract (`FundamentalTheorem.SectorBNT.Basic`).
Placing it in `FundamentalTheorem.SectorBNT.Supplier` re-establishes the natural
layering: `FundamentalTheorem.SectorBNT` is above `CanonicalForm`, so importing
from both directions here is consistent with the overall layer order.
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

/-! ### Prepared-block SectorBNT constructor -/

/--
**Prepared-block SectorBNT constructor.**

Given a finite family of TP, primitive, irreducible, injective blocks with
nonzero weights satisfying the SectorBNT normalization conditions, produce a
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

/-! ### Arbitrary-input prepared-block supplier

This is the arbitrary-input layer of the paper-BNT supplier path.  Starting
from any MPS tensor `A`, after a single positive blocking length `p` we
produce a finite family of prepared blocks that are simultaneously
left-canonical, primitive, irreducible, and one-site injective, with nonzero
weights, and matching the blocked input in positive-length MPVs.

This is the "everything except the weight normalization" layer.  The
remaining ingredient is the CPSV16 §II.A line 246 normalization
(absolute value of every weight at most one and at least one of unit modulus),
which the source paper makes an explicit user choice ("we can always choose
this normalization, which we will assume").  A separate normalization layer
or hypothesis passes those facts to the prepared-block supplier
`exists_isBNTCanonicalForm_of_tp_primitive_irr_injective_blocks` to obtain
the full `IsBNTCanonicalForm` conclusion.

Paper anchor: CPSV16 §II.A line 237-280 (canonical form definition,
normalization, and BNT discussion), Cirac–Pérez-García–Schuch–Verstraete,
arXiv:1606.00608.
-/

private lemma sameMPV₂Pos_reindexPhysical_aux
    {d₁ d₂ D₁ D₂ : ℕ} (f : Fin d₁ → Fin d₂)
    {A : MPSTensor d₂ D₁} {B : MPSTensor d₂ D₂}
    (hSame : SameMPV₂Pos A B) :
    SameMPV₂Pos (reindexPhysical f A) (reindexPhysical f B) := by
  intro N hN σ
  rw [mpv_reindexPhysical, mpv_reindexPhysical]
  exact hSame N hN _

/-- **Arbitrary-input prepared-block supplier (positive-length).**

Given an arbitrary MPS tensor `A` of bond dimension `D`, there is a single
positive blocking length `p` and a finite family of prepared blocks
(left-canonical, primitive, irreducible, one-site injective, with nonzero
weights and positive bond dimensions) whose direct-sum tensor matches the
`p`-blocked input `blockTensor A p` at every positive length.

The CPSV16 §II.A line 246 weight normalization is **not** delivered
here, since the source paper makes this an explicit user assumption.  A
separate normalization hypothesis is composed with the prepared
blocks here to feed the `IsBNTCanonicalForm` constructor
`exists_isBNTCanonicalForm_of_tp_primitive_irr_injective_blocks`.

Construction steps:

1. `unconditional_commonPrimitiveIrreducibleBlocks A A (fun _ _ => rfl)` —
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
      (∀ k, _root_.IsPrimitive (transferMap (blocks k))) ∧
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      (∀ k, IsInjective (blocks k)) ∧
      (∀ k, μ k ≠ 0) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) := by
  classical
  -- Step 1: arbitrary-input two-sided reduction at `B = A`.
  obtain ⟨p₀, hp₀, _zeroTailA, _zeroTailB,
      rA, dimA, μA, blocksA,
      _rB, _dimB, _μB, _blocksB,
      _hZAflat, _hZBflat, hAPos, _hBPos, _hNonzeroPos, _hZeroFlat,
      hμA, _hμB, hTPA, _hTPB, hPrimA, _hPrimB,
      hIrrA, _hIrrB, hDimA, _hDimB⟩ :=
    unconditional_commonPrimitiveIrreducibleBlocks
      (d := d) (D₁ := D) (D₂ := D) A A (fun _ _ => rfl)
  -- Step 2: common positive extra blocking that makes each block injective and
  -- preserves trace-preservation, transfer-map primitivity, and tensor
  -- irreducibility.
  obtain ⟨L, hL, hBlocked⟩ :=
    exists_common_injective_blocking_of_tp_primitive_irr_family
      (d := blockPhysDim d p₀) (r := rA) (dim := dimA)
      (blocks := blocksA) hDimA hTPA hPrimA hIrrA
  -- Step 3: package the result.  The final blocks live in the direct
  -- `blockPhysDim d (p₀ * L)` alphabet via `flattenedIteratedBlockTensor`.
  refine ⟨p₀ * L, Nat.mul_pos hp₀ hL, rA, dimA, fun k => (μA k) ^ L,
    fun k => flattenedIteratedBlockTensor
      (d := d) (p := p₀) (D := dimA k) (blocksA k) L, hDimA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- IsLeftCanonical of each flattened-iterated block.
  · intro k
    have hLCBlocked : ∑ i : Fin (blockPhysDim (blockPhysDim d p₀) L),
        (blockTensor (d := blockPhysDim d p₀) (D := dimA k) (blocksA k) L i)ᴴ *
          blockTensor (d := blockPhysDim d p₀) (D := dimA k) (blocksA k) L i = 1 :=
      (hBlocked k).2.1
    change IsLeftCanonical
      (flattenedIteratedBlockTensor (d := d) (p := p₀) (D := dimA k)
        (blocksA k) L)
    exact (leftCanonical_reindexPhysical_equiv
      (directIteratedBlockEquiv d p₀ L)
      (blockTensor (d := blockPhysDim d p₀) (D := dimA k) (blocksA k) L)).mpr
        hLCBlocked
  -- Transfer-map primitivity of each flattened-iterated block.
  · intro k
    have hPrimBlocked := (hBlocked k).2.2.1
    change _root_.IsPrimitive
      (transferMap (d := blockPhysDim d (p₀ * L)) (D := dimA k)
        (flattenedIteratedBlockTensor (d := d) (p := p₀) (D := dimA k)
          (blocksA k) L))
    exact (isPrimitive_transferMap_reindexPhysical_equiv
      (directIteratedBlockEquiv d p₀ L)
      (blockTensor (d := blockPhysDim d p₀) (D := dimA k) (blocksA k) L)).mpr
        hPrimBlocked
  -- Tensor irreducibility of each flattened-iterated block.
  · intro k
    have hIrrBlocked := (hBlocked k).2.2.2
    change IsIrreducibleTensor
      (flattenedIteratedBlockTensor (d := d) (p := p₀) (D := dimA k)
        (blocksA k) L)
    exact (isIrreducibleTensor_reindexPhysical_equiv
      (directIteratedBlockEquiv d p₀ L)
      (blockTensor (d := blockPhysDim d p₀) (D := dimA k) (blocksA k) L)).mpr
        hIrrBlocked
  -- One-site injectivity of each flattened-iterated block.
  · intro k
    have hInjBlocked := (hBlocked k).1
    change IsInjective
      (flattenedIteratedBlockTensor (d := d) (p := p₀) (D := dimA k)
        (blocksA k) L)
    exact (isInjective_reindexPhysical_equiv
      (directIteratedBlockEquiv d p₀ L)
      (blockTensor (d := blockPhysDim d p₀) (D := dimA k) (blocksA k) L)).mpr
        hInjBlocked
  -- Nonzero weights at the power.
  · intro k; exact pow_ne_zero L (hμA k)
  -- Positive-length MPV equality with the blocked input.
  · -- (i) blocked Pos:
    have hBlockPos :
        SameMPV₂Pos
          (blockTensor (d := blockPhysDim d p₀) (D := D)
            (blockTensor (d := d) (D := D) A p₀) L)
          (blockTensor (d := blockPhysDim d p₀) (D := ∑ k : Fin rA, dimA k)
            (toTensorFromBlocks (d := blockPhysDim d p₀) (μ := μA) blocksA) L) :=
      sameMPV₂Pos_blockTensor
        (d := blockPhysDim d p₀)
        (blockTensor (d := d) (D := D) A p₀)
        (toTensorFromBlocks (d := blockPhysDim d p₀) (μ := μA) blocksA)
        hAPos L hL
    -- (ii) blocking distributes over toTensorFromBlocks (full-length SameMPV₂):
    have hDistr : SameMPV₂
        (blockTensor (d := blockPhysDim d p₀) (D := ∑ k : Fin rA, dimA k)
          (toTensorFromBlocks (d := blockPhysDim d p₀) (μ := μA) blocksA) L)
        (toTensorFromBlocks
          (d := blockPhysDim (blockPhysDim d p₀) L)
          (fun k => (μA k) ^ L)
          (fun k => blockTensor (d := blockPhysDim d p₀) (D := dimA k)
            (blocksA k) L)) :=
      sameMPV₂_blockTensor_toTensorFromBlocks
        (d := blockPhysDim d p₀) (dim := dimA) μA blocksA L
    -- (iii) combine the two on the iterated phys-dim alphabet:
    have hIter : SameMPV₂Pos
        (blockTensor (d := blockPhysDim d p₀) (D := D)
          (blockTensor (d := d) (D := D) A p₀) L)
        (toTensorFromBlocks
          (d := blockPhysDim (blockPhysDim d p₀) L)
          (fun k => (μA k) ^ L)
          (fun k => blockTensor (d := blockPhysDim d p₀) (D := dimA k)
            (blocksA k) L)) := by
      intro N hN σ
      exact (hBlockPos N hN σ).trans (hDistr N σ)
    -- (iv) physically reindex both sides to the direct `blockPhysDim d (p₀ * L)`
    -- alphabet via `directIteratedBlockEquiv`.
    have hReindex :
        SameMPV₂Pos
          (reindexPhysical (directIteratedBlockEquiv d p₀ L)
            (blockTensor (d := blockPhysDim d p₀) (D := D)
              (blockTensor (d := d) (D := D) A p₀) L))
          (reindexPhysical (directIteratedBlockEquiv d p₀ L)
            (toTensorFromBlocks
              (d := blockPhysDim (blockPhysDim d p₀) L)
              (fun k => (μA k) ^ L)
              (fun k => blockTensor (d := blockPhysDim d p₀) (D := dimA k)
                (blocksA k) L))) :=
      sameMPV₂Pos_reindexPhysical_aux
        (f := (directIteratedBlockEquiv d p₀ L : _ → _)) hIter
    -- (v) rewrite both sides using `flattenedIteratedBlockTensor_blockTensor`
    -- and `toTensorFromBlocks_flattenedIteratedBlockTensor`.
    have hLeft :
        reindexPhysical (directIteratedBlockEquiv d p₀ L)
          (blockTensor (d := blockPhysDim d p₀) (D := D)
            (blockTensor (d := d) (D := D) A p₀) L) =
          blockTensor (d := d) (D := D) A (p₀ * L) :=
      flattenedIteratedBlockTensor_blockTensor (d := d) (D := D) A p₀ L
    have hRight :
        reindexPhysical (directIteratedBlockEquiv d p₀ L)
          (toTensorFromBlocks
            (d := blockPhysDim (blockPhysDim d p₀) L)
            (fun k => (μA k) ^ L)
            (fun k => blockTensor (d := blockPhysDim d p₀) (D := dimA k)
              (blocksA k) L)) =
          toTensorFromBlocks
            (d := blockPhysDim d (p₀ * L))
            (μ := fun k => (μA k) ^ L)
            (fun k => flattenedIteratedBlockTensor (d := d) (p := p₀)
              (D := dimA k) (blocksA k) L) :=
      (toTensorFromBlocks_flattenedIteratedBlockTensor (d := d) (p := p₀)
        (r := rA) (L := L) (dim := dimA) (fun k => (μA k) ^ L) blocksA).symm
    rw [hLeft, hRight] at hReindex
    exact hReindex

/-! ### End-to-end arbitrary-input SectorBNT supplier

Composing the prepared-block supplier `exists_prepared_BNT_blocks_afterBlocking_pos`
with the prepared-block BNT constructor
`exists_isBNTCanonicalForm_of_tp_primitive_irr_injective_blocks` closes the
arbitrary-input path on the paper-BNT side, with one explicit user assumption.

The CPSV16 paper makes the weight normalization (absolute value of every weight
at most one and at least one of unit modulus) an explicit user choice: see
arXiv:1606.00608, §II.A line 246 ("we can always *choose* this normalization,
which we will assume from now on").  Accordingly the end-to-end entry below
exposes the prepared-block family produced by blocking and lets the user
supply the §II.A line 246 normalization on those specific weights, after which
the prepared-block BNT constructor delivers a full `IsBNTCanonicalForm`
decomposition together with positive-length MPV agreement.
-/

/-- **Arbitrary-input BNT block preparation (CPSV16 §II.A L237-280).**

For any tensor `A : MPSTensor d D`, after at most one positive blocking length
`p`, there is a finite family of **prepared** blocks (left-canonical,
primitive, irreducible, one-site injective, with nonzero weights and positive
bond dimensions) whose direct-sum tensor matches the `p`-blocked input
`blockTensor A p` at every positive length.  When the user supplies the
CPSV16 §II.A line 246 normalization choice on those weights (every weight
has absolute value at most one and at least one of unit modulus), there is a
BNT canonical-form sector decomposition `P` satisfying `IsBNTCanonicalForm`
with `blockTensor A p` matching `P.toTensor` at every positive length.

The normalization is, per CPSV16 line 246, an explicit user choice:  the paper
writes "we can always *choose* this normalization, which we will assume from
now on".  We therefore expose the prepared-block family and embed the
conditional sector-decomposition supplier inside the existential.

Paper anchor: arXiv:1606.00608 §II.A line 237-280; proposition
char-BNT line 1135-1149. -/
theorem exists_isBNTCanonicalForm_afterBlocking_pos
    {d D : ℕ} (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧
    ∃ r : ℕ, ∃ dim : Fin r → ℕ, ∃ μ : Fin r → ℂ,
    ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
      (∀ k, 0 < dim k) ∧
      (∀ k, IsLeftCanonical (blocks k)) ∧
      (∀ k, _root_.IsPrimitive (transferMap (blocks k))) ∧
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      (∀ k, IsInjective (blocks k)) ∧
      (∀ k, μ k ≠ 0) ∧
      SameMPV₂Pos (blockTensor (d := d) (D := D) A p)
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
      (∀ (_hμLe : ∀ k, ‖μ k‖ ≤ 1) (_hμUnit : ∃ k, ‖μ k‖ = 1),
        ∃ P : SectorDecomposition (blockPhysDim d p),
          SameMPV₂Pos (blockTensor (d := d) (D := D) A p) P.toTensor ∧
          IsBNTCanonicalForm P) := by
  classical
  obtain ⟨p, hp, r, dim, μ, blocks, hDim, hTP, hPrim, hIrr, hInj, hμne, hSamePos⟩ :=
    exists_prepared_BNT_blocks_afterBlocking_pos (d := d) (D := D) A
  refine ⟨p, hp, r, dim, μ, blocks, hDim, hTP, hPrim, hIrr, hInj, hμne, hSamePos, ?_⟩
  intro hμLe hμUnit
  obtain ⟨P, hSame, hBNT⟩ :=
    exists_isBNTCanonicalForm_of_tp_primitive_irr_injective_blocks
      (d := blockPhysDim d p) (r := r) (dim := dim)
      μ blocks hDim hTP hPrim hIrr hInj hμne hμLe hμUnit
  refine ⟨P, ?_, hBNT⟩
  -- Chain the positive-length MPV identity with the prepared-block agreement.
  -- `hSamePos`: `mpv (blockTensor A p) σ = mpv (toTensorFromBlocks μ blocks) σ` for `N > 0`.
  -- `hSame`:    `mpv P.toTensor σ = mpv (toTensorFromBlocks μ blocks) σ` for all `N`.
  intro N hN σ
  exact (hSamePos N hN σ).trans (hSame N σ).symm

end MPSTensor
