/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.MPS.SharedInfra.SectorDecomposition
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Spectral.TransferOperatorGapNT

open scoped Matrix BigOperators
open Filter

/-!
# Phase-class BNT sector data

This file builds BNT sector decompositions by quotienting a family of primitive
irreducible blocks by MPV phase equivalence.  It proves the representative
overlap data and transports finite-length MPV span identities through the chosen
phase classes.
-/

namespace MPSTensor

variable {d : ℕ}

/-! ### Phase-class quotient construction -/

/-- The concrete sector decomposition obtained from representatives of MPV phase classes.

Made non-`private` so the prepared-block SectorBNT constructor
(`TNLean.MPS.FundamentalTheorem.SectorBNT.Supplier`) can construct an
`IsBNTCanonicalForm P` directly on top of this concrete `P`, with full access
to the underlying phase-class representatives. -/
noncomputable def collapsedBntSectorDecomp
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0) : SectorDecomposition d :=
  let classes := mpvPhaseClassData blocks
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose
  let hζ_ne : ∀ j q, ζFn j q ≠ 0 :=
    fun j q => (classes.enum_phase j q).choose_spec.1
  let sectors : SectorWeightData classes.g := {
    copies := classes.copies
    copies_pos := classes.copies_pos
    weight := fun j q => ζFn j q * μ (classes.enum j q)
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j q) (hμne (classes.enum j q))
  }
  {
    basisCount := classes.g
    basisDim := fun j => dim (classes.repr j)
    basis := fun j => blocks (classes.repr j)
    sectors := sectors
  }

/-- The total tensor of `collapsedBntSectorDecomp` has the same MPV at every length
as the original `toTensorFromBlocks μ blocks`.  Exposed (was previously `private`)
for the prepared-block SectorBNT constructor. -/
theorem collapsedBntSectorDecomp_sameMPV₂
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0) :
    SameMPV₂ (collapsedBntSectorDecomp (d := d) μ blocks hμne).toTensor
      (toTensorFromBlocks (d := d) (μ := μ) blocks) := by
  classical
  let classes := mpvPhaseClassData blocks
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose
  have hζ_mpv : ∀ j q (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks (classes.enum j q)) σ = (ζFn j q) ^ N * mpv (blocks (classes.repr j)) σ :=
    fun j q N σ => (classes.enum_phase j q).choose_spec.2 N σ
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  intro N σ
  calc mpv P.toTensor σ
      = ∑ j : Fin P.basisCount,
          ∑ q : Fin (P.copies j), (P.weight j q) ^ N * mpv (P.basis j) σ :=
          P.mpv_toTensor_eq_sum_sectors σ
    _ = ∑ j : Fin classes.g,
          ∑ q : Fin (classes.copies j),
            (ζFn j q * μ (classes.enum j q)) ^ N *
              mpv (blocks (classes.repr j)) σ := by
            rfl
    _ = ∑ j : Fin classes.g,
          ∑ q : Fin (classes.copies j),
            (μ (classes.enum j q)) ^ N * mpv (blocks (classes.enum j q)) σ := by
            refine Finset.sum_congr rfl (fun j _ =>
              Finset.sum_congr rfl (fun q _ => ?_))
            rw [mul_pow, hζ_mpv j q N σ]
            ring
    _ = ∑ k : Fin r, (μ k) ^ N * mpv (blocks k) σ :=
          classes.regroup (fun k => (μ k) ^ N * mpv (blocks k) σ)
    _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
            symm
            simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ

/-- **Total dimension of a dimension-preserving phase-class quotient.**

If every block in an MPV phase class has the same bond dimension as the
chosen representative of that class, then the collapsed BNT sector
decomposition has the same total bond dimension as the original direct sum.

This is the length-zero dimension statement needed in the arbitrary-input
supplier: without the displayed same-dimension hypothesis, the quotient is
allowed to identify MPV-phase-equivalent blocks of differing bond dimensions,
and the length-zero MPV coefficient need not be preserved by dimension counting
alone. -/
theorem collapsedBntSectorDecomp_totalDim_eq_sum_dim
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0)
    (hDim : ∀ j q,
      dim ((mpvPhaseClassData blocks).enum j q) =
        dim ((mpvPhaseClassData blocks).repr j)) :
    (collapsedBntSectorDecomp (d := d) μ blocks hμne).totalDim =
      ∑ k : Fin r, dim k := by
  classical
  let classes := mpvPhaseClassData blocks
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hRegroupC :
      (∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
          (dim (classes.enum j q) : ℂ)) =
        ∑ k : Fin r, (dim k : ℂ) :=
    classes.regroup (fun k : Fin r => (dim k : ℂ))
  have hRegroupN :
      (∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
          dim (classes.enum j q)) =
        ∑ k : Fin r, dim k := by
    exact_mod_cast hRegroupC
  have hRepEnum :
      (∑ j : Fin classes.g, ∑ q : Fin (classes.copies j), dim (classes.repr j)) =
        ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
          dim (classes.enum j q) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (hDim j q).symm
  have hFlat :
      P.totalDim =
        ∑ x : (j : Fin classes.g) × Fin (classes.copies j), dim (classes.repr x.1) := by
    change (∑ s : Fin (∑ j : Fin classes.g, classes.copies j),
        dim (classes.repr ((finSigmaFinEquiv.symm s).1))) =
      ∑ x : (j : Fin classes.g) × Fin (classes.copies j), dim (classes.repr x.1)
    symm
    simpa using
      (Equiv.sum_comp
        (finSigmaFinEquiv (m := classes.g) (n := classes.copies))
        (fun s : Fin (∑ j : Fin classes.g, classes.copies j) =>
          dim (classes.repr ((finSigmaFinEquiv.symm s).1))))
  calc
    P.totalDim =
        ∑ x : (j : Fin classes.g) × Fin (classes.copies j), dim (classes.repr x.1) := hFlat
    _ = ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j), dim (classes.repr j) := by
      rw [Fintype.sum_sigma]
    _ = ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j), dim (classes.enum j q) :=
      hRepEnum
    _ = ∑ k : Fin r, dim k := hRegroupN

/-- `collapsedBntSectorDecomp` carries `HasBNTSectorData`.  Exposed (was previously
`private`) for the prepared-block SectorBNT constructor. -/
theorem collapsedBntSectorDecomp_hasBNT
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    HasBNTSectorData (d := d) (collapsedBntSectorDecomp (d := d) μ blocks hμne) := by
  classical
  let classes := mpvPhaseClassData blocks
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ
        (fun j : Fin classes.g => mpvState (d := d) (blocks (classes.repr j)) N) := by
    apply exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal
      (fun j : Fin classes.g => blocks (classes.repr j))
    · intro j
      exact overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
        (blocks (classes.repr j)) (hIrr (classes.repr j))
        (hTP (classes.repr j)) (hPrim (classes.repr j))
    · intro i j hij
      exact cross_overlap_tendsto_zero_of_separated_normal_bnt_data
        (fun j : Fin classes.g => blocks (classes.repr j))
        (HasIrreducibleBlocks.ofForall (fun j => hIrr (classes.repr j)))
        (IsLeftCanonicalBlockFamily.ofForall (fun j => hTP (classes.repr j)))
        classes.blocks_not_equiv i j hij
  simpa [P, collapsedBntSectorDecomp] using hLI





end MPSTensor
