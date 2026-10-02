/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualBoundaryOverlap
import TNLean.MPS.ParentHamiltonian.CyclicPrimitiveSectorDecomposition

/-!
# Residual-sector projection comparison for periodic tensors

Blocking a periodic tensor by its period gives primitive cyclic sectors with
faithful invariant matrices. Periodicity excludes gauge-phase repetitions
between distinct cyclic corners. Retaining their support isometries identifies
the original ground space at every length with the sum of the correlated
rectangular residual boundary ranges.

As the blocked prefix grows, the sum of the residual-sector projections
approaches the original full ground projection. The original tail length may
vary arbitrarily. Primitive fixed points and sector separation are derived
from periodicity, rather than supplied as hypotheses. Positive virtual
dimensions are likewise derived; no ambient dimension instance is assumed.
This is a comparison between the sector projection sum and the full ground
projection, not an overlapping-window defect or an all-residue gap theorem.

Source: DCCSP17, arXiv:1708.00029, Lemma `bdcf`, lines 404--423,
and Lemma `lem:blocking-arbitrary`, lines 434--451; Nachtergaele,
arXiv:cond-mat/9410110, Lemma `disjoint`, lines 1744--1820, and
Lemma `commutation` (i), lines 2442--2531.
-/

open Filter
open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D m : ℕ}

/-- A periodic tensor admits primitive faithful inequivalent residual sectors
whose ranges give the exact original ground space at every length, including
zero. Their projection sum approaches the original ground projection for every
varying tail length. All normalization and separation data are derived.
Source: DCCSP17, arXiv:1708.00029, Lemma `bdcf`, lines 404--423;
Nachtergaele, arXiv:cond-mat/9410110, Lemmas `disjoint` and `commutation` (i). -/
theorem IsPeriodic.exists_residual_primitive_projection_sum
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (hdim : ∀ j, 0 < dim j),
      let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
      ∃ (B : ∀ j, MPSTensor (blockPhysDim d m) (dim j))
        (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
        (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
        (∀ j, IsPrimitiveMPS (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
        BlocksNotGaugePhaseEquiv B ∧
        (∀ j, (V j)ᴴ * V j = 1) ∧ (∑ j, V j * (V j)ᴴ) = 1 ∧
        (∀ j i, (V j)ᴴ * blockTensor A m i = B j i * (V j)ᴴ) ∧
        (∀ N r, groundSpaceES A (N * m + r) =
          ⨆ j, (blockedResidualBoundaryMapES A m (B j) (V j) N r).range) ∧
        (∀ r : ℕ → ℕ, Tendsto (fun N =>
          ‖(∑ j, ((blockedResidualBoundaryMapES A m (B j) (V j) N (r N)).range).starProjection) -
            (groundSpaceES A (N * m + r N)).starProjection‖) atTop (nhds 0)) := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨dim, hdim, B, P, V, ρ, hP, hρ, hDistinct, hproj, hsum,
    hShift, hiso, hV, hInt, hCoInt⟩ := hA.exists_cyclic_primitive_sector_resolution
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hResolution : (∑ j, V j * (V j)ᴴ) = 1 := by simpa only [hV] using hsum
  have hGS (N r : ℕ) :=
    groundSpaceES_eq_iSup_range_blockedResidualBoundaryMapES A B V hResolution hCoInt N r
  have hSep : ∀ i j : Fin m, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := by
    intro i j hij e
    simpa only [eqRec_eq_cast] using hDistinct j i hij.symm e
  refine ⟨dim, hdim, B, V, ρ, hP, hρ,
    hDistinct, hiso, hResolution, hCoInt, hGS, ?_⟩
  intro r
  simpa only [hGS, id_eq] using tendsto_norm_residual_sector_projection_sum_sub_iSup_zero
    A B V ρ hP hρ hSep (N := id) (r := r) tendsto_id

end MPSTensor
