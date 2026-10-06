/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedFiniteGapTransport
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyPresentation
import TNLean.MPS.ParentHamiltonian.GaugePhaseSeparationTransport

/-!
# Aligned finite-chain gaps for periodic block families

A finite weighted family of normalized periodic tensors admits an exact
primitive faithful presentation after blocking by any positive common period
multiple. A positive interaction with the eventual original joint MPS kernel
therefore has one gap on all volumes divisible by that blocking length.
The product of the periods supplies a positive blocking length automatically,
including the empty family, for which this product is one.

The norm inequality is measured on the orthogonal complement of the actual
finite-volume kernel. Short aligned volumes are included through the existing
finite minimum argument; no lower length bound remains in the conclusion.
The original family need not be pairwise inequivalent and no invariant
matrices are supplied.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
site grouping at lines 825--836, and Section 3, equations (3.12)--(3.14),
lines 1547--1570; DCCSP17, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451.

**Scope restriction (common-period divisible lengths):** The conclusions
concern lengths divisible by the chosen common blocking length. Uniform gaps
for the other original residue lengths and identification of general GVBS
presentations remain separate. See
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace BigOperators
namespace MPSTensor
variable {d r R : ℕ} [NeZero d] {dim : Fin r → ℕ}

/-- Any positive common multiple of the sector periods gives a uniform gap
on all aligned volumes, under positivity and the eventual original kernel
identity. The gap is measured on each volume's actual kernel complement,
including short volumes. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2 and Section 3, equations (3.12)--(3.14), lines 1547--1570;
DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451. -/
theorem exists_aligned_openInteractionMatrix_gap_of_periodic_family_of_dvd
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (L : ℕ) (hL : 0 < L) (hdiv : ∀ j, m j ∣ L)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) n) =
        groundSpaceES (toTensorFromBlocks μ A) n) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (openInteractionMatrix h (N * L))))ᗮ,
        γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) v‖ := by
  obtain ⟨g, bdim, hdim, B, ρ, hP, hρ, hDistinct, hJoint⟩ :=
    exists_primitive_blockFamilyPresentation_of_period_dvd μ A hμ m hPeriodic L hL hdiv
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let : ∀ j, NeZero (bdim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hcover : R + L ≤ (R + 1) * L + 1 := by nlinarith [hL]
  exact exists_aligned_openInteractionMatrix_gap_of_blocked_primitive_family
    (K := R + 1) (toTensorFromBlocks μ A) (fun _ => 1) B (fun _ => one_ne_zero)
    ρ hP hρ hDistinct.forall_ne_transport hJoint h hh hR (by omega) hcover hker

/-- A finite periodic weighted family and eventual original open-chain kernels
have a positive blocking length with one gap on every aligned volume.
No faithful fixed-point witnesses or original sector inequivalence are supplied.
The family may be empty. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, site grouping at lines 825--836, and Section 3;
DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451. -/
theorem exists_aligned_openInteractionMatrix_gap_of_periodic_family
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) n) =
        groundSpaceES (toTensorFromBlocks μ A) n) :
    ∃ L : ℕ, 0 < L ∧ ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (openInteractionMatrix h (N * L))))ᗮ,
        γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) v‖ := by
  have hL : 0 < ∏ j, m j := Finset.prod_pos fun j _ => (hPeriodic j).period_pos
  exact ⟨∏ j, m j, hL,
    exists_aligned_openInteractionMatrix_gap_of_periodic_family_of_dvd
      μ A hμ m hPeriodic _ hL (fun j => Finset.dvd_prod_of_mem m (Finset.mem_univ j))
      h hh hR hker⟩
end MPSTensor
