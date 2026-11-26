/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.JointGroundSpaceIntersection
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicGroundSpaceIndependence
import TNLean.MPS.ParentHamiltonian.Interaction.PeriodicOriginalIntersection
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport

/-!
# Primitive-family intersections from support-space independence

For finitely many inequivalent normalized primitive tensors with faithful
invariant matrices, mixed-overlap decay gives eventual independence of their
middle support spaces. The geometric joint-intersection criterion then combines
the individual period-one intersection identities. Contiguous iteration yields
exact canonical open kernels and a positive parent interaction.

The general family criterion requires only eventual middle independence and
the individual intersection identities. The primitive-family argument assumes
no simultaneous word span and does not ask the weighted direct sum to be
irreducible or injective.

**Scope restriction (primitive generating family):** The last three statements
concern explicitly supplied primitive faithful tensors and their gauge-phase
inequivalence. The source's arbitrary GVBS presentation remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4, Proposition
forintersection, Lemmas disjoint and intersectionequivalence, and
Lemma existenceinteraction in Section 5, equations (3.10)--(3.13).

It also contains the following results.

* `MPSTensor.toMatrix'_parentInteraction_eq_of_groundSpaceES_eq`,
  `MPSTensor.hamiltonian_parentChainInteraction_eq_of_groundSpaceES_eq`: canonical interactions
  determined by their local support.
* `exists_posSemidef_eq_toMatrix'_parentInteraction_of_ker_hamiltonian_parentChainInteraction`
  (in `MPSTensor`):
  the positive canonical interaction from exact open kernels.
-/

section OpenInteraction

/-!
## The positive canonical interaction from exact open kernels

An exact kernel identity for the canonical range-\(R\) open Hamiltonian gives
an explicit positive local interaction with those same open kernels. The
witness is recorded as the canonical projection matrix itself. This equality
retains the literal local support when subsequent gap and state arguments
use the constructed interaction.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `existenceinteraction`,
lines 2195--2230, the orthogonal-complement construction of the interaction.
-/

open scoped ComplexOrder
namespace MPSTensor
variable {d D R : ℕ}

open ManyBody.Interaction (chainTranslates) in
/-- Exact kernels of the Hamiltonians of the parent interaction on the open chain give a positive
semidefinite interaction equal to the matrix of the canonical parent interaction, with the same
kernels at every volume at least its range. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma `existenceinteraction`, lines 2195--2230. -/
theorem exists_posSemidef_eq_toMatrix'_parentInteraction_of_ker_hamiltonian_parentChainInteraction
    (A : MPSTensor d D)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
        groundSpaceES A N) :
    ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h = LinearMap.toMatrix' (parentInteraction A R) ∧ h.PosSemidef ∧
      ∀ N, R ≤ N →
        LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
          groundSpaceES A N :=
  ⟨LinearMap.toMatrix' (parentInteraction A R), rfl, posSemidef_toMatrix'_parentInteraction A R,
    hKernel⟩

end MPSTensor

end OpenInteraction

section PrimitiveFamilyIntersection

open Filter
open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d : ℕ}

variable {ι : Type*} [Finite ι] {dim : ι → ℕ}

/-- Eventual middle-space independence and the individual eventual one-step
intersection identities imply the eventual joint intersection identity.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4, Proposition
forintersection and Lemma intersectionequivalence. -/
theorem eventually_iSup_groundSpace_restriction_intersection_of_independent_middle
    (A : ∀ j, MPSTensor d (dim j))
    (hIndep : ∀ᶠ n in atTop, iSupIndep (fun j => groundSpace (A j) n))
    (hInter : ∀ j, ∀ᶠ n in atTop,
      ((⨅ b : Fin d, (groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
        ⨅ a : Fin d, (groundSpace (A j) (n + 1)).comap (restrictFirstₗ a)) =
        groundSpace (A j) (n + 2)) :
    ∀ᶠ n in atTop,
      ((⨅ b : Fin d, (⨆ j, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
        ⨅ a : Fin d, (⨆ j, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a)) =
        ⨆ j, groundSpace (A j) (n + 2) := by
  filter_upwards [hIndep, Filter.eventually_all.mpr hInter] with n hn hStep
  exact iSup_groundSpace_eq_restriction_intersection_of_middle_independent A hn hStep

/-- A finite family of inequivalent primitive tensors with faithful
invariant matrices has the joint one-step intersection property at every
sufficiently large length. Middle-space independence follows from overlap
decay; the individual intersections follow from period-one periodicity.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4,
Proposition forintersection, Lemmas disjoint and intersectionequivalence. -/
theorem eventually_iSup_groundSpace_restriction_intersection_of_hasComplementaryFixedPointGap
    [∀ j, NeZero (dim j)]
    (A : ∀ j, MPSTensor d (dim j))
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∀ᶠ n in atTop,
      ((⨅ b : Fin d, (⨆ j, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
        ⨅ a : Fin d, (⨆ j, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a)) =
        ⨆ j, groundSpace (A j) (n + 2) := by
  have hPeriodic : ∀ j, IsPeriodic 1 (A j) := fun j =>
    (IsPeriodic.one_iff_primitive (A j)).mpr
      ⟨(hP j).isIrreducibleFamily_of_posDef (hρ j), (hP j).norm, (hP j).isPrimitive⟩
  apply eventually_iSup_groundSpace_restriction_intersection_of_independent_middle A
  · exact (eventually_groundSpaceES_iSupIndep_of_primitive A ρ hP hρ hDistinct).mono
      fun n hn => (groundSpace_iSupIndep_iff_groundSpaceES_iSupIndep A n).mpr hn
  · intro j
    obtain ⟨n₀, hn₀⟩ := (hPeriodic j).exists_eventually_groundSpace_restriction_intersection
    exact (eventually_ge_atTop n₀).mono fun n hn => hn₀ n hn

/-- The overlap and geometric-intersection argument gives, for a weighted primitive family, the
boundary-condition space as the kernel of the Hamiltonian of the parent interaction on the open
chain at every volume at least any sufficiently large interaction range. No joint word-span
condition is supplied. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4,
Lemma existenceinteraction, and equations (3.12)--(3.13). -/
theorem exists_ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_primitive_overlap
    [NeZero d] {r : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∃ R₀, 0 < R₀ ∧ ∀ R N, R₀ ≤ R → R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks μ A) R N).hamiltonian) =
        groundSpaceES (toTensorFromBlocks μ A) N := by
  apply exists_ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_eventually_intersection
  filter_upwards [
    eventually_iSup_groundSpace_restriction_intersection_of_hasComplementaryFixedPointGap
      A ρ hP hρ hDistinct] with n hn
  simpa only [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ] using hn

open ManyBody.Interaction (chainTranslates) in
/-- A weighted inequivalent primitive family admits a positive semidefinite canonical
interaction whose open-chain translates have exact joint kernels for all volumes at least its
range. The interaction is constructed from the overlap-based joint intersection. Source:
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1 and Lemma existenceinteraction, in the supplied
primitive-family setting. -/
theorem exists_positive_parent_interaction_of_primitive_overlap
    [NeZero d] {r : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧ ∀ N : ℕ, R ≤ N →
        LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
          groundSpaceES (toTensorFromBlocks μ A) N := by
  obtain ⟨R, hR, hKernel⟩ :=
    exists_ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_primitive_overlap
      μ A hμ ρ hP hρ hDistinct
  obtain ⟨h, _heq, hh, hKernelInteraction⟩ :=
    exists_posSemidef_eq_toMatrix'_parentInteraction_of_ker_hamiltonian_parentChainInteraction
      (toTensorFromBlocks μ A) (fun N => hKernel R N le_rfl)
  exact ⟨R, hR, h, hh, hKernelInteraction⟩

end MPSTensor

end PrimitiveFamilyIntersection

section CanonicalGroundSpaceTransport

/-!
## Canonical interactions determined by their local support

Equal local boundary spaces determine equal canonical interaction matrices
and equal open Hamiltonians. The tensors may have different bond dimensions.
Only the physical support space enters the canonical projection.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `existenceinteraction`,
lines 2195--2230, the orthogonal-complement construction of the interaction.
-/

namespace MPSTensor
variable {d DA DB R : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}

/-- Equal local support spaces give equal canonical interaction matrices,
also for tensors of different bond dimensions. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma `existenceinteraction`, lines 2195--2230. -/
theorem toMatrix'_parentInteraction_eq_of_groundSpaceES_eq
    (h : groundSpaceES A R = groundSpaceES B R) :
    LinearMap.toMatrix' (parentInteraction A R) = LinearMap.toMatrix' (parentInteraction B R) := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_toMatrix'_parentInteraction, toEuclideanLin_toMatrix'_parentInteraction, h]

/-- Equal local support spaces give equal Hamiltonians of the parent interaction on the open
chain at every volume, independently of the bond dimensions. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma `existenceinteraction`, lines 2195--2230. -/
theorem hamiltonian_parentChainInteraction_eq_of_groundSpaceES_eq
    (h : groundSpaceES A R = groundSpaceES B R) (N : ℕ) :
    (parentChainInteraction A R N).hamiltonian = (parentChainInteraction B R N).hamiltonian := by
  have hP : parentInteraction A R = parentInteraction B R := by
    simp only [parentInteraction, h]
  unfold parentChainInteraction
  rw [hP]

end MPSTensor

end CanonicalGroundSpaceTransport
