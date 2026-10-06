/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.OpenKernelOfIntersection
import TNLean.MPS.ParentHamiltonian.JointGroundSpaceIntersection
import TNLean.MPS.ParentHamiltonian.GroundSpaceIndependence
import TNLean.MPS.ParentHamiltonian.PeriodicOriginalIntersection
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionExistence

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
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4, Proposition
`forintersection`, Lemmas `disjoint` and `intersectionequivalence`, and
Lemma `existenceinteraction` in Section 5, equations (3.10)--(3.13).
-/

open Filter
open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d : ℕ}

variable {ι : Type*} [Finite ι] {dim : ι → ℕ}

/-- Eventual middle-space independence and the individual eventual one-step
intersection identities imply the eventual joint intersection identity.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4, Proposition
`forintersection` and Lemma `intersectionequivalence`. -/
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
Proposition `forintersection`, Lemmas `disjoint` and `intersectionequivalence`. -/
theorem eventually_iSup_groundSpace_restriction_intersection_of_isPrimitiveMPS
    [∀ j, NeZero (dim j)]
    (A : ∀ j, MPSTensor d (dim j))
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
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

/-- The overlap and geometric-intersection argument gives exact canonical
open kernels for a weighted primitive family, at every volume at least any
sufficiently large interaction range. No joint word-span condition is
supplied. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 4,
Lemma `existenceinteraction`, and equations (3.12)--(3.13). -/
theorem exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_primitive_overlap
    [NeZero d] {r : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∃ R₀, 0 < R₀ ∧ ∀ R N, R₀ ≤ R → R ≤ N →
      LinearMap.ker (openParentHamiltonianES (toTensorFromBlocks μ A) R N) =
        groundSpaceES (toTensorFromBlocks μ A) N := by
  apply exists_ker_openParentHamiltonianES_eq_groundSpaceES_of_eventually_restriction_intersection
  filter_upwards [eventually_iSup_groundSpace_restriction_intersection_of_isPrimitiveMPS
    A ρ hP hρ hDistinct] with n hn
  simpa only [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ] using hn

/-- A weighted inequivalent primitive family admits a positive canonical
interaction with exact joint open kernels for all volumes at least its
range. The interaction is constructed from the overlap-based joint
intersection. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1
and Lemma `existenceinteraction`, in the supplied primitive-family setting. -/
theorem exists_positive_parent_interaction_of_primitive_overlap
    [NeZero d] {r : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧ ∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks μ A) N := by
  obtain ⟨R, hR, hKernel⟩ :=
    exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_primitive_overlap
      μ A hμ ρ hP hρ hDistinct
  obtain ⟨h, _heq, hh, hKernelInteraction⟩ :=
    exists_positive_canonical_parent_interaction_of_exact_open_kernels
      (toTensorFromBlocks μ A) hR (fun N => hKernel R N le_rfl)
  exact ⟨R, hR, h, hh, hKernelInteraction⟩

end MPSTensor
