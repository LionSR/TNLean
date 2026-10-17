/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PinnedNestedFilters
import TNLean.PEPS.Approximation.SquareAreaLawHamiltonian
import QICLean.Entropy.FilterOutputCovariance
import QICLean.Entropy.RegionUnion

/-!
# Original-grid filter families in canonical square coordinates

The adapted positive filters are equivalent, at positive weights, to all
floor-zero feasible regional matrices. The ascending source action and its
inverse-norm normalization agree exactly with the canonical ordered product.
The inverse conversion covers every feasible competitor, not a spectral subclass.

Source conventions: openai/math revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, companion
`lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean`, lines 151–179.
Independently formalized using the existing QICLean feasibility, configuration
and ordered-output results; no upstream Lean proof text is reused. These are
compatibility results for the attributed adapted types, not unimported OAI types.
No nesting, positive dimension, invertibility or nonzero-output assumption is used.
-/

noncomputable section

open Matrix

namespace TNLean.PEPS.Approximation.Pinned

/-- The adapted complement-agreement matrix is the existing local lift. -/
theorem liftLocal_eq_localLift {L q : ℕ} (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ) :
    liftLocal X A = Entropy.localLift (n := fun _ ↦ q) X A := by
  ext x y
  exact (Entropy.localLift_apply X A x y).symm

namespace NestedFilter

variable {L q m : ℕ} {X : Fin m → Finset (Vertex L)}

/-- Bundled filters are determined by their matrices. -/
@[ext] theorem PositiveFilter.ext {Y : Finset (Vertex L)}
    {F G : PositiveFilter q Y} (h : F.matrix = G.matrix) : F = G := by
  cases F
  cases G
  cases h
  rfl

private def extendRegions (X : Fin m → Finset (Vertex L)) (k : ℕ) :
    Finset (Vertex L) :=
  if h : k < m then X ⟨k, h⟩ else ∅

private theorem extendRegions_fin (X : Fin m → Finset (Vertex L)) (j : Fin m) :
    extendRegions X j = X j := by
  simp only [extendRegions, dif_pos j.isLt]

/-- The supplied finite regions in integer-square coordinates, extended by empty
regions only to meet the existing natural-indexed ordered-chain API. -/
def canonicalRegions (X : Fin m → Finset (Vertex L)) (k : ℕ) :
    Finset (AreaLaw.Site (AreaLaw.rectangularDomain L L)) :=
  (extendRegions X k).map (AreaLaw.rectangleSiteEquiv L L).toEmbedding

/-- The extension has exactly the supplied regions at every family index. -/
@[simp] theorem canonicalRegions_fin (X : Fin m → Finset (Vertex L)) (j : Fin m) :
    canonicalRegions X j = (X j).map (AreaLaw.rectangleSiteEquiv L L).toEmbedding := by
  rw [canonicalRegions, extendRegions_fin]

/-- Regional configuration coordinates, using the existing dependent equivalence. -/
def regionEquiv (X : Fin m → Finset (Vertex L)) (j : Fin m) :
    RegionConfiguration q (X j) ≃ Entropy.RegionConfig
      (fun _ : AreaLaw.Site (AreaLaw.rectangularDomain L L) ↦ q) (canonicalRegions X j) :=
  Entropy.regionConfigurationEquiv (n := fun _ : Vertex L ↦ q)
    (n' := fun _ : AreaLaw.Site (AreaLaw.rectangularDomain L L) ↦ q)
    (X j) (canonicalRegions X j) (AreaLaw.rectangleSiteEquiv L L)
    (by intro v; simp) (fun _ ↦ Equiv.refl (Fin q))

/-- All regional matrix families on the transported supplied regions. -/
abbrev CanonicalFamily (q : ℕ) (X : Fin m → Finset (Vertex L)) :=
  (j : Fin m) → Matrix
    (Entropy.RegionConfig (fun _ : AreaLaw.Site (AreaLaw.rectangularDomain L L) ↦ q)
      (canonicalRegions X j))
    (Entropy.RegionConfig (fun _ : AreaLaw.Site (AreaLaw.rectangularDomain L L) ↦ q)
      (canonicalRegions X j)) ℂ

/-- The regional matrices of a bundled family in canonical square coordinates. -/
def canonicalMatrices (F : FilterFamily q m X) : CanonicalFamily q X :=
  fun j ↦ reindex (regionEquiv X j) (regionEquiv X j) (F j).matrix

/-- Every feasible canonical family gives a bundled positive family on the original grid. -/
def fromCanonical {a : Fin m → ℝ} (K : CanonicalFamily q X)
    (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j)) : FilterFamily q m X :=
  fun j ↦ ⟨reindex (regionEquiv X j).symm (regionEquiv X j).symm (K j),
    ((hK j).reindex (regionEquiv X j).symm).posSemidef le_rfl⟩

/-- Pulling a feasible competitor back and then forward returns exactly that competitor. -/
@[simp] theorem canonicalMatrices_fromCanonical {a : Fin m → ℝ}
    (K : CanonicalFamily q X) (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j)) :
    canonicalMatrices (fromCanonical K hK) = K := by
  funext j
  simp [canonicalMatrices, fromCanonical, reindex_apply]

/-- The reverse round trip preserves the positive bundle, including its proof field. -/
@[simp] theorem fromCanonical_canonicalMatrices {a : Fin m → ℝ}
    (F : FilterFamily q m X)
    (hF : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (canonicalMatrices F j)) :
    fromCanonical (canonicalMatrices F) hF = F := by
  funext j
  apply PositiveFilter.ext
  simp [fromCanonical, canonicalMatrices, reindex_apply]

/-- Source eigenvalue normalization is exactly floor-zero matrix feasibility. -/
theorem admissible_iff_feasible (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (F : FilterFamily q m X) :
    Admissible a F ↔ ∀ j, Entropy.IsFeasibleFilter 0 (a j) (canonicalMatrices F j) := by
  simp only [Admissible, canonicalMatrices, Entropy.isFeasibleFilter_reindex_iff]
  exact forall_congr' fun j ↦
    (Entropy.isFeasibleFilter_zero_iff_eigenvalues (ha j) (F j).positive).symm

/-- The pullback of every feasible family has the source eigenvalue normalization. -/
theorem admissible_fromCanonical (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (K : CanonicalFamily q X) (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j)) :
    Admissible a (fromCanonical K hK) := by
  rw [admissible_iff_feasible a ha, canonicalMatrices_fromCanonical]
  exact hK

/-- The existing physical isometry is the generic site relabelling with identity basis maps. -/
theorem squareAreaLawState_eq_relabelVector (Ω : State L q) :
    squareAreaLawState Ω = Entropy.relabelVector
      (n := fun _ : Vertex L ↦ q)
      (n' := fun _ : AreaLaw.Site (AreaLaw.rectangularDomain L L) ↦ q)
      (AreaLaw.rectangleSiteEquiv L L) (fun _ ↦ Equiv.refl (Fin q)) Ω := by
  ext σ
  rfl

private def extendedMatrices (F : FilterFamily q m X) :
    (j : Fin m) → Matrix (Entropy.RegionConfig (fun _ : Vertex L ↦ q) (extendRegions X j))
      (Entropy.RegionConfig (fun _ : Vertex L ↦ q) (extendRegions X j)) ℂ :=
  fun j ↦ by simpa only [extendRegions_fin] using (F j).matrix

private theorem output_eq_extended_chain (F : FilterFamily q m X) (Ω : State L q) :
    output F Ω = toEuclideanLin
      (Entropy.liftProd (Entropy.chainList (extendRegions X) (extendedMatrices F)
        fun _ ↦ True)) Ω := by
  simpa only [output, asMap, liftLocal_eq_localLift, extendedMatrices,
    extendRegions_fin] using
    Entropy.foldl_localLift_eq_liftProd_chainList (extendRegions X) (extendedMatrices F) Ω

/-- The actual adapted ascending output equals the canonical reverse-product action.
Every matrix occurrence is retained; no commutation or nesting is assumed. -/
theorem squareAreaLawState_output (F : FilterFamily q m X) (Ω : State L q) :
    squareAreaLawState (output F Ω) =
      toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) (canonicalMatrices F) fun _ ↦ True))
        (squareAreaLawState Ω) := by
  rw [output_eq_extended_chain, squareAreaLawState_eq_relabelVector,
    squareAreaLawState_eq_relabelVector]
  have hD (k : ℕ) (v : Vertex L) :
      v ∈ extendRegions X k ↔
        AreaLaw.rectangleSiteEquiv L L v ∈ canonicalRegions X k := by
    simp [canonicalRegions]
  simpa only [extendedMatrices, extendRegions_fin, canonicalMatrices, regionEquiv] using
    Entropy.relabelVector_liftProd_chainList
      (n := fun _ : Vertex L ↦ q)
      (n' := fun _ : AreaLaw.Site (AreaLaw.rectangularDomain L L) ↦ q)
      (extendRegions X) (canonicalRegions X) (AreaLaw.rectangleSiteEquiv L L)
      hD (fun _ ↦ Equiv.refl (Fin q)) (extendedMatrices F) (fun _ ↦ True) Ω

/-- Inverse-norm normalization commutes with the same exact output identification,
including zero output. -/
theorem squareAreaLawState_normalizedOutput (F : FilterFamily q m X) (Ω : State L q) :
    let ψ := toEuclideanLin (Entropy.liftProd
      (Entropy.chainList (canonicalRegions X) (canonicalMatrices F) fun _ ↦ True))
      (squareAreaLawState Ω)
    squareAreaLawState (normalizedOutput F Ω) = ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ := by
  dsimp only
  rw [← squareAreaLawState_output, norm_squareAreaLawState]
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (AreaLaw.rectangleConfigurationEquiv L L q)).map_smul _ _

private theorem norm_canonical_output (F : FilterFamily q m X) (Ω : State L q) :
    ‖toEuclideanLin (Entropy.liftProd
      (Entropy.chainList (canonicalRegions X) (canonicalMatrices F) fun _ ↦ True))
      (squareAreaLawState Ω)‖ = ‖output F Ω‖ := by
  rw [← squareAreaLawState_output, norm_squareAreaLawState]

/-- Source maximality is equivalent to canonical feasibility and comparison with
every feasible matrix family. The inverse conversion supplies all competitors. -/
theorem isMaximizer_iff (Ω : State L q) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (F : FilterFamily q m X) :
    IsMaximizer Ω a F ↔
      (∀ j, Entropy.IsFeasibleFilter 0 (a j) (canonicalMatrices F j)) ∧
      (∀ K : CanonicalFamily q X,
        (∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j)) →
        ‖toEuclideanLin (Entropy.liftProd
          (Entropy.chainList (canonicalRegions X) K fun _ ↦ True))
          (squareAreaLawState Ω)‖ ≤
        ‖toEuclideanLin (Entropy.liftProd
          (Entropy.chainList (canonicalRegions X) (canonicalMatrices F) fun _ ↦ True))
          (squareAreaLawState Ω)‖) := by
  constructor
  · rintro ⟨hF, hmax⟩
    refine ⟨(admissible_iff_feasible a ha F).mp hF, ?_⟩
    intro K hK
    have h := hmax (fromCanonical K hK) (admissible_fromCanonical a ha K hK)
    rw [← norm_canonical_output (fromCanonical K hK), ← norm_canonical_output F,
      canonicalMatrices_fromCanonical] at h
    exact h
  · rintro ⟨hF, hmax⟩
    refine ⟨(admissible_iff_feasible a ha F).mpr hF, ?_⟩
    intro G hG
    simpa only [norm_canonical_output] using
      hmax (canonicalMatrices G) ((admissible_iff_feasible a ha G).mp hG)

end NestedFilter
end TNLean.PEPS.Approximation.Pinned
