/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Algebra.UnitaryMulVecInner
import TNLean.PEPS.GInjectiveConcatenation
import TNLean.PEPS.GInjectiveMPS

/-!
# G-isometric tensors: stability under concatenation and virtual unitaries

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Section 6,
`Papers/1001.3807/paper_v3.tex`:

* the tensor `A†` with `𝒫(A†) = 𝒫(A)†`, lines 1668–1686;
* Definition 6.1 (`def:iso:isopeps`), lines 1692–1700: a `G`-injective PEPS is `G`-isometric if
  `U_g = L_g` is the left-regular representation, `L_g|h⟩ = |gh⟩`, and `𝒫(A)⁻¹ = 𝒫(A†)`, or
  equivalently `𝒫(A)` restricted to its domain and range is unitary;
* Lemma 6.2 (`lemma:iso:iso-stable-under-concat`), lines 1704–1716: `G`-isometry is stable
  under concatenation. The proof: for `U_g = L_g`, `Δ = |G|⁻¹ 𝟙`, so the left inverse of the
  concatenated tensor in equation `eq:noninj:linv` is `(B^j)†(A^i)† = (A^i B^j)†`;
* Lemma 6.3 (`lemma:iso:sym-virt-can-be-done-on-phys`), lines 1729–1761, figures
  `figs4/V-comm-w-sym.pdf`, `figs4/phys-op-from-V.pdf`, `figs4/phys-op-from-V-action.pdf` and
  `figs4/virt-op-from-phys.pdf`: for a `G`-isometric tensor, the unitaries `V` on the virtual
  level that can be implemented by a unitary on the physical system are exactly those commuting
  with the symmetry (equation `eq:iso:V-comm-sym`). One direction takes the physical operation
  `𝒫(A) V 𝒫(A)⁻¹`; the other takes `V = 𝒫(A)⁻¹ U 𝒫(A)` and uses
  equation `eq:inj:rightinv-always`.

**Formalized here.** The source illustrates its proofs in one dimension (lines 1688–1689), and
the proof of Lemma 6.2 uses the one-dimensional left inverse `eq:noninj:linv` of Lemma 4.7. For an
MPS tensor `A : ι → End ℂ[G]` with the left-regular representation on its bond,
`𝒫(A†) |i⟩ = (A^i)†` (`mpsAdjointSiteMap`), the adjoint being taken in the basis of group
elements (`regularAdjoint`). `IsGIsometricMPS A` is Definition 6.1 in its first form,
`𝒫(A)⁻¹ = 𝒫(A†)`, up to the positive factor of the Local fix below. The step `Δ = |G|⁻¹ 𝟙` of
the proof of Lemma 6.2 is `concatLeftInverse_leftRegular` in one dimension and
`linkContractionLeftInverse_leftRegular` for the two-dimensional link contraction of Lemma 5.2:
with the regular representation on the contracted link, the left inverse of the concatenation is
the plain composition (contraction) of the left inverses. The identity `(B^j)†(A^i)† = (A^i B^j)†`
is `concatLeftInverse_mpsAdjointSiteMap`, and Lemma 6.2 is `IsGIsometricMPS.concatTensor`, with
the factors multiplying.

Lemma 6.3 is stated for the general predicate `TNLean.PEPS.IsGIsometric` on coordinate spaces.
Its proof uses the isometry of `𝒫(A)` on the invariant subspace and no property of the
left-regular representation, so it is stated for the representation parameter of that
predicate. The source's standing assumption from Observation `obs:surjective`
(lines 541–554), invoked again for isometric PEPS on lines 1670–1674, that the physical system
is the range of `𝒫(A)` (equation `eq:inj:rightinv-always`), is the hypothesis
`Function.Surjective T`; the source's physical
operation `𝒫(A) V 𝒫(A)⁻¹` is unitary only under it. The two directions are
`IsGIsometric.exists_unitary_comp_eq` and `IsGIsometric.exists_comp_eq_of_unitary`; the virtual
operation `V = 𝒫(A)⁻¹ U 𝒫(A)` of the second is `G`-invariant on both sides and unitary on the
invariant subspace, which is where the source says it acts (lines 1722–1728).

The one-dimensional concatenation theorem is `IsGIsometricMPS.concatTensor`, the case in which
the source writes its proof. The elementary two-dimensional step is proved in
`TNLean.PEPS.GIsometricConcatenation`: the contraction of adjoints is the adjoint of the
contracted map, and `IsGIsometric.linkContraction_fourLeg` joins two square-lattice tensors
along one regular virtual bond. The more general `IsGIsometric.linkContraction` allows
unitary actions on the remaining legs. The Gram identity for an arbitrary connected
untwisted regular-bond region, including its internal cycles and normalization factor,
is proved in `TNLean.PEPS.RegularRegionGram`. The physical entropy of an untwisted
finite cut with both sides connected is proved in `TNLean.PEPS.RegularRegionEntropy`.
`TNLean.PEPS.RegularRegionIsometry` derives the block's `G`-isometry from this
Gram identity and the translation invariance of the actual contraction.
The actual open tensor and the contraction of canonical averaging-projector sites
are related in both directions by physical product maps in
`TNLean.PEPS.RegularProjectorOpenRegion`.
`TNLean.PEPS.RegularPhysicalUnitaryTransport` derives a unitary implementation
on the original physical region for every canonical unitary commuting with the
product of its local regular invariant projectors. The product Gram identity
is derived from local isometry; unused physical dimensions are allowed.
`TNLean.PEPS.RegularRegionCoordinates` constructs reversible spanning-tree
coordinates, and `TNLean.PEPS.RegularRegionProjectorCoordinates` computes the
canonical tensor in these coordinates: its boundary factor is the regular
projector, its internal reference and normalized vertex coordinates are uniform,
and its residual cycle coordinates are fixed to the identity.
`TNLean.PEPS.RegularRegionInjectivity` uses one row of this coordinate formula
to prove that an actual connected regular block is `G`-injective from local
`G`-injectivity alone, allowing internal cycles and empty boundaries.
For inserted bond operators, `TNLean.PEPS.RegularProjectorTwistedRegion`
gives both accessibility identities with the same physical maps for every
choice of operators, including those on crossing bonds.
`TNLean.PEPS.RegularRegionTreeGauge` removes tree-edge operators and records
the remaining cycle operators and boundary transport explicitly.
`TNLean.PEPS.RegularTwistedRegionProjectorCoordinates` computes the actual
twisted canonical block in these coordinates: one common group translation
relates the boundary labels and simultaneously conjugates every cycle residual.
`TNLean.PEPS.RegularRegionGaugeContraction` implements the vertex gauge inside
the original open-region sum. When its internal residuals are identities,
`TNLean.PEPS.RegularRegionGaugeGram` derives a positive Gram factor multiplying
the transported boundary projector of `TNLean.PEPS.RegularRegionGaugeBoundary`.
`TNLean.PEPS.RegularClosedGauge` proves equality of the actual closed vectors
under endpoint gauge changes, using local regular invariance alone.
`TNLean.PEPS.RegularTwistedRegionCrossGramCoordinates` computes the exact
mixed Gram matrix of two canonical blocks and proves orthogonality when
their residual cycle tuples are not simultaneously conjugate.
For commuting native torus closures, `TNLean.PEPS.TorusRegionLiftGauge`
constructs the gauge from a supplied integer lift preserving internal unit
steps. `TNLean.PEPS.TorusRegionLiftGram` derives its actual transported Gram
matrix and rank; `TNLean.PEPS.TorusRegionLiftCoordinates` derives a canonical
factorization with one normalized internal vector common to all such sectors.
The supplied arithmetic lift remains distinct from the geometric disk condition.
`TNLean.PEPS.TorusRegionRealization` constructs the actual closed-cell union,
proves local path connectedness, and obtains its integer unit-step lift from
geometric simple connectedness. `TNLean.PEPS.TorusSimplyConnectedRegionRank`
therefore derives the actual rank for commuting closures on graph-connected
regions with simply connected cell realizations, without a supplied lift.
`TNLean.PEPS.RegularWalkHolonomy` supplies the nonabelian transport identities
along native graph walks, including endpoint-gauge covariance, reversal and
concatenation. These are the path identities needed to express complement
boundary transports through its accessible cycle coordinates.
`TNLean.PEPS.RegularRegionCycleHolonomy` constructs actual free-group words
from induced-region walks and evaluates them at the native cycle residuals.
`TNLean.PEPS.RegularBoundaryRoute` identifies the composition of the two
boundary transports with the endpoint-gauged crossing operator and derives
its relative multiplier from an actual closed route through the two trees.
`TNLean.PEPS.TorusWalkWinding` computes the actual commuting closure transport
from oriented seam crossing numbers. `TNLean.PEPS.TorusRegionWalkWinding`
identifies these numbers with endpoint deck-coordinate differences inside a
lifted region and derives path independence from geometric simple connectedness.
`TNLean.PEPS.TorusRegionLiftRealization` identifies the continuous covering lift
with the actual planar union of closed unit squares centered at the lifted sites.
`TNLean.PEPS.TorusRegionPeriodicLift` identifies the full plane preimage with
all period translates of this union and proves that distinct copies are disjoint,
including their cell boundaries. `TNLean.PEPS.TorusExteriorPathApproximation`
turns a supplied continuous exterior plane path into a genuine complementary
lattice walk with the exact crossing numbers of its lifted endpoints.
`TNLean.PEPS.TorusRegionExteriorCollar` proves that a collar of radius three
quarters around the planar lift avoids all foreign period copies, so its exterior
part projects outside the actual torus region.
`TNLean.PEPS.TorusIntegerStepWinding` supplies the common seam arithmetic for
integer unit steps. `TNLean.PEPS.TorusRegionBoundaryLift` constructs actual
crossing endpoints in that exterior collar and identifies their deck-coordinate
difference with the winding of the corresponding interior route.
`TNLean.PEPS.FiniteCellTopology` provides the shared finite-cell local path
connectedness argument. `TNLean.PEPS.IntegerCellNoHoles` rules out finite
components of missing integer cells from genuine simple connectedness of the
closed-cell union, and derives this obstruction for the actual planar torus lift.
Routing between the exterior boundary endpoints inside the collar remains open.
`TNLean.PEPS.RegularCycleControlledBoundary` constructs the unitary boundary
permutation controlled by cycle coordinates and computes its exact action on the
actual canonical block. Its relative-word consequence remains conditional on
the complement path identity. `TNLean.PEPS.TorusComplementCycleWords` derives
that identity for actual closures from fixed complementary loops with the required
geometric winding. `TNLean.PEPS.TorusComplementDisentangling` obtains one unitary
before choosing any commuting closure labels, with its exact action on every
actual canonical complementary block. Existence of the required exterior paths
remains part of the unrestricted disk entropy theorem.
`TNLean.PEPS.RegularControlledBoundaryFactor` contracts the two actual canonical
blocks and separates the fixed normalized maximally entangled boundary factor
and a fixed normalized region ancillary vector from every finite coherent sector
sum. `TNLean.PEPS.TorusControlledBoundaryFactor` derives its algebraic conditions
for native torus closures from geometric simple connectedness and fixed winding data.
`TNLean.PEPS.RegularCycleControlledSupport` proves that actual walk-word controls
commute with the product local invariant projector, preserve its range, and admit
unitary implementations on the original physical region.
`TNLean.PEPS.FixedBoundaryFactorDensity` and
`TNLean.PEPS.RegularReferenceBoundaryDensity` identify the fixed native reduced
matrix of the normalized boundary factor. `TNLean.PEPS.TorusControlledBoundaryDensity`
then derives the same reduced density for all nonzero coherent commuting-closure
sums under the supplied complementary winding data.
`TNLean.PEPS.RegularPhysicalCutTransfer` derives the actual physical cut and its
positive density normalization from the local site maps.
`TNLean.PEPS.RegularPhysicalDensity` preserves the rank and flat spectrum under
this supported physical embedding. `TNLean.PEPS.TorusPhysicalCutDensity` consequently
obtains one density on the original physical region, chosen before all closure
labels and coefficients, with rank equal to the expected boundary power.
`TNLean.Algebra.FlatDensityRenyiEntropy` computes all nonnegative finite Rényi
orders from the genuine spectral trace powers, including rank at order zero
and von Neumann entropy at order one. The unrestricted disk conclusion still
requires construction of the complementary walks from the geometric region.
The overlaps of actual torus contractions with noncontractible regular closure operators
are computed in `TNLean.PEPS.RegularTorusGram`; the class vectors are nonzero, orthogonal,
and linearly independent in `TNLean.PEPS.RegularTorusSectors`. The commuting subfamily
gives the regular isometric independence assertion underlying Theorem 5.9.
G-injective independence for regular virtual representations is proved in
`TNLean.PEPS.RegularGInjectiveTorus` by applying the local left inverse at every site.
The semi-regular case is proved in `TNLean.PEPS.GInjectiveTorusSectors`: the local inverse
and the explicit weighted trace contraction in `TNLean.PEPS.TorusProjectorExtraction`
send the actual vectors to independent simultaneous-conjugacy operator sums.
Parent-Hamiltonian identification remains a separate step.
The projected mixed Gram operators of actual complementary twists are computed in
`TNLean.PEPS.RegularTwistedRegionGram`; `TNLean.PEPS.RegularTwistedRegionEntropy` proves
a common reduced density for their nonzero superpositions.
`TNLean.PEPS.RegularTorusEntropy` derives the same density and entropy for actual torus
closure superpositions on strictly interior rectangles, from local isometry and coordinate
bounds alone. Arbitrary disk cuts meeting
the torus closure seams still require the source's disentangling argument; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

**Local fix (normalization):** as for `TNLean.PEPS.IsGIsometric`, `𝒫(A†) 𝒫(A)` is required to
be a positive multiple `c Π` of the projector onto the invariant subspace rather than `Π`
itself; the concatenation has factor `c_A c_B`. Documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## Main definitions

* `TNLean.PEPS.regularAdjoint`: the adjoint of an operator on `ℂ[G]`.
* `TNLean.PEPS.mpsAdjointSiteMap`: the map `𝒫(A†)`.
* `TNLean.PEPS.IsGIsometricMPS`: Definition 6.1 for an MPS tensor.

## Main results

* `TNLean.PEPS.concatLeftInverse_leftRegular`,
  `TNLean.PEPS.linkContractionLeftInverse_leftRegular`: the step `Δ = |G|⁻¹ 𝟙`.
* `TNLean.PEPS.concatLeftInverse_mpsAdjointSiteMap`: `(B^j)†(A^i)† = (A^i B^j)†`.
* `TNLean.PEPS.IsGIsometricMPS.concatTensor`: Lemma 6.2.
* `TNLean.PEPS.IsGIsometric.exists_unitary_comp_eq`,
  `TNLean.PEPS.IsGIsometric.exists_comp_eq_of_unitary`: Lemma 6.3.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap Representation TensorProduct
open scoped Matrix

namespace TNLean
namespace PEPS

attribute [local instance] Representation.invertibleFintypeCardComplex

section Regular

variable {G : Type*} [Group G] [Fintype G]

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1021–1022 and 1710. For the
left-regular representation `|G| Δ = 𝟙`. -/
theorem card_smul_deltaOperator_leftRegular :
    (Fintype.card G : ℂ) • deltaOperator (leftRegular ℂ G) = 1 := by
  rw [deltaOperator_leftRegular, Nat.card_eq_fintype_card, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Bridge: arXiv:1001.3807, proof of Lemma 6.2, `Papers/1001.3807/paper_v3.tex`
lines 1709–1713. For the left-regular representation on the bond, `Δ = |G|⁻¹ 𝟙` and the left
inverse `eq:noninj:linv` of the concatenation is `C⁻¹|ij⟩ = L_B|j⟩ L_A|i⟩`. -/
theorem concatLeftInverse_leftRegular (LA : (ι → ℂ) →ₗ[ℂ] Module.End ℂ (MonoidAlgebra ℂ G))
    (LB : (κ → ℂ) →ₗ[ℂ] Module.End ℂ (MonoidAlgebra ℂ G)) :
    concatLeftInverse (leftRegular ℂ G) LA LB =
      ∑ p : ι × κ, (LinearMap.proj p).smulRight (LB (Pi.single p.2 1) * LA (Pi.single p.1 1)) := by
  have h := card_smul_deltaOperator_leftRegular (G := G)
  refine LinearMap.ext fun x => ?_
  simp only [concatLeftInverse, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_comm, ← smul_mul_assoc (Fintype.card G : ℂ), ← mul_smul_comm (Fintype.card G : ℂ), h,
    mul_one]

end Regular

section Link

variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
variable {WA WB PA PB : Type*} [AddCommGroup WA] [Module ℂ WA] [AddCommGroup WB] [Module ℂ WB]
  [AddCommGroup PA] [Module ℂ PA] [AddCommGroup PB] [Module ℂ PB]

omit [FiniteDimensional ℂ E] in
/-- The contraction of the inner legs is linear in the operator it contracts through. -/
theorem innerContraction_smul (r : ℂ) (M : Module.End ℂ E) :
    innerContraction (WA := WA) (WB := WB) (r • M) = r • innerContraction M := by
  refine TensorProduct.ext_fourfold' fun x f e y => ?_
  simp [smul_smul]

/-- Bridge: arXiv:1001.3807, proof of Lemma 6.2, `Papers/1001.3807/paper_v3.tex`
lines 1709–1713, for the two-dimensional link contraction of Lemma 5.2 (figure
`figs3/ab-inv.pdf`). If the contracted link carries the left-regular representation, then
`|G| Δ = 𝟙` and the left inverse of the contracted tensor applies `L_A ⊗ L_B` and contracts the
two ends of the link directly. -/
theorem linkContractionLeftInverse_leftRegular
    (LA : PA →ₗ[ℂ] WA ⊗[ℂ] Module.Dual ℂ (MonoidAlgebra ℂ G))
    (LB : PB →ₗ[ℂ] MonoidAlgebra ℂ G ⊗[ℂ] WB) :
    linkContractionLeftInverse (leftRegular ℂ G) LA LB =
      innerContraction 1 ∘ₗ TensorProduct.map LA LB := by
  rw [linkContractionLeftInverse, ← LinearMap.smul_comp, ← innerContraction_smul,
    card_smul_deltaOperator_leftRegular]

end Link

section Adjoint

variable {G ι κ : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1668–1686 and 1699–1700.
The adjoint of an operator on `ℂ[G]` for the inner product in which the group elements `|h⟩`,
on which the left-regular representation acts by `L_g|h⟩ = |gh⟩`, are orthonormal: the operator
whose matrix in this basis is the conjugate transpose. -/
noncomputable def regularAdjoint (X : Module.End ℂ (MonoidAlgebra ℂ G)) :
    Module.End ℂ (MonoidAlgebra ℂ G) :=
  (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G ℂ)).symm
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G ℂ) X).conjTranspose

omit [Group G] in
/-- The adjoint reverses products, `(XY)† = Y† X†`. -/
theorem regularAdjoint_mul (X Y : Module.End ℂ (MonoidAlgebra ℂ G)) :
    regularAdjoint (X * Y) = regularAdjoint Y * regularAdjoint X := by
  simp only [regularAdjoint, map_mul, Matrix.conjTranspose_mul]

omit [Group G] in
theorem regularAdjoint_smul (r : ℂ) (X : Module.End ℂ (MonoidAlgebra ℂ G)) :
    regularAdjoint (r • X) = star r • regularAdjoint X := by
  simp only [regularAdjoint, map_smul, Matrix.conjTranspose_smul]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1668–1686. The map
`𝒫(A†) = ∑ \bar{A}^i_{αβ} |α,β⟩⟨i|` of the tensor `A†`, from the physical to the virtual system.
With the virtual vector `|α,β⟩` identified with the operator `|β⟩⟨α|`, as in
`TNLean.PEPS.mpsSiteMap`, it sends `|i⟩` to `(A^i)†`. -/
noncomputable def mpsAdjointSiteMap (A : ι → Module.End ℂ (MonoidAlgebra ℂ G)) :
    (ι → ℂ) →ₗ[ℂ] Module.End ℂ (MonoidAlgebra ℂ G) :=
  ∑ i, (LinearMap.proj i).smulRight (regularAdjoint (A i))

omit [Group G] in
@[simp]
theorem mpsAdjointSiteMap_single (A : ι → Module.End ℂ (MonoidAlgebra ℂ G)) (i : ι) :
    mpsAdjointSiteMap A (Pi.single i 1) = regularAdjoint (A i) := by
  simp [mpsAdjointSiteMap, Pi.single_apply]

/-- Source: arXiv:1001.3807, proof of Lemma 6.2, `Papers/1001.3807/paper_v3.tex`
lines 1709–1713. For the left-regular representation on the bond, the left inverse
`eq:noninj:linv` of `C^{ij} = A^i B^j` built from `𝒫(A†)` and `𝒫(B†)` is
`(B^j)†(A^i)† = (A^i B^j)†`, that is, `𝒫(C†)`. -/
theorem concatLeftInverse_mpsAdjointSiteMap (A : ι → Module.End ℂ (MonoidAlgebra ℂ G))
    (B : κ → Module.End ℂ (MonoidAlgebra ℂ G)) :
    concatLeftInverse (leftRegular ℂ G) (mpsAdjointSiteMap A) (mpsAdjointSiteMap B) =
      mpsAdjointSiteMap (concatTensor A B) := by
  simp only [concatLeftInverse_leftRegular, mpsAdjointSiteMap_single]
  rw [mpsAdjointSiteMap]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [concatTensor_apply, regularAdjoint_mul]

/-- Source: arXiv:1001.3807, Definition 6.1 (`def:iso:isopeps`), `Papers/1001.3807/paper_v3.tex`
lines 1692–1700, for an MPS tensor in the form `𝒫(A)⁻¹ = 𝒫(A†)`. The bond carries the
left-regular representation `L_g`, the tensor is invariant, `L_g A^i L_g⁻¹ = A^i`, and `𝒫(A†)` is a
left inverse of `𝒫(A)` onto the commutant up to a positive factor:
`𝒫(A†) 𝒫(A) = c σ`, with `σ` the twirl. The factor is the Local fix of
`TNLean.PEPS.IsGIsometric`. -/
structure IsGIsometricMPS (A : ι → Module.End ℂ (MonoidAlgebra ℂ G)) : Prop where
  /-- Invariance of the tensor under the left-regular representation on the bond. -/
  invariant : ∀ g i, leftRegular ℂ G g * A i * leftRegular ℂ G g⁻¹ = A i
  /-- `𝒫(A†)` is a left inverse of `𝒫(A)` up to a positive factor. -/
  exists_adjoint_comp : ∃ c : ℝ, 0 < c ∧
    mpsAdjointSiteMap A ∘ₗ mpsSiteMap A =
      (c : ℂ) • (linHom (leftRegular ℂ G) (leftRegular ℂ G)).averageMap

omit [DecidableEq ι] in
/-- Bridge: arXiv:1001.3807, Definition 6.1, `Papers/1001.3807/paper_v3.tex` lines 1692–1695.
A `G`-isometric MPS tensor is `G`-injective for the left-regular representation, with the left
inverse `c⁻¹ 𝒫(A†)`. -/
theorem IsGIsometricMPS.isGInjective {A : ι → Module.End ℂ (MonoidAlgebra ℂ G)}
    (hA : IsGIsometricMPS A) :
    IsGInjective (linHom (leftRegular ℂ G) (leftRegular ℂ G)) (mpsSiteMap A) := by
  obtain ⟨c, hc, h⟩ := hA.exists_adjoint_comp
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  refine (isGInjective_iff_exists_leftInverse _ _).2 ⟨?_, (c : ℂ)⁻¹ • mpsAdjointSiteMap A, ?_⟩
  · exact (mpsSiteMap_comp_linHom_eq_iff _ _).2 hA.invariant
  · rw [LinearMap.smul_comp, h, smul_smul, inv_mul_cancel₀ hc', one_smul]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Source: arXiv:1001.3807, Lemma 6.2 (stability of isometry under concatenation),
`Papers/1001.3807/paper_v3.tex` lines 1704–1716. If the MPS tensors `A` and `B` are
`G`-isometric, so is `C^{ij} = A^i B^j`: the left inverse `eq:noninj:linv` built from
`𝒫(A†)` and `𝒫(B†)` is `𝒫(C†)` (`concatLeftInverse_mpsAdjointSiteMap`). The factors multiply,
`𝒫(C†) 𝒫(C) = c_A c_B σ`. -/
theorem IsGIsometricMPS.concatTensor {A : ι → Module.End ℂ (MonoidAlgebra ℂ G)}
    {B : κ → Module.End ℂ (MonoidAlgebra ℂ G)} (hA : IsGIsometricMPS A)
    (hB : IsGIsometricMPS B) : IsGIsometricMPS (PEPS.concatTensor A B) := by
  classical
  obtain ⟨cA, hcA, hA'⟩ := hA.exists_adjoint_comp
  obtain ⟨cB, hcB, hB'⟩ := hB.exists_adjoint_comp
  have hcA' : (cA : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcA.ne'
  have hcB' : (cB : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcB.ne'
  refine ⟨concatTensor_conj_eq hA.invariant hB.invariant, cA * cB, mul_pos hcA hcB, ?_⟩
  have hLA : ((cA : ℂ)⁻¹ • mpsAdjointSiteMap A) ∘ₗ mpsSiteMap A =
      (linHom (leftRegular ℂ G) (leftRegular ℂ G)).averageMap := by
    rw [LinearMap.smul_comp, hA', smul_smul, inv_mul_cancel₀ hcA', one_smul]
  have hLB : ((cB : ℂ)⁻¹ • mpsAdjointSiteMap B) ∘ₗ mpsSiteMap B =
      (linHom (leftRegular ℂ G) (leftRegular ℂ G)).averageMap := by
    rw [LinearMap.smul_comp, hB', smul_smul, inv_mul_cancel₀ hcB', one_smul]
  have hC := concatLeftInverse_comp_mpsSiteMap (leftRegular ℂ G) hLA hLB
  have hsmul : concatLeftInverse (leftRegular ℂ G) ((cA : ℂ)⁻¹ • mpsAdjointSiteMap A)
      ((cB : ℂ)⁻¹ • mpsAdjointSiteMap B) =
      ((cA : ℂ) * cB)⁻¹ • mpsAdjointSiteMap (PEPS.concatTensor A B) := by
    simp only [concatLeftInverse_leftRegular, LinearMap.smul_apply, mpsAdjointSiteMap_single]
    rw [mpsAdjointSiteMap, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, concatTensor_apply,
      regularAdjoint_mul, smul_mul_smul_comm, smul_smul]
    rw [mul_inv, mul_comm (cA : ℂ)⁻¹, mul_comm]
  rw [hsmul, LinearMap.smul_comp] at hC
  rw [← hC, smul_smul, Complex.ofReal_mul, mul_inv_cancel₀ (mul_ne_zero hcA' hcB'), one_smul]

end Adjoint

section VirtualUnitary

/-- A square matrix preserving the dot products `star x ⬝ᵥ y` is unitary. -/
theorem mem_unitaryGroup_of_dotProduct {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : ∀ x y : n → ℂ, star (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = star x ⬝ᵥ y) :
    M ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec] at hij
  simpa [Matrix.star_eq_conjTranspose, Matrix.mulVec_single_one, Matrix.one_apply,
    Pi.single_apply, eq_comm] using hij

variable {G ι κ : Type*} [Group G] [Fintype G] [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] {ρ : Representation ℂ G (ι → ℂ)} {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Under the standing assumption that `𝒫(A)` is onto the physical system, a left inverse `L`
with `L 𝒫(A) = Π` lands in the invariant subspace and is a right inverse. -/
theorem IsGInjective.leftInverse_mem_invariants_of_surjective (hT : IsGInjective ρ T)
    (hsurj : Function.Surjective T) {L : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)}
    (hL : L ∘ₗ T = ρ.averageMap) (y : κ → ℂ) : L y ∈ ρ.invariants ∧ T (L y) = y := by
  obtain ⟨x, rfl⟩ := hsurj y
  have h : L (T x) = ρ.averageMap x := LinearMap.congr_fun hL x
  rw [h]
  exact ⟨ρ.averageMap_invariant x, apply_averageMap_of_forall_comp_eq hT.invariant x⟩

omit [Fintype G] in
/-- Source: arXiv:1001.3807, Lemma 6.3 (`lemma:iso:sym-virt-can-be-done-on-phys`), first
direction, `Papers/1001.3807/paper_v3.tex` lines 1739–1752, figures `figs4/V-comm-w-sym.pdf`,
`figs4/phys-op-from-V.pdf` and `figs4/phys-op-from-V-action.pdf`. For a `G`-isometric map
`T = 𝒫(A)` onto the physical system (Observation `obs:surjective`, lines 541–554), every unitary
`V` on the virtual level commuting with the symmetry (equation `eq:iso:V-comm-sym`) is
implemented by a unitary `U` on the physical system, `U 𝒫(A) = 𝒫(A) V`; here
`U = 𝒫(A) V 𝒫(A)⁻¹`. -/
theorem IsGIsometric.exists_unitary_comp_eq [Finite G] (hT : IsGIsometric ρ T)
    (hsurj : Function.Surjective T) {V : Matrix ι ι ℂ} (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hVρ : ∀ g, Matrix.toLin' V ∘ₗ ρ g = ρ g ∘ₗ Matrix.toLin' V) :
    ∃ U ∈ Matrix.unitaryGroup κ ℂ, Matrix.toLin' U ∘ₗ T = T ∘ₗ Matrix.toLin' V := by
  have := Fintype.ofFinite G
  obtain ⟨-, L, hL⟩ := (isGInjective_iff_exists_leftInverse ρ T).1 hT.toIsGInjective
  obtain ⟨c, hc, hcT⟩ := hT.exists_inner_eq
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  -- `V` preserves the invariant subspace.
  have hVinv : ∀ x ∈ ρ.invariants, V *ᵥ x ∈ ρ.invariants := fun x hx g => by
    have := LinearMap.congr_fun (hVρ g) x
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply] at this
    rw [← this, hx g]
  -- On the range, `U (T x) = T (V x)` for invariant `x`.
  have hU : ∀ x ∈ ρ.invariants, T (V *ᵥ L (T x)) = T (V *ᵥ x) := fun x hx => by
    rw [← LinearMap.comp_apply L T, hL, ρ.averageMap_id x hx]
  refine ⟨LinearMap.toMatrix' (T ∘ₗ Matrix.toLin' V ∘ₗ L), ?_, ?_⟩
  · refine mem_unitaryGroup_of_dotProduct fun y y' => ?_
    obtain ⟨hy, hTy⟩ := hT.toIsGInjective.leftInverse_mem_invariants_of_surjective hsurj hL y
    obtain ⟨hy', hTy'⟩ := hT.toIsGInjective.leftInverse_mem_invariants_of_surjective hsurj hL y'
    simp only [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', LinearMap.comp_apply]
    simp only [Matrix.toLin'_apply]
    rw [hcT _ (hVinv _ hy) _ (hVinv _ hy'), Matrix.star_mulVec_dotProduct_mulVec_of_mem_unitary hV,
      ← hcT _ hy _ hy', hTy, hTy']
  · refine LinearMap.ext fun x => ?_
    have hx : T x = T (ρ.averageMap x) := (apply_averageMap_of_forall_comp_eq hT.invariant x).symm
    simp only [Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [hx, hU _ (ρ.averageMap_invariant x), averageMap_apply_eq_sum, Matrix.mulVec_smul,
      Matrix.mulVec_sum, map_smul, map_sum]
    have hg : ∀ g, T (V *ᵥ ρ g x) = T (V *ᵥ x) := fun g => by
      have h1 := LinearMap.congr_fun (hVρ g) x
      simp only [LinearMap.comp_apply, Matrix.toLin'_apply] at h1
      rw [h1]
      exact LinearMap.congr_fun (hT.invariant g) _
    simp only [hg, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      invOf_mul_self, one_smul]

omit [DecidableEq ι] [Fintype G] in
/-- Source: arXiv:1001.3807, Lemma 6.3 (`lemma:iso:sym-virt-can-be-done-on-phys`), second
direction, `Papers/1001.3807/paper_v3.tex` lines 1752–1761, figure
`figs4/virt-op-from-phys.pdf`. For a `G`-isometric map `T = 𝒫(A)` onto the physical system
(Observation `obs:surjective`, lines 541–554, equation `eq:inj:rightinv-always`), every unitary
`U` on the physical system acts on the virtual level as `V = 𝒫(A)⁻¹ U 𝒫(A)`: `V` is invariant under
the symmetry on both sides, so it commutes with it, it is unitary on the invariant subspace,
and `𝒫(A) V = U 𝒫(A)`. -/
theorem IsGIsometric.exists_comp_eq_of_unitary [Finite G] (hT : IsGIsometric ρ T)
    (hsurj : Function.Surjective T) {U : Matrix κ κ ℂ} (hU : U ∈ Matrix.unitaryGroup κ ℂ) :
    ∃ V : (ι → ℂ) →ₗ[ℂ] (ι → ℂ), (∀ g, V ∘ₗ ρ g = V) ∧ (∀ g, ρ g ∘ₗ V = V) ∧
      (∀ x ∈ ρ.invariants, ∀ y ∈ ρ.invariants, star (V x) ⬝ᵥ V y = star x ⬝ᵥ y) ∧
      T ∘ₗ V = Matrix.toLin' U ∘ₗ T := by
  have := Fintype.ofFinite G
  obtain ⟨-, L, hL⟩ := (isGInjective_iff_exists_leftInverse ρ T).1 hT.toIsGInjective
  obtain ⟨c, hc, hcT⟩ := hT.exists_inner_eq
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hLy := hT.toIsGInjective.leftInverse_mem_invariants_of_surjective hsurj hL
  refine ⟨L ∘ₗ Matrix.toLin' U ∘ₗ T, fun g => ?_, fun g => ?_, fun x _ y _ => ?_, ?_⟩
  · rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hT.invariant g]
  · exact LinearMap.ext fun x => (hLy _).1 g
  · refine mul_left_cancel₀ hc' ?_
    simp only [LinearMap.comp_apply]
    rw [← hcT _ (hLy _).1 _ (hLy _).1, (hLy _).2, (hLy _).2, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.star_mulVec_dotProduct_mulVec_of_mem_unitary hU, hcT _ ‹_› _ ‹_›]
  · exact LinearMap.ext fun x => (hLy _).2

end VirtualUnitary

end PEPS
end TNLean
