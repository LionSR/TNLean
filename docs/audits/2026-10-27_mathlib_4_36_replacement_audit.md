# Mathlib 4.36 release-candidate replacement audit

Date: 2026-10-27. This is a bounded source audit for a coordinated draft,
not a claim of completed migration or target-version compilation.

## Comparison and scope

The comparison is from Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`
(`v4.35.0-rc3`) to `625d8914199bc567cca9b91f90e8e5afafa5ae51`
(`v4.36.0-rc1`). TNLean's starting source is
`56f7f58b5db4f14ba4f550cba22dd05065118df9`. The coordinated QICLean candidate is
`d5037d843552c55a5919bc21366b2eec2559fe0f`, proposed in
[QICLean #974](https://github.com/LionSR/QICLean/pull/974).

The QICLean audit at that candidate examined 529 non-merge commit titles.
This TNLean review checks its relevant findings against the exact old and
new source trees, the declarations below, and their TNLean consumers. It
compares the group-cohomology, bialgebra, Hopf-algebra and rigid-category
foundations and searches the target source for the mandatory structural
areas. It is not a comprehensive proof of absence of equivalent APIs.

## Included replacement: transpose surjectivity

`LinearIndependent.mulVec_surjective` is new in
`Mathlib/LinearAlgebra/Matrix/Rank.lean`. Over a semisimple ring it turns
linear independence of a matrix's rows into surjectivity of its action.
`Matrix.mulVec_injective_iff` in `Matrix/ToLin.lean` already identifies
injectivity with linear independence of columns.

In `TNLean/PEPS/ParentHamiltonian/InjectiveRegionSupport.lean`, the private
`range_mul_transpose_of_injective` declaration is removed entirely, with no
compatibility alias. Its sole caller,
`range_regionReducedDensity_eq_regionGroundSpace_of_injective_complement`,
now derives transpose surjectivity directly from its existing `hS`:

```lean
  have hsurj : Function.Surjective (Matrix.mulVecLin S.transpose) :=
    (show LinearIndependent ℂ S.transpose.row from
      Matrix.mulVec_injective_iff.mp hS).mulVec_surjective
```

The columns of `S` are the rows of its transpose. Thus the same injectivity
hypothesis gives the same surjectivity statement; composition with a
surjection leaves the range of `T` unchanged. The finite index assumptions
are unchanged and still allow empty index types. The caller replaces the
private-helper invocation with `Matrix.mulVecLin_mul`,
`LinearMap.range_comp`, `LinearMap.range_eq_top.mpr hsurj`, and
`Submodule.map_top`. Its final `Matrix.toLin'` / `toMatrix_openRegionMap`
rewrite is unchanged. Every public theorem header and definition is
unchanged. The new theorem is available through the existing import chain
`RegionReducedDensity` → `QICLean.Channel.MaximalOverlap` →
`QICLean.Channel.SchmidtRank` → `Mathlib.LinearAlgebra.Matrix.Rank`.
Source-level equivalence does not establish successful Lean elaboration.

## Required structural recheck

- **Multiplicative degree-three cohomology and universes.**
  `RepresentationTheory/Homological/GroupCohomology/Basic.lean` already
  supplies general-degree `groupCohomology` and cochains. `LowDegree.lean`
  already supplies `IsMulCocycle₁`, `IsMulCocycle₂`,
  `cocyclesOfIsMulCocycle₂`, and `IsMulCoboundary₂`. Its change in this range
  is a proof rewrite, not a new multiplicative degree-three interface.
  The shared `{k G : Type u}` restriction and the `{G M : Type}` binders
  on the multiplicative-to-cohomology constructors remain. No dedicated
  `IsMulCocycle₃` interface was identified. TNLean's
  `Algebra/ScalarThreeCocycleGroupCohomology.lean` still bridges its scalar
  three-cochains to the existing general-degree theory.
- **Projective representations, twisted group algebras and coefficients.**
  Existing `IsMulCocycle₂` is useful infrastructure, not a newly introduced
  bundled matrix projective representation or twisted group algebra.
  The target search identified no exact replacement for the constructions
  in `Algebra/ProjectiveRepresentation.lean`,
  `Algebra/TwistedRegularRepresentation.lean`, and
  `Algebra/TwistedRegularProjective.lean`. `Circle.toUnits` in
  `Analysis/Complex/Circle.lean` already provides the coefficient inclusion;
  it is not the finite-group cohomology equivalence proved in TNLean's
  `Algebra/CircleCohomology.lean`. No new matching equivalence was identified.
- **Weak/pre-bialgebras and C*-Hopf structures.**
  `Bialgebra` in `RingTheory/Bialgebra/Basic.lean` and `HopfAlgebra` in
  `RingTheory/HopfAlgebra/Basic.lean` are existing ordinary unital,
  counital foundations. New `HopfAlgebra.ofAntipodeOfAdjoin` in
  `RingTheory/HopfAlgebra/Convolution.lean` constructs an antipode from
  identities on algebra generators, assuming an ordinary bialgebra.
  It does not remove the unital/counital requirements for a coproduct whose
  unit image is a projector. No matching weak/pre-bialgebra or C*-Hopf
  replacement was identified; ordinary Hopf foundations must not be
  presented as resolving those distinct hypotheses.
- **Rigid, pivotal, spherical, fusion and module categories; dimensions.**
  `CategoryTheory/Monoidal/Rigid/Basic.lean` already supplies
  `ExactPairing`, `HasRightDual`, `HasLeftDual` and `RigidCategory`.
  Its changes here concern imports and proof syntax. Existing
  `MonoidalLeftAction` and `MonoidalRightAction` in
  `CategoryTheory/Monoidal/Action/Basic.lean` provide categorical actions;
  `monModuleEquivalenceAlgebra` in `Monoidal/Internal/Module.lean` compares
  monoid objects in modules with algebras. These are foundations, not an
  identified replacement for the full pivotal/spherical/fusion-category
  or Frobenius–Perron-dimension requirements. No such new matching
  implementation was identified in the bounded search.
- **Fusion/based rings and NIM-representations.**
  No matching new based-ring, fusion-ring or NIM-representation interface
  was identified. TNLean's `MPS/Symmetry/MPOSymmetry/FusionRing.lean` and
  `NIMRep.lean` remain local layers; this draft does not claim their
  migration is complete or infer completeness from keyword absence.
- **Star-closed matrix-algebra semisimplicity.**
  `Analysis/InnerProductSpace/Semisimple.lean` is unchanged in the range.
  Its `LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule` and
  `isFinitelySemisimple` concern an individual symmetric operator.
  They are not the simultaneous invariant-complement statement for a
  star-subalgebra in TNLean's `Algebra/StarClosedSemisimple.lean`, notably
  `StarSubalgebra.isSemisimpleModule`. No exact replacement was identified.

## Deferred migrations and draft gates

The structural layers above remain under
[tracker #8315](https://github.com/LionSR/TNLean/issues/8315); their existing
migration work is outside this draft. In particular, the reported closure
of [#8317](https://github.com/LionSR/TNLean/issues/8317) does not establish
completion: this exact TNLean base still defines the raw `ScalarCocycle`
abbreviation and local `ProjectiveRepresentation` in
`Algebra/ProjectiveRepresentation.lean`, and `ScalarCocycle.CohomologousTo`
in `Algebra/CocycleCohomology.lean`. The existing use of Mathlib's
`IsMulCocycle₂` is evidence of partial adoption, not deletion of all local
layers. These declarations and other owners' migration work are preserved.
The remaining cohomology-relation work is tracked by
[#10238](https://github.com/LionSR/TNLean/pull/10238); the raw-cochain/helper
namespace work and other #8315 layers still require their own resolution.

`docs/project_conventions.md` ordinarily requires deferred migrations to
land before another bump PR opens. The user's explicit instruction permits
preparing this coordinated draft while that gate remains pending; the
protocol itself is unchanged. Before readiness or merge, remaining covered
local layers must be resolved and the QICLean upgrade runbook's validation
and release requirements met. The draft's exact QIC commit must become the
validated immutable semantic-version release tag, with its matching
release archive. No tag is invented here.

Root, documentation and QICLean toolchains and Mathlib revisions must agree.
Target-version production builds, strict checks, regressions and axiom
checks, executable lint, compiled blueprint declaration checks and full
web/PDF validation remain acceptance requirements. This mathematical source
audit does not certify those checks or migration completion.
