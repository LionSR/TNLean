# Generic many-body notions defined in TNLean (audit, 2026-11-20)

Scope: every TNLean-local definition, structure, predicate or hypothesis bundle that encodes a
many-body notion stated without a tensor network, and that therefore belongs in, or already
exists in, QICLean `ManyBody/` (Sites, Dynamics, Hamiltonian) under the rules of
`docs/many_body_circuit_architecture.md` ("Where a declaration goes", "Repository boundary",
"No dual systems").

Revisions read:

* TNLean `origin/main` at `0c76bc5a1` (#10934).
* QICLean pinned by TNLean: `817108b` (`lake-manifest.json`). QICLean `main`: `f0c1bb9`,
  26 commits ahead of the pin. It adds `ManyBody/Hamiltonian/{HardTruncation,
  DisjointRegionalGround, ProductGround, KroneckerSum}`, `ManyBody/Dynamics/
  BoundedDegreeImaginaryTime`, `ManyBody/Sites/{Lattice/Ring, SupportedUnitary}` and
  `Entropy/{RegionEntropyInequalities, ZeroEntropy, SumSitesProduct, TypicalMarginalMass,
  MutualInformationPerturbation}`.
* Open PR #10936 (`claude/ff2d-model`), which introduces the frustration-free plane model.

Method. Counts are `grep -rl` over `TNLean/**/*.lean`, and they include the defining file. A
name that QICLean also uses (`edgeBoundary`, `StateSpace`) is counted by its usual spelling, so
the count is an upper bound for the TNLean copy. A pattern count, given for an inline
hypothesis bundle, counts the files whose text matches the regular expression quoted in the
row. "QICLean (pin)" means the counterpart is already in the pinned revision; "QICLean (main)"
means it is on QICLean `main` and not yet pinned.

Recommendation classes:

* **(a)** delete, and use the QICLean notion;
* **(b)** move up to QICLean, generalized to an arbitrary `Interaction`, support family or
  graph;
* **(c)** keep as a genuine specialization, restated through the QICLean notion;
* **(d)** keep, because it is specific to tensor networks.

---

## 1. Frustration-freeness

QICLean has no frustration-free notion. The words appear only in docstrings of
`Channel/ProductOverlapBootstrap`, `Analysis/ProjectionResidual` and
`Analysis/ComplementProdKernel`. TNLean encodes the notion in five representations: a
predicate on MPS parent models, two structures for commuting two-term parents, a root
namespace `FrustrationFree` for the martingale method, abstract families of projections on an
inner product space, and at least four inline hypothesis bundles on matrices. PR #10936 adds a
sixth, a structure on `PlaneInteraction`.

### 1.1 Definitions and structures

| # | Lean name, `file:line` | Meaning | QICLean counterpart | Files | Rec. |
|---|---|---|---|---|---|
| FF1 | `MPSTensor.IsFrustrationFree`, `MPS/ParentHamiltonian/Defs.lean:233` | `∀ i : Fin N, localTerm A L N i ψ = 0`: every translate of the parent interaction annihilates `ψ` | none | 5 | (c): `ψ ∈ Φ.zeroSpace` for the parent interaction `Φ` of `A` on the ring (§1.3). Dependent theorems are `parentHamiltonian_frustrationFree` (`Basic.lean:257`), `isFrustrationFree_of_mem_chainGroundSpace` (`ChainGroundSpace.lean:120`), `HasNNCPHGroundSpace.isFrustrationFree` (`Commuting.lean:203`) and `bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_frustrationFree` (`Commuting.lean:317`) |
| FF2 | `MPSTensor.IsNNCPHGroundState`, `MPS/ParentHamiltonian/Commuting.lean:108` | `IsNNCPH A N ∧ IsFrustrationFree A 2 N (mpv A)` | none | 2 | (d): the commuting-parent clause mentions the tensor. Its frustration-free conjunct is restated by FF1 |
| FF3 | `Decorrelation.HasCommutingParentHam`, `MPS/ParentHamiltonian/Decorrelation.lean:150`, with `Decorrelation.IsDecorrelated`, `:119` | two commuting idempotents with `P_AX ∘ P_XB = P_K`, on an abstract module. Its own scope note says `P_AX = P_XB = P_K` always works (`ofIdem`, `:171`), so the structure carries no locality | `TripartiteDecorrelation.IsDecorrelated`, `QICLean/Channel/TripartiteDecorrelation.lean:311` (pin) | 3 | (a): a second, vacuous system beside FF4. Delete it; the extended lemmas in `MPS/RFP/Decorrelation.lean` go with it or are restated on FF4 |
| FF4 | `TripartiteDecorrelation.CommutingParentHamiltonian`, `MPS/ParentHamiltonian/TripartiteDecorrelation.lean:104`; `HasCommutingParentHamiltonian` `:147`; `HasGroundSpaceIntersection` `:38` | CPSV16 Def. D.2: local Hermitian projectors on `AX` and `XB` whose lifts commute and whose ranges intersect in `ran P`. This is the commuting frustration-free two-term Hamiltonian on `A ⊔ X ⊔ B` | `IsDecorrelated`, `liftAX`, `liftXB` (QICLean pin) | 1 | (b): move next to `IsDecorrelated`. State it as a two-term interaction on the sites `A ⊔ X ⊔ B` that is frustration-free with commuting terms, and drop `liftAX`/`liftXB` in favour of `place` |
| FF5 | `LinearMap.frustration_free_ham_eq`, `MPS/RFP/Decorrelation.lean:60` | `(1−P)+(1−Q)−(1−P)(1−Q) = 1−PQ` | none | 1 | (b): a pure ring identity. Move it to QICLean `Algebra`, or inline it (`abel`) |
| FF6 | root namespace `FrustrationFree` (9 defining files in `MPS/ParentHamiltonian/Martingale/`): `NestedGroundProjections` (`DifferenceProjections.lean:42`), `martingaleDifference`, `UnrestrictedNachtergaeleEstimate` (`NachtergaeleLowerEndpoint.lean:125`), `norm_gap_of_two_ground_projection_bounds` (`TwoGroundProjectionGap`), `spectralGap_of_martingale_of_finiteDimensional` (`AbstractCriterion.lean:53`), `energy_lower_bound_of_nachtergaele_c1_c3_*` | Nachtergaele's martingale method for the gap of a frustration-free Hamiltonian. It is stated for nested ground projections `G_n` on an inner product space, with the hypothesis bundle `ker (H M) = range (G M)` and `ker (localHamiltonian n) = range (Q n)` | none | 11 use `NestedGroundProjections`; 21 use the namespace | (b): `ManyBody/Hamiltonian/Martingale`. The abstract part moves unchanged. Its many-body corollary is stated for an `Interaction` with `IsFrustrationFree` and the nested regional zero spaces |
| FF7a | `TNLean.MPS.AreaLaw.ALVV.complementProd_apply_eq_self_iff`, `MPS/AreaLaw/ALVV/FrustrationFree.lean:31` | a product of complementary projections fixes `x` iff every factor annihilates `x` | `complementProd_apply_eq_self_iff`, `QICLean/Analysis/ComplementProdKernel.lean:29` (pin), which is stronger because it drops the commutation hypothesis | 2 | (a) |
| FF7b | `ALVV.restrictedTerm` `:48`, `regionalProjection`, `regionalReplacement`, `regionalReplacement_frustrationFree` `:189`, `sum_apply_eq_zero_iff` `:119` | ALVV Def. 5.10 and Thm 5.14(1) for abstract projection families `h : ℕ → E →L[𝕜] E`, with the inline bundle `(hh : ∀ i, IsStarProjection (h i)) (hx : ∀ i < m, h i x = 0)` | `Analysis/DetectabilityLemma`, `Analysis/ComplementProdKernel` (pin) | 5 | (b): move to QICLean `Analysis` beside `ComplementProdKernel` |
| FF8 | `ALVV.chainOperator`, `chainTerm`, `chainReplacement_frustrationFree` (`ALVV/FrustrationFreeChain.lean:390`), `frustrationFree_regionalReplacement_chain` (`:429`) | the same on a chain: projections `h : Fin m → Matrix`, supported on bonds via `Entropy.IsSupportedOn (h i) (interval L i (i+2))`, with `chainOperator h Ω = 0` | none | 3 | (c): restate over the bond interaction of H1 with `IsFrustrationFree` |
| FF9 | `physicalFrustrationFreeTruncation`, `MPS/AreaLaw/PhysicalFrustrationFreeTruncation.lean:33` | ALVV `def:FF-tH`: replaces the two parity layers in a region by complementary products | none | 2 | (c): define it on the bond interaction, with the hypotheses `hp` and `hs` carried by the interaction |
| FF10 | `IsFrustrationFreeGapped`, `PEPS/AreaLaw/FrustrationFree/Model.lean:59` (PR #10936, not on `main`) | `eq:model` of the frustration-free note on `PlaneInteraction Λ q R`, as the fields `posSemidef`, `le_bound` (`h_X ≤ J`), `mulVec_eq_zero` (`h_X Ω = 0`), `norm_eq_one` and `gap` (`Δ(1−|Ω⟩⟨Ω|) ≤ H`) | none | 0 on `main` | (b): the frustration-free content is `ManyBody.Interaction.IsFrustrationFree` plus `Ω ∈ Φ.zeroSpace`. Delete the structure before merge. Keep `le_bound` and `norm_eq_one` as hypotheses, and replace `gap` by `IsGapped`/`groundSpace` through the pinned `isGapped_and_groundSpace_eq_span_iff`. Its theorems `isGapped`, `groundSpace_eq`, `isHermitian` and `hamiltonian_mulVec_eq_zero` hold for every interaction and belong in QICLean |
| FF11 | `TNLean.MPS.parentGroundStateFace`, `MPS/ParentHamiltonian/QuasiLocalParentGroundStateFace.lean:35` | the states of the quasi-local algebra with zero expectation on every translate of `h`: the infinite-volume frustration-free ground states | none | 27 | (b), late: it mentions no tensor. It moves when the quasi-local algebra (`QCA/SpinChain`) has a QICLean home; until then it stays next to its consumer |

### 1.2 Hypothesis bundles spelled out inline

| # | Where (first `file:line`) | Bundle | QICLean counterpart | Files | Rec. |
|---|---|---|---|---|---|
| FF12 | AKLV: `exists_frustrationFree_chain_chebyshev_filter` (`MPS/AreaLaw/AKLV/ChebyshevProjector.lean:240`), `frustrationFree_twoSidedEnergyTruncation_ground_gap` (`AKLV/FrustrationFreeClipping.lean:40`), `exists_aklv_frustrationFree_physical_entropy_bound` (`AKLV/FrustrationFreeEntropy.lean:51`), `…_mps_approximation` (`AKLV/FrustrationFreeMPSApproximation.lean:55,174,279`), `aklv_frustrationFree_dimension_and_gap_bounds` (`AKLV/FrustrationFreeGapBounds.lean:34`) | `(h : Fin (L-1) → Matrix …)`, `(hs : ∀ i, Entropy.IsSupportedOn (h i) (interval L i (i+2)))`, `(h0 : ∀ i, 0 ≤ h i)`, `(h1 : ∀ i, h i ≤ 1)`, `(hΩ : ‖Ω‖ = 1)`, `(hzero : (∑ i, h i) *ᵥ Ω = 0)`, `(hgap : (∑ h − g(1−|Ω⟩⟨Ω|)).PosSemidef)` | none for frustration-freeness; `isGapped_and_groundSpace_eq_span_iff` for the gap | 15 name `frustrationFree`; 6 state `(∑ h) Ω = 0` | (c): `Φ` a bond interaction with `Φ.IsFrustrationFree`, `Ω ∈ Φ.zeroSpace`, `∀ i, Φ.term i ≤ 1`, `IsGapped Φ.hamiltonian 0 g` and `groundSpace … = span {Ω}`. The sum is `Φ.hamiltonian`, not `∑ i, h i` |
| FF13 | PEPS amplification: `AmplificationProof.lean:404` (`hk : ∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ Ω = 0`), `Amplification/ConstraintWordLists.lean:80,93`, `ChannelGroundVectors.lean:67,89`, `LocalConstraintProducts.lean:98`, `LatticeChannelSpatialOmission.lean:171,235` | positive contractions `k i` annihilating `Ω`. These are the filtered constraints of the general area law, which are frustration-free for `Ω` by construction | none | 9 (pattern `k i *ᵥ … Ω = 0`) | (c): the constraint family becomes an `Interaction` (its supports are the designated supports), with `Ω ∈ zeroSpace` and `0 ≤ k ≤ 1`. The lemmas of `ConstraintWordLists` on bare `Matrix n n` are generic (b) |
| FF14 | `PEPS/AreaLaw/FrustrationFree/SweepContraction.lean:80,102` (`norm_sq_complementProd_le_of_gap`, `norm_pow_complementProd_le_of_gap`, on `main` since #10935); `RangeProjection.lean:43` (`Matrix.PosSemidef.le_smul_supportProj`), `:74` (`supportProj_mem_supportedOperators`) | `(hh : ∀ k, IsStarProjection (h k)) (hΩ : ∀ k, h k Ω = 0) (hgap : ∀ v ⟂ Ω, γ‖v‖² ≤ re⟪v, ∑ h v⟫)` on an abstract inner product space; a matrix order lemma; a support lemma | `Analysis/DetectabilityLemma` (`re_inner_sum_complementProd_le`), `Analysis/SupportProjectionOrder`, `ManyBody.cfc_mem_supportedOperators` (pin) | 7 use `complementProd` | (b): all three mention no plane. Move them into those QICLean modules |
| FF15 | PEPS parent Hamiltonians: `regionParentHamiltonian` (`PEPS/ParentHamiltonian/RegionParentHamiltonian.lean:196`, `∑ i, place (R i) (h i)`), `regionParentHamiltonian_posSemidef`, `regionParentHamiltonian_mulVec_eq_zero_iff` ("frustration-free ground space", lines 2008–2011 of arXiv:2011.12127), `place_stateCoeff_eq_zero` (`:165`) | positive placed terms; the kernel of their sum is the common kernel | none | 39 (`regionParentHamiltonian`); 6 (`…_mulVec_eq_zero_iff`) | (c): the Hamiltonian is `Interaction.hamiltonian` of the interaction with terms `place (R i) (h i)`. The kernel lemma is the generic `zeroSpace_eq_groundSpace` of §1.3 (b) |
| FF16 | MPS parent Hamiltonians: `localTerm`/`parentHamiltonian` (`MPS/ParentHamiltonian/Defs.lean:201,213`, linear maps on `NSiteSpace`), and the Euclidean copies `localTermES`/`parentHamiltonianES` (`Martingale/Transport.lean:109,167`), `openParentHamiltonianES` (`Martingale/OpenHamiltonian.lean:46`), `periodicInteractionHamiltonianES`, `openInteractionHamiltonianES`, `obcParentHamiltonian` (`VaryingOBCProjectorKernel.lean:138`) | sums of placed translates of one positive local term. The frustration-free hypotheses (`IsSymmetricProjection`, `ker = range`) are repeated on each copy | none | 30 / 67 / 39 / 79 | (c): one ring or open-chain `Interaction` whose term is the tensor's parent projector. The `ES` copies are a second representation of the same operator, a dual system inside TNLean |

### 1.3 Proposed QICLean statement

In `QICLean/ManyBody/Hamiltonian/FrustrationFree.lean`, importing `GroundSpace` and
`Dynamics/Interaction`:

```lean
namespace ManyBody.Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} {S : ι → Finset V}

/-- The zero space of an interaction: the vectors annihilated by every term. -/
noncomputable def zeroSpace (Φ : Interaction X S) :
    Submodule ℂ (EuclideanSpace ℂ (Config X)) :=
  ⨅ i, LinearMap.ker (Matrix.toEuclideanLin (Φ.term i))

/-- `Φ` is frustration-free: its terms are positive semidefinite and have a common nonzero
zero vector, so a ground state of the sum is a ground state of every term. -/
def IsFrustrationFree (Φ : Interaction X S) : Prop :=
  (∀ i, (Φ.term i).PosSemidef) ∧ Φ.zeroSpace ≠ ⊥

theorem mem_zeroSpace_iff {Φ : Interaction X S} {ψ} :
    ψ ∈ Φ.zeroSpace ↔ ∀ i, Φ.term i *ᵥ WithLp.ofLp ψ = 0

/-- For positive terms the zero space is the ground space of the sum at energy `0`. -/
theorem zeroSpace_eq_groundSpace [Fintype ι] {Φ : Interaction X S}
    (hΦ : ∀ i, (Φ.term i).PosSemidef) : Φ.zeroSpace = groundSpace Φ.hamiltonian 0

theorem IsFrustrationFree.groundSpace_ne_bot [Fintype ι] {Φ : Interaction X S}
    (h : Φ.IsFrustrationFree) : groundSpace Φ.hamiltonian 0 ≠ ⊥

/-- Frustration-freeness in the unnormalized sense: shifting each term by its least
eigenvalue gives a frustration-free interaction iff `λ_min (∑ h_i) = ∑ λ_min (h_i)`. -/
theorem isFrustrationFree_shift_iff …

/-- The gap of a positive sum above its zero space, in quadratic-form and norm form. -/
theorem isGapped_zero_iff_inner [Fintype ι] {Φ : Interaction X S}
    (hΦ : ∀ i, (Φ.term i).PosSemidef) (hne : Φ.zeroSpace ≠ ⊥) {Δ : ℝ} :
    IsGapped Φ.hamiltonian 0 Δ ↔
      ∀ v ∈ Φ.zeroSpaceᗮ, Δ * ‖v‖ ^ 2 ≤ RCLike.re ⟪v, toEuclideanLin Φ.hamiltonian v⟫_ℂ

end ManyBody.Interaction
```

Positivity is part of the definition, not a hypothesis, because "common zero vector" means
"common ground state" only when every term has least eigenvalue `0`. Shifting each term by its
least eigenvalue is the convention, recorded once by `isFrustrationFree_shift_iff`. Norm
bounds, range and Hermiticity stay hypotheses, as for every `Interaction` statement.

How each item above specializes:

| Item | Specialization |
|---|---|
| FF1, FF2, FF16 | `Φ := parentInteraction A L N`, an `Interaction (Qudits (Fin N) d) ringWindows`. `IsFrustrationFree A L N ψ` becomes `ψ ∈ Φ.zeroSpace`, and `parentHamiltonian_frustrationFree` becomes `mpv A ∈ Φ.zeroSpace` |
| FF8, FF9, FF12 | `Φ : BondInteraction L q` (H1) with `Φ.IsFrustrationFree`, `Ω ∈ Φ.zeroSpace` and `∀ i, Φ.term i ≤ 1` |
| FF10 | `Φ : PlaneInteraction Λ q R`, `Φ.IsFrustrationFree`, `Ω ∈ Φ.zeroSpace`, `∀ X, Φ.term X ≤ J • 1`, `‖Ω‖ = 1`, `IsGapped Φ.hamiltonian 0 Δ`, `groundSpace Φ.hamiltonian 0 = span {Ω}` |
| FF13 | the constraint interaction `κ` with supports the designated supports; `Ω ∈ κ.zeroSpace` |
| FF4 | the two-term interaction on `A ⊔ X ⊔ B` with commuting projector terms; `ran P = Φ.zeroSpace` |
| FF15 | `Φ := ofPlace R h`. `regionParentHamiltonian_mulVec_eq_zero_iff` is `zeroSpace_eq_groundSpace` |
| FF6, FF7b, FF14 | abstract lemmas on operator families in QICLean `Analysis`. Their many-body corollaries take `Φ.IsFrustrationFree` |

---

## 2. Gaps, ground spaces and ground projections

QICLean has one gap predicate, `ManyBody.IsGapped H E₀ Δ`, one ground space,
`ManyBody.groundSpace H E₀`, and the operator form `isGapped_and_groundSpace_eq_span_iff`
(`QICLean/ManyBody/Hamiltonian/GroundSpace.lean:105,122,219`, all at the pin). TNLean also uses
four other encodings of a gap.

| # | Lean name or bundle, `file:line` | Meaning | QICLean counterpart | Files | Rec. |
|---|---|---|---|---|---|
| G1 | projector-form gap `(H − g(1−\|Ω⟩⟨Ω\|)).PosSemidef` or `Δ • (1 − vecMulVec Ω Ω*) ≤ H`; first at `MPS/AreaLaw/AKLV/ChebyshevProjector.lean:240` | gapped unique ground vector at energy `0` | `isGapped_and_groundSpace_eq_span_iff` (pin) | 51 (pattern `1 - (Matrix.)?vecMulVec`), 23 of them in AKLV | (a): state `IsGapped` and `groundSpace = span {Ω}`, and derive the operator form at the use site |
| G2 | quadratic-form gap on `ker H ⊥`, `γ‖y‖² ≤ re⟪y, H y⟫`; `ALVV/FrustrationFreeChain.lean:380`, `SweepContraction.lean:80`, `Algebra/CommonKernelGapInterpolation.lean:24` | gap above the kernel of a positive operator | none (`isGapped_zero_iff_inner` of §1.3 is missing) | 8 | (b): add the characterization to QICLean, then restate |
| G3 | norm-form gap on `ker H ⊥`, `γ‖v‖ ≤ ‖H v‖`; first at `Martingale/AbstractCriterion.lean:53` | the same, in norm form, for linear maps on `EuclideanSpace` | none | about 106 (pattern `[γδΔ] * ‖v‖ ≤ ‖…‖`), about 79 of them in `MPS/ParentHamiltonian`, 21 in `MPS/Symmetry` and 5 in `Algebra` | (b): add a characterization theorem `IsGapped H 0 γ ↔ …` for positive `H` with nonzero kernel. The parent-Hamiltonian gap theorems then conclude `IsGapped` |
| G4 | `SymmetricGappedInteractionPath`, `MPS/Symmetry/GappedInteractionPath.lean:45` (field `gap`, spectrum form `∃ E ∈ spectrum, ∀ z, E ≤ z.re ∧ (z.re = E ∨ E + δ ≤ z.re)`) | Chen–Gu–Wen symmetric gapped path of two-site interactions, uniform in the chain length | `IsGapped` (pin) | 36 | (b): a gapped path of interactions with an on-site symmetry is a generic many-body notion. Move it with the gap field as `∃ E, IsGapped (Φ γ N).hamiltonian E δ`. The tensor path constructions (`canonicalInjectiveGappedPath`, …) stay in TNLean |
| G5 | `MPSTensor.HasUniqueGroundState`, `MPS/ParentHamiltonian/UniqueGroundState.lean:56` | `finrank S = 1` for any submodule | `groundSpace H E₀ = span {Ω}` convention (pin) | 7 | (a) |
| G6 | `IsSquareGroundState`, `PEPS/Approximation/Basic.lean:61`; `IsRangeSquareGroundState`, `PEPS/Approximation/RangeSquareGroundState.lean:52` | the class of unit unique gapped ground vectors of some square-lattice interaction with term norms at most `J` (polynomial-PEPS `eq:model`) | stated on `SquareInteraction`/`PlaneInteraction` with `IsGapped` | 25 | (c): already restated on QICLean. Keep these as the source's model class, but do not copy them as a generic predicate (the design document forbids a gapped-ground-state bundle) |
| G7 | `Algebra/CommonKernelGapInterpolation.lean:24` (`gap_interpolation_of_le`), `Algebra/CommonKernelSpectralGap.lean:37–138`, `Algebra/KernelGapPerturbation.lean`, `Algebra/CompactGapBounds.lean` (`IsCompact.exists_uniform_norm_lower_bound_on_tail`), `Algebra/CommutingProjectionProduct.lean` | matrix gap stability along interpolations and perturbations | none | 3 / 5 / 5 / 6 / 3 importers | (b): step 3A, into `ManyBody/Hamiltonian`, stated with `IsGapped` |
| G8 | `QuantumCircuit.exists_common_ground_of_disjoint`, `exists_supported_ground_cutoff` (`Circuit/SupportedGroundSpace.lean:34,85`), `exists_normalized_common_ground_of_disjoint` (`Circuit/SupportedNormalizedGroundSpace.lean:32`) | common ground vectors of Hamiltonians on disjoint regions (a Hamiltonian-layer statement in a circuit directory) | `ManyBody/Hamiltonian/DisjointRegionalGround` (main) | 2 / 1 / 2 | (b): into `DisjointRegionalGround` |
| G9 | `TNLean/Lattice/{HardTruncation, DisjointRegionalGround, ProductGroundState, BoundedDegreeImaginaryTime}.lean` | hard truncation of a region, regional clipping structure, product ground states of Kronecker sums, imaginary-time conjugation bounds | `ManyBody/Hamiltonian/{HardTruncation, DisjointRegionalGround, ProductGround, KroneckerSum}`, `ManyBody/Dynamics/BoundedDegreeImaginaryTime` (main) | 3 / 8 / 2 / 3 importers | (a) at the next pin move |
| G10 | `TNLean.MPS.AreaLaw.Hastings.groundCentered`, `MPS/AreaLaw/Hastings/ThreeWaySplitting.lean:84` | `M − re⟨Ψ, MΨ⟩ · 1` | `ManyBody.centeredObservable`, `Hamiltonian/NegativeFrequency.lean:68` (pin), equal for unit `Ψ` and Hermitian `M` | 2 | (a) |
| G11 | `Hastings.spectralCutoff`, `MPS/AreaLaw/Hastings/SpectralCutoff.lean:67` | spectral projection of `M` onto `\|t\| ≤ θ` by `cfc` | `spectralSpanLE` (`Analysis/LowEnergyPerturbation.lean:81`), in subspace form | 4 | (b): a matrix spectral projection, for `Analysis` |
| G12 | `ManyBody.PlaneInteraction.positiveTerm`, `PEPS/AreaLaw/Scan/ActualEnergyTerms.lean:172` | the positive constraint of a filtered term, built from QICLean `centeredFilter` and `positiveConstraint` | `Analysis/SpectralFilter/PositiveReplacement` (pin) | 2 | (b): `Interaction.positiveTerm` for every interaction. The plane only fixes `ι` |
| G13 | tensor ground spaces and projections: `MPSTensor.groundSpace A L` (`ParentHamiltonian/GroundSpace.lean:56`), `chainGroundSpace`, `groundSpaceProjectionMatrix`, `openChainLeftGroundProjectionES`, `InLeftGround`/`InRightGround`/`InTailGround`, `IsParentInteraction` (`PhysicalDeformation.lean:171`), `IsRegionParentInteraction` (`RegionParentHamiltonian.lean:56`), `IsPositiveGapPhysicalCID`, `IsPositiveGapBNTZCL` (`RFP/ZeroCorrelationLength.lean:100,223`), `IsSameExactMPSGappedPhase` | spaces spanned by tensor contractions, and predicates on a tensor | none | 19–79 | (d). Once FF16 holds, their Hamiltonian-side statements should conclude `groundSpace`/`IsGapped` of the parent `Interaction` |

---

## 3. Local and finite-range Hamiltonians, interaction structures

QICLean has `ManyBody.Interaction X S` and its `hamiltonian` (`Dynamics/Interaction.lean:51,64`),
and the model abbreviations `ChainInteraction`, `DomainInteraction`, `PlaneInteraction`,
`RectangleInteraction` and `SquareInteraction` (`Hamiltonian/Models.lean:52–75`), all at the
pin. Step 3H.2 removed TNLean's five Hamiltonian structures. What remains is a sixth spelling,
the bare bond family, and a layer of generic operations defined on the QICLean types inside
TNLean.

| # | Lean name or bundle, `file:line` | Meaning | QICLean counterpart | Files | Rec. |
|---|---|---|---|---|---|
| H1 | bond-family bundle `(h : Fin (L - 1) → Matrix (Fin L → Fin q) …)` with `(hs : ∀ i, Entropy.IsSupportedOn (h i) (interval L i (i + 2)))` and the bare sum `∑ i, h i`; e.g. `AKLV/ChebyshevProjector.lean:240`, `PhysicalFrustrationFreeTruncation.lean:33` | a nearest-neighbour chain Hamiltonian | `ChainInteraction L q 1`, which is indexed by all range-one supports, singletons included | 214 (pattern `interval L i (i + 2)`): 106 `MPS/AreaLaw`, 47 ALVV, 30 AKLV, 12 ViableSet, 10 Algorithm, 9 Huang. 149 files also carry `h i ≤ 1` | (b): add `abbrev BondInteraction L q := Interaction (fun _ ↦ Fin q) (fun i : Fin (L-1) ↦ interval L i (i+2))` to `Models.lean`, then sweep. It is the largest remaining second spelling of a Hamiltonian, and it also keeps the old `Entropy.IsSupportedOn` alive |
| H2 | `ChainInteraction.ofBonds`, `MPS/AreaLaw/ViableSet/PowerProjector.lean:118`; `ChainInteraction.ofNearestNeighborPositive`, `MPS/AreaLaw/Huang/PositiveChainHamiltonian.lean:74` | two constructions of the same range-one interaction from a bond family (one by `∑ if`, one by `Function.extend`) | none | 16 | (b): one QICLean map `BondInteraction → ChainInteraction L q 1`. Delete the other (dual system) |
| H3 | generic operations on QICLean interactions, defined in TNLean: `ChainInteraction.termSum`, `leftPart`, `bufferPart`, `rightPart` (`Hastings/ThreeWaySplitting.lean:270–316`), `cutLeftPart`/`cutBoundaryPart` (`GluingHamiltonian.lean:32,40`), `smul` (`Hastings/ProjectorFactorizationScaling.lean:53`), `localizedPart` (`Hastings/CutoffPair.lean:82`), `doubled` (`DoubledHamiltonian.lean:42`), `swappedDoubled` (`SwappedDoubledHamiltonian.lean:43`), `DomainInteraction.doubled`/`swappedDoubled` (`DomainPartialSwap.lean:42,84`), `DomainInteraction.toChain` (`ComponentReduction.lean:158`), `paddedInteraction` (`ViableSet/ChainPadding.lean:82`) | the partial Hamiltonian `∑ i ∈ s, Φ.term i`, the scalar multiple, the two-copy interaction `h ⊗ 1 + 1 ⊗ h` on `X × X`, and relabelling or padding of sites | `∑ i ∈ s, Φ.term i` is already the spelling of `Dynamics/BoundedDegreeImaginaryTime` (main); the rest has no counterpart | 4 / 7 / 9 / 29 / 1 | (b): `Interaction.partialHamiltonian s`, an `SMul ℝ` instance, `Interaction.doubled` for any `X`, and `Interaction.relabel`, each stated once for `Interaction X S`. The chain and domain versions are deleted. The doubled chain and domain interactions are currently two copies |
| H4 | `MPSTensor.interactionHamiltonian`, `MPS/Symmetry/GappedInteractionPath.lean:35` | the translation-invariant nearest-neighbour ring Hamiltonian `∑_i embedLocalOperator 2 N i h` | `Sites/Lattice/Ring` (main) for the geometry; no translation-invariant constructor | 33 | (b): `Interaction.translationInvariant` on the ring. Uses `place`, not `MPOTensor.embedLocalOperator` |
| H5 | `MPSTensor.openInteractionMatrix`, `MPS/ParentHamiltonian/BulkObservableCommutator.lean:57`; `blockedInteractionMatrix`, `BlockedInteractionKernel.lean:68`; `chainWindowOperator` | `∑_{i<N+1−R} chainWindowOperator N i h`: the open-chain translates of one window matrix | `ChainInteraction`, `place` (pin) | 36 / 4 / 26 | (c): the open-chain analogue of H4. Express it as `Interaction.hamiltonian`; `chainWindowOperator` becomes `place` |
| H6 | `ManyBody.RectangleInteraction.toAreaLawHamiltonian`, `PEPS/AreaLaw/RectangularHamiltonian.lean:124` | the rectangle interaction as a range-one `PlaneInteraction` on `rectangularDomain` (via `QuantumCircuit.embedOp`) | both types are QICLean's | 10 | (b): a map between two QICLean models belongs in `Models.lean`. Use `place` instead of `embedOp` |
| H7 | endpoint and fusion Hamiltonians in `MPS/Symmetry/MPOSymmetry` (`mixedEndpointActiveHamiltonian` `MixedEndpointActiveHamiltonian.lean:351`, `endpointCoreHamiltonian`, `jointEndpointCoreHamiltonian`, `…ParentInteraction`), `bondProductParentHamiltonian` (`MPS/Symmetry/BondProductParentHamiltonian.lean:80`), `varyingPhysicalParentHamiltonian` | Hamiltonians built from tensor data | none | 1–5 each | (d). Sum them as `Interaction.hamiltonian` when they are next touched |
| H8 | area-law statements on QICLean models: `AmplificationBound`, `SublinearCollarBound`, `TwoFamilyDecomposition` (`PEPS/AreaLaw/BoundaryTheorem.lean:110–193`), `UniformAreaLaw`, and `FrustrationFreeAreaLaw` (PR #10936) | statements and intermediate propositions of a specific proof | stated with `PlaneInteraction` and `IsGapped` | 3–9 | (c): proof-specific. Under rule 3 of "Where a declaration goes" they stay next to their consumer until they have a second use |

---

## 4. Regional entropy, cuts, supports and geometry

| # | Lean name, `file:line` | Meaning | QICLean counterpart | Files | Rec. |
|---|---|---|---|---|---|
| E1 | `TNLean.Lattice.reducedState`, `regionalEntropy` (`Lattice/RegionalEntropy.lean:35,60`), and the bridge `Lattice/RegionalEntropyBridge` (`reducedState_eq_regionState`, `regionalEntropy_eq_regionEntropy`) | the reduced state and entanglement entropy of a region | `ManyBody.regionState`, `regionEntropy` (`Sites/RegionState.lean:42,66`, pin) | 40 / 89; bridge imported by 8 | (a): the outstanding part of step 3H.2. The design document already lists the bridge for deletion |
| E2 | the QICLean-side duplicates still used by TNLean: `Entropy.SiteConfig`, `Entropy.IsSupportedOn` (`QICLean/Entropy/SupportedMarginalTails.lean:59,68`), `Entropy.regionEntropy`, `Entropy.regionState` (`Entropy/LocalLift.lean:99`), `Entropy.reducedPure` | site configurations, support predicate and regional entropy in the `Entropy` namespace | `ManyBody.Config`, `ManyBody.IsSupportedOn`/`supportedOperators`, `ManyBody.regionEntropy` (pin) | 323 (`Entropy.IsSupportedOn`), 57 (`Entropy.regionEntropy`) | (a): QICLean step 4.0 deletes the abbreviations, then TNLean sweeps. QICLean currently has two regional entropies and two support predicates, which breaks "one definition per notion" inside QICLean |
| E3 | `TNLean.Lattice.Site`, `Configuration` (`Lattice/FiniteDomain.lean:39,43`), `StateSpace` (`Lattice/StateSpace.lean:41`); `TNLean.PEPS.Approximation.Configuration`, `StateSpace` (`PEPS/Approximation/Basic.lean:50,54`) | `↥Λ`, `↥Λ → Fin q`, `EuclideanSpace ℂ (↥Λ → Fin q)`; and the same for the `L × L` square | `ManyBody.Config (Qudits V q)` (`Sites/Config.lean:39,42`) | 247 (`(Site Λ)`), 22, 126 (`StateSpace Λ q`); 65 (`StateSpace L q`) | (a): two TNLean copies of one QICLean abbreviation. If a short name is wanted, add a single `ManyBody.StateSpace X` to QICLean |
| E4 | `TNLean.Lattice.configurationSplit`, `Lattice/FiniteDomain.lean:78` | `Configuration Λ q ≃ RegionConfig × ComplConfig` | `ManyBody.cutEquiv` (`Sites/Config.lean:53`) | 5 | (a) |
| E5 | `TNLean.Lattice.edgeBoundary`, `ambientDilation`, `Lattice/FiniteDomain.lean:54,62` | edge boundary `∂_Λ A`; integer sup-norm dilation | `ManyBody.edgeBoundary`, `ambientDilation` (`Sites/Lattice/Plane.lean:176,208`, pin): the same text | ≤ 63 / ≤ 107 (shared names) | (a): exact copies |
| E6 | `TNLean.Lattice.graphNeighborhood`, `Lattice/FiniteDomain.lean:47` | closed `R`-neighbourhood of a set in the induced plane graph | `ManyBody.graphBall G a l` for one point (`Dynamics/GraphBall.lean:60`), `metricRangeBall` | 21 | (b): a set version of `graphBall` for any `SimpleGraph`, with the plane as the instance |
| E7 | `TNLean.PEPS.AreaLaw.cutEdges`, `PEPS/AreaLaw/CrossingBudget.lean:58`; `innerBoundary`, `endpointBoundary` (`BoundaryConventions.lean`); `graphPseudoEMetricSpace` (`GraphExtendedMetric.lean`); `setDist` (`FiniteSetTruncation.lean`) | ordered edge boundary in any graph; inner and endpoint vertex boundaries; graph distance as an extended pseudometric; distance between sets | QICLean's `edgeBoundary` exists for the plane only; `metricRangeGraph` | 3 / 4 / 4 / 6 / 2 | (b): generic graph geometry for `Sites`. QICLean's plane `edgeBoundary` should itself be the instance of a `SimpleGraph` edge boundary |
| E8 | three cut budgets: `TNLean.MPS.AreaLaw.cutLogBudget` (`MPS/AreaLaw/Hamiltonian.lean:80`), `TNLean.Lattice.cutLogBudget` (`Lattice/MarginalTails.lean:65`), `TNLean.PEPS.AreaLaw.cutBudget` (`PEPS/AreaLaw/CrossingBudget.lean:211`, with the bridge `cutBudget_eq_cutLogBudget`) | `ℬ_A = 1 + ∑_{X crossing A} log²(e·dim X)` | `Entropy.cutLogBudget` (`Entropy/GapSurprisal.lean:188`) with `crossingTerms` (`Sites/Cut.lean:32`) | 16 / 23 | (b): one `ManyBody.cutLogBudget S X A` for any support family. The chain, plane and designated-support budgets are its instances, and the bridge disappears |
| E9 | `TNLean.Lattice.concentrationWidth`, `Lattice/MarginalTails.lean:119` | width at which the marginal tail reaches `(n+2)^{-M}` | `Entropy.concentrationWidth` (`Entropy/TypicalMarginalMass.lean:48`, main) | 2 | (a) at the next pin move |
| E10 | `TNLean.Lattice.relabelSites`, `regionRelabel`, `sumSitesProduct`, `disjSumRegionEquiv` (`Lattice/SiteRelabelEntropy.lean:60–145`) | site relabelling of a vector; product vector on `A ⊕ B` | `ManyBody.relabelVector` (`Sites/Relabel.lean`, pin); `Entropy.sumSitesProduct`, `disjSumEquiv` (`Entropy/SumSitesProduct.lean`, main) | 9 / 5 | (a) |
| E11 | `TNLean/Lattice/{RegionEntropyInequalities, ZeroEntropy, SupportedUnitaryEntropy, EntropyComparison, EntropyDimension}.lean` | regional entropy inequalities, zero entropy, mutual information under supported unitaries | `Entropy/{RegionEntropyInequalities, ZeroEntropy, MutualInformationPerturbation}`, `Sites/SupportedUnitary` (main, QICLean #1151) | 12 / 9 / 5 / 5 / 6 importers | (a) for the ported modules at the next pin move. Check `EntropyComparison` and `EntropyDimension` declaration by declaration against #1151 |
| E12 | five coefficient matrices of a chain vector across a cut: `TNLean.MPS.AreaLaw.cutMatrix` (`MPS/AreaLaw/OpenMPS.lean:60`), `MPSPreparation.cutMatrix`/`cutRank` (`MPS/Preparation/CutRank.lean:72,78`), `cutCoefficientMatrix`/`cutCoefficientRank`/`CutPrefixConfig` (`MPS/Preparation/MinimalCutRepresentationCuts.lean:29–121`), `cutColumn` (`MPS/AreaLaw/ViableSet/Basic.lean:88`), `physicalCutMatrix` (`PEPS/PhysicalProductCut.lean:38`) | the Schmidt coefficient matrix `ψ(σ_A, τ_{Aᶜ})` and its rank, for the region `A` | `cutEquiv`, `cutVector` (`Sites/RegionState.lean:35`), `schmidtRank` (`Channel/SchmidtRank.lean:91`), `Matrix.schmidtCoeffMatrix` | 65 (shared name `cutMatrix`) / 7 / 39 / 7 / 5 | (b): one `ManyBody.cutMatrix D ψ` along `cutEquiv` and one `cutRank`. The prefix cuts of `Fin N` are the case `D = {i < k}` |
| E13 | `QuantumCircuit.IsSeparatedBy` (`Circuit/Geometry.lean:220`), `ringSupportDistance` (`MPS/Preparation/FiniteRingLiebRobinson.lean:76`) | separation of two sets on the ring | `ManyBody.IsRingSeparated`, `ringBall` (`Sites/Lattice/Ring.lean:55,120`, main) | 11 / 6 | (a) at the next pin move |

---

## 5. Remarks

* "Positive terms annihilating a vector" is assumed in at least eight different ways: on the
  terms of a `PlaneInteraction` (PR #10936), on a bare bond family through the sum (AKLV), on
  a bare bond family of projections (ALVV), on constraint families (PEPS amplification), on
  abstract `E →L[𝕜] E` and `E →ₗ[ℂ] E` families (ALVV, sweep, martingale), on placed regional
  terms (PEPS parent), on linear maps on `NSiteSpace` (MPS parent), and in the root namespace
  `FrustrationFree`. None of them can `rw` against the others.
* A gap is encoded in five ways (§2: `IsGapped`, projector form, quadratic form, norm form,
  spectrum form). QICLean has the bridge only for the projector form.
* The Hamiltonian of an interaction is spelled as `Φ.hamiltonian`, `∑ i, h i`, `termSum`,
  `parentHamiltonian`, `parentHamiltonianES`, `regionParentHamiltonian`,
  `interactionHamiltonian` and `openInteractionMatrix`. The design document requires the single
  spelling `Φ.hamiltonian`.
* Two QICLean-internal dual systems block the TNLean sweep: `Entropy.IsSupportedOn` against
  `ManyBody.IsSupportedOn`, and `Entropy.regionEntropy`/`regionState`/`reducedPure` against
  `ManyBody.regionEntropy`/`regionState` (E2). They are QICLean step 4.0.

## 6. Counts by recommendation

51 items in total.

| Class | Count | Items |
|---|---:|---|
| (a) delete, use QICLean | 15 | FF3, FF7a, G1, G5, G9, G10, E1, E2, E3, E4, E5, E9, E10, E11, E13 |
| (b) move up to QICLean, generalized | 23 | FF4, FF5, FF6, FF7b, FF10, FF11, FF14, G2, G3, G4, G7, G8, G11, G12, H1, H2, H3, H4, H6, E6, E7, E8, E12 |
| (c) keep, restated through QICLean | 10 | FF1, FF8, FF9, FF12, FF13, FF15, FF16, G6, H5, H8 |
| (d) keep, tensor specific | 3 | FF2, G13, H7 |

## 7. Prioritized migration list

1. **PR #10936 before it merges.** Do not add `IsFrustrationFreeGapped` on `PlaneInteraction`.
   Land `ManyBody.Interaction.zeroSpace`, `IsFrustrationFree`, `mem_zeroSpace_iff`,
   `zeroSpace_eq_groundSpace` and `isGapped_zero_iff_inner` in QICLean (§1.3). Restate Step 0
   of `docs/formalization/frustration-free-area-law-plan.md` with these and with hypotheses, and
   rebase the stack #10936–#10938 onto them. Move the abstract sweep and support-projection
   lemmas already on `main` (FF14) to QICLean `Analysis` and `Sites` in the same QICLean pull
   request.
2. **Next pin move (QICLean `main`).** Delete the TNLean copies of what QICLean now has: G9,
   E9, E10, E11 and E13. In the same pull request delete the copies of what the current pin
   already has: E1 (with `RegionalEntropyBridge`), E3, E4, E5, FF7a, G5 and G10.
3. **The bond-family bundle (H1, H2).** Add `BondInteraction` to `Models.lean` and one map to
   `ChainInteraction L q 1`. Sweep the 214 files of `MPS/AreaLaw` one subdirectory per pull
   request, in this order: AKLV and ALVV (restating FF8, FF9 and FF12 with
   `IsFrustrationFree`), then Huang, ViableSet and Algorithm. The sweep also removes most uses
   of `Entropy.IsSupportedOn`, so do it together with QICLean step 4.0 (E2).
4. **Gap encodings (G1–G3).** With the characterization theorems of item 1, restate the 51
   projector-form, 8 quadratic-form and 106 norm-form statements to conclude or assume
   `IsGapped`. Start with the martingale method (FF6, moved to QICLean `ManyBody/Hamiltonian`)
   and `Algebra/*Gap*` (G7), then the parent-Hamiltonian gap theorems.
5. **Generic interaction operations (H3, H4, H6, G12).** Add `partialHamiltonian`, `SMul`,
   `doubled`, `relabel`, `translationInvariant` and `positiveTerm` for an arbitrary
   `Interaction`, and delete their chain, domain and plane copies.
6. **Parent Hamiltonians as interactions (FF1, FF15, FF16, H5).** Make the MPS and PEPS parent
   Hamiltonians `Interaction.hamiltonian`, so that frustration-freeness is `mpv A ∈ Φ.zeroSpace`.
   Remove the `ES` second representation in `Martingale/`, and replace `chainWindowOperator`
   and `embedLocalOperator` by `place` (step 4.1 of the design document, still open for
   `embedLocalOperator`).
7. **Cut and boundary notions (E6, E7, E8, E12).** Add a generic `SimpleGraph` edge boundary
   and set neighbourhood, one `cutLogBudget` over a support family, and one `cutMatrix`/`cutRank`
   along `cutEquiv`. Then delete the three budgets, the bridge `cutBudget_eq_cutLogBudget` and
   the five cut flattenings.
8. **Commuting parent structures (FF3, FF4, FF5).** Delete `Decorrelation.HasCommutingParentHam`
   and `Decorrelation.IsDecorrelated`. Move `CommutingParentHamiltonian` next to QICLean's
   `IsDecorrelated`, stated as a commuting frustration-free two-term interaction.
9. **Late:** G4 (a gapped symmetric path of interactions, in QICLean); FF11 (with the
   quasi-local algebra); G8 and G11 (into `DisjointRegionalGround` and `Analysis`).
