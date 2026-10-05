# SCP10 current coverage: source obligations and publication layers

Read-only audit, 2026-10-05. Source: `Papers/1001.3807/paper_v3.tex`, arXiv:1001.3807v3. This supplements, rather than overwrites, the inventory pinned to `680b30da6fec94f5b269c3753ab4b8c86da79936`.

## Evidence and verdict

The old inventory understates several proved results. In particular, the entire uniform semi-regular torus parent kernel and its exact degeneracy, and genuine two-dimensional physical parent-term commutation, are already merged. The full source three-block intersection is local, and the full source four-block closure is in a draft. Neither the old declaration counts nor these upgrades justify “the paper is complete.”

Publication layers checked:

- **Merged:** main `846837a23c6c0382e497531ef7da2708d95c44c3`, incorporating #8678/#8694.
- **Draft #8696:** remote head `28e280fba1a76bcd4e880775116879e97e6fce1b`. Its published tree was verified as exactly `bda84c7e17ddb0f7b1b2fb5bafd8b1eab5178dce`. I independently verified that tree for local `1917417cd3441a1140dd3fcb83d5d14cfe101502` and inspected that local tree. The source audit used this verified tree-equivalent local commit.
- **Local, independently reviewed packets:** `8a531f13d26b5f6c46ab5216609aca04a02327cf` (geometric regular RG) and `f0b67785c42c554696fa56a031043bd5243fcb57` (full source three-block intersection).
- **Locally verified, pending publication:** direct parent-ground-state observable corollaries for 6.7–6.10 at source commit 42f83ebe620995fa982bf036ffc4d6c9cb1b0fc8. Independent strict review passed. Dependent/nonuniform parent-to-cut development remains active.

This is a source/signature audit, not a new Lean build, CI report, or re-proof. Existing focused validation reports were read, but no build, download, repository edit, issue edit, or publication was performed. Uncommitted integration/router changes are not evidence for proof coverage.

## Proposed row revisions

Use two independent facts in each row: **what mathematical scope is proved** and **where that proof is published**. A bare “Partial” conceals major completed conclusions; a bare “Complete” conceals the remaining model restrictions.

### 5.4: source three-block intersection

**Local: complete matching source statement. Merged/draft: restricted predecessors only.**

Replace the strip-only anchor with `TNLean.PEPS.ThreeBlockDependent.regionalBoundarySpace_inf_eq_openBoundarySpace`, `ParentHamiltonian/ThreeBlockGInjectiveIntersection.lean:97–106`, at local `f0b67785c`.

Its equality is between two literal regional contraction ranges and the whole three-tensor open-boundary range. Each regional boundary has six virtual incidences and is freely correlated with the omitted physical factor; the whole boundary has eight virtual incidences. All ten bonds have independently chosen finite alphabets and matching semi-regular representations, and all three physical alphabets/tensors may differ. Hypotheses are finite group, per-bond semi-regularity, and local G-injectivity. No regularity, common dimension, supplied expansion, or closure/parent theorem is assumed.

The source Theorem 5.4 is this three-block geometry, not an assertion about every arbitrary pair of graph regions. The old “unrestricted overlapping graph-region contraction remains” must not keep this precise source theorem marked mathematically unproved. General region-growing/parent assembly is a separate downstream obligation.

### 5.5: source four-block closure

**Draft #8696: complete matching source statement. Merged: restricted predecessors only.**

Use [`DependentTorus.fourCutSpace_eq_commutingClosureSpan`](https://github.com/LionSR/TNLean/blob/28e280fba1a76bcd4e880775116879e97e6fce1b/TNLean/PEPS/DependentTorusClosureTheorem.lean#L89-L106).

The conclusion is the actual four-cut intersection equals the span of commuting closures. `fourCutSpace` is an intersection of four correlated-boundary ranges, not a parent kernel or a subspace defined to have the conclusion. Eight independently sized, labelled bonds preserve parallel incidences; four independent physical alphabets/tensors are permitted. Each bond carries its own semi-regular representation, matched at both ends. No isometry, uniformity, parent-kernel classification, or assumed spanning premise occurs. Algebraic unitarity is not required, making the statement at least as strong as the source convention.

This proves the source four-block theorem. It does not by itself identify an arbitrary large-lattice plaquette parent kernel with those four blocked cut spaces.

### 5.7 and 5.9: parent kernel and degeneracy

**Merged: the whole kernel and its exact dimension in the uniform native torus scope. Residual broader scope remains.**

Use:

- [`IsGInjective.torusParentKernel_eq_commutingClosureSpan_of_isSemiRegular`](https://github.com/LionSR/TNLean/blob/846837a23c6c0382e497531ef7da2708d95c44c3/TNLean/PEPS/ParentHamiltonian/TorusSemiRegularParentGroundSpace.lean#L31-L58).
- [`IsGInjective.finrank_torusParentKernel_of_isSemiRegular`](https://github.com/LionSR/TNLean/blob/846837a23c6c0382e497531ef7da2708d95c44c3/TNLean/PEPS/ParentHamiltonian/TorusSemiRegularParentDimension.lean#L75-L89).

Exact hypotheses: both periods at least three; one arbitrary unitary semi-regular `U` on all native bonds; one arbitrary native G-injective tensor `a` repeated at every site; actual positive parent interactions with the prescribed regional kernels. Conclusion: `ker H = span {torusGClosure U a g h | Commute g h}` and `finrank ker H = Nat.card (CommutingPairConjugacyClass G)`. This is not merely `ker H ∩ closureSpan`, and a ground-vector expansion is not a hypothesis. Canonical projector-complement parents are an instance.

Remove the old “global kernel inclusion and full semi-regular parent transport remain” and “exact count awaits spanning” statements. Remaining source generality: link-dependent representations/alphabets, fully independently chosen site alphabets/tensors in the final native closure capstone, and exceptional periodic presentations with parallel bonds or loops. Existing oriented parent transport already handles vertex-dependent tensors for a fixed `U` and common finite physical alphabet; do not describe that component as absent. It still does not furnish the independently dimensioned full native closure classification.

### 6.5: physical blocking with removable Bell pairs

**Draft: actual global bundled-graph physical factorization. Local: actual 2×2 fine-lattice specialization. Still scope-restricted overall.**

Draft `exists_regularGraphPhysicalSupportIsometry` in `RegularGraphPhysicalBlocking.lean` derives normalized-adjoint local physical maps, their isometry on the original product physical range, and the exact graph state factorization into a regular canonical coarse state and normalized Bell registers. It retains the positive site factors and `sqrt(|G|^|K|)^|E|`. This is not merely a virtual representation-coordinate identity. Its input graph is already bundled.

Local `isGIsometric_twoByTwoBundledGraphSite` and `exists_regularTwoByTwoPhysicalSupportIsometry` in `RegularTwoByTwoPhysicalBlocking.lean` remove the missing fine-lattice bridge for 2×2 blocks. The actual block Gram and complete bond reindexing are derived from fine-site G-isometry. Fine tensors may vary. Physical Bell separation uses coarse periods at least three; the bond-indexed regrouping alone works at every positive coarse period.

Keep a precise remaining target for other block/quotient geometries, small-period physical Bell separation, boundary conditions, and inserted/twisted sectors. Do not retain “global physical state factorization remains” without these qualifications.

### 6.6: RG fixed point with the same original tensor

**Local: full normalized same-original-tensor identity for the untwisted homogeneous torus, coarse periods at least three. Broader scope remains.**

Use `exists_regularTwoByTwoOriginalTensorIsometry`, `RegularTwoByTwoOriginalTensor.lean:83–99`, at local `8a531f13d`.

Its sole substantive tensor assumption is regular G-isometry of the homogeneous four-leg `a`. It derives nonzero fine and coarse states, unit Bell norm, positive factors, block-local physical matrices, and a Hilbert isometry on the actual fine physical support. The conclusion includes both `I ψfine = R · (ψcoarse ⊗ ω)` with complete positive scalar and `I (ψfine/‖ψfine‖) = (ψcoarse/‖ψcoarse‖) ⊗ ω`. The coarse tensor is the original `a`, not just an unspecified canonical representative. Locality is exposed by the product-of-block-matrices coefficient formula.

Replace “Open; local prerequisites only” with this proved local result. Remaining: physical separation for coarse periods one/two, inserted/twisted closures, other boundary conditions/tilings. A unitary on unused ambient directions is not asserted; support isometries are the precise formulation allowed by the source's physical-support restriction. Non-regular approximate RG and the source's tentative uniqueness footnote are not secretly proved by this theorem.

### 6.7–6.10: ground-state observables

**Merged: closure-superposition statements; mathematical corollaries for the same uniform regular parent scope. Direct parent-vector API packaging is independently verified locally, pending publication.**

Existing exact conclusions:

- 6.7: `IsGIsometric.torusClosureSuperpositionCut_stripe_local_equivalence` produces a unitary on the union of two coordinate-zero width-one stripes between normalized nonzero superpositions.
- 6.8: `IsGIsometric.torusPhysicalCut_local_equivalence_of_isSimplyConnected` gives equal expectations of every local observable and a complementary physical unitary.
- 6.9: `IsGIsometric.exists_torusPhysicalCut_common_density_of_isSimplyConnected` gives one common trace-one positive density, rank `|G|^(b−1)`, flatness, von Neumann entropy, and every finite real-order Rényi entropy with `α≥0` equal to `(b−1) log |G|`.
- 6.10: `IsGInjective.torusPhysicalCut_rank_zeroEntropy_of_isSimplyConnected` gives the rank and zero-order entropy for regular G-injective tensors; it does not assert flatness or other entropy orders.

All use ordinary native periods at least three. For 6.8–6.10, the induced occupied nearest-neighbor graph is connected and the actual closed-cell realization is simply connected. Those geometry hypotheses are explicit and already sufficient; spanning trees, boundary enumeration, and complementary winding paths are derived internally.

The old “all parent states await spanning” is now stale **within this scope**. The merged 5.7 theorem spans by exactly the same `torusGClosure`, and `torusClosureSuperpositionCut` (`RegularTorusEntropy.lean:162–168`) is definitionally that finite linear combination evaluated at `assembleRegionσ`. Finite span-membership supplies coefficients; the physical-coordinate equivalence transports nonzeroness. Thus no new density, entropy, stripe, or topology theorem is required to apply them to every nonzero vector of that uniform regular parent kernel. The five direct-parent corollaries and actual-Hψ=0 regressions have passed independent strict review; publication and aggregate CI remain.

Real remaining scope is smaller periodic incidence models and any enlargement beyond the precise source block/regular-tensor hypotheses. Extension of the independently dimensioned parent classification is a different target; do not characterize routine coefficient extraction as an unresolved global spanning proof.

### 6.11 and 6.12: projector correction and commuting PEPS parents

**6.11 remains Corrected. 6.12 is merged in genuine two-dimensional finite-simple-graph scope.**

Keep the source correction: the displayed operator is the normalized projector onto the local range; the parent interaction is its complement. Positive factors cannot be omitted.

Replace the MPS-only 6.12 anchor by [`regularIsometric_canonicalRegionParentInteractions_commute`](https://github.com/LionSR/TNLean/blob/846837a23c6c0382e497531ef7da2708d95c44c3/TNLean/PEPS/ParentHamiltonian/GIsometricRegionParentHamiltonian.lean#L124-L146). For any finite simple graph, arbitrary locally regular G-isometric physical tensors, and any two possibly overlapping regions, the actual extended canonical physical parent interactions commute. No connectedness, ambient physical surjectivity, assumed regional Gram, or supplied physical transport is required.

Every pair of ordinary torus plaquettes with periods at least three is covered by specialization. This is already the substantive two-dimensional theorem, not a missing geometric proof. Remaining incidence scope: parallel bonds/self-loops and degenerate small periodic presentations. Do not claim all positive operators with the same kernels commute; the theorem concerns canonical orthogonal projector-complement interactions.

## Section 7 and unchanged qualifications

- **7.B needs an explicit merged upgrade:** `torusBondNetwork_kitaevPeriodicElementarySite_eq_colorNetwork` and `_eq_quantumDoubleNetwork` in `KitaevNativeGlobalBlocking.lean` derive the globally tiled alternating binary checkerboard contraction on even fine periods, for all positive coarse periods, with identity bonds and exact scalar one. The old “no globally tiled alternating checkerboard state” is false now. These maps regroup physical spins; they are not a physical CNOT disentangler or the nonabelian T-to-K RG construction.
- **7.A and 7.D remain open at their advertised conclusions:** checkerboard stabilizer Hamiltonian/projection preparation and the full explicit quantum-double Hamiltonian identification are not supplied by a tensor coefficient or generic commutation theorem.
- **7.C/7.E retain source corrections:** local quantum-double tensor normalization/orientation and the torus trivial-holonomy qualification on color/Gauss-law coefficients remain essential.
- **7.F/7.G and 7.H's strong closed-state result must not be understated:** the minimal semi-regular representation, printed bond isometry, actual full finite closed simple-graph state equivalence, nonvanishing and universal semi-regular minimum are proved. Missing dangling boundaries, general inserted matrices, multigraphs or infinite contractions do not erase this exact closed-state conclusion.
- **Qualify 7.H's old “parent-Hamiltonian equivalence open”:** merged `nonempty_orientedSemiRegularGInjectiveParentEquiv` and its kernel counterpart provide linear full-parent-space equivalence for fixed `U`, constant-incidence finite simple graphs, common physical alphabet, and vertex/edge-covering regional families. This is not yet a theorem that the specific Section 7 bond isometry conjugates all local Hamiltonian operators or preserves spectra/gaps. State-isometry equivalence, parent-kernel equivalence, and Hamiltonian conjugacy must remain separate claims.
- **6.13–6.21 retain their source-string/excitation qualifications.** New closure, ground-kernel and RG theorems do not prove arbitrary endpoint-fixed string deformation, unrestricted excitation geometry, vacancy-free flux motion, or global excitation membership. Keep the six-spin flux-creation normalization `( |G| |C_G(g)| )^(-1/2)` and the existing size/vacancy restrictions. 6.18 remains definition-level, not proof that an isolated closed-vacuum charge is nonzero.
- Preserve all other source corrections and previously justified specializations, including unitality in 4.1, the scaled regular convention in 6.1, and derived ordinary specializations 3.2–3.4. No reclassification based on line counts or a separate wrapper name is justified.

## Existing tracker ownership and precise next targets

1. [#8271](https://github.com/LionSR/TNLean/issues/8271): retain the overall source crosswalk and the still-open string/excitation/Section 7 obligations. Update the proof anchors and publication layer, not a completion percentage.
2. [#8674](https://github.com/LionSR/TNLean/issues/8674): source 5.5 is in draft #8696; source 5.4 is locally complete at `f0b67785c`. After their respective publication/verification, do not retain arbitrary-graph-region generalization as a hidden condition for these exact source declarations.
3. [#8675](https://github.com/LionSR/TNLean/issues/8675): replace the uniform spanning/count blocker with the completed merged results. Retain the actual independently dimensioned/nonuniform parent-to-cut task: prove that local plaquette parent constraints yield the genuine blocked open-cut ranges, with representation/tensor/physical-coordinate identifications derived, then invoke 5.4/5.5. Record the active 6.7–6.10 direct-parent wrappers as API consolidation rather than another spanning theorem.
4. [#8676](https://github.com/LionSR/TNLean/issues/8676): distinguish draft bundled physical Bell separation from local geometric/same-original-tensor 2×2 RG; retain the specifically excluded small-period, inserted-sector and other-boundary/tiling work. Record the merged binary checkerboard global contraction separately.
5. [#8464](https://github.com/LionSR/TNLean/issues/8464): the substantive original 2D physical commutation target is now proved on finite simple graphs. If kept open for scope, narrow its remaining target to exceptional periodic incidence/multigraph models; do not describe overlapping plaquette commutation as absent.

No duplicate issue is proposed. MPU gauging is outside this audit.
