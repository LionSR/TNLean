# GLM23 v3 source-complete implementation inventory

Audit baseline: `f3d3bade1f56b87f88fc8a87314bf451591483b7` of `LionSR/TNLean`, 2026-10-05 UTC. Source: [arXiv:2203.12563v3](https://arxiv.org/abs/2203.12563v3), Garre-Rubio, Lootens and Molnár, *Classifying phases protected by matrix product operator symmetries using matrix product states*.

The 2,477-line vendored `Papers/2203.12563/REsubmission.tex` was read through its prose, equations, tables and tensor-diagram indices, together with `Papers/NOTICE.md`, repository guidance, relevant Lean statements, blueprint nodes, audits and paper-gap notes. The exact-version check downloaded the exact v3 source archive from `https://arxiv.org/src/2203.12563v3`, extracted the TeX, and verified byte equality (`cmp`) with the vendored file. Both SHA-256 digests: `c820b20187584d441c1a40ef80fdccbc8a2aad819ac6673464c6b913c28fa58c`. The source is CC BY 4.0, not covered by the repository Apache license.

This report records baseline source coverage, not a new proof or build attestation. Existing declarations were inspected in the baseline checkout. Tracker #8012 was refreshed during the audit. Candidate declarations are listed separately and are not counted as merged coverage; their verification is recorded in the accompanying PR.

## Findings that change the plan

- The paper has only two numbered definitions and one unnumbered lemma; almost all mathematical content is in unnumbered claims and displayed tensor identities. The inventory therefore has 103 claim rows and an exhaustive 58-label index, not just a theorem checklist.
- The general §2–3 starting point is length-independent arbitrary-boundary closedness/invariance. Merged periodic reductions have nilpotent remainders. Exact complete-zipper F theory is reusable, but adding star closure, zero remainder, an exact decomposition, or a supplied coupled pentagon is not completion of the source theorem.
- The scalar group branch is substantially implemented: tensor-derived anomaly, scalar L compatibility, stabilizer restriction, corrected reconstruction and Mathlib H² torsor, and the exact-closed-fusion on-site lemma. These do not establish general multiplicity symbols or the physical §5 classification.
- The §5 main iff is missing. Its target includes arbitrary non-fixed-point tensors, endpoint physical embeddings, degenerate blocks, continuous and varying-bond paths, symmetrization, and a gap uniform in both parameter and chain length. A fixed-point/on-site/single-block path is not source-complete.
- The full examples section ends at line 2287, not 2233. The omitted tail includes the right-zipper projector and its PBC-support identity. Appendix A and Appendix B each contain load-bearing proofs and need explicit leaves.
- Existing genuine source corrections must survive: Eq. (20) needs a stabilizer-trivializing fusion gauge; TRSF1group needs conjugate(L)/L rather than |L|²; the periodic group operator has one shift per site; the Rep(S₃)/Z₃ printed ψ row is false. No attempt should prove the false printed equations.
- The positive symmetric-boundary theorem is already general over the current fusion-ring assumptions; it requires neither commutativity nor indecomposability. Old #8049 prose speculating otherwise is not the signature.
- Printed Klein one-qubit anomaly coverage remains only the ab sign; generic four-level and two-qubit condensation models are different realizations. Degree-three U(1) versus C× comparison remains an explicit gap even though C× Klein H³ is fully classified.

## Status semantics

- **merged**: the indicated mathematical statement has existing implementation in the audited main snapshot. Any explicit boundary still applies.
- **restricted**: only a specialization, a weaker-conclusion layer, or related existing ingredient is present; the whole source claim remains open.
- **conditional**: source-relevant algebra is proved for supplied tensors/gauges/relations whose construction from the source hypotheses is not yet established.
- **corrected-source**: the printed claim has a documented genuine correction; the row states which corrected portion is implemented and what remains.
- **missing**: no implementation of the specific source claim was found. Shared reusable modules are not credited as its proof.
- **unmerged**: only work in flight; never count it as main or built. This baseline inventory identifies no pre-existing open PR from the scoped live searches, and lists the candidate files separately.

## Live tracker and PR reconciliation

All eleven PRs historically listed as open in #8012 were fetched live and are merged. The audit has corrected the tracker body; the immutable baseline below explains the discrepancy.

| PR | Merged at (UTC) | Subject |
|---|---|---|
| [#7971](https://github.com/LionSR/TNLean/pull/7971) | 2026-09-25T17:35:13Z | feat(MPS/Symmetry): anomaly three-cocycle of a group of matrix product unitaries from fusion tensors |
| [#7976](https://github.com/LionSR/TNLean/pull/7976) | 2026-09-25T18:38:56Z | feat(Algebra): cyclic gauge invariant of scalar three-cocycles |
| [#7985](https://github.com/LionSR/TNLean/pull/7985) | 2026-09-25T17:41:12Z | feat(MPS/MPDO): gauge covariance of complete-zipper F-matrices |
| [#7988](https://github.com/LionSR/TNLean/pull/7988) | 2026-09-25T17:24:13Z | feat(MPS/Symmetry): fusion and action tensors of matrix product operator algebras |
| [#7989](https://github.com/LionSR/TNLean/pull/7989) | 2026-09-25T17:23:32Z | feat(MPS/MPDO): complete zipper fusion families from split compressions |
| [#7990](https://github.com/LionSR/TNLean/pull/7990) | 2026-09-26T04:36:26Z | feat(MPS/MPDO): reductions of action tensors |
| [#7991](https://github.com/LionSR/TNLean/pull/7991) | 2026-09-25T18:24:56Z | feat(MPS/MPDO): complete zipper fusion family in the star-closed case |
| [#7992](https://github.com/LionSR/TNLean/pull/7992) | 2026-09-26T06:14:25Z | feat(MPS/Symmetry): an anomalous group of matrix product operators has no invariant normal state |
| [#8007](https://github.com/LionSR/TNLean/pull/8007) | 2026-09-25T17:40:57Z | feat(MPS/Symmetry): uniqueness of zipper fusion and action tensors up to multiplicity gauge |
| [#8008](https://github.com/LionSR/TNLean/pull/8008) | 2026-09-26T04:59:15Z | feat(MPS/MPDO): simultaneous block left inverse after blocking |
| [#8010](https://github.com/LionSR/TNLean/pull/8010) | 2026-09-26T10:32:20Z | feat(MPS/Symmetry): L-symbols of permuted blocks and the CZX anomaly from its two product states |

Live closed issues verified: #7966 (glossary), #8046 (reconstruction/torsor), #8047/#8143 (closed-fusion on-site criterion), #8049/#8142 (positive boundary/FP dimensions), #8052 (printed NIM-rep tables), #8088 (fusion gauge orientation). Closure of #8052 does not close the explicitly scoped completeness successor #8348. Live open source owners: #7968, #8045, #8048, #8050, #8051, #8053, #8054, #8348, #8480. Shared MPU issues #7330/#7331/#7332/#7360 remain open and must be coordinated, not duplicated. #8315 and children concern Mathlib migration, not blanket absence of the scalar mathematics.

## Coherent implementation leaves

Every leaf delivers a theorem/construction plus source-cited docstrings, correct blueprint owner tags, glossary changes where needed, and narrowly scoped proof/build checks. Source-labelled `\leanok` requires exactly the source hypothesis set (or an explicitly documented source correction). The entire-paper closure gate is PH7 plus the general algebra, TRS, examples and appendices below, not any isolated leaf.

### AB1: Define arbitrary-boundary symmetry
Source: 325–358; 431–458. Existing owner: [#7968](https://github.com/LionSR/TNLean/issues/7968). Dependencies: existing main ingredients only.
Source-faithful length-independent closure and invariance predicates using mpoWithBoundary and groundSpaceMap, their block-diagonal boundary reduction, and exact tensor contractions. Prove finite-length consequences without reversing quantifiers. No conclusion of fusion/action existence yet.

### AB2: Derive exact fusion tensors
Source: 361–426; Appendix A 2307–2453. Existing owner: [#7968](https://github.com/LionSR/TNLean/issues/7968). Dependencies: AB1.
Linearize the boundary multiplication map on the visible block boundary algebra, construct minimal two-sided matrix channels, prove all-word reconstruction, derive n=1/n=2 biorthogonality and exact splitting; instantiate existing CompleteZipperFusionFamily and its F, inverse, pentagon/gauge. Derive any required simultaneous block inverse from source block-injectivity after one justified blocking. No star-closure or zero-remainder assumption may survive the source theorem.

### AB3: Derive exact action tensors
Source: 459–490; 567–591; Appendix A 2455. Existing owner: [#7968](https://github.com/LionSR/TNLean/issues/7968), [#8045](https://github.com/LionSR/TNLean/issues/8045). Dependencies: AB1, AB2.
Apply the same finite-dimensional argument to the boundary action. Construct exact multiplicity action maps, orthogonality, integer multiplicities, periodic consequence, and a complete action-coordinate family usable with existing fusion coordinates.

### FL1: Construct multiplicity L symbols
Source: 491–550. Existing owner: [#8045](https://github.com/LionSR/TNLean/issues/8045). Dependencies: AB2, AB3.
Construct both action-tree bases on their actual support, prove they span the same support, extract the invertible L matrix and contraction formula. Reuse complete-zipper F orientations and treat vanishing individual entries correctly.

### FL2: Prove coupled pentagon gauges
Source: 552–602. Existing owner: [#8045](https://github.com/LionSR/TNLean/issues/8045). Dependencies: FL1.
Compare five three-operator action trees; prove full indexed coupled pentagon, exact action/fusion GL gauge covariance, equivalence relation, and scalar group specialization with reciprocal convention stated. Do not supply the pentagon as an assumption.

### FL3: Prove regular module obstruction
Source: 604; 610–636; 1805. Existing owner: [#7968](https://github.com/LionSR/TNLean/issues/7968), [#8045](https://github.com/LionSR/TNLean/issues/8045), [#8053](https://github.com/LionSR/TNLean/issues/8053). Dependencies: FL2.
Construct the regular module with L=F and establish the full single-state multiplicity-one F trivialization. Keep the fusion-ring no-go distinct. Provide group and regular FP-eigenvalue corollaries.

### PB1: Complete PBC tensor equivalences
Source: 1001–1207. Existing owner: [#7330](https://github.com/LionSR/TNLean/issues/7330), [#7331](https://github.com/LionSR/TNLean/issues/7331). Dependencies: existing main ingredients only.
Package existing reductions, nilpotent residual and exterior-buffer theorems into forward and reverse operator/action equivalences at a common positive blocking. Clearly separate word-dressed identities from bare zipper identities. Coordinate with MPU owner; no parallel implementation.

### PB3: Prove tensor L gauge law
Source: 720–726; 1129. Existing owner: [#7331](https://github.com/LionSR/TNLean/issues/7331). Dependencies: PB1.
Show actual fusion/action tensor gauge changes and different admissible choices induce the library scalar L gauge. Reuse existing β anomaly comparison and dressed uniqueness; prove what can be recovered before claiming bare-matrix gauge exhaustiveness. Owned with MPU track.

### GC1: Assemble stabilizer phase data
Source: 734–761; 840–863. Existing owner: [#7332](https://github.com/LionSR/TNLean/issues/7332), [#7360](https://github.com/LionSR/TNLean/issues/7360). Dependencies: PB3.
Consume merged reconstruction and H² torsor; construct coherent group action from invertible labels, classify transitive actions by stabilizer/coset sets and conjugacy, establish block counts and on-site specialization. No normal-subgroup assumption, quotient-group substitution, or raw-cocycle/class confusion. Coordinate with MPU owner.

### GC2: Derive virtual induced action
Source: 763–836. Existing owner: [#7332](https://github.com/LionSR/TNLean/issues/7332). Dependencies: AB3, GC1.
Prove displayed gxdecomp using coset and inverse action maps; define the partial virtual odot product, prove projective stabilizer law and ω-associativity. State block stabilizers accurately.

### TR1: Derive antiunitary scalar constraints
Source: 865–957. Existing owner: [#8048](https://github.com/LionSR/TNLean/issues/8048). Dependencies: PB3.
From block-preserving TRS and commuting global MPO operators derive q, β, γ and the correct conjugation gauge equations. Apply existing scalar real-gauge and corrected phase-square results. Keep printed |L|² false-source correction and same-β joint hypothesis visible.

### TR2: Derive multiplicity TRS constraints
Source: 959–991. Existing owner: [#8048](https://github.com/LionSR/TNLean/issues/8048). Dependencies: FL2, TR1.
Audit and formalize matrix-valued action-basis conjugation, F/L gauge-reality and squared-phase equivalence. Scalar examples alone cannot establish this generalization.

### PH0: Define MPO-symmetric phase paths
Source: 1234–1272. Existing owner: [#8050](https://github.com/LionSR/TNLean/issues/8050). Dependencies: FL2.
Define source Defs. 1–2 independently of symbols, with same fusion category/F equivalence, endpoint physical embeddings, fixed enlarged exact MPO representation, local Hermitian continuous uniformly gapped PBC path, and exact MPS/action data along it. Identify the minimal Mathlib-based categorical/WHA interface; do not insert desired classification conclusions as fields.

### PH1: Symmetrize parent Hamiltonians
Source: 1274–1320; Appendix B 2457–2466. Existing owner: [#8050](https://github.com/LionSR/TNLean/issues/8050), [#8315](https://github.com/LionSR/TNLean/issues/8315). Dependencies: AB3, PH0.
Construct group and C*-WHA canonical-integral averaging, prove local Hermiticity, symmetry, kernel/ground-space preservation and gap comparison. Audit the nonzero-complement inference in Appendix B; if necessary record a genuine source correction rather than assume the desired positive rank. This requires actual weak-Hopf/integral mathematics, not merely coproduct coassociativity.

### PH2: Reduce to symmetric parents
Source: 1322–1330. Existing owner: [#8050](https://github.com/LionSR/TNLean/issues/8050). Dependencies: PH1.
Construct the qubit embedding of fixed-representation paths; prove common-ground-space convex interpolation remains uniformly gapped and symmetric, yielding parent-Hamiltonian reduction in the exact source phase relation.

### PH3: Choose continuous action bases
Source: 1332–1387. Existing owner: [#8050](https://github.com/LionSR/TNLean/issues/8050). Dependencies: FL1, PH0.
Derive separating block inverses and continuous action bases from continuous exact MPS ground paths. Resolve reverse Hamiltonian-to-canonical-tensor continuity, using shared SCP11 work without stronger fixed-rank or prechosen-coherent-basis assumptions.

### PH4: Prove L-class path invariance
Source: 1388–1577. Existing owner: [#8050](https://github.com/LionSR/TNLean/issues/8050). Dependencies: FL2, PH3.
Turn infinitesimal gauge variation into local and global gauge-class constancy. Include merely continuous tensors and changing minimal bond dimensions, and source PBC long-word extension. A differentiable fixed-dimension specialization remains separately labelled until extensions exist.

### PH5: Build arbitrary-endpoint interpolation
Source: 1580–1685. Existing owner: [#8050](https://github.com/LionSR/TNLean/issues/8050). Dependencies: AB3, FL2, PH0.
Define A(γ), mixed matrix-unit blocks, enlarged MPO and action/fusion tensors for arbitrary injective endpoints with aligned F/L. Prove exact symmetry and coherent unchanged symbols. Must work beyond zero-correlation fixed points.

### PH6: Prove endpoint uniform gaps
Source: 1687–1692. Existing owner: [#8050](https://github.com/LionSR/TNLean/issues/8050), [#190](https://github.com/LionSR/TNLean/issues/190). Dependencies: PH5.
Prove mixed MPO injectivity, interior state injectivity, endpoint extended-support projector continuity, exact endpoint ground spaces, and a positive gap uniform in parameter and system size. Import parent-gap results only at their proved hypothesis/length scope.

### PH7: Complete degenerate phase classification
Source: 1695–1777; main result 1231. Existing owner: [#8050](https://github.com/LionSR/TNLean/issues/8050). Dependencies: PH2, PH4, PH6.
Extend interpolation to all matched blocks/multiplicity channels, establish gap above full degenerate ground space, and prove both directions of the source iff. Consume scalar/group results as specializations; keep the PEPS interface out of this owner’s code.

### GX1: Build arbitrary-boundary group example
Source: 2003–2096. Existing owner: [#8054](https://github.com/LionSR/TNLean/issues/8054). Dependencies: AB2.
Construct the doubled-physical group tensor, exact fusion maps and inverse anomaly, projector identity O_e, group law and unit-modulus adjoint law. Explicitly distinguish it from existing compressed PBC GroupCocycle.tensor.

### GX2: Build coset invariant states
Source: 2098–2200. Existing owner: [#8054](https://github.com/LionSR/TNLean/issues/8054). Dependencies: GX1, GC1, AB3.
Audit printed group/coset indexing and bond dimensions, construct MPS/action entries from reconstructed L, prove source MPOsymG and appropriate injectivity/distinctness. Do not restrict H to normal subgroups.

### GX3: Connect projected and periodic examples
Source: 2202–2224. Existing owner: [#8054](https://github.com/LionSR/TNLean/issues/8054). Dependencies: GX1.
Construct neighboring-half isometry Γ, prove projected-family/PBC intertwining and one-shift-per-site correction, and identify existing Z₂ instance. Keep normality failure of generic identity tensor explicit.

### GX4: Verify right-zipper projector obstruction
Source: 2243–2287. Existing owner: [#8054](https://github.com/LionSR/TNLean/issues/8054). Dependencies: existing main ingredients only.
For existing corrected PBC tensors define P_g,h, prove idempotence, modified right-zipper/exact-factorization identity and PBC closure support, and provide a nontrivial witness disproving unprojected right zipper. Existing left zipper/reduction theorem is reusable.

### EX1: Complete cyclic-two phase examples
Source: 1819–1843. Existing owner: [#7332](https://github.com/LionSR/TNLean/issues/7332), [#8050](https://github.com/LionSR/TNLean/issues/8050). Dependencies: GC1, PH7.
Assemble trivial/nontrivial Z₂ phase counts and normalized L signs; finish degree-three U(1) comparison if claiming the printed coefficient group. Separate Hamiltonian commutation from parameter-range spectral phase proofs, citing or formalizing the external model theorem.

### EX2: Complete Klein coefficient phase table
Source: 1845–1888. Existing owner: [#8051](https://github.com/LionSR/TNLean/issues/8051). Dependencies: GC1.
Reuse complete C× H³ table, prove degree-three U(1) comparison and required stabilizer H² counts, then exact phase counts. Reuse existing (1,1,1) free-action regular phase. Do not omit H_e fully broken phase in anomalous rows.

### EX3: Identify printed Klein anomaly
Source: 1884–1886. Existing owner: [#8480](https://github.com/LionSR/TNLean/issues/8480), [#8051](https://github.com/LionSR/TNLean/issues/8051). Dependencies: existing main ingredients only.
Compute a,b cyclic signs +1 for printedFamily, combine existing ab=−1 with Klein completeness to class (0,0,1), and derive the two source L relations from actual block action. Keep condensation/four-level realizations distinct.

### EX4: Complete categorical example lists
Source: 1890–1987. Existing owner: [#8348](https://github.com/LionSR/TNLean/issues/8348), [#8045](https://github.com/LionSR/TNLean/issues/8045). Dependencies: FL3.
Derive NIM-rep duality from the module-category structure, prove indecomposable rank bounds/classification, supply cited F/6j and L/TY restrictions, and establish categorifiability/exhaustiveness. Preserve corrected Rep(S₃)/Z₃ table. Bare NIM-rep axioms admit extra examples.

### EX5: Classify arbitrary-rank Fibonacci modules
Source: 1991–1993. Existing owner: [#8053](https://github.com/LionSR/TNLean/issues/8053). Dependencies: FL3.
Prove every nonnegative integral M with M²=I+M decomposes into regular 2×2 blocks, then indecomposable uniqueness and actual L=F up to gauge. Existing rank≤2 result is only the terminal finite-size step. SCC/Perron trace argument in gap note is a concrete route.

### Recommended sequencing and ownership
1. Finish AB1, then AB2 and AB3. These determine the faithful common algebra and prevent the rest from drifting into a conditional model.
2. In parallel, finish concrete EX3, GX4 and the arbitrary-rank algebra part of EX5 using existing scalar/contraction APIs; finish PB1/PB3 only with the other MPU owner.
3. Build FL1–FL3, then TR2 and categorical example realization; GC1 consumes the already merged scalar torsor rather than reimplementing it.
4. Split #8050 immediately into PH0–PH7. Advance genuine path/gap/symmetrization dependencies in parallel; do not wait for a monolithic final theorem to discover endpoint or WHA gaps.
5. Complete GX1–GX3 and EX1–EX5 with explicit distinction between table consistency, symbol realization, and physical phase completeness.
6. PEPS is an interface dependency only. The other dot owns PEPS and MPU gauging; this plan does not authorize edits to their work.

## Claim-by-claim source inventory

Module paths are relative to the repository. Names below are exact existing declarations when marked as such. A related module reference is explicitly labelled and carries no coverage claim. Blueprint owner labels are discovered from exact declaration tags; untagged narrative cross-references are discussed after the inventory.

### B01. MPS tensor, arbitrary and periodic boundaries, and S_A^n
Source: `304–315`; `MPSssubs`. Kind: definitions. Status: **merged**.
- Lean: `MPSTensor.groundSpaceMap` in `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
- Lean: `MPSTensor.groundSpace` in `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
- Lean: `MPSTensor.mpv` in `TNLean/MPS/Defs.lean`
- Blueprint: `def:ground_space_map` in `blueprint/src/chapter/ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex:19` (`leanok`)
- Blueprint: `def:ground_space_parent` in `blueprint/src/chapter/ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex:215` (`leanok`)
- Blueprint: `def:mpv` in `blueprint/src/chapter/ch02_mps.tex:133` (`leanok`)
- Boundary: The source trace tr(X A^w) equals groundSpaceMap via trace cyclicity. Do not duplicate these definitions.

### B02. Boundary dimension, block-injective normal form, finite blocking and asymptotic block separation
Source: `312–317`; `MPSssubs`. Kind: background claims. Status: **restricted**.
- Lean: `MPSTensor.groundSpace` in `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
- Lean: `MPSTensor.IsBNT` in `TNLean/MPS/BNT/Basic.lean`
- Blueprint: `def:ground_space_parent` in `blueprint/src/chapter/ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex:215` (`leanok`)
- Blueprint: `def:bnt` in `blueprint/src/chapter/ch10_bnt_definitions_and_characterization.tex:3` (`leanok`)
- Boundary: Shared foundational background; the exact packaged implication from the paper’s direct-sum standing assumptions to all hypotheses used here must be stated. “Any MPS becomes injective after blocking” is not literal without periodic/block qualifications; use existing canonical/periodic APIs. This is not GLM23-specific coverage credit.

### B03. Gapped frustration-free parent; PBC block-count and OBC sum-of-squared-bonds degeneracy; GHZ spin-flip example
Source: `319`; unlabelled. Kind: background theorem and example. Status: **restricted**.
- Lean: `MPSTensor.parentInteraction` in `TNLean/MPS/ParentHamiltonian/Defs.lean`
- Lean: `MPSTensor.groundSpace` in `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
- Blueprint: `def:parent_interaction` in `blueprint/src/chapter/ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex:3188` (`leanok`)
- Blueprint: `def:ground_space_parent` in `blueprint/src/chapter/ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex:215` (`leanok`)
- Issue: [#190](https://github.com/LionSR/TNLean/issues/190) (not verified in this inventory)
- Boundary: Reuse parent-Hamiltonian and GHZ developments; source shorthand suppresses sufficient chain/block lengths. No blanket GLM23 theorem established by these references.
- Next leaf: PH1

### B04. MPO with arbitrary boundary and distinct injective blocks
Source: `321–323`; unlabelled. Kind: definition. Status: **merged**.
- Lean: `MPOTensor.mpoWithBoundary` in `TNLean/MPS/MPDO/Boundary.lean`
- Lean: `MPOTensor.mpoWithBoundary_one` in `TNLean/MPS/MPDO/Boundary.lean`
- Blueprint: `def:mpdo_commuting_boundary` in `blueprint/src/chapter/ch20_mpdo_symmetry.tex:10` (`leanok`)
- Boundary: Definition permits all boundaries even though Boundary.lean also studies commuting boundaries.

### A01. Length-independent arbitrary-boundary closedness: for X,Y there is one Z working for every n (algcond)
Source: `325–358`; `algcond`. Kind: definition. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Keep quantifier order ∀X,Y ∃Z ∀n; pointwise closure with Z depending on n is strictly weaker. Periodic IsMPOFusionAlgebra is not this definition.
- Next leaf: AB1

### A02. Closedness produces exact fusion tensors, natural-number multiplicities and letterwise reconstruction (fusiontensors)
Source: `361–381`; `fusiontensors`. Kind: existence theorem. Status: **restricted**.
- Lean: `MPOTensor.exists_fusionTensors_of_mpo_mul_eq_sum` in `TNLean/MPS/Symmetry/MPOSymmetry/FusionTensors.lean`
- Lean: `MPOTensor.CompleteZipperFusionFamily.ofCompression` in `TNLean/MPS/MPDO/CompleteZipperFusionOfCompression.lean`
- Blueprint: `cor:asym_fusion_action_multiplicity` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:247` (`leanok`)
- Blueprint: `thm:mpdo_complete_zipper_of_compression` in `blueprint/src/chapter/ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex:182` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Merged periodic compression has nilpotent remainder. Exact reconstruction requires proving remainder=0 from source closedness; supplied zero remainder or star closure is insufficient.
- Next leaf: AB2

### A03. Fusion tensors are biorthogonal; multiplicities count independent channels (eq:orthoW)
Source: `361–391`; `fusiontensors`, `eq:orthoW`. Kind: orthogonality theorem. Status: **restricted**.
- Lean: `MPSTensor.exists_multiplicityReductions_of_isNormal` in `TNLean/MPS/Symmetry/MPOSymmetry/FusionTensors.lean`
- Lean: `MPOTensor.CompleteZipperFusionFamily` in `TNLean/MPS/MPDO/CompleteZipperFusionDefs.lean`
- Blueprint: `thm:asym_multiplicity_reductions` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:221` (`leanok`)
- Blueprint: `def:mpdo_complete_zipper_fusion_family` in `blueprint/src/chapter/ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex:1` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Biorthogonality of periodic reductions is merged; the source’s exact construction from arbitrary boundaries is missing.
- Next leaf: AB2

### A04. Periodic operators obey O_a O_b = sum_c N_ab^c O_c
Source: `361`; unlabelled. Kind: consequence. Status: **restricted**.
- Lean: `MPOTensor.IsMPOFusionAlgebra` in `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`
- Lean: `MPOTensor.mpo_mul_eq_sum_of_multiBlockCompression` in `TNLean/MPS/FundamentalTheorem/Reduction/CompressionPeriodic.lean`
- Blueprint: `def:mpo_fusion_algebra` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:293` (`leanok`)
- Blueprint: `cor:asym_compression_periodic` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:188` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: The periodic predicate and compression⇒periodic theorem exist; source closedness⇒the canonical integer coefficients remains dependent on AB2.
- Next leaf: AB2

### F01. Associativity gives invertible multiplicity F change-of-basis (Fsymbolsdef)
Source: `392–409`; `Fsymbolsdef`. Kind: definition and existence. Status: **conditional**.
- Lean: `MPOTensor.CompleteZipperFusionFamily.printedFMatrix` in `TNLean/MPS/MPDO/CompleteZipperFusion.lean`
- Lean: `MPOTensor.CompleteZipperFusionFamily.rightTripleSynthesis_mul_printedFMatrix` in `TNLean/MPS/MPDO/CompleteZipperFusion.lean`
- Lean: `MPOTensor.CompleteZipperFusionFamily.printedFMatrix_mul_inversePrintedFMatrix` in `TNLean/MPS/MPDO/CompleteZipperFusionInverse.lean`
- Blueprint: `thm:mpdo_complete_zipper_printed_fmove` in `blueprint/src/chapter/ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex:347` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Complete-zipper hypotheses and simultaneous left inverse are supplied. This is valid reusable conditional F theory, not closedness⇒F. Orientation is source-specific: printed F and its inverse must not be conflated.
- Next leaf: AB2

### F02. Multiplicity F pentagon (pentagon0F)
Source: `410–414`; `pentagon0F`. Kind: theorem. Status: **conditional**.
- Lean: `MPOTensor.CompleteZipperFusionFamily.inversePrintedFMatrix_pentagon` in `TNLean/MPS/MPDO/CompleteZipperFusionPentagon.lean`
- Blueprint: `thm:mpdo_complete_zipper_fusion_pentagon` in `blueprint/src/chapter/ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex:634` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Merged pentagon for complete zipper families; source-faithful constructor missing.
- Next leaf: AB2

### F03. Fusion GL-multiplicity gauge, F covariance, quotient by gauge
Source: `416–424`; unlabelled. Kind: gauge theorem and equivalence. Status: **conditional**.
- Lean: `MPOTensor.CompleteZipperFusionFamily.regauge_fusionTensor` in `TNLean/MPS/MPDO/CompleteZipperFusionGauge.lean`
- Lean: `MPOTensor.CompleteZipperFusionFamily.printedFMatrix_regauge` in `TNLean/MPS/MPDO/CompleteZipperFusionGauge.lean`
- Lean: `MPOTensor.CompleteZipperFusionFamily.inversePrintedFMatrix_regauge` in `TNLean/MPS/MPDO/CompleteZipperFusionGauge.lean`
- Lean: `MPOTensor.exists_unique_zipperFusionGauge` in `TNLean/MPS/Symmetry/MPOSymmetry/ZipperUniqueness.lean`
- Blueprint: `thm:mpdo_complete_zipper_fmatrix_gauge` in `blueprint/src/chapter/ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex:447` (`leanok`)
- Blueprint: `cor:asym_zipper_fusion_uniqueness` in `blueprint/src/chapter/ch25_asymmetric_ft_splitting.tex:273` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open), [#8088](https://github.com/LionSR/TNLean/issues/8088) (closed)
- Boundary: Row convention repaired in audit 2026-09-29; raw periodic multi-target compression does not have this uniqueness. An equivalence class object/classification still needs the multiplicity-symbol layer.
- Next leaf: FL1

### F04. Finite injective blocks plus closedness suffice for F pentagon, without unit, duality or pivotal assumptions
Source: `426`; unlabelled. Kind: scope claim. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Do not replace the paper’s §2–3 theorem by a fusion-category/WHA or star-closed specialization.
- Next leaf: AB2

### A05. Arbitrary-boundary MPO-symmetric MPS, one output boundary independent of n (eq:compatible)
Source: `431–458`; `eq:compatible`. Kind: definition. Status: **missing**.
- Lean: `MPOTensor.IsMPOSymmetricFamily` in `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`
- Lean: `MPSTensor.groundSpaceMap` in `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
- Blueprint: `def:mpo_symmetric_family` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:595` (`leanok`)
- Blueprint: `def:ground_space_map` in `blueprint/src/chapter/ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex:19` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: IsMPOSymmetricFamily is only the periodic consequence. Use ∀B,X ∃Y ∀n, not merely finite-length subspace invariance.
- Next leaf: AB1

### A06. Arbitrary-boundary invariance produces exact multiplicity action tensors (fusiontensors2)
Source: `459–480`; `fusiontensors2`. Kind: existence theorem. Status: **restricted**.
- Lean: `MPOTensor.exists_actionTensors_of_mpo_mulVec_eq_sum` in `TNLean/MPS/Symmetry/MPOSymmetry/FusionTensors.lean`
- Lean: `MPOTensor.actTensor` in `TNLean/MPS/MPDO/ActionTensor.lean`
- Lean: `MPSTensor.IsReduction.actTensor_idKron` in `TNLean/MPS/MPDO/ActionTensorReduction.lean`
- Blueprint: `cor:asym_fusion_action_multiplicity` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:247` (`leanok`)
- Blueprint: `def:mpug_action_tensor` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4608` (`leanok`)
- Blueprint: `thm:mpug_action_tensor_reductions` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4684` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Merged periodic reductions do not eliminate their remainder or construct the exact action decomposition.
- Next leaf: AB3

### A07. Biorthogonal action tensors (eq:orthoV)
Source: `481–490`; `eq:orthoV`. Kind: orthogonality theorem. Status: **restricted**.
- Lean: `MPOTensor.exists_actionTensors_of_mpo_mulVec_eq_sum` in `TNLean/MPS/Symmetry/MPOSymmetry/FusionTensors.lean`
- Lean: `MPOTensor.exists_unique_zipperActionGauge` in `TNLean/MPS/Symmetry/MPOSymmetry/ZipperUniqueness.lean`
- Blueprint: `cor:asym_fusion_action_multiplicity` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:247` (`leanok`)
- Blueprint: `cor:asym_zipper_action_uniqueness` in `blueprint/src/chapter/ch25_asymmetric_ft_splitting.tex:297` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Same distinction between periodic reduction and source exact action.
- Next leaf: AB3

### L01. Two action trees, invertible multiplicity L-symbol comparison, and contraction formula (rawrels, eq:F_symbol2, 1Fsymbol)
Source: `491–550`; `rawrels`, `eq:F_symbol2`, `1Fsymbol`. Kind: definition and existence. Status: **missing**.
- Lean: `MPOTensor.actTensor_mulTensor` in `TNLean/MPS/MPDO/ActionTensorReduction.lean`
- Blueprint: `thm:mpug_action_tensor_reductions` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4684` (`leanok`)
- Issue: [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Scalar group L-symbols are not an implementation of multiplicity L-symbols. The word “non-zero constants” must mean invertible change of basis, not every matrix entry nonzero.
- Next leaf: FL1

### L02. Full coupled pentagon with all channel indices (coupledpent)
Source: `552–562`; `coupledpent`. Kind: theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Do not assume a coupled-pentagon field and label it derived from tensors.
- Next leaf: FL2

### L03. NIM-rep associativity identity for M and N
Source: `564–565`; unlabelled. Kind: theorem. Status: **merged**.
- Lean: `MPOTensor.sum_fusion_mul_eq_sum_mul_of_isMPOSymmetricFamily` in `TNLean/MPS/Symmetry/MPOSymmetry/NIMRep.lean`
- Lean: `MPOTensor.exists_isNIMRep_of_isMPOSymmetricFamily` in `TNLean/MPS/Symmetry/MPOSymmetry/NIMRep.lean`
- Blueprint: `thm:mpo_symmetric_nimrep` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:828` (`leanok`)
- Boundary: Proved from weaker periodic data plus normal blocks and a faithful block-independence hypothesis. Source arbitrary-boundary bridge still A05/A06.

### L04. Periodic action O_a ψ_x = sum_y M_ax^y ψ_y
Source: `567–591`; unlabelled. Kind: consequence. Status: **restricted**.
- Lean: `MPOTensor.IsMPOSymmetricFamily` in `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`
- Lean: `MPOTensor.mpo_mulVec_mpv_eq_sum_of_multiBlockCompression` in `TNLean/MPS/FundamentalTheorem/Reduction/CompressionPeriodic.lean`
- Blueprint: `def:mpo_symmetric_family` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:595` (`leanok`)
- Blueprint: `cor:asym_compression_periodic` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:188` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Existing predicate alone does not derive this from arbitrary-boundary symmetry.
- Next leaf: AB3

### L05. Action GL-multiplicity gauges and joint F/L covariance; quotient of coupled-pentagon solutions
Source: `593–602`; unlabelled. Kind: gauge and classification definition. Status: **missing**.
- Lean: `MPOTensor.exists_unique_zipperActionGauge` in `TNLean/MPS/Symmetry/MPOSymmetry/ZipperUniqueness.lean`
- Blueprint: `cor:asym_zipper_action_uniqueness` in `blueprint/src/chapter/ch25_asymmetric_ft_splitting.tex:297` (`leanok`)
- Issue: [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Uniqueness for supplied exact zipper decompositions exists; full L covariance/equivalence construction missing.
- Next leaf: FL2

### L06. Regular module M=N with L=F, as many state as operator blocks; maximal degeneracy claim
Source: `604`; unlabelled. Kind: existence example. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8045](https://github.com/LionSR/TNLean/issues/8045) (open), [#8053](https://github.com/LionSR/TNLean/issues/8053) (open)
- Boundary: Needs actual action/module data and coherent L, not only NIMRep N N. “Maximally degenerate” needs indecomposable scope; arbitrary direct sums are not excluded by bare NIM-rep axioms.
- Next leaf: FL3

### O01. Single injective block with every action multiplicity one forces F gauge-trivial via λ
Source: `607–634`; `nonuniqueGS`. Kind: no-go theorem. Status: **restricted**.
- Lean: `MPOTensor.GroupFamily.IsNormalRepresentation.isTrivialGaugeClass_omega_of_invariant` in `TNLean/MPS/Symmetry/MPOSymmetry/AnomalyObstruction.lean`
- Lean: `MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter` in `TNLean/MPS/Symmetry/MPOSymmetry/Character.lean`
- Blueprint: `thm:mpug_anomaly_obstruction` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4948` (`leanok`)
- Blueprint: `cor:mpo_symmetric_no_go` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:879` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Group scalar cohomological case merged; fusion-ring obstruction is different; general multiplicity F obstruction not yet implemented. Retain M_ax^x=1.
- Next leaf: FL3

### O02. Nontrivial MPO algebra excludes unique gapped MPS ground state without action multiplicity
Source: `636`; unlabelled. Kind: physical consequence. Status: **restricted**.
- Lean: `MPOTensor.GroupFamily.IsNormalRepresentation.not_exists_invariant_of_not_isTrivialGaugeClass` in `TNLean/MPS/Symmetry/MPOSymmetry/AnomalyObstruction.lean`
- Blueprint: `thm:mpug_anomaly_obstruction` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4948` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open), [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Needs general O01 and faithful bridge between ground-space degeneracy, normal blocks, and symmetry.
- Next leaf: PH7

### G01. Group labels, exact group fusion, projector identity O_e and representation on its range
Source: `638–660`; `groupcase`, `fusiontensorG`. Kind: specialization and consequence. Status: **restricted**.
- Lean: `MPOTensor.GroupFamily.isMPOFusionAlgebra` in `TNLean/MPS/Symmetry/MPOSymmetry/GroupFusion.lean`
- Lean: `MPOTensor.GroupFamily.FusionData.IsClosed` in `TNLean/MPS/Symmetry/MPOSymmetry/ClosedFusion.lean`
- Blueprint: `thm:mpug_group_fusion_rules` in `blueprint/src/chapter/ch29_mpu_gauging.tex:188` (`leanok`)
- Blueprint: `thm:mposym_closed_fusion_onsite` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:195` (`leanok`)
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open), [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: General operator multiplicativity is present; arbitrary-boundary projector representation and exact source construction remain separate. Do not force O_e=identity outside §4.4.
- Next leaf: GX1

### G02. Group F=ω, three-cocycle condition, coboundary gauge and H³ class
Source: `662–681`; `3cocygroup`. Kind: definition and theorem. Status: **merged, restricted**.
- Lean: `MPOTensor.GroupFamily.FusionData.omega` in `TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`
- Lean: `MPOTensor.GroupFamily.FusionData.isCocycle_omega` in `TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`
- Lean: `MPOTensor.GroupFamily.FusionData.omega_eq_fusionGauge` in `TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`
- Lean: `MPOTensor.GroupFamily.IsNormalRepresentation.anomalyClass` in `TNLean/MPS/Symmetry/MPOSymmetry/AssociatorCohomology.lean`
- Lean: `TNLean.Algebra.ScalarThreeCochain.anomalyClass` in `TNLean/Algebra/ScalarThreeCocycleGroupCohomology.lean`
- Blueprint: `def:mpug_anomaly_three_cochain` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4357` (`leanok`)
- Blueprint: `thm:mpug_anomaly_three_cocycle` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4492` (`leanok`)
- Blueprint: `thm:mpug_anomaly_three_cocycle_gauge` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4542` (`leanok`)
- Blueprint: `def:mpug_anomaly_class` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4574` (`leanok`)
- Blueprint: `def:mpug_h3_group_cohomology` in `blueprint/src/chapter/ch29_mpu_gauging.tex:7499` (`leanok`)
- Boundary: Construction uses boundary-dressed comparison valid for normal periodic representations; source exact case needs the AB bridge. Mathlib cohomology comparison already exists; #8319 tracks migration, not absence.

### G03. Nonnegative integer group action with identity is a permutation action on blocks
Source: `683–702`; `MPOsymG`. Kind: theorem and definition. Status: **merged**.
- Lean: `MPOTensor.exists_equiv_mpo_mulVec_eq_of_isInvertibleLabel` in `TNLean/MPS/Symmetry/MPOSymmetry/Character.lean`
- Lean: `MPOTensor.exists_isNIMRep_of_isMPOSymmetricFamily` in `TNLean/MPS/Symmetry/MPOSymmetry/NIMRep.lean`
- Blueprint: `thm:mpo_invertible_labels` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:898` (`leanok`)
- Blueprint: `thm:mpo_symmetric_nimrep` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:828` (`leanok`)
- Boundary: Group action law/coherence must be retained when assembling chosen label permutations, not just existence of independent equivalences.

### G04. Scalar L from action/fusion tensors and pentagongroups compatibility
Source: `703–719`; `F1group`, `pentagongroups`. Kind: definition and theorem. Status: **merged, restricted**.
- Lean: `MPOTensor.GroupFamily.BlockActionData.lSymbol` in `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`
- Lean: `MPOTensor.GroupFamily.BlockActionData.isCompatible_lSymbol` in `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`
- Lean: `TNLean.Algebra.LSymbol.IsCompatible` in `TNLean/Algebra/LSymbol.lean`
- Blueprint: `def:mpug_permuted_block_l_symbol` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4986` (`leanok`)
- Blueprint: `thm:mpug_permuted_block_l_compatibility` in `blueprint/src/chapter/ch29_mpu_gauging.tex:5039` (`leanok`)
- Blueprint: `def:mpug_l_symbols` in `blueprint/src/chapter/ch29_mpu_gauging.tex:7790` (`leanok`)
- Boundary: Merged scalar construction is boundary-dressed. Full exact GLM23 symbols require AB3; multiplicity generalization remains L01/L02.

### G05. Reciprocal scalar action/fusion gauges induce gdgroup
Source: `720–726`; `gdgroup`. Kind: gauge theorem. Status: **restricted**.
- Lean: `TNLean.Algebra.LSymbol.gauge` in `TNLean/Algebra/LSymbol.lean`
- Lean: `TNLean.Algebra.LSymbol.IsCompatible.gauge` in `TNLean/Algebra/LSymbol.lean`
- Lean: `MPOTensor.GroupFamily.FusionData.omega_eq_fusionGauge` in `TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`
- Blueprint: `def:mpug_l_gauge` in `blueprint/src/chapter/ch29_mpu_gauging.tex:7812` (`leanok`)
- Blueprint: `thm:mpug_l_gauge_preservation` in `blueprint/src/chapter/ch29_mpu_gauging.tex:7922` (`leanok`)
- Blueprint: `thm:mpug_anomaly_three_cocycle_gauge` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4542` (`leanok`)
- Issue: [#7331](https://github.com/LionSR/TNLean/issues/7331) (open)
- Boundary: Scalar gauge algebra and tensor-derived ω gauge are merged. Tensor-derived L gauge law/exhaustiveness for arbitrary choices is not supplied by scalar compatibility; coordinate with owner of #7331. Library convention is reciprocal to GLM23.
- Next leaf: PB3

### G06. Normalize all identity-component L symbols by action gauge
Source: `728`; unlabelled. Kind: normalization theorem. Status: **merged**.
- Lean: `TNLean.Algebra.LSymbol.IsCompatible.isNormalized_gauge` in `TNLean/Algebra/LSymbol.lean`
- Lean: `TNLean.Algebra.LSymbol.IsCompatible.apply_right_one` in `TNLean/Algebra/LSymbol.lean`
- Lean: `TNLean.Algebra.LSymbol.IsCompatible.apply_left_one` in `TNLean/Algebra/LSymbol.lean`
- Blueprint: `thm:asymex_l_symbol_normalization` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1257` (`leanok`)
- Blueprint: `thm:mpug_block_factorization` in `blueprint/src/chapter/ch29_mpu_gauging.tex:8677` (`leanok`)
- Blueprint: `thm:mpug_relative_block_character` in `blueprint/src/chapter/ch29_mpu_gauging.tex:8718` (`leanok`)
- Boundary: Normalized anomaly hypothesis is explicit where needed, with scalar normalization API available.

### G07. Transitive action, stabilizer H, orbit G/H, basepoint conjugacy, anomaly-protected lower degeneracy
Source: `734–738`; unlabelled. Kind: classification and degeneracy. Status: **restricted**.
- Lean: `TNLean.Algebra.StabilizerRepresentatives.h2EquivSolutionClasses` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Lean: `TNLean.Algebra.LSymbol.isTrivialGaugeClass_comap_of_isCompatible` in `TNLean/Algebra/ScalarThreeCocycleCyclicInvariant.lean`
- Blueprint: `thm:mpug_stabilizer_torsor` in `blueprint/src/chapter/ch29_mpu_gauging.tex:9207` (`leanok`)
- Blueprint: `thm:mpug_fixed_block_trivializes` in `blueprint/src/chapter/ch29_mpu_gauging.tex:8154` (`leanok`)
- Issue: [#7332](https://github.com/LionSR/TNLean/issues/7332) (open)
- Boundary: Fixed transitive G-set scalar classification exists. Assemble classification across actions/subgroup conjugacy, exact degeneracy and robustness argument; do not assume H normal. Use Mathlib orbitEquivQuotientStabilizer.
- Next leaf: GC1

### G08. Restriction to stabilizer trivializes ω; after fusion gauge ψ=L/β is a 2-cocycle modulo action gauge
Source: `740–749`; unlabelled. Kind: theorem. Status: **merged**.
- Lean: `TNLean.Algebra.LSymbol.isTrivialGaugeClass_comap_of_isCompatible` in `TNLean/Algebra/ScalarThreeCocycleCyclicInvariant.lean`
- Lean: `TNLean.Algebra.LSymbol.IsCompatible.isCocycle_restrict` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Lean: `TNLean.Algebra.ScalarThreeCochain.exists_fusionGauge_eq_one_of_isTrivialGaugeClass_comap` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Blueprint: `thm:mpug_fixed_block_trivializes` in `blueprint/src/chapter/ch29_mpu_gauging.tex:8154` (`leanok`)
- Blueprint: `thm:mpug_stabilizer_torsor` in `blueprint/src/chapter/ch29_mpu_gauging.tex:9207` (`leanok`)
- Blueprint: `thm:mpug_stabilizer_reconstruction` in `blueprint/src/chapter/ch29_mpu_gauging.tex:9138` (`leanok`)
- Boundary: Already merged; source statement concerns stabilizer of one block, not kernel of the full action.

### G09. Coset transition elements and Eq. (20) Lexpre reconstruct all L entries
Source: `752–759`; `Lexpre`. Kind: reconstruction theorem. Status: **corrected-source**.
- Lean: `TNLean.Algebra.StabilizerRepresentatives.reconstructedLSymbol` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Lean: `TNLean.Algebra.StabilizerRepresentatives.reconstructedLSymbol_isCompatible` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Lean: `TNLean.Algebra.StabilizerRepresentatives.exists_actionGauge_gauge_eq_reconstructedLSymbol` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Blueprint: `thm:mpug_stabilizer_reconstruction` in `blueprint/src/chapter/ch29_mpu_gauging.tex:9138` (`leanok`)
- Blueprint: `thm:mpug_stabilizer_torsor` in `blueprint/src/chapter/ch29_mpu_gauging.tex:9207` (`leanok`)
- Issue: [#8046](https://github.com/LionSR/TNLean/issues/8046) (closed)
- Boundary: Merged correction glm23_eq20_fusion_gauge: printed formula first in a fusion gauge trivial on H, then transport back. Merely ω|H=dβ is insufficient for the uncorrected formula.

### G10. For fixed fusion gauge, action-gauge solution classes form an H²(H,C×) torsor
Source: `761`; unlabelled. Kind: torsor theorem. Status: **merged**.
- Lean: `TNLean.Algebra.StabilizerRepresentatives.solutionSetoid` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Lean: `TNLean.Algebra.StabilizerRepresentatives.solutionAddAction` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Lean: `TNLean.Algebra.StabilizerRepresentatives.h2EquivSolutionClasses` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Lean: `TNLean.Algebra.StabilizerRepresentatives.existsUnique_vadd_eq` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Blueprint: `thm:mpug_stabilizer_torsor` in `blueprint/src/chapter/ch29_mpu_gauging.tex:9207` (`leanok`)
- Issue: [#8046](https://github.com/LionSR/TNLean/issues/8046) (closed)
- Boundary: Fixed fusion gauge matters: quotienting also by all fusion cocycles changes the classification. Uses Mathlib H², not just a raw cocycle set.

### G11. gxdecomp: factor virtual action through coset representatives and internal stabilizer action; inverse action-tensor identity
Source: `763–814`; `gxdecomp`. Kind: tensor decomposition theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#7332](https://github.com/LionSR/TNLean/issues/7332) (open)
- Boundary: Scalar transition/reconstruction is not a proof of the displayed tensor factorization. This is a separate leaf, reusable by induced-representation interpretation.
- Next leaf: GC2

### G12. odot product, projective law intactens, ω-associativity nonasso, global linearity vs boundary associator
Source: `816–836`; `defodot`, `intactens`, `nonasso`. Kind: definition and theorems. Status: **missing**.
- Lean: `MPOTensor.GroupFamily.BlockActionData.isCompatible_lSymbol` in `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`
- Blueprint: `thm:mpug_permuted_block_l_compatibility` in `blueprint/src/chapter/ch29_mpu_gauging.tex:5039` (`leanok`)
- Issue: [#7332](https://github.com/LionSR/TNLean/issues/7332) (open)
- Boundary: Dressed scalar compatibility supplies an ingredient, not the source’s defined tensor product and its laws. Stabilizer statement must use the stabilizer of the chosen block, not fixed H on arbitrary x.
- Next leaf: GC2

### G13. On-site F trivial; virtual projective representation; singleton classes H²(G,U(1))
Source: `840–856`; `Lgroupdef`, `coupengroup`. Kind: on-site specialization. Status: **restricted**.
- Lean: `TNLean.Algebra.StabilizerRepresentatives.inducedLSymbol_isCompatible` in `TNLean/Algebra/StabilizerCocycleLSymbol.lean`
- Lean: `MPSTensor.cohomologousTo_of_isInjective` in `TNLean/MPS/Symmetry/CocycleCoboundary.lean`
- Blueprint: `thm:mpug_stabilizer_cocycle_l_symbol` in `blueprint/src/chapter/ch29_mpu_gauging.tex:8986` (`leanok`)
- Blueprint: `thm:cocycle_gauge_independence` in `blueprint/src/chapter/ch12_symmetry_virtual_and_cohomology.tex:517` (`leanok`)
- Issue: [#7332](https://github.com/LionSR/TNLean/issues/7332) (open)
- Boundary: Extensive on-site symmetry/SPT library exists, but exact GLM23 reduction theorem and coefficient comparison should be assembled instead of relabelling fixed-point-only results.
- Next leaf: GC1

### G14. Recover induced-representation classification for degenerate on-site ground spaces
Source: `858–863`; unlabelled. Kind: on-site multiblock theorem. Status: **restricted**.
- Lean: `TNLean.Algebra.StabilizerRepresentatives.inducedLSymbol_isCompatible` in `TNLean/Algebra/StabilizerCocycleLSymbol.lean`
- Lean: `TNLean.Algebra.StabilizerRepresentatives.exists_actionGauge_eq_inducedLSymbol` in `TNLean/Algebra/StabilizerCocycleReconstruction.lean`
- Blueprint: `thm:mpug_stabilizer_cocycle_l_symbol` in `blueprint/src/chapter/ch29_mpu_gauging.tex:8986` (`leanok`)
- Blueprint: `thm:mpug_stabilizer_torsor` in `blueprint/src/chapter/ch29_mpu_gauging.tex:9207` (`leanok`)
- Issue: [#7332](https://github.com/LionSR/TNLean/issues/7332) (open), [#7360](https://github.com/LionSR/TNLean/issues/7360) (open)
- Boundary: Scalar fixed-action result is merged; tensor/physical induced representation and across-action classification remain separate.
- Next leaf: GC1

### T01. Block-preserving antiunitary TRS, signs S_x conjugate(S_x)=±I; commuting MPO gives q_g
Source: `865–871`; `sec:TRS`. Kind: definitions and tensor theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8048](https://github.com/LionSR/TNLean/issues/8048) (open)
- Boundary: Existing unrelated time-reversal/on-site APIs do not establish this tensor bridge for general MPOs. Preserve source assumption that TRS does not permute blocks.
- Next leaf: TR1

### T02. TRS gives fusion β; anomaly cohomologous to a real cocycle
Source: `872–891`; unlabelled. Kind: tensor-to-scalar theorem. Status: **conditional**.
- Lean: `TNLean.Algebra.ScalarThreeCochain.exists_cohomologousTo_star_eq_self` in `TNLean/Algebra/ScalarThreeCocycleTimeReversal.lean`
- Blueprint: `thm:mpug_time_reversal_real_anomaly` in `blueprint/src/chapter/ch29_mpu_gauging.tex:8024` (`leanok`)
- Issue: [#8048](https://github.com/LionSR/TNLean/issues/8048) (open)
- Boundary: Scalar reality theorem is merged conditional on conjugate anomaly gauge relation. Derive β and this relation from q_g/antiunitary symmetry.
- Next leaf: TR1

### T03. TRS action comparison gives γ and TRSF1group
Source: `894–957`; `TRSF1group`. Kind: tensor-to-scalar theorem. Status: **corrected-source**.
- Lean: `TNLean.Algebra.LSymbol.star_apply_eq_gauge_one_apply` in `TNLean/Algebra/ScalarThreeCocycleTimeReversal.lean`
- Lean: `TNLean.Algebra.LSymbol.phase_sq_eq_of_gauge_eq_star` in `TNLean/Algebra/ScalarThreeCocycleTimeReversal.lean`
- Blueprint: `thm:mpug_time_reversal_l_symbol_relation` in `blueprint/src/chapter/ch29_mpu_gauging.tex:8105` (`leanok`)
- Issue: [#8048](https://github.com/LionSR/TNLean/issues/8048) (open)
- Boundary: Printed |L|² equation is false. Correct ratio conjugate(L)/L, equivalently squared phase gauge-trivial; scalar cancellation merged, tensor β/γ bridge missing. glm23_time_reversal_l_symbol.
- Next leaf: TR1

### T04. General non-group F real and multiplicity L squared gauge-trivial under TRS
Source: `959–991`; unlabelled. Kind: generalization. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8048](https://github.com/LionSR/TNLean/issues/8048) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Do not infer from scalar joint-real theorem. Requires multiplicity TRS tensors and conjugation/gauge convention audit.
- Next leaf: TR2

### P01. Weaker PBC group representation with U_e=I and permuted normal/injective state blocks
Source: `994–998`; `sec:PBC`. Kind: definition. Status: **merged**.
- Lean: `MPOTensor.GroupFamily` in `TNLean/MPS/MPU/GroupRepresentation.lean`
- Lean: `MPOTensor.GroupFamily.IsNormalRepresentation` in `TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`
- Lean: `MPOTensor.GroupFamily.CarriesMPV` in `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`
- Blueprint: `def:mpug_group_representation` in `blueprint/src/chapter/ch29_mpu_gauging.tex:110` (`leanok`)
- Blueprint: `def:mpug_anomaly_three_cochain` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4357` (`leanok`)
- Blueprint: `def:mpug_permuted_block_l_symbol` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4986` (`leanok`)
- Boundary: IsNormalRepresentation permits projector unit; add the separate U_e=I equation when matching §4.4. IsRepresentation additionally carries MPU/simple assumptions and is not the only source-faithful entry point.

### P02. PBC fusion reductions for every interior word, including n=0 orthogonality (fusiontensorG2)
Source: `1001–1026`; `fusiontensorG2`. Kind: existence theorem. Status: **merged**.
- Lean: `MPOTensor.GroupFamily.IsNormalRepresentation.exists_fusionTensors` in `TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`
- Blueprint: `cor:asym_fusion_tensors_group` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:105` (`leanok`)
- Issue: [#7330](https://github.com/LionSR/TNLean/issues/7330) (open)
- Boundary: General normal representation route, not just unitary representations.

### P03. Nilpotent residual tails and anomaly comparison after long words
Source: `1028–1060`; unlabelled. Kind: nilpotence and associator theorem. Status: **merged**.
- Lean: `MPSTensor.IsReduction.isReductionResidualNilpotencyBound_trans` in `TNLean/MPS/Core/ReductionResidualComposition.lean`
- Lean: `MPOTensor.GroupFamily.FusionData.isReductionResidualNilpotencyBound_left` in `TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`
- Lean: `MPOTensor.GroupFamily.FusionData.isCocycle_omega` in `TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`
- Blueprint: `thm:mpoalg_composite_reduction` in `blueprint/src/chapter/ch30_mpo_algebras.tex:451` (`leanok`)
- Blueprint: `thm:mpug_anomaly_three_cocycle` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4492` (`leanok`)
- Boundary: Residual nilpotence does not imply every off-diagonal letter vanishes after the naive blocking. Use proved dressed/exterior length bounds.

### P04. PBC action reduction (mpoMPSsten)
Source: `1062–1090`; `mpoMPSsten`. Kind: existence theorem. Status: **merged**.
- Lean: `MPOTensor.exists_isReduction_actTensor_of_isNormal` in `TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`
- Lean: `MPOTensor.GroupFamily.nonempty_blockActionData` in `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`
- Blueprint: `cor:asym_action_tensors` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:134` (`leanok`)
- Blueprint: `thm:mpug_permuted_block_l_symbol_spec` in `blueprint/src/chapter/ch29_mpu_gauging.tex:5011` (`leanok`)
- Issue: [#7330](https://github.com/LionSR/TNLean/issues/7330) (open)
- Boundary: The target equality is source-faithful; operational common blocking and all exterior identities are separate coordination items.

### P05. Dressed scalar L and coupled pentagon for PBC group action
Source: `1091–1129`; unlabelled. Kind: definition and theorem. Status: **merged**.
- Lean: `MPOTensor.GroupFamily.BlockActionData.lSymbol` in `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`
- Lean: `MPOTensor.GroupFamily.BlockActionData.isCompatible_lSymbol` in `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`
- Blueprint: `def:mpug_permuted_block_l_symbol` in `blueprint/src/chapter/ch29_mpu_gauging.tex:4986` (`leanok`)
- Blueprint: `thm:mpug_permuted_block_l_compatibility` in `blueprint/src/chapter/ch29_mpu_gauging.tex:5039` (`leanok`)
- Issue: [#7331](https://github.com/LionSR/TNLean/issues/7331) (open)
- Boundary: Compatibility is merged; complete tensor-choice gauge invariance remains G05/PB3.

### P06. Exterior-buffer identities oPBCMPO/oPBCMPSs and equivalence to periodic operator/action equality
Source: `1131–1207`; `oPBCMPO`, `oPBCMPSs`. Kind: theorems. Status: **restricted**.
- Lean: `MPSTensor.IsReductionExteriorBufferLength` in `TNLean/MPS/Core/ReductionBlocking.lean`
- Lean: `MPOTensor.mpo_mul_eq_sum_of_multiBlockCompression` in `TNLean/MPS/FundamentalTheorem/Reduction/CompressionPeriodic.lean`
- Blueprint: `def:mps_reduction_exterior_buffer_length` in `blueprint/src/chapter/ch25_asymmetric_ft_reductions.tex:1018` (`leanok`)
- Blueprint: `cor:asym_compression_periodic` in `blueprint/src/chapter/ch25_asymmetric_ft_mpo_coefficients.tex:188` (`leanok`)
- Issue: [#7330](https://github.com/LionSR/TNLean/issues/7330) (open), [#7331](https://github.com/LionSR/TNLean/issues/7331) (open)
- Boundary: Generic reduction/exterior and trace-converse ingredients exist. Package both directions at one justified common finite block, avoiding claims that all residual letters vanish.
- Next leaf: PB1

### P07. Injective group representation with U_e=I and exact closed fusion is on-site; anomaly trivial; anomalous U_e=I excludes arbitrary-boundary closure
Source: `1209–1216`; unlabelled. Kind: unnumbered Lemma and consequence. Status: **restricted**.
- Lean: `MPOTensor.GroupFamily.isOnSite_of_closed_fusion` in `TNLean/MPS/Symmetry/MPOSymmetry/ClosedFusion.lean`
- Lean: `MPOTensor.GroupFamily.bondDim_eq_one_of_closed_fusion` in `TNLean/MPS/Symmetry/MPOSymmetry/ClosedFusion.lean`
- Lean: `MPOTensor.GroupFamily.anomalyClass_eq_zero_of_closed_fusion` in `TNLean/MPS/Symmetry/MPOSymmetry/ClosedFusion.lean`
- Blueprint: `thm:mposym_closed_fusion_onsite` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:195` (`leanok`)
- Issue: [#8047](https://github.com/LionSR/TNLean/issues/8047) (closed), [#8143](https://github.com/LionSR/TNLean/issues/8143) (closed), [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Closed-fusion⇒on-site/triviality merged and faithful. The advertised equivalence with arbitrary-boundary closedness awaits AB2.
- Next leaf: AB2

### C01. MPO-symmetric exact-MPS Hamiltonians are in same symmetric phase iff L classes agree
Source: `1219–1231`; `sec:classif`. Kind: main theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: No full GLM23 capstone in Lean. Algebraic H² classification or on-site/fixed-point path theorem does not settle this.
- Next leaf: PH7

### C02. Physical fusion-category/WHA symmetry; Def. 1 defsym; same F class allows different MPO/WHA representations
Source: `1234–1248`; `sec:fixsym`, `defsym`. Kind: definitions and structural claims. Status: **missing**.
- Lean: `MPOTensor.CompleteZipperFusionFamily.coproduct` in `TNLean/MPS/MPDO/CompleteZipperFusionCoproduct.lean`
- Lean: `MPOTensor.CompleteZipperFusionFamily.coproduct_coassoc` in `TNLean/MPS/MPDO/CompleteZipperFusionCoassoc.lean`
- Blueprint: `thm:mpoalg_fusion_coproduct` in `blueprint/src/chapter/ch30_mpo_algebras.tex:908` (`leanok`)
- Blueprint: `thm:mpoalg_fusion_coproduct_coassoc` in `blueprint/src/chapter/ch30_mpo_algebras.tex:964` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open), [#8315](https://github.com/LionSR/TNLean/issues/8315) (open)
- Boundary: A multiplicative coassociative map is not a C*-WHA or module-category equivalence; require actual unit/counit/antipode/*/integral data and Mathlib reuse.
- Next leaf: PH0

### C03. defphase: common embedding, local continuous uniformly gapped PBC path commuting with fixed direct-sum MPO representation
Source: `1250–1265`; `defphase`. Kind: Definition 2 and scope. Status: **missing**.
- Lean: `MPSTensor.SymmetricGappedInteractionPath` in `TNLean/MPS/Symmetry/GappedInteractionPath.lean`
- Blueprint: `def:spt_common_space_gapped_path` in `blueprint/src/chapter/ch12_symmetry_spt.tex:4904` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Existing path type fixes an on-site group action. Source allows non-on-site comparison, endpoint physical/bond spaces and representation changes via embedding. Do not define phase as L equivalence.
- Next leaf: PH0

### C04. Exact MPS ground spaces with local action tensors throughout interpolation; no claim for paths beyond exact MPS
Source: `1267–1272`; unlabelled. Kind: scope and assumptions. Status: **missing**.
- Lean: `MPSTensor.ExactMPSGroundPath` in `TNLean/MPS/Symmetry/ExactMPSGappedPhase.lean`
- Blueprint: `def:spt_exact_mps_gapped_phase` in `blueprint/src/chapter/ch12_symmetry_spt.tex:4927` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Adapt shared exact-ground-path mechanics, retaining independent physical gap and all source multiblock data. This is source restriction, not an extra formalization assumption.
- Next leaf: PH0

### C05. Parent-Hamiltonian local projector; group average and C*-WHA canonical-left-integral symmetrization; commutation, Hermiticity and nonzero term
Source: `1274–1320`; unlabelled. Kind: symmetrization theorem. Status: **restricted**.
- Lean: `MPSTensor.parentInteractionES_commute_onSiteTensorPow` in `TNLean/MPS/Symmetry/ParentHamiltonianSymmetry.lean`
- Blueprint: `thm:spt_parent_hamiltonian_symmetry` in `blueprint/src/chapter/ch12_symmetry_spt.tex:5062` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: On-site parent symmetry ingredients exist. WHA averaging and Appendix B proof missing; ensure kernel/ground-space preservation and gap bound, not only nonzero trace.
- Next leaf: PH1

### C06. Fixed-representation path embeds into defphase using one-qubit path and O_a⊗I
Source: `1322–1326`; `sec:parentHrestric`. Kind: embedding lemma. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Explicit physical embedding and uniform gap need proof.
- Next leaf: PH2

### C07. A symmetric gapped Hamiltonian with exact MPS ground space is in same phase as symmetric parent via convex interpolation; reduce to parent paths
Source: `1328–1330`; unlabelled. Kind: reduction lemma. Status: **missing**.
- Lean: `Matrix.spectrum_gap_interpolation_of_le` in `TNLean/Algebra/CommonKernelSpectralGap.lean`
- Blueprint: `thm:common_kernel_spectral_gap_interpolation` in `blueprint/src/chapter/ch13_parent_hamiltonian_spectral_gap_continuity.tex:251` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Reuse common-kernel gap inequalities, but must establish the exact shared ground subspace and GLM23 embedding/symmetry.
- Next leaf: PH2

### C08. A simultaneous block-separating left inverse (leftinv)
Source: `1332–1350`; `leftinv`. Kind: left inverse construction. Status: **restricted**.
- Lean: `MPOTensor.exists_blockTensor_isMPOBlockLeftInverse` in `TNLean/MPS/MPDO/CompleteZipperFusionBlocked.lean`
- Blueprint: `thm:mpdo_complete_zipper_of_compression_blocked` in `blueprint/src/chapter/ch21_mpdo_rfp_fusion_isometries_complete_zipper_coherence.tex:229` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: MPO simultaneous inverse after finite blocking is merged. Need MPS analogue/source faithful block-injectivity and continuous choices for paths.
- Next leaf: PH3

### C09. Gapped exact-MPS parent path induces continuous block tensors; locally continuous left inverses and action bases
Source: `1352–1387`; unlabelled. Kind: continuity theorem. Status: **missing**.
- Lean: `MPSTensor.continuous_parentInteraction_matrix_family` in `TNLean/MPS/Symmetry/CanonicalInjectiveGappedPath.lean`
- Blueprint: `thm:spt_canonical_injective_gapped_path` in `blueprint/src/chapter/ch12_symmetry_spt.tex:151` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Forward tensor⇒continuous parent machinery does not prove reverse gapped path⇒continuous canonical/tensor action choices. Source cites SCP11.
- Next leaf: PH3

### C10. Differentiable action-tensor deformation produces infinitesimal gauge variation of L (eq:F_symbol3)
Source: `1388–1551`; `eq:F_symbol3`. Kind: deformation theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Must prove actual finite/local gauge equivalence, not store derivative-gauge conclusion as an input.
- Next leaf: PH4

### C11. Continuous non-differentiable and changing-bond paths; extension to long-word PBC action
Source: `1551–1577`; unlabelled. Kind: extension theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Explicit source includes bond-dimension changes. Fixed dimension or differentiability-only theorem remains restricted.
- Next leaf: PH4

### C12. A(γ)=A W(γ) with mixed matrix units, D=D0+D1 (defAgamma)
Source: `1580–1598`; `defAgamma`. Kind: construction. Status: **missing**.
- Lean: `TNLean/MPS/Symmetry/EmbeddedFixedPointTensor.lean` (related module only)
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Existing fixed-point interpolation is reuse only: endpoints in source need not be fixed points or zero correlation length.
- Next leaf: PH5

### C13. Mixed MPO/action tensors; Agammasym and exact F,L coherence of enlarged representation
Source: `1600–1685`; `Agammasym`. Kind: construction and theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Requires same symbols after genuine gauge alignment, mixed-sector fusion and full tensor identities.
- Next leaf: PH5

### C14. Enlarged MPO injectivity, interior A(γ) injectivity, unique gapped parent
Source: `1687–1691`; unlabelled. Kind: injectivity and gap theorem. Status: **missing**.
- Lean: `MPSTensor.canonicalInjectiveGappedPath` in `TNLean/MPS/Symmetry/CanonicalInjectiveGappedPath.lean`
- Blueprint: `thm:spt_canonical_injective_gapped_path` in `blueprint/src/chapter/ch12_symmetry_spt.tex:151` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: The existing on-site path constructor is not the MPO proof. Interior pointwise gaps do not alone establish a uniform full-path gap.
- Next leaf: PH6

### C15. Continuous extended local supports S′γ, Gram–Schmidt projector limits, endpoint ground states and gaps
Source: `1692`; unlabelled. Kind: endpoint convergence and gap theorem. Status: **missing**.
- Lean: `TNLean/MPS/ParentHamiltonian/CompactParentGap.lean` (related module only)
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open), [#190](https://github.com/LionSR/TNLean/issues/190) (not verified in this inventory)
- Boundary: Must verify the asserted endpoint ground spaces and uniform gap through rank-changing bonds. Merely continuous projectors/interior gap is insufficient.
- Next leaf: PH6

### C16. Degenerate-block path, matching labels/multiplicities, mixed-sector MPO, exact ground-space and full-path gap
Source: `1695–1777`; unlabelled. Kind: multiblock interpolation theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Cannot close capstone with singleton-only interpolation.
- Next leaf: PH7

### C17. MPS boundary of MPO-injective PEPS compatible with virtual symmetry; fusion-module boundary classification
Source: `1782–1793`; `fig:bound`, `sketch`. Kind: boundary interpretation. Status: **restricted**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Record mathematical interface only; PEPS implementation belongs to other dot and must not be duplicated or modified. Exact bulk-boundary theorem not supplied by symmetric-state eigenvector.
- External interface: PEPS-interface (separately owned PEPS implementation; mathematical interface only)

### C18. Positive common NIM-rep eigenvector yields symmetric boundary state (symboundary), spectral radii=FP dimensions
Source: `1795–1805`; `symboundary`. Kind: positive-boundary theorem. Status: **merged**.
- Lean: `MPOTensor.IsNIMRep.exists_pos_left_eigenvector` in `TNLean/MPS/Symmetry/MPOSymmetry/SymmetricBoundary.lean`
- Lean: `MPOTensor.IsNIMRep.spectralRadius_eq_perronFrobeniusDim` in `TNLean/MPS/Symmetry/MPOSymmetry/SymmetricBoundary.lean`
- Lean: `MPOTensor.exists_pos_symmetric_boundary_state` in `TNLean/MPS/Symmetry/MPOSymmetry/SymmetricBoundary.lean`
- Blueprint: `thm:mposym_nimrep_pos_eigenvector` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1221` (`leanok`)
- Blueprint: `thm:mposym_symmetric_boundary_state` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1254` (`leanok`)
- Issue: [#8049](https://github.com/LionSR/TNLean/issues/8049) (closed), [#8142](https://github.com/LionSR/TNLean/issues/8142) (closed)
- Boundary: Proof uses a fusion ring with duality and unital NIM-rep; requires neither commutativity nor indecomposability, contrary to speculative old issue text. Source categorical→ring interface remains C02.

### C19. Group eigenvalue 1; regular action quantum dimension; arbitrary-PBC groups lie outside WHA boundary framework
Source: `1805–1808`; unlabelled. Kind: specializations and scope. Status: **restricted**.
- Lean: `FibonacciCompression.mpo_fibTau_mulVec_boundary` in `TNLean/MPS/Examples/Fibonacci/FibonacciBoundary.lean`
- Lean: `MPOTensor.IsFusionRing.perronFrobeniusDim_pos` in `TNLean/MPS/Symmetry/MPOSymmetry/FusionRing.lean`
- Blueprint: `ex:mposym_fibonacci_boundary_state` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1289` (`leanok`)
- Blueprint: `thm:mposym_fusion_ring_regular` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1188` (`leanok`)
- Issue: [#8049](https://github.com/LionSR/TNLean/issues/8049) (closed)
- Boundary: Fibonacci regular case is explicit. General group/regular-module corollaries and categorical scope should remain visible.
- Next leaf: FL3

### Z01. H³(Z₂,U(1))=Z₂
Source: `1819–1821`; unlabelled. Kind: cohomology classification. Status: **restricted**.
- Lean: `TNLean.Algebra.ScalarThreeCochain.isTrivialGaugeClass_iff_sigma_generator_eq_one` in `TNLean/Algebra/ScalarThreeCocycleCyclicTwo.lean`
- Lean: `TNLean.Algebra.ScalarThreeCochain.nat_card_groupCohomology_three_cyclic` in `TNLean/Algebra/ScalarThreeCocycleCyclicClass.lean`
- Blueprint: `thm:mpug_z2_trivial_scalar_class` in `blueprint/src/chapter/ch29_mpu_gauging.tex:9917` (`leanok`)
- Blueprint: `thm:asymex_group_cocycle_cyclic_classes` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:663` (`leanok`)
- Issue: [#8051](https://github.com/LionSR/TNLean/issues/8051) (open)
- Boundary: Merged C× cocycle classification; exact degree-three circle comparison is not the existing H² comparison.
- Next leaf: EX1

### Z02. Trivial Z₂ anomaly: one- and two-block phases, normalized L equality, transverse-field Ising realization
Source: `1823–1831`; unlabelled. Kind: phase classification and realization. Status: **restricted**.
- Lean: `TNLean.Algebra.LSymbol.IsCompatible.apply_involution` in `TNLean/Algebra/LSymbol.lean`
- Lean: `TNLean.Algebra.LSymbol.actionGaugeEquiv_of_bijective_smul` in `TNLean/Algebra/LSymbolFreeAction.lean`
- Blueprint: `thm:asymex_l_symbol_normalization` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1257` (`leanok`)
- Blueprint: `thm:asymex_free_action_l_symbols` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1196` (`leanok`)
- Issue: [#7332](https://github.com/LionSR/TNLean/issues/7332) (open)
- Boundary: Scalar compatibility ingredients merged. Exhaustive phase count and physical parameter-range/gap realization are not obtained merely by these identities.
- Next leaf: EX1

### Z03. Nontrivial Z₂ anomaly forces two blocks; opposite L signs; regular solution L=ω
Source: `1833–1841`; unlabelled. Kind: phase classification. Status: **restricted**.
- Lean: `CZXCompression.czx_lSymbol_ratio_eq_neg_one` in `TNLean/MPS/Symmetry/MPOSymmetry/CZXPermutedBlocks.lean`
- Lean: `TNLean.Algebra.LSymbol.isCompatible_regular` in `TNLean/Algebra/LSymbolFreeAction.lean`
- Lean: `TNLean.Algebra.ScalarThreeCochain.not_isTrivialGaugeClass_iff_sigma_generator_eq_neg_one` in `TNLean/Algebra/ScalarThreeCocycleCyclicTwo.lean`
- Blueprint: `thm:asymex_czx_product_state_l_symbols` in `blueprint/src/chapter/ch25_asymmetric_examples_czx.tex:843` (`leanok`)
- Blueprint: `thm:asymex_free_action_l_symbols` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1196` (`leanok`)
- Blueprint: `thm:mpug_z2_nontrivial_scalar_class` in `blueprint/src/chapter/ch29_mpu_gauging.tex:10030` (`leanok`)
- Issue: [#7332](https://github.com/LionSR/TNLean/issues/7332) (open)
- Boundary: Regular/free-action scalar gauge uniqueness merged. Bridge to source exhaustive physical phases still missing.
- Next leaf: EX1

### Z04. Roose cluster-like Hamiltonian, decorated CZX symmetry, ordered/translation-broken parameter regions
Source: `1843`; unlabelled. Kind: physical example. Status: **restricted**.
- Lean: `MPOTensor.GroupCocycle.rooseHamiltonian` in `TNLean/MPS/Examples/CZX/ClusterIsingSymmetry.lean`
- Lean: `MPOTensor.GroupCocycle.czxDecorated_mul_rooseHamiltonian` in `TNLean/MPS/Examples/CZX/ClusterIsingSymmetry.lean`
- Blueprint: `def:asymex_group_cocycle_z2_hamiltonians` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:419` (`leanok`)
- Blueprint: `thm:asymex_group_cocycle_z2_hamiltonians` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:435` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Commutation merged. Spectral phase/gap assertions for μ>0 and μ<0 are separate, not inferred from commutation.
- Next leaf: EX1

### K01. Eight Klein three-cocycles, generators and H³(Z₂×Z₂,U(1))=Z₂³
Source: `1845–1848`; unlabelled. Kind: cohomology classification. Status: **restricted**.
- Lean: `TNLean.Algebra.ScalarThreeCochain.kleinCocycleFamily` in `TNLean/Algebra/KleinCocycleTable.lean`
- Lean: `TNLean.Algebra.ScalarThreeCochain.existsUnique_cohomologousTo_kleinCocycleFamily` in `TNLean/Algebra/KleinCocycleCompleteness.lean`
- Lean: `TNLean.Algebra.ScalarThreeCochain.kleinH3Equiv` in `TNLean/Algebra/KleinCocycleCompleteness.lean`
- Blueprint: `def:asymex_klein_cocycle_family` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1088` (`leanok`)
- Blueprint: `thm:asymex_klein_complete_classification` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1522` (`leanok`)
- Issue: [#8051](https://github.com/LionSR/TNLean/issues/8051) (open)
- Boundary: C× classification complete; U(1) comparison is explicitly open in glm23_klein_h3_circle_coefficients.
- Next leaf: EX2

### K02. Diagonal/cyclic invariants separate classes; all trivializing subgroups match printed eight-row table
Source: `1850–1873`; unlabelled. Kind: subgroup and invariant table. Status: **merged**.
- Lean: `TNLean.Algebra.ScalarThreeCochain.kleinCocycleFamily_signs` in `TNLean/Algebra/KleinCocycleTable.lean`
- Lean: `TNLean.Algebra.ScalarThreeCochain.kleinCocycleFamily_isTrivialGaugeClass_comap_iff_generators` in `TNLean/Algebra/KleinCocycleTable.lean`
- Lean: `TNLean.Algebra.ScalarThreeCochain.cohomologousTo_iff_klein_three_cyclicInvariants` in `TNLean/Algebra/KleinCocycleCompleteness.lean`
- Blueprint: `thm:asymex_klein_cocycle_restrictions` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1102` (`leanok`)
- Blueprint: `thm:asymex_klein_subgroup_table` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1313` (`leanok`)
- Blueprint: `thm:asymex_klein_complete_classification` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1522` (`leanok`)
- Issue: [#8051](https://github.com/LionSR/TNLean/issues/8051) (open)
- Boundary: Use cyclic invariant for unnormalized representatives; raw diagonal alone is gauge-invariant only under required normalization.

### K03. Trivial anomaly six phases; seven anomalous classes grouped by stabilizers; (1,1,1) unique four-block regular phase
Source: `1875–1888`; unlabelled. Kind: phase counting. Status: **restricted**.
- Lean: `TNLean.Algebra.LSymbol.exists_regular_actionGaugeEquiv_of_kleinCocycleFamily_one` in `TNLean/Algebra/KleinCocyclePhase.lean`
- Lean: `TNLean.Algebra.LSymbol.card_of_kleinCocycleFamily_one` in `TNLean/Algebra/KleinCocycleTable.lean`
- Blueprint: `thm:asymex_klein_four_block_uniqueness` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1230` (`leanok`)
- Blueprint: `thm:asymex_klein_four_blocks` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1172` (`leanok`)
- Issue: [#8051](https://github.com/LionSR/TNLean/issues/8051) (open)
- Boundary: (1,1,1) scalar/free action and table are proved. Exhaustive phase counts need subgroup H² and physical classification bridges; fully broken H_e phase must not disappear in prose that counts only two-block phases.
- Next leaf: EX2

### K04. Printed one-qubit Klein generators, representation and the two invariant subspaces
Source: `1884–1886`; unlabelled. Kind: explicit operator and invariant-state example. Status: **merged**.
- Lean: `KleinSymmetry.operator_mul` in `TNLean/MPS/Examples/KleinSymmetry.lean`
- Lean: `KleinSymmetry.generators_preserve_constantSpinSpace` in `TNLean/MPS/Examples/KleinSymmetry.lean`
- Lean: `KleinSymmetry.generators_preserve_clusterPairSpace` in `TNLean/MPS/Examples/KleinSymmetry.lean`
- Blueprint: `thm:asymex_klein_spin_representation` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1381` (`leanok`)
- Blueprint: `thm:asymex_klein_spin_spaces` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1427` (`leanok`)
- Issue: [#8051](https://github.com/LionSR/TNLean/issues/8051) (open)

### K05. Printed realization carries class (0,0,1), diagonal signs (+,+,−), and displayed L ratios
Source: `1884–1886`; unlabelled. Kind: anomaly and L signs. Status: **restricted**.
- Lean: `KleinSymmetry.cyclicInvariant_omega_printedFamily` in `TNLean/MPS/Examples/KleinSymmetryAnomaly.lean`
- Lean: `KleinSymmetry.not_isTrivialGaugeClass_omega_printedFamily` in `TNLean/MPS/Examples/KleinSymmetryAnomaly.lean`
- Lean: `TNLean.Algebra.LSymbol.apply_self_of_kleinCocycleFamily` in `TNLean/Algebra/KleinCocyclePhase.lean`
- Blueprint: `thm:asymex_klein_printed_anomaly` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1580` (`leanok`)
- Blueprint: `thm:asymex_klein_l_symbol_signs` in `blueprint/src/chapter/ch25_asymmetric_examples_z2z2.tex:1286` (`leanok`)
- Issue: [#8480](https://github.com/LionSR/TNLean/issues/8480) (open), [#8051](https://github.com/LionSR/TNLean/issues/8051) (open)
- Boundary: Only ab sign and nontriviality are proved for this realization. Need a,b signs and full class, then tensor-derived L signs. Do not substitute the two-qubit condensation realization (#8041) or four-level generic construction. “Only nontrivial element” in source is safely the three diagonal entries, not all cocycle entries.
- Next leaf: EX3

### S01. su(2)₄ five-label fusion table and unit
Source: `1890–1905`; unlabelled. Kind: fusion-table example. Status: **merged**.
- Lean: `MPOTensor.su24Fusion` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.isFusionUnit_su24Fusion` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.isNIMRep_su24Fusion` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `def:mposym_su24_reps3` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1024` (`leanok`)
- Blueprint: `thm:mposym_su24_reps3_units` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1040` (`leanok`)
- Blueprint: `thm:mposym_su24_reps3_nimreps` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1060` (`leanok`)
- Issue: [#8052](https://github.com/LionSR/TNLean/issues/8052) (closed)

### S02. Exactly regular five-block and TY four-block phases; positive-Frobenius-Schur F data
Source: `1906–1911`; unlabelled. Kind: categorical classification. Status: **restricted**.
- Lean: `MPOTensor.su24TY` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.isNIMRep_su24TY` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `thm:mposym_su24_reps3_nimreps` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1060` (`leanok`)
- Issue: [#8348](https://github.com/LionSR/TNLean/issues/8348) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Concrete NIM-reps exist; explicit F/L and categorical completeness do not. Rank/duality plus categorifiability must be justified.
- Next leaf: EX4

### S03. TY module table including multiplicity 2 on s
Source: `1911–1925`; unlabelled. Kind: NIM-rep table. Status: **merged**.
- Lean: `MPOTensor.su24TY` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.isNIMRep_su24TY` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `thm:mposym_su24_reps3_nimreps` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1060` (`leanok`)
- Issue: [#8052](https://github.com/LionSR/TNLean/issues/8052) (closed)

### S04. Integer subcategory leaves xyz and s separately; whole symmetry disallows integer-sector-only threefold/onefold phases
Source: `1927–1929`; unlabelled. Kind: restriction and physical interpretation. Status: **restricted**.
- Lean: `MPOTensor.su24TY_repS3ToSU24_castSucc` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.su24TY_repS3ToSU24_last` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.su24TY_repS3ToSU24_mix` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `thm:mposym_reps3_in_su24` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1102` (`leanok`)
- Issue: [#8348](https://github.com/LionSR/TNLean/issues/8348) (open)
- Boundary: Table restriction merged; interpretation/exhaustiveness relies on category and Hamiltonian classification.
- Next leaf: EX4

### R01. Rep(S₃) fusion, inclusion into integer su(2)₄; Wigner 6j F data; phases indexed by subgroups with trivial H²
Source: `1933–1936`; unlabelled. Kind: fusion and categorical claims. Status: **restricted**.
- Lean: `MPOTensor.repS3Fusion` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.su24Fusion_repS3ToSU24` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `def:mposym_su24_reps3` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1024` (`leanok`)
- Blueprint: `thm:mposym_su24_reps3_units` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1040` (`leanok`)
- Issue: [#8348](https://github.com/LionSR/TNLean/issues/8348) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Ring inclusion merged. Tensor/category inclusion and 6j/cohomology classification are not established by the table.
- Next leaf: EX4

### R02. H=1 gives one block with π multiplicity 2, no conflict with multiplicity-one obstruction; L from TY restriction
Source: `1938–1940`; unlabelled. Kind: one-block example. Status: **restricted**.
- Lean: `MPOTensor.repS3Z1` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.isFusionCharacter_repS3Fusion_iff` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `thm:mposym_su24_reps3_nimreps` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1060` (`leanok`)
- Blueprint: `thm:mposym_su24_reps3_one_block` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1126` (`leanok`)
- Issue: [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: One-block NIM-rep classification merged; actual L/TY restriction absent.
- Next leaf: EX4

### R03. H=Z₂ NIM-rep table; L restriction from regular su(2)₄ half-integer sector
Source: `1943–1957`; unlabelled. Kind: two-block example. Status: **restricted**.
- Lean: `MPOTensor.repS3Z2` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.isNIMRep_repS3Z2` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.su24Fusion_repS3ToSU24_half` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `thm:mposym_su24_reps3_nimreps` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1060` (`leanok`)
- Blueprint: `thm:mposym_reps3_in_su24` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1102` (`leanok`)
- Issue: [#8348](https://github.com/LionSR/TNLean/issues/8348) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: NIM-rep table/restriction merged; multiplicity L realization and exhaustiveness missing.
- Next leaf: EX4

### R04. H=Z₃ table and TY restriction
Source: `1959–1972`; unlabelled. Kind: three-block example with source error. Status: **corrected-source**.
- Lean: `MPOTensor.repS3Z3` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.isNIMRep_repS3Z3` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Lean: `MPOTensor.not_isNIMRep_repS3Z3Printed` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `thm:mposym_su24_reps3_nimreps` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1060` (`leanok`)
- Issue: [#8052](https://github.com/LionSR/TNLean/issues/8052) (closed), [#8348](https://github.com/LionSR/TNLean/issues/8348) (open)
- Boundary: Printed ψ swaps y,z and violates fusion; corrected ψ=I. Counterexample + corrected NIM-rep merged; L-symbol restriction still missing. glm23_reps3_z3_table.
- Next leaf: EX4

### R05. H=S₃ regular table and L=F
Source: `1974–1987`; unlabelled. Kind: regular-module example. Status: **restricted**.
- Lean: `MPOTensor.isNIMRep_repS3Fusion` in `TNLean/MPS/Symmetry/MPOSymmetry/RepS3SU24NIMRep.lean`
- Blueprint: `thm:mposym_su24_reps3_nimreps` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:1060` (`leanok`)
- Issue: [#8045](https://github.com/LionSR/TNLean/issues/8045) (open), [#8348](https://github.com/LionSR/TNLean/issues/8348) (open)
- Boundary: Fusion/NIM-rep table merged; actual L=F and exhaustive category list remain.
- Next leaf: EX4

### FIB. Fibonacci unique indecomposable regular two-block module and L=F
Source: `1991–1993`; unlabelled. Kind: classification example. Status: **restricted**.
- Lean: `FibonacciCompression.exists_equiv_of_isMPOSymmetricFamily_fibBlock` in `TNLean/MPS/Examples/Fibonacci/FibonacciNIMRepClassification.lean`
- Lean: `FibonacciCompression.exists_equiv_of_isNIMRep_fibNim_of_card_eq_two` in `TNLean/MPS/Examples/Fibonacci/FibonacciNIMRepClassification.lean`
- Blueprint: `thm:mpo_symmetry_fibonacci_rank_two` in `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex:949` (`leanok`)
- Issue: [#8053](https://github.com/LionSR/TNLean/issues/8053) (open)
- Boundary: Only rank ≤2 classification merged; arbitrary-rank indecomposable classification and L=F missing. Direct sums show uniqueness needs indecomposable scope; gap note records it.
- Next leaf: EX5

### X01. Arbitrary-boundary group tensors on C[G]⊗C[G], bond |G| per label, entries ω(g,l,l⁻¹k)
Source: `2003–2024`; unlabelled. Kind: explicit construction. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: Do not count GroupCocycle.tensor: that is the compressed PBC construction.
- Next leaf: GX1

### X02. ftexam explicit fusion entries ω(g,h,k)⁻¹; exact fusion and inverse anomaly
Source: `2024–2044`; `ftexam`. Kind: fusion and anomaly computation. Status: **restricted**.
- Lean: `MPOTensor.GroupCocycle.fusionV` in `TNLean/MPS/MPU/GroupCocycleMPO/FusionTensors.lean`
- Lean: `MPOTensor.GroupCocycle.fusionData_omega` in `TNLean/MPS/MPU/GroupCocycleMPO/FusionTensors.lean`
- Blueprint: `def:asymex_group_cocycle_fusion_tensors` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:272` (`leanok`)
- Blueprint: `thm:asymex_group_cocycle_inverse_cocycle` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:314` (`leanok`)
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: PBC fusion maps/inverse anomaly present; arbitrary-boundary tensor verification is missing.
- Next leaf: GX1

### X03. W_g diagonal cocycle gate, L_g regular shift, W_e=I; Z₂ CZ(I⊗Z) example
Source: `2046–2070`; unlabelled. Kind: gate definitions and example. Status: **merged**.
- Lean: `MPOTensor.GroupCocycle.wGate` in `TNLean/MPS/MPU/GroupCocycleMPO.lean`
- Lean: `MPOTensor.GroupCocycle.leftShift` in `TNLean/MPS/MPU/GroupCocycleMPO.lean`
- Lean: `MPOTensor.GroupCocycle.wGate_one` in `TNLean/MPS/MPU/GroupCocycleMPO.lean`
- Lean: `MPOTensor.GroupCocycle.wGate_cyclicTwo` in `TNLean/MPS/MPU/GroupCocycleMPO/Instances.lean`
- Blueprint: `def:asymex_group_cocycle_tensor` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:32` (`leanok`)
- Blueprint: `thm:asymex_group_cocycle_one` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:220` (`leanok`)
- Blueprint: `thm:asymex_group_cocycle_z2` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:375` (`leanok`)

### X04. O_e=product of equality projectors; O_g group law and adjoint inverse on projected subspace
Source: `2073–2096`; unlabelled. Kind: explicit operator theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: Adjoint requires unit-modulus cocycle. Arbitrary-boundary projected family is not the existing PBC U_e=I family.
- Next leaf: GX1

### X05. Coset MPS blocks and tensor entries inverse L; claimed bond |G/H| per block
Source: `2098–2116`; unlabelled. Kind: state construction. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: Audit printed diagram/group versus coset indexing before selecting dimension. Need injectivity/normality and distinctness, not only an entry table.
- Next leaf: GX2

### X06. Explicit action entries inverse L and exact MPOsymG local identity
Source: `2117–2200`; unlabelled. Kind: action construction and verification. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: Requires X01–X05 and reconstructed compatible L; verify reciprocal convention and multiplicity spaces.
- Next leaf: GX2

### X07. Neighboring-half isometry Γ maps projected arbitrary-boundary family to PBC family with U_e=I
Source: `2202–2205`; unlabelled. Kind: compression construction. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: The PBC operator exists but Γ circuit/intertwining from X04 does not. Audit source depth-n sentence separately from mathematical contraction.
- Next leaf: GX3

### X08. PBC tensor, group law and Z₂ decorated CZX realization
Source: `2205–2224`; unlabelled. Kind: PBC operator construction and example. Status: **corrected-source**.
- Lean: `MPOTensor.GroupCocycle.tensor` in `TNLean/MPS/MPU/GroupCocycleMPO.lean`
- Lean: `MPOTensor.GroupCocycle.mpo_tensor_mul` in `TNLean/MPS/MPU/GroupCocycleMPO.lean`
- Lean: `MPOTensor.GroupCocycle.mpo_tensor_one` in `TNLean/MPS/MPU/GroupCocycleMPO.lean`
- Lean: `MPOTensor.GroupCocycle.mpo_tensor_cyclicTwo` in `TNLean/MPS/MPU/GroupCocycleMPO/Instances.lean`
- Blueprint: `def:asymex_group_cocycle_tensor` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:32` (`leanok`)
- Blueprint: `thm:asymex_group_cocycle_mul` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:193` (`leanok`)
- Blueprint: `thm:asymex_group_cocycle_one` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:220` (`leanok`)
- Blueprint: `thm:asymex_group_cocycle_z2` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:375` (`leanok`)
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: Merged one-shift-per-site correction. Generic identity tensor is not normal for nontrivial G, so do not instantiate IsNormalRepresentation from its operator laws. glm23_pbc_group_mpo_single_shift.

### X09. Explicit PBC tensors obey fusion reduction and left zipper
Source: `2224–2242`; unlabelled. Kind: fusion and zipper theorem. Status: **merged**.
- Lean: `MPOTensor.GroupCocycle.fusionV_mul_mulTensor` in `TNLean/MPS/MPU/GroupCocycleMPO/FusionTensors.lean`
- Lean: `MPOTensor.GroupCocycle.isReduction_fusion` in `TNLean/MPS/MPU/GroupCocycleMPO/FusionTensors.lean`
- Blueprint: `thm:asymex_group_cocycle_fusion` in `blueprint/src/chapter/ch25_asymmetric_examples_group_cocycle.tex:285` (`leanok`)
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: Source-corrected tensor and explicit fusion maps. Generic family is not a normal representation; explicit nonvanishing comparison proves its computed anomaly.

### X10. Right zipper fails; exact reconstruction requires P_g,h; projector acts identically on PBC-supported virtual configurations
Source: `2243–2287`; unlabelled. Kind: projector/right-zipper theorem. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8054](https://github.com/LionSR/TNLean/issues/8054) (open)
- Boundary: This full source tail is absent from tracker’s 2224–2233 range. Need explicit projector, idempotence, corrected identity, positive witness to failure, and closure identity.
- Next leaf: GX4

### OUT. Restatement of classification; bulk detection and TRS/anyon-condensation/MBQC research proposals
Source: `2289–2299`; `sec:outlook`. Kind: summary and outlook. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Classification restatement is C01; proposals are not proved theorems and are explicitly excluded from closure checklist. PEPS extension coordinated only.
- Next leaf: PH7

### AA1. Length-independent boundary product factors through a linear boundary map B; minimal-rank two-sided matrix decomposition
Source: `2305–2309`; `ap:proofs`. Kind: Appendix A linearization. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Prove linearity/factorization rather than assume B as extra data. Reduce to diagonal block boundary spaces to quotient invisible boundaries.
- Next leaf: AB2

### AA2. Project B into block channels, choose minimal independent fusion maps, derive all-word decompopen and exact one-letter fusion
Source: `2311–2359`; `decompopen`. Kind: Appendix A existence proof. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Keep same B across all lengths and show finite linear rank factorization. Existing trace-only compression is not this argument.
- Next leaf: AB2

### AA3. Compare n=1 and n=2; block-separating inverse and minimal linear independence force eq:ortho
Source: `2360–2453`; `eq:ortho`. Kind: Appendix A orthogonality proof. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open)
- Boundary: Use simultaneous block inverse (or derived faithful blocking), not independent inverses that fail to isolate labels. Must derive exact splitting without unproved semisimplicity assumption.
- Next leaf: AB2

### AA4. Repeat boundary-map argument for action tensors and orthogonality
Source: `2455`; unlabelled. Kind: Appendix A action analogue. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#7968](https://github.com/LionSR/TNLean/issues/7968) (open), [#8045](https://github.com/LionSR/TNLean/issues/8045) (open)
- Boundary: Separate action map from multiplication; same reusable algebraic theorem may cover both.
- Next leaf: AB3

### AB1. Averaged local complement is nonzero projector onto S⊥
Source: `2457–2463`; `app:sumnonull`. Kind: Appendix B on-site proof. Status: **restricted**.
- Lean: `MPSTensor.parentInteractionES_commute_onSiteTensorPow` in `TNLean/MPS/Symmetry/ParentHamiltonianSymmetry.lean`
- Blueprint: `thm:spt_parent_hamiltonian_symmetry` in `blueprint/src/chapter/ch12_symmetry_spt.tex:5062` (`leanok`)
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open)
- Boundary: Source uses nonzero trace of Π_S but that alone does not prove I−Π_S nonzero. Need proper support/nontrivial interaction condition or a documented source correction. For unitary invariant S, averaged Π_S=Π_S is direct.
- Next leaf: PH1

### AB2. Canonical-integral averaging is Hermitian, preserves trace against Δ(1), projects onto S; nonzero complement
Source: `2466`; unlabelled. Kind: Appendix B WHA proof. Status: **missing**.
- Lean: no implementation of this claim located
- Blueprint: no verified declaration-owning node for this full claim; create or update a source-faithful node
- Issue: [#8050](https://github.com/LionSR/TNLean/issues/8050) (open), [#8315](https://github.com/LionSR/TNLean/issues/8315) (open)
- Boundary: Formalize cited weak-Hopf identities and support hypotheses, positivity/rank/kernel and gap preservation. Do not turn these conclusions into structure fields and claim derivation.
- Next leaf: PH1

## Blueprint and audit reconciliation

- `ch30_mpo_algebras.tex` intentionally forwards many implemented periodic/group claims to declaration-owning nodes in chapters 25 and 29. Lack of a duplicate `\lean` tag is not a missing proof. However `def:mpoalg_l_symbols`, `thm:mpoalg_l_compatible`, `thm:mpoalg_no_symmetric_normal`, and several “Planned Lean” comments are stale against existing scalar constructions; update the narrative and dependency edges without duplicating tags or broadening them to full multiplicity claims.
- `def:mpoalg_fusion_tensors` and `def:mpoalg_action_tensors` describe periodic reductions with nilpotent remainder. Their adjacent existence theorems must not read as the exact Appendix A theorem. Main already has useful periodic results at `cor:asym_fusion_action_multiplicity`; the source-faithful exact nodes remain separate.
- `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex` is legitimately still open, but its “not formalized” blanket statements about F/L/gauge/group obstruction are stale. Narrow it to actual missing arbitrary-boundary and general multiplicity constructions and cite implemented conditional/group branches.
- `docs/paper-gaps/glm23_eq20_fusion_gauge.tex`, `glm23_time_reversal_l_symbol.tex`, `glm23_pbc_group_mpo_single_shift.tex`, and `glm23_reps3_z3_table.tex` are resolved mathematical corrections, not implementation debt to erase.
- `glm23_fibonacci_module_rank_scope.tex`, `glm23_reps3_su24_module_list.tex`, `glm23_klein_h3_circle_coefficients.tex`, and `glm23_klein_printed_anomaly_scope.tex` remain real scope gaps.
- The Appendix B nonzero-complement issue is a new audit concern, not a confirmed repository correction: before formalizing the statement, inspect the intended nontrivial-parent/support convention. Positive trace of Π_S proves Π_S≠0, not I−Π_S≠0. Preserve this distinction in the leaf specification.
- Shared on-site phase modules are substantial reuse: `ExactMPSGappedPhase`, `GappedInteractionPath`, `CanonicalInjectiveGappedPath`, `EmbeddedInjectiveGappedPath`, `CommonKernelSpectralGap`, and `CompactParentGap`. Their signatures impose on-site and/or one-site-injective restrictions, so they cannot be tagged as GLM23’s full physical classification.

## Unmerged work observed during audit

The candidate changes add `TNLean/MPS/MPDO/BoundaryTransport.lean`, `TNLean/MPS/Symmetry/MPOSymmetry/GroupAction.lean`, and `blueprint/src/chapter/ch30_mpo_symmetry_group_action.tex`, with aggregator changes. These are **unmerged / not build-verified by this report**. AB1 and the coherent-action part of GC1/G03 should be reconciled to their final reviewed signatures when they land; no in-progress work is credited in the 103 baseline rows.

## Exhaustive source-label index

| Source label | Line | Claim rows |
|---|---:|---|
| `sec:data` | 302 | B01 |
| `MPSssubs` | 313 | B01, B02 |
| `algcond` | 329 | A01 |
| `fusiontensors` | 362 | A02, A03 |
| `eq:orthoW` | 384 | A03 |
| `Fsymbolsdef` | 393 | F01 |
| `pentagon0F` | 411 | F02 |
| `sec:inter` | 429 | A05 |
| `eq:compatible` | 434 | A05 |
| `fusiontensors2` | 461 | A06 |
| `eq:orthoV` | 483 | A07 |
| `rawrels` | 492 | L01 |
| `eq:F_symbol2` | 517 | L01 |
| `1Fsymbol` | 535 | L01 |
| `coupledpent` | 554 | L02 |
| `nonuniqueGS` | 607 | O01 |
| `groupcase` | 638 | G01 |
| `fusiontensorG` | 641 | G01 |
| `3cocygroup` | 664 | G02 |
| `MPOsymG` | 684 | G03 |
| `F1group` | 703 | G04 |
| `pentagongroups` | 716 | G04 |
| `gdgroup` | 722 | G05 |
| `physym` | 731 | G07 |
| `Lexpre` | 755 | G09 |
| `gxdecomp` | 764 | G11 |
| `defodot` | 817 | G12 |
| `intactens` | 831 | G12 |
| `nonasso` | 833 | G12 |
| `Lgroupdef` | 843 | G13 |
| `coupengroup` | 848 | G13 |
| `sec:TRS` | 865 | T01 |
| `TRSF1group` | 954 | T03 |
| `sec:PBC` | 994 | P01 |
| `fusiontensorG2` | 1002 | P02 |
| `mpoMPSsten` | 1066 | P04 |
| `oPBCMPO` | 1132 | P06 |
| `oPBCMPSs` | 1170 | P06 |
| `sec:classif` | 1219 | C01 |
| `sec:fixsym` | 1234 | C02 |
| `defsym` | 1241 | C02 |
| `defphase` | 1255 | C03 |
| `sec:parentHrestric` | 1322 | C06 |
| `leftinv` | 1334 | C08 |
| `eq:F_symbol3` | 1423 | C10 |
| `defAgamma` | 1586 | C12 |
| `Agammasym` | 1633 | C13 |
| `fig:bound` | 1791 | C17 |
| `sketch` | 1792 | C17 |
| `symboundary` | 1796 | C18 |
| `sec:examples` | 1811 | Z01 |
| `sec:expexam` | 1997 | X01 |
| `ftexam` | 2025 | X02 |
| `sec:outlook` | 2289 | OUT |
| `ap:proofs` | 2305 | AA1 |
| `decompopen` | 2313 | AA2 |
| `eq:ortho` | 2440 | AA3 |
| `app:sumnonull` | 2457 | AB1 |

## Explicitly excluded from theorem-completion counts

The introduction’s historical/literature statements (lines 266–300), future-work expectations in §7 (2291–2299), acknowledgements and bibliography are not new proved GLM23 results. Their substantive classification/regularity assertions are mapped to the body rows above. Background theorems cited to MPS canonical-form/Wielandt/parent-Hamiltonian or fusion-category literature remain named shared dependencies with their exact hypothesis scope; they are not assumed proved merely because GLM23 cites them. The diagram labels `fig:bound`/`sketch` are tracked, but the PEPS development is owned elsewhere.

## Machine-readable companions and verification

- `glm23-source-index.json`: all 103 claims, source line/label ownership, Lean paths/declaration evidence, blueprint nodes and issue links.
- `glm23-dependency-leaves.json`: 29 concrete leaves and dependency edges.
- `glm23-pr-status.json`: live normalized PR snapshots for the eleven stale items.
- `glm23-issue-details.json` and `glm23-more-issue-details.json`: live issue snapshots.
- `glm23-lean-declarations.json` and `glm23-all-blueprint-nodes.json`: inspectable declaration/tag indices.
- The Lean proof-body scanner found no new proof placeholders in the principal modules examined; this is a source inspection only. No build, checkdecls or CI result is claimed here.

## Independent review repair and final QA

Blueprint ownership now requires fully qualified declaration-tag equality. A previous terminal-name fallback incorrectly associated 15 row/node pairs, including unrelated `gauge`, `omega`, and `tensor` declarations. Those associations were removed, leaving 138 exact row/node associations; no claim row lost its last verified owner. Related specializations are not retained as declaration owners. The generator reads source, Lean modules, and blueprint nodes from the immutable audit commit, so in-flight changes are excluded from merged evidence.

Every internal row destination now resolves to one of the 29 dependency leaves. B03 points to PH1 for its shared parent-Hamiltonian dependency; O02, C01, and OUT point to PH7 for the physical capstone. C17 is an explicitly external PEPS interface, with the separately owned implementation excluded from the internal DAG.

Final source inspection: 166 exact qualified declaration references in 62 existing Lean modules; all 58 source labels assigned; 29 leaf nodes and every row-to-leaf destination checked; no unresolved declaration, ownership, or dependency errors. Source categories and claim statements are unchanged. Some declarations lack a declaration-owning blueprint tag, as listed in `glm23-blueprint-qa.json`; these are coverage gaps, not guessed matches. No Lean build, blueprint checkdecls, or CI result is asserted by this audit.
