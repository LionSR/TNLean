# SCP10 declaration coverage audit

Source: Schuch, Cirac and Pérez-García, *PEPS as ground states: Degeneracy and topology*, arXiv:1001.3807v3. The repository source is `Papers/1001.3807/paper_v3.tex`. This audit is pinned to main `680b30da6fec94f5b269c3753ab4b8c86da79936` on 2026-10-05. Unmerged work is not counted as proved.

## Counting and verification

The source uses one counter for definitions, lemmas, theorems, corollaries and observations in each section. There are **51 numbered declarations**: **13 definitions, 10 lemmas, 21 theorems, 2 corollaries and 5 observations**. Sections 2–6 contain 4, 5, 12, 9 and 21 declarations respectively. Unnumbered Section 7 constructions are listed separately and are not added to 51.

- **Complete**: a matching implemented statement/definition was inspected, with the stated conventions retained.
- **Derived**: an existing stronger theorem gives the exact source claim by specialization; no separate theorem name or proof API is required.
- **Corrected**: the implemented statement repairs a stated source omission or convention. This does not prove the uncorrected wording.
- **Partial**: a proper restricted result or component is implemented, and the remaining source obligation is stated.
- **Open**: prerequisites exist, but the source conclusion itself has not been located.

This is a declaration/signature and source crosswalk, not a fresh full Lean build or a percentage of the paper completed. Lean declarations, blueprint labels and source ranges were checked on the pinned tree. Existing merged status is distinguished from the new proof work. Citation-only matches do not establish coverage.

Status counts: **Complete: 25**, **Derived: 4**, **Corrected: 3**, **Partial: 18**, **Open: 1**.

## Issue ownership

- #8674: Theorems 5.4–5.5, unrestricted two-dimensional intersection/closure.
- #8675: Theorems 5.7/5.9, full torus parent-kernel spanning and degeneracy; downstream all-parent-state claims in 6.7–6.10 depend on this.
- #8676: Observations 6.5–6.6, physical global blocking and renormalization.
- #8464: reopened for the original two-dimensional Theorem 6.12 target; the completed MPS results remain valid.
- #8677: completed source-crosswalk correction for 3.2–3.4. These are proved specializations, not new mathematical proof targets; the issue was closed after the correction appeared in #8271.
- Existing source issues #8360, #8362, #8365, #8368, #8370, #8374, #8448 and #8272 are reused. Broad source tracker #8271 and region-parent tracker #7681 retain their original roles.

Only existing labels are used: `1001.3807`, `PEPS`, `formalization`, and `parent-hamiltonian` where applicable. No completion percentage is inferred from closed issue counts. The incorrect `all-resolved` label was removed from #8271.

## Numbered declaration inventory

### 2.1 Definition: Periodic MPS

**Complete**. [Source lines 428–439](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L428-L439).

- Lean: [`mpv`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/MPS/Defs.lean#L55).
- Blueprint: [`def:mpv`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch02_mps.tex#L133).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Trace-of-products definition, positive ring lengths as in the source.

### 2.2 Definition: Periodic PEPS

**Complete**. [Source lines 475–487](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L475-L487).

- Lean: [`torusBondNetwork`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusOperatorString.lean#L160).
- Blueprint: [`def:peps_torus_site_tensor`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_torus_examples.tex#L28).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Coefficient contraction gives the four-leg periodic PEPS; rectangular tori are an extension. Native simple-graph identification has its separate period hypotheses.

### 2.3 Definition: Virtual-to-physical map

**Complete**. [Source lines 501–510](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L501-L510).

- Lean: [`siteMap`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjective.lean#L153).
- Blueprint: [`def:peps_g_injective`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L33).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

PEPS site map and MPS trace map mpsSiteMap are implemented; retain their index/vectorization convention.

### 2.4 Observation: Restriction to physical support

**Complete**. [Source lines 541–554](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L541-L554).

- Lean: [`exists_physicalSupport_isometry_section`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/PhysicalSupportSection.lean#L98).
- Blueprint: [`thm:peps_physical_support_section`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_physical_support.tex#L2).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

The tensor factors through its range isometrically; the section is a right inverse and its reverse is the projection onto ker(T) orthogonal complement. The intrinsic support avoids an unjustified row-span identification.

### 3.1 Definition: Injectivity

**Complete**. [Source lines 613–625](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L613-L625).

- Lean: [`isGInjective_trivial_iff`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjective.lean#L122).
- Blueprint: [`thm:peps_g_injective_trivial`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L73).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Full virtual injectivity equals G-injectivity for the trivial representation; the MPS convention is the spanning/Kraus.IsInjective condition.

### 3.2 Lemma: Injective concatenation

**Derived**. [Source lines 627–635](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L627-L635).

- Lean: [`IsGInjective.mpsSiteMap_concatTensor`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPS.lean#L357).
- Blueprint: [`thm:peps_mps_g_injective_concatenation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L357).
- Issue owner: [#8677](https://github.com/LionSR/TNLean/issues/8677).

Proved by the singleton-group specialization of the two-independent-tensor G-injective concatenation theorem. The conjugation action is trivial; isGInjective_trivial_iff gives ordinary injectivity. No new hypothesis or wrapper is needed.

### 3.3 Theorem: Injective intersection

**Derived**. [Source lines 691–703](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L691-L703).

- Lean: [`IsGInjective.intersection_property`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPSIntersection.lean#L131).
- Blueprint: [`thm:peps_mps_g_injective_intersection`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L473).
- Issue owner: [#8677](https://github.com/LionSR/TNLean/issues/8677).

Proved by the singleton-group specialization of the two-independent-tensor G-injective intersection theorem. The source boundary spaces are unchanged. Missing separately named ordinary corollaries are not mathematical gaps.

### 3.4 Theorem: Injective closure

**Derived**. [Source lines 730–740](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L730-L740).

- Lean: [`IsGInjective.closure_property`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPSIntersection.lean#L229).
- Blueprint: [`thm:peps_mps_g_injective_closure`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L505).
- Issue owner: [#8677](https://github.com/LionSR/TNLean/issues/8677).

Proved by the singleton-group specialization of the G-injective closure theorem: the group sum reduces to the scalar line of the untwisted periodic state. No additional representation or normalization hypothesis.

### 3.5 Theorem: Injective parent Hamiltonian

**Complete**. [Source lines 758–772](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L758-L772).

- Lean: [`groundSpace_unique_periodic`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean#L856).
- Blueprint: [`thm:ground_space_unique_periodic`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch13_parent_hamiltonian_normal_closing_reverse.tex#L668).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Periodic unique ground space for range L≥2 and N≥L; take L=2 for the source. Kernel/common-ground-space bridge is implemented separately.

### 4.1 Theorem: Finite-group commutant

**Corrected**. [Source lines 852–863](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L852-L863).

- Lean: [`exists_finite_unitary_group_commutant`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/Algebra/FiniteGroupCommutant.lean#L228).
- Blueprint: [`thm:peps_finite_group_commutant_unital`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_finite_group_commutant.tex#L67).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Proved for a unital complex star-subalgebra. The missing unital qualification is a source correction, not a proof of the printed unrestricted algebra claim.

### 4.2 Definition: G-injective MPS

**Complete**. [Source lines 893–910](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L893-L910).

- Lean: [`isGInjective_mpsSiteMap_iff`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPS.lean#L141).
- Blueprint: [`thm:peps_mps_g_injective_source_form`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L326).
- Issue owner: [#8362](https://github.com/LionSR/TNLean/issues/8362).

Conjugation invariance and injectivity on the commutant, with source-form equivalence.

### 4.3 Lemma: Group average projection

**Complete**. [Source lines 923–937](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L923-L937).

- Lean: [`isProj_averageMap_linHom`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/Algebra/RepresentationDelta.lean#L102).
- Blueprint: [`thm:peps_group_averaging`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L97).
- Issue owner: [#8360](https://github.com/LionSR/TNLean/issues/8360).

Projection onto invariants; orthogonality uses the unitary/adjoint hypothesis stated by the source.

### 4.4 Lemma: Delta expansion

**Complete**. [Source lines 960–984](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L960-L984).

- Lean: [`sum_trace_comp_deltaOperator_smul`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/Algebra/RepresentationDelta.lean#L213).
- Blueprint: [`thm:peps_delta_expansion`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L198).
- Issue owner: [#8360](https://github.com/LionSR/TNLean/issues/8360).

Weighted trace expansion for the given finite-group representation.

### 4.5 Definition: Semi-regular representation

**Complete**. [Source lines 1010–1013](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1010-L1013).

- Lean: [`IsSemiRegular`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/Algebra/RepresentationDelta.lean#L235).
- Blueprint: [`def:peps_semiregular`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L225).
- Issue owner: [#8360](https://github.com/LionSR/TNLean/issues/8360).

Every irreducible representation occurs; equivalent representation transport is available.

### 4.6 Lemma: Semi-regular trace independence

**Complete**. [Source lines 1015–1023](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1015-L1023).

- Lean: [`trace_inv_comp_comp_deltaOperator_of_isSemiRegular`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/Algebra/RepresentationDelta.lean#L335).
- Blueprint: [`thm:peps_semiregular_trace`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L255).
- Issue owner: [#8360](https://github.com/LionSR/TNLean/issues/8360).

Delta trace is the Kronecker delta under semi-regularity; no arbitrary-representation extension claimed.

### 4.7 Lemma: G-injective concatenation

**Complete**. [Source lines 1036–1046](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1036-L1046).

- Lean: [`IsGInjective.mpsSiteMap_concatTensor`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPS.lean#L357).
- Blueprint: [`thm:peps_mps_g_injective_concatenation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L357).
- Issue owner: [#8362](https://github.com/LionSR/TNLean/issues/8362).

Two independent tensors for the same representation, with explicit concatenated left inverse.

### 4.8 Theorem: G-injective MPS intersection

**Complete**. [Source lines 1084–1095](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1084-L1095).

- Lean: [`IsGInjective.intersection_property`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPSIntersection.lean#L131).
- Blueprint: [`thm:peps_mps_g_injective_intersection`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L473).
- Issue owner: [#8365](https://github.com/LionSR/TNLean/issues/8365).

Actual trace-generated boundary spaces for independent A and B; source equality, not a chain-only substitute.

### 4.9 Theorem: G-injective MPS closure

**Complete**. [Source lines 1124–1135](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1124-L1135).

- Lean: [`IsGInjective.closure_property`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPSIntersection.lean#L229).
- Blueprint: [`thm:peps_mps_g_injective_closure`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L505).
- Issue owner: [#8365](https://github.com/LionSR/TNLean/issues/8365).

Independent tensors with the same virtual representation; closure reduces to group insertions.

### 4.10 Definition: MPS with closure

**Complete**. [Source lines 1165–1176](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1165-L1176).

- Lean: [`groundSpaceMap`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/MPS/ParentHamiltonian/GroundSpace.lean#L33).
- Blueprint: [`def:ground_space_map`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex#L19).
- Issue owner: [#8368](https://github.com/LionSR/TNLean/issues/8368).

Trace of the word times the arbitrary closing operator K.

### 4.11 Theorem: G-injective MPS parent space

**Complete**. [Source lines 1178–1191](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1178-L1191).

- Lean: [`chainGroundSpace_eq_span_closure_of_isGInjective`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPSParentHamiltonian.lean#L315).
- Blueprint: [`thm:peps_mps_g_injective_parent_hamiltonian`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L579).
- Issue owner: [#8368](https://github.com/LionSR/TNLean/issues/8368).

All windows 2≤L≤N, hence the source two-site interaction. Full chain space, not an intersection with an assumed closure span.

### 4.12 Theorem: MPS degeneracy and basis

**Complete**. [Source lines 1199–1216](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1199-L1216).

- Lean: [`finrank_chainGroundSpace_of_isSemiRegular`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveMPSParentHamiltonian.lean#L473).
- Blueprint: [`thm:peps_mps_g_injective_ground_space_structure`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L646).
- Issue owner: [#8368](https://github.com/LionSR/TNLean/issues/8368).

Character-projector basis/dimension for occurring irreps; semi-regular conjugacy-class basis and count. Both parts are proved.

### 5.1 Definition: G-injective PEPS

**Complete**. [Source lines 1278–1295](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1278-L1295).

- Lean: [`IsGInjective`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjective.lean#L80).
- Blueprint: [`def:peps_g_injective`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L33).
- Issue owner: [#8370](https://github.com/LionSR/TNLean/issues/8370).

The definition parameterizes the representation; instantiate the source semi-regular action. This does not remove semi-regularity from source theorems.

### 5.2 Lemma: Two-dimensional concatenation

**Complete**. [Source lines 1319–1333](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1319-L1333).

- Lean: [`IsGInjective.linkContraction`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveConcatenation.lean#L158).
- Blueprint: [`thm:peps_g_injective_concatenation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L733).
- Issue owner: [#8370](https://github.com/LionSR/TNLean/issues/8370).

One contracted link with its semi-regular representation and source left inverse. Outer virtual factors are retained.

### 5.3 Observation: Internal leg contraction

**Complete**. [Source lines 1348–1356](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1348-L1356).

- Lean: [`IsGInjective.legContraction`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveConcatenation.lean#L303).
- Blueprint: [`thm:peps_g_injective_leg_contraction`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L792).
- Issue owner: [#8370](https://github.com/LionSR/TNLean/issues/8370).

Additional contraction within a connected block via a commuting nonzero-trace operator, matching the source construction.

### 5.4 Theorem: Two-dimensional intersection

**Partial**. [Source lines 1373–1403](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1373-L1403).

- Lean: [`IsGInjective.strip_intersection_property_of_invariant_left`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveStripIntersection.lean#L44).
- Blueprint: [`thm:peps_g_injective_strip_intersection`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_g_injective_strip_intersection.tex#L62).
- Issue owner: [#8674](https://github.com/LionSR/TNLean/issues/8674).

Blocked strips are proved; identification with unrestricted overlapping graph-region contractions remains.

### 5.5 Theorem: Two-dimensional closure

**Partial**. [Source lines 1424–1475](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1424-L1475).

- Lean: [`IsGInjective.inf_parentKernel_span_torusGClosureClass_eq_commutingSpan`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/ParentHamiltonian/TorusClosureKernelIntersection.lean#L146).
- Blueprint: [`thm:peps_regular_closure_kernel_intersection`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_torus_closure_kernel_intersection.tex#L2).
- Issue owner: [#8674](https://github.com/LionSR/TNLean/issues/8674).

Regular local constraints and closure-span intersection are proved; the full four-cut source equality remains.

### 5.6 Definition: Torus group closures

**Complete**. [Source lines 1515–1525](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1515-L1525).

- Lean: [`torusGClosure`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusGClosure.lean#L49).
- Blueprint: [`def:peps_torus_g_closure`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L4441).
- Issue owner: [#8675](https://github.com/LionSR/TNLean/issues/8675).

Actual horizontal/vertical seam insertions with explicit orientation; positive rectangular periods allowed.

### 5.7 Theorem: Torus parent Hamiltonian

**Partial**. [Source lines 1527–1548](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1527-L1548).

- Lean: [`IsGInjective.inf_parentKernel_span_torusGClosureClass_eq_commutingSpan`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/ParentHamiltonian/TorusClosureKernelIntersection.lean#L146).
- Blueprint: [`thm:peps_regular_closure_kernel_intersection`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_torus_closure_kernel_intersection.tex#L2).
- Issue owner: [#8675](https://github.com/LionSR/TNLean/issues/8675).

Only ker H ∩ closureSpan = commutingClosureSpan. Global kernel inclusion and full semi-regular parent transport remain.

### 5.8 Definition: Pair-conjugacy classes

**Complete**. [Source lines 1560–1577](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1560-L1577).

- Lean: [`pairConjugacyClass`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/PairConjugacy.lean#L42).
- Blueprint: [`def:peps_pair_conjugacy`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L4500).
- Issue owner: [#8675](https://github.com/LionSR/TNLean/issues/8675).

Simultaneous conjugacy quotient, commuting classes, and invariance of the physical closure state are implemented.

### 5.9 Theorem: Torus degeneracy

**Partial**. [Source lines 1582–1589](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1582-L1589).

- Lean: [`IsGInjective.linearIndependent_torusGClosureClass_commuting_of_isSemiRegular`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjectiveTorusSectors.lean#L90).
- Blueprint: [`thm:peps_semiregular_g_injective_closure_independence`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L5233).
- Issue owner: [#8675](https://github.com/LionSR/TNLean/issues/8675).

Semi-regular class-state independence is proved; exact count for the full parent kernel awaits global spanning.

### 6.1 Definition: G-isometric PEPS

**Corrected**. [Source lines 1692–1697](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1692-L1697).

- Lean: [`IsGIsometric`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GInjective.lean#L142).
- Blueprint: [`def:peps_g_injective`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L33).
- Issue owner: [#8374](https://github.com/LionSR/TNLean/issues/8374).

Positive scale c explicitly normalizes the source diagrams; Section 6 requires the regular action even though the formal definition is parameterized.

### 6.2 Lemma: Isometric concatenation

**Complete**. [Source lines 1704–1707](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1704-L1707).

- Lean: [`IsGIsometric.linkContraction_fourLeg`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GIsometricConcatenation.lean#L468).
- Blueprint: [`thm:peps_g_isometric_link_contraction`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L1015).
- Issue owner: [#8448](https://github.com/LionSR/TNLean/issues/8448).

Regular one-link contraction with factor c_A c_B, plus MPS concatenation. This is not arbitrary plaquette commutation.

### 6.3 Lemma: Physical implementation of virtual unitaries

**Complete**. [Source lines 1730–1740](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1730-L1740).

- Lean: [`IsGIsometric.exists_unitary_comp_eq`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GIsometric.lean#L448).
- Blueprint: [`thm:peps_g_isometric_virtual_unitaries`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L1126).
- Issue owner: [#8374](https://github.com/LionSR/TNLean/issues/8374).

Both directions after restricting to physical range as in Observation 2.4. The recovered virtual map is unitary on the invariant support, not the whole unreduced virtual space.

### 6.4 Observation: Accessible virtual bonds

**Derived**. [Source lines 1764–1783](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1764-L1783).

- Lean: [`isGIsometric_regularOpenRegionMatrix_of_connected`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/RegularRegionIsometry.lean#L58).
- Blueprint: [`thm:peps_regular_open_region_accessibility`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L1598).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Physical-support restriction, actual regular-projector coefficient/contraction identities, and the proved connected-region Gram/isometry theorem jointly give the unitary identification on used physical/invariant supports after positive normalization. Unused local dimensions may be discarded as in the source. No new global renormalization claim follows.

### 6.5 Observation: Blocking preserves isometry with removable pairs

**Partial**. [Source lines 1873–1877](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1873-L1877).

- Lean: [`blockingMatrix_conjugates`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/Algebra/RegularRepresentationBlocking.lean#L118).
- Blueprint: [`thm:peps_regular_blocking_coordinates`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L969).
- Issue owner: [#8676](https://github.com/LionSR/TNLean/issues/8676).

Regular relative-coordinate unitaries and one-link isometry are proved; the global physical state factorization with explicit Bell factors remains.

### 6.6 Observation: Renormalization fixed point

**Open**. [Source lines 1903–1909](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1903-L1909).

- Lean: [`blockingFamilyMatrix_conjugates`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/Algebra/RegularRepresentationBlocking.lean#L142).
- Blueprint: [`thm:peps_regular_blocking_coordinates`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L969).
- Issue owner: [#8676](https://github.com/LionSR/TNLean/issues/8676).

Local prerequisites only; no global coarse-lattice fixed-point/state-factorization theorem found.

### 6.7 Theorem: Width-one stripe equivalence

**Partial**. [Source lines 1998–2003](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L1998-L2003).

- Lean: [`IsGIsometric.torusClosureSuperpositionCut_stripe_local_equivalence`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusStripeLocalEquivalence.lean#L57).
- Blueprint: [`thm:peps_torus_stripe_local_equivalence`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_stripe_local_equivalence.tex#L2).
- Issue owner: [#8675](https://github.com/LionSR/TNLean/issues/8675).

Actual unitary on two width-one stripes for nonzero commuting-closure superpositions, regular native periods≥3. All-parent-state claim awaits spanning.

### 6.8 Corollary: Local indistinguishability

**Partial**. [Source lines 2014–2018](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2014-L2018).

- Lean: [`IsGIsometric.torusPhysicalCut_local_equivalence_of_isSimplyConnected`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusSimplyConnectedPhysicalDensity.lean#L119).
- Blueprint: [`thm:peps_torus_simply_connected_physical_local_equivalence`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_simply_connected_physical_density.tex#L51).
- Issue owner: [#8675](https://github.com/LionSR/TNLean/issues/8675).

Equal local expectations for closure states on contiguous simply connected closed-cell regions, periods≥3. All parent states await spanning.

### 6.9 Theorem: Flat density and topological entropy

**Partial**. [Source lines 2027–2040](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2027-L2040).

- Lean: [`IsGIsometric.exists_torusPhysicalCut_common_density_of_isSimplyConnected`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusSimplyConnectedPhysicalDensity.lean#L89).
- Blueprint: [`thm:peps_torus_simply_connected_physical_density`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_simply_connected_physical_density.tex#L2).
- Issue owner: [#8675](https://github.com/LionSR/TNLean/issues/8675).

Rank, flatness, von Neumann and finite nonnegative real-order Rényi entropy for nonzero commuting-closure superpositions, contiguous simply connected regions, regular periods≥3. Keep these restrictions and do not infer full kernel coverage.

### 6.10 Corollary: Regular G-injective zero-order entropy

**Partial**. [Source lines 2074–2082](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2074-L2082).

- Lean: [`IsGInjective.torusPhysicalCut_rank_zeroEntropy_of_isSimplyConnected`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/RegularGInjectiveSimplyConnectedEntropy.lean#L188).
- Blueprint: [`thm:peps_regular_ginjective_simply_connected_entropy`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_regular_ginjective_simply_connected_entropy.tex#L2).
- Issue owner: [#8675](https://github.com/LionSR/TNLean/issues/8675).

Physical invertible transport gives rank and zero-order entropy for regular closure states under the region/period restrictions. It does not preserve flatness or other entropy orders.

### 6.11 Lemma: MPS local projector formula

**Corrected**. [Source lines 2098–2109](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2098-L2109).

- Lean: [`IsGIsometricMPS.parentInteraction_regularMPSTensor`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GIsometricParentHamiltonian.lean#L336).
- Blueprint: [`thm:peps_mps_g_isometric_local_terms`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L1219).
- Issue owner: [#8464](https://github.com/LionSR/TNLean/issues/8464).

The printed operator is the projector onto S₂, while the parent interaction is its complement; positive normalization factor is explicit.

### 6.12 Theorem: Commuting PEPS parents

**Partial**. [Source lines 2131–2135](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2131-L2135).

- Lean: [`IsGIsometricMPS.isNNCPH_regularMPSTensor`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GIsometricParentHamiltonian.lean#L373).
- Blueprint: [`thm:peps_mps_g_isometric_commuting`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L1249).
- Issue owner: [#8464](https://github.com/LionSR/TNLean/issues/8464).

MPS N≥3 proved. Actual overlapping 2×2 PEPS plaquette commutation is the reopened target; not proved by the MPS result.

### 6.13 Definition: Fluxon strings and endpoint type

**Partial**. [Source lines 2174–2197](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2174-L2197).

- Lean: [`torusPlaquetteSideInsertion`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusPlaquetteFluxMeasurement.lean#L328).
- Blueprint: [`def:peps_torus_plaquette_all_sides_insertion`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_torus_plaquette_flux_measurement.tex#L134).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Actual bond insertions and physical contractions are defined. Four attachment sides use periods≥3; the adjacent opposite-holonomy realization uses width≥4,height≥3. A general arbitrary open-string definition with the entire endpoint/type characterization is not supplied by these specific realizations.

### 6.14 Lemma: String deformation

**Partial**. [Source lines 2199–2204](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2199-L2204).

- Lean: [`torusBondNetwork_westSouthOperatorString_eq`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusOperatorString.lean#L368).
- Blueprint: [`thm:peps_torus_operator_string_deformation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex#L1384).
- Issue owner: [#8272](https://github.com/LionSR/TNLean/issues/8272).

Exact rectangle-boundary deformation and arbitrary constant vertex-patch gauge equality are proved. Closed issue8272 deliberately covers the rectangle statement. General endpoint-fixed path deformation and local unobservability are not its conclusion.

### 6.15 Theorem: Plaquette flux detection

**Partial**. [Source lines 2216–2220](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2216-L2220).

- Lean: [`IsGIsometric.exists_torusPlaquette_holonomy_cutMeasurement`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusPlaquetteFluxMeasurement.lean#L238).
- Blueprint: [`thm:peps_torus_plaquette_holonomy_measurement`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_torus_plaquette_flux_measurement.tex#L51).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Complete positive orthogonal PVM on the four original spins detects every inserted-bond holonomy class, with regular G-isometry and periods≥3; group-inserted closed states are separately proved nonzero. Remaining scope is unrestricted string/geometry interpretation, not physical detector transport.

### 6.16 Theorem: Physical flux motion

**Partial**. [Source lines 2270–2273](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2270-L2273).

- Lean: [`IsGIsometric.exists_unitary_torusVacantPlaquetteMove`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusVacantPlaquettePhysicalMove.lean#L87).
- Blueprint: [`thm:peps_vacant_plaquette_physical_move`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_actual_route_flux_move.tex#L102).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Actual state-independent six-spin horizontal motion including seams is proved for width≥4,height≥3; four-direction vacant-neighbor motion for arbitrary inserted inputs is proved for width≥8,height≥7. Retain the target-vacancy condition and finite native geometry.

### 6.17 Theorem: Physical flux-pair creation

**Partial**. [Source lines 2304–2316](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2304-L2316).

- Lean: [`IsGIsometric.exists_unitary_torusTranslatedGlobalFluxCreation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusTranslatedFluxCreation.lean#L181).
- Blueprint: [`thm:peps_torus_translated_flux_creation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_torus_translated_flux_creation.tex#L33).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Actual six-spin unitary creates the coherent opposite-flux pair uniformly in boundary/exterior assignments for width≥4,height≥3. Required normalization is (|G||C_G(g)|)^(-1/2); the source displays an unnormalized sum. Unrestricted geometry is not proved.

### 6.18 Definition: Electric charge insertion

**Complete**. [Source lines 2432–2446](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2432-L2446).

- Lean: [`regularEdgeCharacterSite`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/RegularEdgeChargeContraction.lean#L74).
- Blueprint: [`def:peps_regular_edge_charge_contraction`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_regular_edge_charge_contraction.tex#L2).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

The actual shared bond receives χ(pk). regularChargeMatrix proves the accessible matrix equals the source character-weighted sum. Arbitrary characters include the irreducible case. This is definition-level coverage, not nonvanishing of an isolated charge in a closed vacuum.

### 6.19 Theorem: Physical charge detection

**Partial**. [Source lines 2449–2453](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2449-L2453).

- Lean: [`exists_regularEdgePhysicalAllChargeMeasurement`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/RegularEdgePhysicalChargeMeasurement.lean#L27).
- Blueprint: [`thm:peps_regular_edge_physical_charge_measurement`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_regular_edge_physical_charge_measurement.tex#L2).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

One complete two-spin PVM on a finite simple graph is chosen before every irreducible label, internal parameter, boundary and exterior tensor family; only endpoint tensors require regular G-isometry. Torus periods≥3 include seams. Local columns are nonzero; unrestricted boundaries and arbitrary exterior-contraction nonvanishing are not asserted.

### 6.20 Theorem: Independent two-column charge motion

**Partial**. [Source lines 2483–2485](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2483-L2485).

- Lean: [`IsGIsometric.exists_unitary_torusTwoColumnChargeMotion`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusTwoColumnChargeMotion.lean#L114).
- Blueprint: [`thm:peps_torus_two_column_charge_motion`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_two_column_charge_motion.tex#L172).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

The actual source two-column factorization is proved: independent regional unitaries, uniform before χ,p and boundary labels, on translated plaquettes including seams with periods≥3. The generic theorem covers two disjoint connected finite regions. These are open-column identities, not an unrestricted lattice/global-motion theorem.

### 6.21 Theorem: Physical charge-pair creation

**Partial**. [Source lines 2510–2519](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2510-L2519).

- Lean: [`IsGIsometric.exists_unitary_torusPhysicalChargePairCreation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/TorusPhysicalChargePairCreation.lean#L51).
- Blueprint: [`thm:peps_torus_physical_charge_pair_creation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_regular_physical_charge_pair_creation.tex#L110).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Literal χ(ph⁻¹g) coefficient, physical two-bond contraction, unitary preparation and χ/contragredient endpoint readout are proved. Native width≥3,height≥4 six-spin geometry is derived; generic connected-region preparation uses two distinct internal bonds. Unrestricted lattice/global excitation-membership scope remains.


## Section 7 unnumbered constructions

These eight audit rows group construction claims; they are not source-numbered declarations and are not included in the count of 51. Overlapping source ranges reflect a construction and its consequences.

### 7.A Kitaev checkerboard Hamiltonian and projection preparation

**Open**. [Source lines 2636–2731](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2636-L2731).

- Lean: [`kitaevElementaryTensor`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/KitaevCheckerboardBlocking.lean).
- Blueprint: [`def:peps_kitaev_checkerboard_tensor`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_kitaev_checkerboard_blocking.tex).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

The elementary tensor coefficient is implemented for both checkerboard orientations. The full commuting A/B stabilizer Hamiltonian, projection-circuit-to-tensor derivation, and preparation from the all-zero state are not established by that definition. The printed Hamiltonian/projector normalization also requires a separate source check.

### 7.B Binary blocking and boundary CNOT factorization

**Partial**. [Source lines 2732–2857](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2732-L2857).

- Lean: [`kitaevNativeCheckerboardMatrix_mul_boundaryCNOT`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/KitaevNativeBoundaryCNOT.lean).
- Blueprint: [`thm:peps_kitaev_native_boundary_cnot`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_kitaev_native_boundary_cnot.tex).
- Issue owner: [#8676](https://github.com/LionSR/TNLean/issues/8676).

Exact local B C = K E† tensor-map identity and cyclic physical reordering are proved, including native seam geometry for periods≥3. No physical RG unitary or globally tiled alternating checkerboard state follows; odd-torus checkerboard consistency is not assumed.

### 7.C Quantum-double color-difference tensor and local G-isometry

**Corrected**. [Source lines 2858–2918](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2858-L2918).

- Lean: [`isGIsometric_quantumDoubleDualTensor`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/Examples/QuantumDouble.lean).
- Blueprint: [`thm:peps_quantum_double_dual_g_isometric`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex).
- Issue owner: [#8039](https://github.com/LionSR/TNLean/issues/8039).

The actual K tensor is G-injective and G-isometric with factor |G|, using explicit right-shift/orientation conventions equivalent to the regular source convention. The nonabelian unblocked T-to-K global RG construction is separate.

### 7.D Quantum-double parent Hamiltonian identification

**Open**. [Source lines 2919–2937](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2919-L2937).

- Lean: [`regionParentHamiltonian`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/ParentHamiltonian/RegionParentHamiltonian.lean).
- Blueprint: [`def:peps_region_parent_hamiltonian`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_region_parent_hamiltonian.tex).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

The general region-parent framework exists, but no complete identification of the three source Hamiltonian components with the stated quantum-double construction was located. This is distinct from generic plaquette commutation under #8464.

### 7.E Color-pattern contraction and Gauss-law interpretation

**Corrected**. [Source lines 2913–2937](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2913-L2937).

- Lean: [`stateCoeff_quantumDoubleDualPEPS`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/Examples/QuantumDouble.lean).
- Blueprint: [`thm:peps_quantum_double_dual_gauss_law`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_examples.tex).
- Issue owner: [#8238](https://github.com/LionSR/TNLean/issues/8238).

For periods≥3 the coefficient is |G| on Gauss-law configurations with trivial row and column holonomy and zero otherwise. On a torus this is not all Gauss-law configurations: the holonomy qualification is necessary, not an omitted proof.

### 7.F Multiplicity-one representation and fourth-root-weighted tensor

**Complete**. [Source lines 2938–2980](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2938-L2980).

- Lean: [`exists_minimalSemiRegular_leftRegular_fourier`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/RegularMinimalRepresentation.lean).
- Blueprint: [`thm:peps_regular_minimal_representation`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_regular_minimal_representation.tex).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

The irreducible/Fourier data are derived from the finite group; the single-copy representation is semi-regular. isGInjective_blockFourthRootWeight in TorusWeightedSiteGInjective proves the actual weighted tensor G-injective. Theta normalizations are explicit rather than copied from an unnormalized diagram.

### 7.G Printed multiplicity-restoring bond isometry

**Complete**. [Source lines 2982–3019](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2982-L3019).

- Lean: [`multiplicityBondMap_sqrt_smul`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/SemiRegularBondIsometry.lean).
- Blueprint: [`thm:peps_multiplicity_bond_weight`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_semiregular_bond_isometry.tex).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

The map X↦d^(-1/2) X⊗I is an isometry and carries the weighted block to the repeated block. Full-domain extensions and product-bond isometries are also implemented.

### 7.H Actual reduced-bond state equivalence and minimality

**Partial**. [Source lines 2969–3019](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/Papers/1001.3807/paper_v3.tex#L2969-L3019).

- Lean: [`exists_isometric_minimalSemiRegular_graphState`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/TNLean/PEPS/GraphSemiRegularEquivalence.lean).
- Blueprint: [`thm:peps_graph_minimal_semiregular_equivalence`](https://github.com/LionSR/TNLean/blob/680b30da6fec94f5b269c3753ab4b8c86da79936/blueprint/src/chapter/ch24_peps_graph_semiregular_equivalence.tex).
- Issue owner: [#8271](https://github.com/LionSR/TNLean/issues/8271).

Strong proved scope: every closed finite simple graph, without connectivity; includes isolated vertices and the empty graph. Representation/Fourier witnesses and the product of full-domain physical bond isometries are derived. The theorem proves dimensions |G|=∑dᵢ² and ∑dᵢ, universal semi-regular minimality, strict reduction iff noncommutative, and nonvanishing. GraphInsertedSemiRegularFactory supplies one isometry uniform in all closed group insertions. Open scope: dangling boundaries, parallel edges, self-loops/infinite contractions, arbitrary sector-mixing inserted matrices, and parent-Hamiltonian equivalence. It is not merely a conditional torus lemma.
