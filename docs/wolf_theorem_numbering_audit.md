# Wolf theorem-number audit

This table records the verification of live numbered references to theorem-like
results in M. Wolf, *Quantum Channels & Operations: Guided Tour*. The printed
chapter PDFs in `Notes/WolfNotePDF/` determine the numbers. The searchable
transcriptions in `Notes/WolfNoteTexSource/` locate the corresponding statements
but do not determine their numbering.

Dated historical audits, review records, and slides are outside the scope of
this table. Repeated references to the same result within one file are recorded
once below.

## Chapter 1: (De)constructing quantum mechanics

All seven cited Chapter 1 numbers agree with the printed notes. The PDF page in
the table is the page number within the archived chapter PDF; the printed page
number is the number displayed on that page.

| Citation | Result title | Archived PDF | Local transcription | Verdict |
|---|---|---:|---:|---|
| Proposition 1.1 | Schmidt decomposition | PDF page 7; printed page 13 | lines 195--205 | Correct |
| Theorem 1.1 | Wigner's theorem | PDF page 10; printed page 16 | lines 279--285 | Correct |
| Corollary 1.1 | Spectrum preserving maps | PDF page 11; printed page 17 | lines 289--291 | Correct |
| Proposition 1.3 | Quantum steering | PDF page 13; printed page 19 | lines 348--353 | Correct |
| Proposition 1.5 | Conditional expectations | PDF page 23; printed page 29 | lines 547--555 | Correct |
| Proposition 1.6 | Complete positivity from positivity | PDF page 25; printed page 31 | lines 600--602 | Correct |
| Proposition 1.7 | Extending cp maps from operator systems | PDF page 26; printed page 32 | lines 616--618 | Correct |

No live citation to Proposition 1.2 or Proposition 1.4 occurs in the directories
examined here.

### Citing files

**Proposition 1.1**

- `TNLean/Channel/SchmidtDecomposition.lean`
- `blueprint/src/chapter/ch12_auxiliary_wolf_ch01_states.tex`

**Theorem 1.1**

- `TNLean/Channel/Wigner/Rigidity.lean`

**Corollary 1.1**

- `TNLean/Channel/TransferMatrix.lean`

**Proposition 1.3**

- `TNLean/Channel/QuantumSteering.lean`

**Proposition 1.5**

- `TNLean/Channel/DirectSumConditionalExpectation.lean`
- `TNLean/Channel/FixedPoint/ConditionalExpectation.lean`
- `TNLean/Channel/FixedPoint/TraceAdjointDensityBlocks.lean`
- `TNLean/Channel/PositiveConditionalExpectation.lean`
- `TNLean/Channel/PositiveConditionalExpectationDirectSum.lean`
- `TNLean/Channel/PositiveFunctional.lean`
- `TNLean/Channel/RightFactorConditionalExpectation.lean`
- `TNLean/Channel/StarSubalgebraConditionalExpectation.lean`
- `TNLean/Channel/WolfChapter6Index.lean`
- `blueprint/src/chapter/ch05_schwarz_retractions_and_peripheral_equality.tex`
- `blueprint/src/chapter/ch12_auxiliary_wolf_ch01_positive_maps.tex`
- `docs/paper-gaps/cpsv16_vertical_sector_invertibility.tex`
- `docs/paper-gaps/wolf_prop1_5_one_factor_scope.tex`
- `docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`

**Proposition 1.6**

- `TNLean/Channel/Schwarz/PositiveOnAbelian.lean`
- `TNLean/Channel/Schwarz/PositiveOnAbelian/Basic.lean`
- `TNLean/Channel/Schwarz/PositiveOnAbelian/Characterization.lean`
- `TNLean/Channel/Schwarz/PositiveOnAbelian/CompletePositivity.lean`
- `TNLean/Channel/Schwarz/PositiveOnAbelian/Consequences.lean`
- `TNLean/Channel/Schwarz/SchwarzNormal.lean`
- `blueprint/src/chapter/ch12_auxiliary_wolf_ch01_positive_maps.tex`
- `blueprint/src/chapter/ch18_operator_convexity_schwarz_and_jensen.tex`
- `docs/paper-gaps/wolf_ch5_operator_jensen_lieb.tex`
- `docs/paper-gaps/wolf_prop16_cp_positivity_commutative_side.tex`

**Proposition 1.7**

- `docs/paper-gaps/wolf_ch5_operator_jensen_lieb.tex`

### Reproducibility

The enumeration searches `TNLean/`, `blueprint/src/`, and `docs/` for the
words `Theorem`, `Proposition`, `Corollary`, `Lemma`, and their abbreviations
followed by a number of the form `m.n`, where `m` is the chapter under audit.
It excludes `docs/audits/`,
`docs/archive/`, `docs/reviews/`, `docs/slides/`,
`docs/wolf_theorem_numbering_audit.md`, and `blueprint/comments/`.
Each result-level file list above was then checked against the matching printed
statement in `Notes/WolfNotePDF/ch01_deconstructing_quantum.pdf`.

## Chapter 2: Representations of quantum channels

The Chapter 2 audit is in progress. The corrections below concern the unitary
freedom of Kraus representations and the transfer-matrix documentation.

### Kraus-representation freedom

| Former citation | Printed citation | Result | Archived PDF | Local transcription | Verdict |
|---|---|---|---:|---:|---|
| Theorem 2.18 | Theorem 2.1(4), with Equation (2.10) | Kraus representation: freedom of the Kraus family | PDF pages 4--5; printed pages 36--37 | lines 229--253; item (4) at lines 249--251; Equation (2.10) at lines 277--284 | Corrected |

The printed chapter has no Theorem 2.18. Equation (2.18), on printed page 41,
defines a weighted Hilbert--Schmidt scalar product and is unrelated to Kraus
freedom.

### Files corrected for Theorem 2.1(4)

- `TNLean/Channel/KrausUnitaryFreedom.lean`
- `TNLean/Channel/WolfChapter2Index.lean`
- `TNLean/MPS/Periodic/Applications.lean`
- `TNLean/MPS/Periodic/Symmetry/Theorem41Forward.lean`
- `TNLean/MPS/Periodic/Symmetry/Theorem41Reverse.lean`
- `TNLean/MPS/Symmetry/StringOrderDefs.lean`

### Transfer matrices and normal forms

The printed notes place linear maps as matrices in Section 2.3 and normal forms
in Section 2.4. Several former references assigned elementary transfer-matrix
identities to Propositions 2.5–2.8, but those propositions have different
statements.

| Former citation | Printed result | Archived PDF | Local transcription | Verdict |
|---|---|---:|---:|---|
| Proposition 2.5 | Environment-induced instruments | PDF page 8; printed page 40 | lines 447–456 | Removed from transfer-matrix criteria |
| Proposition 2.6 | Self-dual channels | PDF page 10; printed page 42 | lines 578–600 | Removed from transfer-matrix criteria |
| Proposition 2.7 | SIC POVMs | PDF page 14; printed page 46 | lines 790–800 | Removed from unitary-conjugation identities |
| Proposition 2.8 | Generic normal form for a positive-definite Choi matrix | PDF page 16; printed page 48 | lines 894–899 | Removed from unitary-conjugation identities |
| Proposition 2.11 | Lorentz normal form for qubit channels | PDF page 18; printed page 50 | lines 1021–1035 | Retained for the actual qubit theorem |

The transfer-matrix criteria are entrywise consequences of Equation (2.20),
at lines 560–576, rather than numbered propositions. The unitary-conjugation
formula is the arbitrary-dimensional matrix-unit analogue of the qubit
Pauli-transfer discussion at lines 1000–1010. The ordinary complex SVD of an
arbitrary invertible transfer matrix is a general linear-algebraic result; it
is not the real SVD of the qubit `3 × 3` block discussed in that passage.

### Files corrected

- `TNLean/Channel/TransferMatrix.lean`
- `TNLean/Channel/WolfChapter2Index.lean`
- `TNLean/Channel/NormalForm.lean`
- `TNLean/Channel/LorentzNormalForm.lean`
- `TNLean/Channel/LorentzNormalForm/Basic.lean`
- `TNLean/Channel/LorentzNormalForm/Infimum.lean`
- `TNLean/Channel/LorentzNormalForm/NormalForm.lean`
- `TNLean/Channel/LorentzNormalForm/QubitNormalForm.lean`
- `TNLean/Algebra/MatrixAux.lean`
- `TNLean/Analysis/MatrixTraceInequalities.lean`
- `blueprint/src/chapter/ch16_channel_representations_normal_forms_and_determinant.tex`

## Chapter 3: Positive, but not completely positive

The first five live theorem citations agree with the printed notes. Two later
citations used numbers from a divergent transcription counter: the printed
numbers are Proposition 3.6 for automorphisms of the positive semidefinite cone
and Proposition 3.7 for the Lorentz-cone trace inequalities.

| Former citation | Printed citation | Result title | Archived PDF | Local transcription | Verdict |
|---|---|---|---:|---:|---|
| Proposition 3.1 | Proposition 3.1 | Choi--Jamiołkowski criterion for n-positive maps | PDF page 2; printed page 54 | lines 89--98 | Correct |
| Lemma 3.1 | Lemma 3.1 | Maximal overlap with fixed Schmidt rank | PDF page 3; printed page 55 | lines 119--128 | Correct |
| Proposition 3.2 | Proposition 3.2 | Spectral criterion for n-positivity | PDF page 4; printed page 56 | lines 153--164 | Correct |
| Proposition 3.3 | Proposition 3.3 | Entanglement witnesses | PDF page 5; printed page 57 | lines 229--233 | Correct |
| Proposition 3.4 | Proposition 3.4 | Positive maps and entanglement | PDF page 5; printed page 57 | lines 250--253 | Correct |
| Proposition 3.8 | Proposition 3.6 | Automorphisms and rank-preserving maps | PDF page 13; printed page 65 | lines 652--660 | Corrected |
| Proposition 3.9 | Proposition 3.7 | Confining Lorentz cones | PDF page 14; printed page 66 | lines 693--699 | Corrected |
| Example 3.1 | Example 3.1 | Positive maps and entanglement witnesses | PDF pages 6--8; printed pages 58--60 | lines 307--400 | Correct |

The citation “Example 3.1 (Proposition 3.2)” attached to the reduction-map
positivity theorem has two distinct roles and is retained. Example 3.1 states
the reduction-map family, whereas Proposition 3.2 supplies the spectral
criterion used to establish its positivity threshold.

### Citing files

**Proposition 3.1**

- `TNLean/Channel/NPositivitySpectralCriterion.lean`
- `TNLean/Channel/SchmidtRank.lean`
- `TNLean/Channel/Schwarz/ChoiCompression.lean`
- `TNLean/Channel/Schwarz/TwoPositive.lean`
- `blueprint/src/chapter/ch25_positive_not_cp_npositivity_infimum.tex`
- `blueprint/src/chapter/ch25_positive_not_cp_two_positive_schmidt_and_choi.tex`
- `docs/paper-gaps/wolf_prop_3_2_schmidt_rank_reading.tex`
- `docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`

**Lemma 3.1**

- `TNLean/Analysis/KyFanNorm.lean`
- `TNLean/Channel/MaximalOverlap.lean`
- `TNLean/Channel/NPositivityChainStrict.lean`
- `TNLean/Channel/NPositivitySpectralCriterion.lean`
- `TNLean/Channel/SchmidtRank.lean`
- `blueprint/src/chapter/ch25_positive_not_cp_two_positive_schmidt_and_choi.tex`
- `docs/paper-gaps/wolf_lemma_3_1_top_index_scope.tex`
- `docs/paper-gaps/wolf_t_eta_top_index_scope.tex`

**Proposition 3.2**

- `TNLean/Channel/NPositivityChainStrict.lean`
- `TNLean/Channel/NPositivitySpectralCriterion.lean`
- `TNLean/Channel/ReductionCriterion.lean`
- `blueprint/src/chapter/ch25_positive_not_cp_npositivity_infimum.tex`
- `blueprint/src/chapter/ch25_positive_not_cp_two_positive_schmidt_and_choi.tex`
- `docs/paper-gaps/wolf_lemma_3_1_top_index_scope.tex`
- `docs/paper-gaps/wolf_prop_3_2_schmidt_rank_reading.tex`
- `docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`

**Proposition 3.3**

- `TNLean/Algebra/MatrixRankClosed.lean`
- `TNLean/Channel/EntanglementWitness.lean`
- `TNLean/Channel/PositiveMapDetection.lean`
- `TNLean/Channel/SchmidtNumber.lean`
- `TNLean/Channel/SchmidtNumberCompact.lean`
- `blueprint/src/appendix/full_only/ch25_schmidt_number_and_witnesses.tex`
- `blueprint/src/chapter/ch25_positive_not_cp_schmidt_number_and_entanglement.tex`

**Proposition 3.4**

- `TNLean/Channel/PositiveMapDetection.lean`
- `TNLean/Channel/SchmidtNumber.lean`
- `TNLean/Channel/SchmidtNumberFactors.lean`
- `TNLean/Channel/Separable.lean`
- `blueprint/src/appendix/full_only/ch25_schmidt_number_and_witnesses.tex`
- `blueprint/src/chapter/ch25_positive_not_cp_schmidt_number_and_entanglement.tex`

**Proposition 3.6**

- `TNLean/Channel/TransferMatrix.lean`
- `blueprint/src/chapter/ch25_positive_not_cp_positivity_reduction_and_breuer_hall.tex`

**Proposition 3.7**

- `TNLean/Analysis/MatrixTraceInequalities.lean`
- `blueprint/src/chapter/ch25_positive_not_cp_trace_normalization_and_lorentz_cone.tex`
- `docs/paper-gaps/wolf_ch3_lorentz_cone_trace_sign.tex`
- `docs/paper-gaps/wolf_lecture_notes_errata.tex`

**Example 3.1**

- `TNLean/Algebra/HermitianHelpers.lean`
- `TNLean/Channel/BreuerHallIndecomposable.lean`
- `TNLean/Channel/BreuerHallMap.lean`
- `TNLean/Channel/ChoiTypeMap.lean`
- `TNLean/Channel/PartialTranspose.lean`
- `TNLean/Channel/PositiveExamples.lean`
- `TNLean/Channel/ReductionCriterion.lean`
- `TNLean/Channel/SchmidtNumber.lean`
- `TNLean/Channel/SchmidtNumberFactors.lean`
- `TNLean/Channel/Separable.lean`
- `blueprint/src/chapter/ch25_positive_not_cp_choi_and_decomposable_maps.tex`
- `blueprint/src/chapter/ch25_positive_not_cp_positivity_reduction_and_breuer_hall.tex`
- `docs/paper-gaps/README.md`
- `docs/paper-gaps/breuer_hall_even_dim_restriction.tex`
- `docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`

### Reproducibility

The enumeration uses the same directories and exclusions as the Chapter 1
audit. Each result was checked against
`Notes/WolfNotePDF/ch03_positive_not_completely.pdf`; the line ranges above
refer only to the searchable transcription and do not determine numbering.

## Chapter 5: Operator inequalities

The printed chapter confirms all live Chapter 5 numbers except the former
operator-Jensen references to Theorem 5.1. In the printed notes, Theorem 5.1
is Douglas' theorem. The subunital Jensen inequality for convex powers is a
case of Theorem 5.11, and the corresponding inequality for concave powers is
a case of Theorem 5.13.
The logarithm inequality is Corollary 5.2(3).

| Former citation | Printed citation | Result title | Archived PDF | Local transcription | Verdict |
|---|---|---|---:|---:|---|
| Theorem 5.1 | Theorem 5.11 | Projection inequality from operator convexity | PDF page 9; printed page 81 | lines 627--655 | Corrected |
| Theorem 5.1 | Theorem 5.13 | Operator monotonicity and positive maps | PDF page 11; printed page 83 | lines 714--759 | Corrected |
| Theorem 5.1 | Corollary 5.2(3) | Logarithm inequality for positive maps | PDF page 11; printed page 83 | lines 761--768 | Corrected with unital local fix |
| Theorem 5.2 | Theorem 5.2 | Block matrices and Schur complements | PDF page 2; printed page 74 | lines 103--118 | Correct |
| Theorem 5.3 | Theorem 5.3 | Operator Schwarz inequality | PDF page 3; printed page 75 | lines 180--196 | Correct |
| Proposition 5.1 | Proposition 5.1 | Schwarz inequality for commutative domains | PDF page 4; printed page 76 | lines 245--260 | Correct |
| Theorem 5.5 | Theorem 5.5 | Schwarz inequality for subnormal operators | PDF page 4; printed page 76 | lines 282--309 | Correct |
| Theorem 5.6 | Theorem 5.6 | Schwarz inequality for commuting dominant operators | PDF page 5; printed page 77 | lines 311--323 | Correct |
| Theorem 5.7 | Theorem 5.7 | Multiplicative domains | PDF page 6; printed page 78 | lines 399--407 | Correct |
| Theorem 5.10 | Theorem 5.10 | Operator convexity from the projection inequality | PDF page 8; printed page 80 | lines 575--625 | Correct |
| Theorem 5.11 | Theorem 5.11 | Projection inequality from operator convexity | PDF page 9; printed page 81 | lines 627--655 | Correct |
| Theorem 5.12 | Theorem 5.12 | Operator convexity and unital positive maps | PDF page 10; printed page 82 | lines 657--697 | Correct |
| Theorem 5.13 | Theorem 5.13 | Operator monotonicity and positive maps | PDF page 11; printed page 83 | lines 714--759 | Correct |
| Corollary 5.2 | Corollary 5.2 | Power and logarithm inequalities for positive subunital maps | PDF page 11; printed page 83 | lines 761--777 | Correct |
| Theorem 5.15 | Theorem 5.15 | Ando--Lieb joint concavity and convexity | PDF page 14; printed page 86 | lines 967--991 | Correct |
| Theorem 5.17 | Theorem 5.17 | Convex functions and positive maps under the trace | PDF page 16; printed page 88 | lines 1039--1083 | Correct |
| Example 5.3 | Example 5.3 | A Schwarz map which is not 2-positive | PDF page 5; printed page 77 | lines 354--378 | Correct |

The corrected rows distinguish the conclusions that had formerly been
assigned collectively to Theorem 5.1. For a positive subunital map,
Theorem 5.11 gives Jensen's inequality for an operator-convex function with
nonpositive value at zero. Theorem 5.13 gives the reversed inequality for an
operator-monotone function with nonnegative value at zero. These apply,
respectively, to powers with exponent in `[1, 2]` and powers with exponent in
`[0, 1]`. The logarithm inequality is Corollary 5.2(3). Its printed subunital
form is false because the logarithm is unbounded below at zero, so the Lean
theorem uses the necessary unital hypothesis, as documented in
`docs/paper-gaps/wolf_ch5_operator_jensen_lieb.tex`.

### Citing files

**Theorem 5.2**

- `TNLean/Channel/Schwarz/SchurComplement.lean`
- `TNLean/Channel/Schwarz/TwoVariable.lean`
- `TNLean/Channel/Schwarz/TwoVariableUnconditional.lean`
- `blueprint/src/chapter/ch05_schwarz_schur_complement.tex`
- `docs/paper-gaps/schur_complement_tfae.tex`

**Theorem 5.3**

- `TNLean/Channel/Peripheral/ClosureFixedPointKraus.lean`
- `TNLean/Channel/Schwarz/TwoVariable.lean`
- `TNLean/Channel/Schwarz/TwoVariableEquality.lean`
- `TNLean/Channel/Schwarz/TwoVariableUnconditional.lean`
- `blueprint/src/chapter/ch07_spectral_mixed_transfer_and_overlap.tex`
- `docs/paper-gaps/wolf_ch5_two_variable_unconditional.tex`

**Proposition 5.1**

- `TNLean/Channel/Schwarz/PositiveOnAbelian.lean`
- `TNLean/Channel/Schwarz/PositiveOnAbelian/Basic.lean`
- `TNLean/Channel/Schwarz/PositiveOnAbelian/Consequences.lean`
- `TNLean/Channel/Schwarz/SchwarzNormal.lean`
- `TNLean/Channel/Schwarz/SchwarzSubnormal.lean`
- `blueprint/src/chapter/ch18_operator_convexity_schwarz_and_jensen.tex`

**Theorems 5.5 and 5.6**

- `TNLean/Channel/Schwarz/SchwarzSubnormal.lean`
- `blueprint/src/chapter/ch18_operator_convexity_schwarz_and_jensen.tex`

**Theorem 5.7**

- `TNLean/Channel/Schwarz/MultiplicativeDomain.lean`
- `TNLean/Channel/Schwarz/MultiplicativeDomainFull.lean`
- `blueprint/src/chapter/ch05_schwarz_abstract_domains_and_order_auxiliary.tex`

**Theorems 5.10--5.13 and Corollary 5.2**

- `TNLean/Analysis/LiebConcavity.lean`
- `TNLean/Channel/Schwarz/OperatorConvexity.lean`
- `TNLean/Channel/Schwarz/OperatorJensenAux.lean`
- `TNLean/Channel/Schwarz/OperatorMonotone.lean`
- `blueprint/src/chapter/ch18_operator_convexity.tex`
- `blueprint/src/chapter/ch18_operator_convexity_schwarz_and_jensen.tex`
- `docs/paper-gaps/wolf_ch5_operator_jensen_lieb.tex`

**Theorem 5.15**

- `TNLean/Analysis/LiebConcavity.lean`
- `TNLean/Analysis/LiebSubBoundary.lean`
- `blueprint/src/chapter/ch18_operator_convexity_lieb_and_resolvent.tex`
- `docs/paper-gaps/wolf_ch5_operator_jensen_lieb.tex`

**Theorem 5.17**

- `TNLean/Analysis/OperatorConvexity.lean`

**Example 5.3**

- `TNLean/Channel/Schwarz/SchwarzNotCP.lean`
- `blueprint/src/chapter/ch05_schwarz_abstract_domains_and_order_auxiliary.tex`
- `blueprint/src/chapter/ch27_channel_asymptotics_fixed_point_algebras.tex`
- `docs/paper-gaps/wolf_lecture_notes_errata.tex`
- `docs/paper-gaps/wolf_thm6_12_abstract_schwarz_fixed_points.tex`

### Reproducibility

The enumeration uses the same directories and exclusions as the Chapter 1
audit, and also checks grouped citations such as “Theorems 5.10--5.13”. Each
result was checked against
`Notes/WolfNotePDF/ch05_operator_inequalities.pdf`; the line ranges above refer
only to the searchable transcription and do not determine numbering.

## Chapter 7: Semigroup structure

All eleven cited Chapter 7 numbers agree with the printed notes.

| Citation | Result title | Archived PDF | Local transcription | Verdict |
|---|---|---:|---:|---|
| Proposition 7.1 | From continuous semigroups to differentiable groups | PDF page 2; printed page 120 | lines 67--69 | Correct |
| Lemma 7.1 | No printed title | PDF page 3; printed page 121 | lines 113--118 | Correct |
| Corollary 7.1 | Perturbation of generators | PDF page 4; printed page 122 | lines 135--141 | Correct |
| Proposition 7.2 | Conditional complete positivity | PDF page 4; printed page 122 | lines 158--170 | Correct |
| Proposition 7.3 | Completely positive dynamical semigroups | PDF page 5; printed page 123 | lines 195--201 | Correct |
| Proposition 7.4 | Freedom in representation of generators | PDF page 6; printed page 124 | lines 223--236 | Correct |
| Theorem 7.1 | Generators for semigroups of quantum channels | PDF page 7; printed page 125 | lines 245--256 | Correct |
| Proposition 7.5 | Irreducibility implies primitivity | PDF page 7; printed page 125 | lines 268--277 | Correct |
| Proposition 7.6 | Reducible quantum dynamical semigroups | PDF page 8; printed page 126 | lines 285--296 | Correct |
| Corollary 7.2 | Necessary conditions for relaxation | PDF page 9; printed page 127 | lines 313--320 | Correct |
| Theorem 7.2 | Kernel of the Liouvillian | PDF page 10; printed page 128 | lines 332--338 | Correct |

### Citing files

**Proposition 7.1**

- `TNLean/Channel/Semigroup/Basic.lean`
- `blueprint/src/chapter/ch17_semigroup_dynamics_and_gksl.tex`

**Lemma 7.1 and Corollary 7.1**

- `TNLean/Channel/Semigroup/Perturbation.lean`
- `blueprint/src/chapter/ch17_semigroup_dynamics_and_gksl.tex`

**Proposition 7.2**

- `TNLean/Channel/Semigroup/GeneratorDefs.lean`
- `TNLean/Channel/Semigroup/LindbladForm/ChoiCCP.lean`
- `TNLean/Channel/Semigroup/LindbladForm/EulerStep.lean`
- `blueprint/src/chapter/ch17_semigroup_dynamics_and_gksl.tex`

**Proposition 7.3**

- `TNLean/Channel/Semigroup/LindbladForm/EulerStep.lean`
- `blueprint/src/chapter/ch17_semigroup_dynamics_and_gksl.tex`

**Proposition 7.4**

- `TNLean/Channel/Semigroup/LindbladForm/GKSLTheorem.lean`
- `TNLean/Channel/Semigroup/LindbladForm/Uniqueness.lean`
- `blueprint/src/chapter/ch17_semigroup_dynamics_and_gksl.tex`

**Theorem 7.1**

- `TNLean/Channel/Semigroup/KossakowskiForm.lean`
- `TNLean/Channel/Semigroup/LindbladForm/GKSLTheorem.lean`
- `blueprint/src/chapter/ch17_semigroup_dynamics_and_gksl.tex`

**Proposition 7.5**

- `TNLean/Channel/Semigroup/Primitivity/Basic.lean`
- `TNLean/Channel/Semigroup/Primitivity/IrreducibleAnalysis.lean`
- `TNLean/Channel/Semigroup/Primitivity/MainTheorem.lean`
- `blueprint/src/chapter/ch17_semigroup_dissipation_and_primitivity.tex`

**Proposition 7.6**

- `TNLean/Channel/Semigroup/ReducibleQDS/Defs.lean`
- `TNLean/Channel/Semigroup/ReducibleQDS/Equivalence.lean`
- `TNLean/Channel/Semigroup/ReducibleQDS/FixedDensity.lean`
- `TNLean/Channel/Semigroup/ReducibleQDS/GeneratorCompression.lean`
- `TNLean/Channel/Semigroup/ReducibleQDS/SubsequenceAnalysis.lean`
- `blueprint/src/chapter/ch17_semigroup_adjoint_kernel_and_reducibility.tex`
- `docs/blueprint_style_guide.md`

**Corollary 7.2**

- `TNLean/Channel/Semigroup/ReducibleQDS/GeneratorCompression.lean`
- `TNLean/Channel/Semigroup/RelaxationConditions.lean`
- `blueprint/src/chapter/ch17_semigroup_adjoint_kernel_and_reducibility.tex`
- `docs/blueprint_style_guide.md`

**Theorem 7.2**

- `TNLean/Channel/Semigroup/LiouvillianKernel.lean`
- `blueprint/src/chapter/ch17_semigroup_adjoint_kernel_and_reducibility.tex`

### Reproducibility

The enumeration uses the same directories and exclusions as the Chapter 1
audit. Each result was checked against
`Notes/WolfNotePDF/ch07_semigroup_structure.pdf`; the line ranges above refer
only to the searchable transcription and do not determine numbering.

## Chapter 8: Measures for distances and mixedness

All three cited Chapter 8 numbers agree with the printed notes.

| Citation | Result title | Archived PDF | Local transcription | Verdict |
|---|---|---:|---:|---|
| Theorem 8.6 | Birkhoff | PDF page 5; printed page 135 | lines 263--266 | Correct |
| Theorem 8.16 | Trace-norm contractivity | PDF page 18; printed page 148 | lines 898--918 | Correct |
| Theorem 8.17 | Quantum version of Doeblin's theorem | PDF page 19; printed page 149 | lines 943--969 | Correct |

### Citing files

**Theorem 8.6**

- `TNLean/Analysis/Birkhoff.lean`
- `blueprint/src/chapter/ch19_entropy_majorization.tex`
- `docs/paper-gaps/wolf_ch8_birkhoff_doubly_substochastic_gap.tex`

**Theorem 8.16**

- `TNLean/Analysis/TraceNormContractivity.lean`
- `blueprint/src/chapter/ch19_entropy_trace_norm.tex`

**Theorem 8.17**

- `TNLean/Analysis/TraceNormContractivity.lean`
- `TNLean/Channel/ChoiDoeblin.lean`
- `blueprint/src/chapter/ch19_entropy_trace_norm.tex`

### Reproducibility

The enumeration uses the same directories and exclusions as the Chapter 1
audit. Each result was checked directly against
`Notes/WolfNotePDF/ch08_distance_measures.pdf`; the line ranges above refer
only to the searchable transcription and do not determine numbering.

## Chapters 4 and 9--11: no live numbered theorem-like citations

No live numbered citation to a theorem-like result in Wolf Chapters 4, 9, 10,
or 11 occurs in the directories examined here.

The Chapter 4 search finds many unqualified numerical near matches. Inspection
shows that they refer to other sources, principally the matrix-product density
operator paper of Cirac, Pérez-García, Schuch, and Verstraete. The files
`TNLean/MPS/MPDO/DiagonalCutRank.lean` and
`TNLean/MPS/MPDO/DiagonalFiniteChain.lean`, the corresponding blueprint entry
in `ch21_mpdo_rfp_area_law_diagonal_and_pure_state_bounds.tex`, and the note
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex` cite Riazanov and
Vyalyi, arXiv:1704.06507, Theorem 4.1. All other matches refer to papers by De
las Cuevas and coauthors or to internal blueprint labels. None is attributed
to Wolf, and none uses the Wolf bibliography key.

For Chapters 9--11, the general theorem-like-number search itself has no live
match. Searches with the word `Wolf` on either side of the number, and searches
requiring the `Wolf2012Quantum` bibliography key, also have no match for any of
the four chapters.

### Reproducibility

The search covers `TNLean/`, `blueprint/src/`, and `docs/` for singular and
plural forms of `Theorem`, `Proposition`, `Corollary`, `Lemma`, and `Example`,
including abbreviated forms and either ordinary or nonbreaking spaces before a
number of the form `4.n`, `9.n`, `10.n`, or `11.n`. It excludes
`docs/audits/`, `docs/archive/`, `docs/reviews/`, `docs/slides/`, and
`blueprint/comments/`. The Chapter 4 near matches were then checked for a
nearby occurrence of `Wolf` and for the `Wolf2012Quantum` bibliography key.
Definitions lie outside this result-numbering audit. In particular,
`TNLean/Channel/Basic.lean` cites Wolf Definition 4.1; this is the sole live
numbered Wolf citation from Chapter 4.
