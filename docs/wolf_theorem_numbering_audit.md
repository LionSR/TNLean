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
followed by a number of the form `1.n`. It excludes `docs/audits/`,
`docs/archive/`, `docs/reviews/`, `docs/slides/`, and `blueprint/comments/`.
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
