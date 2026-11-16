# MPU campaign: open issues, sources and Lean status

Source: Cirac, Pérez-García, Schuch and Verstraete, *Matrix product unitaries:
structure, symmetries, and topological invariants*, arXiv:1703.09188v2, local copy
`Papers/1703.09188/paper_v2.tex` (line numbers below refer to it). Tracker: #5704.
Blueprint: `blueprint/src/chapter/ch28_mpu_fundamental_theorem.tex` (structure,
standard form, index) and `ch28_mpu_symmetries.tex` (symmetries).

Audit baseline: main `73007e1` (2026-11-16), updated after #10688. The closed structure issues
#5705–#5711 (operator family, normality, simple tensors, ranks, standard form and
fundamental theorem, QCA correspondence, index definition and additivity) are not
listed. The fundamental theorem is proved in the form comparing tensors on rings of
even length; the printed all-length converse fails
(`docs/paper-gaps/mpu_standard_form_parity_gap.tex`).

Out of scope here: the MPO-symmetry campaign (tracker #8012, #8048–#8060, #8321,
#8322), #7574 (pull request #10640), and `mpu`-labelled issues about other papers
(#10521, #8040, #8011, #8273, #8315, #8319, #8320). The MPU–QCA and gauging issues
#5710, #6028, #7036 were handed over to QCALean (see `docs/related_libraries.md`).

## Index (tracker #5712)

| Issue | Source result | Lines | Lean on main | Status |
|---|---|---|---|---|
| #6023 | `IndexTh`, four-clause index theorem | statement 824–832, proof 834–865 | `MPOTensor.IsMPU.indexTheorem`; clause (iv) `IsMPU.equivalent_iff_index_eq` (`IndexClassification.lean`); (i) `IsMPU.index_blockTensor`; (ii) `IsMPU.index_tensorProduct`, `IsMPU.index_mulTensor`; (iii) `IsMPU.index_const_of_continuous` | Proved (#10687, #10691, #10692, #10696, #10703); the canonical-form hypotheses of clause (iv) are the source's (lines 708–714); the omitted step from gates to tensors is recorded in `docs/paper-gaps/mpu_index_classification_tensor_to_gates.tex` |
| #6024 | `coruvSF`, continuous choice of standard form | 869–875, proof 877–950 | `MPOTensor.IsMPU.exists_continuous_standardForm_of_path`; gate relation `TwoSiteStandardFormData.mpo_eq_iff_exists_gate_gauges` (#10715); local cross-section `Matrix.exists_continuous_lift_of_continuous_mod_localUnitary` (#10716) | Proved (#10715, #10725, #10731, #10733, #10735, #10736, #10739, #10742) with no canonical-form hypothesis on the path; the slice theorem is replaced by a direct local cross-section (`docs/paper-gaps/mpu_standard_form_path_cross_section.tex`, resolved) |
| #6140 | continuous reduced source data along equivalence paths (context `coruvSF`, `lem:equivalent-symmetry`) | 867–950, 1367–1380 | none | Closed as superseded: `coruvSF` (#10742) and the path criterion (#10747) need no reduced source data |

## Symmetry-respecting equivalence (tracker #6017) and source-data transport (#6136, #6139)

| Issue | Source result | Lines | Lean on main | Status |
|---|---|---|---|---|
| #7016 | `lem:equivalent-symmetry`, standard-form path criterion | 1369–1376, proof 1378–1380 | `strictlyEquivalentUnderSymmetry_blockTwo_of_gate_path`, `exists_gate_path_of_strictlyEquivalentUnderSymmetry` (`SymmetryPathCriterion.lean`) | Reverse direction proved as printed; forward direction proved after blocking 2k₀ sites (#10747). The unblocked forward direction is open (`docs/paper-gaps/mpu_symmetry_path_criterion_blocking.tex`) |
| #7032 | transport of reduced source data along symmetry paths (infrastructure for `lem:equivalent-symmetry`) | 1367–1380, 867–875 | none | Closed as superseded by #10742 and #10747 |

## Complex conjugation (tracker #5713)

| Issue | Source result | Lines | Lean on main | Status |
|---|---|---|---|---|
| #7017 | `prop1conj`, local characterization (equations `uconjugation`, `vconjugation`) | 1014–1027, proof 1029–1039 | `IsMPUCanonicalFormII.standardForm_conjugation_iff`, `TwoSiteStandardFormData.blockTwo_mpo_conjugation_invariant_of_local` (`StandardFormConjugation.lean`) | Proved (#10704, #10714), with SF the standard form of a canonical representative and lengths counted in two-spin sites (`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`, `mpu_standard_form_parity_gap.tex`) |
| #7018 | `corconj`; `cor:sympl-to-orthogonal` (equation `upvpconj`) | 1098–1127, proof 1129–1163; 1168–1181, proof 1183–1185 | `IsMPUCanonicalFormII.exists_conjugation_standard_form`, `exists_orthogonal_gauge_of_mpo_eq`, `exists_symplectic_gauge_of_mpo_eq` (`ConjugationStandardForms.lean`); `Matrix.exists_real_of_map_star_eq_sourceSkewForm_mul` | Proved (#10693, #10714); Case II uniqueness carries the local fix of `docs/paper-gaps/mpu_conjugation_symplectic_uniqueness_transpose.tex` |
| #7019 | `conjphs`, `prop:conjsym-strict-equiv`, `cor:equiv-under-conjugation` | 1406–1413, 1482–1546, 1548–1567 | `strictlyEquivalentUnderSymmetry_conjugation_of_det_mul_eq`, `strictlyEquivalentUnderSymmetry_conjugation_of_det_eq_of_even` (`ConjugationStrictEquivalence.lean`), `Matrix.IsUnitaryBetween.joinedIn_real_of_det_eq` | The "if" directions of VI.4 and VI.6 are proved (#10745, #10760). Their "only if" directions need the unblocked forward direction of #7016, since blocking makes the determinant invariants trivial. VI.7 is in progress |

## Time reversal and transposition (trackers #5714, #7021, #7109)

| Issue | Source result | Lines | Lean on main | Status |
|---|---|---|---|---|
| #7020 | `PropChiral` (equation `UUdaggertrick`); `prop:local-char-transposition` (equation `UUtransposetrick`) | 1214–1225, proof 1230–1252; 1266–1276, proof 1278–1288 | `IsMPUCanonicalFormII.standardForm_even_timeReversal_iff`, `IsMPUCanonicalFormII.standardForm_even_transposition_iff` (`StandardFormSymmetryCriteria.lean`), `intermediateRanks_eq_phys_of_even_mpo_eq_adjoint`, `intermediateRanks_eq_phys_of_even_mpo_eq_transpose` | Proved (#10688), reading "tensor in SF" as the standard form of a canonical representative and counting lengths in two-spin sites (`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`) |
| #7108 | `eq:sigma-from-trace`, trace formula for σ | 1595–1603, proof 1605–1611 | `IsMPUCanonicalFormII.standardForm_timeReversalSign` (`StandardFormTimeReversalSign.lean`), `TwoSiteStandardFormData.timeReversalSign_eq_of_local_relation`, `Matrix.trace_swapMatrix_mul_kronecker` | Proved (#10702); the local relation is derived from `PropChiral` (#10688), under `docs/paper-gaps/mpu_standard_form_canonical_convention.tex` |
| #9880 | `prop:sigma-well-defined`, gauge and path invariance of σ | 1616–1622, proof 1624–1631 | `IsMPUSimple.intrinsicTimeReversalSign_blockTwo_eq_standardForm_sign`, `intrinsicTimeReversalSign_blockTwo_eq_one_or_neg_one_of_representative`, `intrinsicTimeReversalSign_blockTwo_eq_on_path` (`TimeReversalSignInvariance.lean`), `MPOTensor.timeReversalTrace_gauge` | Proved (#10706); a path stays in SF when each tensor has a simple canonical-form-II representative with the same operators; no canonical form or continuous choice of gates along the path |
| #7111 | `prop:sigma1-and-sigma2-equal`, blocking parity of σ (equation `eq:unwind-dagger-trick`) | 1643–1655, proof 1657–1733 | `TNLean.Algebra.blockedSign_eq_first_of_odd`, `..._second_of_even`, intrinsic parity in `IntrinsicBlockingParity.lean` | Intrinsic parity proved; the sequential unwinding is in draft #10690 (another workstream); source statement open |
| #7110 | unnumbered corollary: σ is a necessary invariant of equivalence | 1736–1743 | `StrictlyEquivalentUnderSymmetry`, `EquivalentUnderSymmetry` | Open; depends on #7111 (#9880 proved in #10706) |
| #7023 | `prop:mps-class-eq-mpu-class-for-conjugation`, `prop:dagger-mps-class-and-mpu-class-equal` (equation `eq:mps-class-gauge-trafo`) | 1748–1789, 1791–1805, 1808–1829 | `IsMPUCanonicalFormII.mps_conjugation_sign_iff` (`ConjugationMPSClass.lean`, entry `lem:mpu_mps_sign_conjugation_case`); `IsMPUCanonicalFormII.mps_timeReversal_sign_eq` (`TimeReversalMPSClass.lean`) | Time-reversal proposition proved (#10732). For the conjugation proposition, the sign is matched with the two cases of `corconj` (#10730); its identification of the cases with the two phases needs `cor:equiv-under-conjugation` (#7019) |

## Examples (tracker #5715)

Open stream #6290 (symmetry phases of shift families) has only #7574 open, handled
by pull request #10640.
