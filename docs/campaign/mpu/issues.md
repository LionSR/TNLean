# MPU campaign: open issues, sources and Lean status

Source: Cirac, Pérez-García, Schuch and Verstraete, *Matrix product unitaries:
structure, symmetries, and topological invariants*, arXiv:1703.09188v2, local copy
`Papers/1703.09188/paper_v2.tex` (line numbers below refer to it). Tracker: #5704.
Blueprint: `blueprint/src/chapter/ch28_mpu_fundamental_theorem.tex` (structure,
standard form, index) and `ch28_mpu_symmetries.tex` (symmetries).

Audit baseline: main `73007e1` (2026-11-16). The closed structure issues
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
| #6023 | `IndexTh`, four-clause index theorem | statement 824–832, proof 834–865 | (i) `MPOTensor.IsMPU.index_blockTensor`; (ii) `IsMPU.index_tensorProduct`, `IsMPU.index_mulTensor`; (iii) `IsMPU.index_const_of_continuous`; `IsMPU.index_padBond`, `IsMPU.index_tensorPhysicalId`; `MPOTensor.StrictlyEquivalent`, `MPOTensor.Equivalent` | Clauses (i)–(iii) proved; clause (iv) open in both directions (equivalence ⇒ equal index is an assembly; the converse needs explicit paths of standard forms) |
| #6024 | `coruvSF`, continuous choice of standard form | 869–875, proof 877–950 | none | Open; needs a slice theorem for compact group actions |
| #6140 | continuous reduced source data along equivalence paths (context `coruvSF`, `lem:equivalent-symmetry`) | 867–950, 1367–1380 | none | Open; depends on #6024 |

## Symmetry-respecting equivalence (tracker #6017) and source-data transport (#6136, #6139)

| Issue | Source result | Lines | Lean on main | Status |
|---|---|---|---|---|
| #7016 | `lem:equivalent-symmetry`, standard-form path criterion | 1369–1376, proof 1378–1380 | `MPOTensor.StrictlyEquivalentUnderSymmetry`, `MPOTensor.EquivalentUnderSymmetry`, `IsInvariantUnderSymmetry.blockTensor`, `IsInvariantUnderSymmetry.tensorPhysicalId` | Open; forward direction needs #6024 |
| #7032 | transport of reduced source data along symmetry paths (infrastructure for `lem:equivalent-symmetry`) | 1367–1380, 867–875 | none | Open; depends on #6024, #6140 |

## Complex conjugation (tracker #5713)

| Issue | Source result | Lines | Lean on main | Status |
|---|---|---|---|---|
| #7017 | `prop1conj`, local characterization (equations `uconjugation`, `vconjugation`) | 1014–1027, proof 1029–1039 | `IsMPUCanonicalFormII.exists_local_conjugation_gauges`, `..._common_transpose_case`, `TwoSiteStandardFormData.map_star_mpo_eq_of_gate_conjugation`, `sourceU_mapStar`, `sourceV_mapStar` | Forward direction for canonical form II; converse on even lengths only (parity gap); arbitrary ambient open |
| #7018 | `corconj`; `cor:sympl-to-orthogonal` (equation `upvpconj`) | 1098–1127, proof 1129–1163; 1168–1181, proof 1183–1185 | `lemma:conjclass-normalform-continuous` done (`Matrix.exists_unitary_congruence_normalForm`); `Matrix.exists_symmetric_unitary_squareRoot`, `Matrix.exists_unitary_congruence_interleavedSkewForm`, `Matrix.symplecticOrthogonalR_identities` | Open; in progress in this campaign |
| #7019 | `conjphs`, `prop:conjsym-strict-equiv`, `cor:equiv-under-conjugation` | 1406–1413, 1482–1546, 1548–1567 | `Matrix.det_kronecker_eq_one_of_mem_orthogonalGroup`, `..._symplecticGroup` | Open; depends on #7016, #7017, #7018 |

## Time reversal and transposition (trackers #5714, #7021, #7109)

| Issue | Source result | Lines | Lean on main | Status |
|---|---|---|---|---|
| #7020 | `PropChiral` (equation `UUdaggertrick`); `prop:local-char-transposition` (equation `UUtransposetrick`) | 1214–1225, proof 1230–1252; 1266–1276, proof 1278–1288 | `TwoSiteStandardFormData.even_timeReversal_iff_exists_certificate`, `intermediateRanks_eq_phys_of_even_mpo_eq_adjoint`, `intermediateRanks_eq_phys_of_even_mpo_eq_transpose`, `transpositionPhaseScalar` | Proved for standard forms whose two-site tensor is in canonical form II; scope of the source statement under review; in progress in this campaign |
| #7108 | `eq:sigma-from-trace`, trace formula for σ | 1595–1603, proof 1605–1611 | `MPOTensor.timeReversalSign`, `TwoSiteStandardFormData.timeReversalSign_eq_of_local_relation`, `Matrix.trace_swapMatrix_mul_kronecker` | Open; follows from #7020 |
| #9880 | `prop:sigma-well-defined`, gauge and path invariance of σ | 1616–1622, proof 1624–1631 | `intrinsicTimeReversalSign`, `TwoSiteStandardFormData.timeReversalSign_eq_intrinsic`, `timeReversalSign_eq_of_mpo_two_eq`, `continuous_intrinsicTimeReversalSign`, `MPOTensor.timeReversalTrace_gauge` | Intrinsic sign proved; source statement open pending #7020 |
| #7111 | `prop:sigma1-and-sigma2-equal`, blocking parity of σ (equation `eq:unwind-dagger-trick`) | 1643–1655, proof 1657–1733 | `TNLean.Algebra.blockedSign_eq_first_of_odd`, `..._second_of_even`, intrinsic parity in `IntrinsicBlockingParity.lean` | Intrinsic parity proved; source statement open pending #7020, #7108 |
| #7110 | unnumbered corollary: σ is a necessary invariant of equivalence | 1736–1743 | `StrictlyEquivalentUnderSymmetry`, `EquivalentUnderSymmetry` | Open; depends on #9880, #7111 |
| #7023 | `prop:mps-class-eq-mpu-class-for-conjugation`, `prop:dagger-mps-class-and-mpu-class-equal` (equation `eq:mps-class-gauge-trafo`) | 1748–1789, 1791–1805, 1808–1829 | MPS symmetry API in `TNLean/MPS/Symmetry/` | Open; depends on #7017–#7019 and #7021 |

## Examples (tracker #5715)

Open stream #6290 (symmetry phases of shift families) has only #7574 open, handled
by pull request #10640.
