# Paper-Gap Notes

This directory records places where the formal development needs more detail
than the cited source paper states locally. A note should identify the exact
source passage, state the mathematical input in paper notation, and then name
the current formal boundary.

- `wolf_thm6_12_abstract_schwarz_fixed_points.tex` records the former
  Kraus-only scope restriction in the source-labelled fixed-point algebra
  theorem, its resolution by an abstract positive unital Schwarz-map lemma,
  and the remaining reduction from a full-rank fixed point to an explicitly
  chosen positive-definite invariant weight.

For GNVW support algebras, the source corrections and the remaining scope
restriction are recorded separately.

- `gnvw12_support_algebra_star_closure.tex` records the necessary
  star-closed-input correction to the printed support-algebra lemma, the
  non-star-closed counterexample, and why the QCA and MPU applications supply
  the corrected hypothesis. This local correction is resolved.
- `gnvw12_support_algebra_outer_factor_basis.tex` records the resolved
  correction that the printed coefficient basis element $e'_\nu$ belongs to
  the third factor, as forced by both the typed expansion and the outer-factor
  basis argument.
- `gnvw12_support_algebra_full_matrix_scope.tex` records the remaining open
  restriction from arbitrary finite-dimensional $C^*$-algebra factors to
  full complex matrix factors.

For the present non-periodic MPS Fundamental Theorem work, the repeated-copy and
equal-modulus comparison has these current reference points.

- `blueprint/src/chapter/ch10_bnt.tex` records the SectorBNT canonical-form
  surface, the repeated-copy sector coefficients, and the Newton--Girard
  power-sum recovery.
- [cpsv16_global_vs_persector_unit_witness.tex](https://sirui-lu.com/QICLean/paper-gaps/cpsv16_global_vs_persector_unit_witness.pdf) records the earlier
  global-versus-per-sector unit-witness gap and its elimination by the exact
  linear-independence matcher, together with the unitary equal-case assembly
  of CPSV16 Source Corollary A.6 (`thm:Fundamental-CFII`). It is now a closure
  record, not a live restriction.
- `blueprint/src/chapter/ch11_fundamental_theorem_proof.tex` records how the
  Chapter 10 comparison is used in the equal-MPV and proportional-MPV
  Fundamental Theorem arguments.
- GitHub issue #2150 records the verification request. The outcome now
  recorded in the paper-gap note is that neither a strictly-decreasing-moduli
  hypothesis nor a per-sector unit-witness hypothesis survives in the SectorBNT
  declaration path. The remaining unit-modulus normalization is exactly the
  single global witness stated in CPSV16 line 246.

The global-versus-per-sector unit-witness restriction has one closed paper-gap
note.

- [cpsv16_global_vs_persector_unit_witness.tex](https://sirui-lu.com/QICLean/paper-gaps/cpsv16_global_vs_persector_unit_witness.pdf) records that earlier
  full-basis matching theorems assumed a unit-modulus copy in every sector,
  while CPSV16 line 246 gives only one global unit-weight witness. The current
  SectorBNT matching and global-gauge theorems use only that global witness.

The following proportional-FT notes are historical proof archaeology, not live
formalization gaps:

- `cpsv16_fixed_block_cancellation.tex` records the source's fixed-block
  sentence and the lower-bound obstruction in the abandoned discharge plan.
- `cpsv16_bnt_rate_quantification.tex` records the extra geometric-rate
  hypothesis that the retired non-dominant projection argument would have
  required.
- `cpsv16_nondominant_per_block_projection.tex` records why projection onto a
  non-dominant block can send both sides to zero. It is retained as a warning
  against reviving that proof route.
- `cpsv16_two_layer_sector_refinement.tex` records the mismatch between the
  retired strict-modulus specialization and the repeated-copy source
  decomposition, together with its resolution by the SectorBNT surface.

These notes are discoverable for proof archaeology, but none indexes a current
obligation. The unreferenced strict-modulus removal record was deleted because
its useful content is already preserved in the non-dominant projection and
two-layer refinement notes.

For MPDO renormalization fixed points:

- `cpsv16_active_physical_support_compression.tex` records that CPSV16
  Lemma `propSN` and Proposition `3to4` use the full physical-sector factor
  spaces, whereas the local development first restricts them to the joint
  column supports of the left and right factor families. It also separates
  this restriction from the generic physical-coordinate transport identities,
  which make explicit a basis change that the source uses without stating the
  corresponding two-site and four-site congruences.
- `cpsv16_vertical_sector_invertibility.tex` records the fixed contraction
  families and product-generation theorem used in Appendix C.4. The later
  mixed one-site/two-site comparison and zero-sector completion close the
  density-weighted argument: Theorem 4.14(i)--(ii) is formalized under the
  source's literal canonical-form and MPDO hypotheses, and the corresponding
  (i)--(iii) equivalence is formalized for the documented active-support
  correction of the printed fusion clause. See
  `cpsv16_two_site_sector_unitary_gauge_gap.tex` and
  `TNLean/MPS/MPDO/CPSVBNTTheoremEquivalence.lean`. The unrestricted printed
  statement (iii), including inactive product sectors, is not claimed.
- [cpsv16_simple_tensor_nilpotency.tex](https://sirui-lu.com/QICLean/paper-gaps/cpsv16_simple_tensor_nilpotency.pdf) identifies the source's nilpotent BNT
  elements with nilpotent physical-trace transfer matrices. The formal
  predicate is `MPOTensor.IsSimple`: it existentially chooses a positive
  physical blocking and a BNT sector presentation whose representative
  physical-trace transfers are all nonnilpotent. Every representative has a
  positive number of copies and every copy has nonzero weight, the
  nonzero-coefficient convention recorded in
  [cpsv16_bnt_uniqueness_zero_coefficient.tex](https://sirui-lu.com/QICLean/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.pdf). Positive-length nontriviality is derived
  from this presentation, while isolated vanishing lengths remain possible.
- [cpsv16_unit_weight_rfp_scale_tension.tex](https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf) records the tension between the
  source's line-246 unit-weight convention and the scale fixed by Definition
  4.1. The dimer tensor satisfies `MPOTensor.IsSimple`, witnessed by blocking
  length one, while its canonical-form weight $\sqrt{337/512}$ is not a unit
  weight; the line-246 witness is therefore not part of simplicity (see
  `docs/audits/2026-08-24_degenerate_readings_wave_2.md`). The same note also
  records the exact scalar repeated-copy counterexample to Theorem
  4.9(iv)$\Rightarrow$(v): weights $1$ and $1/2$ satisfy the global
  convention and every condition-(iv) clause, while the blocked tensor fails
  Definition 4.1.
- [cpgsv17_mpdo_mutual_information_bound.tex](https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_mpdo_mutual_information_bound.pdf) is the resolved false-source
  record for Proposition 4.5.  The monotonicity and finite-chain bounds remain
  proved separately.  The parity-sensitive tensor is an MPDO, but at every
  fixed nonempty cut its mutual information alternates between $0$ and
  $h_2(1/3)>0$, so the printed thermodynamic-limit clause is formally refuted.
  Aperiodicity or convergence is a genuine boundary condition absent from the
  proposition.
- `cpgsv17_mpdo_theorem_4_9_implication_label.tex` records the cyclic mismatch
  among the Appendix C proposition labels, the hidden use of the ZCL lemma
  `lemmus` in the printed proof of `prop3to4`, and the distinction between the
  refuted literal (iv)$\Rightarrow$(v) statement and the viable source
  (ii)$\Rightarrow$(v) route.
- [cpgsv17_pf_rank_one.tex](https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_pf_rank_one.pdf) records the completed normal Case-I rank-one
  theorem, the false absorbed-normality route in Case II, the exact
  repeated-copy counterexample to (iv)$\Rightarrow$(v), the nonminimality of
  the selected four-sector inverse-map factorization, and the remaining
  source question after ZCL-derived common-weight absorption: the printed
  per-representative factorization. Proposition C.7 supplies the resulting
  representative channels, and their outer-sector combination is complete.
- `cpsv16_gsnnch_sector_decomposition.tex` records that
  `MPOTensor.GSNNCHData` retains the source orthogonal sectors and natural
  multiplicities. Positive commuting products on supplied orthogonal sectors
  can be assembled into the outer direct sum, and the BNT SAL construction
  supplies one such family under its projector, closure, inverse, word-span,
  and sectorwise-SAL hypotheses. The active factor supports now give the
  canonical physical restriction without unused complementary directions,
  the compressed neighboring operators remain positive by explicit
  congruence, and the resulting positive commuting bonds are supported on the
  printed absorbing projections. Proposition `prop3to4` is complete under its
  five printed identities and the standing Case II assumptions: orthogonal
  compression makes every fixed-length sector coefficient nonnegative, and an
  \(N\)-th-root rescaling of the supported bond preserves the natural BNT
  multiplicity. This chainwise proof requires no copy independence. The note
  also records that the printed invocation of `lemmus` is invalid because its
  source-ZCL hypothesis is absent from the proposition.
- `cpgsv17_mpdo_sal_zcl_eta_local_structure.tex` records the missing
  coherent positive choice for the inverse-map neighboring operators in
  Appendix C.2. The comparison with the conjugated Hayashi decomposition,
  the tensors $l_k,r_k$, the resulting physical-sector factorization,
  and the exact finite-chain bond product are formalized. Deriving recurrence
  from injectivity and choosing positive representatives coherently across
  the sector graph remain open.
- `cpsv16_purification_rfp_definition.tex` records the distinction between
  the printed global PRFP predicate, formalized here at positive chain lengths,
  and the corrected local purification condition. A nonzero MPDO with a
  trace-invisible nilpotent bond sector formally refutes the printed global
  implication to literal physical-trace idempotence. The stronger scale-invariant
  counterexample is retained separately, while the local-purification equivalences remain
  restricted results.
- `cpsv16_pure_zcl_local_orthogonality_scope.tex` records that the current
  pure-MPS ZCL theorem is a single-block idempotence/CID equivalence. The
  source theorem also includes the BNT-level local-orthogonality equations
  between distinct blocks. The unrestricted source equivalence is false under
  its stated raw-weight BNT normalization, as recorded in
  `cpsv16_pure_zcl_raw_weight_counterexample.tex`.
- `cpsv16_pure_zcl_raw_weight_counterexample.tex` gives the canonical tensor
  $A^0=\operatorname{diag}(1,1/2)$. It satisfies physical CID and has a
  one-component, hence locally orthogonal, BNT, but its transfer map is not
  idempotent. It identifies the failed inference at source lines 1248--1251.
- `cpsv16_rfp_isometry_scope.tex` records the normalization and cross-block
  content of the source's equation `III_isometry`. The blockwise hypotheses are
  now derived from the single BNT canonical-form predicate for the
  multiplicity-one basis direct sum. The note also records why the fixed-letter
  virtual-block reading of the repeated-copy display `III_CFI_RFP` is out of
  scope: the source requires the copy index to contribute to the physical
  direct sum as well, which a one-letter tensor cannot do. The source relation
  `AA=A` and its unrestricted equivalence with transfer-map idempotence are
  formalized; the physical-space meaning of the repeated-copy index remains
  open.
- `cpsv16_renormalization_flow_index_typo.tex` records the local correction of
  the malformed summation and output indices in the displayed equation of
  CPSV16 Theorem 3.1. The preceding renormalization equation, the diagrams, and
  the Appendix proof all determine the corrected blocking-isometry identity;
  the correction changes no hypothesis or conclusion.
- `cpsv16_rfp_sal_data_processing.tex` is the closure record for the source
  RFP-to-ZCL-and-SAL implication. The exact boundary is a positive semidefinite
  density family with nonzero trace at every positive length, together with the
  Definition 4.1 local renormalization equations. Positivity alone admits the
  zero tensor. The horizontal-form theorems are stronger specializations that
  derive the required nonvanishing. This closes only implication
  $\mathrm{(i)}\Rightarrow\mathrm{(ii)}$. Theorem 4.9 is partial and partly
  refuted: its literal (iv)$\Rightarrow$(v) implication is false, while the
  stronger (ii)$\Rightarrow$(v) route remains a missing statement.
- `hjpw04_ssa_product_marginal_reference.tex` records the singular
  product-marginal evaluation in the relative-entropy form of strong
  subadditivity. The support-compressed tensor logarithm, the bipartite entropy
  identity, and the exact Hayden--Jozsa--Petz--Winter equality criterion are
  formalized. This note is now a closure record.
- `hjpw04_petz_factorization_maximally_mixed_scope.tex` records the support
  interpretation of HJPW equation (10) and the completed structural
  implication. The general product-reference raw map factors globally as
  first-factor support compression tensored with local raw recovery; the
  identity-tensored formula holds on supported inputs and globally for a
  positive-definite first factor. The invariant conditional family,
  joint-support block form, ambient equations (14)--(15), and final
  probability normalization now prove the Hayashi forward implication. Every
  supported right factor remains its sector output state, including at
  zero weight; only the left factor may then be a filler. Complementary sectors
  may use fillers on both sides. No factorization is claimed for TNLean's
  generic completed singular channel away from the supported input.
- `cpsv16_ssa_equality_hayashi_markov.tex` records the completed, axiom-free
  forward and reverse strong-subadditivity equality characterization and the
  exact normalization boundary between supported and complementary sectors.
- [cpsv16_zcl_canonical_form_normalization.tex](https://sirui-lu.com/QICLean/paper-gaps/cpsv16_zcl_canonical_form_normalization.pdf) records the corresponding
  normalization issue for mixed-state ZCL.
- `cpsv16_exact_arithmetic_scope.tex` records the scope boundary of the
  certified four-site arithmetic for Examples~4.10 and~4.11. The exact integer
  comparisons and logarithmic ratios are machine-checked. For the corrected
  fixed-$p=1/4$ Example~4.10 tensor and the literal four-site Example~4.11
  family, the reduced spectra, entropy comparisons, and non-SAL conclusions
  are complete. The finite-marginal calculation for Example~4.11 independently
  verifies the printed non-ZCL clause. The resolved scope restriction is that
  the arithmetic statements alone do not establish these tensor conclusions.

For the non-periodic MPS Fundamental Theorem background:

- [cpsv16_bnt_uniqueness_zero_coefficient.tex](https://sirui-lu.com/QICLean/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.pdf) records the nonzero-coefficient
  convention: every coefficient of a CPSV16 canonical form is nonzero, as the
  line-246 normalization presupposes. Under this convention Proposition 2.7,
  the line-1148 uniqueness sentence, Theorem 2.10, Corollaries 2.11, 3.12,
  and A.6, and Lemma A.5 are formalized as stated, and the note lists the
  blueprint node for each.
- `tnlean_bnt_ft_theorem_surface.tex` separates paper-level theorem
  statements from auxiliary formal declarations.
- `rmp_nonperiodic_bnt_comparison_inputs.tex` compares the current
  canonical-form/BNT/after-blocking proof boundary against the local paper
  sources.
- `pgvwc07_direct_sum_input.tex` explains the older MPS representation
  paper's direct-sum input behind block-injective canonical form.
- `spwc10_wielandt_one_step_subspace.tex` records the local proof boundary for the
  quantum Wielandt inequality.
- `cpsv16_zero_tail_length_zero_decomposition.tex` explains why stating the
  blocked canonical form as an all-length matrix-product-vector identity
  (carrying the empty-word "zero-tail" coefficient through the whole
  after-blocking chain) is the wrong formal shape, and records the
  positive-length comparison plus single bond-dimension identity that replaces
  it. It also names the one headline decomposition theorem that still keeps the
  explicit zero block to match CPSV16 Section 2.3.

Parent-Hamiltonian notes live here too, but they are not part of the current
non-periodic FT cleanup loop unless explicitly brought back into scope.

- `cpgsv21_normal_range_reduction.tex` records the normal parent-Hamiltonian
  range-reduction comparison and the remaining periodic-boundary identity.
- `cpgsv21_block_diagonal_parent_ground_space.tex` records the degenerate
  parent-Hamiltonian block-diagonal boundary-condition theorem behind the
  periodic block decomposition and the BNT ground-space span. The fixed-window
  PGVWC07 \(C^j,D^j\) comparison is now formalized under a crossing-tail
  word-span hypothesis; the remaining boundary is the replacement of that
  span-dependent short-tail statement by the source \(C^j,D^j,E^j\) comparison.
- `pgvwc07_common_identity_coefficients.tex` distinguishes the right-canonical
  normalization used in the proof of PGVWC07 Theorem 12 from the local variant
  that assumes a common one-letter expansion of every block identity.
- `cpgsv21_martingale_overlap.tex` records the spectral-gap martingale
  comparison: the finite-row cyclic-window reduction is formalized, while the
  remaining source comparison is the overlapping-window anticommutator estimate;
  the local norm-compression statements are sufficient stronger substitutes
  tracked by issue #952.
- `cpsv16_nncph_ground_state_scope.tex` records the separation between the
  zero-energy ground-vector predicate and the source ground-space spanning
  predicates for CPSV16 Theorem 3.10(iii). The finite Beigi sector graph and
  its ordered-cycle ground-space dimension formula are formalized; each
  positive-loop product state is proved to belong to the finite parent ground
  space for lengths at least two. Identifying these states with the chosen
  normal-tensor basis and proving that they span remain open.
- `cpsv16_parent_commuting_hamiltonian_scope.tex` records that the current
  parent commuting Hamiltonian predicate keeps only the idempotent-product
  consequence of CPSV16 Definition D.2, while the source definition also has
  tensor-product locality and orthogonal-projector hypotheses.

For Wolf Chapter 3 positive maps:

- `wolf_ex3_1_choi_positivity_subcase_scope.tex` records that the current
  Choi-type positivity theorem is only the \(d=3,n=1\) positive-map subcase of
  Wolf Example 3.1.  The general cyclic reciprocal estimate, and hence
  positivity of \(T_C\) for the full range \(1\le n\le d-2\), remain open.

For Wolf Chapter 5 Schwarz maps:

- `wolf_ch5_abstract_multiplicative_domains.tex` distinguishes the
  source-faithful multiplicative-domain theorem for an arbitrary linear map
  satisfying the Schwarz inequality from the older unital-Kraus
  specialization. The abstract one-variable theorem is now proved; the
  two-variable inverse-on-range inequality and its equality criterion remain
  open.

For the periodic (irreducible-form) MPS Fundamental Theorem of
arXiv:1708.00029, the overlap-dichotomy development has one route-alignment
note.

- `dccsp17_periodic_overlap_route_alignment.tex` records where the Lean
  development of the periodic overlap dichotomy (`MPS/Periodic/Overlap/`)
  substitutes a mathematically equivalent proof route for the Appendix-A
  argument: the different-period decay via the peripheral spectrum (Case 1),
  the sector non-repetition via the blocked fixed-point structure of
  Lemma bdcf (SelfOverlap), and the sector-match propagation plus the
  load-bearing κ/θ/φ phase assembly (Case 3). It also records the scope
  restriction of `periodicBasis_eventuallyLinearlyIndependent` (independence
  half only, no spanning clause).
