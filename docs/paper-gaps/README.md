# Paper-Gap Notes

This directory records places where the formal development needs more detail
than the cited source paper states locally. A note should identify the exact
source passage, state the mathematical input in paper notation, and then name
the current formal boundary.

For the present non-periodic MPS Fundamental Theorem work, the repeated-copy and
equal-modulus comparison has these current reference points.

- `blueprint/src/chapter/ch10_bnt.tex` records the SectorBNT canonical-form
  surface, the repeated-copy sector coefficients, and the Newton--Girard
  power-sum recovery.
- `cpsv16_global_vs_persector_unit_witness.tex` records the earlier
  global-versus-per-sector unit-witness gap and its elimination by the exact
  linear-independence matcher. It is now a closure record, not a live
  restriction.
- `blueprint/src/chapter/ch11_fundamental_theorem_proof.tex` records only how
  the Chapter 10 comparison is used in the equal-MPV and proportional-MPV
  Fundamental Theorem arguments.
- GitHub issue #2150 records the verification request. The outcome now
  recorded in the paper-gap note is that neither a strictly-decreasing-moduli
  hypothesis nor a per-sector unit-witness hypothesis survives in the SectorBNT
  declaration path. The remaining unit-modulus normalization is exactly the
  single global witness stated in CPSV16 line 246.

The global-versus-per-sector unit-witness restriction has one closed paper-gap
note.

- `cpsv16_global_vs_persector_unit_witness.tex` records that earlier
  full-basis matching theorems assumed a unit-modulus copy in every sector,
  while CPSV16 line 246 gives only one global unit-weight witness. The current
  SectorBNT matching and global-gauge theorems use only that global witness.

Older notes in this directory record why previous one-copy or projection-based
formulations were insufficient. They should be read as historical comparisons
unless they are cited by one of the current blueprint chapters above.

For MPDO renormalization fixed points:

- `cpsv16_purification_rfp_definition.tex` records why the former
  local-purification PRFP predicate was removed: it required a generic
  pure-state RFP witness, but did not enforce the source's global purification
  equation and trace-preserving post-ancilla map, and therefore produced a
  counterexample contradicting CPSV16's PRFP--ZCL theorem.
- `cpsv16_pure_zcl_local_orthogonality_scope.tex` records that the current
  pure-MPS ZCL theorem is a single-block idempotence/CID equivalence. The
  source theorem also includes the BNT-level local-orthogonality equations
  between distinct blocks.
- `cpsv16_rfp_isometry_scope.tex` records that the current per-block RFP
  isometry theorem exposes only a contracted per-block isometry condition,
  while the source's equation `III_isometry` imposes full pair-index
  orthonormality and cross-block orthogonality.
- `cpsv16_zcl_canonical_form_normalization.tex` records the corresponding
  normalization issue for mixed-state ZCL.

For the non-periodic MPS Fundamental Theorem background:

- `canonical_bnt_ft_theorem_surface.tex` separates paper-level theorem
  statements from auxiliary formal declarations.
- `nonperiodic_mps_bnt_comparison_inputs.tex` compares the current
  canonical-form/BNT/after-blocking proof boundary against the local paper
  sources.
- `david2006_direct_sum_input.tex` explains the older MPS representation
  paper's direct-sum input behind block-injective canonical form.
- `cpsv16_fixed_block_cancellation.tex` records the fixed-block cancellation
  step implicit in CPSV16 Theorem II.1, line 1182.
- `quantum_wielandt_deviation.tex` records the local proof boundary for the
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
  range-reduction comparison and the remaining boundary-closing identity.
- `cpgsv21_block_diagonal_parent_ground_space.tex` records the degenerate
  parent-Hamiltonian block-diagonal boundary-condition theorem behind the
  periodic block decomposition and the BNT ground-space span.
- `cpsv16_parent_commuting_hamiltonian_scope.tex` records that the current
  parent commuting Hamiltonian predicate keeps only the idempotent-product
  consequence of CPSV16 Definition D.2, while the source definition also has
  tensor-product locality and orthogonal-projector hypotheses.

For the periodic (irreducible-form) MPS Fundamental Theorem of
arXiv:1708.00029, the overlap-dichotomy development has one route-alignment
note.

- `1708_periodic_overlap_route_alignment.tex` records where the Lean
  development of the periodic overlap dichotomy (`MPS/Periodic/Overlap/`)
  substitutes a mathematically equivalent proof route for the Appendix-A
  argument: the different-period decay via the peripheral spectrum (Case 1),
  the sector non-repetition via the blocked fixed-point structure of
  Lemma bdcf (SelfOverlap), and the sector-match propagation plus the
  load-bearing κ/θ/φ phase assembly (Case 3). It also records the scope
  restriction of `periodicBasis_eventuallyLinearlyIndependent` (independence
  half only, no spanning clause).
