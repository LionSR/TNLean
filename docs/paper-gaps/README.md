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
- `cpsv16_global_vs_persector_unit_witness.tex` records the current Lean
  declaration path for equal-modulus copy matching and the surviving
  per-sector unit-witness restriction.
- `blueprint/src/chapter/ch11_fundamental_theorem_proof.tex` records only how
  the Chapter 10 comparison is used in the equal-MPV Fundamental Theorem
  argument.
- GitHub issue #2150 records the verification request.  The outcome now
  recorded in the paper-gap note is that no strictly-decreasing-moduli
  hypothesis survives in the SectorBNT declaration path; the remaining
  non-source-faithful hypothesis is the per-sector unit witness.

The global-versus-per-sector unit-witness restriction has one current paper-gap
note.

- `cpsv16_global_vs_persector_unit_witness.tex` records that the current
  full-basis matching theorems assume a unit-modulus copy in every sector,
  while CPSV16 line 246 gives only one global unit-weight witness.

Older notes in this directory record why previous one-copy or projection-based
formulations were insufficient. They should be read as historical comparisons
unless they are cited by one of the current blueprint chapters above.

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
