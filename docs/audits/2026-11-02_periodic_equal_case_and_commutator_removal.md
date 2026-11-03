# Removal of the periodic equal-case hypothesis and the local lattice commutator

Baseline: TNLean main `0b35bb975f84257a76f992c90384b085dfafab38`.
Issues: #10483 and #10491.

## Periodic equal-case hypothesis

The predicate `MPSTensor.PeriodicEqualCaseFT d D` asserted that two tensors in
irreducible form with the same matrix product vectors are related by a
finite-order Z-gauge. It is false whenever `d ≥ 1` and `D ≥ 2`. Take letter 0
equal to `1 + E`, with `E` a matrix unit squaring to zero, and every other letter
zero, against the tensor whose letter 0 is `1`. Both tensors have the same word
traces, and both are in irreducible form with `D` one-dimensional blocks. The
only intertwiner is `1 - E`, and none of its positive powers is the identity.
Every theorem taking the predicate as a hypothesis was therefore vacuous in that
range.

The removed declarations, all in namespace `MPSTensor`, are:

- `PeriodicEqualCaseFT` (`Periodic/Symmetry/EqualCaseFTHyp.lean`, deleted);
- `cor_4_1_physical_symmetry_zgauge`, `cor_4_1_physical_symmetry_zgauge_explicit`
  and `twistedTensor_eq_rotatePhysical` (`Periodic/Symmetry/Corollary41.lean`,
  deleted);
- `zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical`
  (`Periodic/Applications.lean`), which took the same false statement written
  out as a hypothesis;
- `zGaugeEquiv_of_periodicEqualCaseFT_of_irreducibleForm`
  (`Periodic/Symmetry/Theorem41Forward.lean`).

The Blueprint entries `cor:cor_4_1_physical_symmetry_zgauge`,
`cor:symmetry_periodic_assembly` and `thm:zgauge_equiv_periodicFT_irreducible_form`
are removed with them.

Replacement: the source's symmetry corollary (arXiv:1708.00029, Section 4.2,
lines 834–845) is formalized without any equal-case premise by
`MPSTensor.exists_diagonal_unitary_of_irreducibleForm_physical_symmetry`
(`Periodic/Symmetry/PhysicalSymmetry.lean`, Blueprint
`ch22_periodic_ft_physical_symmetries.tex`). It rests on the multiplicity-bearing
equal-case theorem `fundamentalTheorem_periodic_equalCase_derivedPeriods`, which
is unchanged. The removed conditional results are replaced by this theorem.
`twistedTensor_eq_rotatePhysical` was a one-line definitional rewrite used only
by the removed corollary, so it is retired without a replacement.

## Local lattice commutator

The removed declarations are `TNLean.Lattice.commutatorCLM`
(`O M ↦ M * O - O * M`) and its `commutatorCLM_apply`, both in
`Lattice/GaussianFilteredLocality.lean`. Replacement: QICLean's
`GaussianFilter.commutatorCLM` (`H W ↦ H * W - W * H`) with
`GaussianFilter.commutatorCLM_apply`. The two maps differ by a sign, which only
reverses a subtraction inside a norm at each use and is absorbed by
`norm_sub_rev`. No theorem statement changes.

## Verification boundary

A repository-wide search found no remaining use of any removed name outside
dated audit records and historical Blueprint comments. No Blueprint `\lean{...}`
tag cites a removed name. Import aggregators are regenerated after the module
deletions. The hosted build passed on the pull request head before this note
was added.
