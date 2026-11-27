# Proof-Debt Ledger

Ranked registry of the open structural proof debts. Process rules:
[`docs/proof_debt.md`](proof_debt.md). Entry ids are stable; weekly audits update
evidence and status rather than renumbering. Closed, retired and rejected entries
are removed when they close; git history keeps them.

Tracking issue: [#4529](https://github.com/LionSR/TNLean/issues/4529), with
each open debt attached as a native sub-issue.

## Metrics

Weekly snapshot from `python3 scripts/loc_report.py` (see the shrink rhythm
in [`docs/proof_debt.md`](proof_debt.md)); every quantity should trend down.

| Date | Total lines | Dup 10-line windows | Sequel files (lines) | Cap-riding | Degenerate sites | Sorries |
|------|-------------|---------------------|----------------------|------------|------------------|---------|
| 2026-07-20 | 319,850 | 1,260 | 48 (20,500) | 29 | 1,934 | 4 |
| 2026-09-19 | 369,316 | 982 | 40 (17,963) | 15 | 2,190 | 1 |

## D13. The MPU canonical-form-II convention is threaded pointwise, while admissible path nodes carry an additional continuous-source-data gap  —  api-design, impact 7/10, effort 5/10
- **Status**: open. The convention predicate exists, the reduced
  representative is constructed in the ambient diagonal gauge, and the
  MPU-level theorem migration has landed: the stabilized pair is now a
  consequence of the predicate at the single positive exponent
  $\max(D^2-1,1)$, and the forced-block contractions, the source-$u$
  isometry with its rank bound, the source-$v$ isometry with its rank bound,
  and the simple-tensor equivalence take the predicate in place of the
  `(cfii, hfull)`, `(ρ, hρ, hρdiag)` and `(J, hJ, hpower)` groups. The
  source-labelled nodes `lemuisometry` and `ThmFund1` are therefore checked
  against those statements. The three same-tensor blueprint twins have now
  been merged using the supplied-pair converse; the generic source-u entry,
  twelve derived-tensor entries, and twenty-three pathwise entries remain.
  Seven further twins, whose source-labelled counterparts are now proved
  under the standing canonical-form convention (the Index Theorem, constancy
  of the source ranks, local time reversal and transposition, and the trace
  formula, gauge invariance and well-definedness of the time-reversal sign),
  have been deleted, together with the admissible continuous choice of
  standard form, now subsumed by `coruvSF`; see the superseded-entries
  subsection of `docs/paper-gaps/mpu_canonical_form_full_support.tex`.
  The last nine path-datum entries, including
  `def:mpu_admissible_equivalence_datum` and
  `def:mpu_reduced_full_support_source_datum`, were deleted on 2026-11-17
  without a continuous-selection theorem: they restated open source results
  under an unconstructed hypothesis, and their source-labelled counterparts
  keep their status. No Chapter 28 entry now carries the path datum.
  Other open work includes the `HasFullSupport` deletion
  (still consumed by the physical-adjoint, identity-ancilla, and
  tensor-product transports and by the reduced-representative construction),
  and the `fin_one` stabilization branch (still consumed on route by
  `cor:simple1` and `blockingsimple`(ii) in `SimpleBlocking.lean`). The
  remaining derived-tensor cases require their own preservation or reduction
  arguments. Of the original 16 pointwise nodes,
  `lem:mpu_admissible_source_u_isometry` is the generic supplied-fixed-pair
  step whose Lean statements still carry `(ρ, hρ, K, hpower)` and which the
  `lemuisometry` proof consumes. Three nodes
  (`thm:mpu_admissible_simple_tensor_equivalence`,
  `def:mpu_admissible_standard_form`, `thm:mpu_admissible_fundamental`)
  restricted only the tensor their source-labelled counterpart already places
  under the convention and have now been removed; the other 12
  restrict a physical block, a physical-adjoint, transposed, or conjugate
  comparison tensor, a tensor product, or a composition, whose preservation
  or reduction arguments are separate. Positive blocking, physical adjunction,
  and independent tensor products now preserve the predicate, but their
  downstream entries have not been consolidated. The 3 had been cited by
  11 retained nodes (7 pointwise plus the path nodes
  `prop:mpu_admissible_continuity_index`, `thm:mpu_admissible_index`,
  `cor:mpu_admissible_continuous_standard_form`, and
  `lem:mpu_admissible_symmetry_path_criterion`) whose tensors carry a supplied
  fixed pair. Their citations now use the converse with exactly that fixed
  matrix, without removing their other hypotheses. The converse
  `IsMPU U → ρ.PosDef → ρ.IsDiag → Matrix.trace ρ = 1 → 0 < J →
  E ^ J = vecMulVec ρ.vec 1.vec → IsMPUCanonicalFormII U`, by the spectral
  step of `Papers/1703.09188/paper_v2.tex` lines 344--355, turns a supplied
  positive-definite diagonal trace-one pair into a presentation of the same
  tensor. The generic supplied-pair entry does not assume trace normalization,
  but it follows from its power identity. Put $P=|\rho)(\Phi|$ and
  $t=\operatorname{tr}(\rho)$, so $P^2=tP$ and $\operatorname{tr}(P)=t$.
  For $K\geq2$, the MPU trace identity gives $t=\operatorname{tr}(E^K)=1$.
  For $K=1$, it gives $t^2=\operatorname{tr}(E^2)=1$ and
  $t^3=\operatorname{tr}(E^3)=1$, hence $t=1$; no length-one MPU trace
  identity is needed. For $K=0$, $P=I$ and $D=1$ as below give $t=1$.
  Thus trace normalization does not strengthen the generic entry.
  The positive-length trace identities are formalized in
  `IsMPU.trace_transferMatrix_normalizedFlattening_pow_eq_one` for lengths
  greater than one; the detailed gap note records the calculation.
  `IsMPU` has to stay a premise, since `IsMPUCanonicalFormII` contains it and
  a rank-one transfer power constrains only the normalized double layer;
  every intended call site
  supplies it. The `K = 0` inputs the generic node admits are not lost: at
  that exponent the condition forces `D = 1`, where
  `IsMPU.normalized_transfer_matrix_eq_one_fin_one` gives `E = 1` and the same
  pair works at exponent one. It therefore reaches only the 4
  nodes whose restricted tensor is the one the convention already governs
  (`lem:mpu_admissible_source_u_isometry` and the 3 candidates), and it
  dissolves the citation obstruction, but it constructs no datum for a
  derived tensor and so leaves all 12 restricted. The three same-tensor
  duplicates have been removed, with the 12 still standing. The remaining
  derived-tensor arguments require preservation of `IsMPUCanonicalFormII`
  under the relevant operation or transport through a reduced representative.
  In a preservation theorem, all four clauses (`isMPU`, `cfii`,
  `fullSupport_eq`, and the positive diagonal trace-one `ρ` with `ρ_fixed`)
  must hold for the derived tensor. The constructors
  `IsMPUCanonicalFormII.blockTensor`,
  `IsMPUCanonicalFormII.physicalAdjointTensor`, and
  `IsMPUCanonicalFormII.tensorProduct` now cover positive blocking, physical
  adjunction, and independent products. Transposition and conjugation exist
  only as the composite. For
  composition only `IsMPU.mulTensor` is available: `TNLean/MPS/MPU/` has no
  canonical-form-II construction for `mulTensor` and no transfer-map identity
  for it, only the entrywise `normalizedFlattening_mulTensor_apply`. Supplying
  those two would not settle that case, because no preservation statement can
  hold for `mulTensor` as it stands: `mulTensor (rightShiftTensor d)
  (leftShiftTensor d)` for `d ≥ 2` generates the identity operator with
  one-site matrices `A (i, k) = |i, k⟩⟨Φ|`, `⟨Φ| = ∑ γ, ⟨γ, γ|`, which are
  rank one with a common row functional, so every product at every length is
  rank one, no retained block of dimension ≥ 2 fits, blocks of dimension 1
  would force the `A (i, k)` to commute, and they do not
  (`A (0, 0) * A (0, 1) = 0` while `A (0, 1) * A (0, 0) ≠ 0`). The composition
  case therefore needs `IsMPU.exists_reduced_cfii_representative` applied to
  the product plus a transport of the source cuts and ranks across that
  reduction, which that theorem explicitly does not give.
  `thm:mpu_admissible_index_composition` now proves composition additivity
  of the representative index without this restriction, through rectangular
  reductions to canonical representatives (`IsMPU.index_mulTensor`). The
  nonsymmetric same-fixed-point problem in #7653 remains an optional
  out-of-source question; the transpose-reparameterized construction rejected
  in #7705 is not part of this plan.
- **Evidence**: `TNLean/MPS/MPU/` carries the paper's standing convention
  (`Papers/1703.09188/paper_v2.tex` lines 271--281 and 356--361) as explicit
  hypotheses in three shapes: `hρ : ρ.PosDef` at 65 sites in 11 files,
  `hpower : E ^ J = vecMulVec ρ.vec 1.vec` at 12 theorem-parameter binders in
  4 files, and `hfull : … .HasFullSupport` at 28 sites in 6 files; an exact
  `hpower` token search gives 34 lines in 6 files, including uses, derived
  locals, and an unrelated 3-line helper in `SimpleBlocking.lean`; 8
  `hasFullSupport_*`
  transport theorems and 3 canonical-form-II constructions
  (`PhysicalAncilla.lean`, `TensorProductCanonicalForm.lean`) exist only to
  carry the pair between statements; a separate `D = 1` branch
  (`normalizedTransferStabilization_fin_one`,
  `normalized_transfer_matrix_eq_one_fin_one`, consumed on route by
  `cor:simple1` and `blockingsimple`(ii) in `SimpleBlocking.lean`) exists
  because `Matrix.StabilizedRankOneData` needs a positive exponent at most
  `D * D - 1`, which is empty at `D = 1`. Chapter 28 has 82 `\notready`
  nodes among 508, of which 39 carry an `mpu_admissible` label: 16 are
  pointwise, while 23 define or use the pathwise equivalence datum. The
  fixed-tensor nodes replace the standing convention by a supplied fixed
  pair. The family also contains
  `def:mpu_admissible_equivalence_datum`, which has no source-labelled twin
  and requires continuously varying reduced source data for the actual
  blocked path and its conjugate, adjoint, transpose, and symmetry comparison
  paths. The continuity, index, equivalence, symmetry, and example nodes that
  depend on it record a separate continuous-selection gap. Four
  `**Scope restriction (full support)**` markers repeat the pointwise
  restriction.
- **Remediation**: one predicate on `MPOTensor d D` stating canonical form
  II for an MPU tensor by bundling `IsMPU`,
  `CPSVCanonicalFormIIData U.normalizedFlattening`, the equality
  $\sum_k D_k=D$ rather than the old `HasFullSupport` predicate, and an
  ambient positive definite diagonal trace-one fixed matrix $\rho$. The
  left-canonical equation is inherited from the CFII witness, but ambient
  diagonality is an additional field: blockwise diagonal fixed points may be
  scrambled by the ambient coisometry. The existing stabilization and
  normality theorems apply to the CFII and full-support fields, with
  $E^{\max(D^2-1,1)}=|\rho)(\Phi|$ stated as one power
  identity (no `D = 1` branch), normality, the forced-block simple
  contractions, and the five preservation lemmas proved once (the
  identity-ancilla and tensor-product lemmas build the `cfii` field with the
  retained witness constructors `normalizedDiagonalLiftCFIIData`,
  `tensorPhysicalIdCFIIData`, and `tensorProductCFIIData`, so only the
  `hasFullSupport_*` wrappers are deleted);
  their stabilized fixed matrix proved equal to the recorded $\rho$.
  `exists_reduced_cfii_representative` is strengthened to choose the ambient
  diagonal gauge and restated as the without-loss-of-generality theorem. This
  supplies the explicit $\rho^{\mathsf T}=\rho$ boundary now required by #7633
  under #5982, without an arbitrary nonsymmetric strengthening. While
  `HasFullSupport` still exists, current consumers derive it by unfolding the
  definition from the equality field. Every MPU-level step-7-to-13 statement
  (one that also assumes `IsMPU`, CFII data, full support, or the stabilized
  pair) is then migrated to the predicate or the equality directly, while the
  generic positive-metric constructions of `SourceFactors.lean` (lines
  82--476) and the gate constructors of `SourceUV.lean` (lines 141--202) keep
  their `(ρ) (hρ : ρ.PosDef)` parameters, since they assume nothing about
  $U$ and migrating them would shrink the API; only afterward delete
  `HasFullSupport`,
  the transports, the `fin_one` branch,
  `def:mpu_reduced_full_support_source_datum`, and only the
  admissible twins whose extra content is pointwise. In the same migration,
  delete or retarget the Chapter 28 tags on `def:mpu_full_support`,
  `thm:mpu_full_support_blocking`, `thm:mpu_full_support_reindexing`,
  `thm:mpu_physical_adjoint_full_support`, `thm:mpu_tensor_product_cfii_data`,
  `thm:mpu_identity_ancilla_reduced_cfii`, and
  `thm:mpu_normalized_transfer_fin_one`, and retarget the 17 surviving
  `\uses` references to `def:mpu_full_support` in 14 nodes (the
  reduced-representative, stabilization, forced-contraction, and normality
  nodes among them) to the convention predicate's node before that label is
  removed. Retain
  `def:mpu_admissible_equivalence_datum` and every node requiring its
  continuously varying path data until a continuous-selection theorem is
  proved. Keep the positive-power API in `TransferStabilization.lean` and the
  forced-block contractions in downstream `MatchingContractions.lean`; moving
  the latter into `CanonicalForm.lean` would create an import cycle through
  `SimpleBlocking.lean`. Rewrite
  `docs/paper-gaps/mpu_canonical_form_full_support.tex` as the pointwise
  convention record while keeping the pathwise supplier gap explicit.
- **First PR**: define the predicate in `CanonicalForm.lean` with the CFII,
  full-support-equality, and ambient-diagonal-$\rho$ fields. Use the existing
  theorems for normality and stabilization, prove that the stabilized matrix is
  this recorded $\rho$, and strengthen `exists_reduced_cfii_representative` to
  choose the ambient diagonal gauge; no consumer changes yet.

## D18. One-site long-range gates and register gates kept as two layer stacks  —  duplication, impact 3/10, effort 4/10
- **Status**: open (recorded in the review of #8492)
- **Evidence**: `QuantumCircuit.RegisterGate` at `s = 1`
  (QICLean `Circuit/Protocol/Teleportation/RegisterGates.lean`) is the same object as
  `QuantumCircuit.LongRangeGate` (QICLean `Circuit/Protocol/Teleportation/LongRangeGates.lean`): a
  gate on the sites `a` and `a + 2L + 1`, with the same stretch, interior and
  zone, applied by a forward chain, a local gate and a backward chain. Both
  files carry the layer machinery (all-gate chain lists, site-permutation
  lemmas, the conjugation identity). The depths differ: `LongRangeGate` merges
  the local gate into the backward round and has depth at most `5`, while
  `RegisterGate` applies it as a circuit between the rounds and has depth at
  most `4s + K`. Both are now QICLean declarations, so the duplication is
  QICLean's to remove.
- **Remediation**: derive the one-site layer of `LongRangeGates` (and its use
  in `TreeMeasurement`) from `RegisterGate` at `s = 1`, after merging the local
  circuit into the last forward or first backward round so that the `s = 1`
  depth matches.
- **First PR**: merge the local round into the backward rounds of
  `RegisterGate.rounds`, then restate `LongRangeGate.rounds` through it.

## Honorable mentions (ranks 11-12)

- **D11 (plumbing tax)** — 486 `finCongr`/`Fin.cast` sites in 91 files;
  a 434-line proof repeating one insert-and-cancel calc four times
  (`MPS/CanonicalForm/CyclicSectors/Compression.lean:72`); 435
  inference-redundant `(d := d) (D := D)` annotations;
  `matrix_entry_cases` unpromoted at 10 occurrences. Fix as transport
  lemma packs, simp sets, and tactic promotion — not a Fin-generalization
  rewrite.
- **D12 (scope-restriction accumulation)** — 251 `**Scope restriction**`
  markers across 107 files (MPDO 82, ParentHamiltonian 46, RFP 38);
  headline results including
  `fundamentalTheorem_normalSquarePEPS_unconditional` are narrower than
  their cited sources. Mostly missing mathematics, not refactoring: track
  marker density, eliminate per-cluster definitional restrictions
  (closing-matrices and periodic-boundary families first).
