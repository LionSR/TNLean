# Simplification pass: TNLean/MPS/MPDO

Date: 2026-10-22. Audit clarified: 2026-10-23. PR: #9933. Addresses #9881.

This simplification preserves the mathematical content of `TNLean/MPS/MPDO`.
The retained public statements have unchanged hypotheses and conclusions. The
seven removed declarations below are consequences of retained results or
identities supplied by the retained definitions. Following
`docs/project_conventions.md`, no deprecated aliases are retained.

## Removed declarations and replacements

Names in the first column are relative to the namespace stated in that row.
File paths are relative to `TNLean/MPS/MPDO/`.

| Removed declaration and namespace | File | Retained replacement or derivation |
|---|---|---|
| `ofWords_left` in `MPSTensor.MultiBlockCompression` | `CompleteZipperFusionBlocked.lean` | `ofWords` retains the original compression coordinates. The equality `(P.ofWords u hu hB' hC').left s = P.left s` holds by definition (`rfl`). |
| `ofWords_right` in `MPSTensor.MultiBlockCompression` | `CompleteZipperFusionBlocked.lean` | `ofWords` retains the original compression coordinates. The equality `(P.ofWords u hu hB' hC').right s = P.right s` holds by definition (`rfl`). |
| `leftTreeGaugeInv_mul_leftTreeGauge` in `MPOTensor.CompleteZipperFusionFamily` | `CompleteZipperFusionGauge.lean` | Apply `mul_eq_one_comm.mp` to `Fus.leftTreeGauge_mul_leftTreeGaugeInv Y a b c d`. For these finite square complex matrices, the retained right-inverse identity also gives the left-inverse identity. |
| `mulTensor_smul_left` in `MPOTensor` | `OperatorProduct.lean` | Specialize `mulTensor_smul_smul a 1 M N` and simplify multiplication and scalar multiplication by one. |
| `mulTensor_smul_right` in `MPOTensor` | `OperatorProduct.lean` | Specialize `mulTensor_smul_smul 1 b M N` and simplify multiplication and scalar multiplication by one. |
| `activeRestrictedPhysicalSectorFactorization_sector` in `MPOTensor.PhysicalSectorFactorization` | `PhysicalSectorActiveNeighboring.lean` | The subtype proof `(F.activeSectorFinEquiv j).2` already proves `F.IsActiveSector (F.activeSectorFinEquiv j).1`. The removed declaration's support-data argument is unnecessary. |
| `closedSectorTraceMatrix_normalized_trace_pow_eq_trace` in `MPOTensor` | `SectorPairingTransfer.lean` | From `closedSectorTraceMatrix_normalized_relations K hK hη R hρ α₁ β₃ hm hZCL`, extract `⟨lam, hlam, _, htrace⟩` and retain `⟨lam, hlam, htrace⟩`. The positive normalization and every positive-power trace identity are preserved, with exactly the same hypotheses. |

## Preservation of source statements

The four public statements in `LocalOrthogonalSumAreaLaw.lean` concerning
sector probabilities, the normalized state, reduced states, and entropy are
retained with their original hypotheses and conclusions. Their proofs now
specialize the proportional statements to coefficient one.

The deleted trace-power declaration records an intermediate display in the
proof of CPSV16, Appendix C.2, Lemma `SALZCL`
(`Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 1485–1497).
It is not the lemma's full conclusion. Its mathematical content remains in
`closedSectorTraceMatrix_normalized_relations`, which also supplies the
square–cube identity for the same normalization. The existing distinction
between the paper's literal normalization and the development's positive
scalar normalization is unchanged. None of the seven deletions removes a
paper headline statement without retaining its content.

## Verification

At Lean head `4fa0f2866bc2006428955c1775db4f23f6b5d318`, repository-wide
searches for all seven removed names found only this audit note: no Lean
consumer, test, script, or blueprint declaration tag remains. The same check
passed for the prospective combined tree with #9932 and #9935 merged.

[PR CI run 39831182746](https://github.com/LionSR/TNLean/actions/runs/39831182746)
passed on that exact head, including the full build, strict checks on changed
Lean files and affected tests, style and module-policy checks, blueprint and
paper-gap declaration checks, blueprint web compilation, and compilation-time
checks. The diagram and blueprint PDF checks were skipped.

The audit clarification changes only this Markdown file. Diff and prose
checks confirm that it changes no Lean source, mathematical statement, proof,
blueprint, or dependency. No additional Lean build was run for this
documentation-only correction.
