# Rescaling-stable bond-matching predicate rename (issue #7706)

Issue #7706 applies the `Is`-prefix convention to the bond-matching condition in
`TNLean/MPS/MPDO/RescalingStableLengthDependentRFPViaTS.lean`. The definition remains
`bondBit2 p = bondBit1 q` for `p q : Fin 4`. The decidability instance still uses
`inferInstanceAs (Decidable (bondBit2 p = bondBit1 q))`; no replacement mathematics
or automation is introduced. The theorem statements and proofs are unchanged apart
from identifier substitution and line wrapping.

## Exact mapping

All declarations below belong to `MPOTensor.RescalingStableLengthDependentRFP`.

| Old declaration | New declaration |
|---|---|
| `gate` | `IsBondMatchedPair` |
| `decidableGate` | `decidableIsBondMatchedPair` |
| `bondBit2_ne_of_gate_combine_eq` | `bondBit2_ne_of_isBondMatchedPair_combine_eq` |

The supporting lemma's name follows the renamed predicate, with the lower-camel
`isBondMatchedPair` component required for predicates embedded in theorem names.
Other declarations, including the existing gated and ungated Kraus families, are
outside this narrowly scoped rename.

**No compatibility alias is provided.** The old name encodes the misleading internal
term `gate`, not a quantum gate or paper-defined predicate (see
[`docs/CONTRIBUTING.md` Section Mathematical-language renames](../CONTRIBUTING.md#mathematical-language-renames)).

## Reference and source audit

A repository-wide tracked-file search, including `TNLean/Archive`, found every Lean
reference to these three declarations in `RescalingStableLengthDependentRFPViaTS.lean`.
All these references, including the module and declaration docstrings, are migrated.
Unrelated quantum-gate terminology and historical audit mappings are unchanged.

`docs/glossary.md` has no entry for this example's bond-matching predicate, so no
existing glossary entry requires migration. This is a rename, not a new predicate.
No Blueprint declaration tag names any of the three renamed declarations.
The existing tag in `blueprint/src/chapter/ch21_mpdo_rfp_bnt_coefficients.tex:1813`
continues to name `MPOTensor.RescalingStableLengthDependentRFP.isRFPViaTS_R`.
Its proof at lines 1831–1841 displays the two indicators for equality of neighboring
bond bits, agreeing with the unchanged Lean condition. The phrase `gate-restricted`
in that proof is prose, not a stale declaration reference; LaTeX is left unchanged.

The example constructs the maps from CPSV16 Definition 4.1, source label
`RFPMixedTS`, and equations `eq:Smap` and `eq:Tmap` in
`Papers/1606.00608/MPDO-22-12-17-2.tex:645–659`: “there exist two tpCPM” acting on
the physical indices and fulfilling the two equations. The coordinate predicate is
internal to this example, not a definition from that passage. No claim about the
source's canonical-form hypothesis, the example, or its renormalization maps changes.
