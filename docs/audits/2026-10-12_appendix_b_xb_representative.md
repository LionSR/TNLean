# Appendix B XB coefficient representative collapsed (2026-10-12)

`MPSTensor.AppendixBStructuralData.appendixBQXBOnCoeffSpace` was defined as
`hStruct.appendixBQAXOnCoeffSpace`: arXiv:1606.00608 (lines 543--578 and
Definition D.2, lines 2205--2218) places one two-site coefficient
representative on both the $AX$ and the $XB$ face, so
$\widehat Q_{XB}=\widehat Q_{AX}$. Its two lemmas restated the $AX$ ones,
and one left-canonical wrapper had no Lean consumer. #7918 removes them;
every statement that named the $XB$ representative now names the $AX$ one,
which is the same map by definition.

| Removed | Replacement |
|---|---|
| `MPSTensor.AppendixBStructuralData.appendixBQXBOnCoeffSpace` (`TNLean/MPS/RFP/AppendixBStructuralData.lean`) | `MPSTensor.AppendixBStructuralData.appendixBQAXOnCoeffSpace` (same file), its definitional value |
| `MPSTensor.AppendixBStructuralData.appendixBQXBOnCoeffSpace_eq_parentInteraction` (same file) | `MPSTensor.AppendixBStructuralData.appendixBQAXOnCoeffSpace_eq_parentInteraction` |
| `MPSTensor.AppendixBStructuralData.appendixBQXBOnCoeffSpace_idempotent` (same file) | `MPSTensor.AppendixBStructuralData.appendixBQAXOnCoeffSpace_idempotent` |
| `MPSTensor.AppendixBStructuralData.localTerm_two_three_one_eq_appendixBQXBOnCoeffSpace_lift` (same file) | renamed to `MPSTensor.AppendixBStructuralData.localTerm_two_three_one_eq_appendixBQAXOnCoeffSpace_rightLift`; the statement only replaces the representative by its definitional value |
| `MPSTensor.rfp_hasAppendixD2ParentCommutingHamiltonian_of_leftCanonical` (`TNLean/MPS/RFP/AppendixBChainCommutation.lean`) | `MPSTensor.AppendixBStructuralData.hasAppendixD2ParentCommutingHamiltonian` applied to `MPSTensor.AppendixBStructuralData.ofRFP` and `MPSTensor.rfp_nt_structural_of_leftCanonical`, which was its whole body |

## Blueprint and paper-gap notes

- `def:appendixB_qxb` is folded into `def:appendixB_qax`, which states
  $\widehat Q_{XB}=\widehat Q_{AX}$; the four `\uses` edges that named it,
  three in `ch13_parent_hamiltonian_commuting_gap_appendix_b_commutation.tex`
  and one in `ch13_parent_hamiltonian_commuting_gap_all_chain_sector_graph.tex`,
  point at `def:appendixB_qax`.
- The parent-interaction and idempotence lemmas, the Definition D.2 analogue
  and the three-site lift lemma drop or rename the removed tags. The
  Definition D.2 analogue keeps the general theorem's tag, whose hypotheses
  (an injective tensor with a fixed structural datum) are the node's.
- `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex` and
  `docs/paper-gaps/cpsv16_parent_commuting_hamiltonian_scope.tex` cite the
  single coefficient map; the Definition D.2 footnote cites
  `rfp_nt_structural_of_leftCanonical` and `AppendixBStructuralData.ofRFP`.

## Kept

`MPSTensor.rfp_implies_nncph_ground_state_of_leftCanonical` stays. Retagging
`thm:left_canonical_rfp_chain_commutation` to the general
`MPSTensor.rfp_implies_nncph_ground_state` would give that declaration a
second blueprint owner beside `thm:rfp_implies_nncph_ground_state`, which
`scripts/blueprint_lean_sync.py --report-duplicate-tags` rejects.
