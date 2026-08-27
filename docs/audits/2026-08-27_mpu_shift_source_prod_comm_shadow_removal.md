# MPU shift-source four-way product shadow and single-use restatements

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for one public reindexing equivalence that
duplicated a Mathlib equivalence, together with four `private` entry-formula
restatements that were inlined into their sole consumers. All five removals are
in `TNLean/MPS/MPU/Examples/ShiftSourceFormulas.lean`.

## Removed declarations

| Removed | Replacement |
|---|---|
| `MPOTensor.shiftExampleU₃SourceVSwapShuffle` (public, `TNLean/MPS/MPU/Examples/ShiftSourceFormulas.lean`) | `Equiv.prodProdProdComm` (Mathlib, `Mathlib/Logic/Equiv/Prod.lean`) |
| `MPOTensor.shiftExampleU₁_sourceU_product_apply` (`private`, same file) | inlined into the single `calc` step of `MPOTensor.shiftExampleU₁_sourceU_apply` |
| `MPOTensor.shiftExampleU₁_sourceV_product_apply` (`private`, same file) | inlined into the single `calc` step of `MPOTensor.shiftExampleU₁_sourceV_apply` |
| `MPOTensor.shiftExampleU₂_sourceU_product_apply` (`private`, same file) | inlined into the single `calc` step of `MPOTensor.shiftExampleU₂_sourceU_fourSpin_apply` |
| `MPOTensor.shiftExampleU₂_sourceV_product_apply` (`private`, same file) | inlined into the single `calc` step of `MPOTensor.shiftExampleU₂_sourceV_fourSpin_apply` |

## The four-way product shadow

The removed equivalence sent a pair of pairs $((a,b),(c,e))$ to $((a,c),(b,e))$
with an identity inverse and two `rcases`-and-`rfl` round-trip proofs. That is
exactly the four-way commutativity of the product, which Mathlib supplies as
`Equiv.prodProdProdComm` with the same underlying function and the same inverse.
The one definition using it, the composite-site source-column equivalence for
$v_3$, now names the Mathlib equivalence at the four factors `Fin d`; the entry
formula that evaluates it drops the shuffle from its `simp` set, because
Mathlib's `@[simps (attr := grind =) apply]` attribute already tags the applied
form as a simp lemma. The unused-simp-argument linter, which runs under the
package lean options, reports nothing on the shortened `simp` call.

The sibling `MPOTensor.shiftExampleU₃SourceUSwapShuffle` was left in place. It
sends $((a,b),(c,e))$ to $((e,b),(c,a))$, which is not a four-way product
commutation, and has no Mathlib counterpart.

## The single-use entry-formula restatements

Each of the four removed `private` theorems stated the tensor-product entry
formula for one supplied source of one shift example, at one fixed
instantiation, and was proved by a single `simpa only` from the general
`SourceFactors.sourceU_independentTensorProductOfIdentityWeight_apply` or its
`sourceV` counterpart. Each had exactly one consumer, whose first `calc` step
retyped the removed statement verbatim before invoking it. The `simpa only`
line now sits in that `calc` step directly, so the fixed instantiation is
written once rather than twice.

The two `U₃` restatements were kept: each has two consumers, at different
instantiations of the four spin indices, so inlining them would duplicate their
bodies rather than remove a copy.

## What was checked

No blueprint `\lean{}` tag names any of the five removed declarations, no entry
of `docs/glossary.md` names them, and no note in `docs/paper-gaps/` cites them.
Both use sites of the removed shuffle were inside its defining file. The paper
citation for arXiv:1703.09188, equation `vdagger` (lines 520--543), is retained
on the docstring of `MPOTensor.shiftExampleU₃SwapSourceVColumnEquiv_apply`,
which is where the reader now meets that reindexing. The tagged endpoints of
the module — the identity-tensor-identity and swap standard-form theorems, and
the two-site block capstones of
`TNLean/MPS/MPU/Examples/ShiftSourceBlockedFormulas.lean` — keep their
statements unchanged.

Because the shuffle was public, `docs/project_conventions.md` §Style requires
the pull-request body to carry the same removal-and-replacement table; it does.

## Net effect

About 72 lines removed from `TNLean/MPS/MPU/Examples/ShiftSourceFormulas.lean`.
