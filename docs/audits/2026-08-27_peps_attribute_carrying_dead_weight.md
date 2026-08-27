# PEPS attribute-carrying dead weight

This audit records the retirement of three zero-reference declarations in the
PEPS subdirectories that a name search alone could not have cleared, because
each carries an attribute — two `@[simp]` lemmas and one `instance` — through
which it can act on downstream proofs without ever being named. It follows the
repository-local pass-through exception of `docs/project_conventions.md` §Style.

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.notMem_vertexComplementVertices_self` (`@[simp]`, `TNLean/PEPS/VertexComplement/Basic.lean`) | `TNLean.PEPS.mem_vertexComplementVertices_iff`, the sibling `@[simp]` iff immediately above it in the same file, which subsumes it |
| `TNLean.PEPS.instFintypeVertexComplementPhysicalConfig` (`TNLean/PEPS/VertexComplement/Basic.lean`) | `Pi.fintype`, found through the reducible `abbrev VertexComplementPhysicalConfig` — the removed body was literally `inferInstance` |
| `TNLean.PEPS.edgeComplementConfigSplitAt_fst` (`@[simp]`, `TNLean/PEPS/EdgeMiddlePhysical/KernelDescent.lean`) | none — the forward direction of the splitting equivalence is used nowhere; the lemma actually consumed in the file is the sibling `edgeComplementValue_edgeComplementConfigSplitAt_symm` |

## What was checked

The clearance for all three is a **root `lake build`**, not a name search. This
distinction is the point of the note. A `@[simp]` lemma contributes to the
default simp set of every importing module, and an `instance` contributes to
typeclass synthesis in every importing module, so neither leaves a textual
occurrence at the sites where it does its work. `lake build` on the root target
is what exercises the importers; a module-target build compiles a module's
dependencies, not its dependents, and would have proved nothing here.

**The self-nonmembership lemma.** `mem_vertexComplementVertices_iff`, the
`@[simp]` iff directly above it, rewrites `w ∈ vertexComplementVertices v` to
`w ≠ v` for every `w`, so `simp` reaches the removed lemma's conclusion by the
survivor plus `ne_eq`/`not_true`. Both carried the same
`omit [DecidableRel G.Adj]`; the survivor's is untouched. The consumers most
likely to notice a change in the simp set — `VertexComplement/Injective.lean`,
the `RegionBlock` modules, and `FundamentalTheorem/OneVertexComparison.lean` —
all build unchanged.

**The `Fintype` instance.** `VertexComplementPhysicalConfig` is an `abbrev`,
hence reducible, so synthesis unfolds it to the pi type
`(w : {w : V // w ≠ v}) → Fin d` and finds `Pi.fintype` on its own; the removed
instance's body was `inferInstance`, that is, exactly this search performed once
and re-registered under a new name. Its only risk was a `maxSynthPendingDepth`
interaction — the package sets that option to 3 — and the root build shows the
depth is not reached. The `abbrev` itself is retained: it is used in
`VertexComplement/Injective.lean`, in ten places in
`FundamentalTheorem/OneVertexComparison.lean`, in `RegionBlock/Recovery3.lean`,
and by `vertexComplementWeight` and `vertexComplementTensorFamily` in its own
file.

**The first-component projection.** `edgeComplementConfigSplitAt_fst` states
that the forward direction of the splitting equivalence reads off the
complement value. Nothing in the repository uses the forward direction; the
`symm` direction is what the file's own descent argument needs, and that is
`edgeComplementValue_edgeComplementConfigSplitAt_symm`, which survives and is
consumed later in the same file. The three real importers of `KernelDescent.lean`
— `InsertionAlgebra.lean`, `InsertionRealization.lean`, and
`EdgeGaugeFamily.lean` — build unchanged, as does the private helper
`edgeComplementConfigSplitAt_symm_apply_incident` between the two.

No member of the batch came back out: the root build was green on the first
attempt with all three removed.

## Transition declarations

All three names have zero references anywhere outside their own declarations,
and no blueprint `\lean{...}` tag names any of them. No deprecation alias is
warranted under the pass-through exception.

## Ledger

These three are an attribute-carrying slice adjacent to ledger entry S2
(zero-reference declarations). S2's written scope excluded instances and
`@[simp]`/`@[grind]`-tagged lemmas, on the reasoning that a name search cannot
clear them; the root build can, so that bullet is widened rather than the
removals being filed under a scope that excluded them.
