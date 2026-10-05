# Site-dependent physical product range support

## Statement and intended use

`TNLean.PEPS.mem_range_physicalProductFamilyMap_iff` proves, for a finite site
set and finite common input and output alphabets, that

\[
\psi\in\operatorname{ran}\Bigl(\bigotimes_v F_v\Bigr)
\quad\Longleftrightarrow\quad
\forall v,\tau,\quad
\bigl(s\mapsto\psi(\tau[v\mapsto s])\bigr)
\in\operatorname{ran}(F_v).
\]

The matrices `F v` vary independently with the site. Their ranks need not
agree, and no injectivity, surjectivity, isometry, or nonemptiness hypothesis
is imposed. The Lean signature asks for `Fintype Site`, `DecidableEq Site`,
`Fintype In`, and only `Finite Out`.

This is the site-dependent version of the product-support argument underlying
Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7, source lines
2992–3019. It provides linear algebra for the separate four-cut closure
argument: take the site set to be `TorusVertex 2 2 × Bool`, with horizontal
and vertical representation-entry maps at every vertex. It does not itself
prove four-cut support, flatness, or the closure classification. It accepts
no closure-spanning premise.

## Public interface

The new module is `TNLean/PEPS/PhysicalProductFamilyRangeSupport.lean`.
All declarations are in `TNLean.PEPS`:

- `physicalProductFamilyMatrix` and `physicalProductFamilyMap`: the literal
  product matrix and its induced coefficient-space linear map.
- `physicalProductFamilyMap_apply`: the finite sum/product coefficient
  formula, proved by reflexivity.
- `physicalProductFamilyMatrix_mul` and `physicalProductFamilyMap_comp`:
  composition separately at every site.
- `physicalProductFamilyMatrix_const`, `physicalProductFamilyMap_const`:
  agreement with the existing constant-family definitions.
- `physicalProductFamilyMatrix_one`, `physicalProductFamilyMap_one`:
  product identities, including the empty site set.
- `physicalProductFamilyMap_oneCoordinate_apply`: action on one slice.
- `physicalProductFamilyMap_fixed_of_slices_fixed`: fixedness under every
  local matrix gives fixedness under their product.
- `physicalProductFamilyMap_slice_mem_range`: every slice of a product image
  belongs to its corresponding local range.
- `mem_range_physicalProductFamilyMap_iff`: the converse and equivalence.

## Proof and reuse audit

The forward implication expands a slice as a linear combination of columns
of `F v`. For the converse, each local map admits a linear section on its
range. Extend that section to the output space, using Mathlib's
`LinearMap.exists_rightInverse_of_surjective` and `LinearMap.exists_extend`.
Each resulting local retraction fixes its own coordinate slices. A finite
induction applies the one-coordinate actions, giving a full product
retraction and hence an explicit product-image witness.

The proof uses Mathlib's `Fintype.prod_sum`, `Equiv.funSplitAt`, matrix
composition, and submodule APIs. Mathlib's dependent tensor-product range
lemmas were scouted; they concern spans of pure tensors rather than the
coefficient-space slice predicate required here.

The previous constant-family module keeps its product-family machinery
private. Under this packet's new-files-only integration constraint, it cannot
be imported by ordinary public names. The new module promotes that minimal
matrix, composition, and one-coordinate infrastructure to a public
site-dependent interface and generalizes the fixedness and retraction
arguments. Existing public constant-family definitions remain unchanged.
The repeated one-coordinate calculation is a consolidation candidate:
when shared-file edits are permitted, the constant-family theorem can become
a specialization of the new theorem, with the corresponding dependency
imports rearranged to avoid a cycle. No private generated name is used.
The tactic-pattern scanner was run over the PEPS source tree; this packet
introduces no new tactic or simp-set framework.

## Regression and validation evidence

`TNLeanTest/PhysicalProductFamilyRangeSupport.lean` checks:

1. The generic signature with only `Finite Out`.
2. Empty sites, empty input, and empty output simultaneously.
3. Empty sites and input with nonempty output: all coefficient vectors remain
   in the product range, as the empty tensor product requires.
4. A nonempty site set with empty input: the product range is zero.
5. A nonempty site set with empty output.
6. Different local ranks, zero and two, forcing the full product range to zero.
7. Different nonzero local ranks, one and two, with an explicitly nonzero
   supported vector in the product range.
8. Independent horizontal and vertical matrix families on all eight bonds of
   the native two-by-two torus.
9. A guarded axiom report containing only `propext`, `Classical.choice`, and
   `Quot.sound`.

The source and test passed the pinned toolchain with one worker and
`autoImplicit=false`, `relaxedAutoImplicit=false`,
`linter.mathlibStandardSet=true`, and `warningAsError=true`.
Observed source elaboration took 3.2 seconds and the final test 2.5 seconds.
A private symlink overlay reused the supplied exact dependency environment;
new artifacts were written only in that private overlay. The complete named
TNLean dependency closure matches the supplied cache worktree's source, and
the QICLean dependencies in this closure match the pinned `2ba242ee` source.
The prebuilt Mathlib artifact was verified; Mathlib was not rebuilt.

The new Lean files contain no `sorry`, `admit`, `native_decide`, `unsafeCast`,
or new axiom declarations. No root import router, existing source, blueprint,
or shared audit file was changed. A full aggregate build and full repository
CI were not run by this targeted packet.
