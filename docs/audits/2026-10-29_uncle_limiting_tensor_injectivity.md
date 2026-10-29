# Injectivity of the two-site uncle tensor

Issue #10284; native tracker #7685. Baseline main `3af48c184`.
Source: `Papers/1210.6613/UncleHMPS.tex:973–1016`, definition of injective
perturbation and Lemma `lemma:inj-perturbation`, arXiv:1210.6613.

## Exact algebraic target

For square blocks `A_i` and `B_i` of sizes `a` and `b`, and rectangular
blocks `R_i,L_i`, the source's injective perturbation condition is that
the full one-site matrices `T_i = [[A_i,R_i],[L_i,B_i]]` span the full
matrix algebra of size `a+b`. It is not injectivity of the diagonal
perturbation blocks `P_i,Q_i`, nor merely injectivity of the perturbed
tensor at a nonzero parameter.

The uncle tensor already defined in `UncleTensor.lean` has letters
`U_ij = [[A_i A_j, A_i R_j+R_i B_j],
         [L_i A_j+B_i L_j, B_i B_j]]`.
The lower-left summands occur in the opposite written order in the paper;
addition of matrices makes these expressions equal. No source correction
is needed.

## Written proof

`UncleInjectivity.lean` extracts coefficients `c_i` for the identity from
the full perturbation span, using Mathlib's finite linear-combination
description of a span. The four block equations are
`sum c_i A_i=I_a`, `sum c_i B_i=I_b`, `sum c_i R_i=sum c_i L_i=0`.
Contracting the first physical uncle leg then gives
`sum c_i U_ij=T_j`. Thus every perturbation letter lies in the uncle
span, which must be the full algebra. The proof uses the existing
`Kraus.IsInjective` span formulation and existing blocking equivalence;
there is no supplied uncle-injectivity premise or parallel predicate.

The paper's proof chooses separate identity coefficients for individual
blocks. The single full-identity contraction is the same coefficient
argument with one common physical vector. It avoids four repeated
blockwise witness constructions.

The standing source setting has a block-injective background `A ⊕ B`
and positive block dimensions. The span implication itself is stronger:
it holds for arbitrary natural dimensions, including zero blocks, under
the full perturbation injectivity hypothesis alone. It imposes no extra
dimension, irreducibility, normality or genericity hypothesis. The source's
separate assertion that injective perturbations are generic when the
physical dimension is large enough is not proved here.

Two corollaries discharge the actual uncle-injectivity hypothesis in the
existing local interaction and finite-periodic Hamiltonian limits.
`UncleParentLimit.lean` is reused without modifying or re-proving its
operator-limit argument. The diagonal perturbations remain arbitrary.

## Verification boundary

This is a source-written proof candidate. The user expressly requested
no local Lean invocation, so no compilation or Lean builds were run.
The new Blueprint lemma and corollary remain `notready`, and #10284 stays
open until verification and integration. Source/API inspection, generated
imports, formatting and integrity checks do not establish kernel acceptance.
No proof placeholders, new axioms or persistent Lean fixtures are added.
