# A physical soft family chosen before the regional estimates

The public theorem
`ALVV.exists_uniform_physical_soft_improving_family` constructs an actual
common family from the original positive-contraction nearest-neighbour
interactions. Its source context is ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1311–1420. The statement is
a corrected auxiliary with explicit residual and geometry conditions; it is
not identified with the unrestricted source algorithm or its running time.

## Quantifiers and the represented operator

The parameters q, ell, m, k, g, tau, t, T0 and T1 precede the chain length
and the interactions. The hypotheses include q >= 2, ell,k >= 1, m >= 2,
0 < tau <= 1, t >= 3m, and both corrected residual budgets. For the natural
five-region decomposition, the actual original regional minima e_j and the
centered original ground energy E are selected once. Fixed native tensors,
polynomial closing coefficients and one finite left family W are then
selected before every p_j in [e_j-10,e_j], j in {0,2,4}.

The middle is represented by

    Z(z) = trace-chain(Acore, sum_a z^a C_a),
    z = exp((p_2-e_2)/t).

Writing F_j = p_j I + h_(m,t)(A_j-p_j I), the actual approximant is

    Ghat_p = G_p - F_2 + p_2 I + placement(Z(z)).

The scalar p_2 I remains exact. The raw two-window alphabet has exterior
terms F_0 + (p_2 - sum_ALL_FIVE e_j) I and F_4. Its two windows and the
native middle sum exactly to Ghat_p. The proof never substitutes an
independently chosen pointwise approximant or a hard-clipped matrix.

The native bond is the explicit logarithmic-cluster-order expression B in
the theorem. The common left count and individual paired-alphabet bond are

    n <= D = (m*k+1)*(q*k)^(36*ell+4*floor(k/ell)),
    bond(W_i) <= (max(1,B))^(2*k).

The approximation is Hermitian, differs from the same actual G_p by norm
at most xi, and has norm at most Msoft+xi. Its own canonical spectral span
at E+g/4 equals its span at E+3g/4. Its dimension is that of the original
full ground space, and the two spaces are mutually 3*tau/200-close.

The actual Chebyshev operator K_p has a tensor decomposition with these
same W_i, preserves the transported target and its complement, has minimum
gain one on the target, and has squared complementary norm at most

    Delta = (2*exp(-2*k*sqrt((g/2)/(Msoft+xi+4+g))))^2.

Every literal ordered-word image of length r has dimension at most
D^r dim(S) and viability loss at most Delta^r/(1-delta)^2. No positivity
or identity assertion is made for the unsquared filter. Delta < 1 is not
an extra conclusion for arbitrary k; strict error reduction requires a
suitable numerical choice of the displayed parameters.

## Proof and foundations

The proof uses the physical uniform-cluster factory once, the uniform
native soft-middle construction once, and the common polynomial-closing
family once. A private physical lemma establishes the matrix polynomial
decomposition and the approximant's own cluster. A second private matrix
lemma applies the existing actual-cluster Chebyshev theorem and its
ordered-word estimate. These lemmas separate mathematical stages without
introducing another predicate, structure, family or proof assumption.

Rewriting the complete isometry-conjugation expression was expensive.
The final proof transports the matrix equality through polynomial
evaluation and invokes the existing canonical Kronecker-conjugation
identity. The production source has no diagnostic commands or resource
settings. Earlier statement-scope and default-heartbeat failures remain
recorded in the private attempt logs; they are not verification evidence.

The final production source passed the strict actual-name check in
18.311 seconds against immutable TN 8f85b0be / QIC cc2569b6, with 626
selected source/object pairs guarded. The imported public foundation audit
passed in 8.245 seconds and reports only propext, Classical.choice and
Quot.sound. Temporary foundation commands were deleted after the check.
No Mathlib source, provider cache or package input was rebuilt or changed.

The new declaration resolves in the source/blueprint comparison; its
entry and proof are marked complete. The source-only worktree has no
companion checkouts, so its whole-library declaration scan cannot resolve
external declarations. The complete dependency-aware blueprint and ordinary
build remain required in the coordinated integration. A two-page local
reader was rendered and visually inspected; its only unresolved references
are the two earlier lemmas omitted from that isolated reader.

## Remaining scope

The common family can depend on the actual original Hamiltonian and its
true regional minima; its independence concerns the subsequent estimated
centers. This existence theorem is not an efficient procedure for computing
those exact minima. It does not identify the source's fourth-order choice,
prove the adaptive soft generating algorithm, or supply a running-time
bound. A fixed-parameter polynomial bond in the chain length must not be
substituted for a bound when the order or degree varies with that length.

The source's false uniform soft-energy estimate and false spatial cluster
estimate remain documented, with their counterexamples unchanged, in
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
