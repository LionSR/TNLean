# A physical common family before the closing parameter

`MPS/AreaLaw/CommonClosingPolynomialFamily.lean` constructs one finite retained operator family from a fixed native core and polynomial closing matrix C(z)=sum_a z^a C_a. The family precedes every complex parameter z, supported exterior pair, and scalar polynomial of degree at most k. No desired interpolation formula, polynomial degree bound, tensor decomposition, spectral target, or successful sample is supplied as a hypothesis.

For the actual two-window geometry, the count is at most

    (m*k+1) * ((q*k)^(18*ell+2*floor(k/ell)))^2.

Every member retains the existing open-boundary matrix product representation with bond at most (max(1,B))^(2*k) on the paired physical alphabet. The exponent is not replaced by the printed sharper exponent. The theorem gives both the literal whole-chain matrix decomposition and its conjugated continuous-operator identity under the same canonical middle-first isometry. The same exterior factors occur in both identities.

The proof chooses genuine existing common families at the m*k+1 fixed integer nodes, then enumerates their disjoint union. This adds their cardinalities without increasing any individual member's bond. The exact interpolation weights are absorbed only into exterior factors. A direct equality of the represented matrix supplies the tensor-coordinate identity; no second coordinate isometry is chosen.

Only the closing matrix depends on z. Shared closing-linearity and placement linear maps show that every matrix entry has degree at most m, independently of chain length. The actual scalar-polynomial evaluation has entrywise degree at most m*k by the QICLean matrix-polynomial degree theorem, and QICLean's parameter-interpolation theorem derives the required finite-node identity. The coefficient matrices need not commute, and the nodes need not define Hermitian operators.

## Parameter order and scalar shifts

The exterior operators are held fixed during interpolation. They can subsequently be chosen as arbitrary functions of the requested physical parameter. In particular, the scalar term p I may remain in the left exterior operator even when z=exp((p-e)/t); no polynomial dependence of p=e+t log z is asserted or needed. The matrices evaluated at the interpolation nodes retain that same exterior operator, rather than replacing it by a different node-dependent energy shift.

For the actual uniform native soft approximation, the coefficient matrices already include the heat-expansion coefficients. Its represented Z(z) approximates the soft function without the separate p I. Thus the corresponding five-region left exterior is raw F_0+(p_2-sum_j e_j)I, with right exterior raw F_4. This differs from the earlier pointwise native approximation of the entire raw F_2. Those two constructed approximants are not identified.

The present theorem is exact structural algebra. A specialization must still supply the independently constructed native core and coefficients, derive the relevant physical approximation and cluster estimates, and address any subsequent adaptive probability argument. It is not a running-time or source-sharp bond theorem and does not change the recorded counterexamples to the printed cluster estimate. The spanning-family correction remains documented at https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

The geometric scope is ell>=1, q>=2, k>=1, a+2ell<=b and b+2ell<=L-1. The degree m and virtual dimension B may be zero. The blueprint entry `thm:common_closing_polynomial_family` states these hypotheses explicitly; it is an auxiliary to ALVV, arXiv:1602.08828v2, Proposition 5.7 and the soft construction, lines 1311–1420.
