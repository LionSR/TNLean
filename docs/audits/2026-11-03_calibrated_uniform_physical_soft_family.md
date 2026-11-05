# Calibrated numerical choices for the same physical soft family

The public theorem
`ALVV.exists_calibrated_uniform_physical_soft_improving_family` chooses
all numerical scales and a natural polynomial bond ceiling before the
chain length. It then retains the complete physical conclusion of
`exists_uniform_physical_soft_improving_family` for those choices.
Its source context is ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1311–1420.

## Numerical choices and their order

For fixed q >= 2 and g > 0, the uniform scalar calibration is applied
once at exponents (24,10,10). It chooses u >= 2 and sets

    ell=u^8, m=u^10, k=u^16, t=3m, T=u^9,
    D=(m*k+1)*(q*k)^(36*ell+4*floor(k/ell)),
    M=3*t*(1+log m)+4*ell+34,
    tau=1/(D^24*M^10),
    xi=min(1,tau*g^2/[20000*(M+g+8)]).

The actual squared-complement envelope is the same expression as in the
explicit-budget physical theorem. Both residual inequalities are derived,
with T0=T1=T. The proof also derives D >= 2, M >= 34 and

    Delta <= 1/(D^12*M^10),
    3*tau/200 <= ((3/100)/D^2)^2/100,
    3*tau/200 <= 1/200,
    D^12*Delta <= 1/100000.

The stronger M-dependent estimate is retained for later energy estimates;
it is not replaced by the coarse last inequality. Positivity and upper
bounds for tau and xi are conclusions, not numerical feasibility inputs.

The geometric-order polynomial theorem is applied with coefficient
multiplicity m+1 and heat coefficient budget t*2^(m+1). It chooses natural
Cpoly >= 1 and ppoly before every N. With EXACTLY the native cluster order
and bond B_N of the explicit physical theorem, it proves

    (max(1,B_N))^(2*k) <= Cpoly*(N+1)^ppoly.

Since B_N >= 1, the geometric theorem's expression
(2*(m+1)*order^2*q^order)^(2*k) is the same permitted member bond.
The common count upper bound D, soft scale and order, filter degree,
precision, norm ceiling and polynomial constants precede N and the word
length. The logarithmic cluster order and the native bond do depend on N,
exactly as displayed.

## The actual family is retained

For every supplied original chain and natural two-window geometry, the
explicit-budget physical theorem is invoked once with the derived scalar
budgets. Its entire conclusion is preserved: the same original minima,
actual native core, polynomial closing coefficients, common left operators,
represented soft matrices, their own spectral clusters, actual Chebyshev
operators and all ordered-word estimates.

The scalar polynomial inequality is returned alongside the original
native member-bond certificate. It bounds the bond allowance of those
SAME operators. It does not select an unrelated polynomial MPS family.
The existing `IsOpenMPS.mono` can enlarge that allowance if a consumer
requires the polynomial ceiling as the literal bound argument.

A single locally defined proposition-valued function names the complete
unchanged physical conclusion in the statement. It is fully expanded in
that statement; it is neither a global predicate nor an additional premise.
The proof first establishes the physical conclusion at abstract scales,
then instantiates the calibrated choices. This avoids reconstructing a
long dependent spectral and word certificate under specialized powers of u.
There are no source options, diagnostic commands, supplied successful
samples, spectral-gap or approximation assumptions absent from the physical
inputs, or additional decomposition hypotheses.
