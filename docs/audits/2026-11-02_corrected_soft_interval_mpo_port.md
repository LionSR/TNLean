# A corrected one-interval soft-truncation MPO

This contribution constructs an operator approximation for one regional soft
replacement, including the exterior sum and scalar shift. Its independent
parameters satisfy t >= 3m and m >= 1. The interactions are the actual
nearest-neighbour Hermitian matrices of norm at most one. For the regional
sum A an explicit lower energy epsilon I <= A is retained.

Put W=t 2^(m+1) and b=2(exp(1/3)-1), so 0<b<1. The displayed logarithmic
cluster order r determines actual site-dependent operator tensors of dimension

    D = 1 + N q^2 + (m+1) r^2 q^r

and error at most every requested xi>0. The physical chain has N+1 sites
and q>=1. The heat operators are approximated separately and combined by
diagonal blocks; no approximate heat operator is raised to power m. The
regional energy shift remains outside the norm-one local terms, and its
normalization cancels exactly from the error bound.

For fixed q, the logarithm of this dimension is

    O_q(m + log_+ t + log(N+1) + log_+(1/xi)).

Thus m=O(log(N+2)), polynomially bounded t, and inverse-polynomial accuracy
give a polynomial bond. Polylogarithmic bounds on m, log_+ t and log_+(1/xi)
give a quasipolynomial bond. The dependence on m(N) and t(N) is not discarded.
The source GEN choice m=4 and t proportional to a buffer width is covered
at the representation level once t>=12.

The cluster selector counts connected components of interaction labels and
retains the lower-energy normalization. The existing positive two-qubit and
negative forty-qubit counterexamples, together with the false-source/open
record, remain unchanged. The new statement is the corrected estimate,
not the printed physical-support theorem. This contribution does not prove
multi-region spectral comparisons, the unrestricted parameter statement,
GEN, the final algorithm, or a computational running-time bound. It does
not close issue 9847.

## Source selection

Twenty-five previously absent production modules are selected individually
from the preserved cluster/MPO and soft-MPO sources. Existing mathematical
files, including `ProductForm` and `TraceChainOperator`, are retained and used
by the verified port. No old branch, old generated import file, or old
complete blueprint chapter is restored.

The finite heat expansion imports the existing scalar soft definition
directly; it does not require the separate soft-versus-hard comparison. All 61
new public declarations across the two contributions have mathematical book
entries. No matching declaration headers already exist on either current base.
The accuracy signatures are generalized directly, without compatibility
aliases.
