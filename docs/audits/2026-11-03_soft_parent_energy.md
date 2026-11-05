# The actual central soft replacement and regional energy

The regional Hamiltonians are the original interaction sums, with no supplied
minimum, residual, native matrix or decomposition. Let P be the sum internal
to [l,r), and M the sum internal to [u,v), where l<=u<=v<=r and each collar
has at most 2ell sites. The interactions are positive contractions with their
designated nearest-neighbour supports, and the local dimension is positive.
No spectral gap or unique-ground-state assumption is imposed.

The original interactions determine attained minima eP,eM before every p,t,m.
For eM-10<=p<=eM, t>0 and m>=2, define the literal replacement

    R = P-M+pI+h_{m,t}(M-pI).

The theorem constructs its attained minimum eSoft and a positive matrix K on
the native Hilbert space of [l,r), with

    R = localLift(K)+eSoft I,
    norm(K) <= t(1+log m)+4ell+14.

The matrix, its actual minimum and K are selected before the auxiliary tail
cutoff T and before every candidate subspace. The raw R is defined before
its true minimum; knowledge of that minimum is not an input to R.
For t,T>=48, set

    rho = 32 exp(-(T-48)/8)+(t/m)(T/t)^m.

Then eSoft<=eP<=eSoft+rho. For every vector g in the entire ground space
of the original full chain, the quadratic energy of localLift(K) is at most
(2+rho)norm(g)^2. The norm concerns the centered matrix R-eSoft I, rather
than the raw R. Weak cuts, empty intervals, L=0 and local dimension one
are retained in the statement.

## Construction

Set the original bonds outside the parent interval to zero. The actual
five-region construction applies at cuts 0,l,u,v,r,L. The two exterior
regional sums vanish, the two collars are unchanged, and only the central
sum is softened. The estimated-center defect is at most ten; the actual
crossing set has cardinality at most four. The existing reverse residual
applied to an attained soft ground vector gives the comparison of minima.
The positive soft matrix has an upper bound from the actual collar lengths,
the corrected harmonic cap and the crossing-bond count. Subtracting its
minimum adds at most ten, yielding the stated norm.

The centered replacement is supported on the parent interval. A fixed
complementary configuration gives an actual positive regional matrix K
with the same upper norm cap. This generic construction also covers empty
configuration spaces and belongs to QICLean. The order inequality

    R-eSoft I <= P-eP I+(eP-eSoft)I

and the proved original-ground regional energy bound of two give the energy
estimate. An original full ground vector is not assumed to be a ground
vector of P.

## Relation to the source

These are corrected auxiliaries to ALVV, arXiv:1602.08828v2, Figure
`fig:generate`, lines 1348-1392, and the separate untrimmed energy candidate
at line 1631 in Figure `fig:algo1`. The source distinctions are documented in
[the energy-centering note](../paper-gaps/alvv16_soft_regional_energy_centering.tex).
The definition requires a one-sided energy center, whereas the efficient
DG theorem accepts an absolute-error estimate. The parent estimate also
concerns a larger interval than the softened middle. Neither identification
is assumed here.

The scalar harmonic-cap correction is owned by QICLean:
https://sirui-lu.com/QICLean/paper-gaps/alvv16_soft_truncation_log_bound.pdf.
The false printed soft-energy and cluster estimates, and their explicit
counterexamples, remain in their respective existing notes. No cluster
approximation theorem is used in this exact functional-calculus argument.

The original ground space and the generated soft spectral target are
separate. The source energy candidate is an untrimmed powered family image
viable for the latter. The estimate here must be transferred quantitatively
to that same target before it can bound the candidate compression. This
contribution does not complete that transfer, the recursive energy invariant,
the generation procedure, or its running-time bound.
