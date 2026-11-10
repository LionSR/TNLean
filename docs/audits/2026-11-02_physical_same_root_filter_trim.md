# The physical raw filter and actual same-root trim

The original positive chain Hamiltonian H=sum h_i supplies its own norm
scale M=||H||. The actual spectral values mu<nu and the original global gap
gamma imply M>mu>=0 and mu+gamma<=nu<=M. Thus c=gamma/(M-mu) lies in (0,1].
No unique ground vector, supplied filter, spectral ceiling or gap cap is
assumed. The full original closed ground span is retained.

The actual centered normalized matrix B=(M I-H)/(M-mu) fixes the entire
original ground space and contracts squared norms on its complement by
at most 1-c. The proof uses QICLean's actual isolated-ground spectral
construction. The literal printed filter I-H/M is a nonzero scalar
multiple of B. Mathlib's invariance of submodule images under nonzero
scaling proves equality of the image spaces, their standard orthonormal
bases, and the actual subsequent collective trims, for every candidate.

Consequently the stable recurrence

    delta_next <= (1-c/4) delta + c eta/8

holds directly for the actual raw-filter-and-trim operation at the same
native root. The common reference and its accuracy, all-span MPS bond,
and threshold budgets remain explicit inputs. The squared whole-exterior
reference rank remains in the threshold budget. Choosing these inputs
from the actual physical reference, iterating the actual operation and
performing final Ritz extraction are separate obligations. The correction
to the printed raw overlap gain is documented in
`docs/paper-gaps/alvv16_final_filter_gain.tex`.
