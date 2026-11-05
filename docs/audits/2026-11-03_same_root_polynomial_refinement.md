# Polynomial final refinement of a prescribed viable root

For fixed positive local dimension, gap lower bound and positive integer
filter parameter, the coefficient and natural exponent are chosen before
length, interactions, multiplicity and requested accuracy. For each
physical chain and positive accuracy, one refinement count, positive
trimming radius and integer coefficient are chosen before every candidate
and dimension bound. The final MPS bond is that coefficient times the
square of the supplied candidate-count bound.

The initial candidate is the actual supplied full-interval space. Its only
analytic requirement is 3/200-closeness to the original full ground space;
no initial MPS representation is assumed. Its literal raw-filter-and-trim
iterate supplies the terminal space, and the final space is the actual
lowest-r Ritz space of its compression. The theorem returns the terminal
dimension bound, Ritz inclusion, exact ground multiplicity, both directed
errors at most half the requested accuracy, and the every-vector MPS bound.

The nonflat branch uses the existing automatic same-candidate theorem with
its first dimension parameter equal to one. The existing uniform scalar
refinement-cost theorem is applied at numerical comparison values
Btree=1, s=1 and Ktree=0. Its extra factor Dfilter^12 is at least one;
discarding it bounds the actual coefficient. These are solely scalar
comparison arguments. They select no initial reference space, alternate
recursive output or independent MPS approximant.

The spectral hypothesis is only membership of the original ground energy
and the spectral-gap alternative. Existence of an excited value is split
on internally. In the flat branch, zero actual rounds retain the same
root and its exact actual Ritz space, with zero projection errors. The
positive scalar raw filter may vanish, so it is not applied in this case.
The positive-dimensional scalar local case and empty-chain case are included.

This is a conditional final-refinement auxiliary to ALVV,
arXiv:1602.08828v2, lines 1801–1817. The physical recursive construction
must still supply its own viable initial root and polynomial dimension
bound. The initial tree's trimming radius may be fixed independently
of the accuracy-dependent final radius; the theorem does not identify
these two choices. The capped-gap reference estimate and corrected
normalized-gain iteration are recorded in
`docs/paper-gaps/alvv16_approximation_parameters.tex` and
`docs/paper-gaps/alvv16_final_filter_gain.tex`. No running time or printed
sharp inverse-gap estimate is asserted.

No Mathlib source build or cache mutation is used.
