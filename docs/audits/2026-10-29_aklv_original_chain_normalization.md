# AKLV original-chain normalization

Source: AKLV, arXiv:1301.1162v1, Section 6.1 and Theorem 6.1.

The merged normalized robustness theorem consumed regional positivity and the
shifted energy bound. This change derives both from the original nearest-neighbour
positive unit interactions, their supports, and the original ground vector and gap.

For zero-based cut bonds a,b with a+2<b, the three cores contain i+1<a,
a+1<i and i+1<b, and b+1<i. Their site supports are disjoint. Ground spectral
cutoffs remain supported; their product has nonzero trace by the existing product
trace identity. A normalized nonzero column is therefore a common actual core
ground vector. Each core is shifted by its own actual minimum eigenvalue.

The complement of the core bonds has cardinality at most six. Its sum is a
positive operator bounded by six identities. The common core ground vector and
the original ground lower bound give shifted ground energy in [0,6]. Each of the
three clipped blocks adds only original positive boundary bonds to its core.
The original ground vector and gap survive the total scalar shift. Applying the
existing robustness theorem gives the actual exterior clipping, half gap, and
phase-aligned squared distance at most exp(-t/16), at the universal sufficient
cutoff 32768(6+g)/g².

The middle shift uses the corrected total minimum; the existing paper-gap note
records the printed off-by-one denominator. No individual shifted middle bond
is assumed positive. No common ground vector, regional positivity, shifted energy
bound, clipped gap or residual estimate is a supplied premise.

Moved the existing functional-calculus support theorem from the Hastings
supersite hierarchy to Circuit/SupportedFunctionalCalculus. Updated its consumer
and Blueprint anchor, without a dead compatibility alias.

Validation: independent source/API reviews cover the supported ground cutoffs,
normalization, six-bond count, scalar actions and rectangular spectral equations.
Native import, Blueprint, prose, integrity and whitespace checks are recorded in
the PR. No local Lean, Lake, build or checkdecls was run, as instructed. Every new
Blueprint mathematical result and proof remains notready pending hosted acceptance.
