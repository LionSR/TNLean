# Finite-site product forms in Hastings' thermal construction

Source: Hastings, *Solving gapped Hamiltonians locally*,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 176–188 and 1024–1077.

`TNLean.Lattice.Locality.ProductForm` is the single structure recording the
product expansion. It allows an arbitrary finite site set, site-dependent
physical dimensions, and coefficient neighbourhoods. Coefficient locality is
Mathlib's `DependsOn`. The common finite auxiliary index set is part of the
representation, not an assumed bound.

The former structure `TNLean.Lattice.ProductForm` is now its specialization
to walk neighbourhoods and constant physical dimension. Its generated
constructor and projections are supplied by the canonical structure;
no duplicate structure or deprecated projection aliases remain.
`TNLean.Lattice.HasProductForm` specializes the same existence predicate,
and `TNLean.Lattice.IsLocalCoefficient` specializes `DependsOn`.
These walk-local specializations remain used by the local-Hamiltonian and
truncated-cluster theorems. Their mathematical statements are unchanged.
The truncated-cluster construction adapts the application of its
coefficient-locality theorem and restates the entry product as the same
Kronecker product before applying the existing summation identity.

The generic multiplication theorem and supported-operator construction replace
the duplicate planar proofs. The counted construction uses a private
site-dependent expansion while recording its cardinalities, then converts it
to the same public structure. For one occurrence of each centre per sweep,
the common auxiliary index has cardinality `(D * D) ^ (n * S)`, where
`D = max 1 (sup_j d_j)` and `S` is the largest radius-ball cardinality.
An arbitrary list counts factor occurrences with multiplicity instead.

The finite Trotter assertions include empty sites, empty supports, zero physical
dimensions, and zero steps. They do not supply a Gibbs convergence estimate.
The separate truncated operator still has a planar-domain restriction and
an unproved quantitative cluster-label count; both remain documented in
`docs/paper-gaps/hastings05_planar_domain_scope.tex` and tracked by #9854.
