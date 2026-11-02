# Active Trotter occurrences with site-dependent dimensions

Source: Hastings, *Solving gapped Hamiltonians locally*,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1069–1077.

Pull request #10254 proposed a second product-form structure allowing a
different physical dimension at each site, together with a split of
`TNLean/Lattice/ProductForm.lean`. Main has since rewritten that file around
`TNLean.Lattice.ProductForm q near ρ`, with one physical dimension `q` and a
finite index type that may vary with the site. The one-dimension Trotter
results of the pull request are already on main:
`ProductForm.ofSupported`, `exists_productForm_list_prod_card_index`,
`exists_productForm_trotterProduct_card_index` and
`exists_productForm_trotterProduct_card_index_of_dist_le` in
`TNLean/Lattice/TrotterIndexCount.lean`. A second public product-form
structure would duplicate this predicate, so the varying-dimension structure
and its counted construction were not carried over.

Only `TNLean/Lattice/TrotterActiveIndices.lean` was kept. It depends only on
`TNLean.Lattice.FiniteDomain` and counts the factor occurrences acting at a
site, with exact cardinality `(d * d) ^ (n * c_j)` for any local dimension `d`.
The count does not by itself provide a product form with site-dependent
dimensions; that remains unformalized.
