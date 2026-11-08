# Product forms with site-dependent physical dimensions

Source: Hastings, *Solving gapped Hamiltonians locally*,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1024–1039 (eq. `mpf`) and
1069–1077 (grouping the indices of a Trotter product).

`TNLean.Lattice.ProductForm` now takes a dimension family `d : ι → ℕ` in
place of one physical dimension `q`. Operators act on the configurations
`(j : ι) → Fin (d j)`, the site operators of site `j` are `d j × d j`
matrices, and the expansion uses the product `Matrix.piKronecker` of
matrices whose labels vary with the site. A common dimension `q` is the
constant family `fun _ ↦ q`, so every one-dimension statement is the
specialization of the same predicate; no second product-form structure is
introduced. This updates the note of 2026-11-02
(`2026-11-02_hastings_active_indices.md`), which recorded the site-dependent
product form as unformalized.

Generalized in place:

* `ProductForm`, `HasProductForm`, `HasProductForm.mono`, `ProductForm.one`,
  `ProductForm.mul`, `ProductForm.pow`, their index counts,
  `hasProductForm_list_prod`, `HasProductForm.pow`,
  `ProductForm.restrict`, `ProductForm.card_index_restrict` and
  `HasProductForm.pow_of_even` hold for every dimension family.
* `ProductForm.ofSupported` and `ProductForm.card_index_ofSupported` take a
  matrix-entry support `Entropy.IsSupportedOn` and a configuration supplying
  the labels off the support. For a common dimension, membership in
  `QuantumCircuit.supportedOperators q` gives this support through
  `QuantumCircuit.isSupportedOn_of_mem_supportedOperators`.
* `exists_productForm_list_prod_card_index`,
  `exists_productForm_trotterProduct_card_index` and
  `exists_productForm_trotterProduct_card_index_of_dist_le` count `d_j²`
  values per index component at the site `j`. The two bounds assume every
  dimension positive, as the one-dimension versions assumed `q` positive.

Added:

* `exists_productForm_trotterProduct_card_index_eq`: for sweeps with one
  factor per centre, the index set at `j` has as many values as the maps from
  the active occurrences `trotterActiveOccurrences X n j` to pairs of physical
  indices at `j`, that is `(d_j²)^(n c_j)` values (`card_trotterActiveIndices`).
* `isSupportedOn_exp_smul`: exponentials of scalar multiples preserve a
  matrix-entry support, for any dimension family.
* `Matrix.piKronecker`, `Matrix.piKronecker_apply`, `Matrix.piKronecker_mul`,
  `Matrix.piKronecker_one`.

Renamed:

* `TNLean.Lattice.ClusterExpansion.sum_smul_rectKronecker_single_apply` is
  now `TNLean.Lattice.ClusterExpansion.sum_smul_piKronecker_single_apply`,
  stated for `Matrix.piKronecker`, which the generalized expansion uses.

The radius and diameter constructions `hasProductForm_of_mem_supportedOperators_radius`,
`hasProductForm_of_mem_supportedOperators`, the Trotter statements
`hasProductForm_trotterProduct_of_radius`, `hasProductForm_trotterProduct_of_dist_le`,
`LocalHamiltonian.hasProductForm_trotterProduct`, and the cluster-expansion
product forms keep a common dimension `q` and conclude
`HasProductForm (fun _ ↦ q) near ρ`.
