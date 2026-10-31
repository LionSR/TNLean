# Physical sector support of actual projector kernels

Context: #10386. This child of #10408 supplies the mixed-sector exclusion
needed for a proposed physical alphabet of three main-sector and two
particle-sector letters. It does not supply the remaining main-sector
periodic classification or assert a full source counterexample.

The maps are the shared `Function.Embedding.euclideanExtendByZero` on the
actual pointwise word embeddings. The generic owner commit is reused from
the varying-physical-alphabet work; no second physical-vector embedding,
normalization factor, or configuration record is introduced. Mathlib's
`Submodule.map` and supremum describe the sum of the two local spaces.

A word with two sector labels is outside each one-sector word embedding.
The standard outside-range coefficient identity makes both embedded vectors
zero there, hence every vector in the sum is zero there.

The actual local interaction is the complementary orthogonal projection of
that sum. Positivity of the existing periodic Hamiltonian gives every actual
local section equation. Each section therefore belongs to the local sum.
For a nonzero global coefficient, the window starting at each site forces
equality of that site's label with its successor's label. The promoted
`Fin.cyclic_induction` proves all labels equal. Thus every mixed word has
zero coefficient in the actual Hamiltonian kernel at every M ≥ R ≥ 2.
The final specialization uses the standard `Fin.castAddEmb b` and
`Fin.natAddEmb a`, exactly the two parts of `finSumFinEquiv`.

The public result requires no supplied local-support conclusion in its
two-embedded-sector form, no global kernel decomposition, and no local-term
annihilation supplier. Local spaces S and T remain arbitrary so the actual
Weyl boundary range and pure particle line can be inserted directly.
Identifying the restrictions of the remaining uniform-sector coefficients
with the separate component Hamiltonian kernels is a subsequent step.

## Verification

No local Lean, Lake, build, elaboration or checkdecls is run, as requested.
All six new declarations and their supporting Blueprint entries are
`notready`. Source and native checks are recorded in the draft PR; they do
not replace hosted Lean kernel acceptance. No persistent Lean fixtures.

Independent bounded review against the exact pinned APIs found no concrete
mismatch in the image/sum witnesses, endpoint sector labels, positive section
argument, cyclic induction, or concrete finite-sum alphabet specialization.
Generic interaction-section Blueprint entries are moved before their new
parent-Hamiltonian consumers; their statements and anchors are unchanged.
