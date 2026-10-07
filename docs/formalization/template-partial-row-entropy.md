# Partial-final-row entropy cost (issue #8754)

Source: OpenAI, September 24, 2026, Lemma 9.4 (`scanner:templates`),
`08-scanner.tex:571–676`, pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proof says: “Adding an arbitrary part of one depth row changes entropy by
at most \(n\log q\).” All proofs here are independently written from that
mathematical argument; no upstream Lean proof text is reused.

The source's ambient `T_j` is `ambientDilation T.points j`. Its physical
intersection with `A` is `A.filter (fun x ↦ x.val ∈ U)` for ambient `U`.
The theorem therefore states exactly the absolute entropy difference for
`A ∩ ((T_(j−1) \ T) ∪ Y)` and `A ∩ (T_(j−1) \ T)`, for arbitrary
`Y ⊆ T_j \ T_(j−1)`. `Geometry.template_layer_card_le` supplies `|Y| ≤ n`
from the actual `Template`, with `Ctpl ≥ 24` and `1 ≤ j ≤ s₀`.

The two local auxiliary bounds use the actual normalized physical vector and
canonical regional entropy. They specialize existing accepted QIC finite-product
subadditivity, complementary entropy and log-rank results. The bridge
`regionalEntropy_eq_finiteProduct` is consumed unchanged from #8800.
No entropy assumptions, extra Hamiltonian assumptions, or new density definitions
are introduced. Normalization handles the empty tensor product, and `q ≥ 1`
makes multiplication by `log q` monotone. The dimension helper even allows q=0
when a normalized vector exists (for example, an empty domain).

Dependencies: corrected model #8788 at `162fa69a`, geometry #8798 at `a8da4372`,
and entropy consumer #8800 at `55ec6dcd`, with its accepted QIC pin `826a56f5`.
Dependency merges preserve production source and regenerate aggregators.
#8797/#8803 remain owned separately and are not modified. Full safe-box,
dyadic-cover and shell entropy results remain open.

Validation: production proof and regressions await normal CI. Local Lean release
installation succeeded, but the Mathlib cache endpoint returned HTTP 403; no
Mathlib proof sources were rebuilt. Strict test and axiom-print commands are
registered after the full build; the production target runs early. No `leanok`
marks are applied before successful kernel validation.
