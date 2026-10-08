# Three-site normality of the mixed MPO

## Source and scope

The source is Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`Papers/2203.12563/REsubmission.tex`, with version and license recorded in
`Papers/NOTICE.md`:

- `eq:orthoV`: biorthogonal analysis and synthesis;
- lines 1584–1601: the square-physical state support and mixed construction;
- lines 1600–1631: the crossed action-map contractions;
- lines 1667–1685: the additional aligned L- and F-symbol setting;
- lines 1687–1689: the one-site injectivity discussion.

The new result concerns the actual `mixedEndpointMPO`, and concludes
injectivity after blocking **three** sites. Its isolated assumptions are
positive state-bond dimensions and common multiplicity, injectivity of both
endpoint MPO tensors, and biorthogonality of both endpoint action-map pairs.
It does not assume any state tensor, exact action reconstruction, L- or
F-symbol alignment, or ambient completeness. It is not a formalization of
the source's one-site assertion in its full categorical setting.

For a rectangular matrix X, biorthogonality gives

    V₀ν (Σμ W₀μ X V₁μ) W₁ν = X.

Taking X to be a nonzero matrix unit produces a nonzero entry in a crossed
mixed-MPO letter. Exchanging the endpoints gives the other crossed corner.
Endpoint MPO injectivity supplies all diagonal matrix units in the
one-letter span. If Cᵤᵥ is a nonzero crossed entry, then

    Eₐᵤ C Eᵥᵦ = Cᵤᵥ Eₐᵦ.

Dividing by Cᵤᵥ supplies every crossed matrix unit in the exact three-letter
span. Diagonal units have the same length because Eₐᵦ = Eₐᵦ Eᵦᵦ Eᵦᵦ.
Thus that span is the full operator-bond matrix algebra.

A separate source-facing consequence derives positive multiplicity from
one endpoint's positive MPO bond, injective MPO, injective square-physical
state tensor, and exact action decomposition. The D² state letters are a
basis; a zero-copy action would make every MPO coefficient vanish. The
mixed exact-action result requires injectivity only of A₀, together with
both exact action decompositions and both MPO injectivities. Injectivity
of A₁ is not added.

The one-site assertion is neither imported as a premise nor refuted here.
A numerical example satisfying only isolated assumptions is not a
counterexample to the paper's full aligned categorical setting. No
uncertified full-source counterexample is included.

## Blueprint ownership

`blueprint/src/chapter/ch30_mpo_mixed_normality.tex` has three theorem nodes
and three mathematical proofs. The first node owns both the three-site
result and its immediate normality consequence. Its four declaration links
are, in namespace `MPSTensor.MPOSymmetry`:

- `isNBlkInjective_mixedEndpointMPO_three`
- `isNormal_mixedEndpointMPO`
- `multiplicity_pos_of_injective_endpoint_action`
- `isNBlkInjective_mixedEndpointMPO_three_of_exact_action`

The signatures were compared against the production source. All four have
exactly one owner in the new leaf.
