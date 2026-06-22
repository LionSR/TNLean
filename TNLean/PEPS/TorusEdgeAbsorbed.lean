import TNLean.PEPS.TorusWitnessCapstone
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed

/-!
# The bare-edge absorbed equality from an edge witness

This file converts, at a single torus edge, a conjugation-form coefficient identity into the
*bare-edge absorbed equality* against `applyGauge B X` (arXiv:1804.04964, Section 3, proof of
Theorem 3, lines 1519--1544 of `Papers/1804.04964/paper_normal.tex`):

> `edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ (reindex N)`.

An `EdgeCoeffIdentityWitness` at `e` carries a red blocking region `R_e` whose single boundary
edge is `e` and a conjugation-form coefficient identity realized by a per-edge gauge `Z_e`.
When `X e` is the orientation-adapted absorbing gauge `absorbedBoundaryGauge B R_e ⟨e,_⟩ Z_e`,
the bare-edge absorbed equality at `e` follows from `edgeAbsorbed_of_conjIdentity`.  Because the
bare-edge identity at `e` depends only on the gauge `X e` (the open-edge gauge cancellation
`edgeInsertedCoeff_applyGauge`), the conversion at each edge is independent of the others.

The every-edge family consuming this conversion is the translation-covariant absorbed gauge
family (`exists_torusCovariantAbsorbedGaugeFamily`), built by transporting one reference witness
per orientation class; see `docs/paper-gaps/peps_normal_ft_section3_route.tex`, section
"Closure on the torus".

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The bare-edge absorbed equality from a single edge witness.**

If an edge `e` of the torus carries an `EdgeCoeffIdentityWitness` with per-edge gauge `Z`, then the
bare-edge absorbed equality holds at `e` against `applyGauge B X`, provided `X e` is the
orientation-adapted absorbing gauge `absorbedBoundaryGauge B w.region ⟨e, w.isBoundary⟩ Z` and
every bond dimension of `A` is positive.

The witness's conjugation-form coefficient identity (`EdgeCoeffIdentityWitness.hidZ`) is fed to
`edgeAbsorbed_of_conjIdentity`, which converts it to the absorbed region equality and cancels the
shared positive interior multiplicity to the bare-edge identity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeAbsorbed_of_edgeCoeffIdentityWitness
    {A B : Tensor (torusGraph width height) d} {e : Edge (torusGraph width height)}
    {Z Zref : GL (Fin (B.bondDim e)) ℂ} {hE : A.bondDim e = B.bondDim e}
    (w : EdgeCoeffIdentityWitness A B e Z Zref hE)
    (hbd : A.bondDim = B.bondDim)
    (X : (g : Edge (torusGraph width height)) → GL (Fin (B.bondDim g)) ℂ)
    (hXe : X e = absorbedBoundaryGauge (G := torusGraph width height) B w.region
      ⟨e, w.isBoundary⟩ Z)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (σ : TorusVertex width height → Fin d)
    (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := torusGraph width height) A e σ N =
      edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N) := by
  -- The witness's boundary edge is `⟨e, w.isBoundary⟩`; `hE` and `congr_fun hbd e` agree.
  have hEeq : hE = congr_fun hbd e := Subsingleton.elim _ _
  subst hEeq
  exact edgeAbsorbed_of_conjIdentity A B w.region ⟨e, w.isBoundary⟩ hbd Z X hXe hposA
    (fun M σ' τ' => w.hidZ M σ' τ') σ N

end PEPS
end TNLean
