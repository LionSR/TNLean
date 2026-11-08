# Pre-bialgebra counit: three declarations replaced

Scope: issue #10517. Base: `5a13935af88f0349e57dfb2a0edd75e40aae0437`.

The pre-bialgebra class in `TNLean/Algebra/PreBialgebra.lean` now extends
Mathlib's `Coalgebra`, so it carries the counit of arXiv:2204.05940, `mpo.tex`,
Definition 3.1 (lines 866--875), and adds only multiplicativity of the
comultiplication (Definition 4.1, lines 1409--1414). The old class stored a
comultiplication `A →ₙₐ[R] A ⊗[R] A` and a coassociativity field. Three
declarations about that encoding are removed:

- `PreBialgebra.coassoc_apply`: the pointwise form of the old coassociativity
  field. Replacement: Mathlib's `Coalgebra.coassoc_apply`, inherited through
  the `Coalgebra` parent.
- `PreBialgebra.comul_mul` (theorem): multiplicativity of the old
  comultiplication, obtained from `map_mul`. Replacement: the class field of
  the same name, `PreBialgebra.comul_mul`.
- `Bialgebra.preBialgebra_comul_apply`: identified the old pre-bialgebra
  comultiplication of a bialgebra with its coalgebra comultiplication. The two
  are now the same `Coalgebra.comul`, so the lemma has no content.
  Replacement: none needed.

None of the three had a Lean consumer. The Blueprint entry for the
pre-bialgebra now tags the class and `Bialgebra.toPreBialgebra`.
`CompleteZipperFusionCoassoc.toPreBialgebra` keeps its name and gains the
counit and its letter values as arguments; the paper-gap note
`docs/paper-gaps/mrgscp22_pre_bialgebra_counit_scope.tex` records why the
fusion data do not force the counit to exist.
