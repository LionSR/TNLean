import TNLean.PEPS.Approximation.FamilyPhysicalReadout

/-!
# Physical tensor columns under dimension-preserving owner relabelling

A prescribed physical column depends on the ordered local dimensions and
labels. Composing these data with an owner map preserves the column, even
when owners repeat or the ordered list omits other parties.

Source: polynomial-PEPS manuscript, proof of Theorem 5.2,
`04-compression.tex`, lines 137–151 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect

/-- Relabelling the owners of an ordered physical register list preserves
its prescribed tensor column when the dimensions and labels are composed
with the same map. No injectivity, distinctness, exhaustiveness or positive
dimension hypothesis is imposed. The empty list retains its scalar column.
Source: polynomial-PEPS manuscript, proof of Theorem 5.2,
`04-compression.tex`, lines 137–151 and 565–588. -/
private theorem familyPhysicalListBasis_owner_column_heq
    {P Q : Type} (f : P → Q) (δ : Q → ℕ) (ps : List P)
    (y : (q : Q) → Fin (δ q)) :
    HEq
      (familyPhysicalListBasis (fun p ↦ δ (f p)) ps
        (fun j ↦ y (f (ps.get j))))
      (familyPhysicalListBasis δ (ps.map f)
        (fun j ↦ y ((ps.map f).get j))) := by
  done

end TNLean.PEPS.PairEffect
