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

open scoped TensorProduct

/-- Transporting a vector across an equality of the right tensor factor commutes
with tensoring on the left by a fixed vector. -/
private theorem tmul_heq {W A B : HSpace} (hAB : A = B) (v : W)
    {a : A} {b : B} (h : HEq a b) :
    HEq (v ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) := by
  subst hAB
  cases h
  rfl

/-- The physical memory of an ordered register list ignores the owner labels, so
relabelling owners along `f` leaves the memory space unchanged once the
dimensions are composed with `f`. -/
private theorem familyPhysicalListBasis_owner_mem_eq {P Q : Type} (f : P → Q) (δ : Q → ℕ) :
    (ps : List P) →
    Mem (familyPhysicalLayout (fun p ↦ δ (f p)) ps) = Mem (familyPhysicalLayout δ (ps.map f))
  | [] => rfl
  | p :: ps =>
      congrArg (fun S : HSpace ↦ HSpace.of (euc (Fin (δ (f p))) ⊗[ℂ] S))
        (familyPhysicalListBasis_owner_mem_eq f δ ps)

/-- Evaluating the physical tensor basis on a nonempty register list splits off the
first register as a standard basis vector of its local space. -/
private theorem familyPhysicalListBasis_cons_apply {P : Type} (d : P → ℕ) (p : P) (ps : List P)
    (v : (j : Fin (p :: ps).length) → Fin (d ((p :: ps).get j))) :
    familyPhysicalListBasis d (p :: ps) v =
      (EuclideanSpace.basisFun (Fin (d p)) ℂ) (v 0) ⊗ₜ[ℂ]
        familyPhysicalListBasis d ps (fun i ↦ v i.succ) :=
  (((EuclideanSpace.basisFun (Fin (d p)) ℂ).tensorProduct
    (familyPhysicalListBasis d ps)).reindex_apply
      (Fin.consEquiv (fun i ↦ Fin (d ((p :: ps).get i)))) v).trans
    (OrthonormalBasis.tensorProduct_apply'
      (EuclideanSpace.basisFun (Fin (d p)) ℂ) (familyPhysicalListBasis d ps)
      ((Fin.consEquiv (fun i ↦ Fin (d ((p :: ps).get i)))).symm v))

/-- Evaluating the physical tensor basis on the empty register list returns the
scalar `1`. -/
private theorem familyPhysicalListBasis_nil_apply {P : Type} (d : P → ℕ)
    (g : (j : Fin ([] : List P).length) → Fin (d (([] : List P).get j))) :
    familyPhysicalListBasis d ([] : List P) g = 1 := by
  simp only [familyPhysicalListBasis]
  let I : Type := (i : Fin 0) → Fin (d (([] : List P).get i))
  have hcast : ∀ (ft ft' : Fintype I) (hf : ft = ft')
      (B : @OrthonormalBasis I ℂ _ ℂ _ _ ft') (i : I),
      (Eq.mpr (congrArg (fun j : Fintype I ↦ @OrthonormalBasis I ℂ _ ℂ _ _ j) hf) B) i = B i := by
    rintro ft ft' rfl B i
    rfl
  refine (hcast inferInstance _ (Subsingleton.elim _ _)
    (OrthonormalBasis.singleton I ℂ) g).trans ?_
  simp only [OrthonormalBasis.singleton_apply]

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
  induction ps with
  | nil =>
      simp only [List.map_nil]
      rw [familyPhysicalListBasis_nil_apply, familyPhysicalListBasis_nil_apply]
      rfl
  | cons p ps ih =>
      rw [List.map_cons, familyPhysicalListBasis_cons_apply, familyPhysicalListBasis_cons_apply]
      exact tmul_heq (familyPhysicalListBasis_owner_mem_eq f δ ps) _ ih

end TNLean.PEPS.PairEffect
