/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SelectedPhysicalPrivateGrouping
import TNLean.Lattice.Compression.SelectedPhysicalPartyGrouping
import QICLean.Channel.PartialTraceBasisInvariance

/-!
# Physical mixed-vector traces in the original coordinates

The actual grouped physical/private basis gives the same reduced matrix as the
original physical basis and any reference basis of the original private memory.
Only the canonical exterior singleton coordinate is removed. The two vectors
are independent and need not be normalized, so the identity also applies to
mixed terms in the original ket and bra source expansions.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–151, 409–434 and 565–588.
-/

noncomputable section
open scoped TensorProduct Matrix Kronecker ComplexConjugate
namespace TNLean.Lattice.PartyCircuit
open TNLean.Lattice.PartyCircuit

private theorem partialTrace_mixed_private_basis_eq
    {H K : HSpace} {X J G : Type} [Fintype X] [Fintype J] [Fintype G]
    (bX : OrthonormalBasis X ℂ H) (bG : OrthonormalBasis G ℂ K)
    (bJ : OrthonormalBasis J ℂ K) (v t : H ⊗[ℂ] K) :
    Matrix.partialTraceRight
        (Matrix.vecMulVec ((bX.tensorProduct bG).repr v).ofLp
          (fun i ↦ conj ((bX.tensorProduct bG).repr t i))) =
      Matrix.partialTraceRight
        (Matrix.vecMulVec ((bX.tensorProduct bJ).repr v).ofLp
          (fun i ↦ conj ((bX.tensorProduct bJ).repr t i))) := by
  classical
  have hself : bX.toBasis.toMatrix bX = 1 := by
    change bX.toBasis.toMatrix bX.toBasis = 1
    exact Module.Basis.toMatrix_self bX.toBasis
  have hc := OrthonormalBasis.tensorProduct_rankOne_basisChange bX bX bG bJ v t
  have h := Matrix.partialTraceRight_kronecker_conj_of_right_isometry
    (bX.toBasis.toMatrix bX) (bJ.toBasis.toMatrix bG)
    (bJ.toMatrix_orthonormalBasis_conjTranspose_mul_self bG)
    (Matrix.vecMulVec ((bX.tensorProduct bG).repr v).ofLp
      (fun i ↦ conj ((bX.tensorProduct bG).repr t i)))
  rw [hc] at h
  simpa only [hself, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one] using h.symm

variable {P : Type} [Fintype P] [DecidableEq P]
variable {E : Option {_p : P // true = true} → Type} [∀ q, Fintype (E q)]

/-- Tracing the actual grouped private coordinates yields the original physical
matrix of two arbitrary output vectors. The reference private basis is arbitrary;
no normalization, nonempty-party or finite-dimensional hypothesis is imposed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
409–434 and 565–588. -/
theorem selectedPhysicalPrivateBasis_partialTrace_mixed
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P)
    (bGarbage : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    {J : Type} [Fintype J] (bRef : OrthonormalBasis J ℂ (Mem garbage))
    (v t : Mem (familyPhysicalLayout d ps ++ garbage)) :
    let qs := selectedPartyOrder ps
    let B := partyGroupedBasis
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage))
      (selectedPhysicalPrivateBasis d ps hn hc garbage bGarbage) qs
      (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc)
    let e := (Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true})
      (selectedFamilyPhysicalIndex d) E).trans
        (Equiv.prodCongr (selectedFamilyPhysicalConfigEquiv d)
          (Equiv.refl ((q : Option {_p : P // true = true}) → E q)))
    Matrix.partialTraceRight
      ((Matrix.vecMulVec
        (B.repr (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true))
          (familyPhysicalLayout d ps ++ garbage) v)).ofLp
        (fun i ↦ conj (B.repr (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true))
          (familyPhysicalLayout d ps ++ garbage) t) i))).submatrix e.symm e.symm) =
      Matrix.partialTraceRight
        (Matrix.vecMulVec
          (((familyLabelledPhysicalBasis d ps hn hc).tensorProduct bRef).repr
            (appendIso (familyPhysicalLayout d ps) garbage v)).ofLp
          (fun i ↦ conj (((familyLabelledPhysicalBasis d ps hn hc).tensorProduct bRef).repr
            (appendIso (familyPhysicalLayout d ps) garbage t) i))) := by
  classical
  intro qs B e
  let f := affectedOwner (fun _ : P ↦ true)
  let physical := familyPhysicalLayout d ps
  let bPhysical := familyLabelledPhysicalBasis d ps hn hc
  let bPrivate := partyGroupedBasis (Layout.mapOwner f garbage) bGarbage qs
    (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc)
  let bOriginalPrivate := bPrivate.map (Layout.mapOwnerIso f garbage).symm
  let A := ((bPhysical.tensorProduct bOriginalPrivate).map
    (appendIso physical garbage).symm).map (Layout.mapOwnerIso f (physical ++ garbage))
  have hB : B.reindex e = A := by
    apply DFunLike.ext
    intro xy
    rcases xy with ⟨x, y⟩
    have hJoined := DFunLike.congr_fun
      (selectedPhysicalPrivateBasis_grouped d ps hn hc garbage bGarbage qs
        (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc))
      ((selectedFamilyPhysicalConfigEquiv d).symm x, y)
    have hPhysical := DFunLike.congr_fun
      (selectedFamilyPhysicalPartyBasis_grouped d ps hn hc) x
    simp only [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply,
      OrthonormalBasis.tensorProduct_apply, LinearIsometryEquiv.trans_apply] at hJoined hPhysical
    change B (e.symm (x, y)) =
      Layout.memCongr (Layout.mapOwner_append f physical garbage).symm
        ((appendIso (Layout.mapOwner f physical) (Layout.mapOwner f garbage)).symm
          ((partyGroupedBasis (Layout.mapOwner f physical)
            (selectedFamilyPhysicalPartyBasis d ps hn hc) qs
            (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc))
              ((selectedFamilyPhysicalConfigEquiv d).symm x) ⊗ₜ[ℂ] bPrivate y)) at hJoined
    change (partyGroupedBasis (Layout.mapOwner f physical)
      (selectedFamilyPhysicalPartyBasis d ps hn hc) qs
      (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc))
        ((selectedFamilyPhysicalConfigEquiv d).symm x) =
      Layout.mapOwnerIso f physical (bPhysical x) at hPhysical
    simp only [OrthonormalBasis.reindex_apply, A, OrthonormalBasis.map_apply,
      OrthonormalBasis.tensorProduct_apply, bOriginalPrivate]
    rw [hJoined, hPhysical]
    apply (Layout.memCongr (Layout.mapOwner_append f physical garbage)).injective
    rw [Layout.memCongr_symm (Layout.mapOwner_append f physical garbage),
      LinearIsometryEquiv.apply_symm_apply]
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (Layout.mapOwnerIso_append_tmul f physical garbage (bPhysical x)
        ((Layout.mapOwnerIso f garbage).symm (bPrivate y))).symm
  have hCoordinates (z : Mem (physical ++ garbage)) :
      (B.reindex e).repr (Layout.mapOwnerIso f (physical ++ garbage) z) =
        (bPhysical.tensorProduct bOriginalPrivate).repr (appendIso physical garbage z) := by
    rw [hB]
    simp only [A, OrthonormalBasis.map, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]
  have hEntry (z : Mem (physical ++ garbage))
      (i : ((p : P) → Fin (d p)) × ((q : Option {_p : P // true = true}) → E q)) :
      B.repr (Layout.mapOwnerIso f (physical ++ garbage) z) (e.symm i) =
        (bPhysical.tensorProduct bOriginalPrivate).repr (appendIso physical garbage z) i := by
    have hi := congrArg
      (fun u : EuclideanSpace ℂ
        (((p : P) → Fin (d p)) × ((q : Option {_p : P // true = true}) → E q)) ↦ u i)
      (hCoordinates z)
    simpa only [OrthonormalBasis.repr_reindex] using hi
  have hMatrix :
      (Matrix.vecMulVec (B.repr (Layout.mapOwnerIso f (physical ++ garbage) v)).ofLp
        (fun i ↦ conj (B.repr (Layout.mapOwnerIso f (physical ++ garbage) t) i))).submatrix
          e.symm e.symm =
      Matrix.vecMulVec
        ((bPhysical.tensorProduct bOriginalPrivate).repr (appendIso physical garbage v)).ofLp
        (fun i ↦ conj ((bPhysical.tensorProduct bOriginalPrivate).repr
          (appendIso physical garbage t) i)) := by
    ext i j
    simpa only [Matrix.submatrix_apply, Matrix.vecMulVec_apply] using
      congrArg₂ (fun x y : ℂ ↦ x * conj y) (hEntry v i) (hEntry t j)
  rw [hMatrix]
  exact partialTrace_mixed_private_basis_eq bPhysical bOriginalPrivate bRef
    (appendIso physical garbage v) (appendIso physical garbage t)

end TNLean.Lattice.PartyCircuit
