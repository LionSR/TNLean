/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.FrontChanges

/-!
# Ownership sheets on a finite set of sites

A sheet on a finite set `Λ` of sites is the space `⊗_{x ∈ Λ} ℂ^q` with an owner assigned to each
site; its reference vector is a vector `Ω` of `ℂ^{Λ → Fin q}` placed in these registers. This is
the sheet of the one-dimensional note and the raw sheet of the polynomial-PEPS manuscript; a
sheet carries no encoded holes. This file defines sheets, their registers and canonical
coordinates, the changes of owner of a birth or a death, and the two sheets after an exchange
inside a region.

* `Sheet ι Party`: an owner function `ι → Party`.
* `Sheet.regs q`, `Sheet.regIso q`: one raw register `ℂ^q` per site, held by its owner, and the
  identification of their tensor product with `ℂ^{ι → Fin q}`, sending `⊗_x |c x⟩` to `|c⟩`.
* `Sheet.regRef`: the reference vector `Ω` read on the registers.
* `Sheet.twoRegIso q`: the registers of two sheets, those of the first followed by those of the
  second, identified with `ℂ^{(ι → Fin q) × (ι → Fin q)}`.
* `Sheet.changeOwner`, `Sheet.birthEnv`: the sheet after handing a set `T` of sites to another
  party, and the set `E` of sites not owned by `P∘` (Lemma `lem:birth` of the one-dimensional
  note).
* `Sheet.swapIn`, `Sheet.exchangeEnv`, `Sheet.tSet`, `Sheet.eSet`, `Sheet.aSet`,
  `Sheet.exchangeOp`: the two-sheet exchange inside a region `Y`, the sets `Z`, `T = Z ∩ Y`,
  `E = Z ∖ Y` and `A = Y ∖ Z`, and the implemented map `D_U F_A ℛ`, where on sheets the renaming
  `ℛ` is the swap `F_Y` of the two sheets on `Y` (Lemma `lem:exchange` of the note).

The canonical coordinates of a sheet are those of an encoded frame without holes, whose block of
tag registers is empty (`regIso_eq_frontLayoutIso`, `twoRegIso_eq_twoFrontLayoutIso`), so the
monomials of `TNLean.Lattice.Sheet.FrontChanges` apply to sheets with the empty front block.

These are original proofs; no OpenAI Lean code is copied or adapted.

## References

* One-dimensional note, `docs/notes/one_dimensional_note/part2b_mps_protocol.tex`, lines 67–68
  (a sheet and its reference vector), Lemma `lem:birth`, lines 70–94, Lemma `lem:exchange`,
  lines 112–158, and the remark of lines 165–171: on a line no trijunctions occur and no encoded
  holes are needed.
* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 13–20 (sheets), 94–96
  (canonical site coordinates with the owners of the registers specified separately);
  Lemma 6.5 `lem:birth`, lines 396–456; Lemma 6.6 `lem:exchange`, lines 460–561.
-/

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator
open TNLean.Lattice.Sheet TNLean.Lattice.PartyCircuit

namespace TNLean.Lattice

/-! ### The empty front block -/

section UnitCoordinates

/-- The memory of the empty layout, the scalars, identified with `ℂ^{Unit}`. -/
def nilFrontIso {Party : Type} : Mem ([] : Layout Party) ≃ₗᵢ[ℂ] EuclideanSpace ℂ Unit :=
  (OrthonormalBasis.singleton Unit ℂ).repr

/-- Dropping the trivial first factor of `ℂ^{Unit × α}`. -/
abbrev unitProdIso (α : Type) [Fintype α] :
    EuclideanSpace ℂ (Unit × α) ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.punitProd α)

/-- Dropping the trivial first factors of `ℂ^{(Unit × α) × (Unit × β)}`. -/
abbrev unitProdIso₂ (α β : Type) [Fintype α] [Fintype β] :
    EuclideanSpace ℂ ((Unit × α) × (Unit × β)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (α × β) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ((Equiv.punitProd α).prodCongr (Equiv.punitProd β))

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem unitProdIso_apply (v : EuclideanSpace ℂ (Unit × α)) (a : α) :
    unitProdIso α v a = v ((), a) := by
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem unitProdIso₂_apply (v : EuclideanSpace ℂ ((Unit × α) × (Unit × β))) (a : α) (b : β) :
    unitProdIso₂ α β v (a, b) = v (((), a), ((), b)) := by
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- The operator `1_{Unit} ⊗ M` read without the trivial factor is `M`. -/
theorem unitProdIso_act_one_kronecker (M : Matrix α β ℂ) (v : EuclideanSpace ℂ (Unit × β)) :
    unitProdIso α (act ((1 : Matrix Unit Unit ℂ) ⊗ₖ M) v) = act M (unitProdIso β v) := by
  ext a
  simp only [unitProdIso_apply, act_apply_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton, Matrix.kroneckerMap_apply,
    Matrix.one_apply_eq, one_mul]

/-- The operator `1_{Unit × Unit} ⊗ G` on two sheets, read without the trivial factors, is `G`. -/
theorem unitProdIso₂_act_liftFront (G : Matrix (α × β) (γ × δ) ℂ)
    (v : EuclideanSpace ℂ ((Unit × γ) × (Unit × δ))) :
    unitProdIso₂ α β (act (((1 : Matrix (Unit × Unit) (Unit × Unit) ℂ) ⊗ₖ G).submatrix
        (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)) v) =
      act G (unitProdIso₂ γ δ v) := by
  ext ⟨a, b⟩
  simp only [unitProdIso₂_apply, act_apply_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Equiv.prodProdProdComm_apply, Matrix.one_apply_eq, one_mul]

end UnitCoordinates

/-! ### Sheets -/

/-- **A sheet.** An owner for each site of a finite set `ι`; its registers are one raw register
`ℂ^q` per site, held by the owner of the site.

One-dimensional note, `part2b_mps_protocol.tex`, lines 67–68; polynomial-PEPS manuscript,
`05-frames.tex`, lines 13–20. -/
@[ext]
structure Sheet (ι Party : Type) where
  /-- The owner of each site. -/
  owner : ι → Party

namespace Sheet

variable {ι Party : Type} [Fintype ι] [DecidableEq ι] (q : ℕ) (S : Sheet ι Party)

/-- **The registers of a sheet**: one raw register `ℂ^q` per site, in the fixed order of the
sites, held by the owner of the site. -/
abbrev regs : Layout Party := siteRegs q S.owner (sites ι)

/-- **The canonical coordinates of a sheet.** The tensor product of the registers is identified
with `ℂ^{ι → Fin q}` by sending `⊗_x |c x⟩` to `|c⟩` (`regIso_siteVec`).

Polynomial-PEPS manuscript, `05-frames.tex`, lines 15–19 and 94–96. -/
def regIso : Mem (S.regs q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ι → Fin q) :=
  groupIso S.owner (sites ι) (sitesEquiv ι)

theorem regIso_siteVec (c : ι → Fin q) :
    S.regIso q (siteVec S.owner (sites ι) c) = EuclideanSpace.single c (1 : ℂ) :=
  groupIso_siteVec S.owner _ _ id (fun _ => rfl) c

theorem regIso_symm_single (c : ι → Fin q) :
    (S.regIso q).symm (EuclideanSpace.single c (1 : ℂ)) = siteVec S.owner (sites ι) c := by
  rw [LinearIsometryEquiv.symm_apply_eq, regIso_siteVec]

/-- The canonical coordinates of a sheet are those of the empty front block followed by the raw
registers, without the trivial tag coordinate. -/
theorem regIso_eq_frontLayoutIso (z : Mem (S.regs q)) :
    S.regIso q z = unitProdIso _ (frontLayoutIso [] nilFrontIso S.owner z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (S.regIso q).symm y := ⟨S.regIso q z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hv : (S.regIso q).symm (EuclideanSpace.basisFun _ ℂ c) =
      frontLayoutVec [] nilFrontIso S.owner () c := by
    rw [EuclideanSpace.basisFun_apply, regIso_symm_single, frontLayoutVec,
      appendIso_nil_symm_tmul]
    have h1 : (nilFrontIso (Party := Party)).symm (EuclideanSpace.single () (1 : ℂ)) = (1 : ℂ) := by
      simp [nilFrontIso]
    rw [h1, one_smul]
  rw [hv, frontLayoutIso_frontLayoutVec, EuclideanSpace.basisFun_apply]
  ext a
  simp [PiLp.single_apply]

variable {q} in
/-- The reference vector `Ω` placed in the registers of a sheet.

One-dimensional note, `part2b_mps_protocol.tex`, line 68. -/
def regRef (Ω : EuclideanSpace ℂ (ι → Fin q)) : Mem (S.regs q) := (S.regIso q).symm Ω

variable {q} in
theorem norm_regRef (Ω : EuclideanSpace ℂ (ι → Fin q)) : ‖S.regRef Ω‖ = ‖Ω‖ :=
  LinearIsometryEquiv.norm_map _ _

variable {q} in
theorem norm_regRef_le {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) : ‖S.regRef Ω‖ ≤ 1 :=
  (S.norm_regRef Ω).trans_le hΩ

/-- **The registers of two sheets in canonical coordinates.** Those of the first sheet followed
by those of the second, identified with `ℂ^{(ι → Fin q) × (ι → Fin q)}`. -/
def twoRegIso (S₁ S₂ : Sheet ι Party) :
    Mem (S₁.regs q ++ S₂.regs q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ((ι → Fin q) × (ι → Fin q)) :=
  (appendIso _ _).trans ((((S₁.regIso q).rTensor _).trans ((S₂.regIso q).lTensor _)).trans
    (pairIso _ _))

theorem twoRegIso_appendIso_symm (S₁ S₂ : Sheet ι Party) (x : Mem (S₁.regs q))
    (y : Mem (S₂.regs q)) :
    twoRegIso q S₁ S₂ ((appendIso _ _).symm (x ⊗ₜ y)) =
      vecKron (S₁.regIso q x) (S₂.regIso q y) := by
  change pairIso _ _ ((S₂.regIso q).lTensor _ ((S₁.regIso q).rTensor _
    (appendIso _ _ ((appendIso _ _).symm (x ⊗ₜ y))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul]
  ext i
  simp [vecKron]

/-- The reference vector of two sheets on their concatenated registers is `Ω ⊗ Ω` in canonical
coordinates. -/
theorem appendIso_symm_regRef (S₁ S₂ : Sheet ι Party) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    (appendIso _ _).symm (S₁.regRef Ω ⊗ₜ S₂.regRef Ω) = (twoRegIso q S₁ S₂).symm (vecKron Ω Ω) := by
  rw [LinearIsometryEquiv.eq_symm_apply, twoRegIso_appendIso_symm, regRef, regRef,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

theorem twoRegIso_symm_single (S₁ S₂ : Sheet ι Party) (c₁ c₂ : ι → Fin q) :
    (twoRegIso q S₁ S₂).symm (EuclideanSpace.single (c₁, c₂) (1 : ℂ)) =
      (appendIso _ _).symm (siteVec S₁.owner (sites ι) c₁ ⊗ₜ siteVec S₂.owner (sites ι) c₂) := by
  rw [LinearIsometryEquiv.symm_apply_eq, twoRegIso_appendIso_symm, regIso_siteVec,
    regIso_siteVec]
  ext ⟨a, b⟩
  simp only [vecKron, PiLp.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Operators between the registers of two pairs of sheets agree in canonical coordinates with a
matrix as soon as they agree on the basis vectors. -/
theorem twoRegIso_eq_act_of_basis (S₁ S₂ S₁' S₂' : Sheet ι Party)
    (f : Mem (S₁.regs q ++ S₂.regs q) →L[ℂ] Mem (S₁'.regs q ++ S₂'.regs q))
    (A : Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ)
    (hf : ∀ c₁ c₂, twoRegIso q S₁' S₂'
      (f ((appendIso _ _).symm (siteVec S₁.owner (sites ι) c₁ ⊗ₜ siteVec S₂.owner (sites ι) c₂))) =
        act A (EuclideanSpace.single (c₁, c₂) (1 : ℂ)))
    (z : Mem (S₁.regs q ++ S₂.regs q)) :
    twoRegIso q S₁' S₂' (f z) = act A (twoRegIso q S₁ S₂ z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (twoRegIso q S₁ S₂).symm y := ⟨twoRegIso q S₁ S₂ z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨c₁, c₂⟩ := i
  rw [EuclideanSpace.basisFun_apply, twoRegIso_symm_single, hf]

/-- The canonical coordinates of two sheets are those of two empty front blocks followed by the
raw registers, without the trivial tag coordinates. -/
theorem twoRegIso_eq_twoFrontLayoutIso (S₁ S₂ : Sheet ι Party) (z : Mem (S₁.regs q ++ S₂.regs q)) :
    twoRegIso q S₁ S₂ z = unitProdIso₂ _ _
      (twoFrontLayoutIso [] nilFrontIso S₁.owner [] nilFrontIso S₂.owner z) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = (appendIso (S₁.regs q) (S₂.regs q)).symm w :=
    ⟨appendIso _ _ z, by simp⟩
  induction w using TensorProduct.inductionOn with
  | tmul x y =>
      rw [twoRegIso_appendIso_symm]
      change _ = unitProdIso₂ _ _ (pairIso _ _ ((frontLayoutIso [] nilFrontIso S₂.owner).lTensor _
        ((frontLayoutIso [] nilFrontIso S₁.owner).rTensor _
          (appendIso _ _ ((appendIso _ _).symm (x ⊗ₜ y))))))
      rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
        LinearIsometryEquiv.lTensor_tmul, regIso_eq_frontLayoutIso, regIso_eq_frontLayoutIso]
      ext ⟨a, b⟩
      simp [vecKron, unitProdIso_apply, unitProdIso₂_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### Change of owner -/

variable {q}

/-- The sheet obtained by handing the sites of `T` to `Q`.

One-dimensional note, Lemma `lem:birth`, `part2b_mps_protocol.tex`, lines 70–79. -/
def changeOwner (T : Finset ι) (Q : Party) : Sheet ι Party :=
  ⟨fun x => if x ∈ T then Q else S.owner x⟩

open Classical in
/-- The set `E = {x : the owner of x is not P∘}` of Lemma `lem:birth`.

One-dimensional note, `part2b_mps_protocol.tex`, lines 71–73; on a sheet the set
`E = {x : owner x ≠ P∘} ∪ H⁺(F)` of the polynomial-PEPS manuscript, `05-frames.tex`,
lines 400–405, has no hole part. -/
def birthEnv (P : Party) : Finset ι := Finset.univ.filter fun x => S.owner x ≠ P

section Birth

variable {T : Finset ι} {P Q : Party}

omit [DecidableEq ι] in
theorem mem_birthEnv {x : ι} : x ∈ S.birthEnv P ↔ S.owner x ≠ P := by
  classical
  unfold birthEnv
  simp

omit [DecidableEq ι] in
/-- `T` and `E` are disjoint when `T` is owned by `P∘`. -/
theorem disjoint_birthEnv (hTP : ∀ x ∈ T, S.owner x = P) : Disjoint T (S.birthEnv P) := by
  rw [Finset.disjoint_left]
  intro x hxT hxE
  exact (S.mem_birthEnv).mp hxE (hTP x hxT)

/-- The ownership facts of a birth: when `T` is owned by `P∘`, the sites outside `T ∪ E` are owned
by `P∘` before and after `T` is handed to `Q∘`, the sites of `T` are owned by `Q∘` afterwards,
and the owners on `E` are unchanged. -/
theorem changeOwner_birth_owners (hTP : ∀ x ∈ T, S.owner x = P) :
    (∀ x ∈ (T ∪ S.birthEnv P)ᶜ, S.owner x = P) ∧ (∀ x ∈ T, (S.changeOwner T Q).owner x = Q) ∧
      (∀ x ∈ (T ∪ S.birthEnv P)ᶜ, (S.changeOwner T Q).owner x = P) ∧
      ∀ x ∈ S.birthEnv P, S.owner x = (S.changeOwner T Q).owner x := by
  have hB : ∀ x ∈ (T ∪ S.birthEnv P)ᶜ, S.owner x = P := fun x hx => by
    by_contra h
    exact Finset.mem_compl.mp hx (Finset.mem_union_right _ ((S.mem_birthEnv).mpr h))
  refine ⟨hB, fun x hx => by simp [changeOwner, hx], fun x hx => ?_, fun x hx => ?_⟩
  · have hxT : x ∉ T := fun h => Finset.mem_compl.mp hx (Finset.mem_union_left _ h)
    simpa [changeOwner, hxT] using hB x hx
  · have hxT : x ∉ T := fun hT => Finset.disjoint_left.mp (S.disjoint_birthEnv hTP) hT hx
    simp [changeOwner, hxT]

end Birth

/-! ### Two-sheet exchange -/

/-- The sheet `S₁` after an exchange inside `Y` with `S₂`: inside `Y` it carries the owners of
`S₂`.

One-dimensional note, Lemma `lem:exchange`, `part2b_mps_protocol.tex`, lines 113–116. -/
def swapIn (S₁ S₂ : Sheet ι Party) (Y : Finset ι) : Sheet ι Party :=
  ⟨fun x => if x ∈ Y then S₂.owner x else S₁.owner x⟩

open Classical in
/-- The set `Z = {x : the two owners of x are not both P∘}` of Lemma `lem:exchange`.

One-dimensional note, `part2b_mps_protocol.tex`, lines 117–120. -/
def exchangeEnv (S₁ S₂ : Sheet ι Party) (P : Party) : Finset ι :=
  Finset.univ.filter fun x => ¬(S₁.owner x = P ∧ S₂.owner x = P)

/-- `T = Z ∩ Y`. -/
def tSet (S₁ S₂ : Sheet ι Party) (Y : Finset ι) (P : Party) : Finset ι := exchangeEnv S₁ S₂ P ∩ Y

/-- `E = Z ∖ Y`. -/
def eSet (S₁ S₂ : Sheet ι Party) (Y : Finset ι) (P : Party) : Finset ι := exchangeEnv S₁ S₂ P \ Y

/-- `A = Y ∖ Z = Y ∩ U`, where the private swap `F_A` acts. -/
def aSet (S₁ S₂ : Sheet ι Party) (Y : Finset ι) (P : Party) : Finset ι := Y \ exchangeEnv S₁ S₂ P

variable (S₁ S₂ : Sheet ι Party) (Y : Finset ι) (P : Party)

omit [DecidableEq ι] in
theorem mem_exchangeEnv {x : ι} :
    x ∈ exchangeEnv S₁ S₂ P ↔ ¬(S₁.owner x = P ∧ S₂.owner x = P) := by
  classical
  unfold exchangeEnv
  simp

theorem disjoint_tSet_eSet : Disjoint (tSet S₁ S₂ Y P) (eSet S₁ S₂ Y P) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [tSet, eSet, Finset.mem_inter, Finset.mem_sdiff] at hx hx'
  exact hx'.2 hx.2

theorem tSet_union_eSet : tSet S₁ S₂ Y P ∪ eSet S₁ S₂ Y P = exchangeEnv S₁ S₂ P := by
  ext x
  simp only [tSet, eSet, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem mem_tSet_iff (x : ι) : x ∈ tSet S₁ S₂ Y P ↔ x ∈ Y ∧ x ∉ aSet S₁ S₂ Y P := by
  simp only [tSet, aSet, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem aSet_subset_region : aSet S₁ S₂ Y P ⊆ Y := Finset.sdiff_subset

/-- `A` lies in `U = Λ ∖ Z`. -/
theorem aSet_subset_compl : aSet S₁ S₂ Y P ⊆ (tSet S₁ S₂ Y P ∪ eSet S₁ S₂ Y P)ᶜ := by
  intro x hx
  rw [tSet_union_eSet, Finset.mem_compl]
  exact (Finset.mem_sdiff.mp hx).2

/-- Every register of `U = Λ ∖ Z` is held by `P∘` on both sheets after the exchange
(`part2b_mps_protocol.tex`, lines 129–130). -/
theorem swapIn_owner_eq_of_mem_compl {x : ι} (hx : x ∈ (tSet S₁ S₂ Y P ∪ eSet S₁ S₂ Y P)ᶜ) :
    (swapIn S₁ S₂ Y).owner x = P ∧ (swapIn S₂ S₁ Y).owner x = P := by
  rw [tSet_union_eSet, Finset.mem_compl, mem_exchangeEnv, not_not] at hx
  obtain ⟨h₁, h₂⟩ := hx
  simp only [swapIn]
  split_ifs <;> exact ⟨by assumption, by assumption⟩

/-- **The implemented map of an exchange, `C = D_U F_A ℛ`.** On sheets the renaming `ℛ` acts in
canonical coordinates as the swap `F_Y` of the two sheets on `Y`; it is followed by the private
swap `F_A` and the private buffer correction `D_U` on the two copies of `U`.

One-dimensional note, proof of Lemma `lem:exchange`, `part2b_mps_protocol.tex`, lines 125–138. -/
def exchangeOp (σ : SplittingData q (tSet S₁ S₂ Y P) (eSet S₁ S₂ Y P)) :
    Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ :=
  sheetBufferCorrection (disjoint_tSet_eSet S₁ S₂ Y P) σ * sheetSwapOp q (aSet S₁ S₂ Y P) *
    sheetSwapOp q Y

/-- **The net map of an exchange (`D_U F_A F_Y = D_U F_T`).**

One-dimensional note, proof of Lemma `lem:exchange`, `part2b_mps_protocol.tex`, lines 134–138. -/
theorem exchangeOp_eq (σ : SplittingData q (tSet S₁ S₂ Y P) (eSet S₁ S₂ Y P)) :
    exchangeOp S₁ S₂ Y P σ =
      sheetBufferCorrection (disjoint_tSet_eSet S₁ S₂ Y P) σ * sheetSwapOp q (tSet S₁ S₂ Y P) := by
  rw [exchangeOp, Matrix.mul_assoc,
    sheetSwapOp_mul_sheetSwapOp (mem_tSet_iff S₁ S₂ Y P) (aSet_subset_region S₁ S₂ Y P)]

end Sheet

end TNLean.Lattice
