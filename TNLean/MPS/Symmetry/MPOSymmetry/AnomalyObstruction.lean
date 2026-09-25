/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.MPDO.ActionTensorReduction
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# An anomalous group of matrix product operators has no invariant normal state

Let `g ↦ O_g` be a group of matrix product operators with normal tensors and the exact
operator law `O_g O_h = O_{gh}` on every nonempty chain, and let `A` be a normal matrix
product state tensor whose periodic vector is invariant, `O_g |V_N(A)⟩ = |V_N(A)⟩` for every
`g` and every `N > 0`. The action tensors `X_g` reduce `O_g · A` onto `A`. For two elements
the stacked action `(O_g O_h) · A` reduces onto `A` in two ways: by two successive action
tensors, and by the fusion tensor of `(g, h)` followed by the action tensor of `gh`. The two
reductions agree against long words up to a nonzero scalar `L(g,h)`, the L-symbol of the
single block.

Comparing the five reductions of the triple action `((O_g O_h) O_k) · A` gives the
compatibility relation of arXiv:2502.20257, `eq:omega_and_Ls`, with a single block:
`L(g,hk) L(h,k) = ω(g,h,k) L(g,h) L(gh,k)`. Hence `ω` is the coboundary of `L` and its gauge
class is trivial.

## Main definitions

* `MPOTensor.GroupFamily.ActionData`: a choice of action tensors onto an invariant state.
* `MPOTensor.GroupFamily.ActionData.actV`, `MPOTensor.GroupFamily.ActionData.fuseV`: the left
  boundaries of the two reductions of `(O_g O_h) · A` onto `A`.
* `MPOTensor.GroupFamily.ActionData.lSymbol`: the L-symbol of the single block.

## Main results

* `MPOTensor.GroupFamily.ActionData.isCompatible_lSymbol`: the compatibility relation
  `eq:omega_and_Ls` with the anomaly three-cochain of lane `FusionData.omega`.
* `MPOTensor.GroupFamily.IsNormalRepresentation.isTrivialGaugeClass_omega_of_invariant`:
  **Theorem.** An invariant normal state forces the anomaly to be trivial.
* `MPOTensor.GroupFamily.IsNormalRepresentation.not_exists_invariant_of_not_isTrivialGaugeClass`:
  an anomalous group has no invariant normal state.

## References

* arXiv:2502.20257, `main.tex` line 1545 ("An MPU symmetry group with nontrivial `ω`
  cannot have an invariant injective MPS"), lines 1875--1925 (`eq:defL`, `eq:omega_and_Ls`
  and the remark that a single block reduces it to the three-coboundary condition).
* arXiv:2203.12563, `REsubmission.tex` line 738 (no injective MPS is invariant under an MPO
  with a nontrivial three-cocycle), and the periodic setting `sec:PBC`, lines 994--1129:
  exact invariance `U_g |ψ_{A_x}⟩ = |ψ_{A_y}⟩` (line 1064), L-symbols on long words
  (line 1091), and their compatibility with `ω` (line 1129).

The hypotheses are weaker than the sources': the operator and state tensors are normal rather
than injective, and neither unitarity nor simplicity of the operators is used.
-/

open scoped Matrix Kronecker
open TNLean.Algebra

namespace MPOTensor

namespace GroupFamily

universe u

variable {d : ℕ} {G : Type u} [Group G] {F : GroupFamily G d} {D : ℕ} {A : MPSTensor d D}

/-! ### Invariance -/

/-- The periodic operators of `T` fix the periodic vector of `A` at every positive length.

Source: arXiv:2203.12563, line 1064, with `y = x`. -/
def FixesMPV {D₁ : ℕ} (T : MPOTensor d D₁) (A : MPSTensor d D) : Prop :=
  ∀ N, 0 < N →
    mpo T N *ᵥ (fun τ : Fin N → Fin d ↦ MPSTensor.mpv A τ) = fun σ ↦ MPSTensor.mpv A σ

/-- A product of two operators fixing a vector fixes it. -/
theorem FixesMPV.mulTensor {D₁ D₂ : ℕ} {M : MPOTensor d D₁} {N : MPOTensor d D₂}
    (hM : FixesMPV M A) (hN : FixesMPV N A) : FixesMPV (mulTensor M N) A := by
  intro L hL
  rw [mpo_mulTensor, ← Matrix.mulVec_mulVec, hN L hL, hM L hL]

/-- An action tensor of an operator fixing `A`, applied to a state with the positive-length
vectors of `A`, again has the positive-length vectors of `A`. -/
theorem FixesMPV.sameMPV₂Pos_actTensor {D₁ D₂ : ℕ} {T : MPOTensor d D₁} {B : MPSTensor d D₂}
    (hT : FixesMPV T A) (hB : MPSTensor.SameMPV₂Pos B A) :
    MPSTensor.SameMPV₂Pos (actTensor T B) A := by
  intro N hN σ
  have hB' : (fun τ : Fin N → Fin d ↦ MPSTensor.mpv B τ) = fun τ ↦ MPSTensor.mpv A τ :=
    funext (hB N hN)
  rw [← congrFun (mpo_mulVec_mpv T B N) σ, hB', hT N hN]

omit [Group G] in
theorem sameMPV₂Pos_refl (A : MPSTensor d D) : MPSTensor.SameMPV₂Pos A A :=
  fun _ _ _ ↦ rfl

/-! ### Action tensors -/

/-- A choice of action tensors: for every group element `g`, a reduction `(V_g, W_g)` of the
action tensor `O_g · A` onto `A`.

Source: arXiv:2203.12563, equation `mpoMPSsten`, lines 1066--1090; arXiv:2502.20257,
`eq:action_exterior` and `eq:action_interior`. -/
structure ActionData (F : GroupFamily G d) (A : MPSTensor d D) where
  /-- The left action tensor of `g`. -/
  V : ∀ g : G, Matrix (Fin D) (Fin (F.bondDim g * D)) ℂ
  /-- The right action tensor of `g`. -/
  W : ∀ g : G, Matrix (Fin (F.bondDim g * D)) (Fin D) ℂ
  isReduction : ∀ g, MPSTensor.IsReduction (actTensor (F.tensor g) A) A (V g) (W g)

omit [Group G] in
/-- **Existence of action tensors** for a normal state of positive bond dimension fixed by
every operator of the family (arXiv:2203.12563, `mpoMPSsten`, citing arXiv:1706.07329v2,
Proposition 20). -/
theorem nonempty_actionData (hA : Kraus.IsNormal A) (hD : 0 < D)
    (hinv : ∀ g, FixesMPV (F.tensor g) A) : Nonempty (ActionData F A) := by
  choose V W h using fun g ↦
    exists_isReduction_actTensor_of_isNormal (F.tensor g) A A hA hD (hinv g)
  exact ⟨⟨V, W, fun g ↦ (h g).1⟩⟩

namespace ActionData

variable (fd : FusionData F) (ad : ActionData F A)

/-- The left boundary of the reduction of `(O_g O_h) · A` onto `A` by two successive action
tensors: `V_g (1 ⊗ V_h) a⁻¹`, with `a` the bond associator.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913. -/
noncomputable def actV (g h : G) :
    Matrix (Fin D) (Fin (F.bondDim g * F.bondDim h * D)) ℂ :=
  ad.V g * idKron (F.bondDim g) (ad.V h) * mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) D

/-- The left boundary of the reduction of `(O_g O_h) · A` onto `A` by the fusion tensor of
`(g, h)` followed by the action tensor of `gh`: `V_{gh} (V_{g,h} ⊗ 1)`.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913. -/
noncomputable def fuseV (g h : G) :
    Matrix (Fin D) (Fin (F.bondDim g * F.bondDim h * D)) ℂ :=
  ad.V (g * h) * kronId (fd.V g h) D

omit [Group G] in
theorem exists_isReduction_actV (g h : G) : ∃ W, MPSTensor.IsReduction
    (actTensor (mulTensor (F.tensor g) (F.tensor h)) A) A (ad.actV g h) W :=
  ⟨_, (((ad.isReduction h).actTensor_idKron (F.tensor g)).trans
    (ad.isReduction g)).actTensor_assoc_left⟩

theorem exists_isReduction_fuseV (g h : G) : ∃ W, MPSTensor.IsReduction
    (actTensor (mulTensor (F.tensor g) (F.tensor h)) A) A (ad.fuseV fd g h) W :=
  ⟨_, ((fd.isReduction g h).actTensor_kronId A).trans (ad.isReduction (g * h))⟩

open Classical in
/-- **The L-symbol of a single invariant block**: the nonzero scalar `L(g,h)` with
`actV g h ~ L(g,h) · fuseV g h` against long words of `(O_g O_h) · A`
(`MPOTensor.GroupFamily.ActionData.isDressedProportional_lSymbol`). It is set to one if no
such scalar exists, which does not happen for a normal invariant state.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913; arXiv:2203.12563,
`sec:PBC`, line 1091. -/
noncomputable def lSymbol : LSymbol G Unit := fun _ g h ↦
  if hz : ∃ z : ℂ, z ≠ 0 ∧ MPSTensor.IsDressedProportional
      (actTensor (mulTensor (F.tensor g) (F.tensor h)) A) (ad.actV g h) (ad.fuseV fd g h) z
  then Units.mk0 hz.choose hz.choose_spec.1 else 1

variable {fd ad}

theorem isDressedProportional_lSymbol (hA : Kraus.IsNormal A)
    (hinv : ∀ g, FixesMPV (F.tensor g) A) (x : Unit) (g h : G) :
    MPSTensor.IsDressedProportional (actTensor (mulTensor (F.tensor g) (F.tensor h)) A)
      (ad.actV g h) (ad.fuseV fd g h) (ad.lSymbol fd x g h) := by
  have hex : ∃ z : ℂ, z ≠ 0 ∧ MPSTensor.IsDressedProportional
      (actTensor (mulTensor (F.tensor g) (F.tensor h)) A) (ad.actV g h) (ad.fuseV fd g h) z := by
    obtain ⟨W, hW⟩ := ad.exists_isReduction_actV g h
    obtain ⟨W', hW'⟩ := ad.exists_isReduction_fuseV fd g h
    exact hW.exists_isDressedProportional hW' hA
      (((hinv g).mulTensor (hinv h)).sameMPV₂Pos_actTensor (sameMPV₂Pos_refl A))
  simp only [lSymbol, hex, ↓reduceDIte, Units.val_mk0]
  exact hex.choose_spec.2

/-! ### The five reductions of the triple action -/

section Triple

variable (g h k : G)

omit [Group G] in
/-- Moving a bond identification of the operator factor out of the action tensor of an
element: `V_y (castMat e Y ⊗ 1) = V_x (Y ⊗ 1)` for `e : x = y`. -/
private theorem V_mul_kronId_castMat {x y : G} (e : x = y) {n : ℕ}
    (Y : Matrix (Fin (F.bondDim x)) (Fin n) ℂ) :
    ad.V y * kronId (F.castMat e * Y) D = ad.V x * kronId Y D := by
  subst e
  simp

omit [Group G] in
/-- The pentagon step: acting with `k` first and then with `h` and `g` is the same boundary
as acting with the pair `(h, k)` inside the action of `g`. -/
private theorem actV_mul_reduce_k :
    ad.actV g h * (idKron (F.bondDim g * F.bondDim h) (ad.V k) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) D) =
      ad.V g * idKron (F.bondDim g) (ad.actV h k) *
        (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) D *
          kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) D) := by
  simp only [actV, ← idKron_mul, Matrix.mul_assoc, assocInv_mul_idKron_assoc]
  rw [← Matrix.mul_assoc (idKron (F.bondDim g) (mulTensorAssocInvMatrix _ _ _)),
    assocInv_pentagon]

/-- The inner fusion step: acting with `g` on the fused pair `(h, k)` is the action tree of
`(g, hk)` composed with the fusion of `h` with `k` on the triple. -/
private theorem fuseV_inner_eq :
    ad.V g * idKron (F.bondDim g) (ad.fuseV fd h k) *
        (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) D *
          kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) D) =
      ad.actV g (h * k) * kronId (idKron (F.bondDim g) (fd.V h k) *
        mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) D := by
  simp only [actV, fuseV, ← idKron_mul, ← kronId_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (idKron _ (kronId _ _)), ← assocInv_mul_kronId_idKron,
    Matrix.mul_assoc]

/-- Acting with `k` first and then fusing `g` with `h` is the action tree of `(gh, k)` composed
with the fusion of `g` with `h` on the triple. -/
private theorem fuseV_mul_reduce_k :
    ad.fuseV fd g h * (idKron (F.bondDim g * F.bondDim h) (ad.V k) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) D) =
      ad.actV (g * h) k * kronId (kronId (fd.V g h) (F.bondDim k)) D := by
  simp only [actV, fuseV, Matrix.mul_assoc, kronId_mul_idKron_assoc]
  rw [← assocInv_mul_kronId_kronId]

/-- Fusing `gh` with `k` after fusing `g` with `h` is the fusion tree `leftV` of the associator,
followed by the action of `ghk`. -/
private theorem fuseV_mul_left :
    ad.fuseV fd (g * h) k * kronId (kronId (fd.V g h) (F.bondDim k)) D =
      ad.V (g * h * k) * kronId (fd.leftV g h k) D := by
  simp only [fuseV, FusionData.leftV, Matrix.mul_assoc, kronId_mul]

/-- Fusing `g` with `hk` after fusing `h` with `k` is the fusion tree `rightV` of the
associator, followed by the action of `ghk`. -/
private theorem fuseV_mul_right :
    ad.fuseV fd g (h * k) * kronId (idKron (F.bondDim g) (fd.V h k) *
        mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) D =
      ad.V (g * h * k) * kronId (fd.rightV g h k) D := by
  simp only [fuseV, FusionData.rightV, Matrix.mul_assoc, kronId_mul]
  rw [V_mul_kronId_castMat]

end Triple

/-- **Compatibility of the L-symbols with the anomaly three-cocycle** for a single invariant
block (arXiv:2502.20257, `eq:omega_and_Ls`, `main.tex` lines 1920--1923; arXiv:2203.12563,
`pentagongroups` and line 1129): `L(g,hk) L(h,k) = ω(g,h,k) L(g,h) L(gh,k)`.

The five fusion-and-action trees of `((O_g O_h) O_k) · A` are reductions onto `A`. Adjacent
trees differ by one L-symbol or by `ω` against long words, and comparing the two paths on a
nonvanishing word gives the identity. -/
theorem isCompatible_lSymbol (hF : F.IsNormalRepresentation) (hA : Kraus.IsNormal A)
    (hD : 0 < D) (hinv : ∀ g, FixesMPV (F.tensor g) A) :
    LSymbol.IsCompatible (ad.lSymbol fd) fd.omega := by
  intro x g h k
  have hfix : ∀ a, FixesMPV (F.tensor a) A := hinv
  set B3 := actTensor (F.tripleTensor g h k) A
  have hSame3 : MPSTensor.SameMPV₂Pos B3 A :=
    (((hfix g).mulTensor (hfix h)).mulTensor (hfix k)).sameMPV₂Pos_actTensor
      (sameMPV₂Pos_refl A)
  have hSameC : ∀ a b : G,
      MPSTensor.SameMPV₂Pos (actTensor (mulTensor (F.tensor a) (F.tensor b)) A) A :=
    fun a b ↦ ((hfix a).mulTensor (hfix b)).sameMPV₂Pos_actTensor (sameMPV₂Pos_refl A)
  have hSame3C : ∀ a b : G,
      MPSTensor.SameMPV₂Pos B3 (actTensor (mulTensor (F.tensor a) (F.tensor b)) A) :=
    fun a b ↦ fun N hN σ ↦ (hSame3 N hN σ).trans (hSameC a b N hN σ).symm
  -- the three reductions of `B3` used for pullbacks
  have hR : MPSTensor.IsReduction B3 (actTensor (mulTensor (F.tensor g) (F.tensor h)) A)
      (idKron (F.bondDim g * F.bondDim h) (ad.V k) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) D) _ :=
    ((ad.isReduction k).actTensor_idKron (mulTensor (F.tensor g) (F.tensor h))).actTensor_assoc_left
  have hS : MPSTensor.IsReduction B3
      (actTensor (mulTensor (F.tensor (g * h)) (F.tensor k)) A)
      (kronId (kronId (fd.V g h) (F.bondDim k)) D) _ :=
    ((fd.isReduction g h).mulTensor_kronId (F.tensor k)).actTensor_kronId A
  have hK : MPSTensor.IsReduction B3
      (actTensor (mulTensor (F.tensor g) (F.tensor (h * k))) A)
      (kronId (idKron (F.bondDim g) (fd.V h k) *
        mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) D) _ :=
    ((fd.isReduction h k).mulTensor_idKron (F.tensor g)).mulTensor_assoc_left.actTensor_kronId A
  -- the L-symbol relations pulled back to `B3`
  have H3 := (isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hinv x g h).pullback hR
    (hSame3C g h)
  have H4 := (isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hinv x (g * h) k).pullback hS
    (hSame3C (g * h) k)
  have H2 := (isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hinv x g (h * k)).pullback hK
    (hSame3C g (h * k))
  have H1 := (((isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hinv x h k).actTensor_idKron
      (F.tensor g)).mul_left (ad.V g)).of_intertwine
      (mulTensorAssocMatrix_mul_invMatrix _ _ _) (mulTensorAssocInvMatrix_mul_matrix _ _ _)
      (actTensor_mulTensor_mul_assocMatrix (F.tensor g)
        (mulTensor (F.tensor h) (F.tensor k)) A)
  have H1' := H1.of_intertwine (B' := B3)
      (P := kronId (mulTensorAssocMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) D)
      (Q := kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) D)
      (by rw [kronId_mul, mulTensorAssocMatrix_mul_invMatrix, kronId_one])
      (by rw [kronId_mul, mulTensorAssocInvMatrix_mul_matrix, kronId_one])
      (actTensor_mul_kronId_of_intertwine A fun i l ↦
        mulTensor_mul_assocMatrix (F.tensor g) (F.tensor h) (F.tensor k) i l)
  have H5 := ((fd.isAssociator_omega hF g h k).actTensor_kronId A).mul_left (ad.V (g * h * k))
  -- rewrite all boundaries into the five canonical ones
  have H1'' : MPSTensor.IsDressedProportional B3
      (ad.actV g h * (idKron (F.bondDim g * F.bondDim h) (ad.V k) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) D))
      (ad.actV g (h * k) * kronId (idKron (F.bondDim g) (fd.V h k) *
        mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) D)
      (ad.lSymbol fd x h k) := by
    rw [actV_mul_reduce_k, ← fuseV_inner_eq]
    simpa only [Matrix.mul_assoc] using H1'
  rw [fuseV_mul_reduce_k] at H3
  rw [fuseV_mul_left] at H4
  rw [fuseV_mul_right] at H2
  have hleft := H1''.trans H2
  have hright := (H3.trans H4).trans H5
  -- uniqueness against a nonvanishing word
  have hne : ∀ N : ℕ, ∃ w : List (Fin d), N ≤ w.length ∧
      ad.actV g h * (idKron (F.bondDim g * F.bondDim h) (ad.V k) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) D) *
          Kraus.evalWord B3 w ≠ 0 := by
    obtain ⟨W, hW⟩ := ad.exists_isReduction_actV g h
    exact (hR.trans hW).exists_mul_evalWord_ne_zero hA hD
  have heq := MPSTensor.IsDressedProportional.eq_of_forall_exists_ne_zero hleft hright hne
  apply Units.ext
  simp only [Units.val_mul]
  have hk : k • x = x := Subsingleton.elim _ _
  rw [hk]
  linear_combination heq

/-- **An invariant normal state forces a trivial anomaly.** If a group of matrix product
operators with normal tensors fixes the periodic vector of a normal matrix product state of
positive bond dimension at every positive length, then the anomaly three-cocycle of every
choice of fusion tensors has trivial gauge class.

Source: arXiv:2502.20257, `main.tex` line 1545 and lines 1920--1925; arXiv:2203.12563,
`REsubmission.tex` line 738 and `sec:PBC`, lines 1064--1129. -/
theorem _root_.MPOTensor.GroupFamily.IsNormalRepresentation.isTrivialGaugeClass_omega_of_invariant
    (hF : F.IsNormalRepresentation) (fd : FusionData F) (hA : Kraus.IsNormal A) (hD : 0 < D)
    (hinv : ∀ g, FixesMPV (F.tensor g) A) :
    ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  obtain ⟨ad⟩ := nonempty_actionData (F := F) hA hD hinv
  exact LSymbol.isTrivialGaugeClass_of_isCompatible_of_forall_smul_eq
    (ad.isCompatible_lSymbol hF hA hD hinv) () fun _ ↦ rfl

end ActionData

/-- **An anomalous group has no invariant normal state.** If the anomaly three-cocycle of some
choice of fusion tensors has nontrivial gauge class, then no normal matrix product state of
positive bond dimension has its periodic vector fixed by every operator of the group at every
positive length.

Source: arXiv:2502.20257, `main.tex` line 1545; arXiv:2203.12563, `REsubmission.tex`
line 738. -/
theorem IsNormalRepresentation.not_exists_invariant_of_not_isTrivialGaugeClass
    (hF : F.IsNormalRepresentation) (fd : FusionData F)
    (hω : ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega) :
    ¬ ∃ (D : ℕ) (A : MPSTensor d D), 0 < D ∧ Kraus.IsNormal A ∧
      ∀ g, FixesMPV (F.tensor g) A :=
  fun ⟨_, _, hD, hA, hinv⟩ ↦ hω (hF.isTrivialGaugeClass_omega_of_invariant fd hA hD hinv)

end GroupFamily

end MPOTensor
