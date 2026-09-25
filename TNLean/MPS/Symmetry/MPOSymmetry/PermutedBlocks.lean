/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.AnomalyObstruction

/-!
# L-symbols of blocks permuted by a group of matrix product operators

Let `g ↦ O_g` be a group of matrix product operators with normal tensors and the exact law
`O_g O_h = O_{gh}` on every nonempty chain, and let `x ↦ A_x` be normal matrix product state
tensors indexed by a set `X` on which the group acts, with
`O_g |V_N(A_x)⟩ = |V_N(A_{g • x})⟩` for every `g`, `x` and `N > 0`. This is the periodic
setting of arXiv:2203.12563, `sec:PBC`, line 1064. Action tensors reduce `O_g · A_x` onto
`A_{g • x}`. The two reductions of `(O_g O_h) · A_x` onto `A_{(gh) • x}`, by two actions and by
fusion followed by action, agree against long words up to a nonzero scalar `Lˣ_{g,h}`, and
these L-symbols are compatible with the anomaly three-cocycle:
`Lˣ_{g,hk} Lˣ_{h,k} = ω(g,h,k) L^{k • x}_{g,h} Lˣ_{gh,k}` (arXiv:2502.20257, `eq:omega_and_Ls`;
arXiv:2203.12563, `pentagongroups` and line 1129).

As a consequence, the restriction of `ω` to any subgroup fixing one block has trivial gauge
class (arXiv:2203.12563, lines 740--745). The single-block theorem
`MPOTensor.GroupFamily.IsNormalRepresentation.isTrivialGaugeClass_omega_of_invariant` is the
case of a one-point set.

## Main definitions

* `MPOTensor.GroupFamily.CarriesMPV`: `O` carries the periodic vector of one state to that of
  another at every positive length.
* `MPOTensor.GroupFamily.BlockActionData`: a choice of action tensors for permuted blocks.
* `MPOTensor.GroupFamily.BlockActionData.lSymbol`: the L-symbols.

## Main results

* `MPOTensor.GroupFamily.BlockActionData.isCompatible_lSymbol`: `eq:omega_and_Ls`.
* `MPOTensor.GroupFamily.IsNormalRepresentation.isTrivialGaugeClass_comap_omega_of_fixed`:
  a subgroup fixing a block trivializes the restricted three-cocycle.

The bond dimensions of the blocks may depend on the block. The hypotheses are weaker than the
sources': operator and state tensors are normal rather than injective, and neither unitarity,
simplicity, transitivity, nor finiteness is used.
-/

open scoped Matrix Kronecker
open TNLean.Algebra

namespace MPOTensor

namespace GroupFamily

universe u v

variable {d : ℕ} {G : Type u} [Group G] {F : GroupFamily G d}
  {X : Type v} [MulAction G X] {D : X → ℕ} {A : (x : X) → MPSTensor d (D x)}

/-! ### Carried vectors -/

/-- The periodic operators of `T` carry the periodic vector of `B` to that of `B'` at every
positive length.

Source: arXiv:2203.12563, `REsubmission.tex` line 1064: `U_g |ψ_{A_x}⟩ = |ψ_{A_y}⟩`. -/
def CarriesMPV {D₁ D₂ D₃ : ℕ} (T : MPOTensor d D₁) (B : MPSTensor d D₂)
    (B' : MPSTensor d D₃) : Prop :=
  ∀ N, 0 < N →
    mpo T N *ᵥ (fun τ : Fin N → Fin d ↦ MPSTensor.mpv B τ) = fun σ ↦ MPSTensor.mpv B' σ

omit [Group G] [MulAction G X] in
/-- An action tensor of an operator carrying `B` to `B'`, applied to a state with the
positive-length vectors of `B`, has the positive-length vectors of `B'`. -/
theorem CarriesMPV.sameMPV₂Pos_actTensor {D₁ D₂ D₃ D₄ : ℕ} {T : MPOTensor d D₁}
    {B : MPSTensor d D₂} {B' : MPSTensor d D₃} {C : MPSTensor d D₄} (hT : CarriesMPV T B B')
    (hC : MPSTensor.SameMPV₂Pos C B) : MPSTensor.SameMPV₂Pos (actTensor T C) B' := by
  intro N hN σ
  have hC' : (fun τ : Fin N → Fin d ↦ MPSTensor.mpv C τ) = fun τ ↦ MPSTensor.mpv B τ :=
    funext (hC N hN)
  rw [← congrFun (mpo_mulVec_mpv T C N) σ, hC', hT N hN]

omit [Group G] [MulAction G X] in
/-- Operators carrying `B` to `B'` and `B'` to `B''` compose to an operator carrying `B` to
`B''`. -/
theorem CarriesMPV.mulTensor {D₁ D₂ D₃ D₄ D₅ : ℕ} {M : MPOTensor d D₁} {N : MPOTensor d D₂}
    {B : MPSTensor d D₃} {B' : MPSTensor d D₄} {B'' : MPSTensor d D₅}
    (hM : CarriesMPV M B' B'') (hN : CarriesMPV N B B') : CarriesMPV (mulTensor M N) B B'' := by
  intro L hL
  rw [mpo_mulTensor, ← Matrix.mulVec_mulVec, hN L hL, hM L hL]

/-! ### Identification of blocks along equal points -/

omit [Group G] [MulAction G X] in
/-- The permutation matrix identifying the bond spaces of the blocks at two equal points. -/
noncomputable def castBlock (D : X → ℕ) {y y' : X} (e : y = y') :
    Matrix (Fin (D y')) (Fin (D y)) ℂ :=
  (finCongr (congrArg D e.symm)).toPEquiv.toMatrix

omit [Group G] [MulAction G X] in
@[simp] theorem castBlock_rfl (y : X) : castBlock D (rfl : y = y) = 1 := by
  simp [castBlock]

omit [Group G] [MulAction G X] in
@[simp] theorem castBlock_mul_castBlock {y y' y'' : X} (e₁ : y = y') (e₂ : y' = y'')
    {n : ℕ} (Z : Matrix (Fin (D y)) (Fin n) ℂ) :
    castBlock D e₂ * (castBlock D e₁ * Z) = castBlock D (e₁.trans e₂) * Z := by
  subst e₁ e₂
  simp

omit [Group G] [MulAction G X] in
/-- A reduction onto the block at `y` is a reduction onto the block at any `y' = y`, after
identifying the bond spaces. -/
theorem isReduction_castBlock {n : ℕ} {B : MPSTensor d n} {y y' : X}
    {V : Matrix (Fin (D y)) (Fin n) ℂ} {W : Matrix (Fin n) (Fin (D y)) ℂ}
    (h : MPSTensor.IsReduction B (A y) V W) (e : y = y') :
    MPSTensor.IsReduction B (A y') (castBlock D e * V) (W * castBlock D e.symm) := by
  subst e
  simpa using h

/-! ### Action tensors -/

/-- A choice of action tensors for permuted blocks: for every `g` and `x`, a reduction
`(V_{g,x}, W_{g,x})` of the action tensor `O_g · A_x` onto `A_{g • x}`.

Source: arXiv:2203.12563, equation `mpoMPSsten`, lines 1066--1090; arXiv:2502.20257,
`sec:MPUonMPS`, lines 1750--1800. -/
structure BlockActionData (F : GroupFamily G d) (A : (x : X) → MPSTensor d (D x)) where
  /-- The left action tensor of `g` on the block `x`. -/
  V : ∀ (g : G) (x : X), Matrix (Fin (D (g • x))) (Fin (F.bondDim g * D x)) ℂ
  /-- The right action tensor of `g` on the block `x`. -/
  W : ∀ (g : G) (x : X), Matrix (Fin (F.bondDim g * D x)) (Fin (D (g • x))) ℂ
  isReduction : ∀ g x,
    MPSTensor.IsReduction (actTensor (F.tensor g) (A x)) (A (g • x)) (V g x) (W g x)

/-- **Existence of action tensors** for normal blocks of positive bond dimension permuted by
the family (arXiv:2203.12563, `mpoMPSsten`, citing arXiv:1706.07329v2, Proposition 20). -/
theorem nonempty_blockActionData (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) :
    Nonempty (BlockActionData F A) := by
  choose V W h using fun g x ↦
    exists_isReduction_actTensor_of_isNormal (F.tensor g) (A x) (A (g • x)) (hA _) (hD _)
      (hperm g x)
  exact ⟨⟨V, W, fun g x ↦ (h g x).1⟩⟩

namespace BlockActionData

variable (fd : FusionData F) (ad : BlockActionData F A)

/-- The left boundary of the reduction of `(O_g O_h) · A_x` onto `A_{g • (h • x)}` by two
successive action tensors: `V_{g, h • x} (1 ⊗ V_{h,x}) a⁻¹`.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913. -/
noncomputable def actV (g h : G) (x : X) :
    Matrix (Fin (D (g • h • x))) (Fin (F.bondDim g * F.bondDim h * D x)) ℂ :=
  ad.V g (h • x) * idKron (F.bondDim g) (ad.V h x) *
    mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (D x)

/-- The left boundary of the reduction of `(O_g O_h) · A_x` onto `A_{g • (h • x)}` by the
fusion tensor of `(g, h)`, the action tensor of `gh`, and the identification
`(gh) • x = g • (h • x)`.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913. -/
noncomputable def fuseV (g h : G) (x : X) :
    Matrix (Fin (D (g • h • x))) (Fin (F.bondDim g * F.bondDim h * D x)) ℂ :=
  castBlock D (mul_smul g h x) * (ad.V (g * h) x * kronId (fd.V g h) (D x))

theorem exists_isReduction_actV (g h : G) (x : X) : ∃ W, MPSTensor.IsReduction
    (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) (A (g • h • x)) (ad.actV g h x) W :=
  ⟨_, (((ad.isReduction h x).actTensor_idKron (F.tensor g)).trans
    (ad.isReduction g (h • x))).actTensor_assoc_left⟩

theorem exists_isReduction_fuseV (g h : G) (x : X) : ∃ W, MPSTensor.IsReduction
    (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) (A (g • h • x))
      (ad.fuseV fd g h x) W :=
  ⟨_, isReduction_castBlock
    (((fd.isReduction g h).actTensor_kronId (A x)).trans (ad.isReduction (g * h) x))
    (mul_smul g h x)⟩

open Classical in
/-- **The L-symbols of permuted blocks**: `Lˣ_{g,h}` is the nonzero scalar with
`actV g h x ~ Lˣ_{g,h} · fuseV g h x` against long words of `(O_g O_h) · A_x`
(`MPOTensor.GroupFamily.BlockActionData.isDressedProportional_lSymbol`), set to one if no such
scalar exists.

Source: arXiv:2502.20257, `eq:defL`, `main.tex` lines 1905--1913; arXiv:2203.12563,
`sec:PBC`, line 1091. -/
noncomputable def lSymbol : LSymbol G X := fun x g h ↦
  if hz : ∃ z : ℂ, z ≠ 0 ∧ MPSTensor.IsDressedProportional
      (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) (ad.actV g h x) (ad.fuseV fd g h x) z
  then Units.mk0 hz.choose hz.choose_spec.1 else 1

variable {fd ad}

theorem isDressedProportional_lSymbol (hA : ∀ x, Kraus.IsNormal (A x))
    (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) (x : X) (g h : G) :
    MPSTensor.IsDressedProportional (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x))
      (ad.actV g h x) (ad.fuseV fd g h x) (ad.lSymbol fd x g h) := by
  have hex : ∃ z : ℂ, z ≠ 0 ∧ MPSTensor.IsDressedProportional
      (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A x)) (ad.actV g h x)
        (ad.fuseV fd g h x) z := by
    obtain ⟨W, hW⟩ := ad.exists_isReduction_actV g h x
    obtain ⟨W', hW'⟩ := ad.exists_isReduction_fuseV fd g h x
    exact hW.exists_isDressedProportional hW' (hA _)
      (((hperm g (h • x)).mulTensor (hperm h x)).sameMPV₂Pos_actTensor
        (sameMPV₂Pos_refl (A x)))
  simp only [lSymbol, hex, ↓reduceDIte, Units.val_mk0]
  exact hex.choose_spec.2

/-! ### The five reductions of the triple action -/

section Triple

variable (g h k : G) (x : X)

/-- Moving an identification of target blocks out of the operator layer of an action tensor:
`V_{g,y'} (1 ⊗ castBlock e Y) = castBlock (g • e) V_{g,y} (1 ⊗ Y)` for `e : y = y'`. -/
private theorem V_mul_idKron_castBlock (g : G) {y y' : X} (e : y = y') {n : ℕ}
    (Y : Matrix (Fin (D y)) (Fin n) ℂ) :
    ad.V g y' * idKron (F.bondDim g) (castBlock D e * Y) =
      castBlock D (congrArg (g • ·) e) * (ad.V g y * idKron (F.bondDim g) Y) := by
  subst e
  simp

/-- Moving a bond identification of the operator factor out of the action tensor of an
element: `V_{b,y} (castMat e Y ⊗ 1) = castBlock (e • y) V_{a,y} (Y ⊗ 1)` for `e : a = b`. -/
private theorem V_mul_kronId_castMat {a b : G} (e : a = b) (y : X) {n : ℕ}
    (Y : Matrix (Fin (F.bondDim a)) (Fin n) ℂ) :
    ad.V b y * kronId (F.castMat e * Y) (D y) =
      castBlock D (congrArg (· • y) e) * (ad.V a y * kronId Y (D y)) := by
  subst e
  simp

/-- The pentagon step: acting with `k` first and then with `h` and `g` is the same boundary
as acting with the pair `(h, k)` inside the action of `g`. -/
private theorem actV_mul_reduce_k :
    ad.actV g h (k • x) * (idKron (F.bondDim g * F.bondDim h) (ad.V k x) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) (D x)) =
      ad.V g (h • k • x) * idKron (F.bondDim g) (ad.actV h k x) *
        (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) (D x) *
          kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (D x)) := by
  simp only [actV, ← idKron_mul, Matrix.mul_assoc, assocInv_mul_idKron_assoc]
  rw [← Matrix.mul_assoc (idKron (F.bondDim g) (mulTensorAssocInvMatrix _ _ _)),
    assocInv_pentagon]

/-- The inner fusion step: acting with `g` on the fused pair `(h, k)` is the action tree of
`(g, hk)` composed with the fusion of `h` with `k` on the triple. -/
private theorem fuseV_inner_eq :
    ad.V g (h • k • x) * idKron (F.bondDim g) (ad.fuseV fd h k x) *
        (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h * F.bondDim k) (D x) *
          kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (D x)) =
      castBlock D (congrArg (g • ·) (mul_smul h k x)) *
        (ad.actV g (h * k) x * kronId (idKron (F.bondDim g) (fd.V h k) *
          mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (D x)) := by
  simp only [fuseV]
  rw [V_mul_idKron_castBlock]
  simp only [actV, ← idKron_mul, ← kronId_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (idKron _ (kronId _ _)), ← assocInv_mul_kronId_idKron,
    Matrix.mul_assoc]

/-- Acting with `k` first and then fusing `g` with `h` is the action tree of `(gh, k)` composed
with the fusion of `g` with `h` on the triple. -/
private theorem fuseV_mul_reduce_k :
    ad.fuseV fd g h (k • x) * (idKron (F.bondDim g * F.bondDim h) (ad.V k x) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) (D x)) =
      castBlock D (mul_smul g h (k • x)) *
        (ad.actV (g * h) k x * kronId (kronId (fd.V g h) (F.bondDim k)) (D x)) := by
  simp only [actV, fuseV, Matrix.mul_assoc, kronId_mul_idKron_assoc]
  rw [← assocInv_mul_kronId_kronId]

/-- Fusing `gh` with `k` after fusing `g` with `h` is the fusion tree `leftV` of the associator,
followed by the action of `ghk`. -/
private theorem fuseV_mul_left :
    ad.fuseV fd (g * h) k x * kronId (kronId (fd.V g h) (F.bondDim k)) (D x) =
      castBlock D (mul_smul (g * h) k x) *
        (ad.V (g * h * k) x * kronId (fd.leftV g h k) (D x)) := by
  simp only [fuseV, FusionData.leftV, Matrix.mul_assoc, kronId_mul]

/-- Fusing `g` with `hk` after fusing `h` with `k` is the fusion tree `rightV` of the
associator, followed by the action of `ghk`. -/
private theorem fuseV_mul_right :
    ad.fuseV fd g (h * k) x * kronId (idKron (F.bondDim g) (fd.V h k) *
        mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (D x) =
      castBlock D ((congrArg (· • x) (mul_assoc g h k)).trans (mul_smul g (h * k) x)) *
        (ad.V (g * h * k) x * kronId (fd.rightV g h k) (D x)) := by
  simp only [fuseV, FusionData.rightV, Matrix.mul_assoc, kronId_mul]
  rw [V_mul_kronId_castMat, castBlock_mul_castBlock]

end Triple

/-- **Compatibility of the L-symbols of permuted blocks with the anomaly three-cocycle**
(arXiv:2502.20257, `eq:omega_and_Ls`, `main.tex` lines 1920--1923; arXiv:2203.12563,
`pentagongroups` and line 1129):
`Lˣ_{g,hk} Lˣ_{h,k} = ω(g,h,k) L^{k • x}_{g,h} Lˣ_{gh,k}`. -/
theorem isCompatible_lSymbol (hF : F.IsNormalRepresentation) (hA : ∀ x, Kraus.IsNormal (A x))
    (hD : ∀ x, 0 < D x) (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x))) :
    LSymbol.IsCompatible (ad.lSymbol fd) fd.omega := by
  intro x g h k
  set B3 := actTensor (F.tripleTensor g h k) (A x)
  have hcar3 : CarriesMPV (F.tripleTensor g h k) (A x) (A (g • h • k • x)) :=
    ((hperm g _).mulTensor (hperm h _)).mulTensor (hperm k x)
  have hSame3 : MPSTensor.SameMPV₂Pos B3 (A (g • h • k • x)) :=
    hcar3.sameMPV₂Pos_actTensor (sameMPV₂Pos_refl (A x))
  have hSameC : ∀ (a b : G) (y : X),
      MPSTensor.SameMPV₂Pos (actTensor (mulTensor (F.tensor a) (F.tensor b)) (A y))
        (A (a • b • y)) :=
    fun a b y ↦ ((hperm a _).mulTensor (hperm b y)).sameMPV₂Pos_actTensor
      (sameMPV₂Pos_refl (A y))
  have hSame3C : ∀ (a b : G) (y : X), a • b • y = g • h • k • x →
      MPSTensor.SameMPV₂Pos B3 (actTensor (mulTensor (F.tensor a) (F.tensor b)) (A y)) := by
    intro a b y e N hN σ
    rw [hSame3 N hN σ, hSameC a b y N hN σ, e]
  have hR : MPSTensor.IsReduction B3
      (actTensor (mulTensor (F.tensor g) (F.tensor h)) (A (k • x)))
      (idKron (F.bondDim g * F.bondDim h) (ad.V k x) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) (D x)) _ :=
    ((ad.isReduction k x).actTensor_idKron
      (mulTensor (F.tensor g) (F.tensor h))).actTensor_assoc_left
  have hS : MPSTensor.IsReduction B3
      (actTensor (mulTensor (F.tensor (g * h)) (F.tensor k)) (A x))
      (kronId (kronId (fd.V g h) (F.bondDim k)) (D x)) _ :=
    ((fd.isReduction g h).mulTensor_kronId (F.tensor k)).actTensor_kronId (A x)
  have hK : MPSTensor.IsReduction B3
      (actTensor (mulTensor (F.tensor g) (F.tensor (h * k))) (A x))
      (kronId (idKron (F.bondDim g) (fd.V h k) *
        mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (D x)) _ :=
    ((fd.isReduction h k).mulTensor_idKron (F.tensor g)).mulTensor_assoc_left.actTensor_kronId
      (A x)
  have H3 := (isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hperm (k • x) g h).pullback
    hR (hSame3C g h (k • x) rfl)
  have H4 := ((isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hperm x (g * h) k).pullback
    hS (hSame3C (g * h) k x (by simp only [mul_smul]))).mul_left
      (castBlock D (mul_smul g h (k • x)))
  have H2 := ((isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hperm x g (h * k)).pullback
    hK (hSame3C g (h * k) x (by simp only [mul_smul]))).mul_left
      (castBlock D (congrArg (g • ·) (mul_smul h k x)))
  have H1 := (((isDressedProportional_lSymbol (fd := fd) (ad := ad) hA hperm x h k).actTensor_idKron
      (F.tensor g)).mul_left (ad.V g (h • k • x))).of_intertwine
      (mulTensorAssocMatrix_mul_invMatrix _ _ _) (mulTensorAssocInvMatrix_mul_matrix _ _ _)
      (actTensor_mulTensor_mul_assocMatrix (F.tensor g)
        (mulTensor (F.tensor h) (F.tensor k)) (A x))
  have H1' := H1.of_intertwine (B' := B3)
      (P := kronId (mulTensorAssocMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (D x))
      (Q := kronId (mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (D x))
      (by rw [kronId_mul, mulTensorAssocMatrix_mul_invMatrix, kronId_one])
      (by rw [kronId_mul, mulTensorAssocInvMatrix_mul_matrix, kronId_one])
      (actTensor_mul_kronId_of_intertwine (A x) fun i l ↦
        mulTensor_mul_assocMatrix (F.tensor g) (F.tensor h) (F.tensor k) i l)
  have H5 := (((fd.isAssociator_omega hF g h k).actTensor_kronId (A x)).mul_left
    (ad.V (g * h * k) x)).mul_left
      (castBlock D ((mul_smul (g * h) k x).trans (mul_smul g h (k • x))))
  -- the canonical boundaries
  have H1'' : MPSTensor.IsDressedProportional B3
      (ad.actV g h (k • x) * (idKron (F.bondDim g * F.bondDim h) (ad.V k x) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) (D x)))
      (castBlock D (congrArg (g • ·) (mul_smul h k x)) *
        (ad.actV g (h * k) x * kronId (idKron (F.bondDim g) (fd.V h k) *
          mulTensorAssocInvMatrix (F.bondDim g) (F.bondDim h) (F.bondDim k)) (D x)))
      (ad.lSymbol fd x h k) := by
    rw [actV_mul_reduce_k, ← fuseV_inner_eq]
    simpa only [Matrix.mul_assoc] using H1'
  rw [fuseV_mul_right, castBlock_mul_castBlock] at H2
  rw [fuseV_mul_reduce_k] at H3
  rw [fuseV_mul_left, castBlock_mul_castBlock] at H4
  have hleft := H1''.trans H2
  have hright := (H3.trans H4).trans H5
  have hne : ∀ N : ℕ, ∃ w : List (Fin d), N ≤ w.length ∧
      ad.actV g h (k • x) * (idKron (F.bondDim g * F.bondDim h) (ad.V k x) *
        mulTensorAssocInvMatrix (F.bondDim g * F.bondDim h) (F.bondDim k) (D x)) *
          Kraus.evalWord B3 w ≠ 0 := by
    obtain ⟨W, hW⟩ := ad.exists_isReduction_actV g h (k • x)
    exact (hR.trans hW).exists_mul_evalWord_ne_zero (hA _) (hD _)
  have heq := MPSTensor.IsDressedProportional.eq_of_forall_exists_ne_zero hleft hright hne
  apply Units.ext
  simp only [Units.val_mul]
  linear_combination heq

end BlockActionData

/-- **A subgroup fixing a block trivializes the anomaly.** For normal blocks of positive bond
dimension permuted by a group of matrix product operators with normal tensors, the
restriction of the anomaly three-cocycle to any subgroup that fixes one block has trivial gauge
class.

Source: arXiv:2203.12563, `REsubmission.tex` lines 740--745 (a subgroup leaving a block
invariant trivializes the three-cocycle), in the periodic setting of `sec:PBC`, lines
1064--1129. -/
theorem IsNormalRepresentation.isTrivialGaugeClass_comap_omega_of_fixed
    (hF : F.IsNormalRepresentation) (fd : FusionData F) (hA : ∀ x, Kraus.IsNormal (A x))
    (hD : ∀ x, 0 < D x) (hperm : ∀ g x, CarriesMPV (F.tensor g) (A x) (A (g • x)))
    {H : Type*} [Group H] (f : H →* G) (x : X) (hfix : ∀ a, f a • x = x) :
    ScalarThreeCochain.IsTrivialGaugeClass (ScalarThreeCochain.comap f fd.omega) := by
  obtain ⟨ad⟩ := nonempty_blockActionData (F := F) hA hD hperm
  exact LSymbol.isTrivialGaugeClass_comap_of_isCompatible
    (ad.isCompatible_lSymbol hF hA hD hperm) x f hfix

end GroupFamily

end MPOTensor
