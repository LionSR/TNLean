/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.MPDO.BoundarySourceMixedPentagon

/-!
# The group specialization of the multiplicity L- and F-symbols

Suppose the operator blocks are labelled by a group `G` with the group
fusion rule `N_{gh}^k = δ_{k,gh}`, and the state blocks by a `G`-set `X`
with action multiplicities `M_{g,x}^y = δ_{y,g·x}`. Then every multiplicity
space of the exact fusion and action maps has exactly one element, so the
L matrix and the F matrix each have one relevant entry:

* `Lˣ_{g,h} = (L^{(gh)·x}_{g,h,x})^{h·x}_{gh}`, and
* `ω(g,h,k) = F^{ghk}_{g,h,k}[(gh),(hk)]`.

The L entries are nonzero because the L matrices are invertible. The
multiplicity coupled pentagon then becomes the scalar compatibility

`Lˣ_{g,hk} Lˣ_{h,k} = ω(g,h,k) L^{k·x}_{g,h} Lˣ_{gh,k}`,

so the pair `(L, ω)` is a scalar L-symbol compatible with a scalar
three-cochain. If some state block is fixed by the whole group, in
particular if there is only one block, the cochain `ω` is a coboundary:
this is the group case of the obstruction of GLM23, lines 607--636.

The hypotheses are those of the formalized coupled pentagon, with the
fusion and action multiplicities of the group case (GLM23, lines 640--683).

## Main results

* `MPOTensor.groupLScalar`, `MPOTensor.groupFScalar`: the scalar entries.
* `MPOTensor.groupLScalar_ne_zero`: the scalar L entries do not vanish.
* `MPOTensor.groupFScalar_mul_groupLScalar`: the coupled pentagon in the
  group case.
* `MPOTensor.exists_lSymbol_isCompatible_of_group`: the scalar L-symbols are
  compatible with the scalar F-symbols.
* `MPOTensor.isTrivialGaugeClass_of_group_of_forall_smul_eq`: a block fixed
  by the whole group forces a trivial gauge class.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
  `coupledpent` (lines 554--562), the group case (lines 640--720), and
  Section `nonuniqueGS` (lines 607--636).
* arXiv:2502.20257, `eq:omega_and_Ls`, for the scalar compatibility.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  {G : Type} [Group G] {X : Type*} [MulAction G X]
  (eG : G ≃ Fin r) (eX : X ≃ Fin s)
  (hN : ∀ g h c, N (eG g) (eG h) c = if c = eG (g * h) then 1 else 0)
  (hM : ∀ g x y, M (eG g) (eX x) y = if y = eX (g • x) then 1 else 0)

include hN in
/-- Group fusion multiplicity spaces have at most one element. -/
theorem subsingleton_fin_fusion_of_group (a b c : Fin r) :
    Subsingleton (Fin (N a b c)) := by
  rw [Fin.subsingleton_iff_le_one, ← eG.apply_symm_apply a, ← eG.apply_symm_apply b, hN]
  split_ifs <;> omega

include hM in
/-- Group action multiplicity spaces have at most one element. -/
theorem subsingleton_fin_action_of_group (a : Fin r) (x y : Fin s) :
    Subsingleton (Fin (M a x y)) := by
  rw [Fin.subsingleton_iff_le_one, ← eG.apply_symm_apply a, ← eX.apply_symm_apply x, hM]
  split_ifs <;> omega

/-- The unique index of the fusion channel `g × h → gh`. -/
def groupFusionIndex (g h : G) {c : Fin r} (hc : c = eG (g * h)) : Fin (N (eG g) (eG h) c) :=
  ⟨0, by rw [hN]; simp [hc]⟩

/-- The unique index of the action channel `g · x → g • x`. -/
def groupActionIndex (g : G) (x : X) {y : Fin s} (hy : y = eX (g • x)) :
    Fin (M (eG g) (eX x) y) :=
  ⟨0, by rw [hM]; simp [hy]⟩

variable (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)

/-- The scalar L-symbol `Lˣ_{g,h}`: the entry of the L matrix of `g, h`
acting on `x`, with intermediate block `h · x` and fused label `gh`.
Source: GLM23, `1Fsymbol` (lines 538--548) in the group case. -/
noncomputable def groupLScalar (x : X) (g h : G) : ℂ :=
  actionLMatrix WF VA WA (eG g) (eG h) (eX x) (eX ((g * h) • x))
    ⟨eX (h • x), groupActionIndex eG eX hM g (h • x) (by rw [mul_smul]),
      groupActionIndex eG eX hM h x rfl⟩
    ⟨eG (g * h), groupActionIndex eG eX hM (g * h) x rfl, groupFusionIndex eG hN g h rfl⟩

/-- The scalar F-symbol `ω(g,h,k)`: the entry of the F matrix of `g, h, k`
with intermediate labels `gh` and `hk`. Source: GLM23, `Fsymbolsdef`, in
the group case. -/
noncomputable def groupFScalar (g h k : G) : ℂ :=
  fusionFMatrix VF WF (eG g) (eG h) (eG k) (eG (g * h * k))
    ⟨eG (g * h), groupFusionIndex eG hN g h rfl, groupFusionIndex eG hN (g * h) k rfl⟩
    ⟨eG (h * k), groupFusionIndex eG hN h k rfl,
      groupFusionIndex eG hN g (h * k) (by rw [mul_assoc])⟩

include hM in
/-- Any L entry with the group indices is the scalar L-symbol. -/
theorem actionLMatrix_eq_groupLScalar (x : X) (g h : G) {z y : Fin s} {c : Fin r}
    (hz : z = eX (h • x)) (hy : y = eX ((g * h) • x)) (hc : c = eG (g * h))
    (i : Fin (M (eG g) z y)) (j : Fin (M (eG h) (eX x) z)) (k : Fin (M c (eX x) y))
    (μ : Fin (N (eG g) (eG h) c)) :
    actionLMatrix WF VA WA (eG g) (eG h) (eX x) y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
      groupLScalar eG eX hN hM WF VA WA x g h := by
  subst hz hy hc
  have := subsingleton_fin_action_of_group eG eX hM
  have := subsingleton_fin_fusion_of_group eG hN
  unfold groupLScalar
  congr 3 <;> apply Subsingleton.elim

include hN in
/-- Any F entry with the group indices is the scalar F-symbol. -/
theorem fusionFMatrix_eq_groupFScalar (g h k : G) {d e f : Fin r}
    (hd : d = eG (g * h)) (he : e = eG (g * h * k)) (hf : f = eG (h * k))
    (η : Fin (N (eG g) (eG h) d)) (χ' : Fin (N d (eG k) e))
    (μ : Fin (N (eG h) (eG k) f)) (ν : Fin (N (eG g) f e)) :
    fusionFMatrix VF WF (eG g) (eG h) (eG k) e ⟨d, η, χ'⟩ ⟨f, μ, ν⟩ =
      groupFScalar eG hN VF WF g h k := by
  subst hd he hf
  have := subsingleton_fin_fusion_of_group eG hN
  unfold groupFScalar
  congr 3 <;> apply Subsingleton.elim

variable {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
  (hInjA : ∀ x, Kraus.IsInjective (A x)) (hD : ∀ x, 0 < D x)
  (hneA : MPSTensor.BlocksNotGaugePhaseEquiv A)

include hF hA hInjA hD hneA in
/-- The scalar L-symbols do not vanish: the one-entry L matrix is invertible.
Source: GLM23, `eq:F_symbol2`, "non-zero constants" (line 522). -/
theorem groupLScalar_ne_zero (x : X) (g h : G) :
    groupLScalar eG eX hN hM WF VA WA x g h ≠ 0 := by
  classical
  obtain ⟨h₁, -⟩ := actionLMatrix_inverse_of_isInjective VF WF VA WA hF hA hD hInjA hneA
    (eG g) (eG h) (eX x) (eX ((g * h) • x))
  have hsM := subsingleton_fin_action_of_group eG eX hM
  have hsN := subsingleton_fin_fusion_of_group eG hN
  have hQ : Subsingleton (FusionActionMultiplicity N M (eG g) (eG h) (eX x)
      (eX ((g * h) • x))) := by
    rw [← Fintype.card_le_one_iff_subsingleton]
    simp only [FusionActionMultiplicity, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin, hN, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, hM, le_refl]
  set p : SequentialActionMultiplicity M (eG g) (eG h) (eX x) (eX ((g * h) • x)) :=
    ⟨eX (h • x), groupActionIndex eG eX hM g (h • x) (by rw [mul_smul]),
      groupActionIndex eG eX hM h x rfl⟩
  set q : FusionActionMultiplicity N M (eG g) (eG h) (eX x) (eX ((g * h) • x)) :=
    ⟨eG (g * h), groupActionIndex eG eX hM (g * h) x rfl, groupFusionIndex eG hN g h rfl⟩
  have h := congrArg (fun Z ↦ Z p p) h₁
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Fintype.sum_subsingleton _ q] at h
  exact left_ne_zero_of_mul_eq_one h

variable (O A) in
include hF hA hInjA hD hneA in
/-- **The coupled pentagon in the group case.** For the group fusion and
action multiplicities, the multiplicity coupled pentagon reads

`L^{k·x}_{g,h} L^x_{gh,k} ω(g,h,k) = L^x_{h,k} L^x_{g,hk}`.

Source: GLM23, `coupledpent` (lines 554--562), specialized to the group
case of lines 640--720. -/
theorem groupFScalar_mul_groupLScalar
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (x : X) (g h k : G) :
    groupLScalar eG eX hN hM WF VA WA (k • x) g h *
        groupLScalar eG eX hN hM WF VA WA x (g * h) k * groupFScalar eG hN VF WF g h k =
      groupLScalar eG eX hN hM WF VA WA x h k *
        groupLScalar eG eX hN hM WF VA WA x g (h * k) := by
  classical
  have hsM := subsingleton_fin_action_of_group eG eX hM
  have hsN := subsingleton_fin_fusion_of_group eG hN
  have hp := actionLMatrix_mixed_pentagon O A hInjO hInjA hχ hD hneO hneA VF WF VA WA hF hA
    (eG g) (eG h) (eG k) (eG (g * h * k)) (eG (h * k)) (eX x) (eX ((g * h * k) • x))
    (eX ((h * k) • x)) (eX (k • x))
    (groupActionIndex eG eX hM g ((h * k) • x) (by rw [← mul_smul, mul_assoc]))
    (groupActionIndex eG eX hM h (k • x) (by rw [mul_smul]))
    (groupActionIndex eG eX hM k x rfl)
    (groupActionIndex eG eX hM (g * h * k) x rfl)
    (groupFusionIndex eG hN h k rfl)
    (groupFusionIndex eG hN g (h * k) (by rw [mul_assoc]))
  rw [Finset.sum_eq_single (eG (g * h)) (fun v _ hv ↦ Finset.sum_eq_zero fun _ _ ↦
      Finset.sum_eq_zero fun η _ ↦ (Fin.cast (by rw [hN]; simp [hv]) η : Fin 0).elim0)
      (fun hmem ↦ absurd (Finset.mem_univ _) hmem),
    Fintype.sum_subsingleton _
      (groupActionIndex eG eX hM (g * h) (k • x) (by rw [mul_smul])),
    Fintype.sum_subsingleton _ (groupFusionIndex eG hN g h rfl),
    Fintype.sum_subsingleton _ (groupFusionIndex eG hN (g * h) k rfl),
    Fintype.sum_subsingleton _ (groupActionIndex eG eX hM (h * k) x rfl)] at hp
  rw [actionLMatrix_eq_groupLScalar eG eX hN hM WF VA WA (k • x) g h
      (z := eX ((h * k) • x)) (y := eX ((g * h * k) • x)) (c := eG (g * h))
      (by rw [mul_smul]) (by rw [mul_smul]) rfl,
    actionLMatrix_eq_groupLScalar eG eX hN hM WF VA WA x (g * h) k
      (z := eX (k • x)) (y := eX ((g * h * k) • x)) (c := eG (g * h * k)) rfl rfl rfl,
    fusionFMatrix_eq_groupFScalar eG hN VF WF g h k
      (d := eG (g * h)) (e := eG (g * h * k)) (f := eG (h * k)) rfl rfl rfl,
    actionLMatrix_eq_groupLScalar eG eX hN hM WF VA WA x h k
      (z := eX (k • x)) (y := eX ((h * k) • x)) (c := eG (h * k)) rfl rfl rfl,
    actionLMatrix_eq_groupLScalar eG eX hN hM WF VA WA x g (h * k)
      (z := eX ((h * k) • x)) (y := eX ((g * h * k) • x)) (c := eG (g * h * k))
      rfl (by rw [mul_assoc]) (by rw [mul_assoc])] at hp
  exact hp

variable (O A) in
include hF hA hInjA hD hneA in
/-- **The group specialization of the L- and F-symbols.** For the group
fusion and action multiplicities, the scalar L entries form a scalar
L-symbol and the scalar F entries a scalar three-cochain, and the
multiplicity coupled pentagon is the scalar compatibility
`Lˣ_{g,hk} Lˣ_{h,k} = ω(g,h,k) L^{k·x}_{g,h} Lˣ_{gh,k}`
(arXiv:2502.20257, `eq:omega_and_Ls`). The state has at least one block;
its nonvanishing L entries make the F entries nonzero. Source: GLM23,
`coupledpent`, lines 554--562, and the group case, lines 640--720. -/
theorem exists_lSymbol_isCompatible_of_group [Nonempty X]
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor)) :
    ∃ (L : TNLean.Algebra.LSymbol G X) (ω : TNLean.Algebra.ScalarThreeCochain G),
      (∀ x g h, (L x g h : ℂ) = groupLScalar eG eX hN hM WF VA WA x g h) ∧
      (∀ g h k, (ω g h k : ℂ) = groupFScalar eG hN VF WF g h k) ∧
      L.IsCompatible ω := by
  have hL := groupLScalar_ne_zero eG eX hN hM VF WF VA WA hF hA hInjA hD hneA
  have hP := groupFScalar_mul_groupLScalar eG eX hN hM VF WF VA WA O A hF hA hInjA hD hneA
    hInjO hχ hneO
  have hω : ∀ g h k, groupFScalar eG hN VF WF g h k ≠ 0 := by
    intro g h k hzero
    obtain ⟨x⟩ := ‹Nonempty X›
    have := hP x g h k
    rw [hzero, mul_zero] at this
    exact mul_ne_zero (hL _ _ _) (hL _ _ _) this.symm
  refine ⟨fun x g h ↦ Units.mk0 _ (hL x g h), fun g h k ↦ Units.mk0 _ (hω g h k),
    fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun x g h k ↦ ?_⟩
  apply Units.ext
  simp only [Units.val_mul, Units.val_mk0]
  rw [mul_comm (groupLScalar eG eX hN hM WF VA WA x g (h * k)), ← hP x g h k]
  ring

variable (O A) in
include hM hF hA hInjA hD hneA in
/-- **The group case of the single-block obstruction.** If some state
block is fixed by the whole group, in particular if the state has a single
injective block acted on without multiplicity, then the scalar F-symbol of
the exact fusion maps is a three-coboundary: the MPO symmetry is
non-anomalous. Source: GLM23, lines 607--636; arXiv:2502.20257, line 1925. -/
theorem isTrivialGaugeClass_of_group_of_forall_smul_eq
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor) (hχ : ∀ a, 0 < χ a)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (x : X) (hfix : ∀ g : G, g • x = x) :
    ∃ ω : TNLean.Algebra.ScalarThreeCochain G,
      (∀ g h k, (ω g h k : ℂ) = groupFScalar eG hN VF WF g h k) ∧
      TNLean.Algebra.ScalarThreeCochain.IsTrivialGaugeClass ω := by
  have : Nonempty X := ⟨x⟩
  obtain ⟨L, ω, -, hω, hLω⟩ := exists_lSymbol_isCompatible_of_group eG eX hN hM VF WF VA WA
    O A hF hA hInjA hD hneA hInjO hχ hneO
  exact ⟨ω, hω, TNLean.Algebra.LSymbol.isTrivialGaugeClass_of_isCompatible_of_forall_smul_eq
    hLω x hfix⟩

end MPOTensor
