/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardForm.TwoSiteStandardFormCircuit
import TNLean.MPS.MPU.StandardForm.VirtualGaugePath

/-!
# Interpolating two standard-form presentations with the same gates

Let \(W_1\) and \(W_2\) be two-site tensors of bond dimensions \(D_1\) and
\(D_2\), both presented in standard form with the same unitary gates \(u\) and
\(v\), through half factors \((X_1,X_2)\) and \((X_1',X_2')\). Stacking the
half factors as \((\cos\theta\,X,\ \sin\theta\,X')\) in the bond space of
dimension \(D_1+D_2\) keeps the contraction
\(\cos^2\theta\,v+\sin^2\theta\,v=v\), so every interpolating tensor is again a
standard form with gates \(u,v\) and generates an MPU. At \(\theta=0\) the
stacked tensor is \(W_1\) with unused bond directions adjoined; at
\(\theta=\pi/2\) it is \(W_2\) placed in the last \(D_2\) coordinates, which a
permutation of the bond coordinates moves to the first ones.

This supplies the step from a simple tensor to the tensor constructed from its
own gates in the proof of arXiv:1703.09188, Theorem `IndexTh` (iv),
lines 857--865, which passes from the gates to the tensors without comment.

## Main statements

* `MPOTensor.IsMPU.joinedIn_bondReindex`: a permutation of the bond coordinates
  is joined to the identity through MPU tensors.
* `MPOTensor.TwoSiteStandardFormData.joinedIn_sameMPOSet_padBond`: two standard-form
  presentations with the same gates are joined through tensors with the same
  periodic operators.
* `MPOTensor.TwoSiteStandardFormData.joinedIn_padBond`: two standard-form
  presentations with the same gates are joined through MPU tensors after
  adjoining unused bond directions.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D D₁ D₂ ℓ r : ℕ}

/-- Relabel the bond coordinates of every letter along a permutation. -/
def bondReindex (σ : Fin D ≃ Fin D) (W : MPOTensor d D) : MPOTensor d D :=
  fun ij ↦ (W ij).submatrix σ σ

/-- **A bond relabelling is joined to the tensor through MPU tensors.** It is
the virtual gauge by the permutation matrix.

Source: the gauge freedom of arXiv:1703.09188, lines 294 and 356. -/
theorem IsMPU.joinedIn_bondReindex {W : MPOTensor d D} (hW : IsMPU W)
    (σ : Fin D ≃ Fin D) :
    JoinedIn {V : MPOTensor d D | IsMPU V} W (bondReindex σ W) := by
  set P : Matrix (Fin D) (Fin D) ℂ := σ.toPEquiv.toMatrix
  set Q : Matrix (Fin D) (Fin D) ℂ := σ.symm.toPEquiv.toMatrix
  have hQP : Q * P = 1 := by
    ext a b
    simp [Q, P, PEquiv.mul_toMatrix_toPEquiv, Matrix.one_apply, PEquiv.toMatrix_apply]
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hdet : IsUnit P.det :=
    (Matrix.isUnit_iff_isUnit_det P).mp ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩
  have hinv : P⁻¹ = Q := Matrix.inv_eq_right_inv hPQ
  have hEq : bondReindex σ W = MPOTensor.virtualSandwich P W P⁻¹ := by
    funext i j
    rw [hinv, virtualSandwich_apply, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    simp [bondReindex]
  rw [hEq]
  exact hW.joinedIn_virtualSandwich hdet

/-- The entries of a tensor with unused bond directions adjoined: the original
entries in the first coordinates, zero elsewhere. -/
theorem padBond_apply {D' : ℕ} (W : MPOTensor d D) (h : D ≤ D') (i j : Fin d)
    (α γ : Fin D') :
    padBond W D' h (i, j) α γ =
      if hα : (α : ℕ) < D then if hγ : (γ : ℕ) < D then W (i, j) ⟨α, hα⟩ ⟨γ, hγ⟩ else 0
      else 0 := by
  have hB : ∀ (a : Fin D') (b : Fin D), bondInclusion D D' h a b =
      if (a : ℕ) = b then 1 else 0 := fun _ _ ↦ rfl
  have hin : ∀ (hα : (α : ℕ) < D) (c : Fin D),
      ∑ b : Fin D, bondInclusion D D' h α b * W (i, j) b c = W (i, j) ⟨α, hα⟩ c := by
    intro hα c
    rw [Finset.sum_eq_single ⟨α, hα⟩]
    · simp [hB]
    · intro b _ hb
      have : (α : ℕ) ≠ b := fun e ↦ hb (Fin.ext e.symm)
      simp [hB, this]
    · simp
  have hzero : ∀ a : Fin D', ¬ (a : ℕ) < D → ∀ b : Fin D, bondInclusion D D' h a b = 0 := by
    intro a ha b
    have : (a : ℕ) ≠ b := by omega
    simp [hB, this]
  simp only [padBond, Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases hα : (α : ℕ) < D
  · simp only [hin hα, hα, ↓reduceDIte]
    by_cases hγ : (γ : ℕ) < D
    · rw [Finset.sum_eq_single ⟨γ, hγ⟩]
      · simp [hB, hγ]
      · intro c _ hc
        have : (γ : ℕ) ≠ c := fun e ↦ hc (Fin.ext e.symm)
        simp [hB, this]
      · simp
    · simp only [hγ, ↓reduceDIte]
      refine Finset.sum_eq_zero fun c _ ↦ ?_
      simp [hzero γ hγ c]
  · simp only [hα, ↓reduceDIte]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    simp [hzero α hα]

/-- The two-site tensor built from half factors and an unshifted gate, by the
contraction of equation `StandardForm`.

Source: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
def tensorOfHalves (X₁ : Matrix (Fin d × Fin D) (Fin r) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin ℓ) ℂ)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) : MPOTensor (d * d) D :=
  fun (i, j) α γ ↦ ∑ t : Fin ℓ, ∑ s : Fin r,
    X₂ (α, (finProdFinEquiv.symm i).1) t * u (t, s) (finProdFinEquiv.symm j) *
      X₁ ((finProdFinEquiv.symm i).2, γ) s

/-- A standard-form presentation is the tensor of its half factors. -/
theorem TwoSiteStandardFormData.eq_tensorOfHalves {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) : W = tensorOfHalves S.X₁ S.X₂ u := by
  funext ⟨i, j⟩
  ext α γ
  exact S.W_apply i j α γ

/-- Stack two right half factors with coefficients `c` and `s` in the bond space
of dimension \(D_1+D_2\). -/
def stackRight (c s : ℂ) (Y : Matrix (Fin d × Fin D₁) (Fin r) ℂ)
    (Y' : Matrix (Fin d × Fin D₂) (Fin r) ℂ) :
    Matrix (Fin d × Fin (D₁ + D₂)) (Fin r) ℂ :=
  fun p t ↦ Fin.addCases (fun b ↦ c * Y (p.1, b) t) (fun b ↦ s * Y' (p.1, b) t) p.2

/-- Stack two left half factors with coefficients `c` and `s` in the bond space
of dimension \(D_1+D_2\). -/
def stackLeft (c s : ℂ) (Y : Matrix (Fin D₁ × Fin d) (Fin ℓ) ℂ)
    (Y' : Matrix (Fin D₂ × Fin d) (Fin ℓ) ℂ) :
    Matrix (Fin (D₁ + D₂) × Fin d) (Fin ℓ) ℂ :=
  fun p t ↦ Fin.addCases (fun b ↦ c * Y (b, p.2) t) (fun b ↦ s * Y' (b, p.2) t) p.1

/-- The stacked half factors again contract to the shifted gate when
\(c^2+s^2=1\).

Source: arXiv:1703.09188, equation `StandardForm`, lines 603--617. -/
noncomputable def TwoSiteStandardFormData.stack {W₁ : MPOTensor (d * d) D₁}
    {W₂ : MPOTensor (d * d) D₂}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData W₁ u v) (S₂ : TwoSiteStandardFormData W₂ u v)
    (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) :
    TwoSiteStandardFormData
      (tensorOfHalves (stackRight c s S₁.X₁ S₂.X₁) (stackLeft c s S₁.X₂ S₂.X₂) u) u v where
  phys_pos := S₁.phys_pos
  bond_pos := Nat.add_pos_left S₁.bond_pos _
  left_pos := S₁.left_pos
  right_pos := S₁.right_pos
  X₁ := stackRight c s S₁.X₁ S₂.X₁
  X₂ := stackLeft c s S₁.X₂ S₂.X₂
  u_unitary := S₁.u_unitary
  v_unitary := S₁.v_unitary
  v_apply i₁ i₂ s' t := by
    rw [Fin.sum_univ_add]
    simp only [stackRight, stackLeft, Fin.addCases_left, Fin.addCases_right]
    have h₁ := S₁.v_apply i₁ i₂ s' t
    have h₂ := S₂.v_apply i₁ i₂ s' t
    calc v (i₁, i₂) (s', t) = (c ^ 2 + s ^ 2) * v (i₁, i₂) (s', t) := by rw [hcs, one_mul]
      _ = _ := by
        rw [add_mul]
        nth_rewrite 1 [h₁]
        rw [h₂, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun β _ ↦ ?_ <;> ring
  W_apply _ _ _ _ := rfl

section Endpoints

variable {W₁ : MPOTensor (d * d) D₁} {W₂ : MPOTensor (d * d) D₂}
  {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
  {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}

/-- At \(\theta=0\) the stacked tensor is the first tensor with unused bond
directions adjoined. -/
theorem TwoSiteStandardFormData.tensorOfHalves_stack_one_zero
    (S₁ : TwoSiteStandardFormData W₁ u v) (S₂ : TwoSiteStandardFormData W₂ u v) :
    tensorOfHalves (stackRight 1 0 S₁.X₁ S₂.X₁) (stackLeft 1 0 S₁.X₂ S₂.X₂) u =
      padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _) := by
  funext ⟨i, j⟩
  ext α γ
  rw [padBond_apply]
  induction α using Fin.addCases with
  | left a =>
    induction γ using Fin.addCases with
    | left g => simp [tensorOfHalves, stackRight, stackLeft, S₁.W_apply]
    | right g => simp [tensorOfHalves, stackRight, stackLeft]
  | right a => simp [tensorOfHalves, stackRight, stackLeft]

/-- The relabelling of \(\{1,\ldots,D_1+D_2\}\) exchanging the first \(D_1\) and
the last \(D_2\) coordinates. -/
def stackFlip (D₁ D₂ : ℕ) : Fin (D₁ + D₂) ≃ Fin (D₁ + D₂) :=
  finAddFlip.trans (finCongr (Nat.add_comm D₂ D₁))

/-- At \(\theta=\pi/2\) the stacked tensor is the second tensor with unused bond
directions adjoined, after exchanging the two groups of bond coordinates. -/
theorem TwoSiteStandardFormData.tensorOfHalves_stack_zero_one
    (S₁ : TwoSiteStandardFormData W₁ u v) (S₂ : TwoSiteStandardFormData W₂ u v) :
    tensorOfHalves (stackRight 0 1 S₁.X₁ S₂.X₁) (stackLeft 0 1 S₁.X₂ S₂.X₂) u =
      bondReindex (stackFlip D₁ D₂) (padBond W₂ (D₁ + D₂) (Nat.le_add_left _ _)) := by
  funext ⟨i, j⟩
  ext α γ
  simp only [bondReindex, Matrix.submatrix_apply]
  rw [padBond_apply]
  induction α using Fin.addCases with
  | left a => simp [tensorOfHalves, stackRight, stackLeft, stackFlip]
  | right a =>
    induction γ using Fin.addCases with
    | left g => simp [tensorOfHalves, stackRight, stackLeft, stackFlip]
    | right g => simp [tensorOfHalves, stackRight, stackLeft, stackFlip, S₂.W_apply]

end Endpoints

section Path

variable {T : Type*} [TopologicalSpace T]

/-- Stacking right half factors is continuous in the coefficients. -/
theorem continuous_stackRight {c s : T → ℂ} (hc : Continuous c) (hs : Continuous s)
    (Y : Matrix (Fin d × Fin D₁) (Fin r) ℂ) (Y' : Matrix (Fin d × Fin D₂) (Fin r) ℂ) :
    Continuous fun t ↦ stackRight (c t) (s t) Y Y' := by
  refine continuous_pi fun p ↦ continuous_pi fun t' ↦ ?_
  obtain ⟨i, β⟩ := p
  induction β using Fin.addCases with
  | left b =>
    simp only [stackRight, Fin.addCases_left]
    exact hc.mul continuous_const
  | right b =>
    simp only [stackRight, Fin.addCases_right]
    exact hs.mul continuous_const

/-- Stacking left half factors is continuous in the coefficients. -/
theorem continuous_stackLeft {c s : T → ℂ} (hc : Continuous c) (hs : Continuous s)
    (Y : Matrix (Fin D₁ × Fin d) (Fin ℓ) ℂ) (Y' : Matrix (Fin D₂ × Fin d) (Fin ℓ) ℂ) :
    Continuous fun t ↦ stackLeft (c t) (s t) Y Y' := by
  refine continuous_pi fun p ↦ continuous_pi fun t' ↦ ?_
  obtain ⟨β, i⟩ := p
  induction β using Fin.addCases with
  | left b =>
    simp only [stackLeft, Fin.addCases_left]
    exact hc.mul continuous_const
  | right b =>
    simp only [stackLeft, Fin.addCases_right]
    exact hs.mul continuous_const

/-- The tensor of half factors is continuous in the half factors. -/
theorem continuous_tensorOfHalves {X₁ : T → Matrix (Fin d × Fin D) (Fin r) ℂ}
    {X₂ : T → Matrix (Fin D × Fin d) (Fin ℓ) ℂ} (h₁ : Continuous X₁) (h₂ : Continuous X₂)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) :
    Continuous fun t ↦ tensorOfHalves (X₁ t) (X₂ t) u := by
  unfold tensorOfHalves
  fun_prop

end Path

/-- The tensors of bond dimension `D` with the periodic operators of `W` at
every positive length. -/
def SameMPOSet (W : MPOTensor d D) : Set (MPOTensor d D) :=
  {X | ∀ N : ℕ, 0 < N → mpo X N = mpo W N}

/-- A virtual gauge is joined to the tensor through tensors with the same
periodic operators. Source: the gauge freedom of arXiv:1703.09188, lines 294
and 356. -/
theorem joinedIn_sameMPOSet_virtualSandwich (W : MPOTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) :
    JoinedIn (SameMPOSet W) W (MPOTensor.virtualSandwich X W X⁻¹) := by
  obtain ⟨γ, hγ⟩ := Matrix.joinedIn_isUnit_det_one hX
  have hdet : ∀ t, (γ t).det ≠ 0 := fun t ↦ (hγ t).ne_zero
  have hinv : Continuous fun t ↦ (γ t)⁻¹ := by
    simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
    exact ((γ.continuous.matrix_det).inv₀ hdet).smul γ.continuous.matrix_adjugate
  have hcont : Continuous fun t ↦ MPOTensor.virtualSandwich (γ t) W (γ t)⁻¹ := by
    refine continuous_pi fun ⟨i, j⟩ ↦ ?_
    simp only [virtualSandwich_apply]
    exact (γ.continuous.matrix_mul continuous_const).matrix_mul hinv
  refine ⟨⟨⟨fun t ↦ MPOTensor.virtualSandwich (γ t) W (γ t)⁻¹, hcont⟩, ?_, ?_⟩, fun t ↦ ?_⟩
  · funext ⟨i, j⟩
    simp
  · simp
  · intro N _
    exact mpo_virtualSandwich _ W _ (Matrix.nonsing_inv_mul _ (hγ t)) N

/-- A bond relabelling is joined to the tensor through tensors with the same
periodic operators. -/
theorem joinedIn_sameMPOSet_bondReindex (W : MPOTensor d D) (σ : Fin D ≃ Fin D) :
    JoinedIn (SameMPOSet W) W (bondReindex σ W) := by
  set P : Matrix (Fin D) (Fin D) ℂ := σ.toPEquiv.toMatrix
  set Q : Matrix (Fin D) (Fin D) ℂ := σ.symm.toPEquiv.toMatrix
  have hQP : Q * P = 1 := by
    ext a b
    simp [Q, P, PEquiv.mul_toMatrix_toPEquiv, Matrix.one_apply, PEquiv.toMatrix_apply]
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hdet : IsUnit P.det :=
    (Matrix.isUnit_iff_isUnit_det P).mp ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩
  have hinv : P⁻¹ = Q := Matrix.inv_eq_right_inv hPQ
  have hEq : bondReindex σ W = MPOTensor.virtualSandwich P W P⁻¹ := by
    funext i j
    rw [hinv, virtualSandwich_apply, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    simp [bondReindex]
  rw [hEq]
  exact joinedIn_sameMPOSet_virtualSandwich W hdet

/-- Two standard forms with the same gates have the same periodic operators at
every positive length. Source: arXiv:1703.09188, equation `StandardForm`,
lines 603--617. -/
theorem TwoSiteStandardFormData.mpo_eq_of_same_gates {W₁ : MPOTensor (d * d) D₁}
    {W₂ : MPOTensor (d * d) D₂}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData W₁ u v) (S₂ : TwoSiteStandardFormData W₂ u v)
    (N : ℕ) (hN : 0 < N) : mpo W₁ N = mpo W₂ N := by
  have : NeZero N := ⟨hN.ne'⟩
  have h₁ := TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := N) W₁ u v S₁
  have h₂ := TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := N) W₂ u v S₂
  exact (Matrix.reindex _ _).injective (h₁.trans h₂.symm)

/-- **Two standard forms with the same gates are joined through tensors with
the same periodic operators**, after adjoining unused bond directions: the
path interpolates the half factors of the two presentations. Source:
arXiv:1703.09188, equation `StandardForm`, lines 603--617, and the proof of
Theorem `IndexTh` (iv), lines 857--865. -/
theorem TwoSiteStandardFormData.joinedIn_sameMPOSet_padBond {W₁ : MPOTensor (d * d) D₁}
    {W₂ : MPOTensor (d * d) D₂}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData W₁ u v) (S₂ : TwoSiteStandardFormData W₂ u v) :
    JoinedIn (SameMPOSet (padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _)))
      (padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _))
      (padBond W₂ (D₁ + D₂) (Nat.le_add_left _ _)) := by
  let c : unitInterval → ℂ := fun t ↦ Complex.cos ((Real.pi / 2 * t : ℝ) : ℂ)
  let s : unitInterval → ℂ := fun t ↦ Complex.sin ((Real.pi / 2 * t : ℝ) : ℂ)
  have hc : Continuous c := by fun_prop
  have hs : Continuous s := by fun_prop
  let F : unitInterval → MPOTensor (d * d) (D₁ + D₂) := fun t ↦
    tensorOfHalves (stackRight (c t) (s t) S₁.X₁ S₂.X₁) (stackLeft (c t) (s t) S₁.X₂ S₂.X₂) u
  have hF : Continuous F :=
    continuous_tensorOfHalves (continuous_stackRight hc hs _ _)
      (continuous_stackLeft hc hs _ _) u
  have h0 : F 0 = padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _) := by
    rw [← S₁.tensorOfHalves_stack_one_zero S₂]
    simp [F, c, s]
  have h1 : F 1 = bondReindex (stackFlip D₁ D₂) (padBond W₂ (D₁ + D₂) (Nat.le_add_left _ _)) := by
    rw [← S₁.tensorOfHalves_stack_zero_one S₂]
    simp [F, c, s]
  have hSt : ∀ t, TwoSiteStandardFormData (F t) u v := fun t ↦
    S₁.stack S₂ (c t) (s t) (Complex.cos_sq_add_sin_sq _)
  have hpath : JoinedIn (SameMPOSet (padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _)))
      (padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _))
      (bondReindex (stackFlip D₁ D₂) (padBond W₂ (D₁ + D₂) (Nat.le_add_left _ _))) := by
    refine ⟨⟨⟨F, hF⟩, h0, h1⟩, fun t N hN ↦ ?_⟩
    change mpo (F t) N = _
    have h := (hSt t).mpo_eq_of_same_gates (hSt 0) N hN
    rwa [h0] at h
  have hW₂ : padBond W₂ (D₁ + D₂) (Nat.le_add_left _ _) ∈
      SameMPOSet (padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _)) := by
    intro N hN
    have : NeZero N := ⟨hN.ne'⟩
    rw [mpo_padBond, mpo_padBond]
    exact S₂.mpo_eq_of_same_gates S₁ N hN
  have hflip := (joinedIn_sameMPOSet_bondReindex
    (padBond W₂ (D₁ + D₂) (Nat.le_add_left _ _)) (stackFlip D₁ D₂)).symm
  refine hpath.trans (hflip.mono fun X hX N hN ↦ ?_)
  rw [hX N hN]
  exact hW₂ N hN

/-- **Two standard-form presentations with the same gates are joined through
MPU tensors.** If \(W_1\) and \(W_2\), of bond dimensions \(D_1\) and \(D_2\),
are presented in standard form with the same unitary gates, then after
adjoining unused bond directions up to \(D_1+D_2\) they are joined by a path of
tensors each generating an MPU.

Source: arXiv:1703.09188, equation `StandardForm`, lines 603--617; this is the
step from the gates to the tensors in the proof of Theorem `IndexTh` (iv),
lines 857--865. -/
theorem TwoSiteStandardFormData.joinedIn_padBond {W₁ : MPOTensor (d * d) D₁}
    {W₂ : MPOTensor (d * d) D₂}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData W₁ u v) (S₂ : TwoSiteStandardFormData W₂ u v) :
    JoinedIn {X : MPOTensor (d * d) (D₁ + D₂) | IsMPU X}
      (padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _))
      (padBond W₂ (D₁ + D₂) (Nat.le_add_left _ _)) := by
  have hW₁ : IsMPU (padBond W₁ (D₁ + D₂) (Nat.le_add_right _ _)) :=
    (TwoSiteStandardFormData.isMPU W₁ u v S₁).padBond _ _
  refine (S₁.joinedIn_sameMPOSet_padBond S₂).mono fun X hX N hN ↦ ?_
  rw [hX N (by omega)]
  exact hW₁ N hN

end MPOTensor
