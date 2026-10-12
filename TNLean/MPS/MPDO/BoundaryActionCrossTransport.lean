/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionLMatrix
import TNLean.MPS.MPDO.BoundaryActionTreeEntries

/-!
# Rectangular transport between endpoint action trees

The actual L matrix carries sequential synthesis to fusion-then-action
synthesis. Together with its analysis equation, equality of the two
endpoints' raw L matrices implies equality of the cross-endpoint tree
contractions against every rectangular matrix.

The endpoint states have one block, represented by `Fin 1`, and may have
different physical and bond dimensions. The fusion and action multiplicities
are common. All fusion and action maps are actual exact biorthogonal
decompositions. No inverse L matrix, common F matrix, operator injectivity,
or assumed tree-contraction equality is used.

This is the local contraction needed for the mixed endpoint operator's
cross sectors. It does not construct that operator's fusion maps or identify
gauge-class equality with equality of the chosen raw L matrices.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
  `eq:F_symbol2`, and `1Fsymbol`, lines 491--552; mixed endpoint fusion,
  `REsubmission.tex`, lines 1667--1685.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

section Synthesis

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
  (hNormal : ∀ y, Kraus.IsNormal (A y)) (hD : ∀ y, 0 < D y)

include hF hA hNormal hD in
/-- Sequential synthesis composed with the actual L matrix is
fusion-then-action synthesis. Source: GLM23 `eq:F_symbol2` and `1Fsymbol`.
The common support is derived from exact decompositions and a positive
simultaneous word span. -/
theorem actionLMatrix_synthesis (a b : Fin r) (x : Fin s)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    (MPSTensor.decompositionSynthesis (sequentialActionSynthesis WA a b x)).submatrix
        id (sequentialActionCoordinateEquiv (D := D) a b x) *
      Matrix.blockDiagonal' (fun y ↦ actionLMatrix WF VA WA a b x y ⊗ₖ
        (1 : Matrix (Fin (D y)) (Fin (D y)) ℂ)) =
      (MPSTensor.decompositionSynthesis (fusionThenActionSynthesis WF WA a b x)).submatrix
        id (fusionActionCoordinateEquiv (D := D) a b x) := by
  rw [← fusionToSequentialComparison_eq_blockDiagonal VF WF VA WA hF hA hNormal hD
      a b x hSpan, Matrix.submatrix_mul_equiv]
  exact congrArg
    (fun Z ↦ Z.submatrix id (fusionActionCoordinateEquiv (D := D) (N := N) (M := M) a b x))
    (fullActionComparison_spec VF WF VA WA hF hA a b x hL hSpan).2.2.1

end Synthesis

section SingleState

variable {d r D : ℕ} {χ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a, Fin (m a) → Matrix (Fin D) (Fin (χ a * D)) ℂ)
  (WA : ∀ a, Fin (m a) → Matrix (Fin (χ a * D)) (Fin D) ℂ)
  {O : ∀ a, MPOTensor d (χ a)} {A : MPSTensor d D}
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a, MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) A)
    (fun _ : Fin (m a) ↦ A) (VA a) (WA a))
  (hInj : Kraus.IsInjective A) (hD : 0 < D)

include hF hA hInj hD in
/-- The two individual L relations for a single injective state block.
The `Fin 1` state labels specialize the existing actual action trees;
positive simultaneous spanning and block separation are derived internally.
Source: GLM23 `eq:F_symbol2`, `1Fsymbol`, and lines 1667--1685. -/
theorem singleState_actionLMatrix_relations (a b : Fin r) :
    (∀ p : SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
      ∑ q : FusionActionMultiplicity N (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
        actionLMatrix WF (fun a _ _ ↦ VA a) (fun a _ _ ↦ WA a) a b 0 0 p q •
          fusionThenActionAnalysis VF (fun a _ _ ↦ VA a) a b 0
            (fusionActionPathEquiv a b 0 ⟨0, q⟩) =
        sequentialActionAnalysis (fun a _ _ ↦ VA a) a b 0
          (sequentialActionPathEquiv a b 0 ⟨0, p⟩)) ∧
    (∀ q : FusionActionMultiplicity N (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
      ∑ p : SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
        actionLMatrix WF (fun a _ _ ↦ VA a) (fun a _ _ ↦ WA a) a b 0 0 p q •
          sequentialActionSynthesis (fun a _ _ ↦ WA a) a b 0
            (sequentialActionPathEquiv a b 0 ⟨0, p⟩) =
        fusionThenActionSynthesis WF (fun a _ _ ↦ WA a) a b 0
          (fusionActionPathEquiv a b 0 ⟨0, q⟩)) := by
  have hAction : ∀ a (x : Fin 1),
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) A)
        (fun _ : (y : Fin 1) × Fin (m a) ↦ A)
        (fun q ↦ VA a q.2) (fun q ↦ WA a q.2) := by
    intro a _
    exact (hA a).reindex
      { toFun := fun q : (y : Fin 1) × Fin (m a) ↦ q.2
        invFun := fun i ↦ ⟨0, i⟩
        left_inv := by
          rintro ⟨y, i⟩
          have hy : y = 0 := Subsingleton.elim _ _
          subst y
          rfl
        right_inv := fun _ ↦ rfl }
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective
      (B := fun _ : Fin 1 ↦ A) (fun _ ↦ hInj) (fun _ ↦ hD)
      (fun y z hyz ↦ (hyz (Subsingleton.elim _ _)).elim)
  constructor
  · intro p
    ext u v
    have h := congrArg (fun Z ↦ Z ⟨0, p, u⟩ v)
      (actionLMatrix_analysis VF WF (fun a _ _ ↦ VA a) (fun a _ _ ↦ WA a)
        hF hAction (fun _ ↦ hInj.isNormal) (fun _ ↦ hD) a b 0 hL hSpan)
    simpa [Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_prod_type,
      MPSTensor.decompositionAnalysis, fusionActionCoordinateEquiv,
      sequentialActionCoordinateEquiv, Matrix.kroneckerMap_apply, Matrix.one_apply,
      mul_ite, ite_mul, Matrix.sum_apply, Matrix.smul_apply, mul_assoc] using h
  · intro q
    ext u v
    have h := congrArg (fun Z ↦ Z u ⟨0, q, v⟩)
      (actionLMatrix_synthesis VF WF (fun a _ _ ↦ VA a) (fun a _ _ ↦ WA a)
        hF hAction (fun _ ↦ hInj.isNormal) (fun _ ↦ hD) a b 0 hL hSpan)
    have hentry :
        (∑ p : SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
          sequentialActionSynthesis (fun a _ _ ↦ WA a) a b 0
              (sequentialActionPathEquiv a b 0 ⟨0, p⟩) u v *
            actionLMatrix WF (fun a _ _ ↦ VA a) (fun a _ _ ↦ WA a) a b 0 0 p q) =
          fusionThenActionSynthesis WF (fun a _ _ ↦ WA a) a b 0
            (fusionActionPathEquiv a b 0 ⟨0, q⟩) u v := by
      simpa [Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_prod_type,
        MPSTensor.decompositionSynthesis, fusionActionCoordinateEquiv,
        sequentialActionCoordinateEquiv, Matrix.kroneckerMap_apply, Matrix.one_apply,
        mul_ite, ite_mul] using h
    rw [← hentry]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun p _ ↦ mul_comm _ _)

end SingleState

section CrossEndpoint

variable {d₀ d₁ r D₀ D₁ : ℕ} {χ₀ χ₁ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (VF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a, Fin (m a) → Matrix (Fin D₀) (Fin (χ₀ a * D₀)) ℂ)
  (WA₀ : ∀ a, Fin (m a) → Matrix (Fin (χ₀ a * D₀)) (Fin D₀) ℂ)
  (VF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a, Fin (m a) → Matrix (Fin D₁) (Fin (χ₁ a * D₁)) ℂ)
  (WA₁ : ∀ a, Fin (m a) → Matrix (Fin (χ₁ a * D₁)) (Fin D₁) ℂ)
  {O₀ : ∀ a, MPOTensor d₀ (χ₀ a)} {A₀ : MPSTensor d₀ D₀}
  {O₁ : ∀ a, MPOTensor d₁ (χ₁ a)} {A₁ : MPSTensor d₁ D₁}
  (hF₀ : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O₀ a) (O₀ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₀ q.1).toMPSTensor)
      (fun q ↦ VF₀ a b q.1 q.2) (fun q ↦ WF₀ a b q.1 q.2))
  (hA₀ : ∀ a, MPSTensor.IsBiorthogonalDecomposition (actTensor (O₀ a) A₀)
    (fun _ : Fin (m a) ↦ A₀) (VA₀ a) (WA₀ a))
  (hF₁ : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O₁ a) (O₁ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₁ q.1).toMPSTensor)
      (fun q ↦ VF₁ a b q.1 q.2) (fun q ↦ WF₁ a b q.1 q.2))
  (hA₁ : ∀ a, MPSTensor.IsBiorthogonalDecomposition (actTensor (O₁ a) A₁)
    (fun _ : Fin (m a) ↦ A₁) (VA₁ a) (WA₁ a))
  (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
  (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- Equal actual raw L matrices identify the two endpoint-crossed tree
contractions for every rectangular final-bond matrix. The analysis equation
at endpoint one transfers its scalar coefficients to the synthesis equation
at endpoint zero. Source: GLM23, `REsubmission.tex`, lines 1667--1685, using
`eq:F_symbol2` at lines 491--552. No common F matrix or operator injectivity
is needed for this local step. -/
theorem crossEndpoint_actionTree_contraction_of_actionLMatrix_eq
    (a b : Fin r)
    (hL : actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0)
    (X : Matrix (Fin D₀) (Fin D₁) ℂ) :
    (∑ p : SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
      sequentialActionSynthesis (fun a _ _ ↦ WA₀ a) a b 0
          (sequentialActionPathEquiv a b 0 ⟨0, p⟩) * X *
        sequentialActionAnalysis (fun a _ _ ↦ VA₁ a) a b 0
          (sequentialActionPathEquiv a b 0 ⟨0, p⟩)) =
    ∑ q : FusionActionMultiplicity N (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
      fusionThenActionSynthesis WF₀ (fun a _ _ ↦ WA₀ a) a b 0
          (fusionActionPathEquiv a b 0 ⟨0, q⟩) * X *
        fusionThenActionAnalysis VF₁ (fun a _ _ ↦ VA₁ a) a b 0
          (fusionActionPathEquiv a b 0 ⟨0, q⟩) := by
  have hS := (singleState_actionLMatrix_relations VF₀ WF₀ VA₀ WA₀
    hF₀ hA₀ hInj₀ hD₀ a b).2
  have hH := (singleState_actionLMatrix_relations VF₁ WF₁ VA₁ WA₁
    hF₁ hA₁ hInj₁ hD₁ a b).1
  calc
    _ = ∑ p : SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
        sequentialActionSynthesis (fun a _ _ ↦ WA₀ a) a b 0
            (sequentialActionPathEquiv a b 0 ⟨0, p⟩) * X *
          (∑ q : FusionActionMultiplicity N (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
            actionLMatrix WF₁ (fun a _ _ ↦ VA₁ a) (fun a _ _ ↦ WA₁ a) a b 0 0 p q •
              fusionThenActionAnalysis VF₁ (fun a _ _ ↦ VA₁ a) a b 0
                (fusionActionPathEquiv a b 0 ⟨0, q⟩)) := by simp_rw [hH]
    _ = ∑ q : FusionActionMultiplicity N (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
        (∑ p : SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
          actionLMatrix WF₀ (fun a _ _ ↦ VA₀ a) (fun a _ _ ↦ WA₀ a) a b 0 0 p q •
            sequentialActionSynthesis (fun a _ _ ↦ WA₀ a) a b 0
              (sequentialActionPathEquiv a b 0 ⟨0, p⟩)) * X *
          fusionThenActionAnalysis VF₁ (fun a _ _ ↦ VA₁ a) a b 0
            (fusionActionPathEquiv a b 0 ⟨0, q⟩) := by
      simp_rw [Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_mul, Matrix.smul_mul, hL]
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [hS]

private theorem sum_rectangular_sandwich_apply
    {ι α β γ δ : Type*} [Fintype ι] [Fintype β] [Fintype γ]
    (S : ι → Matrix α β ℂ) (X : Matrix β γ ℂ) (H : ι → Matrix γ δ ℂ)
    (x : α) (y : δ) :
    (∑ i, S i * X * H i) x y = ∑ i, ∑ u, ∑ v, S i x u * X u v * H i v y := by
  simp only [Matrix.sum_apply, Matrix.mul_assoc, Matrix.mul_apply,
    Finset.mul_sum, mul_assoc]

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- The same cross-endpoint contraction in the physical leg coordinates
used by the mixed operator construction. Only the intermediate state and
operator bonds remain summed. Source: GLM23, lines 1667--1685. -/
theorem crossEndpoint_actionTree_contraction_apply_of_actionLMatrix_eq
    (a b : Fin r)
    (hL : actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0)
    (X : Matrix (Fin D₀) (Fin D₁) ℂ)
    (xa₀ : Fin (χ₀ a)) (xb₀ : Fin (χ₀ b)) (x₀ : Fin D₀)
    (xa₁ : Fin (χ₁ a)) (xb₁ : Fin (χ₁ b)) (x₁ : Fin D₁) :
    (∑ i : Fin (m a), ∑ j : Fin (m b), ∑ u : Fin D₀, ∑ v : Fin D₁,
      (∑ t : Fin D₀,
        WA₀ b j (finProdFinEquiv (xb₀, x₀)) t *
          WA₀ a i (finProdFinEquiv (xa₀, t)) u) * X u v *
      (∑ t : Fin D₁,
        VA₁ a i v (finProdFinEquiv (xa₁, t)) *
          VA₁ b j t (finProdFinEquiv (xb₁, x₁)))) =
    ∑ c : Fin r, ∑ k : Fin (m c), ∑ mu : Fin (N a b c),
      ∑ u : Fin D₀, ∑ v : Fin D₁,
        (∑ t : Fin (χ₀ c),
          WF₀ a b c mu (finProdFinEquiv (xa₀, xb₀)) t *
            WA₀ c k (finProdFinEquiv (t, x₀)) u) * X u v *
        (∑ t : Fin (χ₁ c),
          VA₁ c k v (finProdFinEquiv (t, x₁)) *
            VF₁ a b c mu t (finProdFinEquiv (xa₁, xb₁))) := by
  have h := congrArg
    (fun Z ↦ Z (finProdFinEquiv (finProdFinEquiv (xa₀, xb₀), x₀))
      (finProdFinEquiv (finProdFinEquiv (xa₁, xb₁), x₁)))
    (crossEndpoint_actionTree_contraction_of_actionLMatrix_eq
      VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁ hF₀ hA₀ hF₁ hA₁
      hInj₀ hInj₁ hD₀ hD₁ a b hL X)
  rw [sum_rectangular_sandwich_apply, sum_rectangular_sandwich_apply] at h
  simpa only [Fintype.sum_sigma, Fin.sum_univ_one, Fintype.sum_prod_type,
    sequentialActionPathEquiv, fusionActionPathEquiv, Equiv.coe_fn_mk,
    sequentialActionSynthesis_apply, sequentialActionAnalysis_apply,
    fusionThenActionSynthesis_apply, fusionThenActionAnalysis_apply] using h

end CrossEndpoint

end MPOTensor
