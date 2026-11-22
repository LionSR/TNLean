/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.MPOAction.TriangularBoundaryDecomposition
import TNLean.MPS.Operator.Fusion.BoundaryZipper
import TNLean.MPS.Operator.BoundaryActionTreeEntries
import TNLean.MPS.FundamentalTheorem.Zipper.BoundaryActionLMatrix
import TNLean.MPS.Operator.Fusion.CompleteZipperFusionTrace
import TNLean.MPS.Operator.Fusion.BoundaryFusionFMatrix
import TNLean.MPS.Operator.Fusion.CompleteZipperFusionMixedOrientation
import TNLean.MPS.MPDO.MPOAction.TriangularBoundaryBlocked

/-!
# The auxiliary fusion comparison is the actual action L matrix

This is an algebraic identification of constructed matrices, not a premise
of coherence. Whenever the triangular fusion/action matrices form a complete
zipper family, its forward comparison on two operator labels and one state
label is exactly the normalized-trace L matrix of the original action trees.
The physical alphabet and letters may already have been commonly blocked;
only the unchanged virtual analysis and synthesis maps enter the proof.

The row order of the auxiliary comparison is `(z,j,i)`, whereas the action
L matrix uses `(z,i,j)`. Its column order is `(c,mu,k)`, whereas L uses
`(c,k,mu)`. Neither reordering reverses the comparison: both sides are the
sequential analysis followed by fusion-then-action synthesis.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3,
`eq:F_symbol2` and `1Fsymbol`, lines 517--552.

## Mixed pentagon of the actual fusion and action coefficients

The auxiliary operator-only inverse comparison is the original fusion F
contraction. Combined with the proved auxiliary P=L identification, its
ordinary fourfold coherence gives the coupled pentagon of the actual maps.
No mixed-pentagon, module-category, unit, or duality field is assumed.

The constructor hypotheses in this intermediate module concern the exact
auxiliary family at a suitable physical blocking. The source wrapper derives
that family from the original separated injective operator and state blocks.

**Local fix (multiplicity indices):** The fusion entry has row `(d,eta,chi)`
and column `(f,mu,nu)`. GLM23 reverses both multiplicity pairs in the printed
coupled pentagon. See `docs/paper-gaps/glm23_multiplicity_l_indices.tex`.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `coupledpent`,
lines 554--562, and `Fsymbolsdef`.

## Source-derived multiplicity mixed pentagon

The exact unblocked fusion and action matrices satisfy the coupled pentagon.
Common positive blocking is used only to obtain the simultaneous inverse of
an auxiliary triangular operator family; it does not change any coefficient.
The final theorem derives those exact maps from arbitrary-boundary operator
closedness and operator/state compatibility, together with individually
injective, positive-dimensional, scalar-gauge-separated blocks.

No simultaneous word span, ambient support completeness, semisimple module
structure, unit, duality, or coherence equation is added to the source inputs.
The F coefficient is the actual analysis-oriented fusion contraction and L
is the actual sequential-analysis/fusion-synthesis contraction.

**Local fix (multiplicity indices):** The F factor uses upper `(d,eta,chi)`
and lower `(f,mu,nu)`, correcting both reversed pairs in the source display.
See `docs/paper-gaps/glm23_multiplicity_l_indices.tex`.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `algcond`,
`eq:compatible`, `Fsymbolsdef`, `eq:F_symbol2`, `coupledpent`, and Appendix A.
-/

section

open scoped Matrix BigOperators

namespace MPOTensor

variable {p r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  {T : ∀ q : Fin r ⊕ Fin s, MPOTensor p (triangularBondDim χ D q)}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  (hD : ∀ q, 0 < triangularBondDim χ D q)
  (hT : ∀ q, Kraus.IsInjective (T q).toMPSTensor)
  (hVW : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin r ⊕ Fin s) × Fin (triangularFusionMultiplicity N M a b c) ↦
        (T q.1).toMPSTensor)
      (fun q ↦ triangularFusionAnalysis VF VA a b q.1 q.2)
      (fun q ↦ triangularFusionSynthesis WF WA a b q.1 q.2))
  (K : Matrix ((c : Fin r ⊕ Fin s) ×
    (Fin (triangularBondDim χ D c) × Fin (triangularBondDim χ D c)))
      (Fin p × Fin p) ℂ)
  (hK : ∀ (c d : Fin r ⊕ Fin s)
    (x y : Fin (triangularBondDim χ D c)) (x' y' : Fin (triangularBondDim χ D d)),
    (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
      if he : c = d then
        if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
      else 0)

local notation "F" => CompleteZipperFusionFamily.ofBiorthogonal hD hT
  (triangularFusionAnalysis VF VA) (triangularFusionSynthesis WF WA) hVW K hK

/-- The auxiliary forward F comparison is literally the original action L
matrix, with the source multiplicity orders restored. This assertion is
independent of the physical blocking used to obtain the complete family. -/
theorem triangular_printedFMatrix_eq_actionLMatrix
    (a b c : Fin r) (x y z : Fin s)
    (i : Fin (M a z y)) (j : Fin (M b x z))
    (k : Fin (M c x y)) (mu : Fin (N a b c)) :
    (F).printedFMatrix (.inl a) (.inl b) (.inr x) (.inr y)
        ⟨.inr z, j, i⟩ ⟨.inl c, mu, k⟩ =
      actionLMatrix WF VA WA a b x y ⟨z, i, j⟩ ⟨c, k, mu⟩ := by
  classical
  rw [(F).printedFMatrix_eq_inv_dim_mul_trace]
  change (D y : ℂ)⁻¹ * Matrix.trace _ = (D y : ℂ)⁻¹ * Matrix.trace
    (sequentialActionAnalysis VA a b x ⟨⟨z, j⟩, y, i⟩ *
      fusionThenActionSynthesis WF WA a b x ⟨⟨c, mu⟩, y, k⟩)
  congr 1
  congr 1
  ext u v
  change Fin (D y) at u v
  simp only [Matrix.mul_apply]
  refine Fintype.sum_equiv
    ((Equiv.prodCongr (finProdFinEquiv : Fin (χ a) × Fin (χ b) ≃ Fin (χ a * χ b))
      (Equiv.refl (Fin (D x)))).trans finProdFinEquiv) _ _ ?_
  rintro ⟨⟨xa, xb⟩, xx⟩
  change
    (∑ t : Fin (D z),
      VA a z y i u (finProdFinEquiv (xa, t)) *
        VA b x z j t (finProdFinEquiv (xb, xx))) *
      (∑ t : Fin (χ c),
        WF a b c mu (finProdFinEquiv (xa, xb)) t *
          WA c x y k (finProdFinEquiv (t, xx)) v) =
    sequentialActionAnalysis VA a b x ⟨⟨z, j⟩, y, i⟩ u
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) *
      fusionThenActionSynthesis WF WA a b x ⟨⟨c, mu⟩, y, k⟩
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) v
  exact congrArg₂ (· * ·)
    (sequentialActionAnalysis_apply VA a b x y z i j xa xb xx u).symm
    (fusionThenActionSynthesis_apply WF WA a b c x y mu k xa xb xx v).symm

end MPOTensor

end

section

open scoped Matrix BigOperators

namespace MPOTensor

variable {p r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  {T : ∀ q : Fin r ⊕ Fin s, MPOTensor p (triangularBondDim χ D q)}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  (hD : ∀ q, 0 < triangularBondDim χ D q)
  (hT : ∀ q, Kraus.IsInjective (T q).toMPSTensor)
  (hVW : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin r ⊕ Fin s) × Fin (triangularFusionMultiplicity N M a b c) ↦
        (T q.1).toMPSTensor)
      (fun q ↦ triangularFusionAnalysis VF VA a b q.1 q.2)
      (fun q ↦ triangularFusionSynthesis WF WA a b q.1 q.2))
  (K : Matrix ((c : Fin r ⊕ Fin s) ×
    (Fin (triangularBondDim χ D c) × Fin (triangularBondDim χ D c)))
      (Fin p × Fin p) ℂ)
  (hK : ∀ (c d : Fin r ⊕ Fin s)
    (x y : Fin (triangularBondDim χ D c)) (x' y' : Fin (triangularBondDim χ D d)),
    (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
      if he : c = d then
        if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
      else 0)

local notation "F" => CompleteZipperFusionFamily.ofBiorthogonal hD hT
  (triangularFusionAnalysis VF VA) (triangularFusionSynthesis WF WA) hVW K hK

/-- The operator-only inverse comparison in the auxiliary family is the
actual source-oriented fusion coefficient of the original V/W maps. -/
theorem triangular_inversePrintedFMatrix_eq_fusionFMatrix
    (a b c d e f : Fin r)
    (mu : Fin (N a b e)) (nu : Fin (N e c d))
    (lambda : Fin (N b c f)) (sigma : Fin (N a f d)) :
    (F).inversePrintedFMatrix (.inl a) (.inl b) (.inl c) (.inl d)
        ⟨.inl e, mu, nu⟩ ⟨.inl f, lambda, sigma⟩ =
      fusionFMatrix VF WF a b c d ⟨e, mu, nu⟩ ⟨f, lambda, sigma⟩ := by
  rw [(F).inversePrintedFMatrix_eq_inv_dim_mul_trace]
  rfl

include hD hT hVW hK in
/-- The actual normalized-trace fusion/action coefficients obey the typed
GLM23 mixed pentagon. Both sides are derived from exact fourfold tree
comparison; every intermediate index runs over its actual multiplicity
space, which may be empty. Source: GLM23 `coupledpent`, with the corrected
fusion index order recorded above. -/
theorem triangular_actionLMatrix_mixed_pentagon
    (a b c e f : Fin r) (x y z t : Fin s)
    (i : Fin (M a z y)) (j : Fin (M b t z)) (k : Fin (M c x t))
    (m : Fin (M e x y)) (mu : Fin (N b c f)) (nu : Fin (N a f e)) :
    (∑ d : Fin r, ∑ n : Fin (M d t y),
      ∑ eta : Fin (N a b d), ∑ chi : Fin (N d c e),
        actionLMatrix WF VA WA a b t y ⟨z, i, j⟩ ⟨d, n, eta⟩ *
          actionLMatrix WF VA WA d c x y ⟨t, n, k⟩ ⟨e, m, chi⟩ *
          fusionFMatrix VF WF a b c e ⟨d, eta, chi⟩ ⟨f, mu, nu⟩) =
      ∑ l : Fin (M f x z),
        actionLMatrix WF VA WA b c x z ⟨t, j, k⟩ ⟨f, l, mu⟩ *
          actionLMatrix WF VA WA a f x y ⟨z, i, l⟩ ⟨e, m, nu⟩ := by
  classical
  have hP := triangular_printedFMatrix_eq_actionLMatrix VF WF VA WA hD hT hVW K hK
  have hQ := triangular_inversePrintedFMatrix_eq_fusionFMatrix VF WF VA WA hD hT hVW K hK
  let G (v : Fin r ⊕ Fin s) : ℂ :=
    ∑ n : Fin ((F).fusionMultiplicity v (.inr t) (.inr y)),
      ∑ eta : Fin ((F).fusionMultiplicity (.inl a) (.inl b) v),
      ∑ chi : Fin ((F).fusionMultiplicity v (.inl c) (.inl e)),
        (F).printedFMatrix (.inl a) (.inl b) (.inr t) (.inr y)
            ⟨.inr z, j, i⟩ ⟨v, eta, n⟩ *
          (F).printedFMatrix v (.inl c) (.inr x) (.inr y)
            ⟨.inr t, k, n⟩ ⟨.inl e, chi, m⟩ *
          (F).inversePrintedFMatrix (.inl a) (.inl b) (.inl c) (.inl e)
            ⟨v, eta, chi⟩ ⟨.inl f, mu, nu⟩
  let R (l : Fin (M f x z)) : ℂ :=
    (F).printedFMatrix (.inl b) (.inl c) (.inr x) (.inr z)
        ⟨.inr t, k, j⟩ ⟨.inl f, mu, l⟩ *
      (F).printedFMatrix (.inl a) (.inl f) (.inr x) (.inr y)
        ⟨.inr z, l, i⟩ ⟨.inl e, nu, m⟩
  have h : (∑ v : Fin r ⊕ Fin s, G v) = ∑ l : Fin (M f x z), R l :=
    (F).printedFMatrix_mixed_pentagon
      (.inl a) (.inl b) (.inl c) (.inr x) (.inr y)
      (.inl f) (.inl e) (.inr t) (.inr z) mu nu m k j i
  have hState (v : Fin s) : G (.inr v) = 0 := by
    dsimp only [G]
    exact Finset.sum_eq_zero fun n _ ↦ Fin.elim0 n
  have hOperator (v : Fin r) : G (.inl v) =
      ∑ n : Fin (M v t y), ∑ eta : Fin (N a b v), ∑ chi : Fin (N v c e),
        actionLMatrix WF VA WA a b t y ⟨z, i, j⟩ ⟨v, n, eta⟩ *
          actionLMatrix WF VA WA v c x y ⟨t, n, k⟩ ⟨e, m, chi⟩ *
          fusionFMatrix VF WF a b c e ⟨v, eta, chi⟩ ⟨f, mu, nu⟩ := by
    change (∑ n : Fin (M v t y), ∑ eta : Fin (N a b v), ∑ chi : Fin (N v c e),
      (F).printedFMatrix (.inl a) (.inl b) (.inr t) (.inr y)
          ⟨.inr z, j, i⟩ ⟨.inl v, eta, n⟩ *
        (F).printedFMatrix (.inl v) (.inl c) (.inr x) (.inr y)
          ⟨.inr t, k, n⟩ ⟨.inl e, chi, m⟩ *
        (F).inversePrintedFMatrix (.inl a) (.inl b) (.inl c) (.inl e)
          ⟨.inl v, eta, chi⟩ ⟨.inl f, mu, nu⟩) = _
    refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun eta _ ↦
      Finset.sum_congr rfl fun chi _ ↦ ?_
    exact congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (hP a b v t y z i j n eta) (hP v c e x y t n k m chi))
      (hQ a b c e v f eta chi mu nu)
  have hRight (l : Fin (M f x z)) : R l =
      actionLMatrix WF VA WA b c x z ⟨t, j, k⟩ ⟨f, l, mu⟩ *
        actionLMatrix WF VA WA a f x y ⟨z, i, l⟩ ⟨e, m, nu⟩ :=
    congrArg₂ (· * ·) (hP b c f x z t j k l mu) (hP a f e x y z i l m nu)
  calc
    _ = ∑ v : Fin r, G (.inl v) :=
      Finset.sum_congr rfl fun v _ ↦ (hOperator v).symm
    _ = ∑ v : Fin r ⊕ Fin s, G v := by
      rw [Fintype.sum_sum_type]
      simp only [hState, Finset.sum_const_zero, add_zero]
    _ = ∑ l : Fin (M f x z), R l := h
    _ = _ := Finset.sum_congr rfl fun l _ ↦ hRight l

end MPOTensor

end

section

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- Exact source fusion/action maps satisfy the actual coupled pentagon.
Individual injectivity and scalar-gauge separation derive the common
blocking needed in its proof; the conclusion uses the unblocked maps. -/
theorem actionLMatrix_mixed_pentagon
    (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor)
    (hInjA : ∀ x, Kraus.IsInjective (A x))
    (hχ : ∀ a, 0 < χ a) (hD : ∀ x, 0 < D x)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (hneA : MPSTensor.BlocksNotGaugePhaseEquiv A)
    (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (a b c e f : Fin r) (x y z t : Fin s)
    (i : Fin (M a z y)) (j : Fin (M b t z)) (k : Fin (M c x t))
    (m : Fin (M e x y)) (mu : Fin (N b c f)) (nu : Fin (N a f e)) :
    (∑ v : Fin r, ∑ n : Fin (M v t y),
      ∑ eta : Fin (N a b v), ∑ chi : Fin (N v c e),
        actionLMatrix WF VA WA a b t y ⟨z, i, j⟩ ⟨v, n, eta⟩ *
          actionLMatrix WF VA WA v c x y ⟨t, n, k⟩ ⟨e, m, chi⟩ *
          fusionFMatrix VF WF a b c e ⟨v, eta, chi⟩ ⟨f, mu, nu⟩) =
      ∑ l : Fin (M f x z),
        actionLMatrix WF VA WA b c x z ⟨t, j, k⟩ ⟨f, l, mu⟩ *
          actionLMatrix WF VA WA a f x y ⟨z, i, l⟩ ⟨e, m, nu⟩ := by
  classical
  obtain ⟨L, hL, hInj, K, hK⟩ :=
    exists_triangular_blockTensor_leftInverse O A hInjO hInjA hχ hD hneO hneA
  have hDim : ∀ q, 0 < triangularBondDim χ D q := by
    intro q
    cases q with
    | inl a => exact hχ a
    | inr x => exact hD x
  exact triangular_actionLMatrix_mixed_pentagon VF WF VA WA hDim hInj
    (fun a b ↦ (isBiorthogonalDecomposition_triangularTensor VF WF VA WA O A hF hA
      a b).blockMPO_fintype hL) K hK a b c e f x y z t i j k m mu nu

/-- Arbitrary-boundary closedness and compatibility construct exact fusion
and action maps whose actual normalized-trace coefficients satisfy GLM23's
typed coupled pentagon. There is no coherence or joint-span hypothesis. -/
theorem IsBoundaryCompatible.exists_exact_mixed_pentagon
    {T : MPOTensor d (∑ a : Fin r, χ a)}
    {B : MPSTensor d (∑ x : Fin s, D x)}
    (hClosed : IsBoundaryClosed T) (hCompatible : IsBoundaryCompatible T B)
    (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
    (hT : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun a ↦ (O a).toMPSTensor))
    (hB : B = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) A)
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor)
    (hInjA : ∀ x, Kraus.IsInjective (A x))
    (hχ : ∀ a, 0 < χ a) (hD : ∀ x, 0 < D x)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (hneA : MPSTensor.BlocksNotGaugePhaseEquiv A) :
    ∃ (N : Fin r → Fin r → Fin r → ℕ) (M : Fin r → Fin s → Fin s → ℕ)
      (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
      (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
      (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
      (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ),
      (∀ a b, MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2)) ∧
      (∀ a x, MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2)) ∧
      ∀ (a b c e f : Fin r) (x y z t : Fin s)
        (i : Fin (M a z y)) (j : Fin (M b t z)) (k : Fin (M c x t))
        (m : Fin (M e x y)) (mu : Fin (N b c f)) (nu : Fin (N a f e)),
        (∑ v : Fin r, ∑ n : Fin (M v t y),
          ∑ eta : Fin (N a b v), ∑ chi : Fin (N v c e),
            actionLMatrix WF VA WA a b t y ⟨z, i, j⟩ ⟨v, n, eta⟩ *
              actionLMatrix WF VA WA v c x y ⟨t, n, k⟩ ⟨e, m, chi⟩ *
              fusionFMatrix VF WF a b c e ⟨v, eta, chi⟩ ⟨f, mu, nu⟩) =
          ∑ l : Fin (M f x z),
            actionLMatrix WF VA WA b c x z ⟨t, j, k⟩ ⟨f, l, mu⟩ *
              actionLMatrix WF VA WA a f x y ⟨z, i, l⟩ ⟨e, m, nu⟩ := by
  classical
  choose N VF WF hF using fun a b ↦
    hClosed.exists_blockFusionDecomposition_of_isInjective O hT hInjO hχ hneO a b
  choose M VA WA hA using fun a x ↦
    hCompatible.exists_blockActionDecomposition_of_isInjective
      O A hT hB hInjA hD hneA a x
  exact ⟨N, M, VF, WF, VA, WA, hF, hA,
    actionLMatrix_mixed_pentagon O A hInjO hInjA hχ hD hneO hneA
      VF WF VA WA hF hA⟩

end MPOTensor

end
