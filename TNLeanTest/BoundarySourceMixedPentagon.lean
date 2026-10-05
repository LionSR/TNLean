import TNLean.MPS.MPDO.BoundarySourceMixedPentagon

/-!
# Source mixed-pentagon regressions

The examples retain the exact decomposition hypotheses and actual coefficient
contractions. Guarded axiom reports check the source capstones and their dependencies.
-/

open scoped Matrix BigOperators

set_option linter.hashCommand false

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

example
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
  exact actionLMatrix_mixed_pentagon O A hInjO hInjA hχ hD hneO hneA
    VF WF VA WA hF hA a b c e f x y z t i j k m mu nu

example
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
  exact IsBoundaryCompatible.exists_exact_mixed_pentagon
    hClosed hCompatible O A hT hB hInjO hInjA hχ hD hneO hneA

-- The intermediate theorem retains every exact-family construction input.
example {p r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
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
  exact triangular_actionLMatrix_mixed_pentagon VF WF VA WA hD hT hVW K hK
    a b c e f x y z t i j k m mu nu

end MPOTensor

/-- info:
'MPOTensor.triangular_inversePrintedFMatrix_eq_fusionFMatrix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.triangular_inversePrintedFMatrix_eq_fusionFMatrix

/-- info:
'MPOTensor.triangular_actionLMatrix_mixed_pentagon'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.triangular_actionLMatrix_mixed_pentagon

/-- info:
'MPOTensor.actionLMatrix_mixed_pentagon'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.actionLMatrix_mixed_pentagon

/-- info:
'MPOTensor.IsBoundaryCompatible.exists_exact_mixed_pentagon'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.exists_exact_mixed_pentagon
