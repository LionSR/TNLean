/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryTransport
import TNLean.MPS.MPDO.CompleteZipperFusionDefs

/-!
# Complete zipper tensors from exact boundary decompositions

Biorthogonal synthesis and analysis matrices reconstructing each product
letter satisfy both zipper equations. Collecting their multiplicity blocks
therefore gives a complete zipper fusion family whenever the target letters
have a simultaneous left inverse. The support may be a proper idempotent.

The simultaneous inverse is an explicit assumption only of this intermediate
constructor. The blocked source construction derives it separately.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `fusiontensors`,
  `eq:orthoW`, and Appendix A.
* arXiv:1511.08090, `AnyonsPEPS.tex`, `inversegaugeone`,
  `zippercondition`, and `zippercondition2`, lines 181--200.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor.IsBiorthogonalDecomposition

variable {ι : Type*} [Fintype ι] {d d' D : ℕ} {δ : ι → ℕ}
  {B : MPSTensor d D} {A : ∀ c : ι, MPSTensor d (δ c)}
  {V : ∀ c : ι, Matrix (Fin (δ c)) (Fin D) ℂ}
  {W : ∀ c : ι, Matrix (Fin D) (Fin (δ c)) ℂ}

/-- An exact biorthogonal decomposition is preserved under any common choice
of nonempty words, with the same rectangular maps. Source: GLM23 Appendix A,
`decompopen`, at arbitrary positive lengths. -/
theorem ofWords (h : IsBiorthogonalDecomposition B A V W)
    (u : Fin d' → List (Fin d)) (hu : ∀ j, u j ≠ [])
    {B' : MPSTensor d' D} (hB' : ∀ j, B' j = Kraus.evalWord B (u j))
    {A' : ∀ c : ι, MPSTensor d' (δ c)}
    (hA' : ∀ c j, A' c j = Kraus.evalWord (A c) (u j)) :
    IsBiorthogonalDecomposition B' A' V W where
  retract := h.retract
  orthogonal := h.orthogonal
  letter j := by
    rw [hB', h.evalWord (u j) (hu j)]
    simp_rw [hA']

end MPSTensor.IsBiorthogonalDecomposition

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
  {D : Λ → ℕ} {T : ∀ a, MPOTensor p (D a)} {N : Λ → Λ → Λ → ℕ}

/-- Synthesis columns of an exact pairwise boundary decomposition, expressed
on the product bond coordinates used by the zipper equations. -/
def biorthogonalSynthesis {a b : Λ}
    (W : ∀ c, Fin (N a b c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ) :
    Matrix (Fin (D a) × Fin (D b))
      ((c : Λ) × (Fin (N a b c) × Fin (D c))) ℂ :=
  fun x y ↦ W y.1 y.2.1 (finProdFinEquiv x) y.2.2

/-- Analysis rows of an exact pairwise boundary decomposition. They are
independent left inverses, not conjugate transposes of the synthesis maps. -/
def biorthogonalAnalysis {a b : Λ}
    (V : ∀ c, Fin (N a b c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ) :
    Matrix ((c : Λ) × (Fin (N a b c) × Fin (D c)))
      (Fin (D a) × Fin (D b)) ℂ :=
  fun y x ↦ V y.1 y.2.1 y.2.2 (finProdFinEquiv x)

variable {a b : Λ}
  {V : ∀ c, Fin (N a b c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ}
  {W : ∀ c, Fin (N a b c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ}
  (h : MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
    (fun q : (c : Λ) × Fin (N a b c) ↦ (T q.1).toMPSTensor)
    (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2))

include h

/-- Collecting the separate biorthogonality identities gives a left inverse
on the full multiplicity coordinate space. -/
theorem biorthogonalAnalysis_mul_synthesis :
    biorthogonalAnalysis V * biorthogonalSynthesis W = 1 := by
  funext ⟨c, μ, y⟩ ⟨c', μ', y'⟩
  have hsum :
      (biorthogonalAnalysis V * biorthogonalSynthesis W) ⟨c, μ, y⟩ ⟨c', μ', y'⟩ =
        (V c μ * W c' μ') y y' := by
    simp only [Matrix.mul_apply]
    exact Fintype.sum_equiv finProdFinEquiv _ _ fun _ ↦ rfl
  rw [hsum]
  by_cases heq : (⟨c, μ⟩ : (c : Λ) × Fin (N a b c)) = ⟨c', μ'⟩
  · obtain ⟨rfl, hμ⟩ := Sigma.mk.inj_iff.mp heq
    obtain rfl := eq_of_heq hμ
    rw [h.retract ⟨c, μ⟩]
    simp [Matrix.one_apply]
  · rw [h.orthogonal ⟨c, μ⟩ ⟨c', μ'⟩ heq,
      Matrix.one_apply_ne (fun he => heq (by cases he; rfl))]
    rfl

/-- An exact pairwise boundary decomposition reconstructs the product letter
through the direct sum of the target blocks. Source: GLM23 `fusiontensors`;
arXiv:1511.08090, `inversegaugeone`. -/
theorem pairLetter_eq_biorthogonalSynthesis_mul (i k : Fin p) :
    (∑ j : Fin p, T a i j ⊗ₖ T b j k) =
      biorthogonalSynthesis W * Matrix.blockDiagonal' (fun c ↦
        (1 : Matrix (Fin (N a b c)) (Fin (N a b c)) ℂ) ⊗ₖ T c i k) *
        biorthogonalAnalysis V := by
  let S := biorthogonalSynthesis W
  let C := Matrix.blockDiagonal' (fun c ↦
    (1 : Matrix (Fin (N a b c)) (Fin (N a b c)) ℂ) ⊗ₖ T c i k)
  have hSC (x : Fin (D a) × Fin (D b)) (c : Λ) (μ : Fin (N a b c))
      (y : Fin (D c)) :
      (S * C) x ⟨c, μ, y⟩ = ∑ z, W c μ (finProdFinEquiv x) z * T c i k z y := by
    rw [Matrix.mul_apply, Fintype.sum_sigma,
      Finset.sum_eq_single c
        (fun c' _ hc' ↦ Finset.sum_eq_zero fun _ _ ↦ by
          dsimp only [C]
          rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc', mul_zero])
        (fun hc ↦ absurd (Finset.mem_univ c) hc)]
    simp [C, S, biorthogonalSynthesis, Matrix.blockDiagonal'_apply_eq,
      Matrix.one_apply, Fintype.sum_prod_type]
  funext x x'
  have hletter := congrArg
    (fun M ↦ M (finProdFinEquiv x) (finProdFinEquiv x'))
    (h.letter (finProdFinEquiv (i, k)))
  change _ = ((S * C) * biorthogonalAnalysis V) x x'
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  simp_rw [Fintype.sum_prod_type, hSC]
  simpa [MPOTensor.toMPSTensor,
    Matrix.sum_apply, Fintype.sum_sigma, Matrix.mul_apply, biorthogonalAnalysis,
    mulTensor_apply, Matrix.submatrix_apply] using hletter

omit h

/-- Exact biorthogonal pairwise decompositions give complete zipper tensors
when a simultaneous target-letter inverse is supplied. Both zipper identities
are consequences of reconstruction and the left-inverse identity.
Source: GLM23 Appendix A; arXiv:1511.08090, lines 181--200 and 269--277. -/
@[reducible] noncomputable def ofBiorthogonal
    (hD : ∀ a, 0 < D a) (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor)
    (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ)
    (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ)
    (hVW : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
        (fun q : (c : Λ) × Fin (N a b c) ↦ (T q.1).toMPSTensor)
        (fun q ↦ V a b q.1 q.2) (fun q ↦ W a b q.1 q.2))
    (K : Matrix ((c : Λ) × (Fin (D c) × Fin (D c))) (Fin p × Fin p) ℂ)
    (hK : ∀ (c d : Λ) (x y : Fin (D c)) (x' y' : Fin (D d)),
      (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
        if he : c = d then
          if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
        else 0) : CompleteZipperFusionFamily Λ p where
  bondDim := D
  bondDim_pos := hD
  tensor := T
  tensor_injective := hT
  fusionMultiplicity := N
  fusionSynthesis a b := biorthogonalSynthesis (W a b)
  fusionAnalysis a b := biorthogonalAnalysis (V a b)
  analysis_mul_synthesis a b := biorthogonalAnalysis_mul_synthesis (hVW a b)
  pairLetter_mul_synthesis a b i k := by
    rw [pairLetter_eq_biorthogonalSynthesis_mul (hVW a b), Matrix.mul_assoc,
      biorthogonalAnalysis_mul_synthesis (hVW a b), Matrix.mul_one]
  analysis_mul_pairLetter a b i k := by
    rw [pairLetter_eq_biorthogonalSynthesis_mul (hVW a b), ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, biorthogonalAnalysis_mul_synthesis (hVW a b), Matrix.one_mul]
  pairLetter_eq_synthesis_mul_directSum_mul_analysis a b i k :=
    pairLetter_eq_biorthogonalSynthesis_mul (hVW a b) i k
  blockLeftInverse := K
  blockLeftInverse_apply := hK

end MPOTensor.CompleteZipperFusionFamily
