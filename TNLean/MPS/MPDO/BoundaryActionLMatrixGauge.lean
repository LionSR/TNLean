/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionLMatrix
import TNLean.MPS.MPDO.BoundaryFusionFMatrix

/-!
# Gauge transformations of the multiplicity L and F matrices

The exact fusion and action maps of an MPO algebra and an MPO-symmetric
state are fixed only up to invertible changes of basis of their
multiplicity spaces. Changing every analysis map by
`V^i ↦ ∑_{i'} X_{i i'} V^{i'}` and every synthesis map by
`W^i ↦ ∑_{i'} X̂_{i i'} W^{i'}` changes the normalized-trace coefficients
multilinearly:

* the L matrix by `L' = ∑ X X X̂ Ŷ L`, source lines 593--605;
* the F matrix by `F' = ∑ Y Y Ŷ Ŷ F`, source lines 415--422.

These two identities are coordinate identities and hold for arbitrary
matrices `X, X̂, Y, Ŷ`. Conversely, any two exact biorthogonal decompositions
of the same tensor onto injective, positive-dimensional, scalar-gauge-separated
blocks are related by such a change of basis, with `X̂ = (X⁻¹)ᵀ`; the
existing zipper uniqueness gives this relation after multiplication by a
letter, and injectivity of the target block removes the letter. Hence the
L and F matrices of any two choices of exact fusion and action maps are
related by the source's gauge transformation.

## Main results

* `MPOTensor.actionLMatrix_regauge`: the L-symbol gauge law, GLM23 lines
  593--605.
* `MPOTensor.fusionFMatrix_regauge`: the F-symbol gauge law, GLM23 lines
  415--422.
* `MPSTensor.IsBiorthogonalDecomposition.exists_multiplicityGauge_eq_of_isInjective`:
  two exact decompositions onto injective separated blocks differ by an
  invertible multiplicity gauge, exactly and not only on the letter support.
* `MPOTensor.exists_actionLMatrix_fusionFMatrix_regauge_of_isInjective`: the
  L and F matrices of two choices of exact maps are related by the joint
  gauge transformation.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
  lines 415--422 (fusion-tensor gauge and the F-symbols) and 593--605
  (action-tensor gauge and the L-symbols).
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- `kronId` is linear in its matrix argument. -/
theorem kronId_sum_smul {ι : Type*} [Fintype ι] {m n : ℕ} (c : ι → ℂ)
    (V : ι → Matrix (Fin m) (Fin n) ℂ) (D : ℕ) :
    kronId (∑ i, c i • V i) D = ∑ i, c i • kronId (V i) D := by
  ext p q
  simp [kronId, Matrix.sum_apply, Finset.sum_mul, mul_assoc]

/-- `idKron` is linear in its matrix argument. -/
theorem idKron_sum_smul {ι : Type*} [Fintype ι] {m n : ℕ} (D : ℕ) (c : ι → ℂ)
    (V : ι → Matrix (Fin m) (Fin n) ℂ) :
    idKron D (∑ i, c i • V i) = ∑ i, c i • idKron D (V i) := by
  ext p q
  simp [idKron, Matrix.sum_apply, Finset.mul_sum, mul_left_comm]

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- An entry of the L matrix as the normalized trace of the two tree maps. -/
theorem actionLMatrix_apply
    (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (a b c : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
    (k : Fin (M c x y)) (μ : Fin (N a b c)) :
    actionLMatrix WF VA WA a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
      (D y : ℂ)⁻¹ * Matrix.trace
        (sequentialActionAnalysis VA a b x ⟨⟨z, j⟩, ⟨y, i⟩⟩ *
          fusionThenActionSynthesis WF WA a b x ⟨⟨c, μ⟩, ⟨y, k⟩⟩) :=
  rfl

section Regauge

variable {VA VA' : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
  {WA WA' : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}
  {VF VF' : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ}
  {WF WF' : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ}
  {X Xh : ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ}
  {Y Yh : ∀ a b c, Matrix (Fin (N a b c)) (Fin (N a b c)) ℂ}

/-- Sequential analysis after an action-analysis gauge. -/
theorem sequentialActionAnalysis_regauge
    (hVA : ∀ a x y i, VA' a x y i = ∑ i', X a x y i i' • VA a x y i')
    (a b : Fin r) (x z y : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z)) :
    sequentialActionAnalysis VA' a b x ⟨⟨z, j⟩, ⟨y, i⟩⟩ =
      ∑ i', ∑ j', (X a z y i i' * X b x z j j') •
        sequentialActionAnalysis VA a b x ⟨⟨z, j'⟩, ⟨y, i'⟩⟩ := by
  simp only [sequentialActionAnalysis, hVA, idKron_sum_smul, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by congr 1; ring

/-- Fusion-then-action synthesis after fusion- and action-synthesis gauges. -/
theorem fusionThenActionSynthesis_regauge
    (hWF : ∀ a b c μ, WF' a b c μ = ∑ μ', Yh a b c μ μ' • WF a b c μ')
    (hWA : ∀ a x y k, WA' a x y k = ∑ k', Xh a x y k k' • WA a x y k')
    (a b c : Fin r) (x y : Fin s) (μ : Fin (N a b c)) (k : Fin (M c x y)) :
    fusionThenActionSynthesis WF' WA' a b x ⟨⟨c, μ⟩, ⟨y, k⟩⟩ =
      ∑ μ', ∑ k', (Yh a b c μ μ' * Xh c x y k k') •
        fusionThenActionSynthesis WF WA a b x ⟨⟨c, μ'⟩, ⟨y, k'⟩⟩ := by
  simp only [fusionThenActionSynthesis, hWF, hWA, kronId_sum_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by congr 1; ring

/-- **Gauge transformation of the L-symbols.** Changing the action analysis
maps by `X`, the action synthesis maps by `X̂`, and the fusion synthesis
maps by `Ŷ` changes the L matrix by

`L'^{z,ij}_{c,kμ} = ∑ X^y_{az}[i,i'] X^z_{bx}[j,j'] X̂^y_{cx}[k,k'] Ŷ^c_{ab}[μ,μ']`
`L^{z,i'j'}_{c,k'μ'}`.

The gauge matrices are arbitrary; no invertibility is used. Source:
GLM23, `REsubmission.tex`, lines 593--605. -/
theorem actionLMatrix_regauge
    (hVA : ∀ a x y i, VA' a x y i = ∑ i', X a x y i i' • VA a x y i')
    (hWA : ∀ a x y k, WA' a x y k = ∑ k', Xh a x y k k' • WA a x y k')
    (hWF : ∀ a b c μ, WF' a b c μ = ∑ μ', Yh a b c μ μ' • WF a b c μ')
    (a b c : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
    (k : Fin (M c x y)) (μ : Fin (N a b c)) :
    actionLMatrix WF' VA' WA' a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
      ∑ i', ∑ j', ∑ k', ∑ μ',
        X a z y i i' * X b x z j j' * Xh c x y k k' * Yh a b c μ μ' *
          actionLMatrix WF VA WA a b x y ⟨z, i', j'⟩ ⟨c, k', μ'⟩ := by
  simp only [actionLMatrix_apply]
  rw [sequentialActionAnalysis_regauge hVA, fusionThenActionSynthesis_regauge hWF hWA]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [Fintype.sum_last_two_first_four]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  ring

/-- The left-tree analysis contraction entering the F matrix. -/
private noncomputable def fusionLeftContraction
    (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (a b c d e : Fin r) (mu : Fin (N a b e)) (nu : Fin (N e c d)) :
    Matrix (Fin (χ d)) ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) ℂ :=
  fun z v ↦ ∑ t : Fin (χ e),
    V e c d nu z (finProdFinEquiv (t, v.2)) * V a b e mu t (finProdFinEquiv v.1)

/-- The right-tree synthesis contraction entering the F matrix. -/
private noncomputable def fusionRightContraction
    (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (a b c d f : Fin r) (lam : Fin (N b c f)) (sig : Fin (N a f d)) :
    Matrix ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) (Fin (χ d)) ℂ :=
  fun v z ↦ ∑ t : Fin (χ f),
    W b c f lam (finProdFinEquiv (v.1.2, v.2)) t * W a f d sig (finProdFinEquiv (v.1.1, t)) z

private theorem fusionFMatrix_eq_contraction
    (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (a b c d e f : Fin r) (mu : Fin (N a b e)) (nu : Fin (N e c d))
    (lam : Fin (N b c f)) (sig : Fin (N a f d)) :
    fusionFMatrix V W a b c d ⟨e, mu, nu⟩ ⟨f, lam, sig⟩ =
      (χ d : ℂ)⁻¹ * Matrix.trace (fusionLeftContraction V a b c d e mu nu *
        fusionRightContraction W a b c d f lam sig) :=
  rfl

private theorem fusionLeftContraction_regauge
    (hVF : ∀ a b c μ, VF' a b c μ = ∑ μ', Y a b c μ μ' • VF a b c μ')
    (a b c d e : Fin r) (mu : Fin (N a b e)) (nu : Fin (N e c d)) :
    fusionLeftContraction VF' a b c d e mu nu =
      ∑ mu', ∑ nu', (Y a b e mu mu' * Y e c d nu nu') •
        fusionLeftContraction VF a b c d e mu' nu' := by
  ext z v
  simp only [fusionLeftContraction, hVF, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three, Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ ?_
  ring

private theorem fusionRightContraction_regauge
    (hWF : ∀ a b c μ, WF' a b c μ = ∑ μ', Yh a b c μ μ' • WF a b c μ')
    (a b c d f : Fin r) (lam : Fin (N b c f)) (sig : Fin (N a f d)) :
    fusionRightContraction WF' a b c d f lam sig =
      ∑ lam', ∑ sig', (Yh b c f lam lam' * Yh a f d sig sig') •
        fusionRightContraction WF a b c d f lam' sig' := by
  ext v z
  simp only [fusionRightContraction, hWF, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ ?_
  ring

/-- **Gauge transformation of the F-symbols.** Changing the fusion analysis
maps by `Y` and the fusion synthesis maps by `Ŷ` changes the F matrix by

`F'[(e,μ,ν),(f,λ,σ)] = ∑ Y^e_{ab}[μ,μ'] Y^d_{ec}[ν,ν'] Ŷ^f_{bc}[λ,λ'] Ŷ^d_{af}[σ,σ']`
`F[(e,μ',ν'),(f,λ',σ')]`.

The gauge matrices are arbitrary. Source: GLM23, `REsubmission.tex`,
lines 415--422. -/
theorem fusionFMatrix_regauge
    (hVF : ∀ a b c μ, VF' a b c μ = ∑ μ', Y a b c μ μ' • VF a b c μ')
    (hWF : ∀ a b c μ, WF' a b c μ = ∑ μ', Yh a b c μ μ' • WF a b c μ')
    (a b c d e f : Fin r) (mu : Fin (N a b e)) (nu : Fin (N e c d))
    (lam : Fin (N b c f)) (sig : Fin (N a f d)) :
    fusionFMatrix VF' WF' a b c d ⟨e, mu, nu⟩ ⟨f, lam, sig⟩ =
      ∑ mu', ∑ nu', ∑ lam', ∑ sig',
        Y a b e mu mu' * Y e c d nu nu' * Yh b c f lam lam' * Yh a f d sig sig' *
          fusionFMatrix VF WF a b c d ⟨e, mu', nu'⟩ ⟨f, lam', sig'⟩ := by
  simp only [fusionFMatrix_eq_contraction]
  rw [fusionLeftContraction_regauge hVF, fusionRightContraction_regauge hWF]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [Fintype.sum_last_two_first_four]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  ring

end Regauge

end MPOTensor

namespace MPSTensor.IsBiorthogonalDecomposition

/-- An analysis map that intertwines an injective target block with the
source tensor is determined by its products with the letters. -/
private theorem eq_of_mul_letter_eq {d DB D : ℕ} {B : MPSTensor d DB} {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) {V V' : Matrix (Fin D) (Fin DB) ℂ}
    (hV : ∀ i, V * B i = A i * V) (hV' : ∀ i, V' * B i = A i * V')
    (h : ∀ i, V' * B i = V * B i) : V' = V := by
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
    (hA.span_eq_top ▸ Submodule.mem_top : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range A))
  calc V' = (∑ i, α i • A i) * V' := by rw [hα, Matrix.one_mul]
    _ = (∑ i, α i • A i) * V := by
      simp only [Matrix.sum_mul, Matrix.smul_mul, ← hV', h, hV]
    _ = V := by rw [hα, Matrix.one_mul]

/-- A synthesis map that intertwines an injective target block with the
source tensor is determined by its products with the letters. -/
private theorem eq_of_letter_mul_eq {d DB D : ℕ} {B : MPSTensor d DB} {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) {W W' : Matrix (Fin DB) (Fin D) ℂ}
    (hW : ∀ i, B i * W = W * A i) (hW' : ∀ i, B i * W' = W' * A i)
    (h : ∀ i, B i * W' = B i * W) : W' = W := by
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
    (hA.span_eq_top ▸ Submodule.mem_top : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range A))
  calc W' = W' * (∑ i, α i • A i) := by rw [hα, Matrix.mul_one]
    _ = W * (∑ i, α i • A i) := by
      simp only [Matrix.mul_sum, Matrix.mul_smul, ← hW', h, hW]
    _ = W := by rw [hα, Matrix.mul_one]

/-- **Exact multiplicity gauges.** Two exact biorthogonal decompositions of
the same tensor onto individually injective, positive-dimensional,
scalar-gauge-separated blocks differ by an invertible change of basis of
each multiplicity space: `V' = Y V` and `W' = W Y⁻¹`. The letter-support
relation of the zipper uniqueness theorem holds before multiplication by a
letter because each target block is injective. Source: GLM23, fusion and
action gauge freedoms at lines 415--424 and 595--602. -/
theorem exists_multiplicityGauge_eq_of_isInjective
    {d DB g : ℕ} {dim N : Fin g → ℕ} {B : MPSTensor d DB}
    {A : ∀ c, MPSTensor d (dim c)}
    {V V' : ∀ c, Fin (N c) → Matrix (Fin (dim c)) (Fin DB) ℂ}
    {W W' : ∀ c, Fin (N c) → Matrix (Fin DB) (Fin (dim c)) ℂ}
    (h : IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (N c) ↦ A q.1)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2))
    (h' : IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (N c) ↦ A q.1)
      (fun q ↦ V' q.1 q.2) (fun q ↦ W' q.1 q.2))
    (hInj : ∀ c, Kraus.IsInjective (A c)) (hD : ∀ c, 0 < dim c)
    (hne : BlocksNotGaugePhaseEquiv A) :
    ∃ Y : ∀ c, GL (Fin (N c)) ℂ,
      (∀ c μ, V' c μ =
        ∑ ν, (↑(Y c) : Matrix (Fin (N c)) (Fin (N c)) ℂ) μ ν • V c ν) ∧
      (∀ c κ, W' c κ =
        ∑ ν, (↑(Y c)⁻¹ : Matrix (Fin (N c)) (Fin (N c)) ℂ) ν κ • W c ν) := by
  obtain ⟨Y, ⟨hV, hW⟩, -⟩ := h.exists_unique_multiplicityGauge_of_isInjective h' hInj hD hne
  refine ⟨Y, fun c μ ↦ ?_, fun c κ ↦ ?_⟩
  · refine eq_of_mul_letter_eq (hInj c) (fun i ↦ ?_) (fun i ↦ h'.toZipperDecomposition.V_mul c μ i)
      (fun i ↦ by rw [hV, Matrix.sum_mul]; simp only [Matrix.smul_mul])
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
    exact Finset.sum_congr rfl fun ν _ ↦
      congrArg (fun T ↦ _ • T) (h.toZipperDecomposition.V_mul c ν i)
  · refine eq_of_letter_mul_eq (hInj c) (fun i ↦ ?_) (fun i ↦ h'.toZipperDecomposition.mul_W c κ i)
      (fun i ↦ by rw [hW, Matrix.mul_sum]; simp only [Matrix.mul_smul])
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
    exact Finset.sum_congr rfl fun ν _ ↦
      congrArg (fun T ↦ _ • T) (h.toZipperDecomposition.mul_W c ν i)

end MPSTensor.IsBiorthogonalDecomposition

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- **The joint gauge law of the L- and F-symbols.** Two choices of exact
fusion and action maps for the same individually injective,
positive-dimensional, scalar-gauge-separated operator and state blocks
differ by invertible multiplicity gauges `Y` and `X`. Their L and F matrices
are related by the source's gauge transformation, with hatted gauges the
transposed inverses. Source: GLM23, `REsubmission.tex`, lines 415--422 and
593--605. -/
theorem exists_actionLMatrix_fusionFMatrix_regauge_of_isInjective
    {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor)
    (hInjA : ∀ x, Kraus.IsInjective (A x))
    (hχ : ∀ a, 0 < χ a) (hD : ∀ x, 0 < D x)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (hneA : MPSTensor.BlocksNotGaugePhaseEquiv A)
    {VF VF' : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ}
    {WF WF' : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ}
    {VA VA' : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
    {WA WA' : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (hF' : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF' a b q.1 q.2) (fun q ↦ WF' a b q.1 q.2))
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (hA' : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA' a x q.1 q.2) (fun q ↦ WA' a x q.1 q.2)) :
    ∃ (X : ∀ a x y, GL (Fin (M a x y)) ℂ) (Y : ∀ a b c, GL (Fin (N a b c)) ℂ),
      (∀ (a b c : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
        (k : Fin (M c x y)) (μ : Fin (N a b c)),
        actionLMatrix WF' VA' WA' a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
          ∑ i', ∑ j', ∑ k', ∑ μ',
            (↑(X a z y) : Matrix (Fin (M a z y)) (Fin (M a z y)) ℂ) i i' *
              (↑(X b x z) : Matrix (Fin (M b x z)) (Fin (M b x z)) ℂ) j j' *
              (↑(X c x y)⁻¹ : Matrix (Fin (M c x y)) (Fin (M c x y)) ℂ) k' k *
              (↑(Y a b c)⁻¹ : Matrix (Fin (N a b c)) (Fin (N a b c)) ℂ) μ' μ *
              actionLMatrix WF VA WA a b x y ⟨z, i', j'⟩ ⟨c, k', μ'⟩) ∧
      (∀ (a b c d e f : Fin r) (mu : Fin (N a b e)) (nu : Fin (N e c d))
        (lam : Fin (N b c f)) (sig : Fin (N a f d)),
        fusionFMatrix VF' WF' a b c d ⟨e, mu, nu⟩ ⟨f, lam, sig⟩ =
          ∑ mu', ∑ nu', ∑ lam', ∑ sig',
            (↑(Y a b e) : Matrix (Fin (N a b e)) (Fin (N a b e)) ℂ) mu mu' *
              (↑(Y e c d) : Matrix (Fin (N e c d)) (Fin (N e c d)) ℂ) nu nu' *
              (↑(Y b c f)⁻¹ : Matrix (Fin (N b c f)) (Fin (N b c f)) ℂ) lam' lam *
              (↑(Y a f d)⁻¹ : Matrix (Fin (N a f d)) (Fin (N a f d)) ℂ) sig' sig *
              fusionFMatrix VF WF a b c d ⟨e, mu', nu'⟩ ⟨f, lam', sig'⟩) := by
  choose Y hYV hYW using fun a b ↦
    (hF a b).exists_multiplicityGauge_eq_of_isInjective (hF' a b) hInjO hχ hneO
  choose X hXV hXW using fun a x ↦
    (hA a x).exists_multiplicityGauge_eq_of_isInjective (hA' a x) hInjA hD hneA
  refine ⟨X, Y, fun a b c x y z i j k μ ↦ ?_, fun a b c d e f mu nu lam sig ↦ ?_⟩
  · exact actionLMatrix_regauge
      (X := fun a x y ↦ (↑(X a x y) : Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ))
      (Xh := fun a x y k k' ↦
        (↑(X a x y)⁻¹ : Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ) k' k)
      (Yh := fun a b c μ μ' ↦
        (↑(Y a b c)⁻¹ : Matrix (Fin (N a b c)) (Fin (N a b c)) ℂ) μ' μ)
      (fun a x y i ↦ hXV a x y i) (fun a x y k ↦ hXW a x y k) (fun a b c μ ↦ hYW a b c μ)
      a b c x y z i j k μ
  · exact fusionFMatrix_regauge
      (Y := fun a b c ↦ (↑(Y a b c) : Matrix (Fin (N a b c)) (Fin (N a b c)) ℂ))
      (Yh := fun a b c μ μ' ↦
        (↑(Y a b c)⁻¹ : Matrix (Fin (N a b c)) (Fin (N a b c)) ℂ) μ' μ)
      (fun a b c μ ↦ hYV a b c μ) (fun a b c μ ↦ hYW a b c μ) a b c d e f mu nu lam sig

end MPOTensor
