/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Boundary.NormalAdjointBoundary
import TNLean.MPS.Transfer.Correlation.EntanglementSpectrum
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.MPO.ArbitraryPhysicalMixedMPO
import QICLean.Algebra.Unitary.UnitaryFactorizationComparison

/-!
# Adjoint closure of the mixed boundary range for Hermitian action gauges

Let the endpoint operators of the arbitrary-alphabet mixed path be on-site,
with one-dimensional operator bonds, action multiplicity one, and Hermitian
on-site matrices `u_p`. Let the action gauges `Y_p`, the synthesis maps read
as square matrices, be proportional to Hermitian matrices. Then the physical
adjoint of the common operator tensor is a diagonal bond similarity of the
tensor itself: the diagonal blocks are fixed, and the crossed blocks
`T^{01} = W_0^T ⊗ V_1` and `T^{10} = W_1^T ⊗ V_0` are multiplied by `t` and
`t⁻¹` for one scalar `t`. Hence the adjoint of every boundary operator of the
common operator is again a boundary operator, at every length. For `ℤ₂` with
unitary `u_p` one has `u_p² = 1`, so `u_p` is Hermitian.

The gauge condition holds for endpoint tensors in canonical form: for an
injective tensor with `E(1) = 1` and a positive definite fixed point of the
adjoint transfer map, the gauge of a unitary on-site symmetry is a scalar
multiple of a unitary (arXiv:0802.0447, Lemma 1 and Theorem 2). When
`u² = 1` its square is scalar by injectivity, and a unitary with scalar
square is a scalar multiple of a Hermitian matrix.

**Scope restriction (Z2, unitary on-site endpoints, Hermitian action gauges):**
the endpoint operators are on-site with Hermitian on-site matrices, which
covers unitary `ℤ₂` symmetries, and both action gauges are assumed
proportional to Hermitian matrices. The source imposes no such gauge
condition, and adjoint closure fails without it. See
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, section
"Unitary on-site endpoints", paragraph "When closure holds".

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, Section 5,
`REsubmission.tex`, lines 1600–1631 (the crossed blocks) and
lines 1687–1692 (the canonical parent).
-/

open scoped Matrix BigOperators ComplexOrder

open MPOTensor.PhysicalSectorFactorization (changePhysicalBasis)

namespace MPOTensor

variable {d D : ℕ}

/-- Tensors whose entries differ by the factors `g β / g α` of a nowhere-zero
bond weight have the same boundary operators, after the boundary is
conjugated by the diagonal matrix of the weight. -/
theorem mpoWithBoundary_eq_of_apply_eq_div_mul {M N : MPOTensor d D}
    (g : Fin D → ℂ) (hg : ∀ p, g p ≠ 0)
    (h : ∀ i j β α, N (i, j) β α = g β / g α * M (i, j) β α)
    (X : Matrix (Fin D) (Fin D) ℂ) (L : ℕ) :
    mpoWithBoundary N X L =
      mpoWithBoundary M (Matrix.diagonal g⁻¹ * X * Matrix.diagonal g) L := by
  refine mpoWithBoundary_eq_of_conj (Matrix.diagonal_inv_mul_diagonal hg)
    (Matrix.diagonal_mul_diagonal_inv hg) (fun i j ↦ ?_) X L
  ext β α
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, h]
  simp only [Pi.inv_apply]
  field_simp [hg β, hg α]

/-- The physical adjoint commutes with a change of physical coordinates. -/
theorem physicalAdjointTensor_changePhysicalBasis {e : ℕ}
    (V : Matrix (Fin e) (Fin d) ℂ) (M : MPOTensor d D) :
    physicalAdjointTensor (changePhysicalBasis V M) =
      changePhysicalBasis V (physicalAdjointTensor M) := by
  ext ⟨i, j⟩ β α
  simp only [physicalAdjointTensor_apply, changePhysicalBasis,
    physicalSlice_physicalAdjointTensor]
  rw [← Matrix.conjTranspose_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- A change of physical coordinates preserves an entrywise rescaling of the
virtual indices. -/
theorem changePhysicalBasis_apply_of_apply_eq_mul {e : ℕ} {M N : MPOTensor d D}
    (c : Fin D → Fin D → ℂ) (h : ∀ i j β α, N (i, j) β α = c β α * M (i, j) β α)
    (V : Matrix (Fin e) (Fin d) ℂ) (i j : Fin e) (β α : Fin D) :
    changePhysicalBasis V N (i, j) β α = c β α * changePhysicalBasis V M (i, j) β α := by
  have hs : physicalSlice N β α = c β α • physicalSlice M β α := by
    ext k l
    simp [physicalSlice, h]
  simp only [changePhysicalBasis, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    smul_eq_mul]

/-- A tensor with one-dimensional bond is fixed by the physical adjoint
exactly when its on-site matrix is Hermitian. -/
theorem physicalAdjointTensor_eq_self_of_isHermitian {M : MPOTensor d 1}
    (hM : (physicalSlice M 0 0).IsHermitian) : physicalAdjointTensor M = M := by
  ext ⟨i, j⟩ β α
  rw [Subsingleton.elim β 0, Subsingleton.elim α 0, physicalAdjointTensor_apply]
  exact congrFun (congrFun hM i) j

end MPOTensor

namespace MPSTensor.MPOSymmetry

open MPOTensor

variable {d₀ d₁ D₀ D₁ χ₀ χ₁ m : ℕ}

/-- The bond weight equal to `1` on the first endpoint bond and to `c` on the
second. -/
def mixedEndpointBondWeight (χ₀ χ₁ : ℕ) (c : ℂ) (α : Fin (χ₀ + χ₁)) : ℂ :=
  Sum.elim (fun _ ↦ 1) (fun _ ↦ c) (finSumFinEquiv.symm α)

theorem mixedEndpointBondWeight_ne_zero {c : ℂ} (hc : c ≠ 0) (α : Fin (χ₀ + χ₁)) :
    mixedEndpointBondWeight χ₀ χ₁ c α ≠ 0 := by
  obtain ⟨α, rfl⟩ := finSumFinEquiv.surjective α
  rcases α with α | α <;> simp [mixedEndpointBondWeight, hc]

/-- The physical adjoint of the mixed endpoint operator tensor. If the
physical adjoints of the endpoint tensors are endpoint tensors `T₀'`, `T₁'`,
and the entries of the action maps are conjugated, under transposition of
the state indices, into multiples `ω_p`, `ν_p` of the action maps of `T_p'`,
then the physical adjoint is the mixed operator of the primed data with the
crossed blocks rescaled by `ω₀ ν₁` and `ω₁ ν₀`. When these factors are
inverse to each other, this is a diagonal bond similarity. The primed data
are the unprimed ones for a Hermitian symmetry, and those of the inverse
label for a unitary group representation. Source: arXiv:2203.12563,
lines 1600–1631, and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`,
paragraph "When closure holds". -/
theorem physicalAdjointTensor_mixedEndpointMPO_apply
    {T₀ T₀' : MPOTensor (D₀ * D₀) χ₀} {T₁ T₁' : MPOTensor (D₁ * D₁) χ₁}
    {V₀ V₀' : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ}
    {V₁ V₁' : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ}
    {W₀ W₀' : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ}
    {W₁ W₁' : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ}
    (hT₀ : physicalAdjointTensor T₀ = T₀') (hT₁ : physicalAdjointTensor T₁ = T₁')
    {ω₀ ω₁ ν₀ ν₁ c : ℂ}
    (hW₀ : ∀ μ α r k, star (W₀ μ (finProdFinEquiv (α, r)) k) =
      ω₀ * W₀' μ (finProdFinEquiv (α, k)) r)
    (hW₁ : ∀ μ α r k, star (W₁ μ (finProdFinEquiv (α, r)) k) =
      ω₁ * W₁' μ (finProdFinEquiv (α, k)) r)
    (hV₀ : ∀ μ β l s, star (V₀ μ l (finProdFinEquiv (β, s))) =
      ν₀ * V₀' μ s (finProdFinEquiv (β, l)))
    (hV₁ : ∀ μ β l s, star (V₁ μ l (finProdFinEquiv (β, s))) =
      ν₁ * V₁' μ s (finProdFinEquiv (β, l)))
    (h₀₁ : c * (ω₀ * ν₁) = 1) (h₁₀ : ω₁ * ν₀ = c)
    (i j : Fin ((D₀ + D₁) * (D₀ + D₁))) (β α : Fin (χ₀ + χ₁)) :
    physicalAdjointTensor (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁) (i, j) β α =
      mixedEndpointBondWeight χ₀ χ₁ c β / mixedEndpointBondWeight χ₀ χ₁ c α *
        mixedEndpointMPO T₀' T₁' V₀' V₁' W₀' W₁' (i, j) β α := by
  have hc : c ≠ 0 := left_ne_zero_of_mul_eq_one h₀₁
  have h₀₁' : ω₀ * ν₁ = c⁻¹ := eq_inv_of_mul_eq_one_right h₀₁
  have hT₀' : ∀ x y β α, star (T₀ (y, x) β α) = T₀' (x, y) β α := fun x y β α ↦
    congrFun (congrFun (congrFun hT₀ (x, y)) β) α
  have hT₁' : ∀ x y β α, star (T₁ (y, x) β α) = T₁' (x, y) β α := fun x y β α ↦
    congrFun (congrFun (congrFun hT₁ (x, y)) β) α
  obtain ⟨⟨r, s⟩, rfl⟩ := (mixedEndpointPhysicalEquiv D₀ D₁).surjective i
  obtain ⟨⟨k, l⟩, rfl⟩ := (mixedEndpointPhysicalEquiv D₀ D₁).surjective j
  obtain ⟨β, rfl⟩ := finSumFinEquiv.surjective β
  obtain ⟨α, rfl⟩ := finSumFinEquiv.surjective α
  simp only [physicalAdjointTensor_apply, mixedEndpointMPO, Equiv.symm_apply_apply,
    Matrix.submatrix_apply, mixedEndpointBondWeight]
  rcases r with r | r <;> rcases s with s | s <;> rcases k with k | k <;>
    rcases l with l | l <;> rcases β with β | β <;> rcases α with α | α <;>
    simp only [mixedEndpointMPOLetter, Sum.elim_inl, Sum.elim_inr, star_zero, mul_zero,
      div_one, one_mul, div_self one_ne_zero]
  · exact hT₀' _ _ _ _
  · rw [star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [star_mul', hW₀, hV₁, one_div, ← h₀₁']
    ring
  · rw [star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [star_mul', hW₁, hV₀, ← h₁₀]
    ring
  · rw [div_self hc, one_mul]
    exact hT₁' _ _ _ _

/-- The action gauge of an on-site symmetry: the synthesis map of an action
with one-dimensional operator bond, read as a square matrix. Source:
arXiv:2203.12563, the action maps of `fusiontensors2`, and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"The common operator of on-site symmetries". -/
def bondOneActionGauge {D : ℕ} (W : Matrix (Fin (1 * D)) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun k r ↦ W (finProdFinEquiv (0, k)) r

/-- The analysis map of an action with one-dimensional operator bond, read as
a square matrix; it inverts the action gauge. -/
def bondOneActionAnalysis {D : ℕ} (V : Matrix (Fin D) (Fin (1 * D)) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun l s ↦ V l (finProdFinEquiv (0, s))

/-- The square analysis map is a left inverse of the square action gauge. -/
theorem bondOneActionAnalysis_mul_bondOneActionGauge {D : ℕ}
    {V : Matrix (Fin D) (Fin (1 * D)) ℂ} {W : Matrix (Fin (1 * D)) (Fin D) ℂ}
    (hVW : V * W = 1) : bondOneActionAnalysis V * bondOneActionGauge W = 1 := by
  rw [← hVW]
  ext l r
  simp only [Matrix.mul_apply, bondOneActionAnalysis, bondOneActionGauge]
  rw [← finProdFinEquiv.sum_comp (fun x ↦ V l x * W x r), Fintype.sum_prod_type,
    Fin.sum_univ_one]

/-- If the action gauge of an on-site action is proportional to a Hermitian
matrix, then conjugating the entries of the synthesis map, under
transposition of the state indices, multiplies it by a scalar `ω`, and the
analysis map by `ω⁻¹`. -/
theorem exists_star_synthesis_analysis_of_isHermitian {D : ℕ}
    {V : Matrix (Fin D) (Fin (1 * D)) ℂ} {W : Matrix (Fin (1 * D)) (Fin D) ℂ}
    (hVW : V * W = 1) {c : ℂ} (hc : c ≠ 0) (hY : (c • bondOneActionGauge W).IsHermitian) :
    ∃ ω : ℂ, ω ≠ 0 ∧
      (∀ α r k, star (W (finProdFinEquiv (α, r)) k) = ω * W (finProdFinEquiv (α, k)) r) ∧
      ∀ β l s, star (V l (finProdFinEquiv (β, s))) = ω⁻¹ * V s (finProdFinEquiv (β, l)) := by
  set Y := bondOneActionGauge W with hYdef
  set V' := bondOneActionAnalysis V with hV'def
  have hsc : star c ≠ 0 := star_ne_zero.mpr hc
  set ω := (star c)⁻¹ * c with hωdef
  have hω : ω ≠ 0 := mul_ne_zero (inv_ne_zero hsc) hc
  have hYH : Yᴴ = ω • Y := by
    have h := hY.eq
    rw [Matrix.conjTranspose_smul] at h
    have h' := congrArg ((star c)⁻¹ • ·) h
    simp only [smul_smul, inv_mul_cancel₀ hsc, one_smul] at h'
    exact h'
  have hV'Y : V' * Y = 1 := bondOneActionAnalysis_mul_bondOneActionGauge hVW
  have hYV' : Y * V' = 1 := mul_eq_one_comm.mp hV'Y
  have hV'H : V'ᴴ = ω⁻¹ • V' := by
    have h1 : V'ᴴ * Yᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hYV', Matrix.conjTranspose_one]
    rw [hYH, Matrix.mul_smul] at h1
    have h2 : ω • V'ᴴ = V' := by
      calc ω • V'ᴴ = ω • (V'ᴴ * (Y * V')) := by rw [hYV', Matrix.mul_one]
        _ = (ω • (V'ᴴ * Y)) * V' := by rw [Matrix.smul_mul, Matrix.mul_assoc]
        _ = V' := by rw [h1, Matrix.one_mul]
    calc V'ᴴ = ω⁻¹ • (ω • V'ᴴ) := by rw [smul_smul, inv_mul_cancel₀ hω, one_smul]
      _ = ω⁻¹ • V' := by rw [h2]
  refine ⟨ω, hω, fun α r k ↦ ?_, fun β l s ↦ ?_⟩
  · rw [Subsingleton.elim α 0]
    have h := congrFun (congrFun hYH k) r
    simpa [hYdef, bondOneActionGauge, Matrix.conjTranspose_apply] using h
  · rw [Subsingleton.elim β 0]
    have h := congrFun (congrFun hV'H s) l
    simpa [hV'def, bondOneActionAnalysis, Matrix.conjTranspose_apply] using h

section Canonical

variable {d D : ℕ}

/-- An on-site action decomposition is the gauge relation
`∑ⱼ u_{ij} Aʲ = Y Aⁱ Y⁻¹` of the on-site matrix `u`, with the square action
gauge `Y` and its inverse, the square analysis map. Source: arXiv:2203.12563,
`fusiontensors2`, specialized to a one-dimensional operator bond. -/
theorem sum_smul_eq_bondOneActionGauge_mul_mul {A : MPSTensor d D} {T : MPOTensor d 1}
    {V : Fin 1 → Matrix (Fin D) (Fin (1 * D)) ℂ} {W : Fin 1 → Matrix (Fin (1 * D)) (Fin D) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A) (fun _ : Fin 1 => A) V W)
    (i : Fin d) :
    ∑ j, physicalSlice T 0 0 i j • A j =
      bondOneActionGauge (W 0) * A i * bondOneActionAnalysis (V 0) := by
  ext a b
  have hab := congrFun (congrFun (h.letter i) (finProdFinEquiv (0, a)))
    (finProdFinEquiv (0, b))
  simp only [MPOTensor.actTensor_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply, Fin.sum_univ_one] at hab
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, physicalSlice]
  rw [hab]
  simp only [Matrix.mul_apply, bondOneActionGauge, bondOneActionAnalysis]

/-- **The action gauge of a unitary involutive symmetry in canonical form.**
Let `A` be injective with `E(1) = 1` and a positive definite fixed point of
the adjoint transfer map, and let an on-site unitary `u` with `u² = 1` act on
`A`. Then the action gauge is proportional to a Hermitian matrix. The gauge
is a scalar multiple of a unitary by Pérez-García–Wolf–Sanz–Verstraete–Cirac,
arXiv:0802.0447, Lemma 1 and Theorem 2; its square is scalar by injectivity,
and a unitary with scalar square is a scalar multiple of a Hermitian matrix.
Source: `docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`,
paragraph "When closure holds". -/
theorem exists_isHermitian_smul_bondOneActionGauge
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    {Λ : Matrix (Fin D) (Fin D) ℂ} (hΛpos : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ) {T : MPOTensor d 1}
    (hu : physicalSlice T 0 0 ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hu2 : physicalSlice T 0 0 * physicalSlice T 0 0 = 1)
    {V : Fin 1 → Matrix (Fin D) (Fin (1 * D)) ℂ} {W : Fin 1 → Matrix (Fin (1 * D)) (Fin D) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A) (fun _ : Fin 1 => A) V W) :
    ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W 0)).IsHermitian := by
  classical
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    exact ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
  set u := physicalSlice T 0 0 with hudef
  set Y := bondOneActionGauge (W 0) with hYdef
  set V' := bondOneActionAnalysis (V 0) with hV'def
  have hV'Y : V' * Y = 1 := bondOneActionAnalysis_mul_bondOneActionGauge (h.retract 0)
  have hYV' : Y * V' = 1 := mul_eq_one_comm.mp hV'Y
  have hrel : ∀ i, ∑ j, u i j • A j = Y * A i * V' :=
    sum_smul_eq_bondOneActionGauge_mul_mul h
  let X : GL (Fin D) ℂ := ⟨Y, V', hYV', hV'Y⟩
  have huu : u * uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hu
  obtain ⟨U, hUU, hUU', -, c, hc, hYc⟩ := exists_unitary_gauge_of_symmetry hA hNorm hΛpos
    hΛfix huu (X := X) one_ne_zero fun i => by rw [one_smul, hrel i]; rfl
  change Y = c • U at hYc
  -- The square of the gauge commutes with every letter, hence is scalar.
  have hsq : ∀ i, Y * Y * A i * (V' * V') = A i := by
    intro i
    calc Y * Y * A i * (V' * V') = Y * (Y * A i * V') * V' := by
          simp only [Matrix.mul_assoc]
      _ = ∑ j, u i j • (Y * A j * V') := by
          rw [← hrel i, Matrix.mul_sum, Matrix.sum_mul]
          simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = ∑ j, u i j • ∑ k, u j k • A k := by simp only [hrel]
      _ = ∑ k, (u * u) i k • A k := by
          simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
          exact Finset.sum_comm
      _ = A i := by
          rw [hu2]
          simp [Matrix.one_apply]
  have hcomm : ∀ i, Commute (Y * Y) (A i) := by
    intro i
    calc Y * Y * A i = Y * Y * A i * (V' * V') * (Y * Y) := by
          rw [Matrix.mul_assoc (Y * Y * A i), show V' * V' * (Y * Y) = 1 by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc V' Y, hV'Y, Matrix.one_mul, hV'Y],
            Matrix.mul_one]
      _ = A i * (Y * Y) := by rw [hsq i]
  have hcommAll : ∀ Z ∈ Submodule.span ℂ (Set.range A), Commute (Y * Y) Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hcomm i
    | zero => exact Commute.zero_right _
    | add x y _ _ hx hy => exact hx.add_right hy
    | smul a x _ hx => exact hx.smul_right a
  obtain ⟨κ, hκ⟩ := Matrix.mem_range_scalar_of_commute_single (M := Y * Y)
    fun a b _ => (hcommAll _ (by rw [hA.span_eq_top]; trivial)).symm
  -- A unitary with scalar square is a scalar multiple of a Hermitian matrix.
  set ℓ := (c * c)⁻¹ * κ with hℓdef
  have hUsq : U * U = ℓ • 1 := by
    have h1 : (c * c) • (U * U) = κ • 1 := by
      rw [← smul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hYc, ← hκ,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hℓdef, ← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
  have hUH : ℓ • Uᴴ = U := by
    calc ℓ • Uᴴ = Uᴴ * (U * U) := by rw [hUsq, Matrix.mul_smul, Matrix.mul_one]
      _ = U := by rw [← Matrix.mul_assoc, hUU', Matrix.one_mul]
  have hUne : U ≠ 0 := by
    intro hU0
    have : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by rw [← hUU, hU0, Matrix.zero_mul]
    exact one_ne_zero (congrFun (congrFun this ⟨0, hD⟩) ⟨0, hD⟩)
  have hℓ : ℓ * star ℓ = 1 := by
    have h2 : star ℓ • U = Uᴴ := by
      have := congrArg Matrix.conjTranspose hUH
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose] at this
      exact this
    have h3 : (ℓ * star ℓ) • U = U := by rw [← smul_smul, h2, hUH]
    by_contra hne
    apply hUne
    have h4 : (ℓ * star ℓ - 1) • U = 0 := by rw [sub_smul, h3, one_smul, sub_self]
    exact (smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨s, hs, hsℓ⟩ : ∃ s : ℂ, s ≠ 0 ∧ star s = s * ℓ := by
    by_cases hℓ1 : ℓ = -1
    · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
      rw [hℓ1, mul_neg_one]
      exact Complex.conj_I
    · refine ⟨1 + star ℓ, fun h0 => hℓ1 ?_, ?_⟩
      · have := congrArg star h0
        rw [star_add, star_one, star_star, star_zero] at this
        linear_combination this
      · rw [star_add, star_one, star_star, add_mul, one_mul, mul_comm, hℓ, add_comm]
  refine ⟨s * c⁻¹, mul_ne_zero hs (inv_ne_zero hc), ?_⟩
  have hsY : (s * c⁻¹) • Y = s • U := by
    rw [hYc, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [hsY, Matrix.IsHermitian, Matrix.conjTranspose_smul, hsℓ, ← smul_smul, hUH]

end Canonical

section OnSite

variable (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : MPOTensor d₀ 1) (T₁ : MPOTensor d₁ 1)
  (V₀ : Fin 1 → Matrix (Fin D₀) (Fin (1 * D₀)) ℂ)
  (V₁ : Fin 1 → Matrix (Fin D₁) (Fin (1 * D₁)) ℂ)
  (W₀ : Fin 1 → Matrix (Fin (1 * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin 1 → Matrix (Fin (1 * D₁)) (Fin D₁) ℂ)

/-- **Adjoint closure for Hermitian action gauges.** Let the endpoint
operators be on-site with Hermitian on-site matrices `u_p`, as for unitary
`ℤ₂` symmetries, and let both action gauges be proportional to Hermitian
matrices. Then at every length the adjoint of every boundary operator of the
common operator of the arbitrary-alphabet mixed path is again a boundary
operator of it. Injectivity is not needed. Source: arXiv:2203.12563,
lines 1600–1631, and `docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`,
paragraph "When closure holds". -/
theorem exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq
    (hu₀ : (physicalSlice T₀ 0 0).IsHermitian) (hu₁ : (physicalSlice T₁ 0 0).IsHermitian)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin 1 => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin 1 => A₁) V₁ W₁)
    (hY₀ : ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W₀ 0)).IsHermitian)
    (hY₁ : ∃ c : ℂ, c ≠ 0 ∧ (c • bondOneActionGauge (W₁ 0)).IsHermitian)
    (X : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) (L : ℕ) :
    ∃ Y : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ,
      (mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X L)ᴴ =
        mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) Y L := by
  obtain ⟨c₀, hc₀, hY₀⟩ := hY₀
  obtain ⟨c₁, hc₁, hY₁⟩ := hY₁
  obtain ⟨ω₀, hω₀, hW₀, hV₀⟩ :=
    exists_star_synthesis_analysis_of_isHermitian (h₀.retract 0) hc₀ hY₀
  obtain ⟨ω₁, hω₁, hW₁, hV₁⟩ :=
    exists_star_synthesis_analysis_of_isHermitian (h₁.retract 0) hc₁ hY₁
  have hP₀ : physicalAdjointTensor (polarSupportMPO A₀ T₀) = polarSupportMPO A₀ T₀ := by
    rw [polarSupportMPO, physicalAdjointTensor_changePhysicalBasis,
      physicalAdjointTensor_eq_self_of_isHermitian hu₀]
  have hP₁ : physicalAdjointTensor (polarSupportMPO A₁ T₁) = polarSupportMPO A₁ T₁ := by
    rw [polarSupportMPO, physicalAdjointTensor_changePhysicalBasis,
      physicalAdjointTensor_eq_self_of_isHermitian hu₁]
  set c := ω₁ * ω₀⁻¹ with hcdef
  have hc : c ≠ 0 := mul_ne_zero hω₁ (inv_ne_zero hω₀)
  have hmix := physicalAdjointTensor_mixedEndpointMPO_apply (V₀ := V₀) (V₁ := V₁)
    (W₀ := W₀) (W₁ := W₁) hP₀ hP₁
    (fun μ ↦ by obtain rfl := Subsingleton.elim μ 0; exact hW₀)
    (fun μ ↦ by obtain rfl := Subsingleton.elim μ 0; exact hW₁)
    (fun μ ↦ by obtain rfl := Subsingleton.elim μ 0; exact hV₀)
    (fun μ ↦ by obtain rfl := Subsingleton.elim μ 0; exact hV₁)
    (c := c) (by rw [hcdef]; field_simp) rfl
  set g := mixedEndpointBondWeight 1 1 c
  have hadj : ∀ i j β α,
      physicalAdjointTensor (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) (i, j) β α =
        g β / g α * arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ (i, j) β α := by
    intro i j β α
    rw [arbitraryPhysicalMixedMPO, physicalAdjointTensor_changePhysicalBasis]
    exact changePhysicalBasis_apply_of_apply_eq_mul (fun β α ↦ g β / g α) hmix _ i j β α
  refine ⟨Matrix.diagonal g⁻¹ * X.map (starRingEnd ℂ) * Matrix.diagonal g, ?_⟩
  rw [conjTranspose_mpoWithBoundary,
    mpoWithBoundary_eq_of_apply_eq_div_mul g (mixedEndpointBondWeight_ne_zero hc) hadj]

end OnSite

end MPSTensor.MPOSymmetry
