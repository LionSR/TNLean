/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedParentCommutation

/-!
# Adjoint closure of the mixed boundary ranges for unitary group symmetries

Let a group `G` act at both endpoints of the arbitrary-alphabet mixed path by
unitary on-site representations `u_{p,g}`, with one-dimensional operator
bonds and action multiplicity one, and write `O_g` for the common operator
of the label `g`. Suppose every action gauge `Y_{p,g}`, the synthesis map
read as a square matrix, is a nonzero multiple of a unitary matrix, and the
endpoint tensors are injective. Then the adjoint of every boundary operator
of `O_g` is a boundary operator of `O_{g⁻¹}`, at every length: the union
of the boundary ranges over all labels is closed under the adjoint. The
range of one label need not be: for a label with `u_g²` not scalar its
adjoint fails already in the sector of the first endpoint. Hence the
mixed-path parent, which preserves the union, commutes with every `O_g`.

The proof rests on two facts. First, by injectivity the gauges of `g` and
`g⁻¹` multiply to a scalar, so `Y_{p,g⁻¹}` is a multiple of `Y_{p,g}⁻¹`, and
for a multiple of a unitary `Y_{p,g}⁻¹` is a multiple of `Y_{p,g}ᴴ`. Second,
the physical adjoint of `O_g` is then the common operator of the inverse
label, conjugated by a diagonal bond similarity.

The gauge condition holds for endpoint tensors in canonical form: for an
injective tensor with `E(1) = 1` and a positive definite fixed point of the
adjoint transfer map, the gauge of a unitary on-site symmetry is a nonzero
multiple of a unitary (arXiv:0802.0447, Lemma 1 and Theorem 2).

**Scope restriction (finite group, unitary on-site endpoints, unitary action gauges):**
the endpoint symmetries are unitary on-site representations of a group, the
finite groups of the source being the case of interest (finiteness itself is
not used), and every action gauge is assumed to be a nonzero multiple of a
unitary matrix. The source imposes no gauge condition, and closure fails
without it. See `docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`,
section "Unitary on-site endpoints", paragraphs "Other groups" and
"Unitary groups".

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, Section 5,
`REsubmission.tex`, lines 1600–1631 (the crossed blocks) and
lines 1687–1692 (the canonical parent).
-/

open scoped Matrix BigOperators ComplexOrder

open ManyBody

namespace MPOTensor

variable {d : ℕ}

/-- A tensor with one-dimensional bond has physical adjoint `N` when the
conjugate transpose of its on-site matrix is the on-site matrix of `N`. -/
theorem physicalAdjointTensor_eq_of_conjTranspose_physicalSlice {M N : MPOTensor d 1}
    (h : (physicalSlice M 0 0)ᴴ = physicalSlice N 0 0) : physicalAdjointTensor M = N := by
  ext i j β α
  rw [Subsingleton.elim β 0, Subsingleton.elim α 0, physicalAdjointTensor_apply]
  exact congrFun (congrFun h i) j

end MPOTensor

namespace MPSTensor.MPOSymmetry

open MPOTensor

variable {d₀ d₁ D₀ D₁ : ℕ}

/-- If the conjugate transpose of the action gauge of one on-site action is a
multiple `ω` of the action gauge of another, then conjugating the entries of
the first synthesis map, under transposition of the state indices, gives `ω`
times the second, and the analysis maps are related in the same way by
`ω⁻¹`. -/
theorem star_synthesis_analysis_of_conjTranspose_eq_smul {D : ℕ}
    {V V' : Matrix (Fin D) (Fin (1 * D)) ℂ} {W W' : Matrix (Fin (1 * D)) (Fin D) ℂ}
    (hVW : V * W = 1) (hVW' : V' * W' = 1) {ω : ℂ} (hω : ω ≠ 0)
    (hY : (bondOneActionGauge W)ᴴ = ω • bondOneActionGauge W') :
    (∀ α r k, star (W (finProdFinEquiv (α, r)) k) = ω * W' (finProdFinEquiv (α, k)) r) ∧
      ∀ β l s, star (V l (finProdFinEquiv (β, s))) = ω⁻¹ * V' s (finProdFinEquiv (β, l)) := by
  set Y := bondOneActionGauge W with hYdef
  set Y' := bondOneActionGauge W' with hY'def
  set U := bondOneActionAnalysis V with hUdef
  set U' := bondOneActionAnalysis V' with hU'def
  have hYU : Y * U = 1 := mul_eq_one_comm.mp (bondOneActionAnalysis_mul_bondOneActionGauge hVW)
  have hYU' : Y' * U' = 1 :=
    mul_eq_one_comm.mp (bondOneActionAnalysis_mul_bondOneActionGauge hVW')
  have hUH : Uᴴ = ω⁻¹ • U' := by
    have h1 : Uᴴ * Yᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hYU, Matrix.conjTranspose_one]
    rw [hY, Matrix.mul_smul] at h1
    calc Uᴴ = Uᴴ * (Y' * U') := by rw [hYU', Matrix.mul_one]
      _ = ω⁻¹ • (ω • (Uᴴ * Y')) * U' := by
          rw [smul_smul, inv_mul_cancel₀ hω, one_smul, Matrix.mul_assoc]
      _ = ω⁻¹ • U' := by rw [h1, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨fun α r k ↦ ?_, fun β l s ↦ ?_⟩
  · rw [Subsingleton.elim α 0]
    have h := congrFun (congrFun hY k) r
    simpa [hYdef, hY'def, bondOneActionGauge, Matrix.conjTranspose_apply] using h
  · rw [Subsingleton.elim β 0]
    have h := congrFun (congrFun hUH s) l
    simpa [hUdef, hU'def, bondOneActionAnalysis, Matrix.conjTranspose_apply] using h

section TwoLabels

variable (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)

/-- **Adjoint of a boundary operator of the common operator.** Let the
endpoint operators of two labels be on-site, with the conjugate transposes of
the on-site matrices of the first label equal to those of the second, and the
conjugate transposes of the action gauges of the first label nonzero
multiples of those of the second. Then at every length the adjoint of every
boundary operator of the common operator of the first label is a boundary
operator of the common operator of the second. Injectivity is not needed.
Source: arXiv:2203.12563, lines 1600–1631, and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"Unitary groups". -/
theorem exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq_of_conjTranspose
    {T₀ T₀' : MPOTensor d₀ 1} {T₁ T₁' : MPOTensor d₁ 1}
    {V₀ V₀' : Fin 1 → Matrix (Fin D₀) (Fin (1 * D₀)) ℂ}
    {V₁ V₁' : Fin 1 → Matrix (Fin D₁) (Fin (1 * D₁)) ℂ}
    {W₀ W₀' : Fin 1 → Matrix (Fin (1 * D₀)) (Fin D₀) ℂ}
    {W₁ W₁' : Fin 1 → Matrix (Fin (1 * D₁)) (Fin D₁) ℂ}
    (hu₀ : (physicalSlice T₀ 0 0)ᴴ = physicalSlice T₀' 0 0)
    (hu₁ : (physicalSlice T₁ 0 0)ᴴ = physicalSlice T₁' 0 0)
    (hVW₀ : V₀ 0 * W₀ 0 = 1) (hVW₀' : V₀' 0 * W₀' 0 = 1)
    (hVW₁ : V₁ 0 * W₁ 0 = 1) (hVW₁' : V₁' 0 * W₁' 0 = 1)
    (hY₀ : ∃ ω : ℂ, ω ≠ 0 ∧ (bondOneActionGauge (W₀ 0))ᴴ = ω • bondOneActionGauge (W₀' 0))
    (hY₁ : ∃ ω : ℂ, ω ≠ 0 ∧ (bondOneActionGauge (W₁ 0))ᴴ = ω • bondOneActionGauge (W₁' 0))
    (X : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) (L : ℕ) :
    ∃ Y : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ,
      (mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) X L)ᴴ =
        mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ T₀' T₁' V₀' V₁' W₀' W₁') Y L := by
  obtain ⟨ω₀, hω₀, hY₀⟩ := hY₀
  obtain ⟨ω₁, hω₁, hY₁⟩ := hY₁
  obtain ⟨hW₀, hV₀⟩ := star_synthesis_analysis_of_conjTranspose_eq_smul hVW₀ hVW₀' hω₀ hY₀
  obtain ⟨hW₁, hV₁⟩ := star_synthesis_analysis_of_conjTranspose_eq_smul hVW₁ hVW₁' hω₁ hY₁
  have hP₀ : physicalAdjointTensor (polarSupportMPO A₀ T₀) = polarSupportMPO A₀ T₀' := by
    rw [polarSupportMPO, polarSupportMPO, physicalAdjointTensor_changePhysicalBasis,
      physicalAdjointTensor_eq_of_conjTranspose_physicalSlice hu₀]
  have hP₁ : physicalAdjointTensor (polarSupportMPO A₁ T₁) = polarSupportMPO A₁ T₁' := by
    rw [polarSupportMPO, polarSupportMPO, physicalAdjointTensor_changePhysicalBasis,
      physicalAdjointTensor_eq_of_conjTranspose_physicalSlice hu₁]
  set c := ω₁ * ω₀⁻¹ with hcdef
  have hc : c ≠ 0 := mul_ne_zero hω₁ (inv_ne_zero hω₀)
  have hmix := physicalAdjointTensor_mixedEndpointMPO_apply (V₀ := V₀) (V₁ := V₁)
    (W₀ := W₀) (W₁ := W₁) (V₀' := V₀') (V₁' := V₁') (W₀' := W₀') (W₁' := W₁') hP₀ hP₁
    (fun μ ↦ by obtain rfl := Subsingleton.elim μ 0; exact hW₀)
    (fun μ ↦ by obtain rfl := Subsingleton.elim μ 0; exact hW₁)
    (fun μ ↦ by obtain rfl := Subsingleton.elim μ 0; exact hV₀)
    (fun μ ↦ by obtain rfl := Subsingleton.elim μ 0; exact hV₁)
    (c := c) (by rw [hcdef]; field_simp) rfl
  set g := mixedEndpointBondWeight 1 1 c
  have hadj : ∀ i j β α,
      physicalAdjointTensor (arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁) i j β α =
        g β / g α * arbitraryPhysicalMixedMPO A₀ A₁ T₀' T₁' V₀' V₁' W₀' W₁' i j β α := by
    intro i j β α
    rw [arbitraryPhysicalMixedMPO, arbitraryPhysicalMixedMPO,
      physicalAdjointTensor_changePhysicalBasis]
    exact changePhysicalBasis_apply_of_apply_eq_mul (fun β α ↦ g β / g α) hmix _ i j β α
  refine ⟨Matrix.diagonal g⁻¹ * X.map (starRingEnd ℂ) * Matrix.diagonal g, ?_⟩
  rw [conjTranspose_mpoWithBoundary,
    mpoWithBoundary_eq_of_apply_eq_div_mul g (mixedEndpointBondWeight_ne_zero hc) hadj]

end TwoLabels

section Gauges

variable {d D : ℕ}

/-- The action gauges of two on-site actions on an injective tensor whose
on-site matrices are mutually inverse multiply to a scalar: their product
commutes with every letter. -/
theorem exists_bondOneActionGauge_mul_eq_smul_one {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) {T T' : MPOTensor d 1}
    (hu : physicalSlice T' 0 0 * physicalSlice T 0 0 = 1)
    {V V' : Fin 1 → Matrix (Fin D) (Fin (1 * D)) ℂ}
    {W W' : Fin 1 → Matrix (Fin (1 * D)) (Fin D) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A) (fun _ : Fin 1 => A) V W)
    (h' : IsBiorthogonalDecomposition (MPOTensor.actTensor T' A) (fun _ : Fin 1 => A) V' W') :
    ∃ κ : ℂ, bondOneActionGauge (W 0) * bondOneActionGauge (W' 0) = κ • 1 := by
  classical
  set u := physicalSlice T 0 0 with hudef
  set u' := physicalSlice T' 0 0 with hu'def
  set Y := bondOneActionGauge (W 0) with hYdef
  set Y' := bondOneActionGauge (W' 0) with hY'def
  set U := bondOneActionAnalysis (V 0) with hUdef
  set U' := bondOneActionAnalysis (V' 0) with hU'def
  have hUY : U * Y = 1 := bondOneActionAnalysis_mul_bondOneActionGauge (h.retract 0)
  have hU'Y' : U' * Y' = 1 := bondOneActionAnalysis_mul_bondOneActionGauge (h'.retract 0)
  have hrel : ∀ i, ∑ j, u i j • A j = Y * A i * U :=
    sum_smul_eq_bondOneActionGauge_mul_mul h
  have hrel' : ∀ i, ∑ j, u' i j • A j = Y' * A i * U' :=
    sum_smul_eq_bondOneActionGauge_mul_mul h'
  have hconj : ∀ i, Y * Y' * A i * (U' * U) = A i := by
    intro i
    calc Y * Y' * A i * (U' * U) = Y * (Y' * A i * U') * U := by
          simp only [Matrix.mul_assoc]
      _ = ∑ j, u' i j • (Y * A j * U) := by
          rw [← hrel' i, Matrix.mul_sum, Matrix.sum_mul]
          simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = ∑ j, u' i j • ∑ k, u j k • A k := by simp only [hrel]
      _ = ∑ k, (u' * u) i k • A k := by
          simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
          exact Finset.sum_comm
      _ = A i := by
          rw [hu]
          simp [Matrix.one_apply]
  have hcomm : ∀ i, Commute (Y * Y') (A i) := by
    intro i
    calc Y * Y' * A i = Y * Y' * A i * (U' * U) * (Y * Y') := by
          rw [Matrix.mul_assoc (Y * Y' * A i), show U' * U * (Y * Y') = 1 by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc U Y, hUY, Matrix.one_mul, hU'Y'],
            Matrix.mul_one]
      _ = A i * (Y * Y') := by rw [hconj i]
  have hcommAll : ∀ Z ∈ Submodule.span ℂ (Set.range A), Commute (Y * Y') Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hcomm i
    | zero => exact Commute.zero_right _
    | add x y _ _ hx hy => exact hx.add_right hy
    | smul a x _ hx => exact hx.smul_right a
  obtain ⟨κ, hκ⟩ := Matrix.mem_range_scalar_of_commute_single (M := Y * Y')
    fun a b _ => (hcommAll _ (by rw [hA.span_eq_top]; trivial)).symm
  exact ⟨κ, by rw [← hκ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

/-- **Unitary action gauges of inverse labels.** On an injective tensor, let
two on-site actions have mutually inverse on-site matrices, and let the
action gauge `Y` of the first be a nonzero multiple of a unitary matrix.
Then `Yᴴ` is a nonzero multiple of the action gauge of the second. Source:
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"Unitary groups". -/
theorem exists_conjTranspose_bondOneActionGauge_eq_smul_of_mem_unitaryGroup
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) {T T' : MPOTensor d 1}
    (hu : physicalSlice T' 0 0 * physicalSlice T 0 0 = 1)
    {V V' : Fin 1 → Matrix (Fin D) (Fin (1 * D)) ℂ}
    {W W' : Fin 1 → Matrix (Fin (1 * D)) (Fin D) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A) (fun _ : Fin 1 => A) V W)
    (h' : IsBiorthogonalDecomposition (MPOTensor.actTensor T' A) (fun _ : Fin 1 => A) V' W')
    (hY : ∃ c : ℂ, c ≠ 0 ∧ c • bondOneActionGauge (W 0) ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    ∃ ω : ℂ, ω ≠ 0 ∧ (bondOneActionGauge (W 0))ᴴ = ω • bondOneActionGauge (W' 0) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    exact ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
  obtain ⟨c, hc, hcY⟩ := hY
  obtain ⟨κ, hκ⟩ := exists_bondOneActionGauge_mul_eq_smul_one hA hu h h'
  set Y := bondOneActionGauge (W 0) with hYdef
  set Y' := bondOneActionGauge (W' 0) with hY'def
  set U := bondOneActionAnalysis (V 0) with hUdef
  have hUY : U * Y = 1 := bondOneActionAnalysis_mul_bondOneActionGauge (h.retract 0)
  have hYU : Y * U = 1 := mul_eq_one_comm.mp hUY
  have hU'Y' : bondOneActionAnalysis (V' 0) * Y' = 1 :=
    bondOneActionAnalysis_mul_bondOneActionGauge (h'.retract 0)
  have hs : star c * c ≠ 0 := mul_ne_zero (star_ne_zero.mpr hc) hc
  have h1 : (star c * c) • (Yᴴ * Y) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hcY
    rwa [star_smul, Matrix.star_eq_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul] at this
  have hYH : Yᴴ = (star c * c)⁻¹ • U := by
    calc Yᴴ = Yᴴ * (Y * U) := by rw [hYU, Matrix.mul_one]
      _ = (star c * c)⁻¹ • ((star c * c) • (Yᴴ * Y)) * U := by
          rw [smul_smul, inv_mul_cancel₀ hs, one_smul, Matrix.mul_assoc]
      _ = (star c * c)⁻¹ • U := by rw [h1, Matrix.smul_mul, Matrix.one_mul]
  have hY' : Y' = κ • U := by
    calc Y' = U * (Y * Y') := by rw [← Matrix.mul_assoc, hUY, Matrix.one_mul]
      _ = κ • U := by rw [hκ, Matrix.mul_smul, Matrix.mul_one]
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
      rw [← hU'Y', hY', zero_smul, Matrix.mul_zero]
    exact one_ne_zero (congrFun (congrFun this ⟨0, hD⟩) ⟨0, hD⟩)
  refine ⟨(star c * c)⁻¹ * κ⁻¹, mul_ne_zero (inv_ne_zero hs) (inv_ne_zero hκ0), ?_⟩
  rw [hYH, hY', smul_smul, mul_assoc, inv_mul_cancel₀ hκ0, mul_one]

/-- **Unitary action gauges in canonical form.** Let `A` be injective with
`E(1) = 1` and a positive definite fixed point of the adjoint transfer map,
and let an on-site unitary act on `A`. Then the action gauge is a nonzero
multiple of a unitary matrix, by Pérez-García–Wolf–Sanz–Verstraete–Cirac,
arXiv:0802.0447, Lemma 1 and Theorem 2. -/
theorem exists_smul_bondOneActionGauge_mem_unitaryGroup
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    {Λ : Matrix (Fin D) (Fin D) ℂ} (hΛpos : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ) {T : MPOTensor d 1}
    (hu : physicalSlice T 0 0 ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {V : Fin 1 → Matrix (Fin D) (Fin (1 * D)) ℂ} {W : Fin 1 → Matrix (Fin (1 * D)) (Fin D) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A) (fun _ : Fin 1 => A) V W) :
    ∃ c : ℂ, c ≠ 0 ∧ c • bondOneActionGauge (W 0) ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  set Y := bondOneActionGauge (W 0) with hYdef
  set U := bondOneActionAnalysis (V 0) with hUdef
  have hUY : U * Y = 1 := bondOneActionAnalysis_mul_bondOneActionGauge (h.retract 0)
  have hYU : Y * U = 1 := mul_eq_one_comm.mp hUY
  let X : GL (Fin D) ℂ := ⟨Y, U, hYU, hUY⟩
  have huu : physicalSlice T 0 0 * (physicalSlice T 0 0)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hu
  obtain ⟨Z, -, hZZ, -, c, hc, hYc⟩ := exists_unitary_gauge_of_symmetry hA hNorm hΛpos
    hΛfix huu (X := X) one_ne_zero fun i => by
      rw [one_smul, sum_smul_eq_bondOneActionGauge_mul_mul h i]; rfl
  change Y = c • Z at hYc
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [hYc, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  exact hZZ

end Gauges

section Group

variable {G : Type*} [Group G]
  (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (T₀ : G → MPOTensor d₀ 1) (T₁ : G → MPOTensor d₁ 1)
  (V₀ : G → Fin 1 → Matrix (Fin D₀) (Fin (1 * D₀)) ℂ)
  (V₁ : G → Fin 1 → Matrix (Fin D₁) (Fin (1 * D₁)) ℂ)
  (W₀ : G → Fin 1 → Matrix (Fin (1 * D₀)) (Fin D₀) ℂ)
  (W₁ : G → Fin 1 → Matrix (Fin (1 * D₁)) (Fin D₁) ℂ)

/-- The on-site matrices of a unitary representation: the conjugate transpose
of the matrix of `g` is the matrix of `g⁻¹`, and the two multiply to the
identity. -/
theorem conjTranspose_physicalSlice_eq_inv {d : ℕ} {T : G → MPOTensor d 1}
    (u : G →* Matrix.unitaryGroup (Fin d) ℂ) (hT : ∀ g, physicalSlice (T g) 0 0 = u g)
    (g : G) :
    (physicalSlice (T g) 0 0)ᴴ = physicalSlice (T g⁻¹) 0 0 ∧
      physicalSlice (T g⁻¹) 0 0 * physicalSlice (T g) 0 0 = 1 := by
  have hinv : ((u g⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) =
      star (u g : Matrix (Fin d) (Fin d) ℂ) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  rw [hT, hT, hinv, ← Matrix.star_eq_conjTranspose]
  exact ⟨rfl, Unitary.coe_star_mul_self _⟩

/-- **Adjoint closure of the union of the boundary ranges.** Let a group act
at both endpoints by unitary on-site representations `u_p`, on injective
endpoint tensors, and let every action gauge be a nonzero multiple of a
unitary matrix. Then at every length the adjoint of every boundary operator
of the common operator of `g` is a boundary operator of the common operator
of `g⁻¹`. Source: arXiv:2203.12563, lines 1600–1631, and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"Unitary groups". -/
theorem exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_inv_eq
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (u₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ) (u₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (hT₀ : ∀ g, physicalSlice (T₀ g) 0 0 = u₀ g) (hT₁ : ∀ g, physicalSlice (T₁ g) 0 0 = u₁ g)
    (h₀ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₀ g) A₀)
      (fun _ : Fin 1 => A₀) (V₀ g) (W₀ g))
    (h₁ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₁ g) A₁)
      (fun _ : Fin 1 => A₁) (V₁ g) (W₁ g))
    (hY₀ : ∀ g, ∃ c : ℂ, c ≠ 0 ∧
      c • bondOneActionGauge (W₀ g 0) ∈ Matrix.unitaryGroup (Fin D₀) ℂ)
    (hY₁ : ∀ g, ∃ c : ℂ, c ≠ 0 ∧
      c • bondOneActionGauge (W₁ g 0) ∈ Matrix.unitaryGroup (Fin D₁) ℂ)
    (g : G) (X : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) (L : ℕ) :
    ∃ Y : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ,
      (mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ (T₀ g) (T₁ g) (V₀ g) (V₁ g)
          (W₀ g) (W₁ g)) X L)ᴴ =
        mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ (T₀ g⁻¹) (T₁ g⁻¹) (V₀ g⁻¹)
          (V₁ g⁻¹) (W₀ g⁻¹) (W₁ g⁻¹)) Y L := by
  obtain ⟨hu₀, hu₀'⟩ := conjTranspose_physicalSlice_eq_inv u₀ hT₀ g
  obtain ⟨hu₁, hu₁'⟩ := conjTranspose_physicalSlice_eq_inv u₁ hT₁ g
  exact exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_eq_of_conjTranspose
    A₀ A₁ hu₀ hu₁ ((h₀ g).retract 0) ((h₀ g⁻¹).retract 0) ((h₁ g).retract 0)
    ((h₁ g⁻¹).retract 0)
    (exists_conjTranspose_bondOneActionGauge_eq_smul_of_mem_unitaryGroup hInj₀ hu₀'
      (h₀ g) (h₀ g⁻¹) (hY₀ g))
    (exists_conjTranspose_bondOneActionGauge_eq_smul_of_mem_unitaryGroup hInj₁ hu₁'
      (h₁ g) (h₁ g⁻¹) (hY₁ g)) X L

/-- On the closed interval, the enlarged mixed interaction commutes with every
two-site boundary operator of the common operator of every label `g`, for
unitary on-site endpoint representations of a group whose action gauges are
nonzero multiples of unitary matrices. Source: arXiv:2203.12563, Section 5,
lines 1687–1692, and `docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`,
paragraph "Unitary groups". -/
theorem arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_unitary
    [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (u₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ) (u₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (hT₀ : ∀ g, physicalSlice (T₀ g) 0 0 = u₀ g) (hT₁ : ∀ g, physicalSlice (T₁ g) 0 0 = u₁ g)
    (h₀ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₀ g) A₀)
      (fun _ : Fin 1 => A₀) (V₀ g) (W₀ g))
    (h₁ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₁ g) A₁)
      (fun _ : Fin 1 => A₁) (V₁ g) (W₁ g))
    (hY₀ : ∀ g, ∃ c : ℂ, c ≠ 0 ∧
      c • bondOneActionGauge (W₀ g 0) ∈ Matrix.unitaryGroup (Fin D₀) ℂ)
    (hY₁ : ∀ g, ∃ c : ℂ, c ≠ 0 ∧
      c • bondOneActionGauge (W₁ g 0) ∈ Matrix.unitaryGroup (Fin D₁) ℂ)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (g : G) (X : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) :
    Commute (arbitraryPhysicalMixedInteraction A₀ A₁ γ)
      (mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ (T₀ g) (T₁ g) (V₀ g) (V₁ g)
        (W₀ g) (W₁ g)) X 2) := by
  refine arbitraryPhysicalMixedInteraction_commute_of_forall_mem_Ioo A₀ A₁ hInj₀ hInj₁
    (fun t ht ↦ ?_) hγ
  rw [arbitraryPhysicalMixedInteraction_eq_parent_of_mem_Ioo A₀ A₁ ht]
  exact parentInteraction_matrix_commute_mpoWithBoundary_of_forall_isBoundaryCompatible
    (T := fun g ↦ arbitraryPhysicalMixedMPO A₀ A₁ (T₀ g) (T₁ g) (V₀ g) (V₁ g) (W₀ g) (W₁ g))
    (fun g ↦ isBoundaryCompatible_arbitraryPhysicalMixedInterpolation A₀ A₁ (T₀ g) (T₁ g)
      (V₀ g) (V₁ g) (W₀ g) (W₁ g) (h₀ g) (h₁ g) t) (by norm_num)
    (fun g X ↦ ⟨g⁻¹, exists_conjTranspose_mpoWithBoundary_arbitraryPhysicalMixedMPO_inv_eq
      A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ u₀ u₁ hT₀ hT₁ h₀ h₁ hY₀ hY₁ g X 2⟩) g X

/-- On every periodic ring of length at least two and at every parameter of
the closed interval, the enlarged mixed path Hamiltonian commutes with every
periodic boundary operator, with boundary commuting with the letters, of the
common operator of every label, for unitary on-site endpoint representations
of a group whose action gauges are nonzero multiples of unitary matrices.
Source: arXiv:2203.12563, Section 5, lines 1582 and 1687–1692, and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"Unitary groups". -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_unitary
    {N : ℕ} [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (u₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ) (u₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (hT₀ : ∀ g, physicalSlice (T₀ g) 0 0 = u₀ g) (hT₁ : ∀ g, physicalSlice (T₁ g) 0 0 = u₁ g)
    (h₀ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₀ g) A₀)
      (fun _ : Fin 1 => A₀) (V₀ g) (W₀ g))
    (h₁ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₁ g) A₁)
      (fun _ : Fin 1 => A₁) (V₁ g) (W₁ g))
    (hY₀ : ∀ g, ∃ c : ℂ, c ≠ 0 ∧
      c • bondOneActionGauge (W₀ g 0) ∈ Matrix.unitaryGroup (Fin D₀) ℂ)
    (hY₁ : ∀ g, ∃ c : ℂ, c ≠ 0 ∧
      c • bondOneActionGauge (W₁ g 0) ∈ Matrix.unitaryGroup (Fin D₁) ℂ)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) (g : G)
    {X : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ}
    (hX : X ∈ commutingBoundaryAlgebra
      (arbitraryPhysicalMixedMPO A₀ A₁ (T₀ g) (T₁ g) (V₀ g) (V₁ g) (W₀ g) (W₁ g))) :
    Commute (Interaction.translationInvariant hN
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (mpoWithBoundary (arbitraryPhysicalMixedMPO A₀ A₁ (T₀ g) (T₁ g) (V₀ g) (V₁ g)
        (W₀ g) (W₁ g)) X N) :=
  Commute.sum_left _ _ _ fun i _ =>
    placeAlong_ringWindow_commute_mpoWithBoundary _ hN i _
      (arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_unitary
        A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ u₀ u₁ hT₀ hT₁ h₀ h₁ hY₀ hY₁ hγ g) hX

/-- On every periodic ring of length at least two and at every parameter of
the closed interval, the enlarged mixed path Hamiltonian commutes with the
periodic common operator of every label, for unitary on-site endpoint
representations of a group whose action gauges are nonzero multiples of
unitary matrices. Source: arXiv:2203.12563, Section 5, lines 1582 and
1687–1692, and `docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`,
paragraph "Unitary groups". -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo_of_unitary
    {N : ℕ} [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (u₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ) (u₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (hT₀ : ∀ g, physicalSlice (T₀ g) 0 0 = u₀ g) (hT₁ : ∀ g, physicalSlice (T₁ g) 0 0 = u₁ g)
    (h₀ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₀ g) A₀)
      (fun _ : Fin 1 => A₀) (V₀ g) (W₀ g))
    (h₁ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₁ g) A₁)
      (fun _ : Fin 1 => A₁) (V₁ g) (W₁ g))
    (hY₀ : ∀ g, ∃ c : ℂ, c ≠ 0 ∧
      c • bondOneActionGauge (W₀ g 0) ∈ Matrix.unitaryGroup (Fin D₀) ℂ)
    (hY₁ : ∀ g, ∃ c : ℂ, c ≠ 0 ∧
      c • bondOneActionGauge (W₁ g 0) ∈ Matrix.unitaryGroup (Fin D₁) ℂ)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) (g : G) :
    Commute (Interaction.translationInvariant hN
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (mpo (arbitraryPhysicalMixedMPO A₀ A₁ (T₀ g) (T₁ g) (V₀ g) (V₁ g) (W₀ g) (W₁ g)) N) := by
  rw [← mpoWithBoundary_one]
  exact hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpoWithBoundary_of_unitary
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ u₀ u₁ hT₀ hT₁ h₀ h₁ hY₀ hY₁ hγ hN g
    (Subalgebra.one_mem _)

/-- **Unitary group endpoints in canonical form.** Let both endpoint tensors
be injective with `E(1) = 1` and a positive definite fixed point of the
adjoint transfer map, and let a group act on them by unitary on-site
representations. Then, on every periodic ring of length at least two and at
every parameter of the closed interval, the enlarged mixed path Hamiltonian
commutes with the periodic common operator of every label. Source:
arXiv:2203.12563, Section 5, lines 1582 and 1687–1692; arXiv:0802.0447,
Lemma 1 and Theorem 2; and
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`, paragraph
"Unitary groups". -/
theorem hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo_of_unitary_canonical
    {N : ℕ} [NeZero D₀] [NeZero D₁]
    (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
    (hNorm₀ : Kraus.transferMap A₀ 1 = 1) (hNorm₁ : Kraus.transferMap A₁ 1 = 1)
    {Λ₀ : Matrix (Fin D₀) (Fin D₀) ℂ} {Λ₁ : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hΛ₀ : Λ₀.PosDef) (hΛ₁ : Λ₁.PosDef)
    (hΛfix₀ : Kraus.transferMap (fun i => (A₀ i)ᴴ) Λ₀ = Λ₀)
    (hΛfix₁ : Kraus.transferMap (fun i => (A₁ i)ᴴ) Λ₁ = Λ₁)
    (u₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ) (u₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ)
    (hT₀ : ∀ g, physicalSlice (T₀ g) 0 0 = u₀ g) (hT₁ : ∀ g, physicalSlice (T₁ g) 0 0 = u₁ g)
    (h₀ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₀ g) A₀)
      (fun _ : Fin 1 => A₀) (V₀ g) (W₀ g))
    (h₁ : ∀ g, IsBiorthogonalDecomposition (MPOTensor.actTensor (T₁ g) A₁)
      (fun _ : Fin 1 => A₁) (V₁ g) (W₁ g))
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hN : 2 ≤ N) (g : G) :
    Commute (Interaction.translationInvariant hN
        (arbitraryPhysicalMixedInteraction A₀ A₁ γ)).hamiltonian
      (mpo (arbitraryPhysicalMixedMPO A₀ A₁ (T₀ g) (T₁ g) (V₀ g) (V₁ g) (W₀ g) (W₁ g)) N) :=
  hamiltonian_arbitraryPhysicalMixedInteraction_commute_mpo_of_unitary
    A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ hInj₀ hInj₁ u₀ u₁ hT₀ hT₁ h₀ h₁
    (fun g ↦ exists_smul_bondOneActionGauge_mem_unitaryGroup hInj₀ hNorm₀ hΛ₀ hΛfix₀
      (by rw [hT₀]; exact (u₀ g).2) (h₀ g))
    (fun g ↦ exists_smul_bondOneActionGauge_mem_unitaryGroup hInj₁ hNorm₁ hΛ₁ hΛfix₁
      (by rw [hT₁]; exact (u₁ g).2) (h₁ g)) hγ hN g

end Group

end MPSTensor.MPOSymmetry
