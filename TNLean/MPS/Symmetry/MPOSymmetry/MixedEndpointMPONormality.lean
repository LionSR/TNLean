/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPO
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Three-site injectivity of the mixed endpoint MPO

The actual mixed MPO is injective after blocking three sites when both
endpoint MPOs are injective and their action maps are biorthogonal with
positive common multiplicity. Endpoint injectivity supplies every diagonal
matrix unit in the one-letter span. Biorthogonality supplies a nonzero
coefficient in each cross corner. Sandwiching such a coefficient between
diagonal matrix units supplies the cross matrix units in the three-letter
span; diagonal units can be padded to the same length.

Source context: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`eq:orthoV` and the mixed-MPO discussion in `REsubmission.tex`, lines
1687–1689. The source discusses one-site injectivity in the setting of
aligned fusion and action data. The result here proves three-site
injectivity from the isolated endpoint assumptions. It neither asserts
one-site injectivity under those weaker assumptions nor requires
reconstruction, common L-symbols, F-symbols, or ambient completeness.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {D₀ D₁ χ₀ χ₁ m : ℕ}

private theorem cross_contraction_retract
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (hret₀ : ∀ μ, V₀ μ * W₀ μ = 1)
    (hret₁ : ∀ μ, V₁ μ * W₁ μ = 1)
    (horth₀ : ∀ μ ν, μ ≠ ν → V₀ μ * W₀ ν = 0)
    (ν : Fin m) (X : Matrix (Fin D₀) (Fin D₁) ℂ) :
    V₀ ν * (∑ μ, W₀ μ * X * V₁ μ) * W₁ ν = X := by
  classical
  rw [Matrix.mul_sum, Matrix.sum_mul]
  have hterm (μ : Fin m) :
      V₀ ν * (W₀ μ * X * V₁ μ) * W₁ ν =
        (V₀ ν * W₀ μ) * X * (V₁ μ * W₁ ν) := by
    simp only [Matrix.mul_assoc]
  simp_rw [hterm]
  rw [Finset.sum_eq_single ν]
  · simp only [hret₀, hret₁, Matrix.one_mul, Matrix.mul_one]
  · intro μ _ hμ
    simp only [horth₀ ν μ hμ.symm, Matrix.zero_mul]
  · simp

private theorem exists_cross_entry_ne_zero
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hm : 0 < m)
    (hret₀ : ∀ μ, V₀ μ * W₀ μ = 1)
    (hret₁ : ∀ μ, V₁ μ * W₁ μ = 1)
    (horth₀ : ∀ μ ν, μ ≠ ν → V₀ μ * W₀ ν = 0) :
    ∃ (r : Fin D₀) (s : Fin D₁) (α : Fin χ₀) (k : Fin D₀)
      (β : Fin χ₁) (l : Fin D₁),
      (∑ μ, W₀ μ (finProdFinEquiv (α, k)) r *
        V₁ μ s (finProdFinEquiv (β, l))) ≠ 0 := by
  classical
  let r : Fin D₀ := ⟨0, hD₀⟩
  let s : Fin D₁ := ⟨0, hD₁⟩
  let B : Matrix (Fin (χ₀ * D₀)) (Fin (χ₁ * D₁)) ℂ :=
    ∑ μ, W₀ μ * Matrix.single r s (1 : ℂ) * V₁ μ
  have hB : B ≠ 0 := by
    intro hzero
    have h := cross_contraction_retract V₀ V₁ W₀ W₁ hret₀ hret₁ horth₀
      ⟨0, hm⟩ (Matrix.single r s 1)
    change V₀ ⟨0, hm⟩ * B * W₁ ⟨0, hm⟩ = _ at h
    rw [hzero, Matrix.mul_zero, Matrix.zero_mul] at h
    have he := congrArg (fun M => M r s) h
    simp at he
  obtain ⟨a, b, hab⟩ : ∃ a b, B a b ≠ 0 := by
    by_contra h
    push Not at h
    exact hB (Matrix.ext h)
  obtain ⟨⟨α, k⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨β, l⟩, rfl⟩ := finProdFinEquiv.surjective b
  refine ⟨r, s, α, k, β, l, ?_⟩
  simpa [B, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Finset.sum_mul, ite_and] using hab

/-- The constructed mixed MPO is injective after three-site blocking.
The assumptions are endpoint MPO injectivity, positive state-bond
sizes and multiplicity, and the two endpoint biorthogonality identities.
No exact action reconstruction or fusion data is needed.

Source context: GLM23, `eq:orthoV` and `REsubmission.tex`, lines
1687–1689. This is the three-site conclusion from isolated endpoint data,
not the one-site claim in the source's aligned fusion setting. -/
theorem isNBlkInjective_mixedEndpointMPO_three
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hm : 0 < m)
    (hT₀ : Kraus.IsInjective T₀.toMPSTensor)
    (hT₁ : Kraus.IsInjective T₁.toMPSTensor)
    (hret₀ : ∀ μ, V₀ μ * W₀ μ = 1)
    (hret₁ : ∀ μ, V₁ μ * W₁ μ = 1)
    (horth₀ : ∀ μ ν, μ ≠ ν → V₀ μ * W₀ ν = 0)
    (horth₁ : ∀ μ ν, μ ≠ ν → V₁ μ * W₁ ν = 0) :
    Kraus.IsNBlkInjective (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁).toMPSTensor 3 := by
  classical
  let T := mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁
  let S := Kraus.wordSpan T.toMPSTensor 1
  let e : (Fin χ₀ ⊕ Fin χ₁) ≃ Fin (χ₀ + χ₁) := finSumFinEquiv
  have hletter (i j) : T i j ∈ S := by
    change T i j ∈ Kraus.wordSpan T.toMPSTensor 1
    rw [Kraus.wordSpan_one]
    exact Submodule.subset_span ⟨finProdFinEquiv (i, j), by
      simp [MPOTensor.toMPSTensor]⟩
  have hleft (M : Matrix (Fin χ₀) (Fin χ₀) ℂ) :
      (Matrix.fromBlocks M (0 : Matrix (Fin χ₀) (Fin χ₁) ℂ) 0 0).submatrix
        e.symm e.symm ∈ S := by
    have hM : M ∈ Submodule.span ℂ (Set.range T₀.toMPSTensor) :=
      hT₀ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M hM =>
        obtain ⟨p, rfl⟩ := hM
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
        obtain ⟨⟨r, s⟩, rfl⟩ := finProdFinEquiv.surjective i
        obtain ⟨⟨k, l⟩, rfl⟩ := finProdFinEquiv.surjective j
        convert hletter (mixedEndpointPhysicalEquiv D₀ D₁ (.inl r, .inl s))
          (mixedEndpointPhysicalEquiv D₀ D₁ (.inl k, .inl l)) using 1
        ext a b
        obtain ⟨a, rfl⟩ := e.surjective a
        obtain ⟨b, rfl⟩ := e.surjective b
        cases a <;> cases b <;>
          simp [T, e, mixedEndpointMPOLetter, MPOTensor.toMPSTensor]
    | zero => simp
    | add M N _ _ hM hN =>
        have h := S.add_mem hM hN
        change (Matrix.fromBlocks M (0 : Matrix (Fin χ₀) (Fin χ₁) ℂ) 0 0 +
          Matrix.fromBlocks N 0 0 0).submatrix e.symm e.symm ∈ S at h
        simpa only [Matrix.fromBlocks_add, add_zero] using h
    | smul c M _ hM =>
        have h := S.smul_mem c hM
        change (c • Matrix.fromBlocks M (0 : Matrix (Fin χ₀) (Fin χ₁) ℂ) 0 0).submatrix
          e.symm e.symm ∈ S at h
        simpa only [Matrix.fromBlocks_smul, smul_zero] using h
  have hright (M : Matrix (Fin χ₁) (Fin χ₁) ℂ) :
      (Matrix.fromBlocks (0 : Matrix (Fin χ₀) (Fin χ₀) ℂ) 0 0 M).submatrix
        e.symm e.symm ∈ S := by
    have hM : M ∈ Submodule.span ℂ (Set.range T₁.toMPSTensor) :=
      hT₁ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M hM =>
        obtain ⟨p, rfl⟩ := hM
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
        obtain ⟨⟨r, s⟩, rfl⟩ := finProdFinEquiv.surjective i
        obtain ⟨⟨k, l⟩, rfl⟩ := finProdFinEquiv.surjective j
        convert hletter (mixedEndpointPhysicalEquiv D₀ D₁ (.inr r, .inr s))
          (mixedEndpointPhysicalEquiv D₀ D₁ (.inr k, .inr l)) using 1
        ext a b
        obtain ⟨a, rfl⟩ := e.surjective a
        obtain ⟨b, rfl⟩ := e.surjective b
        cases a <;> cases b <;>
          simp [T, e, mixedEndpointMPOLetter, MPOTensor.toMPSTensor]
    | zero => simp
    | add M N _ _ hM hN =>
        have h := S.add_mem hM hN
        change (Matrix.fromBlocks (0 : Matrix (Fin χ₀) (Fin χ₀) ℂ) 0 0 M +
          Matrix.fromBlocks 0 0 0 N).submatrix e.symm e.symm ∈ S at h
        simpa only [Matrix.fromBlocks_add, add_zero] using h
    | smul c M _ hM =>
        have h := S.smul_mem c hM
        change (c • Matrix.fromBlocks (0 : Matrix (Fin χ₀) (Fin χ₀) ℂ) 0 0 M).submatrix
          e.symm e.symm ∈ S at h
        simpa only [Matrix.fromBlocks_smul, smul_zero] using h
  have h₀₀ (a b : Fin χ₀) : Matrix.single (e (.inl a)) (e (.inl b)) 1 ∈ S := by
    convert hleft (Matrix.single a b 1) using 1
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    cases i <;> cases j <;> simp [Matrix.single_apply, Matrix.fromBlocks]
  have h₁₁ (a b : Fin χ₁) : Matrix.single (e (.inr a)) (e (.inr b)) 1 ∈ S := by
    convert hright (Matrix.single a b 1) using 1
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    cases i <;> cases j <;> simp [Matrix.single_apply, Matrix.fromBlocks]
  have hthree {X Y Z : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ}
      (hX : X ∈ S) (hY : Y ∈ S) (hZ : Z ∈ S) :
      X * Y * Z ∈ Kraus.wordSpan T.toMPSTensor 3 := by
    change X * Y * Z ∈ Kraus.wordSpan T.toMPSTensor ((1 + 1) + 1)
    rw [Kraus.wordSpan_add, Kraus.wordSpan_add]
    exact Submodule.mul_mem_mul (Submodule.mul_mem_mul hX hY) hZ
  have hsandwich {C : Matrix (Fin (χ₀ + χ₁)) (Fin (χ₀ + χ₁)) ℂ}
      {a u v b : Fin (χ₀ + χ₁)} (hC : C ∈ S) (hne : C u v ≠ 0)
      (ha : Matrix.single a u 1 ∈ S) (hb : Matrix.single v b 1 ∈ S) :
      Matrix.single a b 1 ∈ Kraus.wordSpan T.toMPSTensor 3 := by
    have h := (Kraus.wordSpan T.toMPSTensor 3).smul_mem (C u v)⁻¹
      (hthree ha hC hb)
    simpa [Matrix.single_mul_mul_single, Matrix.smul_single, hne] using h
  obtain ⟨r₀, s₁, α₀, k₀, β₁, l₁, h₀₁⟩ :=
    exists_cross_entry_ne_zero V₀ V₁ W₀ W₁ hD₀ hD₁ hm hret₀ hret₁ horth₀
  obtain ⟨r₁, s₀, α₁, k₁, β₀, l₀, h₁₀⟩ :=
    exists_cross_entry_ne_zero V₁ V₀ W₁ W₀ hD₁ hD₀ hm hret₁ hret₀ horth₁
  let C₀₁ := T (mixedEndpointPhysicalEquiv D₀ D₁ (.inl r₀, .inr s₁))
    (mixedEndpointPhysicalEquiv D₀ D₁ (.inl k₀, .inr l₁))
  let C₁₀ := T (mixedEndpointPhysicalEquiv D₀ D₁ (.inr r₁, .inl s₀))
    (mixedEndpointPhysicalEquiv D₀ D₁ (.inr k₁, .inl l₀))
  have hC₀₁ : C₀₁ (e (.inl α₀)) (e (.inr β₁)) ≠ 0 := by
    simpa [C₀₁, T, e, mixedEndpointMPOLetter] using h₀₁
  have hC₁₀ : C₁₀ (e (.inr α₁)) (e (.inl β₀)) ≠ 0 := by
    simpa [C₁₀, T, e, mixedEndpointMPOLetter] using h₁₀
  apply Submodule.eq_top_of_forall_single_mem
  intro a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a with
  | inl a =>
      cases b with
      | inl b => simpa using hthree (h₀₀ a b) (h₀₀ b b) (h₀₀ b b)
      | inr b => exact hsandwich (hletter _ _) hC₀₁ (h₀₀ a α₀) (h₁₁ β₁ b)
  | inr a =>
      cases b with
      | inl b => exact hsandwich (hletter _ _) hC₁₀ (h₁₁ a α₁) (h₀₀ β₀ b)
      | inr b => simpa using hthree (h₁₁ a b) (h₁₁ b b) (h₁₁ b b)

/-- The actual mixed MPO is normal, with blocking length three.
Source context: GLM23, `REsubmission.tex`, lines 1687–1689; only isolated
endpoint injectivity and biorthogonality are used here. -/
theorem isNormal_mixedEndpointMPO
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hm : 0 < m)
    (hT₀ : Kraus.IsInjective T₀.toMPSTensor)
    (hT₁ : Kraus.IsInjective T₁.toMPSTensor)
    (hret₀ : ∀ μ, V₀ μ * W₀ μ = 1)
    (hret₁ : ∀ μ, V₁ μ * W₁ μ = 1)
    (horth₀ : ∀ μ ν, μ ≠ ν → V₀ μ * W₀ ν = 0)
    (horth₁ : ∀ μ ν, μ ≠ ν → V₁ μ * W₁ ν = 0) :
    Kraus.IsNormal (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁).toMPSTensor :=
  ⟨3, by omega, isNBlkInjective_mixedEndpointMPO_three T₀ T₁ V₀ V₁ W₀ W₁
    hD₀ hD₁ hm hT₀ hT₁ hret₀ hret₁ horth₀ horth₁⟩

/-- A positive-bond injective MPO acting exactly on a square-physical
injective MPS cannot have zero multiplicity. Square-physical injectivity
makes the MPS letters a basis, so a zero action would force every MPO
letter to vanish.

Source context: GLM23, `fusiontensors2`, `eq:orthoV`, and the physical
support restriction preceding `defAgamma`, lines 1584–1601. -/
theorem multiplicity_pos_of_injective_endpoint_action {D χ : ℕ}
    (T : MPOTensor (D * D) χ) (A : MPSTensor (D * D) D)
    (V : Fin m → Matrix (Fin D) (Fin (χ * D)) ℂ)
    (W : Fin m → Matrix (Fin (χ * D)) (Fin D) ℂ)
    (hχ : 0 < χ) (hT : Kraus.IsInjective T.toMPSTensor)
    (hA : Kraus.IsInjective A)
    (h : IsBiorthogonalDecomposition (MPOTensor.actTensor T A)
      (fun _ : Fin m => A) V W) : 0 < m := by
  classical
  by_contra hm
  have hm0 : m = 0 := by omega
  subst m
  have hlin : LinearIndependent ℂ A :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (by rw [hA])
      (by simp [Module.finrank_matrix])
  have hzero (i j : Fin (D * D)) (α β : Fin χ) : T i j α β = 0 := by
    apply Fintype.linearIndependent_iff.mp hlin (fun k => T i k α β) _ j
    ext r s
    have he := congrArg (fun M => M (finProdFinEquiv (α, r))
      (finProdFinEquiv (β, s))) (h.letter i)
    simpa [MPOTensor.actTensor, Matrix.sum_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply] using he
  have hle : Submodule.span ℂ (Set.range T.toMPSTensor) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro M ⟨i, rfl⟩
    apply (Submodule.mem_bot ℂ).mpr
    ext α β
    exact hzero _ _ α β
  rw [hT] at hle
  have hI : (1 : Matrix (Fin χ) (Fin χ) ℂ) = 0 :=
    (Submodule.mem_bot ℂ).mp (hle Submodule.mem_top)
  have he := congrArg (fun M => M ⟨0, hχ⟩ ⟨0, hχ⟩) hI
  simp at he

/-- Exact endpoint actions provide the positive multiplicity and
biorthogonality needed for three-site injectivity of the mixed MPO.
One endpoint's square-physical MPS injectivity and positive MPO bond
suffice to derive positive multiplicity.

Source context: GLM23, `fusiontensors2`, `eq:orthoV`, `defAgamma`, and
`REsubmission.tex`, lines 1687–1689. The conclusion is three-site
injectivity from these endpoint data, without aligned fusion hypotheses. -/
theorem isNBlkInjective_mixedEndpointMPO_three_of_exact_action
    (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hχ₀ : 0 < χ₀)
    (hT₀ : Kraus.IsInjective T₀.toMPSTensor)
    (hT₁ : Kraus.IsInjective T₁.toMPSTensor) (hA₀ : Kraus.IsInjective A₀)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁) :
    Kraus.IsNBlkInjective (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁).toMPSTensor 3 :=
  isNBlkInjective_mixedEndpointMPO_three T₀ T₁ V₀ V₁ W₀ W₁ hD₀ hD₁
    (multiplicity_pos_of_injective_endpoint_action T₀ A₀ V₀ W₀ hχ₀ hT₀ hA₀ h₀)
    hT₀ hT₁ h₀.retract h₁.retract h₀.orthogonal h₁.orthogonal

end MPSTensor.MPOSymmetry
