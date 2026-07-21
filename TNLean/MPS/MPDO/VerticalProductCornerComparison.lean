/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalProductSpectralFamily

/-!
# Comparison and transport of retained product corners

This file transports active retained-product corners to the original BNT
labels, compares them with blocked reference corners, and constructs the
resulting original-label corner family.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

namespace RetainedProductSpectralFamily

variable {g D : ℕ} {dim mult : Fin g → ℕ}
  {weight : (α : Fin g) → Fin (mult α) → ℂ}
  {B : (α : Fin g) → MPSTensor (D * D) (dim α)}

private noncomputable def unitaryTransportMap
    {r m n : ℕ} (h : m = n) (W : Matrix (Fin r) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix (Fin r) (Fin m) ℂ :=
  cast (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h.symm)
    (W * (U : Matrix (Fin n) (Fin n) ℂ))

private noncomputable def originalCornerLabel
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂) (sigma : Fin g ≃ Fin g₂)
    (p : VerticalCopyPair mult) (k : Fin (S.count p)) : Fin g :=
  sigma.symm (C.label (S.activeLabelEquiv.symm ⟨p, k⟩))

private theorem localDim_eq_flatDim
    (S : RetainedProductSpectralFamily dim mult weight B)
    (p : VerticalCopyPair mult) (k : Fin (S.count p)) :
    S.localDim p k = S.flatDim (S.activeLabelEquiv.symm ⟨p, k⟩) := by
  change S.localDim p k =
    S.localDim
      (S.activeLabelEquiv (S.activeLabelEquiv.symm ⟨p, k⟩)).1
      (S.activeLabelEquiv (S.activeLabelEquiv.symm ⟨p, k⟩)).2
  rw [S.activeLabelEquiv.apply_symm_apply]

private noncomputable def originalCornerCoefficient
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂) (sigma : Fin g ≃ Fin g₂)
    (mult₂ : Fin g₂ → ℕ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (p : VerticalCopyPair mult) (k : Fin (S.count p)) : ℂ :=
  let j := S.activeLabelEquiv.symm ⟨p, k⟩
  let γ := originalCornerLabel S C sigma p k
  ((S.coefficient p k * C.phase j) *
      (verticalMultiplicityTrace weight γ /
        verticalMultiplicityTrace weight₂ (sigma γ))) /
    (weight p.1.1 p.1.2 * weight p.2.1 p.2.2)

private noncomputable def originalCornerInclusion
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂) (sigma : Fin g ≃ Fin g₂)
    (hDim : ∀ i, dim i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (omega : Fin (Fintype.card S.ActiveLabel) → ℝ)
    (p : VerticalCopyPair mult) (k : Fin (S.count p)) :
    Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (dim (originalCornerLabel S C sigma p k))) ℂ :=
  let j := S.activeLabelEquiv.symm ⟨p, k⟩
  let γ := originalCornerLabel S C sigma p k
  let Vflat : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (S.flatDim j)) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (localDim_eq_flatDim S p k)) (S.localInclusion p k)
  let W₂ := normalizedGroupedSectorMap (C.dim_eq j) Vflat
    (C.gauge j) (omega j)
  let hSigma : sigma γ = C.label j := sigma.apply_symm_apply _
  let Wsigma : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (dim₂ (sigma γ))) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (congrArg dim₂ hSigma).symm) W₂
  unitaryTransportMap (hDim γ) Wsigma (V γ)

private theorem castBondColumns_isometry
    {r m n : ℕ} (V : Matrix (Fin r) (Fin m) ℂ)
    (hV : Vᴴ * V = 1) (h : m = n) :
    let V' := cast (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h) V
    V'ᴴ * V' = 1 := by
  cases h
  simpa using hV

private theorem castBondColumns_compression
    {r m n e : ℕ} (T : MPSTensor e r) (A : MPSTensor e m)
    (V : Matrix (Fin r) (Fin m) ℂ) (c : ℂ)
    (hcorner : ∀ v, c • A v = Vᴴ * T v * V) (h : m = n)
    (v : Fin e) :
    let A' := cast (congrArg (MPSTensor e) h) A
    let V' := cast (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h) V
    c • A' v = V'ᴴ * T v * V' := by
  cases h
  simpa using hcorner v

private theorem castBondColumns_orthogonal
    {r m₁ n₁ m₂ n₂ : ℕ}
    (V₁ : Matrix (Fin r) (Fin m₁) ℂ)
    (V₂ : Matrix (Fin r) (Fin m₂) ℂ)
    (hV : V₁ᴴ * V₂ = 0) (h₁ : m₁ = n₁) (h₂ : m₂ = n₂) :
    let V₁' := cast
      (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h₁) V₁
    let V₂' := cast
      (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h₂) V₂
    V₁'ᴴ * V₂' = 0 := by
  cases h₁
  cases h₂
  simpa using hV

private theorem castBondColumns_intertwining
    {r m n e : ℕ} (T : MPSTensor e r) (A : MPSTensor e m)
    (V : Matrix (Fin r) (Fin m) ℂ) (c : ℂ)
    (hinter : ∀ v, T v * V = V * (c • A v)) (h : m = n)
    (v : Fin e) :
    let A' := cast (congrArg (MPSTensor e) h) A
    let V' := cast (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h) V
    T v * V' = V' * (c • A' v) := by
  cases h
  simpa using hinter v

private theorem castBondColumns_corner
    {r m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (V : Matrix (Fin r) (Fin m) ℂ) (c : ℂ) (h : m = n) :
    let A' := cast
      (congrArg (fun k ↦ Matrix (Fin k) (Fin k) ℂ) h) A
    let V' := cast
      (congrArg (fun k ↦ Matrix (Fin r) (Fin k) ℂ) h) V
    V' * (c • A') * V'ᴴ = V * (c • A) * Vᴴ := by
  cases h
  rfl

private theorem castDependentTensor_eq
    {ι : Type*} {e : ℕ} (bondDim : ι → ℕ)
    (A : (i : ι) → MPSTensor e (bondDim i))
    {i j : ι} (h : i = j) :
    cast (congrArg (MPSTensor e) (congrArg bondDim h)) (A i) = A j := by
  cases h
  rfl

private theorem castTensor_apply
    {e m n : ℕ} (h : m = n) (A : MPSTensor e m) (v : Fin e) :
    (cast (congrArg (MPSTensor e) h) A) v =
      cast (congrArg (fun k ↦ Matrix (Fin k) (Fin k) ℂ) h) (A v) := by
  cases h
  rfl

private theorem unitaryTransportMap_isometry
    {r m n : ℕ} (h : m = n) (W : Matrix (Fin r) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (hW : Wᴴ * W = 1) :
    (unitaryTransportMap h W U)ᴴ * unitaryTransportMap h W U = 1 := by
  cases h
  simp only [unitaryTransportMap, cast_eq, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
  exact Matrix.mem_unitaryGroup_iff'.mp U.prop

private theorem unitaryTransportMap_orthogonal
    {r m₁ n₁ m₂ n₂ : ℕ} (h₁ : m₁ = n₁) (h₂ : m₂ = n₂)
    (W₁ : Matrix (Fin r) (Fin n₁) ℂ)
    (W₂ : Matrix (Fin r) (Fin n₂) ℂ)
    (U₁ : Matrix.unitaryGroup (Fin n₁) ℂ)
    (U₂ : Matrix.unitaryGroup (Fin n₂) ℂ) (hW : W₁ᴴ * W₂ = 0) :
    (unitaryTransportMap h₁ W₁ U₁)ᴴ *
        unitaryTransportMap h₂ W₂ U₂ = 0 := by
  cases h₁
  cases h₂
  simp only [unitaryTransportMap, cast_eq, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc W₁ᴴ W₂, hW,
    Matrix.zero_mul, Matrix.mul_zero]

private theorem unitaryTransportMap_intertwining
    {r m n e : ℕ} (h : m = n) (T : MPSTensor e r)
    (A₁ : MPSTensor e m) (A₂ : MPSTensor e n)
    (W : Matrix (Fin r) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (c t : ℂ)
    (hinter : ∀ v, T v * W = W * (c • A₂ v))
    (hA : ∀ v, A₂ v = t •
      ((U : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) (A₁ v) *
        (U : Matrix (Fin n) (Fin n) ℂ)ᴴ)) (v : Fin e) :
    T v * unitaryTransportMap h W U =
      unitaryTransportMap h W U * ((c * t) • A₁ v) := by
  cases h
  simp only [unitaryTransportMap, cast_eq]
  have hA' : A₂ v = t • ((U : Matrix (Fin m) (Fin m) ℂ) * A₁ v *
      (U : Matrix (Fin m) (Fin m) ℂ)ᴴ) := by
    simpa [finCongr] using hA v
  rw [← Matrix.mul_assoc, hinter, hA']
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (U : Matrix (Fin m) (Fin m) ℂ)ᴴ * U = 1 by
    exact Matrix.mem_unitaryGroup_iff'.mp U.prop]
  simp only [Matrix.mul_one]

private theorem unitaryTransportMap_corner
    {r m n : ℕ} (h : m = n) (A₁ : Matrix (Fin m) (Fin m) ℂ)
    (A₂ : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin r) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (c t : ℂ)
    (hA : A₂ = t • ((U : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) A₁ *
      (U : Matrix (Fin n) (Fin n) ℂ)ᴴ)) :
    unitaryTransportMap h W U * ((c * t) • A₁) *
        (unitaryTransportMap h W U)ᴴ =
      W * (c • A₂) * Wᴴ := by
  cases h
  have hA' : A₂ = t • ((U : Matrix (Fin m) (Fin m) ℂ) * A₁ *
      (U : Matrix (Fin m) (Fin m) ℂ)ᴴ) := by
    simpa [finCongr] using hA
  simp only [unitaryTransportMap, cast_eq, Matrix.conjTranspose_mul]
  rw [hA']
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem originalCornerInclusion_isometry
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂) (sigma : Fin g ≃ Fin g₂)
    (hDim : ∀ i, dim i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (omega : Fin (Fintype.card S.ActiveLabel) → ℝ)
    (hQ : ∀ j, ((Real.sqrt (omega j) : ℂ))⁻¹ •
      (C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ) ∈
        Matrix.unitaryGroup (Fin (S.flatDim j)) ℂ)
    (p : VerticalCopyPair mult) (k : Fin (S.count p)) :
    (originalCornerInclusion S C sigma hDim V omega p k)ᴴ *
        originalCornerInclusion S C sigma hDim V omega p k = 1 := by
  let j := S.activeLabelEquiv.symm ⟨p, k⟩
  let γ := originalCornerLabel S C sigma p k
  let Vflat : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (S.flatDim j)) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (localDim_eq_flatDim S p k)) (S.localInclusion p k)
  have hVflat : Vflatᴴ * Vflat = 1 :=
    castBondColumns_isometry (S.localInclusion p k)
      (S.localInclusion_isometry p k) (localDim_eq_flatDim S p k)
  let W₂ := normalizedGroupedSectorMap (C.dim_eq j) Vflat
    (C.gauge j) (omega j)
  have hW₂ : W₂ᴴ * W₂ = 1 :=
    normalizedGroupedSectorMap_isometry (C.dim_eq j) Vflat
      (C.gauge j) (omega j) hVflat (hQ j)
  let hSigma : sigma γ = C.label j := sigma.apply_symm_apply _
  let Wsigma : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (dim₂ (sigma γ))) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (congrArg dim₂ hSigma).symm) W₂
  have hWsigma : Wsigmaᴴ * Wsigma = 1 :=
    castBondColumns_isometry W₂ hW₂ (congrArg dim₂ hSigma).symm
  change (unitaryTransportMap (hDim γ) Wsigma (V γ))ᴴ *
      unitaryTransportMap (hDim γ) Wsigma (V γ) = 1
  exact unitaryTransportMap_isometry (hDim γ) Wsigma (V γ) hWsigma

private theorem originalCornerInclusion_orthogonal
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂) (sigma : Fin g ≃ Fin g₂)
    (hDim : ∀ i, dim i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (omega : Fin (Fintype.card S.ActiveLabel) → ℝ)
    (p : VerticalCopyPair mult) (k l : Fin (S.count p)) (hkl : k ≠ l) :
    (originalCornerInclusion S C sigma hDim V omega p k)ᴴ *
        originalCornerInclusion S C sigma hDim V omega p l = 0 := by
  let j₁ := S.activeLabelEquiv.symm ⟨p, k⟩
  let j₂ := S.activeLabelEquiv.symm ⟨p, l⟩
  let γ₁ := originalCornerLabel S C sigma p k
  let γ₂ := originalCornerLabel S C sigma p l
  let Vflat₁ : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (S.flatDim j₁)) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (localDim_eq_flatDim S p k)) (S.localInclusion p k)
  let Vflat₂ : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (S.flatDim j₂)) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (localDim_eq_flatDim S p l)) (S.localInclusion p l)
  have hVflat : Vflat₁ᴴ * Vflat₂ = 0 :=
    castBondColumns_orthogonal (S.localInclusion p k)
      (S.localInclusion p l) (S.localInclusion_orthogonal p k l hkl)
      (localDim_eq_flatDim S p k) (localDim_eq_flatDim S p l)
  let W₂₁ := normalizedGroupedSectorMap (C.dim_eq j₁) Vflat₁
    (C.gauge j₁) (omega j₁)
  let W₂₂ := normalizedGroupedSectorMap (C.dim_eq j₂) Vflat₂
    (C.gauge j₂) (omega j₂)
  have hW₂ : W₂₁ᴴ * W₂₂ = 0 :=
    normalizedGroupedSectorMap_orthogonal (C.dim_eq j₁) (C.dim_eq j₂)
      Vflat₁ Vflat₂ (C.gauge j₁) (C.gauge j₂) (omega j₁) (omega j₂)
      hVflat
  let hSigma₁ : sigma γ₁ = C.label j₁ := sigma.apply_symm_apply _
  let hSigma₂ : sigma γ₂ = C.label j₂ := sigma.apply_symm_apply _
  let Wsigma₁ : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (dim₂ (sigma γ₁))) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (congrArg dim₂ hSigma₁).symm) W₂₁
  let Wsigma₂ : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (dim₂ (sigma γ₂))) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (congrArg dim₂ hSigma₂).symm) W₂₂
  have hWsigma : Wsigma₁ᴴ * Wsigma₂ = 0 :=
    castBondColumns_orthogonal W₂₁ W₂₂ hW₂
      (congrArg dim₂ hSigma₁).symm (congrArg dim₂ hSigma₂).symm
  change (unitaryTransportMap (hDim γ₁) Wsigma₁ (V γ₁))ᴴ *
      unitaryTransportMap (hDim γ₂) Wsigma₂ (V γ₂) = 0
  exact unitaryTransportMap_orthogonal (hDim γ₁) (hDim γ₂)
    Wsigma₁ Wsigma₂ (V γ₁) (V γ₂) hWsigma

private theorem originalCornerInclusion_weighted_intertwining
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂) (sigma : Fin g ≃ Fin g₂)
    (mult₂ : Fin g₂ → ℕ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hDim : ∀ i, dim i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin g) (ab : Fin (D * D)),
      A₂ (sigma i) ab =
        (verticalMultiplicityTrace weight i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (B i ab) *
          (V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (omega : Fin (Fintype.card S.ActiveLabel) → ℝ)
    (p : VerticalCopyPair mult) (k : Fin (S.count p))
    (ab : Fin (D * D)) :
    weightedVerticalProductBlock dim mult weight B p ab *
        originalCornerInclusion S C sigma hDim V omega p k =
      originalCornerInclusion S C sigma hDim V omega p k *
        (((S.coefficient p k *
            C.phase (S.activeLabelEquiv.symm ⟨p, k⟩)) *
          (verticalMultiplicityTrace weight
              (originalCornerLabel S C sigma p k) /
            verticalMultiplicityTrace weight₂
              (sigma (originalCornerLabel S C sigma p k)))) •
          B (originalCornerLabel S C sigma p k) ab) := by
  let j := S.activeLabelEquiv.symm ⟨p, k⟩
  let γ := originalCornerLabel S C sigma p k
  let c := S.coefficient p k * C.phase j
  let t := verticalMultiplicityTrace weight γ /
    verticalMultiplicityTrace weight₂ (sigma γ)
  let Vflat : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (S.flatDim j)) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (localDim_eq_flatDim S p k)) (S.localInclusion p k)
  have hx : S.activeLabelEquiv j = ⟨p, k⟩ :=
    S.activeLabelEquiv.apply_symm_apply _
  have hblock : cast
      (congrArg (MPSTensor (D * D)) (localDim_eq_flatDim S p k))
        (S.block p k) = S.flatBlock j := by
    simpa only [flatDim, flatBlock] using
      castDependentTensor_eq
        (fun x : S.ActiveLabel ↦ S.localDim x.1 x.2)
        (fun x : S.ActiveLabel ↦ S.block x.1 x.2) hx.symm
  have hVflat : ∀ ab,
      weightedVerticalProductBlock dim mult weight B p ab * Vflat =
        Vflat * (S.coefficient p k • S.flatBlock j ab) := by
    intro v
    have hcast := castBondColumns_intertwining
      (weightedVerticalProductBlock dim mult weight B p) (S.block p k)
      (S.localInclusion p k) (S.coefficient p k)
      (S.local_intertwine p k) (localDim_eq_flatDim S p k) v
    rw [hblock] at hcast
    simpa only [Vflat, Matrix.mul_smul] using hcast
  have hGauged : ∀ v,
      weightedVerticalProductBlock dim mult weight B p v * Vflat =
        Vflat * (c •
          ((C.gauge j : Matrix (Fin (S.flatDim j))
              (Fin (S.flatDim j)) ℂ) *
            cast (congrArg
              (fun n ↦ Matrix (Fin n) (Fin n) ℂ) (C.dim_eq j))
              (A₂ (C.label j) v) *
            (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
              (Fin (S.flatDim j)) ℂ))) := by
    intro v
    rw [hVflat v, C.block_eq j v]
    rw [castTensor_apply (C.dim_eq j) (A₂ (C.label j)) v]
    simp only [c, smul_smul]
  let W₂ := normalizedGroupedSectorMap (C.dim_eq j) Vflat
    (C.gauge j) (omega j)
  have hW₂ : ∀ v,
      weightedVerticalProductBlock dim mult weight B p v * W₂ =
        W₂ * (c • A₂ (C.label j) v) := by
    intro v
    exact normalizedGroupedSectorMap_intertwining (C.dim_eq j)
      (weightedVerticalProductBlock dim mult weight B p v)
      (A₂ (C.label j) v) Vflat (C.gauge j) c (omega j) (hGauged v)
  let hSigma : sigma γ = C.label j := sigma.apply_symm_apply _
  let Wsigma : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (dim₂ (sigma γ))) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (congrArg dim₂ hSigma).symm) W₂
  have hWsigma : ∀ v,
      weightedVerticalProductBlock dim mult weight B p v * Wsigma =
        Wsigma * (c • A₂ (sigma γ) v) := by
    intro v
    have hcast := castBondColumns_intertwining
      (weightedVerticalProductBlock dim mult weight B p)
      (A₂ (C.label j)) W₂ c hW₂ (congrArg dim₂ hSigma).symm v
    have hAcast := castDependentTensor_eq dim₂ A₂ hSigma.symm
    rw [hAcast] at hcast
    simpa only [Wsigma] using hcast
  change weightedVerticalProductBlock dim mult weight B p ab *
      unitaryTransportMap (hDim γ) Wsigma (V γ) =
    unitaryTransportMap (hDim γ) Wsigma (V γ) * ((c * t) • B γ ab)
  exact unitaryTransportMap_intertwining (hDim γ)
    (weightedVerticalProductBlock dim mult weight B p) (B γ) (A₂ (sigma γ))
    Wsigma (V γ) c t hWsigma (hLetter γ) ab

private theorem originalCornerInclusion_intertwining
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂) (sigma : Fin g ≃ Fin g₂)
    (mult₂ : Fin g₂ → ℕ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (hDim : ∀ i, dim i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin g) (ab : Fin (D * D)),
      A₂ (sigma i) ab =
        (verticalMultiplicityTrace weight i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (B i ab) *
          (V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (omega : Fin (Fintype.card S.ActiveLabel) → ℝ)
    (p : VerticalCopyPair mult) (k : Fin (S.count p))
    (ab : Fin (D * D)) :
    (mulTensor (verticalBNTMPO (B p.1.1))
        (verticalBNTMPO (B p.2.1))).toMPSTensor ab *
          originalCornerInclusion S C sigma hDim V omega p k =
      originalCornerInclusion S C sigma hDim V omega p k *
        (originalCornerCoefficient S C sigma mult₂ weight₂ p k •
          B (originalCornerLabel S C sigma p k) ab) := by
  let a := weight p.1.1 p.1.2 * weight p.2.1 p.2.2
  have ha : a ≠ 0 :=
    (mul_pos (hWeight p.1.1 p.1.2) (hWeight p.2.1 p.2.2)).ne'
  apply smul_right_injective
    (Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (dim (originalCornerLabel S C sigma p k))) ℂ) ha
  calc
    a • ((mulTensor (verticalBNTMPO (B p.1.1))
          (verticalBNTMPO (B p.2.1))).toMPSTensor ab *
        originalCornerInclusion S C sigma hDim V omega p k) =
      weightedVerticalProductBlock dim mult weight B p ab *
        originalCornerInclusion S C sigma hDim V omega p k := by
          simp only [weightedVerticalProductBlock, a, Matrix.smul_mul]
    _ = originalCornerInclusion S C sigma hDim V omega p k *
        (((S.coefficient p k *
            C.phase (S.activeLabelEquiv.symm ⟨p, k⟩)) *
          (verticalMultiplicityTrace weight
              (originalCornerLabel S C sigma p k) /
            verticalMultiplicityTrace weight₂
              (sigma (originalCornerLabel S C sigma p k)))) •
          B (originalCornerLabel S C sigma p k) ab) :=
      originalCornerInclusion_weighted_intertwining S C sigma mult₂ weight₂
        hDim V hLetter omega p k ab
    _ = a • (originalCornerInclusion S C sigma hDim V omega p k *
        (originalCornerCoefficient S C sigma mult₂ weight₂ p k •
          B (originalCornerLabel S C sigma p k) ab)) := by
      simp only [Matrix.mul_smul, smul_smul, originalCornerCoefficient, a]
      rw [mul_assoc, mul_div_cancel₀ _ ha]

private theorem originalCornerTerm_weighted_eq
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂) (sigma : Fin g ≃ Fin g₂)
    (mult₂ : Fin g₂ → ℕ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (hDim : ∀ i, dim i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin g) (ab : Fin (D * D)),
      A₂ (sigma i) ab =
        (verticalMultiplicityTrace weight i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (B i ab) *
          (V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (omega : Fin (Fintype.card S.ActiveLabel) → ℝ)
    (homega : ∀ j, 0 < omega j)
    (hGram : ∀ j,
      (C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ)ᴴ *
        C.gauge j = (omega j : ℂ) • 1)
    (p : VerticalCopyPair mult) (k : Fin (S.count p))
    (ab : Fin (D * D)) :
    (weight p.1.1 p.1.2 * weight p.2.1 p.2.2) •
        (originalCornerInclusion S C sigma hDim V omega p k *
          (originalCornerCoefficient S C sigma mult₂ weight₂ p k •
            B (originalCornerLabel S C sigma p k) ab) *
          (originalCornerInclusion S C sigma hDim V omega p k)ᴴ) =
      S.localInclusion p k * (S.coefficient p k • S.block p k ab) *
        (S.localInclusion p k)ᴴ := by
  let j := S.activeLabelEquiv.symm ⟨p, k⟩
  let γ := originalCornerLabel S C sigma p k
  let c := S.coefficient p k * C.phase j
  let t := verticalMultiplicityTrace weight γ /
    verticalMultiplicityTrace weight₂ (sigma γ)
  let a := weight p.1.1 p.1.2 * weight p.2.1 p.2.2
  have ha : a ≠ 0 :=
    (mul_pos (hWeight p.1.1 p.1.2) (hWeight p.2.1 p.2.2)).ne'
  let Vflat : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (S.flatDim j)) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (localDim_eq_flatDim S p k)) (S.localInclusion p k)
  let W₂ := normalizedGroupedSectorMap (C.dim_eq j) Vflat
    (C.gauge j) (omega j)
  let hSigma : sigma γ = C.label j := sigma.apply_symm_apply _
  let Wsigma : Matrix (Fin (dim p.1.1 * dim p.2.1))
      (Fin (dim₂ (sigma γ))) ℂ :=
    cast (congrArg
      (fun n ↦ Matrix (Fin (dim p.1.1 * dim p.2.1)) (Fin n) ℂ)
      (congrArg dim₂ hSigma).symm) W₂
  have hAcast := castDependentTensor_eq dim₂ A₂ hSigma.symm
  have hSigmaCorner : Wsigma * (c • A₂ (sigma γ) ab) * Wsigmaᴴ =
      W₂ * (c • A₂ (C.label j) ab) * W₂ᴴ := by
    have hcast := castBondColumns_corner (A₂ (C.label j) ab) W₂ c
      (congrArg dim₂ hSigma).symm
    have hAcastLetter := congrFun hAcast ab
    rw [castTensor_apply (congrArg dim₂ hSigma).symm
      (A₂ (C.label j)) ab] at hAcastLetter
    rw [hAcastLetter] at hcast
    simpa only [Wsigma] using hcast
  have hGaugeCorner : W₂ * (c • A₂ (C.label j) ab) * W₂ᴴ =
      Vflat * (c •
        ((C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ) *
          cast (congrArg (fun n ↦ Matrix (Fin n) (Fin n) ℂ) (C.dim_eq j))
            (A₂ (C.label j) ab) *
          (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ))) * Vflatᴴ := by
    exact normalizedGroupedSectorMap_corner (C.dim_eq j)
      (A₂ (C.label j) ab) Vflat (C.gauge j) c (omega j)
      (homega j) (hGram j)
  have hx : S.activeLabelEquiv j = ⟨p, k⟩ :=
    S.activeLabelEquiv.apply_symm_apply _
  have hblock : cast
      (congrArg (MPSTensor (D * D)) (localDim_eq_flatDim S p k))
        (S.block p k) = S.flatBlock j := by
    simpa only [flatDim, flatBlock] using
      castDependentTensor_eq
        (fun x : S.ActiveLabel ↦ S.localDim x.1 x.2)
        (fun x : S.ActiveLabel ↦ S.block x.1 x.2) hx.symm
  have hLocalCorner : Vflat * (S.coefficient p k • S.flatBlock j ab) *
      Vflatᴴ = S.localInclusion p k *
        (S.coefficient p k • S.block p k ab) *
          (S.localInclusion p k)ᴴ := by
    have hcast := castBondColumns_corner (S.block p k ab)
      (S.localInclusion p k) (S.coefficient p k)
      (localDim_eq_flatDim S p k)
    have hblockLetter := congrFun hblock ab
    rw [castTensor_apply (localDim_eq_flatDim S p k) (S.block p k) ab]
      at hblockLetter
    rw [hblockLetter] at hcast
    simpa only [Vflat] using hcast
  have hscalar : a * ((c * t) / a) = c * t := by
    calc
      a * ((c * t) / a) = ((c * t) / a) * a := mul_comm _ _
      _ = c * t := div_mul_cancel₀ _ ha
  calc
    a • (originalCornerInclusion S C sigma hDim V omega p k *
        (originalCornerCoefficient S C sigma mult₂ weight₂ p k • B γ ab) *
        (originalCornerInclusion S C sigma hDim V omega p k)ᴴ) =
      originalCornerInclusion S C sigma hDim V omega p k *
        ((c * t) • B γ ab) *
        (originalCornerInclusion S C sigma hDim V omega p k)ᴴ := by
          change a • (originalCornerInclusion S C sigma hDim V omega p k *
              (((c * t) / a) • B γ ab) *
                (originalCornerInclusion S C sigma hDim V omega p k)ᴴ) = _
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          rw [hscalar]
    _ = Wsigma * (c • A₂ (sigma γ) ab) * Wsigmaᴴ :=
      unitaryTransportMap_corner (hDim γ) (B γ ab) (A₂ (sigma γ) ab)
        Wsigma (V γ) c t (hLetter γ ab)
    _ = W₂ * (c • A₂ (C.label j) ab) * W₂ᴴ := hSigmaCorner
    _ = Vflat * (c •
        ((C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ) *
          cast (congrArg (fun n ↦ Matrix (Fin n) (Fin n) ℂ) (C.dim_eq j))
            (A₂ (C.label j) ab) *
          (↑((C.gauge j)⁻¹) : Matrix (Fin (S.flatDim j))
            (Fin (S.flatDim j)) ℂ))) * Vflatᴴ := hGaugeCorner
    _ = Vflat * (S.coefficient p k • S.flatBlock j ab) * Vflatᴴ := by
      rw [C.block_eq j ab,
        castTensor_apply (C.dim_eq j) (A₂ (C.label j)) ab]
      simp only [c, smul_smul]
    _ = S.localInclusion p k * (S.coefficient p k • S.block p k ab) *
        (S.localInclusion p k)ᴴ := hLocalCorner

/-- The distinguished blocked reference inclusion transported to the bond
dimension of an active product corner.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
noncomputable def FlatBlockedBNTComparison.referenceInclusion
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    Matrix (Fin (d * d)) (Fin (S.flatDim j)) ℂ :=
  cast (congrArg (fun n ↦ Matrix (Fin (d * d)) (Fin n) ℂ) (C.dim_eq j))
    (blockedReferenceInclusion dim₂ mult₂ hMult₂ U₂ (C.label j))

/-- Every transported distinguished reference inclusion is an isometry.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem FlatBlockedBNTComparison.referenceInclusion_isometry
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (j : Fin (Fintype.card S.ActiveLabel)) :
    (C.referenceInclusion mult₂ hMult₂ U₂ j)ᴴ *
        C.referenceInclusion mult₂ hMult₂ U₂ j = 1 := by
  exact castBondColumns_isometry
    (blockedReferenceInclusion dim₂ mult₂ hMult₂ U₂ (C.label j))
    (blockedReferenceInclusion_isometry dim₂ mult₂ hMult₂ U₂ hU₂ (C.label j))
    (C.dim_eq j)

/-- Compression by the transported reference inclusion is the distinguished
weighted blocked BNT copy, transported to the active bond dimension.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem FlatBlockedBNTComparison.reference_compression
    {g₂ d : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    {S : RetainedProductSpectralFamily dim mult weight B}
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (M : MPOTensor d D)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ γ : Fin g₂, mult₂ γ),
        verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (j : Fin (Fintype.card S.ActiveLabel)) (ab : Fin (D * D)) :
    weight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩ •
        (cast (congrArg (MPSTensor (D * D)) (C.dim_eq j))
          (A₂ (C.label j))) ab =
      (C.referenceInclusion mult₂ hMult₂ U₂ j)ᴴ *
        verticalTensor (blockTwo M) ab *
          C.referenceInclusion mult₂ hMult₂ U₂ j := by
  exact castBondColumns_compression
    (verticalTensor (blockTwo M)) (A₂ (C.label j))
    (blockedReferenceInclusion dim₂ mult₂ hMult₂ U₂ (C.label j))
    (weight₂ (C.label j) ⟨0, hMult₂ (C.label j)⟩)
    (blockedReference_compression M dim₂ mult₂ hMult₂ weight₂ A₂ U₂ hU₂
      hReconstruct₂ (C.label j))
    (C.dim_eq j) ab

/-- The active-to-blocked BNT comparisons can be chosen simultaneously.

**Scope restriction (active product BNT):** The chosen label map need not be
surjective.  Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** Unused blocked labels are left
for empty multiplicity fibers.  Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem exists_flatBlockedBNTComparison
    {d g₂ : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (dim₂ : Fin g₂ → ℕ)
    (A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ))
    [∀ γ, NeZero (dim₂ γ)]
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors
      (verticalTensor (blockTwo M)) (fun γ ↦ ⟨dim₂ γ, A₂ γ⟩)) :
    Nonempty (FlatBlockedBNTComparison S dim₂ A₂) := by
  classical
  have hExists := exists_blockedBNT_gaugePhase_of_flatBlock
    S M U hU hReconstruct dim₂ A₂ hBNT₂
  choose label dim_eq gauge phase phase_norm block_eq using hExists
  exact ⟨{
    label := label
    dim_eq := dim_eq
    gauge := gauge
    phase := phase
    phase_norm := phase_norm
    block_eq := block_eq }⟩

/-- Composing with the squared vertical reconstruction gives an isometry into
the blocked ambient bond space. -/
theorem ambientInclusion_isometry {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1) (x : S.ActiveLabel) :
    (S.ambientInclusion U x)ᴴ * S.ambientInclusion U x = 1 := by
  have hsquare := verticalCoisometrySquare_isCoisometry U hU
  unfold ambientInclusion
  calc
    (((verticalCoisometrySquare U)ᴴ * S.retainedInclusion x)ᴴ *
          ((verticalCoisometrySquare U)ᴴ * S.retainedInclusion x)) =
        (S.retainedInclusion x)ᴴ *
          (verticalCoisometrySquare U * (verticalCoisometrySquare U)ᴴ) *
            S.retainedInclusion x := by
      simp only [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (S.retainedInclusion x)ᴴ * S.retainedInclusion x := by
      rw [hsquare, Matrix.mul_one]
    _ = 1 := S.retainedInclusion_isometry x

/-- The composite ambient inclusion intertwines an active weighted corner
with the blocked vertical tensor.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem ambient_intertwine {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    verticalTensor (blockTwo M) ab * S.ambientInclusion U x =
      S.ambientInclusion U x *
        (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) := by
  have hsquare := verticalTensor_blockTwo_squared_coisometry_reconstruction
    M (verticalAssembledTensor dim mult weight B) U hU hReconstruct
  let W := verticalCoisometrySquare U
  let R := S.retainedInclusion x
  let C := retainedVerticalProductTensor dim mult weight B
  calc
    verticalTensor (blockTwo M) ab * S.ambientInclusion U x =
        (Wᴴ * C ab * W) * (Wᴴ * R) := by
      rw [hsquare.2 ab]
      rfl
    _ = Wᴴ * C ab * (W * Wᴴ) * R := by
      simp only [Matrix.mul_assoc]
    _ = Wᴴ * (C ab * R) := by
      rw [hsquare.1]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Wᴴ * (R * (S.coefficient x.1 x.2 • S.block x.1 x.2 ab)) := by
      rw [S.retained_intertwine x ab]
    _ = S.ambientInclusion U x *
        (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) := by
      simp only [ambientInclusion, W, R, Matrix.mul_assoc]

/-- The adjoint composite ambient inclusion satisfies the reverse
intertwining identity.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem ambient_intertwine_adjoint {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    (S.ambientInclusion U x)ᴴ * verticalTensor (blockTwo M) ab =
      (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
        (S.ambientInclusion U x)ᴴ := by
  have hsquare := verticalTensor_blockTwo_squared_coisometry_reconstruction
    M (verticalAssembledTensor dim mult weight B) U hU hReconstruct
  let W := verticalCoisometrySquare U
  let R := S.retainedInclusion x
  let C := retainedVerticalProductTensor dim mult weight B
  calc
    (S.ambientInclusion U x)ᴴ * verticalTensor (blockTwo M) ab =
        (Rᴴ * W) * (Wᴴ * C ab * W) := by
      rw [hsquare.2 ab]
      simp only [ambientInclusion, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, W, R, C,
        retainedVerticalProductTensor]
    _ = Rᴴ * (W * Wᴴ) * C ab * W := by
      simp only [Matrix.mul_assoc]
    _ = (Rᴴ * C ab) * W := by
      rw [hsquare.1]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = ((S.coefficient x.1 x.2 • S.block x.1 x.2 ab) * Rᴴ) * W := by
      rw [S.retained_intertwine_adjoint x ab]
    _ = (S.coefficient x.1 x.2 • S.block x.1 x.2 ab) *
        (S.ambientInclusion U x)ᴴ := by
      simp only [ambientInclusion, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, W, R, Matrix.mul_assoc]

/-- Compression of the blocked vertical tensor by a composite ambient
inclusion gives its active weighted corner.

Source: CPSV16, Appendix C.4, lines 2025--2029. -/
theorem ambient_compression {d : ℕ}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (M : MPOTensor d D)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (x : S.ActiveLabel) (ab : Fin (D * D)) :
    S.coefficient x.1 x.2 • S.block x.1 x.2 ab =
      (S.ambientInclusion U x)ᴴ * verticalTensor (blockTwo M) ab *
        S.ambientInclusion U x := by
  rw [S.ambient_intertwine_adjoint M U hU hReconstruct x ab,
    Matrix.mul_assoc, S.ambientInclusion_isometry U hU x,
    Matrix.mul_one]

/-- Normalized active product corners form a positive decomposition in the
original one-site BNT labels.

**Local fix (Figure-11 fixed-pair support):** Empty active families are kept
empty.  The exact local reconstruction then forces the corresponding weighted
raw product to vanish, and positivity of the outer copy weight gives the raw
reconstruction.  Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
theorem exists_originalCornerFamily
    {g₂ : ℕ} {dim₂ : Fin g₂ → ℕ}
    {A₂ : (γ : Fin g₂) → MPSTensor (D * D) (dim₂ γ)}
    (S : RetainedProductSpectralFamily dim mult weight B)
    (C : FlatBlockedBNTComparison S dim₂ A₂)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (mult₂ : Fin g₂ → ℕ) (hMult₂ : ∀ γ, 0 < mult₂ γ)
    (weight₂ : (γ : Fin g₂) → Fin (mult₂ γ) → ℂ)
    (hWeight₂ : ∀ γ q, (0 : ℂ) < weight₂ γ q)
    (sigma : Fin g ≃ Fin g₂) (hDim : ∀ i, dim i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin g) (ab : Fin (D * D)),
      A₂ (sigma i) ab =
        (verticalMultiplicityTrace weight i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (B i ab) *
          (V i : Matrix (Fin (dim₂ (sigma i)))
            (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (hActivePos : ∀ j, (0 : ℂ) < S.flatCoefficient j * C.phase j)
    (omega : Fin (Fintype.card S.ActiveLabel) → ℝ)
    (homega : ∀ j, 0 < omega j)
    (hGram : ∀ j,
      (C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ)ᴴ *
        C.gauge j = (omega j : ℂ) • 1) :
    Nonempty (OriginalCornerFamily S) := by
  classical
  have hQ : ∀ j, ((Real.sqrt (omega j) : ℂ))⁻¹ •
      (C.gauge j : Matrix (Fin (S.flatDim j)) (Fin (S.flatDim j)) ℂ) ∈
        Matrix.unitaryGroup (Fin (S.flatDim j)) ℂ := fun j ↦
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      (homega j) (hGram j)
  refine ⟨{
    label := originalCornerLabel S C sigma
    coefficient := originalCornerCoefficient S C sigma mult₂ weight₂
    coefficient_pos := ?_
    inclusion := originalCornerInclusion S C sigma hDim V omega
    inclusion_isometry := ?_
    inclusion_orthogonal := ?_
    intertwine := ?_
    reconstruction := ?_ }⟩
  · intro p k
    let j := S.activeLabelEquiv.symm ⟨p, k⟩
    let γ := originalCornerLabel S C sigma p k
    have hx : S.activeLabelEquiv j = ⟨p, k⟩ :=
      S.activeLabelEquiv.apply_symm_apply _
    have hc : (0 : ℂ) < S.coefficient p k * C.phase j := by
      have h := hActivePos j
      change (0 : ℂ) < S.coefficient (S.activeLabelEquiv j).1
        (S.activeLabelEquiv j).2 * C.phase j at h
      rw [hx] at h
      exact h
    have ht : (0 : ℂ) < verticalMultiplicityTrace weight γ /
        verticalMultiplicityTrace weight₂ (sigma γ) :=
      div_pos (verticalMultiplicityTrace_pos hMult hWeight γ)
        (verticalMultiplicityTrace_pos hMult₂ hWeight₂ (sigma γ))
    have ha : (0 : ℂ) <
        weight p.1.1 p.1.2 * weight p.2.1 p.2.2 :=
      mul_pos (hWeight p.1.1 p.1.2) (hWeight p.2.1 p.2.2)
    exact div_pos (mul_pos hc ht) ha
  · exact fun p k ↦
      originalCornerInclusion_isometry S C sigma hDim V omega hQ p k
  · exact fun p k l hkl ↦
      originalCornerInclusion_orthogonal S C sigma hDim V omega p k l hkl
  · exact fun p k ab ↦
      originalCornerInclusion_intertwining S C sigma mult₂ weight₂ hWeight
        hDim V hLetter omega p k ab
  · intro p ab
    let a := weight p.1.1 p.1.2 * weight p.2.1 p.2.2
    have ha : a ≠ 0 :=
      (mul_pos (hWeight p.1.1 p.1.2) (hWeight p.2.1 p.2.2)).ne'
    apply smul_right_injective
      (Matrix (Fin (dim p.1.1 * dim p.2.1))
        (Fin (dim p.1.1 * dim p.2.1)) ℂ) ha
    calc
      a • (mulTensor (verticalBNTMPO (B p.1.1))
          (verticalBNTMPO (B p.2.1))).toMPSTensor ab =
        weightedVerticalProductBlock dim mult weight B p ab := by
          rfl
      _ = ∑ k, S.localInclusion p k *
          (S.coefficient p k • S.block p k ab) *
            (S.localInclusion p k)ᴴ := S.local_reconstruction p ab
      _ = ∑ k, a •
          (originalCornerInclusion S C sigma hDim V omega p k *
            (originalCornerCoefficient S C sigma mult₂ weight₂ p k •
              B (originalCornerLabel S C sigma p k) ab) *
            (originalCornerInclusion S C sigma hDim V omega p k)ᴴ) := by
        apply Finset.sum_congr rfl
        intro k _
        exact (originalCornerTerm_weighted_eq S C sigma mult₂ weight₂
          hWeight hDim V hLetter omega homega hGram p k ab).symm
      _ = a • ∑ k,
          originalCornerInclusion S C sigma hDim V omega p k *
            (originalCornerCoefficient S C sigma mult₂ weight₂ p k •
              B (originalCornerLabel S C sigma p k) ab) *
            (originalCornerInclusion S C sigma hDim V omega p k)ᴴ := by
        rw [Finset.smul_sum]

end RetainedProductSpectralFamily

end MPOTensor
