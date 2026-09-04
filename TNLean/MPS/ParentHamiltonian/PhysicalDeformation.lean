/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.PhysicalRotation
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# Ground-space correspondence under an invertible on-site map

Source: arXiv:2011.12127, Section IV.C, lines 2032--2038 (the deformed parent interaction,
equation deformed-parent-1, and the parenthetical generalization to an invertible on-site
map), reused at lines 2190--2192 (the deformed interaction as a parent interaction for the
physically perturbed tensor) and lines 2260--2262 (physical perturbations of the tensor).

The source writes the deformed tensor as \(A^i = \sum_j \Lambda_{ij} B^j\) with \(\Lambda\)
invertible, and the deformed state as \(\ket{\psi'} = R^{\otimes N}\ket{\psi}\).  Here the
original tensor is \(A\) and the deformed tensor is \(\Lambda A\), with
\((\Lambda A)^i = \sum_j \Lambda_{ij} A^j\); the on-site map \(\Lambda\) plays the role of the
source's \(\Lambda\) and \(R\).

## Main definitions

* `MPSTensor.onSiteTensorPow` — the tensor power \(\Lambda^{\otimes L}\) of an on-site map,
  as a matrix on \(L\)-site configurations.
* `MPSTensor.IsParentInteraction` — a parent interaction in the sense of the source
  definition, lines 1996--1999: a hermitian positive semidefinite operator whose kernel is
  the local ground space.
* `MPSTensor.deformedInteraction` — the deformed interaction
  \(h' = ({\Lambda^{-1}}^\dagger)^{\otimes L} h (\Lambda^{-1})^{\otimes L}\).

## Main results

* `MPSTensor.groundSpace_rotatePhysical` — the local ground space of the deformed tensor is
  the image \(\Lambda^{\otimes L}\mathcal G_L(A)\).
* `MPSTensor.IsParentInteraction.deformedInteraction` — the deformed interaction is a parent
  interaction for the deformed tensor.
* `MPSTensor.chainGroundSpace_rotatePhysical` and
  `MPSTensor.ker_parentHamiltonian_rotatePhysical` — the ground spaces of the two parent
  Hamiltonians correspond one-to-one through \(\Lambda^{\otimes N}\).
* `MPSTensor.hasUniqueGroundState_chainGroundSpace_rotatePhysical` — uniqueness of the
  ground state transfers along the correspondence.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### The tensor power of an on-site map -/

/-- The tensor power \(\Lambda^{\otimes L}\) of an on-site map \(\Lambda\) on \(\mathbb C^d\),
as a matrix on \(L\)-site configurations:
\((\Lambda^{\otimes L})_{\sigma,\tau} = \prod_{n} \Lambda_{\sigma_n \tau_n}\).
This is the map written \(\Lambda^{\otimes k}\) and \(R^{\otimes N}\) in arXiv:2011.12127,
lines 2035--2037 and 2190--2192. -/
noncomputable def onSiteTensorPow (L : ℕ) (Λ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Cfg d L) (Cfg d L) ℂ :=
  Matrix.of fun σ τ => ∏ n : Fin L, Λ (σ n) (τ n)

@[simp] lemma onSiteTensorPow_apply (L : ℕ) (Λ : Matrix (Fin d) (Fin d) ℂ)
    (σ τ : Cfg d L) :
    onSiteTensorPow L Λ σ τ = ∏ n : Fin L, Λ (σ n) (τ n) := rfl

/-- The tensor power is the blocked Kronecker lift read through the decoding of blocked
physical indices. -/
lemma onSiteTensorPow_eq_submatrix_blockKron (L : ℕ) (Λ : Matrix (Fin d) (Fin d) ℂ) :
    onSiteTensorPow L Λ =
      (blockKron L Λ).submatrix (decodeBlockEquiv d L).symm (decodeBlockEquiv d L).symm := by
  ext σ τ
  simp [onSiteTensorPow, blockKron]

/-- The tensor power is multiplicative: \((\Lambda\Lambda')^{\otimes L} =
\Lambda^{\otimes L}\Lambda'^{\otimes L}\). -/
lemma onSiteTensorPow_mul (L : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) ℂ) :
    onSiteTensorPow L (Λ * Λ') = onSiteTensorPow L Λ * onSiteTensorPow L Λ' := by
  rw [onSiteTensorPow_eq_submatrix_blockKron, onSiteTensorPow_eq_submatrix_blockKron,
    onSiteTensorPow_eq_submatrix_blockKron, Matrix.submatrix_mul_equiv, blockKron_mul]

/-- The tensor power of the identity is the identity. -/
lemma onSiteTensorPow_one (L : ℕ) :
    onSiteTensorPow L (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [onSiteTensorPow_eq_submatrix_blockKron, blockKron_one, Matrix.submatrix_one_equiv]

/-- The tensor power commutes with the conjugate transpose:
\((\Lambda^{\otimes L})^\dagger = (\Lambda^\dagger)^{\otimes L}\). -/
lemma onSiteTensorPow_conjTranspose (L : ℕ) (Λ : Matrix (Fin d) (Fin d) ℂ) :
    (onSiteTensorPow L Λ)ᴴ = onSiteTensorPow L Λᴴ := by
  rw [onSiteTensorPow_eq_submatrix_blockKron, onSiteTensorPow_eq_submatrix_blockKron,
    Matrix.conjTranspose_submatrix, blockKron_conjTranspose]

/-- For an invertible on-site map, the tensor power of the inverse is a left inverse of the
tensor power. -/
lemma onSiteTensorPow_inv_mul (L : ℕ) {Λ : Matrix (Fin d) (Fin d) ℂ} (hΛ : IsUnit Λ) :
    onSiteTensorPow L Λ⁻¹ * onSiteTensorPow L Λ = 1 := by
  rw [← onSiteTensorPow_mul, Matrix.nonsing_inv_mul Λ ((Matrix.isUnit_iff_isUnit_det Λ).1 hΛ),
    onSiteTensorPow_one]

/-- For an invertible on-site map, the tensor power of the inverse is a right inverse of the
tensor power. -/
lemma onSiteTensorPow_mul_inv (L : ℕ) {Λ : Matrix (Fin d) (Fin d) ℂ} (hΛ : IsUnit Λ) :
    onSiteTensorPow L Λ * onSiteTensorPow L Λ⁻¹ = 1 := by
  rw [← onSiteTensorPow_mul, Matrix.mul_nonsing_inv Λ ((Matrix.isUnit_iff_isUnit_det Λ).1 hΛ),
    onSiteTensorPow_one]

/-- The matrix product vector of the deformed tensor is the tensor power applied to the
original matrix product vector: \(\ket{\psi'} = \Lambda^{\otimes N}\ket{\psi}\), arXiv:2011.12127,
line 2036. -/
theorem mpv_rotatePhysical_eq_toLin' (Λ : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D)
    (N : ℕ) :
    (mpv (rotatePhysical Λ A) : NSiteSpace d N) =
      Matrix.toLin' (onSiteTensorPow N Λ) (mpv A : NSiteSpace d N) := by
  ext s
  rw [mpv_rotatePhysical]
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-! ### The local ground space of the deformed tensor -/

/-- The boundary map of the deformed tensor is the tensor power applied to the boundary
map of the original tensor. -/
theorem groundSpaceMap_rotatePhysical (Λ : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D)
    (L : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    groundSpaceMap (rotatePhysical Λ A) L X =
      Matrix.toLin' (onSiteTensorPow L Λ) (groundSpaceMap A L X) := by
  ext σ
  simp [groundSpaceMap_apply, evalWord_rotatePhysical_ofFn, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul]

/-- The local ground space of the deformed tensor is the image of the local ground space of
the original tensor under the tensor power: \(\mathcal G_L(\Lambda A) =
\Lambda^{\otimes L}\mathcal G_L(A)\).  This is the parenthetical generalization of
arXiv:2011.12127, lines 2035--2037, at the level of local ground spaces; no invertibility of
\(\Lambda\) is needed for this inclusion-as-equality. -/
theorem groundSpace_rotatePhysical (Λ : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D)
    (L : ℕ) :
    groundSpace (rotatePhysical Λ A) L =
      (groundSpace A L).map (Matrix.toLin' (onSiteTensorPow L Λ)) := by
  have h : groundSpaceMap (rotatePhysical Λ A) L =
      (Matrix.toLin' (onSiteTensorPow L Λ)).comp (groundSpaceMap A L) :=
    LinearMap.ext (groundSpaceMap_rotatePhysical Λ A L)
  rw [groundSpace, groundSpace, h, LinearMap.range_comp]

/-- The Hilbert-space realization of the local ground space of the deformed tensor is the
image under the tensor power of the realization for the original tensor. -/
theorem groundSpaceES_rotatePhysical (Λ : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D)
    (L : ℕ) :
    groundSpaceES (rotatePhysical Λ A) L =
      (groundSpaceES A L).map (Matrix.toEuclideanLin (onSiteTensorPow L Λ)) := by
  rw [groundSpaceES, groundSpaceES, groundSpace_rotatePhysical, ← Submodule.map_comp,
    ← Submodule.map_comp]
  rfl

/-! ### The deformed parent interaction -/

/-- A parent interaction on \(L\) sites for the tensor \(A\), in the sense of
arXiv:2011.12127, lines 1996--1999: a hermitian positive semidefinite operator \(h \ge 0\)
on the \(L\)-site Hilbert space whose kernel is the local ground space \(\mathcal G_L(A)\). -/
structure IsParentInteraction (A : MPSTensor d D) (L : ℕ)
    (h : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L)) : Prop where
  /-- The interaction is hermitian and positive semidefinite. -/
  isPositive : h.IsPositive
  /-- The kernel of the interaction is the local ground space. -/
  ker_eq : LinearMap.ker h = groundSpaceES A L

/-- The canonical parent interaction, the orthogonal projector onto
\(\mathcal G_L(A)^\perp\), is a parent interaction in the sense of the source definition. -/
theorem isParentInteraction_parentInteractionES (A : MPSTensor d D) (L : ℕ) :
    IsParentInteraction A L (parentInteractionES A L) where
  isPositive := parentInteractionES_isPositive A L
  ker_eq := by
    ext v
    rw [LinearMap.mem_ker, parentInteractionES_apply_eq_zero_iff]

/-- The deformed interaction
\(h' = ({\Lambda^{-1}}^\dagger)^{\otimes L}\, h\, (\Lambda^{-1})^{\otimes L}\) of
arXiv:2011.12127, lines 2190--2192, and equation deformed-parent-1 at lines 2033--2035. -/
noncomputable def deformedInteraction (L : ℕ) (Λ : Matrix (Fin d) (Fin d) ℂ)
    (h : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L)) :
    EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  Matrix.toEuclideanLin (onSiteTensorPow L (Λ⁻¹)ᴴ) ∘ₗ h ∘ₗ
    Matrix.toEuclideanLin (onSiteTensorPow L Λ⁻¹)

/-- The deformed interaction of a positive operator is positive: it is the conjugate
\(S^\dagger h S\) with \(S = (\Lambda^{-1})^{\otimes L}\). -/
theorem deformedInteraction_isPositive (L : ℕ) (Λ : Matrix (Fin d) (Fin d) ℂ)
    {h : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L)}
    (hh : h.IsPositive) : (deformedInteraction L Λ h).IsPositive := by
  rw [deformedInteraction, ← onSiteTensorPow_conjTranspose,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact hh.adjoint_conj _

/-- Composition of the Hilbert-space maps of two tensor powers is the map of the tensor
power of the product. -/
lemma toEuclideanLin_onSiteTensorPow_mul_apply (L : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Cfg d L)) :
    Matrix.toEuclideanLin (onSiteTensorPow L Λ)
        (Matrix.toEuclideanLin (onSiteTensorPow L Λ') v) =
      Matrix.toEuclideanLin (onSiteTensorPow L (Λ * Λ')) v := by
  rw [onSiteTensorPow_mul, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  rfl

/-- The kernel of the deformed interaction is the local ground space of the deformed
tensor: \(\ker h' = \Lambda^{\otimes L}\ker h = \mathcal G_L(\Lambda A)\). -/
theorem ker_deformedInteraction (L : ℕ) {Λ : Matrix (Fin d) (Fin d) ℂ} (hΛ : IsUnit Λ)
    {A : MPSTensor d D} {h : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L)}
    (hker : LinearMap.ker h = groundSpaceES A L) :
    LinearMap.ker (deformedInteraction L Λ h) = groundSpaceES (rotatePhysical Λ A) L := by
  have hdet : IsUnit Λ.det := (Matrix.isUnit_iff_isUnit_det Λ).1 hΛ
  have hleft : ∀ v : EuclideanSpace ℂ (Cfg d L),
      Matrix.toEuclideanLin (onSiteTensorPow L Λ)
        (Matrix.toEuclideanLin (onSiteTensorPow L Λ⁻¹) v) = v := by
    intro v
    rw [toEuclideanLin_onSiteTensorPow_mul_apply, Matrix.mul_nonsing_inv Λ hdet,
      onSiteTensorPow_one, Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]
  have hright : ∀ v : EuclideanSpace ℂ (Cfg d L),
      Matrix.toEuclideanLin (onSiteTensorPow L Λ⁻¹)
        (Matrix.toEuclideanLin (onSiteTensorPow L Λ) v) = v := by
    intro v
    rw [toEuclideanLin_onSiteTensorPow_mul_apply, Matrix.nonsing_inv_mul Λ hdet,
      onSiteTensorPow_one, Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]
  have hadj : ∀ v : EuclideanSpace ℂ (Cfg d L),
      Matrix.toEuclideanLin (onSiteTensorPow L Λᴴ)
        (Matrix.toEuclideanLin (onSiteTensorPow L (Λ⁻¹)ᴴ) v) = v := by
    intro v
    rw [toEuclideanLin_onSiteTensorPow_mul_apply, ← Matrix.conjTranspose_mul,
      Matrix.nonsing_inv_mul Λ hdet, Matrix.conjTranspose_one, onSiteTensorPow_one,
      Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]
  rw [groundSpaceES_rotatePhysical, ← hker]
  ext v
  simp only [LinearMap.mem_ker, deformedInteraction, LinearMap.comp_apply, Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨Matrix.toEuclideanLin (onSiteTensorPow L Λ⁻¹) v, ?_, hleft v⟩
    have hzero := congrArg (Matrix.toEuclideanLin (onSiteTensorPow L Λᴴ)) hv
    rw [hadj, map_zero] at hzero
    simpa [LinearMap.mem_ker] using hzero
  · rintro ⟨u, hu, rfl⟩
    have hu' : h u = 0 := hu
    rw [hright, hu', map_zero]

/-- arXiv:2011.12127, lines 2190--2192: if \(A^i = \sum_j \Lambda_{ij} B^j\) with \(\Lambda\)
invertible and \(h\) is a parent interaction for \(B\) on \(k\) sites, then
\(h' = ({\Lambda^{-1}}^\dagger)^{\otimes k} h (\Lambda^{-1})^{\otimes k}\) is a parent
interaction for \(A\).  Here \(B\) is the tensor `A` and \(A\) is `rotatePhysical Λ A`. -/
theorem IsParentInteraction.deformedInteraction (L : ℕ) {Λ : Matrix (Fin d) (Fin d) ℂ}
    (hΛ : IsUnit Λ) {A : MPSTensor d D}
    {h : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L)}
    (hh : IsParentInteraction A L h) :
    IsParentInteraction (rotatePhysical Λ A) L (MPSTensor.deformedInteraction L Λ h) where
  isPositive := deformedInteraction_isPositive L Λ hh.isPositive
  ker_eq := ker_deformedInteraction L hΛ hh.ker_eq

/-! ### The chain ground spaces

The source argument at arXiv:2011.12127, lines 2035--2037, applies to a ground state
\(\ket\Phi\) of the deformed chain Hamiltonian the operator \(X\) that acts as \(\Lambda\)
on the sites of one local term and as \(\Lambda^{-1}\) on all other sites.  The identity
below is the corresponding factorization of \(\Lambda^{\otimes N}\) across a cyclic window
and its complement: the restriction to a window of \(\Lambda^{\otimes N}\phi\) is
\(\Lambda^{\otimes L}\) applied to a linear combination of restrictions of \(\phi\). -/

/-- The sites of the cyclic window at \(i\) are the images of the offsets below \(L\). -/
private lemma prod_eq_window_mul_compl {N L : ℕ} (hLN : L ≤ N) (i : Fin N) (f : Fin N → ℂ) :
    ∏ k : Fin N, f k =
      (∏ r : Fin L, f (cyclicForwardSite i r.val)) *
        ∏ k ∈ (cyclicWindowSupport N L i)ᶜ, f k := by
  rw [← Finset.prod_mul_prod_compl (cyclicWindowSupport N L i) f]
  congr 1
  rw [cyclicWindowSupport, Finset.prod_image, Finset.prod_range]
  intro x hx y hy hxy
  have hxN : x < N := Nat.lt_of_lt_of_le (Finset.mem_range.1 hx) hLN
  have hyN : y < N := Nat.lt_of_lt_of_le (Finset.mem_range.1 hy) hLN
  have hval := congrArg (fun k : Fin N => (k.val + N - i.val) % N) hxy
  simp only [cyclicForwardSite] at hval
  rwa [offset_mod_eq i.isLt hxN, offset_mod_eq i.isLt hyN] at hval

/-- Outside the cyclic window the replaced configuration agrees with the original one. -/
private lemma replaceWindow_apply_of_notMem {N L : ℕ} (hLN : L ≤ N) (i : Fin N)
    (σ : Cfg d N) (τ : Cfg d L) {k : Fin N} (hk : k ∉ cyclicWindowSupport N L i) :
    replaceWindow L hLN i σ τ k = σ k := by
  rw [mem_cyclicWindowSupport_iff hLN] at hk
  simp [replaceWindow, hk]

/-- Inside the cyclic window the replaced configuration reads the inserted word. -/
private lemma replaceWindow_cyclicForwardSite {N L : ℕ} (hLN : L ≤ N) (i : Fin N)
    (σ : Cfg d N) (τ : Cfg d L) (r : Fin L) :
    replaceWindow L hLN i σ τ (cyclicForwardSite i r.val) = τ r :=
  congrFun (extractWindow_replaceWindow L hLN i σ τ) r

/-- The involution on pairs (word, configuration) exchanging the inserted window word with
the window read from the configuration. -/
private def windowSwap {N L : ℕ} (hLN : L ≤ N) (i : Fin N) :
    Cfg d L × Cfg d N ≃ Cfg d L × Cfg d N where
  toFun p := (extractWindow L i p.2, replaceWindow L hLN i p.2 p.1)
  invFun p := (extractWindow L i p.2, replaceWindow L hLN i p.2 p.1)
  left_inv p := by
    obtain ⟨σ', ω⟩ := p
    simp only [extractWindow_replaceWindow, replaceWindow_replaceWindow_same,
      replaceWindow_extractWindow]
  right_inv p := by
    obtain ⟨σ', ω⟩ := p
    simp only [extractWindow_replaceWindow, replaceWindow_replaceWindow_same,
      replaceWindow_extractWindow]

/-- Restricting \(\Lambda^{\otimes N}\phi\) to the cyclic window at \(i\) with outside
configuration \(\tau\) is \(\Lambda^{\otimes L}\) applied to a linear combination of
restrictions of \(\phi\); the coefficients are the products of the entries of \(\Lambda\)
over the sites outside the window.  This is the factorization behind the operator \(X\) of
arXiv:2011.12127, lines 2035--2037. -/
theorem cyclicRestrictₗ_toLin'_onSiteTensorPow {N L : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (i : Fin N) (τ : Cfg d N) (Λ : Matrix (Fin d) (Fin d) ℂ) (φ : NSiteSpace d N) :
    cyclicRestrictₗ hN L i τ (Matrix.toLin' (onSiteTensorPow N Λ) φ) =
      Matrix.toLin' (onSiteTensorPow L Λ)
        (∑ ω : Cfg d N,
          (if extractWindow L i ω = extractWindow L i τ then
            ∏ k ∈ (cyclicWindowSupport N L i)ᶜ, Λ (τ k) (ω k) else 0) •
            cyclicRestrictₗ hN L i ω φ) := by
  ext σ
  have hcfg : ∀ (σ' : Cfg d L) (ω : Cfg d N),
      cyclicCfg hN L i σ' ω = replaceWindow L hLN i ω σ' := fun _ _ => rfl
  -- Reindex a double sum over (window word, configuration) by the window swap.
  have key : ∀ F : Cfg d L → Cfg d N → ℂ,
      ∑ σ' : Cfg d L, ∑ ω : Cfg d N, F σ' ω =
        ∑ σ' : Cfg d L, ∑ ω : Cfg d N,
          F (extractWindow L i ω) (replaceWindow L hLN i ω σ') := by
    intro F
    calc
      ∑ σ' : Cfg d L, ∑ ω : Cfg d N, F σ' ω
          = ∑ p : Cfg d L × Cfg d N, F p.1 p.2 := (Fintype.sum_prod_type' F).symm
      _ = ∑ p : Cfg d L × Cfg d N,
            F (windowSwap (d := d) hLN i p).1 (windowSwap (d := d) hLN i p).2 :=
          ((windowSwap (d := d) hLN i).sum_comp fun p => F p.1 p.2).symm
      _ = ∑ σ' : Cfg d L, ∑ ω : Cfg d N,
            F (extractWindow L i ω) (replaceWindow L hLN i ω σ') :=
          Fintype.sum_prod_type'
            fun σ' ω => F (extractWindow L i ω) (replaceWindow L hLN i ω σ')
  simp only [cyclicRestrictₗ_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    onSiteTensorPow_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcfg]
  simp only [Finset.mul_sum]
  rw [key]
  simp only [extractWindow_replaceWindow, replaceWindow_replaceWindow_same,
    replaceWindow_extractWindow]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hwin : ∀ r : Fin L,
      Λ (replaceWindow L hLN i τ σ (cyclicForwardSite i r.val))
          (ω (cyclicForwardSite i r.val)) =
        Λ (σ r) (extractWindow L i ω r) := fun r => by
    rw [replaceWindow_cyclicForwardSite hLN i τ σ]
    rfl
  have hout : ∀ k ∈ (cyclicWindowSupport N L i)ᶜ,
      Λ (replaceWindow L hLN i τ σ k) (ω k) =
        Λ (τ k) (replaceWindow L hLN i ω (extractWindow L i τ) k) := fun k hk => by
    rw [replaceWindow_apply_of_notMem hLN i τ σ (Finset.mem_compl.1 hk),
      replaceWindow_apply_of_notMem hLN i ω (extractWindow L i τ) (Finset.mem_compl.1 hk)]
  rw [prod_eq_window_mul_compl hLN i, mul_assoc, Finset.prod_congr rfl fun r _ => hwin r,
    Finset.prod_congr rfl hout]

/-- The tensor power maps the chain ground space of \(A\) into the chain ground space of
the deformed tensor \(\Lambda A\).  No invertibility of \(\Lambda\) is needed. -/
theorem map_chainGroundSpace_le_chainGroundSpace_rotatePhysical
    (Λ : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) (L N : ℕ) :
    (chainGroundSpace A L N).map (Matrix.toLin' (onSiteTensorPow N Λ)) ≤
      chainGroundSpace (rotatePhysical Λ A) L N := by
  intro ψ hψ
  obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hψ
  rw [chainGroundSpace] at hφ ⊢
  by_cases hNL : 0 < N ∧ L ≤ N
  · rw [dite_eq_left hNL] at hφ ⊢
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ ⊢
    intro i τ
    rw [cyclicRestrictₗ_toLin'_onSiteTensorPow hNL.1 hNL.2 i τ Λ φ, groundSpace_rotatePhysical]
    exact Submodule.mem_map_of_mem
      (Submodule.sum_mem _ fun ω _ => Submodule.smul_mem _ _ (hφ i ω))
  · rw [dite_eq_right hNL]
    exact Submodule.mem_top

/-- The one-to-one correspondence of arXiv:2011.12127, lines 2035--2037, between the ground
states of the parent Hamiltonians of \(\ket\psi\) and \(\ket{\psi'} = R^{\otimes N}\ket\psi\)
for an invertible on-site map \(R\): the chain ground space of the deformed tensor is the
image of the chain ground space of the original tensor under \(R^{\otimes N}\). -/
theorem chainGroundSpace_rotatePhysical {Λ : Matrix (Fin d) (Fin d) ℂ} (hΛ : IsUnit Λ)
    (A : MPSTensor d D) (L N : ℕ) :
    chainGroundSpace (rotatePhysical Λ A) L N =
      (chainGroundSpace A L N).map (Matrix.toLin' (onSiteTensorPow N Λ)) := by
  refine le_antisymm ?_ (map_chainGroundSpace_le_chainGroundSpace_rotatePhysical Λ A L N)
  have hdet : IsUnit Λ.det := (Matrix.isUnit_iff_isUnit_det Λ).1 hΛ
  have hinv := map_chainGroundSpace_le_chainGroundSpace_rotatePhysical Λ⁻¹
    (rotatePhysical Λ A) L N
  rw [rotatePhysical_rotatePhysical, Matrix.nonsing_inv_mul Λ hdet, rotatePhysical_one] at hinv
  intro ψ hψ
  refine ⟨Matrix.toLin' (onSiteTensorPow N Λ⁻¹) ψ, hinv (Submodule.mem_map_of_mem hψ), ?_⟩
  rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, onSiteTensorPow_mul_inv N hΛ,
    Matrix.toLin'_one, LinearMap.id_apply]

/-- The ground spaces of the parent Hamiltonians of \(\ket\psi\) and
\(\ket{\psi'} = R^{\otimes N}\ket\psi\) correspond one-to-one through \(R^{\otimes N}\)
(arXiv:2011.12127, lines 2035--2037), stated for the kernels of the finite parent
Hamiltonians in the range \(0 < N\), \(L \le N\) where the local terms act on genuine
cyclic windows. -/
theorem ker_parentHamiltonian_rotatePhysical {Λ : Matrix (Fin d) (Fin d) ℂ} (hΛ : IsUnit Λ)
    (A : MPSTensor d D) {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    LinearMap.ker (parentHamiltonian (rotatePhysical Λ A) L N) =
      (LinearMap.ker (parentHamiltonian A L N)).map (Matrix.toLin' (onSiteTensorPow N Λ)) := by
  rw [ker_parentHamiltonian_eq_chainGroundSpace _ hN hLN,
    ker_parentHamiltonian_eq_chainGroundSpace _ hN hLN, chainGroundSpace_rotatePhysical hΛ]

/-- The tensor power of an invertible on-site map as a linear automorphism of the
\(N\)-site space. -/
noncomputable def onSiteTensorPowEquiv (N : ℕ) {Λ : Matrix (Fin d) (Fin d) ℂ}
    (hΛ : IsUnit Λ) : NSiteSpace d N ≃ₗ[ℂ] NSiteSpace d N :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (onSiteTensorPow N Λ))
    (Matrix.toLin' (onSiteTensorPow N Λ⁻¹))
    (by rw [← Matrix.toLin'_mul, onSiteTensorPow_mul_inv N hΛ, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, onSiteTensorPow_inv_mul N hΛ, Matrix.toLin'_one])

/-- arXiv:2011.12127, lines 2037--2038: if the parent Hamiltonian of \(A\) has a unique
ground state, then so does the parent Hamiltonian of the deformed tensor \(\Lambda A\), since
the two ground spaces correspond through the invertible map \(\Lambda^{\otimes N}\). -/
theorem hasUniqueGroundState_chainGroundSpace_rotatePhysical
    {Λ : Matrix (Fin d) (Fin d) ℂ} (hΛ : IsUnit Λ) {A : MPSTensor d D} {L N : ℕ}
    (hA : HasUniqueGroundState (chainGroundSpace A L N)) :
    HasUniqueGroundState (chainGroundSpace (rotatePhysical Λ A) L N) := by
  rw [HasUniqueGroundState, chainGroundSpace_rotatePhysical hΛ]
  exact (LinearEquiv.finrank_map_eq (onSiteTensorPowEquiv N hΛ) (chainGroundSpace A L N)).trans hA

end MPSTensor
