/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardFormConjugation
import TNLean.MPS.MPU.TwoSiteStandardFormSourceCuts
import TNLean.MPS.Symmetry.TimeReversalIndex

/-!
# The MPS sign of a conjugation-invariant matrix product unitary

Proposition `prop:mps-class-eq-mpu-class-for-conjugation` of arXiv:1703.09188
(lines 1791--1797) compares two signs of a conjugation-invariant MPU. Viewed
as a matrix product state, the standard-form tensor `𝒲` and its entrywise
conjugate are related by a unitary gauge, `conj(𝒲ⁱ) = ζ G† 𝒲ⁱ G`, and
`G conj(G) = ±1` is the sign of the classification of MPS phases
(`eq:mps-class-gauge-trafo`, lines 1761--1788). On the other hand,
Proposition `corconj` sorts the MPU into Case I or Case II according to
whether the unitary `x` of Proposition `prop1conj` is symmetric or
skew-symmetric. The proposition states that the two signs agree, "i.e." that
the sign also labels the two MPU phases under equivalence. This file proves
the first half, the agreement of the two signs.

The source proof (lines 1799--1805) deduces this from the classification of
the phases under conjugation (Corollary `cor:equiv-under-conjugation`), the
invariance of the MPS sign along a path, and the example `u = v = 1`. The proof
here is local instead. The
standard-form tensor is the open contraction `𝒲 = A u B` of the unshifted
gate `u` with two half factors. Since `u` is unitary, the relation
`conj(u) = (x ⊗ y) u` and the gauge relation force
`conj(A) x = c G† A` for a nonzero scalar `c`. Conjugating once more gives
`A = |c|² (G conj G) A (x† xᵀ)`, so the two signs agree.

As in `prop1conj`, the tensor in standard form is the two-site block `𝒱₂` of
a simple tensor `𝒱` in canonical form II
(`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`). The closing
clause of the source, that the two cases are "the two possible MPU phases
under equivalence", is Corollary `cor:equiv-under-conjugation`; the full
proposition combines that corollary with these statements.

## Main results

* `MPOTensor.TwoSiteStandardFormData.sign_eq_of_conjugation_gauge`.
* `MPOTensor.IsMPUCanonicalFormII.mps_conjugation_sign_iff`,
  `MPOTensor.IsMPUCanonicalFormII.mps_conjugation_sign_iff_of_gauge`: the first half
  of Proposition `prop:mps-class-eq-mpu-class-for-conjugation`, for a gauge of the standard-form
  tensor and of the MPU tensor.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D ℓ r : ℕ}

/-- Contracting `P uⱼ Q` against the conjugate entries of a coisometric gate
recovers the product of the outer entries. Source: arXiv:1703.09188, the
relation `u u† = 1` of `eq:uu`, lines 532--543. -/
theorem sum_mul_gate_mul_star_eq
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} (hu : u.IsCoisometry)
    (P : Matrix (Fin D) (Fin ℓ) ℂ) (Q : Matrix (Fin r) (Fin D) ℂ)
    (α γ : Fin D) (t : Fin ℓ) (s : Fin r) :
    ∑ j : Fin d × Fin d,
        (∑ t' : Fin ℓ, ∑ s' : Fin r, P α t' * u (t', s') j * Q s' γ) *
          starRingEnd ℂ (u (t, s) j) =
      P α t * Q s γ := by
  have hδ : ∀ t' s', ∑ j, u (t', s') j * starRingEnd ℂ (u (t, s) j) =
      if (t', s') = (t, s) then 1 else 0 := by
    intro t' s'
    have := congrFun (congrFun hu (t', s')) (t, s)
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  calc
    _ = ∑ t' : Fin ℓ, ∑ s' : Fin r, P α t' * Q s' γ *
          ∑ j, u (t', s') j * starRingEnd ℂ (u (t, s) j) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s' _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = P α t * Q s γ := by
        simp only [hδ, mul_ite, mul_one, mul_zero, Prod.mk.injEq]
        simp [ite_and, Finset.sum_ite_eq']

/-- The slice of a gate at one physical output pair, as an `ℓ × r` matrix. -/
def gateSlice (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) (j : Fin d × Fin d) :
    Matrix (Fin ℓ) (Fin r) ℂ :=
  fun t s => u (t, s) j

/-- Matrix form of `sum_mul_gate_mul_star_eq`. -/
theorem sum_mul_gateSlice_mul_star_eq
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} (hu : u.IsCoisometry)
    (P : Matrix (Fin D) (Fin ℓ) ℂ) (Q : Matrix (Fin r) (Fin D) ℂ)
    (α γ : Fin D) (t : Fin ℓ) (s : Fin r) :
    ∑ j : Fin d × Fin d, (P * gateSlice u j * Q) α γ * starRingEnd ℂ (u (t, s) j) =
      P α t * Q s γ := by
  rw [← sum_mul_gate_mul_star_eq hu P Q α γ t s]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [Matrix.mul_apply, gateSlice, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- If `P uⱼ Q = P' uⱼ Q'` for every slice of a coisometric gate, then the
outer factors agree as a tensor product. -/
theorem mul_eq_mul_of_mul_gateSlice_mul_eq
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} (hu : u.IsCoisometry)
    {P P' : Matrix (Fin D) (Fin ℓ) ℂ} {Q Q' : Matrix (Fin r) (Fin D) ℂ}
    (h : ∀ j, P * gateSlice u j * Q = P' * gateSlice u j * Q')
    (α γ : Fin D) (t : Fin ℓ) (s : Fin r) :
    P α t * Q s γ = P' α t * Q' s γ := by
  rw [← sum_mul_gateSlice_mul_star_eq hu P Q, ← sum_mul_gateSlice_mul_star_eq hu P' Q']
  simp only [h]

/-- The conjugation relation `conj(u) = (x ⊗ y) u` of `prop1conj` on one
slice of the gate. -/
theorem gateSlice_map_star_of_conjugation
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y : Matrix (Fin r) (Fin r) ℂ}
    (hu : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) (j : Fin d × Fin d) :
    (gateSlice u j).map (starRingEnd ℂ) = x * gateSlice u j * yᵀ := by
  ext t s
  have := congrFun (congrFun hu (t, s)) j
  simp only [Matrix.map_apply] at this
  simp only [Matrix.map_apply, gateSlice, this, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t' _ => Finset.sum_congr rfl fun s' _ => ?_
  ring

namespace TwoSiteStandardFormData

variable {W : MPOTensor (d * d) D}
  {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
  {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}

/-- The left half factor at one physical input, a `D × ℓ` matrix. -/
def halfLeft (T : TwoSiteStandardFormData W u v) (i : Fin d) : Matrix (Fin D) (Fin ℓ) ℂ :=
  fun α t => T.X₂ (α, i) t

/-- The right half factor at one physical input, an `r × D` matrix. -/
def halfRight (T : TwoSiteStandardFormData W u v) (i : Fin d) : Matrix (Fin r) (Fin D) ℂ :=
  fun s γ => T.X₁ (i, γ) s

/-- The standard-form tensor is the product `A u B` of the left half factor,
a gate slice, and the right half factor. Source: arXiv:1703.09188,
`StandardForm`, lines 603--617. -/
theorem W_eq_halfLeft_mul (T : TwoSiteStandardFormData W u v) (i₁ i₂ : Fin d)
    (j : Fin d × Fin d) :
    W (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv j) =
      T.halfLeft i₁ * gateSlice u j * T.halfRight i₂ := by
  ext α γ
  rw [T.W_apply]
  simp only [Equiv.symm_apply_apply, Matrix.mul_apply, halfLeft, halfRight, gateSlice,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The shifted gate is the product `B A` of the half factors. Source:
arXiv:1703.09188, `StandardForm`, lines 603--617. -/
theorem v_apply_eq_halfRight_mul (T : TwoSiteStandardFormData W u v) (i₁ i₂ : Fin d)
    (s : Fin r) (t : Fin ℓ) :
    v (i₁, i₂) (s, t) = (T.halfRight i₁ * T.halfLeft i₂) s t := by
  rw [T.v_apply]
  rfl

theorem v_ne_zero (T : TwoSiteStandardFormData W u v) : v ≠ 0 := by
  intro hv
  have h : vᴴ * v = 1 := T.v_unitary.1
  rw [hv, Matrix.conjTranspose_zero, Matrix.zero_mul] at h
  have := congrFun (congrFun h (⟨0, T.right_pos⟩, ⟨0, T.left_pos⟩))
    (⟨0, T.right_pos⟩, ⟨0, T.left_pos⟩)
  simp at this

theorem exists_halfLeft_ne_zero (T : TwoSiteStandardFormData W u v) :
    ∃ i, T.halfLeft i ≠ 0 := by
  by_contra h
  push Not at h
  refine T.v_ne_zero (Matrix.ext fun p q => ?_)
  rw [T.v_apply_eq_halfRight_mul p.1 p.2 q.1 q.2, h p.2, Matrix.mul_zero]
  rfl

theorem exists_halfRight_ne_zero (T : TwoSiteStandardFormData W u v) :
    ∃ i, T.halfRight i ≠ 0 := by
  by_contra h
  push Not at h
  refine T.v_ne_zero (Matrix.ext fun p q => ?_)
  rw [T.v_apply_eq_halfRight_mul p.1 p.2 q.1 q.2, h p.1, Matrix.zero_mul]
  rfl

end TwoSiteStandardFormData

/-- Entrywise conjugation of a scalar multiple. -/
theorem map_star_smul {m n : Type*} (c : ℂ) (M : Matrix m n ℂ) :
    (c • M).map (starRingEnd ℂ) = starRingEnd ℂ c • M.map (starRingEnd ℂ) := by
  ext i j
  simp

/-- Entrywise conjugation of an adjoint is the transpose. -/
theorem conjTranspose_map_star {m n : Type*} (M : Matrix m n ℂ) :
    Mᴴ.map (starRingEnd ℂ) = Mᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

/-- **The MPS sign equals the sign of `x`.** Let `𝒲 = A u B` be a tensor in
standard form whose gate satisfies `conj(u) = (x ⊗ y) u` with unitaries `x, y`,
and let `X` be a unitary gauge with `conj(𝒲ⁱʲ) = ζ X† 𝒲ⁱʲ X`. If `xᵀ = s x` and
`X conj(X) = s' 1` with `s, s' ∈ {1, -1}`, then `s = s'`.

Source: arXiv:1703.09188, the first half of Proposition
`prop:mps-class-eq-mpu-class-for-conjugation`, lines 1791--1797. The proof is
local; see the module docstring. -/
theorem TwoSiteStandardFormData.sign_eq_of_conjugation_gauge
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (T : TwoSiteStandardFormData W u v)
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} (hx : x ∈ Matrix.unitaryGroup (Fin ℓ) ℂ)
    {y : Matrix (Fin r) (Fin r) ℂ} (hy : y ∈ Matrix.unitaryGroup (Fin r) ℂ)
    (hu : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ)
    (hgauge : ∀ i j, (W i j).map (starRingEnd ℂ) = ζ • (Xᴴ * W i j * X))
    {s s' : ℂ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1)
    (hxs : xᵀ = s • x) (hXs : X * X.map (starRingEnd ℂ) = s' • 1) :
    s = s' := by
  have huc : u.IsCoisometry := T.u_unitary.2
  set A := T.halfLeft
  set B := T.halfRight
  have key : ∀ i₁ i₂ j, (A i₁).map (starRingEnd ℂ) * x * gateSlice u j *
      (yᵀ * (B i₂).map (starRingEnd ℂ)) =
        Xᴴ * A i₁ * gateSlice u j * (ζ • (B i₂ * X)) := by
    intro i₁ i₂ j
    have h1 := hgauge (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv j)
    rw [T.W_eq_halfLeft_mul, Matrix.map_mul, Matrix.map_mul,
      gateSlice_map_star_of_conjugation hu] at h1
    calc _ = (A i₁).map (starRingEnd ℂ) * (x * gateSlice u j * yᵀ) *
          (B i₂).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
      _ = _ := h1
      _ = _ := by rw [Matrix.mul_smul]; simp only [Matrix.mul_assoc]; rfl
  have hent := fun i₁ i₂ => mul_eq_mul_of_mul_gateSlice_mul_eq huc (key i₁ i₂)
  -- A nonzero entry of the right factor `yᵀ conj(B)`.
  obtain ⟨i₂, hB⟩ := T.exists_halfRight_ne_zero
  have hyy : y.map (starRingEnd ℂ) * yᵀ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hy
    rw [Matrix.star_eq_conjTranspose] at h
    have := congrArg (·.map (starRingEnd ℂ)) h
    simpa only [Matrix.map_mul, conjTranspose_map_star, Matrix.map_one _ (map_zero _)
      (map_one _)] using this
  have hQ : yᵀ * (B i₂).map (starRingEnd ℂ) ≠ 0 := by
    intro h0
    apply hB
    have : (B i₂).map (starRingEnd ℂ) = 0 := by
      rw [← Matrix.one_mul ((B i₂).map _), ← hyy, Matrix.mul_assoc, h0, Matrix.mul_zero]
    ext a b
    simpa using congrFun (congrFun this a) b
  obtain ⟨s₀, γ₀, hQ₀⟩ : ∃ a b, (yᵀ * (B i₂).map (starRingEnd ℂ)) a b ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (Matrix.ext h)
  set c : ℂ := (ζ • (B i₂ * X)) s₀ γ₀ / (yᵀ * (B i₂).map (starRingEnd ℂ)) s₀ γ₀
  have hP : ∀ i₁, (A i₁).map (starRingEnd ℂ) * x = c • (Xᴴ * A i₁) := by
    intro i₁
    ext α t
    have h := hent i₁ i₂ α γ₀ t s₀
    rw [Matrix.smul_apply, smul_eq_mul]
    simp only [c]
    field_simp
    linear_combination h
  -- Conjugating twice.
  have hxx : x * xᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hx
  have hxx' : xᴴ * xᵀ = s • 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hx
    rw [Matrix.star_eq_conjTranspose] at h
    rw [hxs, Matrix.mul_smul, h]
  have hXX : X * Xᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hX
  have hss' : starRingEnd ℂ s' = s' := by rcases hs' with rfl | rfl <;> simp
  have hs'2 : s' * s' = 1 := by rcases hs' with rfl | rfl <;> norm_num
  have hXT : Xᵀ = s' • X := by
    have h1 : X.map (starRingEnd ℂ) = s' • Xᴴ := by
      have h := Matrix.mem_unitaryGroup_iff'.mp hX
      rw [Matrix.star_eq_conjTranspose] at h
      calc X.map (starRingEnd ℂ) = Xᴴ * (X * X.map (starRingEnd ℂ)) := by
            rw [← Matrix.mul_assoc, h, Matrix.one_mul]
        _ = _ := by rw [hXs, Matrix.mul_smul, Matrix.mul_one]
    have h2 : Xᴴ = s' • X.map (starRingEnd ℂ) := by
      rw [h1, smul_smul, hs'2, one_smul]
    have := congrArg (·.map (starRingEnd ℂ)) h2
    simp only [conjTranspose_map_star, map_star_smul, hss'] at this
    rw [this]
    congr 1
    ext a b
    simp
  have hXX' : Xᵀ * Xᴴ = s' • 1 := by rw [hXT, Matrix.smul_mul, hXX]
  obtain ⟨i₁, hA⟩ := T.exists_halfLeft_ne_zero
  have hAbar : (A i₁).map (starRingEnd ℂ) = c • (Xᴴ * A i₁ * xᴴ) := by
    calc (A i₁).map (starRingEnd ℂ) = (A i₁).map (starRingEnd ℂ) * x * xᴴ := by
          rw [Matrix.mul_assoc, hxx, Matrix.mul_one]
      _ = _ := by rw [hP, Matrix.smul_mul]
  have hAA : A i₁ = (starRingEnd ℂ c * c * s' * s) • A i₁ := by
    have := congrArg (·.map (starRingEnd ℂ)) hAbar
    simp only [map_star_smul, Matrix.map_mul, conjTranspose_map_star] at this
    have hmap : ((A i₁).map (starRingEnd ℂ)).map (starRingEnd ℂ) = A i₁ := by
      ext a b; simp
    rw [hmap] at this
    calc A i₁ = starRingEnd ℂ c • (Xᵀ * (A i₁).map (starRingEnd ℂ) * xᵀ) := this
      _ = starRingEnd ℂ c • (Xᵀ * (c • (Xᴴ * A i₁ * xᴴ)) * xᵀ) := by rw [hAbar]
      _ = (starRingEnd ℂ c * c) • ((Xᵀ * Xᴴ) * A i₁ * (xᴴ * xᵀ)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hXX', hxx', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
            smul_smul, smul_smul]
          ring_nf
  have hk : starRingEnd ℂ c * c * s' * s = 1 := by
    have h0 : (starRingEnd ℂ c * c * s' * s - 1) • A i₁ = 0 := by
      rw [sub_smul, ← hAA, one_smul, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hA
  have hnorm : starRingEnd ℂ c * c = (Complex.normSq c : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  rw [hnorm] at hk
  have hn := Complex.normSq_nonneg c
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
  · rfl
  · exfalso
    have := congrArg Complex.re hk
    simp at this
    linarith
  · exfalso
    have := congrArg Complex.re hk
    simp at this
    linarith
  · rfl

/-- **The MPS sign of a conjugation-invariant MPU is its standard-form case.**
Let `𝒱` be a simple tensor in canonical form II, let `u` be the gate of
source factors normalized at its canonical fixed point, so that `𝒱₂` is in
standard form, and let `x, y` be unitaries with `conj(u) = (x ⊗ y) u`, as in
Proposition `prop1conj`. Let `G` be a unitary gauge of the matrix product
state of `𝒱₂` under conjugation: `conj(𝒱₂ⁱʲ) = ζ G† 𝒱₂ⁱʲ G` for every pair
of physical indices. Then `G conj(G) = 1` exactly in Case I (`xᵀ = x`) and
`G conj(G) = -1` exactly in Case II (`xᵀ = -x`) of Proposition `corconj`.

Source: arXiv:1703.09188, the first half of Proposition
`prop:mps-class-eq-mpu-class-for-conjugation`, lines 1791--1797, with the
sign `G conj(G) = ±1` of `eq:mps-class-gauge-trafo` (lines 1761--1770) and the
unitary choice of `G` (lines 1780--1782), and the reading of a tensor in standard form in
`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`. The
identification of the two cases with the two phases under conjugation is
Corollary `cor:equiv-under-conjugation` and is not asserted here. -/
theorem IsMPUCanonicalFormII.mps_conjugation_sign_iff
    {V : MPOTensor d D} (hV : IsMPUCanonicalFormII V) (hsimple : IsMPUSimple V)
    (S : SourceFactors V hV.ρ)
    (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ)
    (hu : (SourceFactors.sourceU V S).map (starRingEnd ℂ) =
      ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
        SourceFactors.sourceU V S)
    (G : Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ)
    (hgauge : ∀ i j, (MPOTensor.blockTwo V i j).map (starRingEnd ℂ) =
      ζ • ((G : Matrix (Fin D) (Fin D) ℂ)ᴴ * MPOTensor.blockTwo V i j * G)) :
    ((G : Matrix (Fin D) (Fin D) ℂ) * (G : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 ↔
        (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)ᵀ = x) ∧
      ((G : Matrix (Fin D) (Fin D) ℂ) * (G : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = -1 ↔
        (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)ᵀ = -x) := by
  let : NeZero d := hV.neZero_phys
  let : NeZero D := hV.neZero_bond
  have huS := hV.sourceFactors_sourceU_isUnitaryBetween hsimple S
  obtain ⟨hl, hr⟩ := hV.nonempty_source_ranks S huS
  have hcase := Matrix.transpose_eq_self_or_transpose_eq_neg_of_gate_conjugation
    x.property y.property huS.2 hu
  obtain ⟨T⟩ := hV.exists_twoSiteStandardFormData_sourceFactors hsimple S
  -- The MPS sign of the normalized flattening.
  have hN : Kraus.IsNormal (MPOTensor.blockTwo V).normalizedFlattening :=
    hV.blockTwo.isNormalTensor_normalizedFlattening.isNormal
  have hG := MPSTensor.mul_map_star_eq_one_or_neg_one_of_timeReversal_gauge hN
    (P := 1) (by simp) G (ζ := ζ) (fun i => by
      simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      simp only [normalizedFlattening, toMPSTensor, map_star_smul, hgauge, Matrix.mul_smul,
        Matrix.smul_mul, smul_comm ζ]
      congr 1
      simp)
  -- The core comparison of the two signs.
  have hcore := fun {s s' : ℂ} hs hs' hxs hXs =>
    T.sign_eq_of_conjugation_gauge (s := s) (s' := s') x.property y.property hu G.property ζ
      hgauge hs hs' hxs hXs
  have hGne : (1 : Matrix (Fin D) (Fin D) ℂ) ≠ -1 := by
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this
  have hxne : (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ≠ -x := by
    intro h
    have h0 : (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) = 0 := by
      have : (2 : ℂ) • (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) = 0 := by
        rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel _
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    have hxx := Matrix.mem_unitaryGroup_iff.mp x.property
    rw [h0, zero_mul] at hxx
    obtain ⟨a⟩ := hl
    have := congrFun (congrFun hxx a) a
    simp at this
  rcases hcase with ⟨hx, -⟩ | ⟨hx, -⟩ <;> rcases hG with hG | hG
  · exact ⟨⟨fun _ => hx, fun _ => hG⟩, ⟨fun h => absurd (hG.symm.trans h) hGne,
      fun h => absurd (hx.symm.trans h) hxne⟩⟩
  · exfalso
    have := hcore (Or.inl rfl) (Or.inr rfl) (by rw [hx, one_smul]) (by rw [hG, neg_one_smul])
    norm_num at this
  · exfalso
    have := hcore (Or.inr rfl) (Or.inl rfl) (by rw [hx, neg_one_smul]) (by rw [hG, one_smul])
    norm_num at this
  · exact ⟨⟨fun h => absurd (h.symm.trans hG) hGne, fun h => absurd (h.symm.trans hx) hxne⟩,
      ⟨fun _ => hx, fun _ => hG⟩⟩

/-- A conjugation gauge of a tensor is a conjugation gauge of its two-site
block, with the square of the phase. -/
theorem blockTwo_map_star_eq_of_gauge {V : MPOTensor d D} (G : Matrix (Fin D) (Fin D) ℂ)
    (hG : G * Gᴴ = 1) (ζ : ℂ)
    (hgauge : ∀ i j, (V i j).map (starRingEnd ℂ) = ζ • (Gᴴ * V i j * G)) (i j : Fin (d * d)) :
    (MPOTensor.blockTwo V i j).map (starRingEnd ℂ) =
      (ζ * ζ) • (Gᴴ * MPOTensor.blockTwo V i j * G) := by
  simp only [MPOTensor.blockTwo, Matrix.map_mul, hgauge, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G, hG, Matrix.one_mul]

/-- **The MPS sign of a conjugation-invariant MPU, for a gauge of the MPU
tensor.** The same comparison as `mps_conjugation_sign_iff`, for a unitary
gauge `conj(𝒱ⁱʲ) = ζ G† 𝒱ⁱʲ G` of the one-site tensor `𝒱` itself; the
source notes that `G` is invariant under blocking (line 1774). Source:
arXiv:1703.09188, the first half of Proposition
`prop:mps-class-eq-mpu-class-for-conjugation`, lines 1791--1797. -/
theorem IsMPUCanonicalFormII.mps_conjugation_sign_iff_of_gauge
    {V : MPOTensor d D} (hV : IsMPUCanonicalFormII V) (hsimple : IsMPUSimple V)
    (S : SourceFactors V hV.ρ)
    (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ)
    (hu : (SourceFactors.sourceU V S).map (starRingEnd ℂ) =
      ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
        SourceFactors.sourceU V S)
    (G : Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ)
    (hgauge : ∀ i j, (V i j).map (starRingEnd ℂ) =
      ζ • ((G : Matrix (Fin D) (Fin D) ℂ)ᴴ * V i j * G)) :
    ((G : Matrix (Fin D) (Fin D) ℂ) * (G : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 ↔
        (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)ᵀ = x) ∧
      ((G : Matrix (Fin D) (Fin D) ℂ) * (G : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = -1 ↔
        (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)ᵀ = -x) :=
  hV.mps_conjugation_sign_iff hsimple S x y hu G (ζ * ζ)
    (blockTwo_map_star_eq_of_gauge (G : Matrix (Fin D) (Fin D) ℂ)
      (by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp G.property)
      ζ hgauge)

end MPOTensor
