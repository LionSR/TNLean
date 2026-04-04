/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.Stinespring
import TNLean.Algebra.TracePairing

/-!
# Rectangular Kraus freedom (Wolf Thm 2.1 item 4, necessary direction)

This file proves the necessary direction of the Kraus freedom theorem:
if two Kraus families define the same completely positive map, they are
related by a rectangular isometry.

## Main results

* `kraus_dual_eq_of_map_eq` — dual map equality from primal map equality
* `kraus_conjTranspose_mul_eq_of_map_eq` — equal Stinespring Gramians
* `kraus_rectangular_freedom` — two Kraus families `{Bα}` and `{Aj}` with
  `∑ Bα X Bα† = ∑ Aj X Aj†` are related by a rectangular isometry `V` satisfying
  `V†V = 1` and `Bα = ∑j Vαj • Aj`

## Proof outline (Wolf Thm 2.1 item 4)

The proof establishes that equal completely positive maps force equal Gram
structures on the vectorised Kraus operators, from which a rectangular isometry
is extracted via inner product preservation and isometry extension.

Concretely:
1. Map equality ⟹ entry-wise inner product equality for the "Stinespring vectors"
2. Inner product preservation ⟹ well-defined partial isometry on the span
3. Partial isometry extension to a full isometry (using `Fintype.card` ≤ constraint)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 2.1 item 4][Wolf2012QChannels]
* arXiv:1606.00608, §3 (application to RFP characterisation)
-/

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### Helper: dual map equality from primal map equality -/

/-- If two Kraus families define the same Schrödinger map, they also define
the same Heisenberg dual: `∑ Bα† Y Bα = ∑ Aj† Y Aj` for all `Y`.

This follows because a linear map determines its adjoint (w.r.t. the
trace inner product) uniquely. -/
theorem kraus_dual_eq_of_map_eq
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : Fin r₂ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ) :
    ∀ Y : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin r₁, (B α)ᴴ * Y * B α =
      ∑ j : Fin r₂, (A j)ᴴ * Y * A j := by
  intro Y
  suffices hsuff : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      trace ((∑ α : Fin r₁, (B α)ᴴ * Y * B α -
              ∑ j : Fin r₂, (A j)ᴴ * Y * A j) * X) = 0 by
    exact sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff _).mp hsuff)
  intro X
  rw [sub_mul, Matrix.trace_sub]
  simp_rw [Finset.sum_mul, Matrix.trace_sum]
  have trace_cycle : ∀ K : Matrix (Fin D) (Fin D) ℂ,
      trace (Kᴴ * Y * K * X) = trace (K * X * Kᴴ * Y) := fun K => by
    rw [Matrix.mul_assoc (Kᴴ * Y) K X, Matrix.trace_mul_comm,
        ← Matrix.mul_assoc (K * X) Kᴴ Y]
  simp_rw [trace_cycle]
  rw [← Matrix.trace_sum, ← Matrix.trace_sum,
      ← Finset.sum_mul, ← Finset.sum_mul]
  rw [h X]; ring

/-- Map equality implies equal Stinespring Gramians:
`∑ Bα†Bα = ∑ Aj†Aj`. -/
theorem kraus_conjTranspose_mul_eq_of_map_eq
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : Fin r₂ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ) :
    ∑ α : Fin r₁, (B α)ᴴ * B α =
    ∑ j : Fin r₂, (A j)ᴴ * A j := by
  have hdual := kraus_dual_eq_of_map_eq B A h
  simpa [Matrix.mul_one] using hdual 1

/-! ### Rectangular Kraus freedom -/

/-- Reindexing a sum from `Fin r₂` to `Fin r₁` via zero-padding. -/
private lemma sum_pad_zeros {r₁ r₂ : ℕ} {β : Type*} [AddCommMonoid β]
    (f : Fin r₂ → β) (hCard : r₂ ≤ r₁) :
    ∑ j : Fin r₂, f j =
    ∑ α : Fin r₁, if hlt : α.val < r₂ then f ⟨α.val, hlt⟩ else 0 := by
  symm
  have hsub : ∑ α ∈ Finset.univ.filter (fun α : Fin r₁ => α.val < r₂),
      (if hlt : α.val < r₂ then f ⟨α.val, hlt⟩ else 0) =
      ∑ α : Fin r₁, if hlt : α.val < r₂ then f ⟨α.val, hlt⟩ else 0 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro α _ hα
    have : ¬(α.val < r₂) := by simpa using hα
    simp [dif_neg this]
  rw [← hsub]; symm
  apply Finset.sum_nbij (fun j : Fin r₂ =>
    (⟨j.val, Nat.lt_of_lt_of_le j.isLt hCard⟩ : Fin r₁))
  · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  · intro j₁ _ j₂ _ hj; exact Fin.ext (Fin.mk.inj hj)
  · intro α hα
    have hα' := (Finset.mem_filter.mp (Finset.mem_coe.mp hα)).2
    exact ⟨⟨α.val, hα'⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
  · intro j _; simp [Fin.eta]

private abbrev KrausCoeffSpace (r : ℕ) := EuclideanSpace ℂ (Fin r)

private abbrev KrausEntrySpace (D : ℕ) := EuclideanSpace ℂ (Fin D × Fin D)

set_option synthInstance.maxHeartbeats 16000000 in
/-- Cached `InnerProductSpace` instance for `EuclideanSpace` to avoid synthesis timeout. -/
private noncomputable abbrev euclideanIPS (ι : Type*) [Fintype ι] :
    InnerProductSpace ℂ (EuclideanSpace ℂ ι) := inferInstance

/-- `EuclideanSpace` is finite-dimensional via its standard basis. -/
private noncomputable abbrev euclideanFiniteDimensional (ι : Type*) [Fintype ι] :
    FiniteDimensional ℂ (EuclideanSpace ℂ ι) :=
  Module.Basis.finiteDimensional_of_finite
    ((Pi.basisFun ℂ ι).map (EuclideanSpace.equiv ι ℂ).symm.toLinearEquiv)

/-- Rewrite a `toEuclideanLin` composition as matrix multiplication. -/
private lemma toEuclideanLin_conjTranspose_mul_apply
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) (w : EuclideanSpace ℂ n) :
    Mᴴ.toEuclideanLin (M.toEuclideanLin w) = (Mᴴ * M).toEuclideanLin w := by
  change (Mᴴ.toEuclideanLin.comp M.toEuclideanLin) w = _
  rw [← toLpLin_mul_same]

set_option maxHeartbeats 1600000 in
-- The partial-isometry extension proof drives higher-order typeclass search in 4.29.
/-- **Rectangular Kraus freedom** (Wolf Thm 2.1 item 4, necessary direction):
if two Kraus families of sizes `r₁` and `r₂` define the same CPM, then the
first family is a linear combination of the second via a rectangular isometry
`V : r₁ × r₂` with `V†V = 1`.

Concretely: if `∑α Bα X Bα† = ∑j Aj X Aj†` for all `X` and `r₂ ≤ r₁`, then
there exists `V` with `V†V = 1` and `Bα = ∑j Vαj • Aj` for all `α`.

**Proof**: The map equality forces the "Stinespring vectors"
`f(a,b)_j = (Aj)_{ab}` and `g(a,b)_α = (Bα)_{ab}` to have equal Gram matrices.
The linear map `f(a,b) ↦ g(a,b)` therefore preserves inner products on the span
of `{f(a,b)}`. The hypothesis `r₂ ≤ r₁` ensures that this partial isometry
extends to a full isometry `V : ℂ^{r₂} → ℂ^{r₁}` whose matrix satisfies
`V†V = 1`. -/
theorem kraus_rectangular_freedom
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : Fin r₂ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ j : Fin r₂, A j * X * (A j)ᴴ)
    (hCard : r₂ ≤ r₁) :
    ∃ V : Matrix (Fin r₁) (Fin r₂) ℂ,
      V.conjTranspose * V = 1 ∧
      ∀ α : Fin r₁, B α = ∑ j : Fin r₂, V α j • A j := by
  -- ===== Phase 1: Pad A to size r₁ =====
  let A' : Fin r₁ → Matrix (Fin D) (Fin D) ℂ :=
    fun α => if hlt : α.val < r₂ then A ⟨α.val, hlt⟩ else 0
  -- B and A' define the same CPM
  have hBA' : ∀ X, ∑ α : Fin r₁, B α * X * (B α)ᴴ =
      ∑ α : Fin r₁, A' α * X * (A' α)ᴴ := by
    intro X; rw [h X]
    rw [sum_pad_zeros (fun j => A j * X * (A j)ᴴ) hCard]
    apply Finset.sum_congr rfl; intro α _
    simp only [A']; split_ifs <;> simp
  -- Dual map equality
  have hdual := kraus_dual_eq_of_map_eq B A' hBA'
  -- ===== Phase 2: Gram matrix equality =====
  let MB : Matrix (Fin r₁) (Fin D × Fin D) ℂ := fun α x => B α x.1 x.2
  let MA' : Matrix (Fin r₁) (Fin D × Fin D) ℂ := fun α x => A' α x.1 x.2
  have hGram : MBᴴ * MB = MA'ᴴ * MA' := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, MB, MA']
    -- Use dual map equality at single a c 1
    have h_entry := congr_fun (congr_fun (hdual (Matrix.single a c 1)) b) d
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.single_apply] at h_entry
    -- Collapse the inner sum (over x₂) using sum_eq_single
    have collapse : ∀ (K : Fin r₁ → Matrix (Fin D) (Fin D) ℂ),
        (∑ α, ∑ x₁, (∑ x₂, star (K α x₂ b) *
          (if a = x₂ ∧ c = x₁ then (1 : ℂ) else 0)) * K α x₁ d) =
        ∑ α, star (K α a b) * K α c d := by
      intro K
      apply Finset.sum_congr rfl; intro α _
      have step₁ : ∀ x₁, (∑ x₂, star (K α x₂ b) *
          (if a = x₂ ∧ c = x₁ then (1 : ℂ) else 0)) * K α x₁ d =
          if c = x₁ then star (K α a b) * K α x₁ d else 0 := by
        intro x₁
        have h_inner : (∑ x₂, star (K α x₂ b) *
            (if a = x₂ ∧ c = x₁ then (1 : ℂ) else 0)) =
            if c = x₁ then star (K α a b) else 0 := by
          rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx])
              (fun h => absurd (Finset.mem_univ _) h)]
          split_ifs <;> simp_all
        rw [h_inner]; split_ifs <;> simp
      simp_rw [step₁]; simp [Finset.sum_ite_eq, Finset.mem_univ]
    rw [collapse, collapse] at h_entry
    exact h_entry
  -- ===== Phase 3: Construct the isometry =====
  letI : InnerProductSpace ℂ (KrausCoeffSpace r₁) := euclideanIPS (Fin r₁)
  letI : InnerProductSpace ℂ (KrausEntrySpace D) := euclideanIPS (Fin D × Fin D)
  letI : FiniteDimensional ℂ (KrausCoeffSpace r₁) := euclideanFiniteDimensional (Fin r₁)
  letI : FiniteDimensional ℂ (KrausEntrySpace D) := euclideanFiniteDimensional (Fin D × Fin D)
  let fB : KrausEntrySpace D →ₗ[ℂ] KrausCoeffSpace r₁ := Matrix.toEuclideanLin MB
  let fA' : KrausEntrySpace D →ₗ[ℂ] KrausCoeffSpace r₁ := Matrix.toEuclideanLin MA'
  -- Inner product preservation from Gram equality
  have hinner : ∀ v w : KrausEntrySpace D,
      ⟪fB v, fB w⟫_ℂ = ⟪fA' v, fA' w⟫_ℂ := by
    intro v w
    rw [← LinearMap.adjoint_inner_right fB v (fB w),
        ← LinearMap.adjoint_inner_right fA' v (fA' w)]
    congr 1
    show fB.adjoint (fB w) = fA'.adjoint (fA' w)
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint MB,
        ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint MA']
    rw [toEuclideanLin_conjTranspose_mul_apply MB,
      toEuclideanLin_conjTranspose_mul_apply MA', hGram]
  -- Kernel inclusion
  have hker : LinearMap.ker fA' ≤ LinearMap.ker fB := by
    intro v hv; rw [LinearMap.mem_ker] at hv ⊢
    have h0 := hinner v v
    simp only [hv, inner_zero_left] at h0
    exact inner_self_eq_zero.mp h0
  -- Construct partial isometry L on range(fA')
  let L_lm : LinearMap.range fA' →ₗ[ℂ] KrausCoeffSpace r₁ :=
    ((LinearMap.ker fA').liftQ fB hker).comp
      fA'.quotKerEquivRange.symm.toLinearMap
  -- Key: L sends fA'(v) to fB(v)
  have hL_apply : ∀ v, L_lm ⟨fA' v, LinearMap.mem_range_self fA' v⟩ = fB v := by
    intro v
    show ((LinearMap.ker fA').liftQ fB hker)
      (fA'.quotKerEquivRange.symm ⟨fA' v, LinearMap.mem_range_self fA' v⟩) = fB v
    rw [fA'.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ _
  -- L preserves inner products
  have hL_inner : ∀ x y : LinearMap.range fA',
      ⟪L_lm x, L_lm y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨v, rfl⟩ := hx; obtain ⟨w, rfl⟩ := hy
    rw [hL_apply, hL_apply, hinner, Submodule.coe_inner]
  -- Extend to full isometry
  let L_iso : LinearMap.range fA' →ₗᵢ[ℂ] KrausCoeffSpace r₁ :=
    by
      exact LinearMap.isometryOfInner L_lm hL_inner
  let U := L_iso.extend
  -- U ∘ fA' = fB
  have hU_eq : ∀ v, U (fA' v) = fB v := by
    intro v
    have : U (fA' v) = L_iso ⟨fA' v, LinearMap.mem_range_self fA' v⟩ :=
      LinearIsometry.extend_apply L_iso ⟨fA' v, LinearMap.mem_range_self fA' v⟩
    rw [this]
    simpa [L_iso] using hL_apply v
  -- ===== Phase 4: Extract V =====
  let U_mat : Matrix (Fin r₁) (Fin r₁) ℂ :=
    Matrix.toEuclideanLin.symm U.toLinearMap
  -- Key: toEuclideanLin U_mat = U.toLinearMap
  have h_U_lin : Matrix.toEuclideanLin U_mat = U.toLinearMap :=
    LinearEquiv.apply_symm_apply Matrix.toEuclideanLin U.toLinearMap
  -- U_mat† U_mat = 1 (U is an isometry on a f.d. space)
  have hU_unitary : U_matᴴ * U_mat = 1 := by
    apply Matrix.toEuclideanLin.injective; ext1 v
    have hadj : U.toLinearMap.adjoint (U.toLinearMap v) = v :=
      ext_inner_right ℂ fun y => by
        rw [LinearMap.adjoint_inner_left]
        exact LinearIsometry.inner_map_map U v y
    rw [toLpLin_mul_same, LinearMap.comp_apply,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, h_U_lin, hadj]
    simp only [toLpLin_one, LinearMap.id_apply]
  -- U_mat * MA' = MB (from U ∘ fA' = fB)
  have hU_mat_eq : U_mat * MA' = MB := by
    apply Matrix.toEuclideanLin.injective; ext1 v
    rw [toLpLin_mul_same, LinearMap.comp_apply, h_U_lin]; exact hU_eq v
  -- Define V as first r₂ columns of U_mat
  refine ⟨fun α j => U_mat α (Fin.castLE hCard j), ?_, ?_⟩
  · -- V†V = 1
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    have h_uu := congr_fun (congr_fun hU_unitary (Fin.castLE hCard j)) (Fin.castLE hCard k)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h_uu
    rw [h_uu]; simp [(Fin.castLE_injective hCard).eq_iff]
  · -- B α = ∑ j, V(α,j) • A j
    intro α; ext a b
    have h_entry : (B α) a b =
        ∑ β : Fin r₁, U_mat α β * (A' β) a b := by
      have := congr_fun (congr_fun hU_mat_eq α) (a, b)
      simpa [Matrix.mul_apply, MB, MA'] using this.symm
    rw [h_entry]; simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [sum_pad_zeros (fun j => U_mat α (Fin.castLE hCard j) * (A j) a b) hCard]
    apply Finset.sum_congr rfl; intro β _
    simp only [A']; split_ifs with hlt
    · simp only [Fin.eta, Fin.castLE]
    · simp only [Matrix.zero_apply, mul_zero]

/-- Variant of `kraus_rectangular_freedom` with general index types. -/
theorem kraus_rectangular_freedom'
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : ι₁ → Matrix (Fin D) (Fin D) ℂ)
    (A : ι₂ → Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α, B α * X * (B α)ᴴ =
      ∑ j, A j * X * (A j)ᴴ)
    (hCard : Fintype.card ι₂ ≤ Fintype.card ι₁) :
    ∃ V : Matrix ι₁ ι₂ ℂ,
      V.conjTranspose * V = 1 ∧
      ∀ α, B α = ∑ j, V α j • A j := by
  -- Reindex to Fin using Fintype.equivFin
  let e₁ : ι₁ ≃ Fin (Fintype.card ι₁) := Fintype.equivFin ι₁
  let e₂ : ι₂ ≃ Fin (Fintype.card ι₂) := Fintype.equivFin ι₂
  let B' : Fin (Fintype.card ι₁) → Matrix (Fin D) (Fin D) ℂ := B ∘ e₁.symm
  let A' : Fin (Fintype.card ι₂) → Matrix (Fin D) (Fin D) ℂ := A ∘ e₂.symm
  have h' : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ α : Fin (Fintype.card ι₁), B' α * X * (B' α)ᴴ =
      ∑ j : Fin (Fintype.card ι₂), A' j * X * (A' j)ᴴ := by
    intro X
    show ∑ α, B (e₁.symm α) * X * (B (e₁.symm α))ᴴ =
        ∑ j, A (e₂.symm j) * X * (A (e₂.symm j))ᴴ
    rw [e₁.symm.sum_comp (fun i => B i * X * (B i)ᴴ),
        e₂.symm.sum_comp (fun j => A j * X * (A j)ᴴ)]
    exact h X
  obtain ⟨V', hV'_iso, hV'_decomp⟩ := kraus_rectangular_freedom B' A' h' hCard
  -- Transform V back to the original index types
  refine ⟨fun α j => V' (e₁ α) (e₂ j), ?_, ?_⟩
  · -- V†V = 1
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [show ∑ x : ι₁, star (V' (e₁ x) (e₂ j)) * V' (e₁ x) (e₂ k) =
        ∑ β, star (V' β (e₂ j)) * V' β (e₂ k) from
      e₁.sum_comp (fun β => star (V' β (e₂ j)) * V' β (e₂ k))]
    have h_entry := congr_fun (congr_fun hV'_iso (e₂ j)) (e₂ k)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      e₂.injective.eq_iff] at h_entry
    exact h_entry
  · -- B α = ∑ j, V(α,j) • A j
    intro α
    have := hV'_decomp (e₁ α)
    simp only [B', A', Function.comp, Equiv.symm_apply_apply] at this
    rw [this, ← e₂.sum_comp (fun β => V' (e₁ α) β • A (e₂.symm β))]
    simp [Equiv.symm_apply_apply]
