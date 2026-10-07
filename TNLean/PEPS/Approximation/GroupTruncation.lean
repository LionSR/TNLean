/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WholeGroupContraction

/-!
# Simultaneous truncation of whole open-leg groups

A tensor `Z` on the open-leg groups `P v` of the vertices of a finite graph is truncated by
projecting every group space onto a subspace of dimension at most `k`. The projections act on
disjoint tensor factors, so they commute, and the truncation errors telescope. When every
single-group flattening of `Z` has nuclear norm at most one, each group contributes an error at
most `1 / √k`, and groups with a one-point configuration space contribute nothing.

## Main definitions

* `WholeGroup.factorMatrix`: the tensor product `⊗ᵥ Qᵥ` of operators on the group spaces.
* `WholeGroup.onFactor`: an operator acting on one group space only.
* `WholeGroup.groupFlattening`: the flattening of a tensor across one group and its complement.

## Main statements

* `WholeGroup.norm_sub_factorMatrix_le`: telescoping for commuting factor projections.
* `WholeGroup.exists_group_truncation`: the simultaneous truncation of a tensor whose
  single-group flattenings have nuclear norm at most one.
* `WholeGroup.exists_simultaneous_group_truncation`: Lemma 6.2 of the polynomial-PEPS
  manuscript, for the contraction of a finite tensor graph without edges from a vertex to itself.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`,
  05-frames.tex:125–179.
-/

open scoped BigOperators Matrix InnerProductSpace

noncomputable section

namespace TNLean.PEPS.WholeGroup

open Matrix

/-! ### Projectors -/

section Projectors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Hermitian idempotent matrix does not increase Euclidean norms. -/
theorem norm_toEuclideanLin_le_of_isProj (M : Matrix ι ι ℂ) (hH : Mᴴ = M) (hI : M * M = M)
    (x : EuclideanSpace ℂ ι) : ‖toEuclideanLin M x‖ ≤ ‖x‖ := by
  have hsq : ‖toEuclideanLin M x‖ ^ 2 ≤ ‖x‖ * ‖toEuclideanLin M x‖ := by
    have h1 : ⟪toEuclideanLin M x, toEuclideanLin M x⟫_ℂ = ⟪x, toEuclideanLin M x⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint, hH,
        ← LinearMap.comp_apply, ← toLpLin_mul_same, hI]
    have h2 : ‖toEuclideanLin M x‖ ^ 2 = ‖⟪x, toEuclideanLin M x⟫_ℂ‖ := by
      rw [← h1, inner_self_eq_norm_sq_to_K]
      simp
    rw [h2]
    exact norm_inner_le_norm _ _
  nlinarith [norm_nonneg (toEuclideanLin M x), norm_nonneg x]

omit [DecidableEq ι] in
theorem conjTranspose_orthonormalProjector {β : Type*} [Fintype β]
    (f : ι → EuclideanSpace ℂ β) : (orthonormalProjector f)ᴴ = orthonormalProjector f := by
  ext b b'
  simp [orthonormalProjector, conjTranspose_apply, mul_comm]

theorem orthonormalProjector_mul_self {β : Type*} [Fintype β] [DecidableEq β]
    {f : ι → EuclideanSpace ℂ β} (hf : Orthonormal ℂ f) :
    orthonormalProjector f * orthonormalProjector f = orthonormalProjector f := by
  apply (toEuclideanLin (𝕜 := ℂ) (m := β) (n := β)).injective
  rw [toLpLin_mul_same]
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, toEuclideanLin_orthonormalProjector,
    toEuclideanLin_orthonormalProjector]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hf.1 i]
    simp
  · intro j _ hji
    rw [inner_smul_right, orthonormal_iff_ite.mp hf i j]
    simp [Ne.symm hji]
  · simp

/-- The coordinatewise complex conjugate of a family of Euclidean vectors. -/
def conjFamily {β : Type*} (f : ι → EuclideanSpace ℂ β) : ι → EuclideanSpace ℂ β :=
  fun i ↦ WithLp.toLp 2 fun b ↦ star (f i b)

omit [Fintype ι] [DecidableEq ι] in
theorem orthonormal_conjFamily {β : Type*} [Fintype β] {f : ι → EuclideanSpace ℂ β}
    (hf : Orthonormal ℂ f) : Orthonormal ℂ (conjFamily f) := by
  classical
  rw [orthonormal_iff_ite] at hf ⊢
  intro i j
  have h := hf j i
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h ⊢
  simp only [conjFamily, dotProduct, Pi.star_apply, star_star] at h ⊢
  calc _ = ∑ b, (f i) b * star ((f j) b) := Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
    _ = _ := by rw [h]; by_cases hij : i = j <;> simp [hij, eq_comm]

omit [DecidableEq ι] in
theorem transpose_orthonormalProjector {β : Type*} [Fintype β] (f : ι → EuclideanSpace ℂ β) :
    (orthonormalProjector f)ᵀ = orthonormalProjector (conjFamily f) := by
  ext b b'
  simp [orthonormalProjector, conjFamily, mul_comm]

end Projectors

/-! ### Operators on tensor factors -/

section Factors

variable {V : Type*} [Fintype V] [DecidableEq V] {P : V → Type*} [∀ v, Fintype (P v)]
  [∀ v, DecidableEq (P v)]

/-- The tensor product `⊗ᵥ Qᵥ` of operators on the group spaces, as a matrix on the
configurations of all groups. -/
def factorMatrix (Q : (v : V) → Matrix (P v) (P v) ℂ) :
    Matrix ((v : V) → P v) ((v : V) → P v) ℂ :=
  fun σ τ ↦ ∏ v, Q v (σ v) (τ v)

omit [∀ v, DecidableEq (P v)] in
theorem factorMatrix_mul (Q R : (v : V) → Matrix (P v) (P v) ℂ) :
    factorMatrix Q * factorMatrix R = factorMatrix fun v ↦ Q v * R v := by
  ext σ τ
  simp only [factorMatrix, mul_apply, Fintype.prod_sum, ← Finset.prod_mul_distrib]

omit [DecidableEq V] [∀ v, Fintype (P v)] in
theorem factorMatrix_one : factorMatrix (fun v ↦ (1 : Matrix (P v) (P v) ℂ)) = 1 := by
  ext σ τ
  simp only [factorMatrix, one_apply, Finset.prod_boole, Finset.mem_univ, true_implies]
  by_cases h : σ = τ
  · simp [h]
  · simp only [h, ite_false]
    exact ite_eq_right_iff.mpr fun h' ↦ absurd (funext h') h

omit [DecidableEq V] [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)] in
theorem conjTranspose_factorMatrix (Q : (v : V) → Matrix (P v) (P v) ℂ) :
    (factorMatrix Q)ᴴ = factorMatrix fun v ↦ (Q v)ᴴ := by
  ext σ τ
  simp [factorMatrix, conjTranspose_apply]

omit [∀ v, DecidableEq (P v)] in
/-- A tensor product of orthogonal projections is an orthogonal projection. -/
theorem factorMatrix_isProj {Q : (v : V) → Matrix (P v) (P v) ℂ} (hH : ∀ v, (Q v)ᴴ = Q v)
    (hI : ∀ v, Q v * Q v = Q v) :
    (factorMatrix Q)ᴴ = factorMatrix Q ∧ factorMatrix Q * factorMatrix Q = factorMatrix Q := by
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_factorMatrix]
    simp_rw [hH]
  · rw [factorMatrix_mul]
    simp_rw [hI]

/-- An operator acting on the group space of `w` only. -/
def onFactor (w : V) (Q : Matrix (P w) (P w) ℂ) : Matrix ((v : V) → P v) ((v : V) → P v) ℂ :=
  factorMatrix (Function.update (fun v ↦ (1 : Matrix (P v) (P v) ℂ)) w Q)

/-- The flattening of a tensor across the group of `w` and its complement, with the group of `w`
as the column index. -/
def groupFlattening (Z : ((v : V) → P v) → ℂ) (w : V) :
    Matrix ((v : {v // v ≠ w}) → P v) (P w) ℂ :=
  fun x p ↦ Z ((Equiv.piSplitAt w P).symm (p, x))

omit [Fintype V] [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)] in
@[simp]
theorem piSplitAt_symm_apply_self (w : V) (p : P w) (x : (v : {v // v ≠ w}) → P v) :
    (Equiv.piSplitAt w P).symm (p, x) w = p := by
  simp [Equiv.piSplitAt_symm_apply]

omit [Fintype V] [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)] in
@[simp]
theorem piSplitAt_symm_apply_ne (w : V) (p : P w) (x : (v : {v // v ≠ w}) → P v)
    (v : {v // v ≠ w}) : (Equiv.piSplitAt w P).symm (p, x) v = x v := by
  simp [Equiv.piSplitAt_symm_apply, v.2]

omit [∀ v, Fintype (P v)] in
theorem onFactor_apply (w : V) (Q : Matrix (P w) (P w) ℂ) (σ τ : (v : V) → P v) :
    onFactor w Q σ τ =
      Q (σ w) (τ w) *
        if (fun v : {v // v ≠ w} ↦ σ v) = fun v : {v // v ≠ w} ↦ τ v then 1 else 0 := by
  classical
  rw [onFactor, factorMatrix, Fintype.prod_eq_mul_prod_compl w, Function.update_self]
  congr 1
  rw [Finset.prod_subtype ({w}ᶜ : Finset V) (p := (· ≠ w)) (F := inferInstance) (by simp)]
  have : ∀ v : {v // v ≠ w},
      Function.update (fun v ↦ (1 : Matrix (P v) (P v) ℂ)) w Q v (σ v) (τ v) =
        if σ v = τ v then 1 else 0 := by
    intro v
    rw [Function.update_of_ne v.2, one_apply]
  simp_rw [this]
  rw [Finset.prod_boole]
  simp [funext_iff]

theorem onFactor_mulVec (Z : ((v : V) → P v) → ℂ) (w : V) (Q : Matrix (P w) (P w) ℂ)
    (p₀ : P w) (x : (v : {v // v ≠ w}) → P v) :
    (onFactor w Q *ᵥ Z) ((Equiv.piSplitAt w P).symm (p₀, x)) =
      (groupFlattening Z w * Qᵀ) x p₀ := by
  classical
  rw [mulVec, dotProduct, ← (Equiv.piSplitAt w P).symm.sum_comp, Fintype.sum_prod_type,
    mul_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [onFactor_apply, piSplitAt_symm_apply_self, piSplitAt_symm_apply_ne]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [groupFlattening, transpose_apply, mul_comm]

/-- The error of a one-group operator is the Hilbert--Schmidt error of the group flattening. -/
theorem norm_sq_sub_onFactor (Z : EuclideanSpace ℂ ((v : V) → P v)) (w : V)
    (Q : Matrix (P w) (P w) ℂ) :
    ‖Z - toEuclideanLin (onFactor w Q) Z‖ ^ 2 =
      hsNormSq (groupFlattening Z.ofLp w - groupFlattening Z.ofLp w * Qᵀ) := by
  rw [EuclideanSpace.norm_sq_eq, hsNormSq, ← (Equiv.piSplitAt w P).symm.sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [WithLp.ofLp_sub, Pi.sub_apply, toLpLin_apply, onFactor_mulVec, Matrix.sub_apply]
  rfl

/-- Telescoping: the projections onto subspaces of the separate group spaces commute, so the
error of their product is at most the sum of the separate errors.

Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 6.2 `lem:group-tensor`,
05-frames.tex:170–176. -/
theorem norm_sub_factorMatrix_le (Q : (v : V) → Matrix (P v) (P v) ℂ)
    (hH : ∀ v, (Q v)ᴴ = Q v) (hI : ∀ v, Q v * Q v = Q v)
    (Z : EuclideanSpace ℂ ((v : V) → P v)) (F : Finset V) :
    ‖Z - toEuclideanLin (factorMatrix fun v ↦ if v ∈ F then Q v else 1) Z‖ ≤
      ∑ v ∈ F, ‖Z - toEuclideanLin (onFactor v (Q v)) Z‖ := by
  induction F using Finset.induction_on with
  | empty => simp [factorMatrix_one]
  | insert w F hw ih =>
    have hsplit : (factorMatrix fun v ↦ if v ∈ insert w F then Q v else 1) =
        onFactor w (Q w) * factorMatrix fun v ↦ if v ∈ F then Q v else 1 := by
      rw [onFactor, factorMatrix_mul]
      congr 1
      funext v
      by_cases hv : v = w
      · subst hv
        simp [hw]
      · simp [hv]
    have hproj := factorMatrix_isProj (Q := Function.update (fun v ↦ (1 : Matrix (P v) (P v) ℂ))
      w (Q w)) (fun v ↦ by
        by_cases hv : v = w
        · subst hv; simp [hH]
        · simp [Function.update_of_ne hv]) (fun v ↦ by
        by_cases hv : v = w
        · subst hv; simp [hI]
        · simp [Function.update_of_ne hv])
    rw [hsplit, toLpLin_mul_same, LinearMap.comp_apply, Finset.sum_insert hw]
    set Tw := toEuclideanLin (onFactor w (Q w))
    set TF := toEuclideanLin (factorMatrix fun v ↦ if v ∈ F then Q v else 1)
    have hdecomp : Z - Tw (TF Z) = (Z - Tw Z) + Tw (Z - TF Z) := by
      rw [map_sub]
      abel
    rw [hdecomp]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    exact (norm_toEuclideanLin_le_of_isProj _ hproj.1 hproj.2 _).trans ih

end Factors

/-! ### Simultaneous truncation -/

section Truncation

variable {V : Type*} [Fintype V] [DecidableEq V] {P : V → Type*} [∀ v, Fintype (P v)]
  [∀ v, DecidableEq (P v)]

omit [DecidableEq V] [∀ v, DecidableEq (P v)] in
/-- The product vector `⊗ᵥ e_{v, i v}` of one member of each family. -/
def productVector {r : V → ℕ} (e : (v : V) → Fin (r v) → EuclideanSpace ℂ (P v))
    (i : (v : V) → Fin (r v)) : EuclideanSpace ℂ ((v : V) → P v) :=
  WithLp.toLp 2 fun σ ↦ ∏ v, e v (i v) (σ v)

omit [∀ v, DecidableEq (P v)] in
theorem norm_productVector {r : V → ℕ} {e : (v : V) → Fin (r v) → EuclideanSpace ℂ (P v)}
    (he : ∀ v, Orthonormal ℂ (e v)) (i : (v : V) → Fin (r v)) : ‖productVector e i‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp only [productVector, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun v p ↦ ‖e v (i v) p‖ ^ 2)]
  refine Finset.prod_eq_one fun v _ ↦ ?_
  rw [← EuclideanSpace.norm_sq_eq, (he v).1 (i v), one_pow]

/-- In product orthonormal bases, the tensor-product projection is a sum of product vectors. -/
theorem factorMatrix_orthonormalProjector_apply {r : V → ℕ}
    (e : (v : V) → Fin (r v) → EuclideanSpace ℂ (P v)) (Z : EuclideanSpace ℂ ((v : V) → P v)) :
    toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v)) Z =
      ∑ i, ⟪productVector e i, Z⟫_ℂ • productVector e i := by
  ext σ
  simp only [toLpLin_apply, mulVec, dotProduct, factorMatrix, orthonormalProjector,
    Fintype.prod_sum, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, productVector, EuclideanSpace.inner_eq_star_dotProduct, PiLp.toLp_apply,
    Pi.star_apply, Finset.sum_mul, Finset.prod_mul_distrib, star_prod]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun τ _ ↦ ?_
  ring

/-- **Simultaneous group truncation.** If a tensor has norm at most one and each of its
single-group flattenings has nuclear norm at most one, then for every `k ≥ 1` there are
orthonormal families of at most `k` vectors in the group spaces whose tensor-product projection
`Z_k` satisfies `‖Z - Z_k‖ ≤ g / √k`, where the `g` groups in `G` include every group with more
than one configuration. In those bases `Z_k` has at most `k ^ g` product terms, with coefficients
of modulus at most one.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, equation
`eq:group-truncation`, 05-frames.tex:134–141; proof 05-frames.tex:170–179. -/
theorem exists_group_truncation (Z : EuclideanSpace ℂ ((v : V) → P v)) (hZ : ‖Z‖ ≤ 1)
    (hnuc : ∀ w, nuclearNorm (groupFlattening Z.ofLp w) ≤ 1) (G : Finset V)
    (hG : ∀ v ∉ G, Fintype.card (P v) ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (r : V → ℕ) (e : (v : V) → Fin (r v) → EuclideanSpace ℂ (P v)),
      (∀ v, r v ≤ k) ∧ (∀ v, Orthonormal ℂ (e v)) ∧
      ‖Z - toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v)) Z‖ ≤
        G.card / √k ∧
      Fintype.card ((v : V) → Fin (r v)) ≤ k ^ G.card ∧
      ∃ c : ((v : V) → Fin (r v)) → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧
        toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v)) Z =
          ∑ i, c i • productVector e i := by
  classical
  have htr := fun w ↦ exists_orthonormal_truncation (groupFlattening Z.ofLp w) k
  choose r hrk f hf herr hzero using htr
  set e : (v : V) → Fin (r v) → EuclideanSpace ℂ (P v) := fun v ↦ conjFamily (f v) with he_def
  have he : ∀ v, Orthonormal ℂ (e v) := fun v ↦ orthonormal_conjFamily (hf v)
  have hr1 : ∀ v ∉ G, r v ≤ 1 := by
    intro v hv
    have := (he v).linearIndependent.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace] at this
    exact this.trans (hG v hv)
  refine ⟨r, e, hrk, he, ?_, ?_, ?_⟩
  · set Q : (v : V) → Matrix (P v) (P v) ℂ := fun v ↦ orthonormalProjector (e v)
    have hH : ∀ v, (Q v)ᴴ = Q v := fun v ↦ conjTranspose_orthonormalProjector _
    have hI : ∀ v, Q v * Q v = Q v := fun v ↦ orthonormalProjector_mul_self (he v)
    have htel := norm_sub_factorMatrix_le Q hH hI Z Finset.univ
    simp only [Finset.mem_univ, ite_true] at htel
    refine htel.trans ?_
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hbound : ∀ v, ‖Z - toEuclideanLin (onFactor v (Q v)) Z‖ ≤
        if v ∈ G then 1 / √k else 0 := by
      intro v
      have hQt : (Q v)ᵀ = orthonormalProjector (f v) := by
        rw [transpose_orthonormalProjector]
        congr 1
        funext i
        ext b
        simp [e, conjFamily]
      have hsq := norm_sq_sub_onFactor Z v (Q v)
      rw [hQt] at hsq
      split_ifs with hv
      · have h1 := herr v
        have hn := hnuc v
        have hn0 := nuclearNorm_nonneg (groupFlattening Z.ofLp v)
        have hle : ‖Z - toEuclideanLin (onFactor v (Q v)) Z‖ ^ 2 ≤ (1 / √k) ^ 2 := by
          rw [hsq, div_pow, one_pow, Real.sq_sqrt hkpos.le, le_div_iff₀ hkpos]
          have hnsq : nuclearNorm (groupFlattening Z.ofLp v) ^ 2 ≤ 1 := by nlinarith
          have hhs := hsNormSq_nonneg
            (groupFlattening Z.ofLp v - groupFlattening Z.ofLp v * orthonormalProjector (f v))
          have hk1 : (k : ℝ) ≤ k + 1 := by linarith
          nlinarith
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle
      · have h0 := hzero v ((hG v hv).trans hk)
        rw [h0] at hsq
        exact (pow_eq_zero_iff two_ne_zero).mp hsq |>.le
    calc ∑ v, ‖Z - toEuclideanLin (onFactor v (Q v)) Z‖
        ≤ ∑ v, (if v ∈ G then 1 / √k else 0) := Finset.sum_le_sum fun v _ ↦ hbound v
      _ = G.card / √k := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
            mul_one_div]
  · rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    calc ∏ v, r v ≤ ∏ v, (if v ∈ G then k else 1) :=
          Finset.prod_le_prod fun v _ ↦ by
            split_ifs with hv
            · exact hrk v
            · exact hr1 v hv
      _ = k ^ G.card := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  · refine ⟨fun i ↦ ⟪productVector e i, Z⟫_ℂ, fun i ↦ ?_,
      factorMatrix_orthonormalProjector_apply e Z⟩
    calc ‖⟪productVector e i, Z⟫_ℂ‖ ≤ ‖productVector e i‖ * ‖Z‖ := norm_inner_le_norm _ _
      _ ≤ 1 := by
        have h1 := norm_productVector he i
        rw [h1, one_mul]
        exact hZ

end Truncation

/-! ### The whole-group tensor lemma -/

section Contraction

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {tail head : E → V} {D : E → Type*} [∀ e, Fintype (D e)]
  {P : V → Type*} [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]
  (A : VertexTensors tail head D P)

/-- The complement of the complement of a singleton has exactly one element. -/
@[instance_reducible]
def uniqueComplSingletonCompl (w : V) : Unique {v // v ∉ ({w} : Finset V)ᶜ} where
  default := ⟨w, by simp⟩
  uniq v := Subtype.ext (by simpa using v.2)

omit [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)] in
variable (P) in
/-- The group space of `w`, seen as configurations on the complement of the complement of `w`. -/
def groupEquiv (w : V) : P w ≃ ((v : {v // v ∉ ({w} : Finset V)ᶜ}) → P v) :=
  (@Equiv.piUnique _ (uniqueComplSingletonCompl w) fun v ↦ P v).symm

omit [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)] in
variable (P) in
/-- The configurations away from `w`, seen on the complement of the singleton `{w}`. -/
def awayEquiv (w : V) :
    ((v : {v // v ≠ w}) → P v) ≃ ((v : {v // v ∈ ({w} : Finset V)ᶜ}) → P v) :=
  piSubtypeCongr P _ _ fun v ↦ by simp

omit [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)] in
theorem piSplitAt_symm_eq (w : V) (p : P w) (x : (v : {v // v ≠ w}) → P v) :
    (Equiv.piSplitAt w P).symm (p, x) =
      (Equiv.piEquivPiSubtypeProd (· ∈ ({w} : Finset V)ᶜ) P).symm
        (awayEquiv P w x, groupEquiv P w p) := by
  funext u
  by_cases hu : u = w
  · subst hu
    simp only [Equiv.piSplitAt_symm_apply, dite_true, Equiv.piEquivPiSubtypeProd_symm_apply,
      Finset.mem_compl, Finset.mem_singleton, not_true_eq_false, dite_false]
    rfl
  · simp [Equiv.piSplitAt_symm_apply, hu, awayEquiv, piSubtypeCongr]

omit [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)] in
/-- The single-group flattening of the contraction factors through the contractions of the
group's vertex and of its complement. -/
theorem groupFlattening_contraction (w : V) :
    groupFlattening (contraction A) w =
      (bipartitionLeft A ({w} : Finset V)ᶜ).submatrix (awayEquiv P w) (Equiv.refl _) *
        ((bipartitionRight A ({w} : Finset V)ᶜ).submatrix (groupEquiv P w) (Equiv.refl _))ᵀ := by
  ext x p
  rw [groupFlattening, piSplitAt_symm_eq]
  change flattening (contraction A) _ (awayEquiv P w x) (groupEquiv P w p) = _
  rw [flattening_contraction]
  simp [mul_apply]

/-- Every single-group flattening of the contraction has nuclear norm at most one. -/
theorem nuclearNorm_groupFlattening_contraction_le_one (hloop : ∀ e, tail e ≠ head e)
    (hA : ∀ v, vertexNormSq A v ≤ 1) (w : V) :
    nuclearNorm (groupFlattening (contraction A) w) ≤ 1 := by
  rw [groupFlattening_contraction]
  refine (nuclearNorm_mul_transpose_le _ _).trans ?_
  rw [hsNormSq_submatrix, hsNormSq_submatrix, hsNormSq_bipartitionLeft, hsNormSq_bipartitionRight]
  have h₁ := partialNormSq_le_one A hloop hA ({w} : Finset V)ᶜ
  have h₂ := partialNormSq_le_one A hloop hA ({w} : Finset V)ᶜᶜ
  calc √(partialNormSq A ({w} : Finset V)ᶜ) * √(partialNormSq A ({w} : Finset V)ᶜᶜ)
      ≤ 1 * 1 := by gcongr <;> exact Real.sqrt_le_one.mpr ‹_›
    _ = 1 := one_mul 1

/-- **Whole-group tensor bound (Lemma 6.2).** Let a finite graph without edges from a vertex to
itself carry at each vertex a tensor of norm at most one, and contract its edges by the coordinate
pairing. Let the finite set `G` contain every vertex whose open-leg group has more than one
configuration (in particular every vertex with a nonempty group of open legs of positive
dimension may be listed; vertices without open legs need not be). Then for every `k ≥ 1` there are
orthonormal families of at most `k` vectors in the group spaces whose tensor-product projection
sends `Z` to `Z_k` with `‖Z - Z_k‖ ≤ |G| / √k`; in those bases `Z_k` has at most `k ^ |G|`
product terms, with coefficients of modulus at most one.

The norm and nuclear-norm statements of the lemma are `contraction_norm_le_one` and
`nuclearNorm_flattening_le_one`.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`,
05-frames.tex:125–141; proof 05-frames.tex:143–179. -/
theorem exists_simultaneous_group_truncation (hloop : ∀ e, tail e ≠ head e)
    (hA : ∀ v, vertexNormSq A v ≤ 1) (G : Finset V) (hG : ∀ v ∉ G, Fintype.card (P v) ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ (r : V → ℕ) (e : (v : V) → Fin (r v) → EuclideanSpace ℂ (P v)),
      (∀ v, r v ≤ k) ∧ (∀ v, Orthonormal ℂ (e v)) ∧
      ‖WithLp.toLp 2 (contraction A) -
          toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v))
            (WithLp.toLp 2 (contraction A))‖ ≤ G.card / √k ∧
      Fintype.card ((v : V) → Fin (r v)) ≤ k ^ G.card ∧
      ∃ c : ((v : V) → Fin (r v)) → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧
        toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v))
            (WithLp.toLp 2 (contraction A)) = ∑ i, c i • productVector e i :=
  exists_group_truncation _ (contraction_norm_le_one A hloop hA)
    (nuclearNorm_groupFlattening_contraction_le_one A hloop hA) G hG k hk

end Contraction

/-! ### Explicit open legs -/

section OpenLegs

variable {V : Type*} [DecidableEq V] {O : Type*} [Fintype O] [DecidableEq O] (owner : O → V) (d : O → Type*)
  [∀ o, Fintype (d o)]

/-- The group of open legs of `v`: the open legs whose original vertex is `v`. Its configurations
are the configurations of the whole group. -/
abbrev OpenLegGroup (v : V) := (o : {o // owner o = v}) → d o

/-- A vertex outside the image of the leg assignment has an empty group of open legs, whose
configuration space has one point. -/
theorem card_openLegGroup_le_one {v : V} (hv : v ∉ Finset.univ.image owner) :
    Fintype.card (OpenLegGroup owner d v) ≤ 1 := by
  have : IsEmpty {o // owner o = v} :=
    ⟨fun o ↦ hv (Finset.mem_image.mpr ⟨o, Finset.mem_univ _, o.2⟩)⟩
  rw [Fintype.card_pi, Finset.univ_eq_empty, Finset.prod_empty]

end OpenLegs

/-- **Whole-group tensor bound (Lemma 6.2), with explicit open legs.** Each open leg `o` has an
original vertex `owner o` and a finite configuration type `d o`; the open legs of each vertex form
one group. With `g` the number of nonempty open-leg groups, the truncation error is at most
`g / √k`, and `Z_k` has at most `k ^ g` product terms with coefficients of modulus at most one.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`,
05-frames.tex:125–141; proof 05-frames.tex:143–179. -/
theorem exists_simultaneous_openLeg_truncation {V E O : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] {tail head : E → V} {D : E → Type*} [∀ e, Fintype (D e)]
    [Fintype O] [DecidableEq O] {owner : O → V} {d : O → Type*} [∀ o, Fintype (d o)] [∀ o, DecidableEq (d o)]
    (A : VertexTensors tail head D (OpenLegGroup owner d)) (hloop : ∀ e, tail e ≠ head e)
    (hA : ∀ v, vertexNormSq A v ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (r : V → ℕ) (e : (v : V) → Fin (r v) → EuclideanSpace ℂ (OpenLegGroup owner d v)),
      (∀ v, r v ≤ k) ∧ (∀ v, Orthonormal ℂ (e v)) ∧
      ‖WithLp.toLp 2 (contraction A) -
          toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v))
            (WithLp.toLp 2 (contraction A))‖ ≤ (Finset.univ.image owner).card / √k ∧
      Fintype.card ((v : V) → Fin (r v)) ≤ k ^ (Finset.univ.image owner).card ∧
      ∃ c : ((v : V) → Fin (r v)) → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧
        toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v))
            (WithLp.toLp 2 (contraction A)) = ∑ i, c i • productVector e i :=
  exists_simultaneous_group_truncation A hloop hA _
    (fun _ hv ↦ card_openLegGroup_le_one (owner := owner) (d := d) hv) k hk

end TNLean.PEPS.WholeGroup
