/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ConjugationEvenRankEquivalence
import TNLean.MPS.MPU.FundamentalTheoremGatesSupplied

/-!
# The case of a conjugation-invariant standard form

The two cases of Proposition `corconj` of arXiv:1703.09188 (lines 1098--1120) are
read on standard-form gates `u, v` through the unitaries `x, y` of Proposition
`prop1conj`, with `x, y` symmetric (Case I) or skew-symmetric (Case II). This file
shows that

* the two cases exclude each other;
* the standard form of a conjugation-invariant MPU is in one of them;
* the case depends only on the MPU, not on the choice of standard form;
* along a continuous path of gates, each in some case, the case is constant.

The last point is the continuity argument of the "only if" direction of Theorem
`prop:conjsym-strict-equiv` (lines 1497--1505). The source lifts `x(p), y(p)` to
continuous families. Here the matrix `conj(u) u† = x ⊗ y` itself is continuous, and
its partial transpose on the first factor is `± (x ⊗ y)` according to the case.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d ℓ r : ℕ}

/-- Transposition of the first tensor factor of a matrix on `a × b`. -/
def partialTransposeLeft {a b : Type*} (K : Matrix (a × b) (a × b) ℂ) :
    Matrix (a × b) (a × b) ℂ :=
  fun i j ↦ K (j.1, i.2) (i.1, j.2)

theorem partialTransposeLeft_kronecker {a b : Type*} (x : Matrix a a ℂ) (y : Matrix b b ℂ) :
    partialTransposeLeft (x ⊗ₖ y) = xᵀ ⊗ₖ y := by
  ext i j
  simp [partialTransposeLeft, Matrix.kroneckerMap_apply]

theorem continuous_partialTransposeLeft {a b : Type*} :
    Continuous (partialTransposeLeft : Matrix (a × b) (a × b) ℂ → _) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply (i.1, j.2)).comp (continuous_apply (j.1, i.2))

/-- The matrix `conj(u) u†` of a gate. -/
noncomputable def gateConjugationMatrix (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) :
    Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ :=
  u.map (starRingEnd ℂ) * uᴴ

theorem gateConjugationMatrix_eq {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    (hu : u.IsCoisometry) {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y : Matrix (Fin r) (Fin r) ℂ}
    (h : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) : gateConjugationMatrix u = x ⊗ₖ y := by
  rw [gateConjugationMatrix, h, Matrix.mul_assoc, hu, Matrix.mul_one]

theorem kronecker_ne_zero_of_mem_unitaryGroup [NeZero ℓ] [NeZero r]
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ}
    {y : Matrix (Fin r) (Fin r) ℂ} (hx : x ∈ Matrix.unitaryGroup (Fin ℓ) ℂ)
    (hy : y ∈ Matrix.unitaryGroup (Fin r) ℂ) : x ⊗ₖ y ≠ 0 := by
  intro h
  have hxy := Matrix.mem_unitaryGroup_iff.mp (Matrix.kronecker_mem_unitary hx hy)
  rw [h, zero_mul] at hxy
  have := congrFun (congrFun hxy (0, 0)) (0, 0)
  simp at this

/-- In Case I the partial transpose of `conj(u) u†` is itself. -/
theorem IsConjugationCaseI.partialTransposeLeft {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (hu : u.IsCoisometry)
    (h : IsConjugationCaseI u v) :
    partialTransposeLeft (gateConjugationMatrix u) = gateConjugationMatrix u := by
  obtain ⟨x, y, -, -, hxT, -, hcu, -⟩ := h
  rw [gateConjugationMatrix_eq hu hcu, partialTransposeLeft_kronecker, hxT]

/-- In Case II the partial transpose of `conj(u) u†` is its negative. -/
theorem IsConjugationCaseII.partialTransposeLeft {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (hu : u.IsCoisometry)
    (h : IsConjugationCaseII u v) :
    partialTransposeLeft (gateConjugationMatrix u) = -gateConjugationMatrix u := by
  obtain ⟨x, y, -, -, hxT, -, hcu, -⟩ := h
  rw [gateConjugationMatrix_eq hu hcu, partialTransposeLeft_kronecker, hxT]
  ext i j
  simp [Matrix.kroneckerMap_apply]

/-- In either case `conj(u) u†` is nonzero. -/
theorem gateConjugationMatrix_ne_zero [NeZero ℓ] [NeZero r]
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hu : u.IsCoisometry) (h : IsConjugationCaseI u v ∨ IsConjugationCaseII u v) :
    gateConjugationMatrix u ≠ 0 := by
  rcases h with ⟨x, y, hx, hy, -, -, hcu, -⟩ | ⟨x, y, hx, hy, -, -, hcu, -⟩ <;>
    rw [gateConjugationMatrix_eq hu hcu] <;> exact kronecker_ne_zero_of_mem_unitaryGroup hx hy

/-- **The two cases of `corconj` exclude each other.** Source: arXiv:1703.09188,
Proposition `corconj`, lines 1098--1120: `x ⊗ y = conj(u) u†` fixes `x` up to a
phase, and a nonzero matrix is not both symmetric and skew-symmetric. -/
theorem not_isConjugationCaseI_and_isConjugationCaseII [NeZero ℓ] [NeZero r]
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hu : u.IsCoisometry) : ¬(IsConjugationCaseI u v ∧ IsConjugationCaseII u v) := by
  rintro ⟨h₁, h₂⟩
  have hK := gateConjugationMatrix_ne_zero hu (Or.inl h₁)
  have e₁ := h₁.partialTransposeLeft hu
  have e₂ := h₂.partialTransposeLeft hu
  rw [e₁] at e₂
  exact hK (by
    have : (2 : ℂ) • gateConjugationMatrix u = 0 := by
      rw [two_smul]; nth_rewrite 2 [e₂]; exact add_neg_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero)

/-- **The case is constant along a continuous path of gates.** If `u(p)` is a
continuous family of coisometric gates and every `(u(p), v(p))` is in Case I or in
Case II, then all of them are in Case I or all of them are in Case II. Source:
arXiv:1703.09188, proof of Theorem `prop:conjsym-strict-equiv`, "only if",
lines 1497--1505. -/
theorem isConjugationCase_const_of_path [NeZero ℓ] [NeZero r]
    {u : unitInterval → Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : unitInterval → Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hcont : Continuous u) (hu : ∀ p, (u p).IsCoisometry)
    (hcase : ∀ p, IsConjugationCaseI (u p) (v p) ∨ IsConjugationCaseII (u p) (v p)) :
    (∀ p, IsConjugationCaseI (u p) (v p)) ∨ (∀ p, IsConjugationCaseII (u p) (v p)) := by
  have hK : Continuous fun p ↦ gateConjugationMatrix (u p) :=
    (hcont.matrix_map continuous_star).matrix_mul hcont.matrix_conjTranspose
  let A : Set unitInterval :=
    {p | partialTransposeLeft (gateConjugationMatrix (u p)) = gateConjugationMatrix (u p)}
  let B : Set unitInterval :=
    {p | partialTransposeLeft (gateConjugationMatrix (u p)) = -gateConjugationMatrix (u p)}
  have hA : IsClosed A := isClosed_eq (continuous_partialTransposeLeft.comp hK) hK
  have hB : IsClosed B := isClosed_eq (continuous_partialTransposeLeft.comp hK) hK.neg
  have hzero : ∀ p, p ∈ A → p ∈ B → False := fun p hpA hpB ↦ by
    have e : gateConjugationMatrix (u p) = -gateConjugationMatrix (u p) :=
      (show _ = _ from hpA).symm.trans hpB
    exact gateConjugationMatrix_ne_zero (hu p) (hcase p) (by
      have : (2 : ℂ) • gateConjugationMatrix (u p) = 0 := by
        rw [two_smul]; nth_rewrite 2 [e]; exact add_neg_cancel _
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero)
  have hIA : ∀ p, IsConjugationCaseI (u p) (v p) → p ∈ A := fun p h ↦
    h.partialTransposeLeft (hu p)
  have hIIB : ∀ p, IsConjugationCaseII (u p) (v p) → p ∈ B := fun p h ↦
    h.partialTransposeLeft (hu p)
  have hAc : Aᶜ = B := by
    ext p
    refine ⟨fun hp ↦ hIIB p ((hcase p).resolve_left fun h ↦ hp (hIA p h)), fun hp hpA ↦
      hzero p hpA hp⟩
  have hclopen : IsClopen A := ⟨hA, isClosed_compl_iff.mp (hAc ▸ hB)⟩
  rcases isClopen_iff.mp hclopen with h | h
  · right
    intro p
    exact (hcase p).resolve_left fun h₁ ↦ by
      have := hIA p h₁
      rw [h] at this
      exact this
  · left
    intro p
    exact (hcase p).resolve_right fun h₂ ↦ hzero p (h ▸ Set.mem_univ p) (hIIB p h₂)

/-- **The standard form of a conjugation-invariant MPU is in one of the two cases.**
Source: arXiv:1703.09188, Proposition `prop1conj`, "only if" (lines 1014--1027,
proof at lines 1031--1093). -/
theorem TwoSiteStandardFormData.isConjugationCase_of_conjugation {D : ℕ}
    {W : MPOTensor (d * d) D} {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (S : TwoSiteStandardFormData W u v)
    (hc : ∀ N : ℕ, 0 < N → mpo W N = (mpo W N).map (starRingEnd ℂ)) :
    IsConjugationCaseI u v ∨ IsConjugationCaseII u v := by
  have : Nonempty (Fin ℓ) := ⟨⟨0, S.left_pos⟩⟩
  have : Nonempty (Fin r) := ⟨⟨0, S.right_pos⟩⟩
  obtain ⟨x, y, hu, hv⟩ := S.exists_gate_gauges_of_mpo_eq S.mapStar fun N hN ↦ by
    rw [mpo_map_star]
    exact hc N (by omega)
  rcases Matrix.transpose_eq_self_or_transpose_eq_neg_of_gate_conjugation x.2 y.2
      S.u_unitary.2 hu with ⟨hxT, hyT⟩ | ⟨hxT, hyT⟩
  · exact Or.inl ⟨x, y, x.2, y.2, hxT, hyT, hu, hv⟩
  · exact Or.inr ⟨x, y, x.2, y.2, hxT, hyT, hu, hv⟩

private theorem gauge_conjugation_relations {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    {a x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {b y : Matrix (Fin r) (Fin r) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin ℓ) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin r) ℂ)
    (hu : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) (hv : v.map (starRingEnd ℂ) = v * (yᴴ ⊗ₖ xᴴ)) :
    ((a ⊗ₖ b) * u).map (starRingEnd ℂ) =
        ((a.map (starRingEnd ℂ) * x * aᴴ) ⊗ₖ (b.map (starRingEnd ℂ) * y * bᴴ)) * ((a ⊗ₖ b) * u) ∧
      (v * (bᴴ ⊗ₖ aᴴ)).map (starRingEnd ℂ) = (v * (bᴴ ⊗ₖ aᴴ)) *
        ((b.map (starRingEnd ℂ) * y * bᴴ)ᴴ ⊗ₖ (a.map (starRingEnd ℂ) * x * aᴴ)ᴴ) := by
  have haa : aᴴ * a = 1 := Matrix.mem_unitaryGroup_iff'.mp ha
  have hbb : bᴴ * b = 1 := Matrix.mem_unitaryGroup_iff'.mp hb
  have hstar : ∀ {n : ℕ} (c : Matrix (Fin n) (Fin n) ℂ), (cᴴ).map (starRingEnd ℂ) = cᵀ :=
    fun c ↦ by ext i j; simp
  have hstar' : ∀ {n : ℕ} (c : Matrix (Fin n) (Fin n) ℂ), (c.map (starRingEnd ℂ))ᴴ = cᵀ :=
    fun c ↦ by ext i j; simp
  refine ⟨?_, ?_⟩
  · rw [Matrix.map_mul, map_star_kronecker, hu, Matrix.mul_kronecker_mul,
      Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (aᴴ ⊗ₖ bᴴ), ← Matrix.mul_kronecker_mul, haa, hbb,
      Matrix.one_kronecker_one, Matrix.one_mul]
  · rw [Matrix.map_mul, hv, map_star_kronecker, hstar, hstar, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hstar',
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hstar', Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_assoc bᴴ,
      ← Matrix.mul_assoc aᴴ, hbb, haa, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_kronecker_mul]

private theorem gauge_transpose {n : ℕ} {a x : Matrix (Fin n) (Fin n) ℂ} :
    (a.map (starRingEnd ℂ) * x * aᴴ)ᵀ = a.map (starRingEnd ℂ) * xᵀ * aᴴ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  congr 1

private theorem gauge_mem_unitaryGroup {n : ℕ} {a x : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin n) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    a.map (starRingEnd ℂ) * x * aᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have h1 : a.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have := congrArg (fun M ↦ M.map (starRingEnd ℂ)) (Matrix.mem_unitaryGroup_iff.mp ha)
    have e : (a.map (starRingEnd ℂ))ᴴ = (aᴴ).map (starRingEnd ℂ) := by ext i j; simp
    rw [Matrix.star_eq_conjTranspose, e]
    simpa [Matrix.map_mul, Matrix.star_eq_conjTranspose] using this
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ h1 hx) (Unitary.star_mem ha)

/-- **The case is invariant under gauges of the gates.** Source:
arXiv:1703.09188, Proposition `corconj`, lines 1098--1120, with the gauge freedom
of Theorem `FundamentalMPU` (lines 640--652). -/
theorem IsConjugationCaseI.gauge {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (h : IsConjugationCaseI u v)
    (a : Matrix.unitaryGroup (Fin ℓ) ℂ) (b : Matrix.unitaryGroup (Fin r) ℂ) :
    IsConjugationCaseI (((a : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (b : Matrix (Fin r) (Fin r) ℂ)) * u)
      (v * (star (b : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (a : Matrix (Fin ℓ) (Fin ℓ) ℂ))) := by
  obtain ⟨x, y, hx, hy, hxT, hyT, hu, hv⟩ := h
  obtain ⟨hu', hv'⟩ := gauge_conjugation_relations a.2 b.2 hu hv
  exact ⟨_, _, gauge_mem_unitaryGroup a.2 hx, gauge_mem_unitaryGroup b.2 hy,
    by rw [gauge_transpose, hxT], by rw [gauge_transpose, hyT], hu', hv'⟩

theorem IsConjugationCaseII.gauge {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (h : IsConjugationCaseII u v)
    (a : Matrix.unitaryGroup (Fin ℓ) ℂ) (b : Matrix.unitaryGroup (Fin r) ℂ) :
    IsConjugationCaseII (((a : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (b : Matrix (Fin r) (Fin r) ℂ)) * u)
      (v * (star (b : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (a : Matrix (Fin ℓ) (Fin ℓ) ℂ))) := by
  obtain ⟨x, y, hx, hy, hxT, hyT, hu, hv⟩ := h
  obtain ⟨hu', hv'⟩ := gauge_conjugation_relations a.2 b.2 hu hv
  exact ⟨_, _, gauge_mem_unitaryGroup a.2 hx, gauge_mem_unitaryGroup b.2 hy,
    by rw [gauge_transpose, hxT, Matrix.mul_neg, Matrix.neg_mul],
    by rw [gauge_transpose, hyT, Matrix.mul_neg, Matrix.neg_mul], hu', hv'⟩

/-- **The case depends only on the MPU.** Two standard forms generating the same
MPU are in the same case. Source: arXiv:1703.09188, Proposition `corconj`,
lines 1098--1120, with Theorem `FundamentalMPU` (lines 640--652). -/
theorem TwoSiteStandardFormData.isConjugationCase_iff {D D' : ℕ}
    {W : MPOTensor (d * d) D} {W' : MPOTensor (d * d) D'}
    {u u' : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v v' : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (S' : TwoSiteStandardFormData W' u' v')
    (hEq : ∀ N : ℕ, 1 < N → mpo W N = mpo W' N) :
    (IsConjugationCaseI u v ↔ IsConjugationCaseI u' v') ∧
      (IsConjugationCaseII u v ↔ IsConjugationCaseII u' v') := by
  obtain ⟨a, b, hu, hv⟩ := S.exists_gate_gauges_of_mpo_eq S' hEq
  obtain ⟨a', b', hu', hv'⟩ := S'.exists_gate_gauges_of_mpo_eq S fun N hN ↦ (hEq N hN).symm
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · rw [hu, hv]; exact h.gauge a b
  · rw [hu', hv']; exact h.gauge a' b'
  · rw [hu, hv]; exact h.gauge a b
  · rw [hu', hv']; exact h.gauge a' b'

end MPOTensor
