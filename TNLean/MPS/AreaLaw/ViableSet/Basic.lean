/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SequentialTruncation
import TNLean.MPS.AreaLaw.OpenMPSCutRank
import QICLean.Channel.SchmidtTrimming

/-!
# Viable sets on a chain

Landau, Vazirani and Vidick build an approximation of the ground state `Γ` of a gapped chain of
`L` sites, local dimension `q`, cut by cut from left to right. At the cut after `i` sites they
keep a set `S` of vectors on the first `i` sites. The set is `(i, δ)`-viable for `Γ` when some
unit vector `φ` with `|⟨φ, Γ⟩| ≥ 1 - δ` has its reduced density on the first `i` sites supported
on `Span(S)`; it is `(i, s, b, δ)`-viable when moreover `|S| ≤ s` and every member of `S` is a
matrix product state of bond dimension at most `b`.

The reduced density of `φ` on the first `i` sites is `M Mᴴ`, where `M` is the cut matrix of `φ`
after `i` sites, and its range is the column space of `M`. So `φ` is supported on `Span(S)`
exactly when every column of `M` lies in `Span(S)`: this is the subspace
`leftSupportSubmodule S`, the vectors of `Span(S) ⊗ H_R`. We prove that this reading agrees with
`P M Mᴴ = M Mᴴ`, with `P M = M` and with `(P ⊗ 1) φ = φ` for the orthogonal projection `P` onto
`Span(S)`.

The extension step of the algorithm appends one site: `S ⊗ {|1⟩, …, |q⟩}` is `(i, q s, b, δ)`-
viable when `S` is `(i - 1, s, b, δ)`-viable, with the same witness (Claim `c:ext`).

**Local fix (bond dimension zero):** a matrix product state of bond dimension at most `b` is read
as one of bond dimension at most `max 1 b` (`IsLeftOpenMPS`). Bond dimension `0` is degenerate:
under `IsOpenMPS` every vector on one site has it while a nonzero product vector on two sites does
not, so the source's remark that the extension does not raise the bond dimension (algo53.tex,
line 399) fails at `b = 0` and holds for `b ≥ 1`. The source allows `b = 0` only at the
initialization `i = 0` (line 372); later bond dimensions are positive polynomials. Documented in
`docs/paper-gaps/lvv13_bond_dimension_zero.tex`.

## Main definitions

* `TNLean.MPS.AreaLaw.leftSupportSubmodule`: the vectors whose cut-matrix columns lie in
  `Span(S)`, that is, `Span(S) ⊗ H_R`.
* `TNLean.MPS.AreaLaw.spanProjection`: the orthogonal projection onto `Span(S)` as a matrix.
* `TNLean.MPS.AreaLaw.IsViable`: the `(i, δ)`-viable sets.
* `TNLean.MPS.AreaLaw.IsLeftOpenMPS`, `TNLean.MPS.AreaLaw.IsViableMPS`: matrix product states on
  the first `i` sites and the `(i, s, b, δ)`-viable sets.
* `TNLean.MPS.AreaLaw.extendSite`, `TNLean.MPS.AreaLaw.extend`: `v ↦ v ⊗ |k⟩` and the extended
  set `S ⊗ {|1⟩, …, |q⟩}`.

## Main results

* `TNLean.MPS.AreaLaw.spanProjection_mul_regionState_eq_iff`,
  `TNLean.MPS.AreaLaw.spanProjection_mul_cutMatrix_eq_iff`,
  `TNLean.MPS.AreaLaw.leftApply_spanProjection_cutVector_eq_iff`: the support condition in
  density, matrix and vector form.
* `TNLean.MPS.AreaLaw.isViable_iff_le_norm_starProjection`: for `δ < 1`, `S` is
  `(i, δ)`-viable iff `‖P_{Span(S) ⊗ H_R} Γ‖ ≥ 1 - δ`.
* `TNLean.MPS.AreaLaw.isViable_iff_forall_mem_span_singleton`: for a unit vector `Γ` and
  `δ < 1`, viability as closeness of `Span(S) ⊗ H_R` to `span {Γ}`.
* `TNLean.MPS.AreaLaw.IsViable.extend`, `TNLean.MPS.AreaLaw.IsViableMPS.extend`: Claim `c:ext`.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`:
  Definition `def:viable`, lines 240–244; algorithm step 1 (extension), lines 379–389;
  Claim `c:ext` and its proof, lines 395–400.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-! ### The support condition -/

/-- Vectors on the configurations of the left block of the cut after `k` sites. -/
abbrev LeftBlockVector (L q k : ℕ) : Type :=
  EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k))

/-- The column of the cut matrix of `ψ` after `k` sites at a configuration `b` of the sites
right of the cut, as a vector on the left block. -/
noncomputable def cutColumn (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ)
    (b : (v : {v : Fin L // v ∉ leftBlock L k}) → Fin q) : LeftBlockVector L q k :=
  WithLp.toLp 2 fun a ↦ cutMatrix ψ k a b

/-- The entries of a cut-matrix column. -/
@[simp]
theorem cutColumn_apply (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ)
    (b : (v : {v : Fin L // v ∉ leftBlock L k}) → Fin q)
    (a : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    cutColumn ψ k b a = cutMatrix ψ k a b :=
  rfl

/-- The vectors on the chain whose reduced density on the first `k` sites is supported on
`Span(S)`: every column of the cut matrix after `k` sites lies in `Span(S)`. This is the
subspace `Span(S) ⊗ H_R` of Landau, Vazirani and Vidick (arXiv:1307.5143v1, algo53.tex,
lines 240–242); `spanProjection_mul_regionState_eq_iff` identifies it with the support
condition on the reduced density. -/
noncomputable def leftSupportSubmodule {k : ℕ} (S : Set (LeftBlockVector L q k)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)) where
  carrier := {ψ | ∀ b, cutColumn ψ k b ∈ Submodule.span ℂ S}
  add_mem' hψ hψ' b := add_mem (hψ b) (hψ' b)
  zero_mem' _ := zero_mem _
  smul_mem' c _ hψ b := Submodule.smul_mem _ c (hψ b)

/-- Membership in `Span(S) ⊗ H_R`: every cut-matrix column lies in `Span(S)`. -/
theorem mem_leftSupportSubmodule {k : ℕ} {S : Set (LeftBlockVector L q k)}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)} :
    ψ ∈ leftSupportSubmodule S ↔ ∀ b, cutColumn ψ k b ∈ Submodule.span ℂ S :=
  Iff.rfl

/-- The orthogonal projection onto `Span(S)`, as a matrix on the configurations of the first
`k` sites. -/
noncomputable def spanProjection {k : ℕ} (S : Set (LeftBlockVector L q k)) :
    LeftBlockMatrix L q k :=
  Matrix.toEuclideanLin.symm (Submodule.span ℂ S).starProjection.toLinearMap

/-- As an operator, the matrix `spanProjection S` is the projection onto `Span(S)`. -/
theorem toEuclideanLin_spanProjection {k : ℕ} (S : Set (LeftBlockVector L q k)) :
    toEuclideanLin (spanProjection S) = (Submodule.span ℂ S).starProjection.toLinearMap :=
  LinearEquiv.apply_symm_apply _ _

/-- The projection onto `Span(S)` is an orthogonal projection. -/
theorem isStarProjection_spanProjection {k : ℕ} (S : Set (LeftBlockVector L q k)) :
    IsStarProjection (spanProjection S) :=
  (isStarProjection_starProjection (U := Submodule.span ℂ S)).map
    (A := LeftBlockVector L q k →L[ℂ] LeftBlockVector L q k)
    (B := LeftBlockMatrix L q k)
    (Matrix.toEuclideanCLM (n := Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k))
      (𝕜 := ℂ)).symm.toStarAlgHom

/-- The projection onto `Span(S)` is Hermitian. -/
theorem isHermitian_spanProjection {k : ℕ} (S : Set (LeftBlockVector L q k)) :
    (spanProjection S).IsHermitian :=
  (isStarProjection_spanProjection S).isSelfAdjoint

/-- The projection onto `Span(S)` is idempotent. -/
theorem spanProjection_mul_self {k : ℕ} (S : Set (LeftBlockVector L q k)) :
    spanProjection S * spanProjection S = spanProjection S :=
  (isStarProjection_spanProjection S).isIdempotentElem.eq

/-- The matrix `spanProjection S` acts on vectors as the projection onto `Span(S)`. -/
theorem toLp_spanProjection_mulVec {k : ℕ} (S : Set (LeftBlockVector L q k))
    (v : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) → ℂ) :
    WithLp.toLp 2 (spanProjection S *ᵥ v) =
      (Submodule.span ℂ S).starProjection (WithLp.toLp 2 v) := by
  have h := congrArg (fun f ↦ f (WithLp.toLp 2 v)) (toEuclideanLin_spanProjection S)
  simpa using h

/-- **Support in matrix form.** `P M = M` for the projection `P` onto `Span(S)` and the cut
matrix `M` after `k` sites exactly when every column of `M` lies in `Span(S)`. -/
theorem spanProjection_mul_cutMatrix_eq_iff {k : ℕ} {S : Set (LeftBlockVector L q k)}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)} :
    spanProjection S * cutMatrix ψ k = cutMatrix ψ k ↔ ψ ∈ leftSupportSubmodule S := by
  rw [mem_leftSupportSubmodule]
  simp_rw [← Submodule.starProjection_eq_self_iff]
  constructor
  · intro h b
    rw [cutColumn, ← toLp_spanProjection_mulVec]
    congr 1
    funext a
    simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun h a) b
  · intro h
    ext a b
    have := congrArg (fun w ↦ w a) (h b)
    rw [cutColumn, ← toLp_spanProjection_mulVec] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct] using this

/-- The reduced density on the first `k` sites is `M Mᴴ` for the cut matrix `M`. -/
theorem regionState_leftBlock_eq (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ) :
    Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ =
      cutMatrix ψ k * (cutMatrix ψ k)ᴴ := by
  simp only [Entropy.regionState, Matrix.partialTraceRight_vecMulVec_eq, cutMatrix]

/-- **Support in density form.** The reduced density `ρ` of `ψ` on the first `k` sites is
supported on `Span(S)`, `P ρ = ρ`, exactly when `ψ ∈ Span(S) ⊗ H_R`. This is the support
condition of Definition `def:viable` (arXiv:1307.5143v1, algo53.tex, lines 240–242). -/
theorem spanProjection_mul_regionState_eq_iff {k : ℕ} {S : Set (LeftBlockVector L q k)}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)} :
    spanProjection S * Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ =
        Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ ↔
      ψ ∈ leftSupportSubmodule S := by
  rw [← spanProjection_mul_cutMatrix_eq_iff, regionState_leftBlock_eq]
  set P := spanProjection S
  set M := cutMatrix ψ k
  constructor
  · intro h
    have h0 : (1 - P) * (M * Mᴴ) = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
    have h1 : (1 - P) * M * ((1 - P) * M)ᴴ = 0 := by
      calc (1 - P) * M * ((1 - P) * M)ᴴ = (1 - P) * (M * Mᴴ) * (1 - P)ᴴ := by
            rw [conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [h0, Matrix.zero_mul]
    have h2 := self_mul_conjTranspose_eq_zero.mp h1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h2
    exact h2.symm
  · intro h
    rw [← Matrix.mul_assoc, h]

/-- In the coordinates of the cut after `k` sites, `(P ⊗ 1) ψ = ψ` exactly when `P M = M` for
the cut matrix `M`. -/
theorem leftApply_cutVector_eq_iff {k : ℕ} (P : LeftBlockMatrix L q k)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    leftApply P (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ) =
        Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ ↔
      P * cutMatrix ψ k = cutMatrix ψ k := by
  constructor
  · intro h
    exact congrArg (fun w ↦ schmidtCoeffMatrix (WithLp.ofLp w)) h
  · intro h
    change toEuclid (P * cutMatrix ψ k) = _
    rw [h]
    rfl

/-- **Support in vector form.** `(P ⊗ 1) ψ = ψ` for the projection `P` onto `Span(S)`, in the
coordinates of the cut after `k` sites, exactly when `ψ ∈ Span(S) ⊗ H_R`. This is the form of
the hypothesis of `Matrix.IsTrimmingProjection.exists_trimmed_witness`. -/
theorem leftApply_spanProjection_cutVector_eq_iff {k : ℕ} {S : Set (LeftBlockVector L q k)}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)} :
    leftApply (spanProjection S)
        (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ) =
        Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ ↔
      ψ ∈ leftSupportSubmodule S := by
  rw [leftApply_cutVector_eq_iff, spanProjection_mul_cutMatrix_eq_iff]

/-! ### Viable sets -/

/-- **`(i, δ)`-viable sets** (Landau, Vazirani, Vidick, arXiv:1307.5143v1, algo53.tex,
Definition `def:viable`, lines 240–242). A set `S` of vectors on the first `i` sites is
`(i, δ)`-viable for `Γ` when some unit vector `φ`, the witness, has `|⟨φ, Γ⟩| ≥ 1 - δ` and
reduced density on the first `i` sites supported on `Span(S)`. The source's ranges `δ > 0` and
`1 ≤ i ≤ L` only exclude degenerate cases and are not imposed. -/
def IsViable (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (δ : ℝ) {i : ℕ}
    (S : Set (LeftBlockVector L q i)) : Prop :=
  ∃ φ : EuclideanSpace ℂ (Fin L → Fin q),
    ‖φ‖ = 1 ∧ 1 - δ ≤ ‖⟪φ, Γ⟫_ℂ‖ ∧ φ ∈ leftSupportSubmodule S

/-- The overlap of a unit vector of a subspace `U` with `Γ` is at most `‖P_U Γ‖`. -/
private theorem norm_inner_le_norm_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {U : Submodule ℂ E} [U.HasOrthogonalProjection] {φ : E}
    (hφ : φ ∈ U) (h1 : ‖φ‖ = 1) (Γ : E) : ‖⟪φ, Γ⟫_ℂ‖ ≤ ‖U.starProjection Γ‖ := by
  have : ⟪φ, Γ⟫_ℂ = ⟪φ, U.starProjection Γ⟫_ℂ := by
    rw [← U.inner_starProjection_left_eq_right, U.starProjection_eq_self_iff.mpr hφ]
  rw [this]
  simpa [h1] using norm_inner_le_norm (𝕜 := ℂ) φ (U.starProjection Γ)

/-- A viable set captures at least `1 - δ` of `Γ` in norm: `‖P_{Span(S) ⊗ H_R} Γ‖ ≥ 1 - δ`. -/
theorem IsViable.le_norm_starProjection {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ : ℝ}
    {i : ℕ} {S : Set (LeftBlockVector L q i)} (h : IsViable Γ δ S) :
    1 - δ ≤ ‖(leftSupportSubmodule S).starProjection Γ‖ := by
  obtain ⟨φ, h1, hδ, hφ⟩ := h
  exact hδ.trans (norm_inner_le_norm_starProjection hφ h1 Γ)

/-- **Viability as a projection bound.** For `δ < 1`, `S` is `(i, δ)`-viable for `Γ` exactly
when `‖P_{Span(S) ⊗ H_R} Γ‖ ≥ 1 - δ`; the normalized projection is then a witness.

The bound `δ < 1` is needed: for `δ = 1` and `Span(S) = 0` the right side holds while no unit
witness exists. -/
theorem isViable_iff_le_norm_starProjection {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ : ℝ}
    (hδ : δ < 1) {i : ℕ} {S : Set (LeftBlockVector L q i)} :
    IsViable Γ δ S ↔ 1 - δ ≤ ‖(leftSupportSubmodule S).starProjection Γ‖ := by
  refine ⟨IsViable.le_norm_starProjection, fun h ↦ ?_⟩
  set U := leftSupportSubmodule S
  set p := U.starProjection Γ
  have hp : 0 < ‖p‖ := by linarith
  refine ⟨((‖p‖⁻¹ : ℝ) : ℂ) • p, ?_, ?_, U.smul_mem _ (U.starProjection_apply_mem Γ)⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hp,
      inv_mul_cancel₀ hp.ne']
  · have hpp : ⟪p, Γ⟫_ℂ = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
      have : ⟪p, Γ⟫_ℂ = ⟪p, p⟫_ℂ := by
        have e : U.starProjection p = p :=
          U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem Γ)
        calc ⟪p, Γ⟫_ℂ = ⟪U.starProjection p, Γ⟫_ℂ := by rw [e]
          _ = ⟪p, U.starProjection Γ⟫_ℂ := U.inner_starProjection_left_eq_right _ _
      rw [this, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [inner_smul_left, hpp, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc 1 - δ ≤ ‖p‖ := h
      _ = ‖p‖⁻¹ * ‖p‖ ^ 2 := by field_simp

/-- **Viability as closeness.** If `S` is `(i, δ)`-viable for a unit vector `Γ` with `δ ≤ 1`,
every `t ∈ span {Γ}` satisfies `(1 - δ') ‖t‖² ≤ ‖P_{Span(S) ⊗ H_R} t‖²` with
`δ' = 1 - (1 - δ)²`. This is the vector form (`Submodule.isCloseTo_iff`, QICLean main, not yet
pinned here) of
`Submodule.IsCloseTo δ' (Span(S) ⊗ H_R) (span {Γ})`: `Span(S)` is `δ'`-viable for `span {Γ}` in the
sense of Arad, Landau, Vazirani and Vidick (arXiv:1602.08828v2, Definitions `d:vs` and
`d:close`). -/
theorem IsViable.forall_mem_span_singleton {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΓ : ‖Γ‖ = 1) {δ : ℝ} (hδ : δ ≤ 1) {i : ℕ} {S : Set (LeftBlockVector L q i)}
    (h : IsViable Γ δ S) :
    ∀ t ∈ ℂ ∙ Γ, (1 - (1 - (1 - δ) ^ 2)) * ‖t‖ ^ 2 ≤
      ‖(leftSupportSubmodule S).starProjection t‖ ^ 2 := by
  intro t ht
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
  have hP := h.le_norm_starProjection
  rw [map_smul, norm_smul, norm_smul, hΓ, mul_one]
  have h0 : 0 ≤ 1 - δ := by linarith
  have h1 : (1 - δ) ^ 2 ≤ ‖(leftSupportSubmodule S).starProjection Γ‖ ^ 2 := by gcongr
  have h2 : 0 ≤ ‖c‖ ^ 2 := by positivity
  nlinarith

/-- **Viability iff closeness.** For a unit vector `Γ` and `δ < 1`, `S` is `(i, δ)`-viable for
`Γ` exactly when `Span(S) ⊗ H_R` is `(1 - (1 - δ)²)`-close to `span {Γ}`, in the vector form of
`Submodule.isCloseTo_iff` (QICLean). -/
theorem isViable_iff_forall_mem_span_singleton {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΓ : ‖Γ‖ = 1) {δ : ℝ} (hδ : δ < 1) {i : ℕ} {S : Set (LeftBlockVector L q i)} :
    IsViable Γ δ S ↔ ∀ t ∈ ℂ ∙ Γ, (1 - (1 - (1 - δ) ^ 2)) * ‖t‖ ^ 2 ≤
      ‖(leftSupportSubmodule S).starProjection t‖ ^ 2 := by
  refine ⟨fun h ↦ h.forall_mem_span_singleton hΓ hδ.le, fun h ↦ ?_⟩
  rw [isViable_iff_le_norm_starProjection hδ]
  have h1 := h Γ (Submodule.mem_span_singleton_self Γ)
  rw [hΓ] at h1
  have h0 : 0 < 1 - δ := by linarith
  have h2 : 0 ≤ ‖(leftSupportSubmodule S).starProjection Γ‖ := norm_nonneg _
  nlinarith

/-! ### Matrix product states on the first sites -/

/-- A configuration of `Fin k` read as a configuration of the left block of the cut after `k`
sites. -/
def leftConfigOfFin {k : ℕ} (x : Fin k → Fin q) :
    Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) :=
  fun v ↦ x ⟨v.1.val, mem_leftBlock.mp v.2⟩

/-- A vector on the first `k` sites is a matrix product state of bond dimension at most `b`
(arXiv:1307.5143v1, algo53.tex, line 243): read on `Fin k → Fin q` through
`leftConfigOfFin`, a bijection when `k ≤ L`, it is an open-boundary matrix product state of bond
dimension at most `max 1 b`; see the module docstring for `b = 0`. -/
def IsLeftOpenMPS (b : ℕ) {k : ℕ} (v : LeftBlockVector L q k) : Prop :=
  IsOpenMPS k q (max 1 b) fun x ↦ v (leftConfigOfFin x)

/-- **`(i, s, b, δ)`-viable sets** (Landau, Vazirani, Vidick, arXiv:1307.5143v1, algo53.tex,
Definition `def:viable`, lines 240–244). `S` has at most `s` members, each a matrix product
state of bond dimension at most `b`, and is `(i, δ)`-viable for `Γ`. -/
def IsViableMPS (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ) {i : ℕ}
    (S : Finset (LeftBlockVector L q i)) : Prop :=
  S.card ≤ s ∧ (∀ v ∈ S, IsLeftOpenMPS b v) ∧ IsViable Γ δ (S : Set (LeftBlockVector L q i))

/-! ### Claim `c:ext` -/

/-- The restriction of a configuration of the first `k'` sites to the first `k ≤ k'`. -/
def restrictLeft {k k' : ℕ} (h : k ≤ k')
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k')) :
    Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) :=
  fun v ↦ x ⟨v.1, leftBlock_mono h v.2⟩

/-- The vector `v ⊗ |k⟩` on the first `i` sites for `v` on the first `i - 1` sites
(arXiv:1307.5143v1, algo53.tex, line 386). The basis state `|k⟩` sits on the sites of the left
block after `i` sites outside that after `i - 1` sites, which for `1 ≤ i ≤ L` is site `i - 1`
(`extendSite_apply`). -/
noncomputable def extendSite (i : ℕ) (k : Fin q) :
    LeftBlockVector L q (i - 1) →ₗ[ℂ] LeftBlockVector L q i where
  toFun v := WithLp.toLp 2 fun x ↦
    if ∀ s : {s : Fin L // s ∈ leftBlock L i}, s.1 ∉ leftBlock L (i - 1) → x s = k then
      v (restrictLeft (Nat.sub_le i 1) x) else 0
  map_add' v w := by
    ext x
    simp only [PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    ext x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-- The site `i - 1`, the last site of the left block after `i` sites. -/
def lastLeftSite {i : ℕ} (hi0 : 0 < i) (hiL : i ≤ L) : {s : Fin L // s ∈ leftBlock L i} :=
  ⟨⟨i - 1, by omega⟩, mem_leftBlock.mpr (by simp only; omega)⟩

/-- For `1 ≤ i ≤ L`, `(v ⊗ |k⟩)(x) = v(x₀, …, x_{i-2})` when `x_{i-1} = k` and `0`
otherwise. -/
theorem extendSite_apply {i : ℕ} (hi0 : 0 < i) (hiL : i ≤ L) (k : Fin q)
    (v : LeftBlockVector L q (i - 1))
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i)) :
    extendSite i k v x =
      if x (lastLeftSite hi0 hiL) = k then v (restrictLeft (Nat.sub_le i 1) x) else 0 := by
  change (if _ then _ else _) = _
  congr 1
  apply propext
  constructor
  · intro h
    exact h _ (by simp [lastLeftSite, mem_leftBlock])
  · intro h s hs2
    have : s = lastLeftSite hi0 hiL := by
      have h1 := mem_leftBlock.mp s.2
      have h2 : ¬ s.1.val < i - 1 := fun h ↦ hs2 (mem_leftBlock.mpr h)
      exact Subtype.ext (Fin.ext (by simp only [lastLeftSite]; omega))
    rw [this, h]

/-- The extended set `S ⊗ {|1⟩, …, |q⟩} = {v ⊗ |k⟩ : v ∈ S, k}` on the first `i` sites
(arXiv:1307.5143v1, algo53.tex, line 386). -/
noncomputable def extend (i : ℕ) (S : Finset (LeftBlockVector L q (i - 1))) :
    Finset (LeftBlockVector L q i) :=
  open Classical in Finset.image₂ (fun v k ↦ extendSite i k v) S Finset.univ

/-- Every `v ⊗ |k⟩` with `v ∈ S` belongs to the extended set. -/
theorem extendSite_mem_extend {i : ℕ} {S : Finset (LeftBlockVector L q (i - 1))}
    {v : LeftBlockVector L q (i - 1)} (hv : v ∈ S) (k : Fin q) :
    extendSite i k v ∈ extend i S := by
  classical
  unfold extend
  convert Finset.mem_image₂_of_mem hv (Finset.mem_univ k)

/-- The extended set has at most `q |S|` members (arXiv:1307.5143v1, algo53.tex, line 399). -/
theorem card_extend_le (i : ℕ) (S : Finset (LeftBlockVector L q (i - 1))) :
    (extend i S).card ≤ q * S.card := by
  classical
  unfold extend
  refine (Finset.card_image₂_le _ _ _).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_fin, mul_comm]

/-- The configuration `(k, b)` of the sites right of the cut after `i - 1` sites, for `b` on
the sites right of the cut after `i` sites. -/
def consRightConfig {i : ℕ} (k : Fin q) (b : (v : {v : Fin L // v ∉ leftBlock L i}) → Fin q) :
    (v : {v : Fin L // v ∉ leftBlock L (i - 1)}) → Fin q :=
  fun v ↦ if h : v.1 ∈ leftBlock L i then k else b ⟨v.1, h⟩

/-- Decomposing site `i - 1` on the computational basis: the column of the cut matrix after `i`
sites at `b` is `∑ₖ c_{k,b} ⊗ |k⟩`, with `c_{k,b}` the column after `i - 1` sites at `(k, b)`
(arXiv:1307.5143v1, algo53.tex, line 399). -/
theorem cutColumn_eq_sum_extendSite {i : ℕ} (hi0 : 0 < i) (hiL : i ≤ L)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (b : (v : {v : Fin L // v ∉ leftBlock L i}) → Fin q) :
    cutColumn ψ i b =
      ∑ k : Fin q, extendSite i k (cutColumn ψ (i - 1) (consRightConfig k b)) := by
  ext x
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [extendSite_apply hi0 hiL, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    cutColumn_apply, cutMatrix_apply]
  refine congrArg (fun y ↦ ψ y) ?_
  funext j
  by_cases h1 : (j : ℕ) < i - 1
  · have hj : j ∈ leftBlock L (i - 1) := mem_leftBlock.mpr h1
    have hj' : j ∈ leftBlock L i := mem_leftBlock.mpr (by omega)
    simp [Equiv.piEquivPiSubtypeProd_symm_apply, hj, hj', restrictLeft]
  · have hj : j ∉ leftBlock L (i - 1) := fun h ↦ h1 (mem_leftBlock.mp h)
    by_cases h2 : (j : ℕ) < i
    · have hj' : j ∈ leftBlock L i := mem_leftBlock.mpr h2
      simp only [Equiv.piEquivPiSubtypeProd_symm_apply, hj, hj', consRightConfig, ↓reduceDIte]
      congr 1
      exact Subtype.ext (Fin.ext (by simp only [lastLeftSite]; omega))
    · have hj' : j ∉ leftBlock L i := fun h ↦ h2 (mem_leftBlock.mp h)
      simp [Equiv.piEquivPiSubtypeProd_symm_apply, hj, hj', consRightConfig]

/-- **The witness survives the extension** (arXiv:1307.5143v1, algo53.tex, line 399). For
`1 ≤ i ≤ L`, every vector supported on `Span(S)` across the cut after `i - 1` sites is supported
on `Span(S ⊗ {|1⟩, …, |q⟩})` across the cut after `i` sites. -/
theorem leftSupportSubmodule_le_extend {i : ℕ} (hi0 : 0 < i) (hiL : i ≤ L)
    (S : Finset (LeftBlockVector L q (i - 1))) :
    leftSupportSubmodule (S : Set (LeftBlockVector L q (i - 1))) ≤
      leftSupportSubmodule (extend i S : Set (LeftBlockVector L q i)) := by
  intro ψ hψ b
  rw [cutColumn_eq_sum_extendSite hi0 hiL]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  have h := Submodule.mem_map_of_mem (f := extendSite i k) (hψ (consRightConfig k b))
  rw [Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨v, hv, rfl⟩
  exact extendSite_mem_extend hv k

/-- **Claim `c:ext`, viability** (arXiv:1307.5143v1, algo53.tex, lines 395–400). For
`1 ≤ i ≤ L`, if `S` is `(i - 1, δ)`-viable for `Γ`, then `S ⊗ {|1⟩, …, |q⟩}` is
`(i, δ)`-viable for `Γ`, with the same witness. -/
theorem IsViable.extend {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ : ℝ} {i : ℕ}
    (hi0 : 0 < i) (hiL : i ≤ L) {S : Finset (LeftBlockVector L q (i - 1))}
    (h : IsViable Γ δ (S : Set (LeftBlockVector L q (i - 1)))) :
    IsViable Γ δ (AreaLaw.extend i S : Set (LeftBlockVector L q i)) := by
  obtain ⟨φ, h1, h2, h3⟩ := h
  exact ⟨φ, h1, h2, leftSupportSubmodule_le_extend hi0 hiL S h3⟩

/-- **Claim `c:ext`, bond dimension** (arXiv:1307.5143v1, algo53.tex, lines 393 and 399). For
`1 ≤ i ≤ L`, if `v` is a matrix product state of bond dimension at most `b` on the
first `i - 1` sites, so is `v ⊗ |k⟩` on the first `i` sites. -/
theorem IsLeftOpenMPS.extendSite {i b : ℕ} (hi0 : 0 < i) (hiL : i ≤ L)
    {v : LeftBlockVector L q (i - 1)} (hv : IsLeftOpenMPS b v) (k : Fin q) :
    IsLeftOpenMPS b (AreaLaw.extendSite i k v) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hv' : IsOpenMPS n q (max 1 b) fun x ↦ v (leftConfigOfFin x) := hv
  have h := hv'.snoc (lt_of_lt_of_le Nat.one_pos (le_max_left 1 b)) fun y ↦
    if y = k then 1 else 0
  unfold IsLeftOpenMPS
  convert h using 1
  funext x
  rw [extendSite_apply hi0 hiL, mul_ite, mul_one, mul_zero]
  rfl

/-- **Claim `c:ext`** (arXiv:1307.5143v1, algo53.tex, lines 379–400). For `1 ≤ i ≤ L`, if `S` is
`(i - 1, s, b, δ)`-viable for `Γ`, then `S ⊗ {|1⟩, …, |q⟩}` is `(i, q s, b, δ)`-viable for `Γ`.
The source states this for `δ = c_ε / n`; the argument does not use the value of `δ`. -/
theorem IsViableMPS.extend {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    (hi0 : 0 < i) (hiL : i ≤ L) {S : Finset (LeftBlockVector L q (i - 1))}
    (h : IsViableMPS Γ s b δ S) : IsViableMPS Γ (q * s) b δ (AreaLaw.extend i S) := by
  classical
  obtain ⟨hs, hmps, hv⟩ := h
  refine ⟨(card_extend_le i S).trans (Nat.mul_le_mul_left q hs), fun w hw ↦ ?_,
    hv.extend hi0 hiL⟩
  unfold AreaLaw.extend at hw
  obtain ⟨v, hvS, k, -, rfl⟩ := Finset.mem_image₂.mp hw
  exact (hmps v hvS).extendSite hi0 hiL k

end TNLean.MPS.AreaLaw
