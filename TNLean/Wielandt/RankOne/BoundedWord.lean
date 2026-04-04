/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.Wielandt.RankOne.SpanGrowth
import TNLean.Wielandt.RankOne.Manufacture
import TNLean.Wielandt.RectangularSpan.Ranges
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan

/-!
# Bounded rank-one element in a blocked word span (Wielandt Lemma 2(b))

This file introduces a two-sided ("bi-rectangular") span

`biRectSpan P Q B n = span{ P * M * Q : M ∈ wordSpan B n }`

and develops basic API (membership, finrank bounds, injectivity tools) for the
missing rank-one extraction step in the Quantum Wielandt proof.

The eventual goal is to show that for suitable choices of `P,Q` (coming from
nilpotent-killing powers) the spans `biRectSpan P Q B n` stabilize to the full
two-sided range of the linear map `X ↦ P * X * Q`, within a bound depending
only on `D`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Two-sided (bi-rectangular) span: image of `wordSpan B n` under right-multiplication by `Q`
followed by left-multiplication by `P`.

This is the linear span of all matrices of the form `P * M * Q` where
`M` ranges over word products of length `n`. -/
noncomputable def biRectSpan
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Submodule.map (LinearMap.mulLeft ℂ P)
    (Submodule.map (LinearMap.mulRight ℂ Q) (wordSpan B n))

@[simp]
lemma biRectSpan_eq_map_comp
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (n : ℕ) :
    biRectSpan (d := d) (D := D) P Q B n =
      Submodule.map ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q))
        (wordSpan B n) := by
  -- `Submodule.map_comp` is stated for semilinear maps; specialize to linear maps.
  simpa [biRectSpan, LinearMap.comp_apply] using
    (Submodule.map_comp (f := (LinearMap.mulRight ℂ Q)) (g := (LinearMap.mulLeft ℂ P))
      (p := wordSpan B n)).symm

/-- If the exact word span is already full, the bi-rectangular span is the full two-sided
range. -/
theorem biRectSpan_eq_range_of_wordSpan_eq_top
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) {n : ℕ}
    (htop : wordSpan B n = ⊤) :
    biRectSpan (d := d) (D := D) P Q B n =
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) := by
  rw [biRectSpan_eq_map_comp, htop, Submodule.map_top]

private theorem mem_biRectSpan_iff
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) {n : ℕ}
    {M : Matrix (Fin D) (Fin D) ℂ} :
    M ∈ biRectSpan (d := d) (D := D) P Q B n ↔
      ∃ X, X ∈ wordSpan B n ∧ P * X * Q = M := by
  constructor
  · intro hM
    rcases Submodule.mem_map.mp hM with ⟨X, hX, rfl⟩
    rcases Submodule.mem_map.mp hX with ⟨Y, hY, rfl⟩
    refine ⟨Y, hY, ?_⟩
    simp [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]
  · rintro ⟨X, hX, hM⟩
    rw [← hM]
    refine Submodule.mem_map.mpr ?_
    refine ⟨X * Q, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨X, hX, by simp [LinearMap.mulRight_apply]⟩
    · simp [LinearMap.mulLeft_apply, Matrix.mul_assoc]

/-- `biRectSpan` always lives in the range of the two-sided multiplication map. -/
theorem biRectSpan_le_range
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (n : ℕ) :
    biRectSpan (d := d) (D := D) P Q B n ≤
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) := by
  intro M hM
  rcases (mem_biRectSpan_iff (d := d) (D := D) P Q B).mp hM with ⟨X, _, hX⟩
  exact ⟨X, by
    simpa [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      Matrix.mul_assoc] using hX⟩

/-- Converting a bi-rectangular span element back into a bounded word span,
assuming `P` and `Q` themselves lie in bounded word spans. -/
theorem biRectSpan_le_wordSpan
    (B : MPSTensor d D) {m₁ m₂ n : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂) :
    biRectSpan (d := d) (D := D) P Q B n ≤ wordSpan B (m₁ + n + m₂) := by
  classical
  intro M hM
  rcases (mem_biRectSpan_iff (d := d) (D := D) P Q B).mp hM with ⟨Y, hY, hM⟩
  have hPY : P * Y ∈ wordSpan B (m₁ + n) := by
    exact (wordSpan_mul_le B m₁ n) (Submodule.mul_mem_mul hP hY)
  have hPYQ : (P * Y) * Q ∈ wordSpan B ((m₁ + n) + m₂) := by
    exact (wordSpan_mul_le B (m₁ + n) m₂) (Submodule.mul_mem_mul hPY hQ)
  rw [← hM]
  simpa [Matrix.mul_assoc, Nat.add_assoc] using hPYQ

/-- Two-sided cumulative bi-rectangular span: image of `cumulativeSpan B n` under
right-multiplication by `Q` followed by left-multiplication by `P`. -/
noncomputable def cumulativeBiRectSpan
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Submodule.map (LinearMap.mulLeft ℂ P)
    (Submodule.map (LinearMap.mulRight ℂ Q) (cumulativeSpan B n))

@[simp]
lemma cumulativeBiRectSpan_eq_map_comp
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (n : ℕ) :
    cumulativeBiRectSpan (d := d) (D := D) P Q B n =
      Submodule.map ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q))
        (cumulativeSpan B n) := by
  simpa [cumulativeBiRectSpan, LinearMap.comp_apply] using
    (Submodule.map_comp (f := (LinearMap.mulRight ℂ Q)) (g := (LinearMap.mulLeft ℂ P))
      (p := cumulativeSpan B n)).symm

private theorem mem_cumulativeBiRectSpan_iff
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) {n : ℕ}
    {M : Matrix (Fin D) (Fin D) ℂ} :
    M ∈ cumulativeBiRectSpan (d := d) (D := D) P Q B n ↔
      ∃ X, X ∈ cumulativeSpan B n ∧ P * X * Q = M := by
  constructor
  · intro hM
    rcases Submodule.mem_map.mp hM with ⟨X, hX, rfl⟩
    rcases Submodule.mem_map.mp hX with ⟨Y, hY, rfl⟩
    refine ⟨Y, hY, ?_⟩
    simp [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]
  · rintro ⟨X, hX, hM⟩
    rw [← hM]
    refine Submodule.mem_map.mpr ?_
    refine ⟨X * Q, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨X, hX, by simp [LinearMap.mulRight_apply]⟩
    · simp [LinearMap.mulLeft_apply, Matrix.mul_assoc]

/-- If the cumulative span is already full, the cumulative bi-rectangular span is the
full two-sided range. -/
theorem cumulativeBiRectSpan_eq_range_of_cumulativeSpan_eq_top
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) {n : ℕ}
    (htop : cumulativeSpan B n = ⊤) :
    cumulativeBiRectSpan (d := d) (D := D) P Q B n =
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) := by
  rw [cumulativeBiRectSpan_eq_map_comp, htop, Submodule.map_top]

/-- Left multiplication by an exact-length word-span element raises cumulative length
by the corresponding offset. -/
theorem mul_mem_cumulativeSpan_of_mem_wordSpan_left
    (B : MPSTensor d D) {m n : ℕ}
    {P X : Matrix (Fin D) (Fin D) ℂ}
    (hP : P ∈ wordSpan B m) (hX : X ∈ cumulativeSpan B n) :
    P * X ∈ cumulativeSpan B (m + n) := by
  have hmap :
      Submodule.map (LinearMap.mulLeft ℂ P) (cumulativeSpan B n) ≤
        cumulativeSpan B (m + n) := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro M ⟨w, hw, rfl⟩
    change P * evalWord B w ∈ cumulativeSpan B (m + n)
    have hw' : evalWord B w ∈ wordSpan B w.length :=
      evalWord_mem_wordSpan B w
    have hprod : P * evalWord B w ∈ wordSpan B (m + w.length) := by
      exact (wordSpan_mul_le B m w.length) (Submodule.mul_mem_mul hP hw')
    exact (wordSpan_le_cumulativeSpan B (by omega)) hprod
  exact hmap (Submodule.mem_map.mpr ⟨X, hX, by simp [LinearMap.mulLeft_apply]⟩)

/-- Right multiplication by an exact-length word-span element raises cumulative length
by the corresponding offset. -/
theorem mul_mem_cumulativeSpan_of_mem_wordSpan_right
    (B : MPSTensor d D) {n m : ℕ}
    {X Q : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ cumulativeSpan B n) (hQ : Q ∈ wordSpan B m) :
    X * Q ∈ cumulativeSpan B (n + m) := by
  have hmap :
      Submodule.map (LinearMap.mulRight ℂ Q) (cumulativeSpan B n) ≤
        cumulativeSpan B (n + m) := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro M ⟨w, hw, rfl⟩
    change evalWord B w * Q ∈ cumulativeSpan B (n + m)
    have hw' : evalWord B w ∈ wordSpan B w.length :=
      evalWord_mem_wordSpan B w
    have hprod : evalWord B w * Q ∈ wordSpan B (w.length + m) := by
      exact (wordSpan_mul_le B w.length m) (Submodule.mul_mem_mul hw' hQ)
    exact (wordSpan_le_cumulativeSpan B (by omega)) hprod
  exact hmap (Submodule.mem_map.mpr ⟨X, hX, by simp [LinearMap.mulRight_apply]⟩)

/-- Converting a cumulative bi-rectangular span element back into a bounded cumulative span,
assuming `P` and `Q` themselves lie in bounded word spans. -/
theorem cumulativeBiRectSpan_le_cumulativeSpan
    (B : MPSTensor d D) {m₁ m₂ n : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂) :
    cumulativeBiRectSpan (d := d) (D := D) P Q B n ≤
      cumulativeSpan B (m₁ + n + m₂) := by
  intro M hM
  rcases (mem_cumulativeBiRectSpan_iff (d := d) (D := D) P Q B).mp hM with
    ⟨Y, hY, hM⟩
  have hPY : P * Y ∈ cumulativeSpan B (m₁ + n) :=
    mul_mem_cumulativeSpan_of_mem_wordSpan_left B hP hY
  have hPYQ : (P * Y) * Q ∈ cumulativeSpan B ((m₁ + n) + m₂) :=
    mul_mem_cumulativeSpan_of_mem_wordSpan_right B hPY hQ
  rw [← hM]
  simpa [Matrix.mul_assoc, Nat.add_assoc] using hPYQ

/-- Membership in the full two-sided range implies membership in a bounded cumulative span,
assuming the middle factor is available cumulatively. -/
theorem range_comp_le_cumulativeSpan
    (B : MPSTensor d D) {m₁ m₂ : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂)
    {n : ℕ} (htop : cumulativeSpan B n = ⊤) :
    LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) ≤
      cumulativeSpan B (m₁ + n + m₂) := by
  rw [← cumulativeBiRectSpan_eq_range_of_cumulativeSpan_eq_top (d := d) (D := D) P Q B htop]
  exact cumulativeBiRectSpan_le_cumulativeSpan (d := d) (D := D) B P Q hP hQ

/-- Under the aperiodicity hypothesis `1 ∈ wordSpan B 1`, cumulative spanning upgrades the
full two-sided range to a single exact-length word span. -/
theorem range_comp_le_wordSpan_of_cumulativeSpan_eq_top_of_aperiodic
    (B : MPSTensor d D) {m₁ m₂ : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂)
    {n : ℕ} (htop : cumulativeSpan B n = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan B 1) :
    LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) ≤
      wordSpan B (m₁ + n + m₂) := by
  rw [← cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one B hone (m₁ + n + m₂)]
  exact range_comp_le_cumulativeSpan (d := d) (D := D) B P Q hP hQ htop

/-- Rank-one manufacture from cumulative spanning: the manufactured rank-one element lies in a
bounded cumulative span. -/
theorem vecMulVec_mem_cumulativeSpan_of_cumulativeSpan_eq_top
    (B : MPSTensor d D) {m₁ m₂ n : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ) (φ ψ : Fin D → ℂ)
    (hφ : φ ∈ LinearMap.range (Matrix.toLin' P))
    (hψ : ψ ∈ LinearMap.range (Q.vecMulLinear))
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂)
    (htop : cumulativeSpan B n = ⊤) :
    Matrix.vecMulVec φ ψ ∈ cumulativeSpan B (m₁ + n + m₂) := by
  have hrange : Matrix.vecMulVec φ ψ ∈
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) :=
    vecMulVec_mem_range_mulLeft_mulRight P Q φ ψ hφ hψ
  exact (range_comp_le_cumulativeSpan (d := d) (D := D) B P Q hP hQ htop) hrange

/-- Rank-one manufacture from cumulative spanning plus aperiodicity: the manufactured rank-one
matrix lies in a single exact-length word span. -/
theorem vecMulVec_mem_wordSpan_of_cumulativeSpan_eq_top_of_aperiodic
    (B : MPSTensor d D) {m₁ m₂ n : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ) (φ ψ : Fin D → ℂ)
    (hφ : φ ∈ LinearMap.range (Matrix.toLin' P))
    (hψ : ψ ∈ LinearMap.range (Q.vecMulLinear))
    (hP : P ∈ wordSpan B m₁) (hQ : Q ∈ wordSpan B m₂)
    (htop : cumulativeSpan B n = ⊤)
    (hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan B 1) :
    Matrix.vecMulVec φ ψ ∈ wordSpan B (m₁ + n + m₂) := by
  have hrange : Matrix.vecMulVec φ ψ ∈
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) :=
    vecMulVec_mem_range_mulLeft_mulRight P Q φ ψ hφ hψ
  exact (range_comp_le_wordSpan_of_cumulativeSpan_eq_top_of_aperiodic
    (d := d) (D := D) B P Q hP hQ htop hone) hrange

/-- A crude finrank bound: any `biRectSpan` has dimension at most `D^2`. -/
theorem biRectSpan_finrank_le
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (n : ℕ) :
    Module.finrank ℂ (biRectSpan (d := d) (D := D) P Q B n) ≤ D ^ 2 := by
  calc
    Module.finrank ℂ (biRectSpan (d := d) (D := D) P Q B n)
        ≤ Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) := Submodule.finrank_le _
    _ = Fintype.card (Fin D) * Fintype.card (Fin D) * Module.finrank ℂ ℂ :=
          Module.finrank_matrix ℂ ℂ _ _
    _ = D * D * 1 := by
          simp [Fintype.card_fin, Module.finrank_self]
    _ = D ^ 2 := by ring

/-!
## Injectivity tools on invertible blocks

The next lemmas package the `RankOneSpanGrowth` disjointness statement into
convenient pointwise injectivity statements for left and right multiplication.
-/

namespace WielandtRankOne

open Module

/-- Vector-level injectivity: if `v ∈ range (M^D)` and `M *ᵥ v = 0`, then `v = 0`.

This is a direct consequence of `disjoint_ker_range_pow` for `Matrix.toLin' M`. -/
lemma vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow
    (M : Matrix (Fin D) (Fin D) ℂ) {v : Fin D → ℂ}
    (hv : v ∈ LinearMap.range (Matrix.toLin' (M ^ D)))
    (hMv : M *ᵥ v = 0) : v = 0 := by
  classical
  -- Convert to the endomorphism formulation.
  let f : End ℂ (Fin D → ℂ) := Matrix.toLin' M
  have hdisj : Disjoint (LinearMap.ker f) (LinearMap.range (f ^ D)) :=
    disjoint_ker_range_pow (D := D) (f := f)
  have hv' : v ∈ LinearMap.range (f ^ D) := by
    -- `Matrix.toLin' (M^D) = (Matrix.toLin' M)^D`.
    simpa [f, Matrix.toLin'_pow] using hv
  have hker : v ∈ LinearMap.ker f := by
    -- `M *ᵥ v = 0` means `f v = 0`.
    refine LinearMap.mem_ker.mpr ?_
    simpa [f, Matrix.toLin'_apply] using hMv
  -- Use disjointness: `ker f ⊓ range (f^D) = ⊥`.
  have hinter : (LinearMap.ker f ⊓ LinearMap.range (f ^ D)) = ⊥ := hdisj.eq_bot
  have hvInf : v ∈ (LinearMap.ker f ⊓ LinearMap.range (f ^ D)) := ⟨hker, hv'⟩
  have : v ∈ (⊥ : Submodule ℂ (Fin D → ℂ)) := by
    simpa [hinter] using hvInf
  simpa using this

/-- Matrix-level injectivity on the range of left multiplication by `M^D`.

If `X ∈ range (mulLeft (M^D))` and `M * X = 0`, then `X = 0`. -/
lemma matrix_eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow
    (M : Matrix (Fin D) (Fin D) ℂ) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ LinearMap.range (LinearMap.mulLeft ℂ (M ^ D)))
    (hMX : M * X = 0) : X = 0 := by
  classical
  -- Use the column characterization of `range (mulLeft _)`.
  have hcols : ∀ j : Fin D, X.col j ∈ LinearMap.range (Matrix.toLin' (M ^ D)) := by
    have := (mem_range_mulLeft_iff_cols (D := D) (P := M ^ D) (M := X)).1 hX
    simpa using this
  -- Each column is killed by `M`.
  have hcol0 : ∀ j : Fin D, X.col j = 0 := by
    intro j
    have hcolKilled : M *ᵥ (X.col j) = 0 := by
      have : (M * X).col j = 0 := by
        simpa using congrArg (fun Z : Matrix (Fin D) (Fin D) ℂ => Z.col j) hMX
      -- Rewrite the column as a matrix-vector product.
      simpa [col_mul (P := M) (X := X) (j := j)] using this
    exact vec_eq_zero_of_mulVec_eq_zero_of_mem_range_pow (D := D) M (hcols j) hcolKilled
  -- If all columns are zero, the matrix is zero.
  apply Matrix.ext_col
  intro j
  have hzero : (0 : Matrix (Fin D) (Fin D) ℂ).col j = (0 : Fin D → ℂ) := by
    ext i
    simp [Matrix.col_apply]
  simp [hcol0 j, hzero]

/-- Matrix-level injectivity on the range of right multiplication by `M^D`.

If `X ∈ range (mulRight (M^D))` and `X * M = 0`, then `X = 0`.

We reduce to the previous lemma by transposing. -/
lemma matrix_eq_zero_of_mul_eq_zero_of_mem_range_mulRight_pow
    (M : Matrix (Fin D) (Fin D) ℂ) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ LinearMap.range (LinearMap.mulRight ℂ (M ^ D)))
    (hXM : X * M = 0) : X = 0 := by
  classical
  -- Unpack `hX` and transpose.
  rcases (LinearMap.mem_range).1 hX with ⟨Y, rfl⟩
  have hX' : (Y * (M ^ D))ᵀ ∈ LinearMap.range (LinearMap.mulLeft ℂ ((Mᵀ) ^ D)) := by
    refine (LinearMap.mem_range).2 ?_
    refine ⟨Yᵀ, ?_⟩
    -- `(Mᵀ)^D * Yᵀ = (Y * (M^D))ᵀ`.
    simp [LinearMap.mulLeft_apply, Matrix.transpose_mul, Matrix.transpose_pow]
  have hMX' : (Mᵀ) * (Y * (M ^ D))ᵀ = 0 := by
    -- Transpose the equation `Y * (M^D) * M = 0`.
    have : ((Y * (M ^ D)) * M)ᵀ = 0 := by
      simpa using congrArg Matrix.transpose hXM
    simpa [Matrix.transpose_mul] using this
  have hXt : (Y * (M ^ D))ᵀ = 0 :=
    matrix_eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow (D := D)
      (M := Mᵀ) (X := (Y * (M ^ D))ᵀ) hX' hMX'
  have hX0 : Y * (M ^ D) = 0 := by
    simpa using congrArg Matrix.transpose hXt
  simp [hX0]

end WielandtRankOne

/-!
## Dimension-growth lemmas for the bi-rectangular span

The intended use is with `P = (B i₀)^D` and `Q = (B i₁)^D` coming from the
nilpotent-killing powers of word-eigenvalue products.

At this stage we record a basic (coarse) monotonicity statement for `finrank`.
-/

noncomputable section BiRectSpanDimGrowth

variable (B : MPSTensor d D) (i₀ i₁ : Fin d)

abbrev P0 : Matrix (Fin D) (Fin D) ℂ := (B i₀) ^ D
abbrev Q0 : Matrix (Fin D) (Fin D) ℂ := (B i₁) ^ D
abbrev W (n : ℕ) : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  biRectSpan (d := d) (D := D) (P0 (B := B) (i₀ := i₀)) (Q0 (B := B) (i₁ := i₁)) B n

/-- Left-multiplying a `biRectSpan` element by the distinguished Kraus operator `B i₀`
raises the word length by 1, when the left multiplier is the power `((B i₀)^D)`. -/
theorem mulLeft_mem_biRectSpan_pow_succ
    (n : ℕ) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ W (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) n) :
    (B i₀) * X ∈ W (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) (n + 1) := by
  classical
  rcases (mem_biRectSpan_iff (d := d) (D := D)
    (P0 (B := B) (i₀ := i₀)) (Q0 (B := B) (i₁ := i₁)) B).mp hX with ⟨Y, hY, hX⟩
  set M0 : Matrix (Fin D) (Fin D) ℂ := B i₀
  have hcomm : M0 * (M0 ^ D) = (M0 ^ D) * M0 := by
    calc
      M0 * (M0 ^ D) = M0 ^ (D + 1) := by simp [pow_succ']
      _ = (M0 ^ D) * M0 := by simp [pow_succ]
  have hM0 : M0 ∈ wordSpan B 1 := by
    simpa [M0, evalWord] using (evalWord_mem_wordSpan B ([i₀] : List (Fin d)))
  have hY' : M0 * Y ∈ wordSpan B (n + 1) := by
    have : M0 * Y ∈ (wordSpan B 1) * (wordSpan B n) :=
      Submodule.mul_mem_mul hM0 hY
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (wordSpan_mul_le B 1 n) this
  refine (mem_biRectSpan_iff (d := d) (D := D)
    (P0 (B := B) (i₀ := i₀)) (Q0 (B := B) (i₁ := i₁)) B).mpr ?_
  refine ⟨M0 * Y, hY', ?_⟩
  rw [← hX]
  calc
    (B i₀ ^ D) * (M0 * Y) * (B i₁ ^ D)
        = ((B i₀ ^ D) * M0) * Y * (B i₁ ^ D) := by simp [Matrix.mul_assoc]
    _ = (M0 * (B i₀ ^ D)) * Y * (B i₁ ^ D) := by
        simpa [M0] using congrArg (fun Z => Z * Y * (B i₁ ^ D)) hcomm.symm
    _ = M0 * ((B i₀ ^ D) * Y * (B i₁ ^ D)) := by simp [Matrix.mul_assoc]

/-- Linear map sending level `n` to level `n+1` by left multiplication with `B i₀`. -/
noncomputable def biRectSpanLeftStep (n : ℕ) :
    (W (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) n) →ₗ[ℂ]
      (W (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) (n + 1)) where
  toFun x := ⟨(B i₀) * x.1, mulLeft_mem_biRectSpan_pow_succ (d := d) (D := D) (B := B)
    (i₀ := i₀) (i₁ := i₁) n x.2⟩
  map_add' x y := by
    ext i j
    simp [Matrix.mul_add]
  map_smul' a x := by
    ext i j
    simp

/-- The left-step map is injective: multiplication by `B i₀` is injective on the range of
left multiplication by `((B i₀)^D)`. -/
theorem biRectSpanLeftStep_injective (n : ℕ) :
    Function.Injective
      (biRectSpanLeftStep (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) n) := by
  classical
  have hRange :
      ∀ {X : Matrix (Fin D) (Fin D) ℂ},
        X ∈ W (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) n →
          X ∈ LinearMap.range (LinearMap.mulLeft ℂ ((B i₀) ^ D)) := by
    intro X hX
    rcases (mem_biRectSpan_iff (d := d) (D := D)
      (P0 (B := B) (i₀ := i₀)) (Q0 (B := B) (i₁ := i₁)) B).mp hX with ⟨Z, _, hZ⟩
    refine (LinearMap.mem_range).2 ?_
    refine ⟨Z * Q0 (B := B) (i₁ := i₁), ?_⟩
    simpa [P0, Q0, LinearMap.mulLeft_apply, Matrix.mul_assoc] using hZ
  intro x y hxy
  have hmat : (B i₀) * x.1 = (B i₀) * y.1 := congrArg Subtype.val hxy
  have hz : (B i₀) * (x.1 - y.1) = 0 := by
    simpa [Matrix.mul_sub, sub_eq_zero] using hmat
  have hzRange : (x.1 - y.1) ∈ LinearMap.range (LinearMap.mulLeft ℂ ((B i₀) ^ D)) :=
    Submodule.sub_mem _ (hRange x.2) (hRange y.2)
  have hzero : x.1 - y.1 = 0 :=
    WielandtRankOne.matrix_eq_zero_of_mul_eq_zero_of_mem_range_mulLeft_pow (D := D)
      (M := B i₀) (X := x.1 - y.1) hzRange hz
  exact Subtype.ext <| by simpa [sub_eq_zero] using hzero

/-- Finrank is nondecreasing along the sequence `n ↦ biRectSpan ((B i₀)^D) ((B i₁)^D) B n`. -/
theorem biRectSpan_finrank_mono (n : ℕ) :
    Module.finrank ℂ (W (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) n) ≤
      Module.finrank ℂ (W (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) (n + 1)) := by
  classical
  -- Apply `LinearMap.finrank_le_finrank_of_injective` to the left-step map.
  exact LinearMap.finrank_le_finrank_of_injective
    (f := biRectSpanLeftStep (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) n)
    (biRectSpanLeftStep_injective (d := d) (D := D) (B := B) (i₀ := i₀) (i₁ := i₁) n)

end BiRectSpanDimGrowth

/-!
## Pigeonhole finrank stabilization

The monotone bounded sequence `finrank(biRectSpan P Q B n)` must have a consecutive
equality within the first `D^2+1` steps. This is a pure natural-number pigeonhole.
-/

/-- Generic pigeonhole: a monotone function `ℕ → ℕ` bounded by `B` has a consecutive
equality within the first `B+1` values. -/
private theorem exists_consecutive_eq_of_monotone_bounded
    {B : ℕ} (a : ℕ → ℕ)
    (ha_mono : ∀ n, a n ≤ a (n + 1))
    (ha_bound : ∀ n, a n ≤ B) :
    ∃ n ≤ B, a n = a (n + 1) := by
  by_contra h
  push Not at h
  have hstrict : ∀ n ≤ B, a n < a (n + 1) := by
    intro n hn
    exact lt_of_le_of_ne (ha_mono n) (h n hn)
  -- Telescoping: a k ≥ a 0 + k for k ≤ B + 1
  have hgrow : ∀ k, k ≤ B + 1 → a k ≥ a 0 + k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      have hk_le : k ≤ B := by omega
      have hih : a k ≥ a 0 + k := ih (by omega)
      have hstep : a k < a (k + 1) := hstrict k hk_le
      omega
  have : a (B + 1) ≥ a 0 + (B + 1) := hgrow (B + 1) le_rfl
  have : a (B + 1) ≤ B := ha_bound (B + 1)
  omega

/-- Finrank stabilization for biRectSpan: there exists `n ≤ D²` with
`finrank(biRectSpan P Q B n) = finrank(biRectSpan P Q B (n+1))`. -/
theorem exists_finrank_eq_succ_of_biRectSpan
    (P Q : Matrix (Fin D) (Fin D) ℂ) (B : MPSTensor d D) (i₀ i₁ : Fin d)
    (hP : P = (B i₀) ^ D) (hQ : Q = (B i₁) ^ D) :
    ∃ n ≤ D ^ 2,
      Module.finrank ℂ (biRectSpan (d := d) (D := D) P Q B n) =
      Module.finrank ℂ (biRectSpan (d := d) (D := D) P Q B (n + 1)) := by
  classical
  let a : ℕ → ℕ := fun n => Module.finrank ℂ (biRectSpan (d := d) (D := D) P Q B n)
  have ha_mono : ∀ n, a n ≤ a (n + 1) := by
    intro n
    change Module.finrank ℂ (biRectSpan (d := d) (D := D) P Q B n) ≤
      Module.finrank ℂ (biRectSpan (d := d) (D := D) P Q B (n + 1))
    subst hP; subst hQ
    exact biRectSpan_finrank_mono B i₀ i₁ n
  have ha_bound : ∀ n, a n ≤ D ^ 2 := by
    intro n
    exact biRectSpan_finrank_le (d := d) (D := D) P Q B n
  exact exists_consecutive_eq_of_monotone_bounded a ha_mono ha_bound

end MPSTensor
