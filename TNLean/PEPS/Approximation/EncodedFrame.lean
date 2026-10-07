/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding
import QICLean.Analysis.MatrixFramePerturbation

/-!
# Encoded frames

A *sheet* has one raw register `ℂ^q` at every site of a finite lattice `Λ`, and an owner for
every register. Its raw configurations are the functions `Λ → Fin q`, and a vector on the
sheet is a vector of `EuclideanSpace ℂ (Λ → Fin q)`. An operator `X` on the sites of a set
`D ⊆ Λ` acts on the sheet as `X ⊗ 1` (`siteLift`).

Around a center `c` in the plane and at scale `h > 0`, the inner and outer squares
`Q^±(c, h)` are the closed sup-norm balls of radii `h` and `2h`; their physical samples are the
sites whose positions lie in them. A `SquarePatch` records the nested-cylinder data of
Proposition 4.1 at such a center: nested square samples `D_j` between the two samples, unit
vectors `v_{jℓ}` on the sites of `D_j`, and mutually orthogonal cylinder projectors
`|v_{jℓ}⟩⟨v_{jℓ}|_{D_j} ⊗ 1`. Their sum is the projector `P_{c,h}`. With the product zero vector
`|0⟩^{⊗ D_j}` the *hole encoder* is
`K_{c,h} = ∑_{j,ℓ} |j, ℓ⟩ ⊗ (|0⟩^{⊗ D_j}⟨v_{jℓ}| ⊗ 1)`, and `K_{c,h}ᴴ K_{c,h} = P_{c,h}`.

An encoded frame is a raw ownership assignment together with a list of holes, each carrying
its square-patch data and the party that holds its tag, with pairwise disjoint outer samples.
The list order is the fixed ordering of the tags. Its encoding `K_F` is the product of the hole
encoders; its reference vector is `Ω_F = K_F Ω`. Disjoint holes commute, so
`K_Fᴴ K_F = ∏_a P_a` and `‖Ω_F‖ = ‖∏_a P_a Ω‖`, and if every hole projector has error at most
`ε` on a unit vector `Ω`, then `1 - rε ≤ ‖Ω_F‖ ≤ 1`.

## Main definitions

* `EncodedFrame.siteLift`: the operator `X_D ⊗ 1_{Λ ∖ D}`.
* `EncodedFrame.squareSample`: the physical sample of a closed square.
* `EncodedFrame.SquarePatch`: the nested-cylinder data of `eq:hole-projector`.
* `EncodedFrame.SquarePatch.proj`, `EncodedFrame.SquarePatch.encoder`: the projector
  `P_{c,h}` and the hole encoder `K_{c,h}`.
* `EncodedFrame.Frame`: an encoded frame (Definition 6.1).
* `EncodedFrame.TagSpace`, `EncodedFrame.rawProd`, `EncodedFrame.frameEncoder`: the tag
  registers of a list of holes in their fixed order, the raw part of the encoding on one tag
  configuration, and the encoding `K_F`.
* `EncodedFrame.Frame.refVec`: the reference vector `Ω_F = K_F Ω`.

## Main results

* `EncodedFrame.SquarePatch.encoder_conjTranspose_mul_self`,
  `EncodedFrame.SquarePatch.norm_encoder_le_one`: `K_{c,h}ᴴ K_{c,h} = P_{c,h}` and
  `‖K_{c,h}‖ ≤ 1` (`eq:encoder-contraction`).
* `EncodedFrame.frameEncoder_conjTranspose_mul_self`: `K_Fᴴ K_F = ∏_a P_a`.
* `EncodedFrame.Frame.norm_refVec_eq`, `EncodedFrame.Frame.one_sub_mul_le_norm_refVec`,
  `EncodedFrame.Frame.norm_refVec_le_one`: `eq:frame-norm`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §6.1, `05-frames.tex`, lines 11–97:
  sheets (lines 13–19), squares and the projector `eq:hole-projector` (lines 26–48), the hole
  encoder `eq:hole-encoder` and `eq:encoder-contraction` (lines 50–69), Definition 6.1
  `def:frame` (lines 71–82), and `eq:frame-norm` (lines 84–94). The cylinder data are those of
  Proposition 4.1 `prop:patch`, `03-patches.tex`, lines 24–49.

The pairwise disjointness of outer squares in Definition 6.1 is used only through the
disjointness of their physical samples, which it implies; `Frame` records the latter.
-/

open Matrix QuantumCircuit
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### Euclidean vectors and matrices -/

section Euclidean

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The action of a matrix on a Euclidean vector. -/
abbrev act (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) : EuclideanSpace ℂ m :=
  WithLp.toLp 2 (A *ᵥ ψ)

omit [Fintype m] in
theorem act_mul {l : Type*} [Fintype l] (A : Matrix m n ℂ) (B : Matrix n l ℂ)
    (ψ : EuclideanSpace ℂ l) : act (A * B) ψ = act A (act B ψ) := by
  simp [act, Matrix.mulVec_mulVec]

omit [Fintype m] in
theorem act_sub (A B : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    act (A - B) ψ = act A ψ - act B ψ := by
  simp [act, Matrix.sub_mulVec]

omit [Fintype m] in
theorem act_add (A B : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    act (A + B) ψ = act A ψ + act B ψ := by
  simp [act, Matrix.add_mulVec]

omit [Fintype m] in
theorem act_one [DecidableEq n] (ψ : EuclideanSpace ℂ n) : act (1 : Matrix n n ℂ) ψ = ψ := by
  simp [act]

theorem norm_act_le [DecidableEq n] (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) : ‖act A ψ‖ ≤ ‖A‖ * ‖ψ‖ :=
  A.l2_opNorm_mulVec ψ

theorem norm_act_le_of_norm_le_one [DecidableEq n] {A : Matrix m n ℂ} (hA : ‖A‖ ≤ 1)
    (ψ : EuclideanSpace ℂ n) : ‖act A ψ‖ ≤ ‖ψ‖ :=
  (norm_act_le A ψ).trans (mul_le_of_le_one_left (norm_nonneg _) hA)

/-- The squared norm of `A ψ` is the expectation of `Aᴴ A` in `ψ`. -/
theorem norm_act_sq (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    (‖act A ψ‖ ^ 2 : ℂ) = star (⇑ψ) ⬝ᵥ ((Aᴴ * A) *ᵥ ⇑ψ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (act A ψ)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct_comm]
  exact_mod_cast h.symm

/-- Two matrices with the same Gram matrix move every vector to the same length. -/
theorem norm_act_eq_of_gram_eq {m' : Type*} [Fintype m'] {A : Matrix m n ℂ}
    {B : Matrix m' n ℂ} (h : Aᴴ * A = Bᴴ * B) (ψ : EuclideanSpace ℂ n) :
    ‖act A ψ‖ = ‖act B ψ‖ := by
  have h2 : (‖act A ψ‖ ^ 2 : ℂ) = (‖act B ψ‖ ^ 2 : ℂ) := by
    rw [norm_act_sq, norm_act_sq, h]
  have h3 : ‖act A ψ‖ ^ 2 = ‖act B ψ‖ ^ 2 := by exact_mod_cast h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-- A matrix whose Gram matrix has operator norm at most one is a contraction. -/
theorem norm_le_one_of_gram [DecidableEq n] {A : Matrix m n ℂ} (h : ‖Aᴴ * A‖ ≤ 1) : ‖A‖ ≤ 1 := by
  rw [l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg A]

/-- The identity matrix has operator norm at most one. -/
theorem norm_one_le [DecidableEq n] : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp

/-- A star projection matrix has operator norm at most one. -/
theorem norm_le_one_of_isStarProjection [DecidableEq n] {P : Matrix n n ℂ}
    (hP : IsStarProjection P) : ‖P‖ ≤ 1 := by
  apply norm_le_one_of_gram
  rw [← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
  by_cases h : ‖P‖ = 0
  · rw [h]; exact zero_le_one
  · have h2 := l2_opNorm_conjTranspose_mul_self P
    rw [← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq] at h2
    have : ‖P‖ = 1 := by
      have hpos : 0 < ‖P‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
      field_simp at h2
      nlinarith
    rw [this]

/-- The product of a list of contractions is a contraction. -/
theorem norm_list_prod_le_one [DecidableEq n] :
    (l : List (Matrix n n ℂ)) → (∀ A ∈ l, ‖A‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simpa using norm_one_le
  | A :: l, h => by
    rw [List.prod_cons]
    refine (l2_opNorm_mul _ _).trans ?_
    have h1 := h A List.mem_cons_self
    have h2 := norm_list_prod_le_one l fun B hB => h B (List.mem_cons_of_mem _ hB)
    nlinarith [norm_nonneg A, norm_nonneg l.prod]

/-- **Telescoping on a vector.** For contractions `A₁, …, A_s`, the defect of their product on
`ψ` is at most the sum of their individual defects on `ψ`.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 237–248. -/
theorem norm_act_list_prod_sub_le [DecidableEq n] :
    (l : List (Matrix n n ℂ)) → (∀ A ∈ l, ‖A‖ ≤ 1) → (ψ : EuclideanSpace ℂ n) →
      ‖act l.prod ψ - ψ‖ ≤ (l.map fun A => ‖act A ψ - ψ‖).sum
  | [], _, ψ => by simp [act_one]
  | A :: l, h, ψ => by
    rw [List.prod_cons, List.map_cons, List.sum_cons, act_mul]
    have hA := h A List.mem_cons_self
    have ih := norm_act_list_prod_sub_le l (fun B hB => h B (List.mem_cons_of_mem _ hB)) ψ
    calc ‖act A (act l.prod ψ) - ψ‖
        = ‖act A (act l.prod ψ - ψ) + (act A ψ - ψ)‖ := by
          rw [act_sub_right]; congr 1; abel
      _ ≤ ‖act A (act l.prod ψ - ψ)‖ + ‖act A ψ - ψ‖ := norm_add_le _ _
      _ ≤ ‖act l.prod ψ - ψ‖ + ‖act A ψ - ψ‖ :=
          add_le_add (norm_act_le_of_norm_le_one hA _) le_rfl
      _ ≤ _ := by linarith
where
  act_sub_right (A : Matrix n n ℂ) (x y : EuclideanSpace ℂ n) :
      act A (x - y) = act A x - act A y := by
    simp [act, Matrix.mulVec_sub]

end Euclidean

/-! ### Operators on a set of sites -/

/-- The operator `X_D ⊗ 1_{Λ ∖ D}` on the raw registers of a sheet, for an operator `X` on the
sites of `D`. -/
def siteLift (D : Finset ι) (X : Matrix (D → Fin q) (D → Fin q) ℂ) :
    Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  embedOp (Subtype.val : D → ι) X

theorem siteLift_mul (D : Finset ι) (X Y : Matrix (D → Fin q) (D → Fin q) ℂ) :
    siteLift D X * siteLift D Y = siteLift D (X * Y) :=
  embedOp_mul Subtype.val_injective X Y

theorem siteLift_conjTranspose (D : Finset ι) (X : Matrix (D → Fin q) (D → Fin q) ℂ) :
    (siteLift D X)ᴴ = siteLift D Xᴴ :=
  embedOp_conjTranspose _ X

/-- An operator lifted from `D` acts on the sites of `D`. -/
theorem siteLift_mem_supportedOperators (D : Finset ι)
    (X : Matrix (D → Fin q) (D → Fin q) ℂ) :
    siteLift D X ∈ supportedOperators q (D : Set ι) := by
  have h := embedOp_mem_supportedOperators (d := q) (Subtype.val_injective (p := (· ∈ D))) X
  rwa [Subtype.range_coe_subtype] at h

/-- The rank-one projector `|v⟩⟨v|`. -/
def rankOne {α : Type*} [Fintype α] (v : EuclideanSpace ℂ α) : Matrix α α ℂ :=
  vecMulVec (⇑v) (star ⇑v)

/-- The product zero vector `|0⟩^{⊗ D}` on the sites of `D`. -/
def zeroVec [NeZero q] (D : Finset ι) : (D → Fin q) → ℂ :=
  Pi.single 0 1

omit [Fintype ι] in
theorem star_zeroVec_dotProduct_zeroVec [NeZero q] (D : Finset ι) :
    star (zeroVec (q := q) D) ⬝ᵥ zeroVec D = 1 := by
  classical
  simp [zeroVec, dotProduct, Pi.single_apply]

theorem vecMulVec_mul_vecMulVec {α β γ : Type*} [Fintype β] (a : α → ℂ) (b c : β → ℂ)
    (d : γ → ℂ) : vecMulVec a b * vecMulVec c d = (b ⬝ᵥ c) • vecMulVec a d := by
  ext i k
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, dotProduct, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem star_dotProduct_self_of_norm_eq_one {α : Type*} [Fintype α] {v : EuclideanSpace ℂ α}
    (hv : ‖v‖ = 1) : star (⇑v) ⬝ᵥ ⇑v = 1 := by
  have h : (inner ℂ v v : ℂ) = (‖v‖ ^ 2 : ℂ) := inner_self_eq_norm_sq_to_K v
  rw [EuclideanSpace.inner_eq_star_dotProduct, hv] at h
  rw [dotProduct_comm]
  simpa using h

theorem rankOne_conjTranspose {α : Type*} [Fintype α] (v : EuclideanSpace ℂ α) :
    (rankOne v)ᴴ = rankOne v := by
  simp [rankOne, conjTranspose_vecMulVec]

theorem rankOne_mul_self {α : Type*} [Fintype α] {v : EuclideanSpace ℂ α} (hv : ‖v‖ = 1) :
    rankOne v * rankOne v = rankOne v := by
  rw [rankOne, vecMulVec_mul_vecMulVec, star_dotProduct_self_of_norm_eq_one hv, one_smul]

/-! ### Squares and their samples -/

/-- The physical sample `Q ∩ Λ` of the closed sup-norm square of radius `r` around `c`, for
site positions `pos : Λ → ℝ²`. -/
def squareSample (pos : ι → ℝ × ℝ) (c : ℝ × ℝ) (r : ℝ) : Finset ι :=
  Finset.univ.filter fun x => dist (pos x) c ≤ r

omit [DecidableEq ι] in
theorem squareSample_mono (pos : ι → ℝ × ℝ) (c : ℝ × ℝ) {r r' : ℝ} (h : r ≤ r') :
    squareSample pos c r ⊆ squareSample pos c r' := fun _ hx => by
  simp only [squareSample, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.trans h

/-- Nested-cylinder data around a center: the projector of `eq:hole-projector`.

There are radii `h ≤ r_1 ≤ ⋯ ≤ r_n ≤ 2h`, square samples `D_j = Q(c, r_j) ∩ Λ`, unit vectors
`v_{jℓ}` on the sites of `D_j` for `ℓ < d_j`, and the cylinder projectors
`|v_{jℓ}⟩⟨v_{jℓ}|_{D_j} ⊗ 1` have mutually orthogonal ranges. The projector is their sum.
The polynomial bound on `∑_j d_j` and the error `‖(1 - P)Ω‖ ≤ ε` are not fields: they are
hypotheses of the statements that use them.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 26–48 (`eq:hole-projector`), with the
cylinder data of Proposition 4.1 `prop:patch`, `03-patches.tex`, lines 24–49. -/
structure SquarePatch (pos : ι → ℝ × ℝ) (q : ℕ) where
  /-- The center `c`. -/
  center : ℝ × ℝ
  /-- The scale `h` (the inner radius). -/
  scale : ℝ
  scale_pos : 0 < scale
  /-- The number of radii. -/
  n : ℕ
  /-- The radii `r_j`. -/
  radius : Fin n → ℝ
  radius_mono : Monotone radius
  scale_le_radius : ∀ j, scale ≤ radius j
  radius_le : ∀ j, radius j ≤ 2 * scale
  /-- The number `d_j` of vectors at radius `r_j`. -/
  dim : Fin n → ℕ
  /-- The unit vectors `v_{jℓ}` on the sites of `D_j`. -/
  vec : (j : Fin n) → Fin (dim j) →
    EuclideanSpace ℂ (squareSample pos center (radius j) → Fin q)
  norm_vec : ∀ j ℓ, ‖vec j ℓ‖ = 1
  /-- The cylinder projectors have mutually orthogonal ranges. -/
  orthogonal : ∀ s s' : (j : Fin n) × Fin (dim j), s ≠ s' →
    siteLift (squareSample pos center (radius s.1)) (rankOne (vec s.1 s.2)) *
      siteLift (squareSample pos center (radius s'.1)) (rankOne (vec s'.1 s'.2)) = 0

namespace SquarePatch

variable {pos : ι → ℝ × ℝ} (p : SquarePatch pos q)

/-- The inner sample `Q^-(c, h) ∩ Λ`. -/
def inner : Finset ι := squareSample pos p.center p.scale

/-- The outer sample `Q^+(c, h) ∩ Λ`, the physical outer footprint. -/
def outer : Finset ι := squareSample pos p.center (2 * p.scale)

/-- The nested square sample `D_j`. -/
abbrev sample (j : Fin p.n) : Finset ι := squareSample pos p.center (p.radius j)

theorem inner_subset_sample (j : Fin p.n) : p.inner ⊆ p.sample j :=
  squareSample_mono pos p.center (p.scale_le_radius j)

theorem sample_subset_outer (j : Fin p.n) : p.sample j ⊆ p.outer :=
  squareSample_mono pos p.center (p.radius_le j)

theorem inner_subset_outer : p.inner ⊆ p.outer :=
  squareSample_mono pos p.center (by linarith [p.scale_pos])

/-- The tag register basis: the pairs `(j, ℓ)`. -/
abbrev Tag : Type := (j : Fin p.n) × Fin (p.dim j)

/-- The cylinder projector `|v_{jℓ}⟩⟨v_{jℓ}|_{D_j} ⊗ 1`. -/
def cyl (s : p.Tag) : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  siteLift (p.sample s.1) (rankOne (p.vec s.1 s.2))

/-- The projector `P_{c,h} = ∑_{j,ℓ} |v_{jℓ}⟩⟨v_{jℓ}|_{D_j} ⊗ 1`. -/
def proj : Matrix (ι → Fin q) (ι → Fin q) ℂ := ∑ s, p.cyl s

/-- The raw part `|0⟩^{⊗ D_j}⟨v_{jℓ}|_{D_j} ⊗ 1` of the hole encoder at the tag `(j, ℓ)`. -/
def branch [NeZero q] (s : p.Tag) : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  siteLift (p.sample s.1) (vecMulVec (zeroVec (p.sample s.1)) (star ⇑(p.vec s.1 s.2)))

theorem cyl_conjTranspose (s : p.Tag) : (p.cyl s)ᴴ = p.cyl s := by
  rw [cyl, siteLift_conjTranspose, rankOne_conjTranspose]

theorem cyl_mul_self (s : p.Tag) : p.cyl s * p.cyl s = p.cyl s := by
  rw [cyl, siteLift_mul, rankOne_mul_self (p.norm_vec _ _)]

theorem cyl_mul_cyl_of_ne {s s' : p.Tag} (h : s ≠ s') : p.cyl s * p.cyl s' = 0 :=
  p.orthogonal s s' h

/-- `P_{c,h}` is an orthogonal projection. -/
theorem proj_isStarProjection : IsStarProjection p.proj := by
  classical
  refine ⟨?_, ?_⟩
  · change p.proj * p.proj = p.proj
    rw [proj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s (fun s' _ h => p.cyl_mul_cyl_of_ne (Ne.symm h))
      (fun h => absurd (Finset.mem_univ s) h), cyl_mul_self]
  · change star p.proj = p.proj
    rw [proj, star_sum]
    exact Finset.sum_congr rfl fun s _ => p.cyl_conjTranspose s

theorem norm_proj_le_one : ‖p.proj‖ ≤ 1 :=
  norm_le_one_of_isStarProjection p.proj_isStarProjection

theorem branch_conjTranspose_mul_self [NeZero q] (s : p.Tag) :
    (p.branch s)ᴴ * p.branch s = p.cyl s := by
  rw [branch, siteLift_conjTranspose, siteLift_mul, conjTranspose_vecMulVec,
    vecMulVec_mul_vecMulVec, star_star, star_zeroVec_dotProduct_zeroVec, one_smul, cyl,
    rankOne]

theorem cyl_mem_supportedOperators (s : p.Tag) :
    p.cyl s ∈ supportedOperators q (p.outer : Set ι) :=
  supportedOperators_mono (Finset.coe_subset.mpr (p.sample_subset_outer s.1))
    (siteLift_mem_supportedOperators _ _)

theorem branch_mem_supportedOperators [NeZero q] (s : p.Tag) :
    p.branch s ∈ supportedOperators q (p.outer : Set ι) :=
  supportedOperators_mono (Finset.coe_subset.mpr (p.sample_subset_outer s.1))
    (siteLift_mem_supportedOperators _ _)

theorem proj_mem_supportedOperators : p.proj ∈ supportedOperators q (p.outer : Set ι) :=
  Submodule.sum_mem _ fun s _ => p.cyl_mem_supportedOperators s

end SquarePatch

/-! ### Stacking tagged operators -/

section Stack

variable {T m n : Type*} [Fintype T] [Fintype m] [Fintype n]

/-- The tagged stack `∑_t |t⟩ ⊗ R_t` of a family of operators. -/
def stack (R : T → Matrix m n ℂ) : Matrix (T × m) n ℂ := Matrix.of fun r τ => R r.1 r.2 τ

omit [Fintype T] [Fintype m] [Fintype n] in
@[simp]
theorem stack_apply (R : T → Matrix m n ℂ) (t : T) (σ : m) (τ : n) :
    stack R (t, σ) τ = R t σ τ := rfl

omit [Fintype n] in
theorem stack_conjTranspose_mul_stack {n' : Type*} [Fintype n'] (R : T → Matrix m n ℂ)
    (S : T → Matrix m n' ℂ) : (stack R)ᴴ * stack S = ∑ t, (R t)ᴴ * S t := by
  ext τ τ'
  simp only [mul_apply, conjTranspose_apply, stack_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]

omit [Fintype T] [Fintype m] in
theorem stack_mul {l : Type*} [Fintype l] (R : T → Matrix m n ℂ) (A : Matrix n l ℂ) :
    stack R * A = stack fun t => R t * A := by
  ext ⟨t, σ⟩ τ
  simp [mul_apply]

end Stack

namespace SquarePatch

variable {pos : ι → ℝ × ℝ} (p : SquarePatch pos q)

/-- The hole encoder `K_{c,h} = ∑_{j,ℓ} |j, ℓ⟩ ⊗ (|0⟩^{⊗ D_j}⟨v_{jℓ}|_{D_j} ⊗ 1)`
(`eq:hole-encoder`). It keeps a raw register at every site. -/
def encoder [NeZero q] : Matrix (p.Tag × (ι → Fin q)) (ι → Fin q) ℂ := stack p.branch

/-- **`eq:encoder-contraction`.** `K_{c,h}ᴴ K_{c,h} = P_{c,h}`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 61–63. -/
theorem encoder_conjTranspose_mul_self [NeZero q] : p.encoderᴴ * p.encoder = p.proj := by
  rw [encoder, stack_conjTranspose_mul_stack, proj]
  exact Finset.sum_congr rfl fun s _ => p.branch_conjTranspose_mul_self s

/-- **`eq:encoder-contraction`.** `‖K_{c,h}‖ ≤ 1`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 61–63. -/
theorem norm_encoder_le_one [NeZero q] : ‖p.encoder‖ ≤ 1 :=
  norm_le_one_of_gram (by rw [encoder_conjTranspose_mul_self]; exact p.norm_proj_le_one)

end SquarePatch

/-! ### Tag registers and encodings of a list of holes -/

variable {pos : ι → ℝ × ℝ}

/-- The tag registers of a list of holes, in the order of the list: the fixed ordering of the
appended tags in Definition 6.1. -/
def TagSpace : List (SquarePatch pos q) → Type
  | [] => Unit
  | p :: l => p.Tag × TagSpace l

instance instFintypeTagSpace : (l : List (SquarePatch pos q)) → Fintype (TagSpace l)
  | [] => inferInstanceAs (Fintype Unit)
  | p :: l =>
    haveI := instFintypeTagSpace l
    inferInstanceAs (Fintype (p.Tag × TagSpace l))

instance instDecidableEqTagSpace : (l : List (SquarePatch pos q)) → DecidableEq (TagSpace l)
  | [] => inferInstanceAs (DecidableEq Unit)
  | p :: l =>
    haveI := instDecidableEqTagSpace l
    inferInstanceAs (DecidableEq (p.Tag × TagSpace l))

/-- Tag registers of a concatenation are the pairs of tag registers of the two parts. -/
def tagAppendEquiv : (l₁ l₂ : List (SquarePatch pos q)) →
    TagSpace (l₁ ++ l₂) ≃ TagSpace l₁ × TagSpace l₂
  | [], l₂ => (Equiv.punitProd (TagSpace l₂)).symm
  | p :: l₁, l₂ =>
    ((Equiv.refl p.Tag).prodCongr (tagAppendEquiv l₁ l₂)).trans
      (Equiv.prodAssoc p.Tag (TagSpace l₁) (TagSpace l₂)).symm

/-- The raw part of the encoding of a list of holes on one tag configuration: the ordered
product of the raw parts `|0⟩^{⊗ D_j}⟨v_{jℓ}|_{D_j} ⊗ 1` of the hole encoders. -/
def rawProd [NeZero q] : (l : List (SquarePatch pos q)) → TagSpace l →
    Matrix (ι → Fin q) (ι → Fin q) ℂ
  | [], _ => 1
  | p :: l, t => p.branch t.1 * rawProd l t.2

/-- The encoding `K_F` of a list of holes: the product of the hole encoders, with the tags
appended in the order of the list. -/
def frameEncoder [NeZero q] (l : List (SquarePatch pos q)) :
    Matrix (TagSpace l × (ι → Fin q)) (ι → Fin q) ℂ :=
  stack (rawProd l)

/-- The product `∏_a P_a` of the hole projectors, in the order of the list. -/
def projProd (l : List (SquarePatch pos q)) : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  (l.map SquarePatch.proj).prod

/-- The union of the physical outer footprints of a list of holes. -/
def footprint (l : List (SquarePatch pos q)) : Set ι := {x | ∃ p ∈ l, x ∈ p.outer}

/-- The outer samples of distinct holes of the list are disjoint. -/
def PairwiseDisjointOuter (l : List (SquarePatch pos q)) : Prop :=
  l.Pairwise fun a b => Disjoint a.outer b.outer

theorem footprint_nil : footprint ([] : List (SquarePatch pos q)) = ∅ := by
  simp [footprint]

theorem footprint_cons (p : SquarePatch pos q) (l : List (SquarePatch pos q)) :
    footprint (p :: l) = (p.outer : Set ι) ∪ footprint l := by
  ext x; simp [footprint]

theorem footprint_append (l₁ l₂ : List (SquarePatch pos q)) :
    footprint (l₁ ++ l₂) = footprint l₁ ∪ footprint l₂ := by
  ext x; simp only [footprint, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, hx⟩
    · exact Or.inl ⟨p, hp, hx⟩
    · exact Or.inr ⟨p, hp, hx⟩
  · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
    · exact ⟨p, Or.inl hp, hx⟩
    · exact ⟨p, Or.inr hp, hx⟩

theorem subset_footprint {p : SquarePatch pos q} {l : List (SquarePatch pos q)} (hp : p ∈ l) :
    (p.outer : Set ι) ⊆ footprint l := fun _ hx => ⟨p, hp, hx⟩

theorem disjoint_outer_footprint {p : SquarePatch pos q} {l : List (SquarePatch pos q)}
    (h : PairwiseDisjointOuter (p :: l)) : Disjoint (p.outer : Set ι) (footprint l) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨b, hb, hxb⟩
  exact Finset.disjoint_left.mp (List.rel_of_pairwise_cons h hb) hx hxb

theorem PairwiseDisjointOuter.of_cons {p : SquarePatch pos q} {l : List (SquarePatch pos q)}
    (h : PairwiseDisjointOuter (p :: l)) : PairwiseDisjointOuter l :=
  List.Pairwise.of_cons h

theorem rawProd_mem_supportedOperators [NeZero q] :
    (l : List (SquarePatch pos q)) → (t : TagSpace l) →
      rawProd l t ∈ supportedOperators q (footprint l)
  | [], _ => one_mem_supportedOperators _
  | p :: l, t => by
    rw [footprint_cons]
    exact mul_mem_supportedOperators
      (supportedOperators_mono Set.subset_union_left (p.branch_mem_supportedOperators t.1))
      (supportedOperators_mono Set.subset_union_right (rawProd_mem_supportedOperators l t.2))

theorem rawProd_conjTranspose_mem_supportedOperators [NeZero q] (l : List (SquarePatch pos q))
    (t : TagSpace l) : (rawProd l t)ᴴ ∈ supportedOperators q (footprint l) :=
  star_mem_supportedOperators (rawProd_mem_supportedOperators l t)

theorem projProd_mem_supportedOperators :
    (l : List (SquarePatch pos q)) → projProd l ∈ supportedOperators q (footprint l)
  | [] => by
    rw [footprint_nil]
    simpa [projProd] using one_mem_supportedOperators (d := q) (∅ : Set ι)
  | p :: l => by
    rw [projProd, List.map_cons, List.prod_cons, footprint_cons]
    exact mul_mem_supportedOperators
      (supportedOperators_mono Set.subset_union_left p.proj_mem_supportedOperators)
      (supportedOperators_mono Set.subset_union_right (projProd_mem_supportedOperators l))

/-- Encodings of a concatenation factor through the encodings of the two parts. -/
theorem rawProd_append [NeZero q] :
    (l₁ l₂ : List (SquarePatch pos q)) → (t : TagSpace (l₁ ++ l₂)) →
      rawProd (l₁ ++ l₂) t =
        rawProd l₁ (tagAppendEquiv l₁ l₂ t).1 * rawProd l₂ (tagAppendEquiv l₁ l₂ t).2
  | [], l₂, t => by
    change rawProd l₂ t = 1 * rawProd l₂ t
    exact (one_mul _).symm
  | p :: l₁, l₂, t => by
    change p.branch t.1 * rawProd (l₁ ++ l₂) t.2 = _
    rw [rawProd_append l₁ l₂ t.2, ← mul_assoc]
    rfl

theorem projProd_append (l₁ l₂ : List (SquarePatch pos q)) :
    projProd (l₁ ++ l₂) = projProd l₁ * projProd l₂ := by
  simp [projProd, List.map_append, List.prod_append]

/-- **Commuting disjoint encodings.** Encodings of holes with disjoint outer footprints
commute: the raw parts of the encodings of two families with disjoint footprints commute on
every pair of tag configurations.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 84–85. -/
theorem rawProd_commute [NeZero q] {l₁ l₂ : List (SquarePatch pos q)}
    (h : Disjoint (footprint l₁) (footprint l₂)) (t₁ : TagSpace l₁) (t₂ : TagSpace l₂) :
    Commute (rawProd l₁ t₁) (rawProd l₂ t₂) :=
  commute_of_mem_supportedOperators h (rawProd_mem_supportedOperators l₁ t₁)
    (rawProd_mem_supportedOperators l₂ t₂)

/-- The hole projectors of a list with disjoint outer footprints have a product that is an
orthogonal projection. -/
theorem projProd_isStarProjection :
    (l : List (SquarePatch pos q)) → PairwiseDisjointOuter l → IsStarProjection (projProd l)
  | [], _ => by simp [projProd]
  | p :: l, h => by
    rw [projProd, List.map_cons, List.prod_cons]
    exact p.proj_isStarProjection.mul (projProd_isStarProjection l h.of_cons)
      (commute_of_mem_supportedOperators (disjoint_outer_footprint h)
        p.proj_mem_supportedOperators (projProd_mem_supportedOperators l))

theorem norm_projProd_le_one (l : List (SquarePatch pos q)) : ‖projProd l‖ ≤ 1 :=
  norm_list_prod_le_one _ fun A hA => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hA
    exact p.norm_proj_le_one

/-- **Frame Gram identity.** For holes with pairwise disjoint outer footprints,
`K_Fᴴ K_F = ∑_t (R_t)ᴴ R_t = ∏_a P_a`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 84–90. -/
theorem sum_rawProd_conjTranspose_mul_self [NeZero q] :
    (l : List (SquarePatch pos q)) → PairwiseDisjointOuter l →
      ∑ t, (rawProd l t)ᴴ * rawProd l t = projProd l
  | [], _ => by
    change ∑ _t : Unit, (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ)ᴴ * 1 = 1
    simp
  | p :: l, h => by
    have ih := sum_rawProd_conjTranspose_mul_self l h.of_cons
    have hc (t : TagSpace l) : Commute p.proj (rawProd l t)ᴴ :=
      commute_of_mem_supportedOperators (disjoint_outer_footprint h)
        p.proj_mem_supportedOperators (rawProd_conjTranspose_mem_supportedOperators l t)
    change ∑ t : p.Tag × TagSpace l, (p.branch t.1 * rawProd l t.2)ᴴ *
      (p.branch t.1 * rawProd l t.2) = _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ t : TagSpace l, ∑ s : p.Tag, (p.branch s * rawProd l t)ᴴ * (p.branch s * rawProd l t)
        = ∑ t : TagSpace l, (rawProd l t)ᴴ * p.proj * rawProd l t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [conjTranspose_mul, SquarePatch.proj, ← p.branch_conjTranspose_mul_self,
            Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = ∑ t : TagSpace l, p.proj * ((rawProd l t)ᴴ * rawProd l t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← (hc t).eq, mul_assoc]
      _ = projProd (p :: l) := by
          rw [← Finset.mul_sum, ih]
          rfl

/-- **Frame Gram identity.** `K_Fᴴ K_F = ∏_a P_a`. -/
theorem frameEncoder_conjTranspose_mul_self [NeZero q] {l : List (SquarePatch pos q)}
    (h : PairwiseDisjointOuter l) : (frameEncoder l)ᴴ * frameEncoder l = projProd l := by
  rw [frameEncoder, stack_conjTranspose_mul_stack, sum_rawProd_conjTranspose_mul_self l h]

/-- The encoding of a list of holes with disjoint outer footprints is a contraction. -/
theorem norm_frameEncoder_le_one [NeZero q] {l : List (SquarePatch pos q)}
    (h : PairwiseDisjointOuter l) : ‖frameEncoder l‖ ≤ 1 :=
  norm_le_one_of_gram (by rw [frameEncoder_conjTranspose_mul_self h]; exact norm_projProd_le_one l)

/-- `‖K_F ψ‖ = ‖∏_a P_a ψ‖` for every raw vector `ψ`. -/
theorem norm_act_frameEncoder [NeZero q] {l : List (SquarePatch pos q)}
    (h : PairwiseDisjointOuter l) (ψ : EuclideanSpace ℂ (ι → Fin q)) :
    ‖act (frameEncoder l) ψ‖ = ‖act (projProd l) ψ‖ := by
  refine norm_act_eq_of_gram_eq ?_ ψ
  have hP := projProd_isStarProjection l h
  rw [frameEncoder_conjTranspose_mul_self h, ← Matrix.star_eq_conjTranspose,
    hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]

/-- If every hole projector has error at most `ε` on `ψ`, the product of the `r` hole
projectors has error at most `rε` on `ψ`. -/
theorem norm_act_projProd_sub_le {l : List (SquarePatch pos q)} {ε : ℝ}
    {ψ : EuclideanSpace ℂ (ι → Fin q)} (hε : ∀ p ∈ l, ‖act p.proj ψ - ψ‖ ≤ ε) :
    ‖act (projProd l) ψ - ψ‖ ≤ l.length * ε := by
  refine (norm_act_list_prod_sub_le _ (fun A hA => ?_) ψ).trans ?_
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hA
    exact p.norm_proj_le_one
  · rw [List.map_map]
    refine (List.sum_le_length_nsmul _ ε fun x hx => ?_).trans_eq ?_
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hε p hp
    · simp

/-! ### Encoded frames -/

/-- A hole of an encoded frame: its square-patch data and the party holding its tag. -/
structure Hole (pos : ι → ℝ × ℝ) (q : ℕ) (Party : Type*) where
  /-- The center, the scale, and the nested-cylinder data of the hole. -/
  patch : SquarePatch pos q
  /-- The party holding the tag register of the hole. -/
  tagOwner : Party

/-- **Definition 6.1 (Encoded frame).** A raw ownership assignment on one sheet and a list of
holes, each with a specified party holding its tag, whose outer footprints are pairwise
disjoint. The order of the list is the fixed ordering of the appended tags.

Polynomial-PEPS manuscript, Definition 6.1 `def:frame`, `05-frames.tex`, lines 71–82. -/
structure Frame (pos : ι → ℝ × ℝ) (q : ℕ) (Party : Type*) where
  /-- The raw ownership assignment of the sheet. -/
  owner : ι → Party
  /-- The holes, in the fixed order of their tags. -/
  holes : List (Hole pos q Party)
  /-- The outer footprints of distinct holes are disjoint. -/
  disjoint : PairwiseDisjointOuter (holes.map Hole.patch)

namespace Frame

variable {Party : Type*} (F : Frame pos q Party)

/-- The square-patch data of the holes of a frame. -/
def patches : List (SquarePatch pos q) := F.holes.map Hole.patch

/-- The encoding `K_F` of a frame. -/
def encoder [NeZero q] : Matrix (TagSpace F.patches × (ι → Fin q)) (ι → Fin q) ℂ :=
  frameEncoder F.patches

/-- The reference vector `Ω_F = K_F Ω` (`eq:frame-vector`). -/
def refVec [NeZero q] (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    EuclideanSpace ℂ (TagSpace F.patches × (ι → Fin q)) :=
  act F.encoder Ω

/-- A raw sheet: the frame without holes, for an ownership assignment. An ownership guide in
the plane gives such an assignment by sampling its labels at the site positions. -/
def raw (owner : ι → Party) : Frame pos q Party where
  owner := owner
  holes := []
  disjoint := List.Pairwise.nil

theorem encoder_conjTranspose_mul_self [NeZero q] :
    F.encoderᴴ * F.encoder = projProd F.patches :=
  frameEncoder_conjTranspose_mul_self F.disjoint

/-- The encoding of a frame is a contraction. -/
theorem norm_encoder_le_one [NeZero q] : ‖F.encoder‖ ≤ 1 :=
  norm_frameEncoder_le_one F.disjoint

/-- **`eq:frame-norm`, identity.** `‖Ω_F‖ = ‖∏_a P_a Ω‖`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 86–90. -/
theorem norm_refVec_eq [NeZero q] (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ‖F.refVec Ω‖ = ‖act (projProd F.patches) Ω‖ :=
  norm_act_frameEncoder F.disjoint Ω

/-- **`eq:frame-norm`, upper bound.** `‖Ω_F‖ ≤ ‖Ω‖`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 86–92. -/
theorem norm_refVec_le [NeZero q] (Ω : EuclideanSpace ℂ (ι → Fin q)) : ‖F.refVec Ω‖ ≤ ‖Ω‖ :=
  norm_act_le_of_norm_le_one F.norm_encoder_le_one Ω

/-- **`eq:frame-norm`, lower bound.** If `‖Ω‖ = 1` and every hole projector satisfies
`‖(1 - P_a) Ω‖ ≤ ε`, then the reference vector of a frame with `r` holes satisfies
`1 - rε ≤ ‖Ω_F‖ ≤ 1`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 86–94. -/
theorem one_sub_mul_le_norm_refVec [NeZero q] {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ = 1) {ε : ℝ} (hε : ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ε) :
    1 - F.holes.length * ε ≤ ‖F.refVec Ω‖ ∧ ‖F.refVec Ω‖ ≤ 1 := by
  refine ⟨?_, hΩ ▸ F.norm_refVec_le Ω⟩
  have h := norm_act_projProd_sub_le (l := F.patches) (ψ := Ω) (ε := ε) fun p hp => by
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
    exact hε h hh
  rw [F.norm_refVec_eq]
  have h2 := norm_sub_norm_le Ω (act (projProd F.patches) Ω)
  rw [norm_sub_rev] at h2
  have hlen : F.patches.length = F.holes.length := List.length_map _
  rw [hlen] at h
  linarith

end Frame

end TNLean.PEPS.EncodedFrame
