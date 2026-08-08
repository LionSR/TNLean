/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import TNLean.Channel.Wigner.Upstream.TransitionProbability

/-!
# Projective Wigner rigidity: orthogonal frames and frame reduction

This module is adapted from
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean` in
`zblore/csd-lean4` at commit
`55ac6758832291c8b0fb94d78e10dc47b1cb8a06`, under the Apache License 2.0.
The upstream single source file was split mechanically at semantic section
boundaries, preserving declaration order, to satisfy TNLean's module-size policy.
Ordinary imports and public declarations replace the upstream module-system commands.
Further adaptations are limited to formatting, explicit qualification, documentation, and
style-linter compliance. Declaration order, theorem statements, and proof structure are
preserved.
-/

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Diagonal value of the projective transition probability -/

/-- The diagonal value of the projective transition probability is `1`: any
projective point coincides with itself. Reduces to `transProbVec_self` on the
(nonzero) canonical representative via `transProb_mk`. -/
lemma transProb_self (p : ℙ ℂ E) : transProb p p = 1 := by
  conv_lhs => rw [← p.mk_rep]
  rw [transProb_mk p.rep_nonzero p.rep_nonzero, transProbVec_self p.rep_nonzero]

/-! ## The transition-probability-preserving predicate -/

/-- A self-map of `ℙ ℂ E` is **transition-probability preserving** when it
preserves `transProb` on every pair of projective points. Both unitary actions
and coordinatewise conjugation satisfy this condition. Wigner rigidity states
that, in finite complex dimension, every such map belongs to one of these two
branches. -/
def TransProbPreserving (f : ℙ ℂ E → ℙ ℂ E) : Prop :=
  ∀ p q, transProb (f p) (f q) = transProb p q

/-! ## Realisability inclusion: `U(N) → TransProbPreserving` -/

variable {N : ℕ}

/-- A transition-probability-preserving self-map of `ℂℙ^{N-1}` is injective: if
`f p = f q` then `transProb p q = transProb (f p) (f q) = transProb (f p) (f p)
= 1`, so `p = q` by `transProb_eq_one_iff`. (The coincidence characterisation
`transProb_eq_one_iff` is the `EuclideanSpace ℂ (Fin N)` ingredient.) -/
theorem TransProbPreserving.injective
    {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hf : TransProbPreserving f) :
    Function.Injective f := by
  intro p q hpq
  rw [← transProb_eq_one_iff, ← hf p q, hpq, transProb_self]

/-- **Realisability inclusion.** Every unitary in `Matrix.unitaryGroup (Fin N) ℂ`,
acting on `ℂℙ^{N-1}`, is transition-probability preserving. Immediate from
`transProb_smul_unitary`. This is the `U(N) → TransProbPreserving` map; the
surjectivity-up-to-phase of this map is the deferred Wigner statement. -/
theorem transProbPreserving_unitary
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    TransProbPreserving (fun p : ℙ ℂ (EuclideanSpace ℂ (Fin N)) => U • p) :=
  fun p q => transProb_smul_unitary U p q

/-! ## The antiunitary witness `conjProj`

Over `ℂ`, transition-probability preservation admits a second class beyond the
unitary one: the **antiunitary** class, realised by complex conjugation. This
subsection builds it concretely. `conjVec` is coordinatewise complex conjugation
on `EuclideanSpace ℂ (Fin N)`, a **conjugate-linear** isometry
(`conjVec_smul` shows the semilinear scaling law `conjVec (c • ψ) = conj c • conjVec ψ`,
which is *not* the linear law of any `≃ₗᵢ[ℂ]`). Its ray map `conjProj` is
`TransProbPreserving` (`conjProj_transProbPreserving`), so the eventual
Wigner dichotomy is not vacuous on the antiunitary side. -/

/-- Coordinatewise complex conjugation on `EuclideanSpace ℂ (Fin N)`: the
conjugate-linear isometry `ψ ↦ (fun i => conj (ψ i))`. -/
noncomputable def conjVec (ψ : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun i => (starRingEnd ℂ) (ψ.ofLp i))

/-- `conjVec` acts coordinatewise: `(conjVec ψ) i = conj (ψ i)` (definitional). -/
lemma conjVec_ofLp (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (conjVec ψ).ofLp i = (starRingEnd ℂ) (ψ.ofLp i) := rfl

/-- **Conjugation inner identity.** `⟪conjVec u, conjVec v⟫ = conj ⟪u, v⟫`.
Reduces via `PiLp.inner_apply` to the coordinatewise identity
`conj(conj (u i)) * conj (v i) = conj (conj (u i) * v i)` (`RCLike.inner_apply'`,
`map_mul`, `Complex.conj_conj`). -/
lemma conjVec_inner (u v : EuclideanSpace ℂ (Fin N)) :
    (inner ℂ (conjVec u) (conjVec v) : ℂ) = (starRingEnd ℂ) (inner ℂ u v) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.inner_apply', RCLike.inner_apply', map_mul, conjVec_ofLp, conjVec_ofLp,
      Complex.conj_conj]

/-- **Conjugation norm identity.** `‖conjVec ψ‖ = ‖ψ‖`. Both squared norms are
the real part of the (conjugation-swapped) self inner product `conjVec_inner`;
`RCLike.conj_re` drops the conjugation on the real part. -/
lemma conjVec_norm (ψ : EuclideanSpace ℂ (Fin N)) : ‖conjVec ψ‖ = ‖ψ‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (conjVec ψ)), ← Real.sqrt_sq (norm_nonneg ψ)]
  congr 1
  rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
  have h2 : RCLike.re (inner ℂ (conjVec ψ) (conjVec ψ) : ℂ)
      = RCLike.re ((starRingEnd ℂ) (inner ℂ ψ ψ)) := by rw [conjVec_inner]
  rwa [RCLike.conj_re] at h2

/-- **Semilinearity of `conjVec`.** `conjVec (c • ψ) = conj c • conjVec ψ`. This
conjugate-linear scaling law witnesses that `conjVec` is genuinely antiunitary:
it is not the linear scaling law satisfied by any `≃ₗᵢ[ℂ]`, so `conjProj` is not
`projMap` of a complex-linear isometry equivalence. -/
lemma conjVec_smul (c : ℂ) (ψ : EuclideanSpace ℂ (Fin N)) :
    conjVec (c • ψ) = (starRingEnd ℂ) c • conjVec ψ := by
  ext i
  change (starRingEnd ℂ) ((c • ψ).ofLp i) = ((starRingEnd ℂ) c • conjVec ψ).ofLp i
  simp [conjVec_ofLp, map_mul]

/-- `conjVec` preserves nonvanishing: `‖conjVec ψ‖ = ‖ψ‖ ≠ 0`. -/
lemma conjVec_ne_zero {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) : conjVec ψ ≠ 0 := by
  rw [← norm_ne_zero_iff, conjVec_norm]; exact norm_ne_zero_iff.mpr hψ

/-- **Conjugation preserves the vector transition probability.**
`transProbVec (conjVec u) (conjVec v) = transProbVec u v`: the numerator is
fixed since `‖conj ⟪u,v⟫‖ = ‖⟪u,v⟫‖` (`conjVec_inner` + `RCLike.norm_conj`), the
denominator by `conjVec_norm`. -/
lemma conjVec_transProbVec (u v : EuclideanSpace ℂ (Fin N)) :
    transProbVec (conjVec u) (conjVec v) = transProbVec u v := by
  unfold transProbVec
  rw [conjVec_inner, RCLike.norm_conj, conjVec_norm, conjVec_norm]

/-- The **antiunitary ray map**: complex conjugation of the canonical
representative. Total and well-defined (conjugation is norm-preserving and
injective, so the image ray does not depend on representative choice up to the
scaling `conjVec_smul` absorbs). -/
noncomputable def conjProj (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  Projectivization.mk ℂ (conjVec p.rep) (conjVec_ne_zero p.rep_nonzero)

/-- **HEADLINE (antiunitary witness).** `conjProj` is `TransProbPreserving`.
Reduce both image rays to `mk (conjVec ·.rep)` via `transProb_mk`, then apply
`conjVec_transProbVec`. This exhibits a concrete `TransProbPreserving` inhabitant
of the **antiunitary** class: `conjVec` is conjugate-linear (`conjVec_smul`), not
the underlying map of any `≃ₗᵢ[ℂ]`; for `2 ≤ N` the ray-level map `conjProj` is
not `projMap` of any unitary (`conjProj_ne_projMap`, WignerDischarge — at
`N ≤ 1` the projective space has at most one point and the distinction vanishes).
The eventual Wigner dichotomy is thus non-vacuous on the antiunitary side. -/
theorem conjProj_transProbPreserving :
    TransProbPreserving (conjProj (N := N)) := by
  intro p q
  change transProb (Projectivization.mk ℂ (conjVec p.rep) _)
      (Projectivization.mk ℂ (conjVec q.rep) _) = transProb p q
  rw [transProb_mk (conjVec_ne_zero p.rep_nonzero) (conjVec_ne_zero q.rep_nonzero),
      conjVec_transProbVec]
  rfl

/-- **Ray-map identity for `conjProj` on arbitrary representatives.**
`conjProj (mk v hv) = mk (conjVec v)`. The canonical representative of `mk v hv`
is `a • v` for some nonzero `a`; `conjVec (a • v) = conj a • conjVec v`
(`conjVec_smul`), a nonzero rescaling, so both sides span the same ray. This is
the representative-independent form of `conjProj`, needed for the eventual
antiunitary conclusion (Stage 3). -/
lemma conjProj_mk {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    conjProj (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (conjVec v) (conjVec_ne_zero hv) := by
  unfold conjProj
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ (Projectivization.mk ℂ v hv).rep v
    (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(starRingEnd ℂ) a, ?_⟩
  rw [← ha, conjVec_smul]

/-! ## Orthogonality preservation -/

/-- `mk`-level orthogonality rewriter: for nonzero representatives `v, w`, the
projective transition probability of `mk v`, `mk w` vanishes iff `v ⟂ w`.
Routes through `transProb_mk` and the fact that the (positive) denominator of
`transProbVec` is irrelevant to vanishing. -/
lemma transProb_mk_eq_zero_iff {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    transProb (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ w hw) = 0
      ↔ (inner ℂ v w : ℂ) = 0 := by
  rw [transProb_mk hv hw]
  unfold transProbVec
  have hden : ‖v‖ ^ 2 * ‖w‖ ^ 2 ≠ 0 := by positivity
  rw [div_eq_zero_iff]
  simp only [hden, or_false, pow_eq_zero_iff (n := 2) (by norm_num), norm_eq_zero]

/-- **Orthogonality preservation (transProb face).** A transition-probability-
preserving map preserves orthogonality of projective points (read as
`transProb = 0`): the hypothesis rewrites the LHS to the RHS. -/
theorem TransProbPreserving.orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℙ ℂ E → ℙ ℂ E} (hf : TransProbPreserving f) (p q : ℙ ℂ E) :
    transProb (f p) (f q) = 0 ↔ transProb p q = 0 := by
  rw [hf p q]

/-- **Orthogonality preservation (inner-product face).** A transition-probability-
preserving self-map of `ℂℙ^{N-1}` preserves orthogonality of the canonical
representatives. Combines `.orthogonal` with the orthogonality characterisation
`transProb_eq_zero_iff` on both sides. -/
theorem TransProbPreserving.inner_rep_eq_zero_iff
    {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hf : TransProbPreserving f) (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    (inner ℂ (f p).rep (f q).rep : ℂ) = 0 ↔ (inner ℂ p.rep q.rep : ℂ) = 0 := by
  rw [← transProb_eq_zero_iff, ← transProb_eq_zero_iff, hf p q]

/-! ## Orthogonal projective families and orthonormal frames -/

/-- Orthogonality of two projective points, read off the transition
probability: `Orthogonal p q` means `transProb p q = 0` (equivalently, the
representatives are inner-product orthogonal). -/
def Orthogonal (p q : ℙ ℂ E) : Prop := transProb p q = 0

/-- **Orthogonal family preservation.** A transition-probability-preserving map
sends a pairwise-orthogonal projective family to a pairwise-orthogonal family.
Pointwise consequence of `.orthogonal`. -/
theorem TransProbPreserving.pairwise_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f : ℙ ℂ E → ℙ ℂ E} (hf : TransProbPreserving f)
    {ι : Type*} {P : ι → ℙ ℂ E}
    (h : Pairwise (fun i j => transProb (P i) (P j) = 0)) :
    Pairwise (fun i j => transProb (f (P i)) (f (P j)) = 0) :=
  fun i j hij => (hf.orthogonal (P i) (P j)).mpr (h hij)

/-- **Orthonormal frame ↦ pairwise-orthogonal projective family.** An
orthonormal basis of `EuclideanSpace ℂ (Fin N)` induces a pairwise-orthogonal
family of projective points (distinct basis rays are orthogonal). Uses
`b.orthonormal.2` (the off-diagonal vanishing of an `Orthonormal` family) and
the `mk`-level rewriter `transProb_mk_eq_zero_iff`. Composing with
`TransProbPreserving.pairwise_orthogonal` exhibits the "orthonormal frame ↦
pairwise-orthogonal family" content at the orthogonality level. -/
theorem orthonormalBasis_pairwise_orthogonal
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Pairwise (fun i j =>
      transProb (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
        (Projectivization.mk ℂ (b j) (b.orthonormal.ne_zero j)) = 0) :=
  fun i j hij =>
    (transProb_mk_eq_zero_iff (b.orthonormal.ne_zero i) (b.orthonormal.ne_zero j)).mpr
      (b.orthonormal.2 hij)

/-! ## Step (2a): the image orthonormal frame

A `TransProbPreserving` map `f` together with a source orthonormal basis `b`
produces an orthonormal family of *image* representatives, the unit-normalised
canonical reps of the image rays `f (mk (b i))`. Pairwise orthogonality is
transported from the source frame through `inner_rep_eq_zero_iff`; the diagonal
is unit by construction. Indexed by `Fin N` in a space of `finrank = N`, the
family is an orthonormal basis. Each image ONB vector spans the image ray:
`mk (imageOrthonormalBasis i) = f (mk (b i))`. -/

variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-- The `i`-th source basis projective point `mk (b i)`. A definitional
abbreviation kept folded inside the auxiliary lemmas; the public headlines
(`mk_imageOrthonormalBasis`, `candidateUnitary_agrees_on_basis`) restate it as
the explicit `mk ℂ (b i) (b.orthonormal.ne_zero i)`. -/
noncomputable def srcPoint
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)

/-- `srcPoint` unfolds to the explicit `mk` of the basis vector. -/
lemma srcPoint_eq
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    srcPoint b i = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := rfl

/-- The unit-normalised canonical representative of the image ray
`f (mk (b i))`. Normalising the (nonzero) rep `(f (srcPoint b i)).rep` by the
real reciprocal of its norm (cast to `ℂ`) gives a unit vector spanning the same
ray. -/
noncomputable def imageVec
    (_hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    EuclideanSpace ℂ (Fin N) :=
  ((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ) • (f (srcPoint b i)).rep

/-- The reciprocal-norm scalar in `imageVec` is nonzero (the rep is nonzero, so
its norm is positive). -/
lemma imageVec_scalar_ne_zero
    (_hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
  have hne : (f (srcPoint b i)).rep ≠ 0 := (f (srcPoint b i)).rep_nonzero
  have hpos : (0 : ℝ) < ‖(f (srcPoint b i)).rep‖ := norm_pos_iff.mpr hne
  exact_mod_cast (ne_of_gt (inv_pos.mpr hpos))

/-- `imageVec` is nonzero. -/
lemma imageVec_ne_zero
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    imageVec hf b i ≠ 0 := by
  unfold imageVec
  exact smul_ne_zero (imageVec_scalar_ne_zero hf b i) (f (srcPoint b i)).rep_nonzero

/-- `imageVec` has unit norm: the reciprocal-norm scaling normalises the rep. -/
lemma imageVec_norm
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    ‖imageVec hf b i‖ = 1 := by
  have hpos : (0 : ℝ) < ‖(f (srcPoint b i)).rep‖ :=
    norm_pos_iff.mpr (f (srcPoint b i)).rep_nonzero
  unfold imageVec
  rw [norm_smul, Complex.norm_real, norm_inv, Real.norm_eq_abs,
      abs_of_pos hpos, inv_mul_cancel₀ (ne_of_gt hpos)]

/-- The image family `imageVec hf b` is orthonormal. Off-diagonal: the source
basis rays are orthogonal (`orthonormalBasis_pairwise_orthogonal` +
`transProb_eq_zero_iff` on the canonical reps), `inner_rep_eq_zero_iff hf`
transports this to the *image* reps, and the scalar normalisation factors pull
out of `inner` leaving `0`. Diagonal: `imageVec_norm`. -/
lemma imageVec_orthonormal
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Orthonormal ℂ (imageVec hf b) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases eq_or_ne i j with hij | hij
  · subst hij
    simp only [if_true]
    rw [inner_self_eq_norm_sq_to_K, imageVec_norm hf b i]
    norm_num
  · simp only [if_neg hij]
    -- source rays orthogonal ⇒ source reps orthogonal ⇒ image reps orthogonal
    have hsrc : transProb (srcPoint b i) (srcPoint b j) = 0 :=
      orthonormalBasis_pairwise_orthogonal b hij
    have hsrc_inner : (inner ℂ (srcPoint b i).rep (srcPoint b j).rep : ℂ) = 0 :=
      (transProb_eq_zero_iff (srcPoint b i) (srcPoint b j)).mp hsrc
    have himg_inner : (inner ℂ (f (srcPoint b i)).rep (f (srcPoint b j)).rep : ℂ) = 0 :=
      (hf.inner_rep_eq_zero_iff (srcPoint b i) (srcPoint b j)).mpr hsrc_inner
    unfold imageVec
    rw [inner_smul_left, inner_smul_right, himg_inner, mul_zero, mul_zero]

/-- The image orthonormal family, packaged as an `OrthonormalBasis (Fin N)`:
an orthonormal family of cardinality `N` in `EuclideanSpace ℂ (Fin N)`
(`finrank = N`) spans the whole space, so `OrthonormalBasis.mk` applies. -/
noncomputable def imageOrthonormalBasis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) := by
  refine OrthonormalBasis.mk (imageVec_orthonormal hf b) ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro x _
    exact (Subsingleton.elim x 0) ▸ Submodule.zero_mem _
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hcard : Fintype.card (Fin N) = Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) := by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
    rw [(imageVec_orthonormal hf b).linearIndependent.span_eq_top_of_card_eq_finrank hcard]

/-- `imageOrthonormalBasis` evaluates to `imageVec` (the `OrthonormalBasis.mk`
apply lemma). -/
lemma imageOrthonormalBasis_apply
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    imageOrthonormalBasis hf b i = imageVec hf b i := by
  unfold imageOrthonormalBasis
  rw [OrthonormalBasis.coe_mk]

/-- **The image ONB vector's ray is the image ray.** `imageVec hf b i` is a
nonzero scalar multiple of `(f (srcPoint b i)).rep`, so `mk (imageVec ..)`
equals `mk ((f (srcPoint b i)).rep) = f (srcPoint b i)` by the `mk`-scaling
characterisation `mk_eq_mk_iff'` and `mk_rep`. -/
lemma mk_imageOrthonormalBasis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    Projectivization.mk ℂ (imageOrthonormalBasis hf b i)
        ((imageOrthonormalBasis_apply hf b i).symm ▸ imageVec_ne_zero hf b i)
      = f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)) := by
  change _ = f (srcPoint b i)
  -- mk (imageONB i) = mk (imageVec i) = mk ((f (srcPoint i)).rep) = f (srcPoint i).
  -- `mk` is proof-irrelevant in the nonzero hypothesis, so the dependent proof
  -- argument is immaterial; chain three `mk` equalities.
  have hrep_ne : (f (srcPoint b i)).rep ≠ 0 := (f (srcPoint b i)).rep_nonzero
  have h1 : Projectivization.mk ℂ (imageOrthonormalBasis hf b i)
        ((imageOrthonormalBasis_apply hf b i).symm ▸ imageVec_ne_zero hf b i)
      = Projectivization.mk ℂ (imageVec hf b i) (imageVec_ne_zero hf b i) := by
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ?_
    exact ⟨1, by rw [one_smul, imageOrthonormalBasis_apply]⟩
  have h2 : Projectivization.mk ℂ (imageVec hf b i) (imageVec_ne_zero hf b i)
      = Projectivization.mk ℂ (f (srcPoint b i)).rep hrep_ne := by
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ?_
    exact ⟨((‖(f (srcPoint b i)).rep‖⁻¹ : ℝ) : ℂ), rfl⟩
  rw [h1, h2, Projectivization.mk_rep]

/-! ## Step (2b): the candidate unitary

The candidate unitary is the `OrthonormalBasis.equiv` change-of-frame
`b ↦ imageOrthonormalBasis hf b` along the identity reindexing. On the source
basis vectors it reproduces the image ONB vectors, hence (via
`mk_imageOrthonormalBasis`) agrees ray-by-ray with `f` on the basis points.
This is the unitary candidate for the Wigner converse; the open content is
extending the agreement off the basis (step (2c)) and ruling out the antiunitary
branch (step (2d)). -/

/-- The candidate unitary: the linear isometry equivalence carrying the source
orthonormal basis `b` to the image orthonormal basis along the identity
reindexing of `Fin N`. -/
noncomputable def candidateUnitary
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  b.equiv (imageOrthonormalBasis hf b) (Equiv.refl (Fin N))

/-- The candidate unitary sends the `i`-th source basis vector to the `i`-th
image ONB vector. From `OrthonormalBasis.equiv_apply_basis` and
`Equiv.refl_apply`. -/
lemma candidateUnitary_apply_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    candidateUnitary hf b (b i) = imageOrthonormalBasis hf b i := by
  unfold candidateUnitary
  rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]

/-- **Step (2b) headline.** The candidate unitary agrees with `f` on the basis
points: the ray spanned by `candidateUnitary hf b (b i)` is exactly the image
ray `f (mk (b i))`. Composes `candidateUnitary_apply_basis` (the image ONB
vector) with `mk_imageOrthonormalBasis` (its ray is the image ray). -/
theorem candidateUnitary_agrees_on_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    Projectivization.mk ℂ (candidateUnitary hf b (b i))
        ((candidateUnitary hf b).toLinearEquiv.map_ne_zero_iff.mpr (b.orthonormal.ne_zero i))
      = f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)) := by
  rw [← mk_imageOrthonormalBasis hf b i]
  -- both rays are `mk` of the same vector `imageOrthonormalBasis hf b i`
  -- (after rewriting `candidateUnitary hf b (b i)` to it); `mk` is irrelevant to
  -- the nonzero-proof argument.
  congr 1
  · exact candidateUnitary_apply_basis hf b i

/-! ## Step (2c) frame reduction: projective image of an isometry equiv

The projective map `projMap e` of a linear isometry equivalence `e` preserves
`transProb` (`transProb_projMap`), so it is `TransProbPreserving`
(`projMap_transProbPreserving`). Composing `f` with the projective map of the
*inverse* candidate unitary yields `reducedMap`, which is `TransProbPreserving`
and **fixes every basis ray** (`reducedMap_fixes_basis`). This reduces the open
converse step (2c) to the single Wigner normal-form lemma stated in the module
header. These declarations are general in `E` wherever they do not consume the
`EuclideanSpace`-specific `candidateUnitary`. -/

section ProjMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The projective self-map induced by a linear isometry equivalence `e`: the
`Projectivization.map` of `e`'s underlying (injective) linear map. -/
noncomputable def projMap (e : E ≃ₗᵢ[ℂ] E) : ℙ ℂ E → ℙ ℂ E :=
  Projectivization.map e.toLinearEquiv.toLinearMap e.injective

/-- `projMap e` sends `mk v` to `mk (e v)`. The nonzero side is `e v ≠ 0` from
`e.injective` (an injective linear map is zero-preserving), packaged through
`Projectivization.map_mk`. -/
lemma projMap_mk (e : E ≃ₗᵢ[ℂ] E) (v : E) (hv : v ≠ 0) :
    projMap e (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (e v) (e.toLinearEquiv.map_ne_zero_iff.mpr hv) := by
  unfold projMap
  rw [Projectivization.map_mk]
  rfl

/-- `projMap` of the identity is the identity ray map. -/
@[simp] lemma projMap_refl :
    projMap (LinearIsometryEquiv.refl ℂ E) = id := by
  funext p
  induction p using Projectivization.ind with
  | h v hv => rw [projMap_mk]; rfl

/-- `projMap` is functorial: the ray map of a composite is the composite of the
ray maps (`trans` composes left-to-right, so `projMap e₂` applies second). -/
lemma projMap_trans (e₁ e₂ : E ≃ₗᵢ[ℂ] E) :
    projMap (e₁.trans e₂) = projMap e₂ ∘ projMap e₁ := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Function.comp_apply, projMap_mk, projMap_mk, projMap_mk]
    rfl

/-- **Transition probability is invariant under a linear isometry equivalence
(vector level).** `transProbVec (e u) (e v) = transProbVec u v`: the numerator
is fixed by `e.inner_map_map`, the denominator by `e.norm_map`. -/
lemma transProbVec_linearIsometryEquiv (e : E ≃ₗᵢ[ℂ] E) (u v : E) :
    transProbVec (e u) (e v) = transProbVec u v := by
  unfold transProbVec
  rw [e.inner_map_map u v, e.norm_map u, e.norm_map v]

/-- **`projMap e` preserves `transProb` (projective level).** Reduce both points
to `mk` of their canonical reps, push `projMap` through `projMap_mk`, collapse to
`transProbVec` via `transProb_mk`, then apply
`transProbVec_linearIsometryEquiv`. -/
lemma transProb_projMap (e : E ≃ₗᵢ[ℂ] E) (p q : ℙ ℂ E) :
    transProb (projMap e p) (projMap e q) = transProb p q := by
  conv_lhs => rw [← p.mk_rep, ← q.mk_rep]
  rw [projMap_mk e p.rep p.rep_nonzero, projMap_mk e q.rep q.rep_nonzero,
      transProb_mk]
  conv_rhs => rw [← p.mk_rep, ← q.mk_rep, transProb_mk p.rep_nonzero q.rep_nonzero]
  exact transProbVec_linearIsometryEquiv e p.rep q.rep

/-- **`projMap e` is `TransProbPreserving`.** Immediate from `transProb_projMap`.
General in `E`. -/
theorem projMap_transProbPreserving (e : E ≃ₗᵢ[ℂ] E) :
    TransProbPreserving (projMap e) :=
  fun p q => transProb_projMap e p q

/-- **Composition of `TransProbPreserving` maps.** `g ∘ f` preserves `transProb`
when both `g` and `f` do. General in `E`. -/
theorem TransProbPreserving.comp {g f : ℙ ℂ E → ℙ ℂ E}
    (hg : TransProbPreserving g) (hf : TransProbPreserving f) :
    TransProbPreserving (fun p => g (f p)) :=
  fun p q => by rw [hg (f p) (f q), hf p q]

end ProjMap

/-! ## Step (2c) frame reduction: the reduced map fixes every basis ray

`reducedMap hf b := projMap (candidateUnitary hf b).symm ∘ f`. It is
`TransProbPreserving` and fixes every source basis ray, since on `srcPoint b i`
the candidate unitary's projective map reproduces `f`'s value (by
`candidateUnitary_agrees_on_basis`) and its inverse returns to the basis ray. -/

variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-- The **frame-reduced map**: post-compose `f` with the projective map of the
*inverse* candidate unitary. Designed so that the basis rays become fixed
points. -/
noncomputable def reducedMap
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  fun p => projMap (candidateUnitary hf b).symm (f p)

/-- **`reducedMap` is `TransProbPreserving`.** It is the composition
`projMap (candidateUnitary hf b).symm ∘ f`; compose `hf` with
`projMap_transProbPreserving`. -/
theorem reducedMap_transProbPreserving
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    TransProbPreserving (reducedMap hf b) :=
  (projMap_transProbPreserving (candidateUnitary hf b).symm).comp hf

/-- **HEADLINE (frame reduction).** The frame-reduced map fixes every source
basis ray: `reducedMap hf b (mk (b i)) = mk (b i)`.

Proof chain. Write `U := candidateUnitary hf b`. By definition
`reducedMap hf b (srcPoint b i) = projMap U.symm (f (srcPoint b i))`. Rewrite
`f (srcPoint b i)` backward via `candidateUnitary_agrees_on_basis` to
`mk (U (b i))`; push `projMap U.symm` through `projMap_mk` to
`mk (U.symm (U (b i)))`; and `U.symm (U (b i)) = b i` by
`LinearIsometryEquiv.symm_apply_apply`. `mk` is proof-irrelevant in its nonzero
hypothesis, so the dependent nonzero proofs are immaterial.

**Residual diagonal-phase freedom.** Fixing the basis rays does *not* make `reducedMap`
the identity: the diagonal-phase freedom is genuine and is exactly what the
remaining normal-form lemma (step (2c)) must pin down. Do not read this as
`reducedMap = id` or `f = projMap (candidateUnitary hf b)`. -/
theorem reducedMap_fixes_basis
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N) :
    reducedMap hf b (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) := by
  set U := candidateUnitary hf b with hU
  change projMap U.symm (f (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)))
      = Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)
  rw [← candidateUnitary_agrees_on_basis hf b i, ← hU,
      projMap_mk U.symm (U (b i))
        ((candidateUnitary hf b).toLinearEquiv.map_ne_zero_iff.mpr (b.orthonormal.ne_zero i))]
  -- `U.symm (U (b i)) = b i`; `mk` is irrelevant to the nonzero-proof argument.
  congr 1
  exact U.symm_apply_apply (b i)

/-! ## Stage 1: moduli preservation

A `TransProbPreserving` map fixing a projective point `q` preserves the
transition probability from every point to `q` (`TransProbPreserving.transProb_of_fixed`).
Applied to `reducedMap hf b`, which fixes every source basis ray, this shows the
**modulus profile** of the coordinates in the basis `b` is preserved: writing
`reducedMap hf b (mk ψ) = mk φ`, the normalised squared modulus
`‖b.repr ψ i‖² / ‖ψ‖²` of each coordinate is preserved
(`reducedMap_coord_modulus`). This is the coordinate-free heart of the Wigner
normal-form argument; it does not yet pin phases. -/

/-- **Moduli-preservation kernel.** A transition-probability-preserving map
fixing a projective point `q` preserves the transition probability from every
point to `q`. General in `E`. -/
theorem TransProbPreserving.transProb_of_fixed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {g : ℙ ℂ E → ℙ ℂ E} (hg : TransProbPreserving g)
    {q : ℙ ℂ E} (hq : g q = q) (p : ℙ ℂ E) :
    transProb (g p) q = transProb p q := by
  conv_lhs => rw [← hq]
  exact hg p q

/-- The transition probability from `mk ψ` to the `i`-th source basis ray
`srcPoint b i` is the normalised squared modulus of the `i`-th coordinate
`b.repr ψ i`. Uses `norm_inner_symm` and `OrthonormalBasis.repr_apply_apply` to
identify `‖⟪ψ, b i⟫‖ = ‖b.repr ψ i‖`, and `Orthonormal.norm_eq_one` to drop the
unit basis norm from the denominator. -/
lemma transProb_srcPoint
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    transProb (Projectivization.mk ℂ ψ hψ) (srcPoint b i)
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  rw [srcPoint_eq, transProb_mk hψ (b.orthonormal.ne_zero i)]
  unfold transProbVec
  rw [b.orthonormal.norm_eq_one i, one_pow, mul_one, norm_inner_symm,
      ← b.repr_apply_apply]

/-- **Stage 1 (moduli preservation).** Writing `reducedMap hf b (mk ψ) = mk φ`,
the normalised squared modulus of every coordinate in the basis `b` is preserved:
`‖b.repr φ i‖² / ‖φ‖² = ‖b.repr ψ i‖² / ‖ψ‖²`, where `φ` is the canonical
representative of the image ray. Combines the moduli-preservation kernel
`TransProbPreserving.transProb_of_fixed` (with `q = srcPoint b i`, fixed by
`reducedMap_fixes_basis`) and the coordinate reading `transProb_srcPoint`. -/
theorem reducedMap_coord_modulus
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ψ ≠ 0) (i : Fin N) :
    ‖b.repr (reducedMap hf b (Projectivization.mk ℂ ψ hψ)).rep i‖ ^ 2
        / ‖(reducedMap hf b (Projectivization.mk ℂ ψ hψ)).rep‖ ^ 2
      = ‖b.repr ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  have hfix : reducedMap hf b (srcPoint b i) = srcPoint b i := by
    rw [srcPoint_eq]; exact reducedMap_fixes_basis hf b i
  have key := (reducedMap_transProbPreserving hf b).transProb_of_fixed hfix
    (Projectivization.mk ℂ ψ hψ)
  rw [transProb_srcPoint b hψ i] at key
  set gp := reducedMap hf b (Projectivization.mk ℂ ψ hψ) with hgp
  have hgp_coord : transProb gp (srcPoint b i)
      = ‖b.repr gp.rep i‖ ^ 2 / ‖gp.rep‖ ^ 2 := by
    conv_lhs => rw [← Projectivization.mk_rep gp]
    exact transProb_srcPoint b gp.rep_nonzero i
  rw [← hgp_coord, key]

end Projectivization
