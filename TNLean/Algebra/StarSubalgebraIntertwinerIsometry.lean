/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.StarSubalgebraIsotypic

/-!
# Intertwiners on irreducible pieces are isometries up to a nonnegative scale

Continuing the structure theory of *Quantum Channels & Operations* (Wolf 2012), Chapter 6,
towards Theorem 6.14, this file shows that an operator carrying an irreducible piece of a
star-subalgebra into another piece, and commuting there with the subalgebra, preserves the
inner product up to a single nonnegative real factor. On the irreducible source it is, after
dividing by the square root of that factor, an isometry onto its image.

This is the metric input to the assembly of a single unitary change of basis: each
isomorphism between pieces of the same type can be normalized to a partial isometry, so the
pieces of one type are unitarily identified.

## Proof outline

Compose the operator with the Euclidean adjoint and project back onto the source. The result
maps the source into itself and commutes there with the subalgebra, because the orthogonal
projection onto an invariant subspace commutes with the subalgebra and the adjoint of every
member of the subalgebra is again a member. Schur's lemma on the irreducible source makes
this composite a scalar, and pairing against the source identifies that scalar with the inner
product of the images. Pairing a nonzero source vector with itself shows the scalar is a
nonnegative real, since it equals the squared norm of the image divided by the squared norm
of the vector.
-/

open scoped Matrix InnerProductSpace ComplexConjugate

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

omit [DecidableEq n] in
/-- Pairing the orthogonal projection onto a subspace with a vector of that subspace ignores
the projection. -/
private theorem inner_starProjection_left_mem
    {p : Submodule ℂ (EuclideanSpace ℂ n)} (z : EuclideanSpace ℂ n)
    {w : EuclideanSpace ℂ n} (hw : w ∈ p) :
    ⟪p.starProjection z, w⟫_ℂ = ⟪z, w⟫_ℂ := by
  have h := Submodule.starProjection_inner_eq_zero (K := p) z w hw
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

/-- A vector of an invariant subspace, mapped by a member of the subalgebra, stays in the
subspace. -/
private theorem toEuclideanLin_mem_of_mem {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsInvariantSubspace p) {A : Matrix n n ℂ} (hA : A ∈ S)
    {x : EuclideanSpace ℂ n} (hx : x ∈ p) : Matrix.toEuclideanLin A x ∈ p :=
  (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := Matrix.toEuclideanLin A)).mp
    (hp A hA) x hx

/-- For an intertwiner `f` of a star-subalgebra `S` of complex matrices from `p` into `q`,
projecting the Euclidean adjoint of `f` applied at a vector of `q` back onto an invariant
subspace `p` commutes with every member of the subalgebra. The adjoint of every member is
again a member and the source is invariant, so the intertwining identity of `f` transfers to
the projected adjoint. See *Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards
Theorem 6.14. -/
private theorem starProjection_adjoint_comm
    {p q : Submodule ℂ (EuclideanSpace ℂ n)} (hp : S.IsInvariantSubspace p)
    {f : Module.End ℂ (EuclideanSpace ℂ n)} (hf : S.IsIntertwiner p q f)
    {A : Matrix n n ℂ} (hA : A ∈ S) (y : EuclideanSpace ℂ n) :
    p.starProjection (LinearMap.adjoint f (Matrix.toEuclideanLin A y)) =
      Matrix.toEuclideanLin A (p.starProjection (LinearMap.adjoint f y)) := by
  -- The conjugate transpose of `A` is again a member of `S`.
  have hAstar : Aᴴ ∈ S := by simpa [Matrix.star_eq_conjTranspose] using star_mem hA
  -- Both vectors lie in `p`; it suffices to test them against every vector of `p`.
  set u := p.starProjection (LinearMap.adjoint f (Matrix.toEuclideanLin A y)) with hu
  set v := Matrix.toEuclideanLin A (p.starProjection (LinearMap.adjoint f y)) with hv
  have hu_mem : u ∈ p := p.starProjection_apply_mem _
  have hv_mem : v ∈ p :=
    S.toEuclideanLin_mem_of_mem hp hA (p.starProjection_apply_mem _)
  have hsub_mem : u - v ∈ p := p.sub_mem hu_mem hv_mem
  -- Against any `w ∈ p`, the difference of the two vectors pairs to zero.
  have hpair : ∀ w ∈ p, ⟪u - v, w⟫_ℂ = 0 := by
    intro w hw
    have hAw : Matrix.toEuclideanLin Aᴴ w ∈ p := S.toEuclideanLin_mem_of_mem hp hAstar hw
    have hLHS : ⟪u, w⟫_ℂ = ⟪Matrix.toEuclideanLin A y, f w⟫_ℂ := by
      rw [hu, inner_starProjection_left_mem _ hw, LinearMap.adjoint_inner_left]
    have hRHS : ⟪v, w⟫_ℂ = ⟪Matrix.toEuclideanLin A y, f w⟫_ℂ := by
      rw [hv, ← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        inner_starProjection_left_mem _ hAw, LinearMap.adjoint_inner_left, hf.2 Aᴴ hAstar w hw,
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
    rw [inner_sub_left, hLHS, hRHS, sub_self]
  -- A vector of `p` orthogonal to all of `p` is zero.
  have hzero : u - v = 0 := inner_self_eq_zero.mp (hpair _ hsub_mem)
  rw [sub_eq_zero] at hzero
  exact hzero

/-- On an irreducible piece `p` of a star-subalgebra `S` of complex matrices, an intertwiner
`f` carrying `p` into a piece `q` preserves the inner product up to a single nonnegative real
factor `c`: for all `x` and `y` in `p`,
$$\langle f(x), f(y)\rangle = c\,\langle x, y\rangle .$$
Following `f` with its Euclidean adjoint and the orthogonal projection onto `p` gives an
operator that maps `p` into itself and commutes there with the subalgebra, so Schur's lemma
makes it a scalar; pairing against `p` identifies the scalar with the inner product of the
images, and pairing a nonzero vector with itself shows the scalar is a nonnegative real. See
*Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem exists_real_smul_inner_of_intertwiner
    {p q : Submodule ℂ (EuclideanSpace ℂ n)} (hp : S.IsIrreducibleSubspace p)
    {f : Module.End ℂ (EuclideanSpace ℂ n)} (hf : S.IsIntertwiner p q f) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ p, ∀ y ∈ p, ⟪f x, f y⟫_ℂ = (c : ℂ) * ⟪x, y⟫_ℂ := by
  obtain ⟨hpinv, hpne, hpmax⟩ := hp
  -- The composite operator: apply `f`, the Euclidean adjoint of `f`, and project onto `p`.
  set g : Module.End ℂ (EuclideanSpace ℂ n) :=
    p.starProjection.toLinearMap ∘ₗ (LinearMap.adjoint f ∘ₗ f) with hg
  have hg_apply : ∀ z, g z = p.starProjection (LinearMap.adjoint f (f z)) := fun z => rfl
  -- `g` maps `p` into itself, since the projection lands in `p`.
  have hg_mem : p ∈ Module.End.invtSubmodule g :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := g)).mpr fun x _ =>
      hg_apply x ▸ p.starProjection_apply_mem _
  -- `g` commutes on `p` with every member: combine the adjoint identity with that of `f`.
  have hg_comm : ∀ A ∈ S, ∀ x ∈ p,
      g (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin A (g x) := by
    intro A hA x hx
    rw [hg_apply, hg_apply, hf.2 A hA x hx,
      S.starProjection_adjoint_comm hpinv hf hA (f x)]
  -- Schur's lemma makes `g` a scalar on the irreducible piece `p`.
  obtain ⟨c, hc⟩ :=
    S.exists_eq_smul_of_commute_of_irreducible ⟨hpinv, hpne, hpmax⟩ hg_mem hg_comm
  -- Pairing `g` against `p` recovers the inner product of the images.
  have hinner : ∀ x ∈ p, ∀ y ∈ p, ⟪f x, f y⟫_ℂ = (starRingEnd ℂ) c * ⟪x, y⟫_ℂ := by
    intro x hx y hy
    have h1 : ⟪f x, f y⟫_ℂ = ⟪g x, y⟫_ℂ := by
      rw [hg_apply, inner_starProjection_left_mem _ hy, LinearMap.adjoint_inner_left]
    rw [h1, hc x hx, inner_smul_left]
  -- Evaluate the scalar at a nonzero vector to see it is a nonnegative real.
  obtain ⟨x₀, hx₀p, hx₀ne⟩ := (Submodule.ne_bot_iff p).mp hpne
  have hx₀norm : (0 : ℝ) < ‖x₀‖ ^ 2 := by positivity
  have hkey : (starRingEnd ℂ) c * (‖x₀‖ ^ 2 : ℂ) = (‖f x₀‖ ^ 2 : ℂ) := by
    have h := hinner x₀ hx₀p x₀ hx₀p
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    exact h.symm
  -- The conjugate scalar is the ratio of squared norms, a nonnegative real.
  refine ⟨‖f x₀‖ ^ 2 / ‖x₀‖ ^ 2, by positivity, fun x hx y hy => ?_⟩
  have hconj : (starRingEnd ℂ) c = ((‖f x₀‖ ^ 2 / ‖x₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_pow, eq_div_iff (by
      exact_mod_cast ne_of_gt hx₀norm)]
    exact_mod_cast hkey
  rw [hinner x hx y hy, hconj]

/-- On an irreducible piece `p` of a star-subalgebra `S` of complex matrices, an intertwiner
`f` carrying `p` into a piece `q` that does not vanish on `p` preserves the inner product up
to a strictly positive real factor `c`: for all `x` and `y` in `p`,
$$\langle f(x), f(y)\rangle = c\,\langle x, y\rangle , \qquad c > 0 .$$
The nonnegative factor from the inner-product identity is strictly positive here, since
evaluating it at a vector of `p` on which `f` is nonzero gives a positive squared norm. After
dividing `f` by the square root of `c`, the restriction to `p` is an isometry onto `q`. See
*Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem exists_pos_smul_inner_of_intertwiner_ne_zero
    {p q : Submodule ℂ (EuclideanSpace ℂ n)} (hp : S.IsIrreducibleSubspace p)
    {f : Module.End ℂ (EuclideanSpace ℂ n)} (hf : S.IsIntertwiner p q f)
    (hne : ¬ ∀ x ∈ p, f x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ p, ∀ y ∈ p, ⟪f x, f y⟫_ℂ = (c : ℂ) * ⟪x, y⟫_ℂ := by
  obtain ⟨c, -, hceq⟩ := S.exists_real_smul_inner_of_intertwiner hp hf
  -- Choose a vector of `p` on which `f` does not vanish.
  obtain ⟨x₀, hx₀p, hfx₀ne⟩ : ∃ x ∈ p, f x ≠ 0 := by simpa using hne
  have hx₀ne0 : x₀ ≠ 0 := fun h => hfx₀ne (by rw [h, map_zero])
  refine ⟨c, ?_, hceq⟩
  -- Evaluating the identity at `x₀` gives `‖f x₀‖² = c‖x₀‖²` with both norms positive.
  have hval : (‖f x₀‖ ^ 2 : ℂ) = (c : ℂ) * (‖x₀‖ ^ 2 : ℂ) := by
    have h := hceq x₀ hx₀p x₀ hx₀p
    rwa [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hvalℝ : ‖f x₀‖ ^ 2 = c * ‖x₀‖ ^ 2 := by exact_mod_cast hval
  have hfpos : (0 : ℝ) < ‖f x₀‖ ^ 2 := by positivity
  have hxpos : (0 : ℝ) < ‖x₀‖ ^ 2 := by positivity
  nlinarith [hvalℝ, hfpos, hxpos]

end StarSubalgebra
