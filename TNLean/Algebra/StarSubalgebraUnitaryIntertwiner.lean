/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.StarSubalgebraIntertwinerIsometry

/-!
# Same-type irreducible pieces are unitarily identified

Continuing the structure theory of *Quantum Channels & Operations* (Wolf 2012), Chapter 6,
towards Theorem 6.14, this file produces, for two irreducible pieces of a star-subalgebra of
complex matrices that are of the same type, an intertwiner that is an isometry of the first
piece onto the second. Such an operator commutes on the source with every member of the
subalgebra, maps the source onto the target, and preserves the inner product on the source, so
it is a unitary identification of the two pieces.

## Proof outline

Same type gives an intertwiner that is injective on the source and maps it onto the target.
Since the target is nonzero, the intertwiner does not vanish on the source, so the scaled
inner-product identity for nonvanishing intertwiners gives a positive real factor `c` with
`⟪f x, f y⟫ = c ⟪x, y⟫` on the source. Normalizing the intertwiner by `1 / √c` keeps the
commuting identity, keeps the image (scaling by a nonzero scalar preserves the image
subspace), and turns the inner-product factor into one, making the normalized operator an
isometry of the source onto the target.
-/

open scoped Matrix InnerProductSpace ComplexConjugate

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- For two irreducible pieces `p` and `q` of a star-subalgebra `S` of complex matrices that
are of the same type, there is an operator `u` that is an intertwiner from `p` into `q`, maps
`p` onto `q`, and preserves the inner product on `p`: for all `x` and `y` in `p`,
$$\langle u(x), u(y)\rangle = \langle x, y\rangle .$$
Same type gives an intertwiner injective on `p` with image `q`; since `q` is nonzero it does
not vanish on `p`, so the scaled inner-product identity gives a positive real factor `c` with
$\langle f(x), f(y)\rangle = c\,\langle x, y\rangle$, and dividing the intertwiner by
$\sqrt{c}$ keeps the commuting identity and the image while turning the factor into one. See
*Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem exists_isometry_intertwiner_of_sameIsotype
    {p q : Submodule ℂ (EuclideanSpace ℂ n)} (hp : S.IsIrreducibleSubspace p)
    (hq : S.IsIrreducibleSubspace q) (h : S.SameIsotype p q) :
    ∃ u : Module.End ℂ (EuclideanSpace ℂ n), S.IsIntertwiner p q u ∧
      Submodule.map u p = q ∧ ∀ x ∈ p, ∀ y ∈ p, ⟪u x, u y⟫_ℂ = ⟪x, y⟫_ℂ := by
  -- Same type gives an intertwiner `f` injective on `p` with image exactly `q`.
  obtain ⟨f, hf, _, hfeq⟩ := (S.sameIsotype_iff_exists_isomorphism hp hq).mp h
  -- Since `q` is nonzero, `f` does not vanish on `p`, giving a positive inner-product factor.
  have hne : ¬ ∀ x ∈ p, f x = 0 := by
    intro hzero
    refine hq.2.1 (eq_bot_iff.mpr ?_)
    rw [← hfeq]
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [hzero x hx]
    exact Submodule.zero_mem _
  obtain ⟨c, hcpos, hceq⟩ := S.exists_pos_smul_inner_of_intertwiner_ne_zero hp hf hne
  -- The normalizing real scalar `s = 1 / √c`, nonzero since `c > 0`.
  set s : ℝ := (Real.sqrt c)⁻¹ with hs
  have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
  have hs_ne : (s : ℂ) ≠ 0 := by
    rw [hs]; exact_mod_cast inv_ne_zero (ne_of_gt hsqrt_pos)
  -- The normalized operator `u = s • f`.
  refine ⟨(s : ℂ) • f, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `u` carries `p` into `q`, since scaling by a nonzero scalar preserves the image.
    rw [Submodule.map_smul f p (s : ℂ) hs_ne, hfeq]
  · -- `u` commutes on `p` with every member: scaling commutes with the linear matrix action.
    intro A hA x hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hf.2 A hA x hx, map_smul]
  · -- `u` maps `p` onto `q`, again by the scaling-invariance of the image.
    rw [Submodule.map_smul f p (s : ℂ) hs_ne, hfeq]
  · -- `u` preserves the inner product: the factor `s² c` equals one.
    intro x hx y hy
    rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hceq x hx y hy]
    have hsc : (s : ℝ) * (s * c) = 1 := by
      have hsqrt : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hcpos.le
      rw [hs]
      field_simp
      linarith [hsqrt]
    have : (s : ℂ) * ((s : ℂ) * ((c : ℂ) * ⟪x, y⟫_ℂ)) =
        (((s * (s * c) : ℝ)) : ℂ) * ⟪x, y⟫_ℂ := by push_cast; ring
    rw [this, hsc]
    simp

end StarSubalgebra
