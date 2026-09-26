/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Invariants

/-!
# G-injective and G-isometric PEPS tensors

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Definition `def:2d-Ug-inj`,
`Papers/1001.3807/paper_v3.tex` lines 1278–1296: a PEPS tensor `A` is `G`-injective for a
representation `g ↦ U_g` on its virtual level if it is invariant under `U_g` and the map
`𝒫(A)` from the virtual to the physical system (lines 501–507) has a left inverse with
`𝒫(A)⁻¹𝒫(A) = Π_U`, the projector onto the `U_g`-invariant subspace. Definition
`def:iso:isopeps`, lines 1692–1697: a `G`-injective tensor is `G`-isometric if `U_g` is the
regular representation and `𝒫(A)` restricted to its domain and range is unitary.
Review: arXiv:2011.12127, Section "Symmetries in PEPS", line 1482, which uses the notion
without restating it.

**Formalized here.** `IsGInjective ρ T` for a linear map `T` (the map `𝒫(A)`) and a
representation `ρ` of `G` on its domain (the whole virtual level, which in the source is a
tensor product of one representation per link, lines 1318–1325). The source's left-inverse
condition is proved equivalent for finite `G` (`isGInjective_iff_exists_leftInverse`).
`IsGIsometric ρ T` asks in addition that `T` preserve inner products of invariant vectors up
to one positive scalar.

**Local fix (normalization and representation):** the source assumes `U_g` semi-regular
(containing every irreducible representation, lines 1010–1013) for `G`-injectivity and the
left-regular representation for `G`-isometry; here both predicates take the representation as
a parameter, and each instance states which representation it uses. The source's
quantum-double tensor `K` (lines 2906–2911), which it calls `G`-isometric, is not normalized,
and neither is the review's (line 2465); `IsGIsometric` therefore allows a positive factor `c`
in `⟪T x, T y⟫ = c ⟪x, y⟫`, which the normalization `T / √c` removes. Documented in
`docs/paper-gaps/scp10_quantum_double_g_isometry.tex`.

## Main definitions

* `TNLean.PEPS.IsGInjective`: invariance under the virtual representation and injectivity on
  the invariant subspace.
* `TNLean.PEPS.IsGIsometric`: `G`-injectivity with inner products of invariant vectors
  preserved up to a positive scalar.
* `TNLean.PEPS.siteMap`: the map `𝒫(A)` of a site tensor with four virtual legs.

## Main results

* `TNLean.PEPS.isGInjective_iff_exists_leftInverse`: the source's left-inverse formulation.
* `TNLean.PEPS.isGInjective_trivial_iff`: for the trivial representation, `G`-injectivity is
  injectivity.
* `TNLean.PEPS.siteMap_injective_iff`: the map of a site tensor is injective exactly when its
  physical vectors, indexed by virtual configurations, are linearly independent, the
  vertex-wise condition of `TNLean.PEPS.IsVertexInjective`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

section GInjective

variable {G W P : Type*} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]

/-- Source: arXiv:1001.3807, Definition `def:2d-Ug-inj`, `Papers/1001.3807/paper_v3.tex`
lines 1278–1296. The map `T = 𝒫(A)` from the virtual to the physical system is
`G`-injective for the representation `ρ` of `G` on the virtual system if it is invariant
under `ρ` (condition i) and injective on the `ρ`-invariant subspace. For finite `G` the
second clause is the source's condition ii, the existence of a left inverse `L` with
`L 𝒫(A) = Π_U` (`isGInjective_iff_exists_leftInverse`). -/
structure IsGInjective (ρ : Representation ℂ G W) (T : W →ₗ[ℂ] P) : Prop where
  /-- Condition i: `𝒫(A) U_g = 𝒫(A)` for every `g`. -/
  invariant : ∀ g : G, T ∘ₗ ρ g = T
  /-- `𝒫(A)` is injective on the `U_g`-invariant subspace. -/
  injOn_invariants : ∀ x ∈ ρ.invariants, T x = 0 → x = 0

/-- A map invariant under `ρ` is unchanged by the projection `Π_U` onto the invariants. -/
theorem apply_averageMap_of_forall_comp_eq [Fintype G] [Invertible (Fintype.card G : ℂ)]
    {ρ : Representation ℂ G W} {T : W →ₗ[ℂ] P} (hT : ∀ g : G, T ∘ₗ ρ g = T) (v : W) :
    T (ρ.averageMap v) = T v := by
  have h : ∀ g : G, T (ρ g v) = T v := fun g => LinearMap.congr_fun (hT g) v
  simp [GroupAlgebra.average, map_sum, h, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]

/-- Bridge: arXiv:1001.3807, Definition `def:2d-Ug-inj` (ii),
`Papers/1001.3807/paper_v3.tex` lines 1289–1294. For finite `G`, `G`-injectivity is
invariance together with a left inverse `L` of `𝒫(A)` with `L 𝒫(A) = Π_U`, the averaging
projector onto the invariant subspace. -/
theorem isGInjective_iff_exists_leftInverse [Fintype G] [Invertible (Fintype.card G : ℂ)]
    (ρ : Representation ℂ G W) (T : W →ₗ[ℂ] P) :
    IsGInjective ρ T ↔ (∀ g : G, T ∘ₗ ρ g = T) ∧ ∃ L : P →ₗ[ℂ] W, L ∘ₗ T = ρ.averageMap := by
  constructor
  · rintro ⟨hinv, hinj⟩
    refine ⟨hinv, ?_⟩
    have hker : LinearMap.ker (T ∘ₗ ρ.invariants.subtype) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      exact Subtype.ext (hinj x.1 x.2 hx)
    obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective _ hker
    refine ⟨ρ.invariants.subtype ∘ₗ L', LinearMap.ext fun v => ?_⟩
    have h := LinearMap.congr_fun hL' ⟨ρ.averageMap v, ρ.averageMap_invariant v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at h ⊢
    rw [← apply_averageMap_of_forall_comp_eq hinv v, h]
  · rintro ⟨hinv, L, hL⟩
    refine ⟨hinv, fun x hx hTx => ?_⟩
    have h := LinearMap.congr_fun hL x
    rw [LinearMap.comp_apply, hTx, map_zero, ρ.averageMap_id x hx] at h
    exact h.symm

/-- Bridge: for the trivial representation `G`-injectivity is injectivity of `𝒫(A)`, the
injectivity of a PEPS tensor (arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex`
lines 501–507). -/
theorem isGInjective_trivial_iff (T : W →ₗ[ℂ] P) :
    IsGInjective (Representation.trivial ℂ G W) T ↔ Function.Injective T := by
  rw [injective_iff_map_eq_zero]
  constructor
  · exact fun h x hx => h.injOn_invariants x (fun _ => rfl) hx
  · exact fun h => ⟨fun _ => rfl, fun x _ hx => h x hx⟩

end GInjective

section GIsometric

variable {G ι κ : Type*} [Group G] [Fintype ι] [Fintype κ]

/-- Source: arXiv:1001.3807, Definition `def:iso:isopeps`, `Papers/1001.3807/paper_v3.tex`
lines 1692–1697. A `G`-injective map `T = 𝒫(A)` between coordinate spaces is `G`-isometric
if it restricts to a unitary from the invariant subspace onto its range, up to a positive
factor `c`: `⟪T x, T y⟫ = c ⟪x, y⟫` for invariant `x, y`. The factor is a normalization
convention: the source's quantum-double tensor (lines 2906–2911) is `G`-isometric in this
sense with `c = |G|`. The source's requirement that `ρ` be the regular representation is
stated by each instance. -/
structure IsGIsometric (ρ : Representation ℂ G (ι → ℂ)) (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) : Prop
    extends IsGInjective ρ T where
  /-- Inner products of invariant vectors are preserved up to one positive factor. -/
  exists_inner_eq : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ ρ.invariants, ∀ y ∈ ρ.invariants,
    star (T x) ⬝ᵥ T y = (c : ℂ) * (star x ⬝ᵥ y)

end GIsometric

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 501–507 ("the
definition extends directly to PEPS"). The map `𝒫(A) = ∑ A^i_{αβγδ} |i⟩⟨αβγδ|` of a site
tensor `a t r b l i` with four virtual legs, from the virtual system to the physical one. -/
def siteMap {V Phys : Type*} [Fintype V] (a : V → V → V → V → Phys → ℂ) :
    ((V × V × V × V) → ℂ) →ₗ[ℂ] (Phys → ℂ) :=
  Matrix.mulVecLin (Matrix.of fun (i : Phys) (c : V × V × V × V) =>
    a c.1 c.2.1 c.2.2.1 c.2.2.2 i)

theorem siteMap_apply {V Phys : Type*} [Fintype V] (a : V → V → V → V → Phys → ℂ)
    (x : (V × V × V × V) → ℂ) (i : Phys) :
    siteMap a x i = ∑ c : V × V × V × V, a c.1 c.2.1 c.2.2.1 c.2.2.2 i * x c := by
  simp [siteMap, Matrix.mulVec, dotProduct]

/-- Bridge: the map `𝒫(A)` of a site tensor is injective exactly when the physical vectors
`i ↦ a t r b l i`, indexed by the virtual configurations `(t, r, b, l)`, are linearly
independent. This is the vertex-wise condition of `TNLean.PEPS.IsVertexInjective`. -/
theorem siteMap_injective_iff {V Phys : Type*} [Fintype V] (a : V → V → V → V → Phys → ℂ) :
    Function.Injective (siteMap a) ↔
      LinearIndependent ℂ fun c : V × V × V × V => a c.1 c.2.1 c.2.2.1 c.2.2.2 :=
  Matrix.mulVec_injective_iff

end PEPS
end TNLean
