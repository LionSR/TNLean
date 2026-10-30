/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.VaryingOBCIntersection
import TNLean.Algebra.EuclideanExtendByZero
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Embedding.Basic

/-!
# Physical embeddings of rectangular open-chain families

Different consecutive blocks may have different physical dimensions. Embedding
each finite alphabet into a common alphabet and extending its matrices by zero
preserves both its rectangular span and its canonical row identity. The same
extension on physical vectors is an isometry, including on dependent products
of site alphabets. For a pair of independently embedded alphabets, its actual
boundary range and complementary parent projector intertwine with this isometry.

These are transport identities for the site-dependent physical spaces in
PGVWC07, arXiv:quant-ph/0608197, Theorem 9, source lines 1195–1220. They do not
assume or assert a full-chain Hamiltonian identification after embedding.
-/

open scoped BigOperators Matrix

namespace Matrix

/-- A finite family of physical alphabets embeds into the single alphabet whose
dimension is their sum. This is derived from finiteness, not supplied as a
restriction on the differently sized blocks in PGVWC07, Theorem 9. -/
noncomputable def commonPhysicalEmbedding {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (i : ι) : Fin (q i) ↪ Fin (∑ j, q j) := by
  classical
  exact Fin.castLEEmb (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (q j)) (Finset.mem_univ i))

/-- The actual dependent configuration space of differently sized physical sites
embeds isometrically into a common-alphabet chain by extension by zero.
Source: PGVWC07, arbitrary consecutive blocking before Theorem 9, lines 1195–1201. -/
noncomputable def commonPhysicalConfigurationIsometry {ι : Type*} [Fintype ι]
    [DecidableEq ι] (q : ι → ℕ) : EuclideanSpace ℂ ((i : ι) → Fin (q i)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ι → Fin (∑ j, q j)) :=
  (Function.Embedding.piCongrRight (commonPhysicalEmbedding q)).euclideanExtendByZero

/-- Every actual physical coefficient is preserved by the full configuration
embedding, without a dimension-dependent factor. -/
@[simp] theorem commonPhysicalConfigurationIsometry_apply_image
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℕ)
    (v : EuclideanSpace ℂ ((i : ι) → Fin (q i))) (σ : (i : ι) → Fin (q i)) :
    commonPhysicalConfigurationIsometry q v (fun i ↦ commonPhysicalEmbedding q i (σ i)) =
      v σ :=
  (Function.Embedding.piCongrRight (commonPhysicalEmbedding q)).euclideanExtendByZero_apply_image
    v σ

variable {I J K L a b c : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [Fintype a] [Fintype b] [Fintype c]

omit [Fintype I] [Fintype J] [Fintype a] [Fintype b] in
/-- Extending a physical matrix family by zero preserves its actual rectangular
span, hence its C1 condition. Source: PGVWC07, Theorem 9, lines 1199–1201. -/
theorem span_range_extend_physical (e : I ↪ J) (A : I → Matrix a b ℂ) :
    Submodule.span ℂ (Set.range (Function.extend e A 0)) =
      Submodule.span ℂ (Set.range A) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [e.injective.extend_apply]
      exact Submodule.subset_span (Set.mem_range_self i)
    · rw [Function.extend_apply' (f := ⇑e) A 0 j hj]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← e.injective.extend_apply A 0 i]
    exact Submodule.subset_span (Set.mem_range_self (e i))

omit [Fintype a] in
/-- Extension by zero preserves the canonical row sum exactly, without a
dimension or normalization factor. Source: PGVWC07, Theorem 9 proof,
canonical row identity at lines 1224–1229. -/
theorem sum_mul_conjTranspose_extend_physical (e : I ↪ J) (A : I → Matrix a b ℂ) :
    ∑ j, Function.extend e A 0 j * (Function.extend e A 0 j)ᴴ =
      ∑ i, A i * (A i)ᴴ := by
  classical
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    rw [Function.extend_apply' (f := ⇑e) A 0 j hj]
    simp
  · intro i
    rw [e.injective.extend_apply]

/-- The actual two-site rectangular boundary map, allowing independent physical
alphabets at its two sites. Source: PGVWC07, Theorem 9, lines 1201–1205. -/
noncomputable def rectangularPairBoundary (A : I → Matrix a b ℂ) (B : K → Matrix b c ℂ) :
    Matrix c a ℂ →ₗ[ℂ] EuclideanSpace ℂ (I × K) :=
  (WithLp.linearEquiv 2 ℂ ((I × K) → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun ik ↦ (Matrix.traceLinearMap c ℂ ℂ).comp
      (_root_.mulRightLinearMap c ℂ (A ik.1 * B ik.2)))

omit [Fintype I] [Fintype K] in
/-- Coordinates of the rectangular pair boundary map are two-site traces.
Source: PGVWC07, Theorem 9, lines 1201–1205. -/
theorem rectangularPairBoundary_apply (A : I → Matrix a b ℂ) (B : K → Matrix b c ℂ)
    (X : Matrix c a ℂ) (ik : I × K) :
    rectangularPairBoundary A B X ik = Matrix.trace (X * (A ik.1 * B ik.2)) := by
  simp [rectangularPairBoundary, Matrix.mul_assoc]

omit [Fintype I] [Fintype J] [Fintype K] [Fintype L] in
private theorem extend_rectangular_pair_coefficients
    (e : I ↪ J) (f : K ↪ L) (A : I → Matrix a b ℂ) (B : K → Matrix b c ℂ)
    (X : Matrix c a ℂ) (j : J) (l : L) :
    Function.extend (e.prodMap f)
      (fun ik ↦ Matrix.trace (X * (A ik.1 * B ik.2))) 0 (j, l) =
      Matrix.trace (X * (Function.extend e A 0 j * Function.extend f B 0 l)) := by
  classical
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    by_cases hl : ∃ k, f k = l
    · obtain ⟨k, rfl⟩ := hl
      rw [e.injective.extend_apply, f.injective.extend_apply]
      exact (e.prodMap f).injective.extend_apply _ (0 : J × L → ℂ) (i, k)
    · have hp : ¬ ∃ ik, e.prodMap f ik = (e i, l) := by
        rintro ⟨⟨i', k⟩, h⟩
        exact hl ⟨k, congrArg Prod.snd h⟩
      rw [Function.extend_apply' _ _ _ hp, Function.extend_apply' (f := ⇑f) B 0 l hl]
      simp
  · have hp : ¬ ∃ ik, e.prodMap f ik = (j, l) := by
      rintro ⟨⟨i, k⟩, h⟩
      exact hj ⟨i, congrArg Prod.fst h⟩
    rw [Function.extend_apply' _ _ _ hp, Function.extend_apply' (f := ⇑e) A 0 j hj]
    simp

/-- The pair boundary range of the zero-extended families is exactly the
isometric image of the original range. No full-matrix span is assumed.
Source: PGVWC07, Theorem 9, actual pair spaces at lines 1201–1205. -/
theorem range_rectangularPairBoundary_extend_physical
    (e : I ↪ J) (f : K ↪ L) (A : I → Matrix a b ℂ) (B : K → Matrix b c ℂ) :
    LinearMap.range (rectangularPairBoundary (Function.extend e A 0) (Function.extend f B 0)) =
      (LinearMap.range (rectangularPairBoundary A B)).map
        (e.prodMap f).euclideanExtendByZero.toLinearMap := by
  rw [← LinearMap.range_comp]
  congr 1
  ext X ⟨j, l⟩
  change rectangularPairBoundary _ _ X (j, l) =
    Function.extend (e.prodMap f) (fun ik ↦ rectangularPairBoundary A B X ik) 0 (j, l)
  simp only [rectangularPairBoundary_apply]
  exact (extend_rectangular_pair_coefficients e f A B X j l).symm

private theorem starProjection_eq_of_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] {K₁ K₂ : Submodule ℂ F}
    [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection]
    (h : K₁ = K₂) (x : F) : K₁.starProjection x = K₂.starProjection x := by
  subst h
  rfl

/-- The actual complementary pair projectors intertwine with the physical
embedding, even when the two physical alphabets have different sizes.
Source: PGVWC07, Theorem 9, lines 1201–1217. -/
theorem pair_parent_projection_extend_physical
    (e : I ↪ J) (f : K ↪ L) (A : I → Matrix a b ℂ) (B : K → Matrix b c ℂ)
    (v : EuclideanSpace ℂ (I × K)) :
    (LinearMap.range
      (rectangularPairBoundary (Function.extend e A 0) (Function.extend f B 0)))ᗮ.starProjection
        ((e.prodMap f).euclideanExtendByZero v) =
      (e.prodMap f).euclideanExtendByZero
        ((LinearMap.range (rectangularPairBoundary A B))ᗮ.starProjection v) := by
  set E := (e.prodMap f).euclideanExtendByZero
  set G := LinearMap.range (rectangularPairBoundary A B)
  have hrange := range_rectangularPairBoundary_extend_physical e f A B
  calc
    _ = (G.map E.toLinearMap)ᗮ.starProjection (E v) :=
      starProjection_eq_of_eq (congrArg (fun S : Submodule ℂ _ ↦ Sᗮ) hrange) (E v)
    _ = E v - (G.map E.toLinearMap).starProjection (E v) := by
      rw [Submodule.starProjection_orthogonal_val]
    _ = E (v - G.starProjection v) := by
      rw [map_sub, E.map_starProjection G v]
    _ = E (Gᗮ.starProjection v) := by
      rw [Submodule.starProjection_orthogonal_val]

end Matrix
