/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Interaction.PhysicalSectorKernelSupport
import QICLean.Analysis.TensorProduct.EuclideanExtendByZero

/-!
# Actual parent projectors on disjoint physical sectors

Disjoint one-letter embeddings give orthogonal physical word sectors at every
positive length. The complementary projection of the sum of two embedded local
spaces therefore restricts to the original complementary projection on each
sector. The statements use the actual embedded spaces and their projections;
no whole-kernel decomposition or dynamical supplier is assumed.

Source context: the physical-sector construction for the finite-prefix
investigation of SPWC10, arXiv:0909.5347, Theorem 5, lines 850–880.

## The full kernel of a two-sector periodic projector Hamiltonian

For two local spaces on disjoint exhaustive physical alphabets, the actual
periodic complementary-projector kernel is exactly the sum of the embedded
component kernels. Mixed-sector exclusion supplies an actual state
decomposition, and orthogonal component dynamics supplies the two kernel
equations. Neither conclusion is assumed as an extra hypothesis.

This is the physical-sector assembly in the finite-prefix investigation of
SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880. The result applies to
arbitrary local spaces, not to an assumed classification of a particular model.

It also contains the following results.

* `MPSTensor.physical_sum_state_decomposition`,
  `MPSTensor.physical_sum_state_decomposition_of_translationInvariant_projector_eq_zero`:
  decomposing physical-sector ground vectors.
-/

section PhysicalSectorStateDecomposition

/-!
## Decomposing physical-sector ground vectors

A vector whose mixed-alphabet coefficients vanish is exactly the sum of the
extensions of its two actual coefficient restrictions. Applied to the periodic
complementary projector of two embedded local spaces, mixed-coefficient
vanishing is derived from the Hamiltonian equation. No state decomposition or
component-state supplier is assumed.

This supplies physical-sector assembly for the finite-prefix investigation of
SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880. It does not identify the
component Hamiltonian kernels or assert a full source counterexample.
-/

namespace MPSTensor

variable {a b M : ℕ}

private theorem mem_castAdd_word_range_iff (σ : Cfg (a + b) M) :
    σ ∈ Set.range (Function.Embedding.piCongrRight
      (fun _ : Fin M ↦ (Fin.castAddEmb b : Fin a ↪ Fin (a + b)))) ↔
      ∀ i, (σ i).val < a := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact (w i).isLt
  · intro hσ
    refine ⟨fun i ↦ ⟨(σ i).val, hσ i⟩, ?_⟩
    funext i
    apply Fin.ext
    rfl

private theorem mem_natAdd_word_range_iff (σ : Cfg (a + b) M) :
    σ ∈ Set.range (Function.Embedding.piCongrRight
      (fun _ : Fin M ↦ (Fin.natAddEmb a : Fin b ↪ Fin (a + b)))) ↔
      ∀ i, a ≤ (σ i).val := by
  constructor
  · rintro ⟨w, rfl⟩ i
    change a ≤ a + (w i).val
    omega
  · intro hσ
    refine ⟨fun i ↦ ⟨(σ i).val - a, by have := (σ i).isLt; have := hσ i; omega⟩, ?_⟩
    funext i
    apply Fin.ext
    change a + ((σ i).val - a) = (σ i).val
    have := hσ i
    omega

/-- A vector supported on the two pure physical alphabets is the sum of the
extensions of its actual coefficient restrictions, without scalar or dimension
factors. The positive chain length makes the two word images disjoint.
Source: physical-sector assembly for SPWC10, Theorem 5, lines 850--880. -/
theorem physical_sum_state_decomposition (hM : 0 < M) (ψ : MPVSpace (a + b) M)
    (hψ : ∀ (σ : Cfg (a + b) M) (i j : Fin M),
      (σ i).val < a → a ≤ (σ j).val → ψ σ = 0) :
    ψ = Function.Embedding.euclideanExtendByZero
          (Function.Embedding.piCongrRight (fun _ : Fin M ↦ Fin.castAddEmb b))
          (WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.castAdd b (w i))) +
      Function.Embedding.euclideanExtendByZero
          (Function.Embedding.piCongrRight (fun _ : Fin M ↦ Fin.natAddEmb a))
          (WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.natAdd a (w i))) := by
  classical
  let E := Function.Embedding.piCongrRight
    (fun _ : Fin M ↦ (Fin.castAddEmb b : Fin a ↪ Fin (a + b)))
  let F := Function.Embedding.piCongrRight
    (fun _ : Fin M ↦ (Fin.natAddEmb a : Fin b ↪ Fin (a + b)))
  let x : MPVSpace a M := WithLp.toLp 2 fun w ↦ ψ (E w)
  let y : MPVSpace b M := WithLp.toLp 2 fun w ↦ ψ (F w)
  change ψ = E.euclideanExtendByZero x + F.euclideanExtendByZero y
  apply PiLp.ext
  intro σ
  change ψ σ = E.euclideanExtendByZero x σ + F.euclideanExtendByZero y σ
  by_cases hE : σ ∈ Set.range E
  · obtain ⟨w, rfl⟩ := hE
    have hF : E w ∉ Set.range F := by
      rintro ⟨v, hv⟩
      have hval := congrArg (fun z : Cfg (a + b) M ↦ (z ⟨0, hM⟩).val) hv
      change a + (v ⟨0, hM⟩).val = (w ⟨0, hM⟩).val at hval
      have hw := (w ⟨0, hM⟩).isLt
      omega
    calc
      ψ (E w) = x w := rfl
      _ = E.euclideanExtendByZero x (E w) + F.euclideanExtendByZero y (E w) := by
        rw [E.euclideanExtendByZero_apply_image,
          F.euclideanExtendByZero_apply_not_mem_range y _ hF, add_zero]
  · by_cases hF : σ ∈ Set.range F
    · obtain ⟨w, rfl⟩ := hF
      calc
        ψ (F w) = y w := rfl
        _ = E.euclideanExtendByZero x (F w) + F.euclideanExtendByZero y (F w) := by
          rw [E.euclideanExtendByZero_apply_not_mem_range x _ hE,
            F.euclideanExtendByZero_apply_image, zero_add]
    · have hnot_left : ¬ ∀ i, (σ i).val < a := by
        intro h
        exact hE ((mem_castAdd_word_range_iff σ).mpr h)
      have hnot_right : ¬ ∀ i, a ≤ (σ i).val := by
        intro h
        exact hF ((mem_natAdd_word_range_iff σ).mpr h)
      push Not at hnot_left hnot_right
      obtain ⟨j, hj⟩ := hnot_left
      obtain ⟨i, hi⟩ := hnot_right
      rw [E.euclideanExtendByZero_apply_not_mem_range x _ hE,
        F.euclideanExtendByZero_apply_not_mem_range y _ hF, zero_add]
      exact hψ σ i j hi hj

/-! ### The translation-invariant interaction of the complementary projection -/

/-- Every vector annihilated by the operator of the Hamiltonian of the translation-invariant
interaction of the two-sector complementary projection splits into the extensions of its actual
sector coefficient restrictions. Mixed coefficients are derived from the Hamiltonian equation
rather than supplied.
Source: physical-sector assembly for SPWC10, Theorem 5, lines 850--880. -/
theorem physical_sum_state_decomposition_of_translationInvariant_projector_eq_zero
    {R : ℕ} (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (hR : 2 ≤ R) (hRM : R ≤ M) (ψ : MPVSpace (a + b) M)
    (hzero : haveI : NeZero M := ⟨by omega⟩;
      Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
      (Matrix.toEuclideanLin.symm
        ((S.map
            (Function.Embedding.piCongrRight
              (fun _ : Fin R ↦ Fin.castAddEmb b)).euclideanExtendByZero.toLinearMap ⊔
          T.map
            (Function.Embedding.piCongrRight
              (fun _ : Fin R ↦ Fin.natAddEmb a)).euclideanExtendByZero.toLinearMap)ᗮ
          |>.starProjection.toLinearMap))).hamiltonian ψ = 0) :
    ψ = Function.Embedding.euclideanExtendByZero
          (Function.Embedding.piCongrRight (fun _ : Fin M ↦ Fin.castAddEmb b))
          (WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.castAdd b (w i))) +
      Function.Embedding.euclideanExtendByZero
          (Function.Embedding.piCongrRight (fun _ : Fin M ↦ Fin.natAddEmb a))
          (WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.natAdd a (w i))) := by
  have : NeZero M := ⟨by omega⟩
  apply physical_sum_state_decomposition (by omega) ψ
  intro σ i j hi hj
  exact coeff_eq_zero_of_physical_sum_translationInvariant_projector S T hR hRM ψ hzero σ i j
    hi hj

end MPSTensor

end PhysicalSectorStateDecomposition

section PhysicalSectorProjectorTransport

section

open scoped InnerProductSpace BigOperators

namespace Function.Embedding

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- Extensions from disjoint coordinate ranges are orthogonal, with no
normalization factor. This is the finite Euclidean orthogonality used by
physical-sector sums in SPWC10's finite-prefix investigation. -/
theorem inner_extendByZero_eq_zero_of_disjoint (e : I ↪ K) (f : J ↪ K)
    (h : Disjoint (Set.range e) (Set.range f))
    (x : EuclideanSpace ℂ I) (y : EuclideanSpace ℂ J) :
    ⟪e.euclideanExtendByZero x, f.euclideanExtendByZero y⟫_ℂ = 0 := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ k, f.euclideanExtendByZero y k * star (e.euclideanExtendByZero x k)) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ∈ Set.range e
  · have hfk : k ∉ Set.range f := fun hf ↦ Set.disjoint_left.mp h hk hf
    rw [euclideanExtendByZero_apply_not_mem_range f y k hfk, zero_mul]
  · rw [euclideanExtendByZero_apply_not_mem_range e x k hk, star_zero, mul_zero]

private theorem euclideanExtendByZero_reindex
    {I' J' : Type*} [Fintype I'] [Fintype J']
    (e : I ↪ J) (f : I' ↪ J') (s : I ≃ I') (t : J ≃ J')
    (h : ∀ i, t (e i) = f (s i)) (v : EuclideanSpace ℂ I) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ t (e.euclideanExtendByZero v) =
      f.euclideanExtendByZero (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s v) := by
  classical
  ext j
  change e.euclideanExtendByZero v (t.symm j) =
    f.euclideanExtendByZero (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s v) j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    have hpre : t.symm (f i) = e (s.symm i) := by
      apply t.injective
      rw [t.apply_symm_apply, h, s.apply_symm_apply]
    calc
      e.euclideanExtendByZero v (t.symm (f i)) = v (s.symm i) := by
        rw [hpre, euclideanExtendByZero_apply_image]
      _ = f.euclideanExtendByZero
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s v) (f i) :=
        (euclideanExtendByZero_apply_image f
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s v) i).symm
  · have hpre : t.symm j ∉ Set.range e := by
      rintro ⟨i, hi⟩
      apply hj
      refine ⟨s i, ?_⟩
      rw [← h, hi, t.apply_symm_apply]
    rw [euclideanExtendByZero_apply_not_mem_range _ _ _ hpre,
      euclideanExtendByZero_apply_not_mem_range _ _ _ hj]

end Function.Embedding

namespace MPSTensor

variable {a b d R M : ℕ}

/-- Disjoint letter embeddings have disjoint word ranges at every positive
length. No coordinate label or support assumption is supplied.
Source: physical-sector separation in the SPWC10 finite-prefix investigation. -/
theorem disjoint_physical_word_ranges (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d)
    (h : ∀ i j, e i ≠ f j) (hR : 0 < R) :
    Disjoint
      (Set.range (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)))
      (Set.range (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
  exact h (u ⟨0, hR⟩) (v ⟨0, hR⟩) ((congrFun hv ⟨0, hR⟩).symm)

/-- The actual complementary parent projection of two disjoint embedded local
spaces restricts to the original complementary projection on the first sector.
Source: orthogonal physical-sector sums in the SPWC10 finite-prefix investigation. -/
theorem physical_sector_parent_projection_embed
    (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (h : ∀ i j, e i ≠ f j)
    (hR : 0 < R) (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (v : MPVSpace a R) :
    (S.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
        |>.euclideanExtendByZero.toLinearMap) ⊔
      T.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
        |>.euclideanExtendByZero.toLinearMap))ᗮ.starProjection
      ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero v) =
    (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero
      (Sᗮ.starProjection v) := by
  let E := (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero
  let F := (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f)).euclideanExtendByZero
  let U := S.map E.toLinearMap
  let V := T.map F.toLinearMap
  let K := U ⊔ V
  have horth (x : MPVSpace a R) (y : MPVSpace b R) : ⟪E x, F y⟫_ℂ = 0 :=
    Function.Embedding.inner_extendByZero_eq_zero_of_disjoint _ _
      (disjoint_physical_word_ranges e f h hR) x y
  have hmem : E (S.starProjection v) ∈ K :=
    Submodule.mem_sup_left
      (Submodule.mem_map.mpr ⟨S.starProjection v, S.starProjection_apply_mem v, rfl⟩)
  have hres : E v - E (S.starProjection v) ∈ Kᗮ := by
    rw [← E.map_sub, ← Submodule.inf_orthogonal]
    constructor
    · apply (Submodule.mem_orthogonal _ _).mpr
      rintro _ ⟨x, hx, rfl⟩
      change ⟪E x, E (v - S.starProjection v)⟫_ℂ = 0
      rw [E.inner_map_map]
      exact (Submodule.mem_orthogonal _ _).mp (S.sub_starProjection_mem_orthogonal v) x hx
    · apply (Submodule.mem_orthogonal _ _).mpr
      rintro _ ⟨y, _, rfl⟩
      exact inner_eq_zero_symm.mpr (horth (v - S.starProjection v) y)
  have hproj : K.starProjection (E v) = E (S.starProjection v) :=
    Submodule.eq_starProjection_of_mem_orthogonal hmem hres
  change Kᗮ.starProjection (E v) = E (Sᗮ.starProjection v)
  rw [Submodule.starProjection_orthogonal' K, Submodule.starProjection_orthogonal' S]
  change E v - K.starProjection (E v) = E (v - S.starProjection v)
  rw [hproj, map_sub]

private theorem physical_embedding_cyclic_active_block
    (e : Fin a ↪ Fin d) (hRM : R ≤ M) (i : Fin M) (v : MPVSpace a M) :
    cyclicActiveBlockConfigLinearIsometryEquiv d R hRM i
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v) =
      ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).prodMap
        (Function.Embedding.piCongrRight (fun _ : Fin (M - R) ↦ e))).euclideanExtendByZero
          (cyclicActiveBlockConfigLinearIsometryEquiv a R hRM i v) := by
  apply Function.Embedding.euclideanExtendByZero_reindex
  intro σ
  apply Prod.ext <;> funext j <;> rfl

/-! ### The translation-invariant interaction of the complementary projections

The Hamiltonian of the translation-invariant interaction on the ring of the matrix of each
complementary projection; statements about vectors take its operator
`Matrix.toEuclideanLin`. -/

private theorem toEuclideanLin_translationInvariant_term_extend_physical
    (e : Fin a ↪ Fin d) (hRM : R ≤ M)
    (G : Matrix (Cfg a R) (Cfg a R) ℂ) (H : Matrix (Cfg d R) (Cfg d R) ℂ)
    (h : ∀ v, Matrix.toEuclideanLin H ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
        |>.euclideanExtendByZero v) =
      (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero
        (Matrix.toEuclideanLin G v))
    (i : Fin M) (v : MPVSpace a M) :
    haveI : NeZero M := NeZero.of_pos i.pos;
    Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant M H).term i)
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v) =
      (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
        (Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant M G).term i) v) := by
  have : NeZero M := NeZero.of_pos i.pos
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRM i
  let V := cyclicActiveBlockConfigLinearIsometryEquiv a R hRM i
  let E := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
  let F := ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).prodMap
    (Function.Embedding.piCongrRight (fun _ : Fin (M - R) ↦ e))).euclideanExtendByZero
  have hcoord (x : MPVSpace a M) : U (E x) = F (V x) :=
    physical_embedding_cyclic_active_block e hRM i x
  apply U.injective
  calc
    U (Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant M H).term i) (E v)) =
        ContinuousLinearMap.rightFiberwiseMap
          (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin H)) (U (E v)) :=
      cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply hRM H i (E v)
    _ = ContinuousLinearMap.rightFiberwiseMap
          (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin H)) (F (V v)) :=
      congrArg _ (hcoord v)
    _ = F (ContinuousLinearMap.rightFiberwiseMap
          (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G)) (V v)) :=
      ContinuousLinearMap.rightFiberwiseMap_extendByZero _ _ _ _ h (V v)
    _ = F (V (Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant M G).term i)
          v)) :=
      congrArg F (cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply hRM G i v).symm
    _ = U (E (Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant M G).term i)
          v)) := (hcoord _).symm

/-- The periodic Hamiltonian of the complementary projection of two embedded sector spaces
intertwines with the first-sector Hamiltonian: the Hamiltonian of the translation-invariant
interaction of the matrix of the combined complementary projection, applied to an embedded
vector, is the embedding of the Hamiltonian of the first sector's complementary projection.
The local covariance is derived from the spaces themselves, not assumed.
Source: physical-sector assembly for the SPWC10 finite-prefix investigation. -/
theorem physical_sector_hamiltonian_translationInvariant_embed
    (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (h : ∀ i j, e i ≠ f j)
    (hR : 0 < R) (hRM : R ≤ M)
    (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (v : MPVSpace a M) :
    haveI : NeZero M := ⟨by omega⟩;
    Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
        (Matrix.toEuclideanLin.symm
          ((S.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
              |>.euclideanExtendByZero.toLinearMap) ⊔
            T.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
              |>.euclideanExtendByZero.toLinearMap))ᗮ.starProjection.toLinearMap))).hamiltonian
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v) =
      (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
        (Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
          (Matrix.toEuclideanLin.symm Sᗮ.starProjection.toLinearMap)).hamiltonian v) := by
  have : NeZero M := ⟨by omega⟩
  simp only [ManyBody.Interaction.hamiltonian, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦
    toEuclideanLin_translationInvariant_term_extend_physical e hRM _ _ (fun w ↦ ?_) i v
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact physical_sector_parent_projection_embed e f h hR S T w

/-- An embedded sector vector is annihilated by the combined periodic parent Hamiltonian exactly
when its original vector is annihilated by its own parent Hamiltonian; both are the
Hamiltonians of the translation-invariant interactions of the matrices of the complementary
projections. The reverse direction uses injectivity of the physical isometry, rather than an
assumed kernel decomposition.
Source: physical-sector assembly for the SPWC10 finite-prefix investigation. -/
theorem physical_sector_hamiltonian_translationInvariant_embed_eq_zero_iff
    (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (h : ∀ i j, e i ≠ f j)
    (hR : 0 < R) (hRM : R ≤ M)
    (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (v : MPVSpace a M) :
    haveI : NeZero M := ⟨by omega⟩;
    Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
        (Matrix.toEuclideanLin.symm
          ((S.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
              |>.euclideanExtendByZero.toLinearMap) ⊔
            T.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
              |>.euclideanExtendByZero.toLinearMap))ᗮ.starProjection.toLinearMap))).hamiltonian
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v) = 0 ↔
      Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
        (Matrix.toEuclideanLin.symm Sᗮ.starProjection.toLinearMap)).hamiltonian v = 0 := by
  have : NeZero M := ⟨by omega⟩
  rw [physical_sector_hamiltonian_translationInvariant_embed e f h hR hRM S T v]
  let E := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
  exact E.toLinearMap.map_eq_zero_iff E.injective

/-- The combined periodic parent Hamiltonian annihilates the sum of two sector vectors exactly
when each component parent Hamiltonian annihilates its own vector; all three are the
Hamiltonians of the translation-invariant interactions of the matrices of the complementary
projections. The component separation is derived from physical orthogonality, not supplied as
a kernel decomposition or an assumed dynamics relation.
Source: physical-sector assembly for the SPWC10 finite-prefix investigation. -/
theorem physical_sector_hamiltonian_translationInvariant_sum_eq_zero_iff
    (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (h : ∀ i j, e i ≠ f j)
    (hR : 0 < R) (hRM : R ≤ M)
    (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (v : MPVSpace a M) (w : MPVSpace b M) :
    haveI : NeZero M := ⟨by omega⟩;
    Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
        (Matrix.toEuclideanLin.symm
          ((S.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
              |>.euclideanExtendByZero.toLinearMap) ⊔
            T.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
              |>.euclideanExtendByZero.toLinearMap))ᗮ.starProjection.toLinearMap))).hamiltonian
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v +
          (Function.Embedding.piCongrRight (fun _ : Fin M ↦ f)).euclideanExtendByZero w) = 0 ↔
      Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
          (Matrix.toEuclideanLin.symm Sᗮ.starProjection.toLinearMap)).hamiltonian v = 0 ∧
        Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
          (Matrix.toEuclideanLin.symm Tᗮ.starProjection.toLinearMap)).hamiltonian w = 0 := by
  have : NeZero M := ⟨by omega⟩
  let E := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
  let F := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ f)).euclideanExtendByZero
  let H := Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
    (Matrix.toEuclideanLin.symm
      ((S.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
          |>.euclideanExtendByZero.toLinearMap) ⊔
        T.map ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
          |>.euclideanExtendByZero.toLinearMap))ᗮ.starProjection.toLinearMap))).hamiltonian
  let G := Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
    (Matrix.toEuclideanLin.symm Sᗮ.starProjection.toLinearMap)).hamiltonian
  let K := Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
    (Matrix.toEuclideanLin.symm Tᗮ.starProjection.toLinearMap)).hamiltonian
  have hE : H (E v) = E (G v) :=
    physical_sector_hamiltonian_translationInvariant_embed e f h hR hRM S T v
  have hF : H (F w) = F (K w) := by
    simpa only [sup_comm] using physical_sector_hamiltonian_translationInvariant_embed f e
      (fun j i ↦ (h i j).symm) hR hRM T S w
  change H (E v + F w) = 0 ↔ G v = 0 ∧ K w = 0
  rw [map_add, hE, hF]
  constructor
  · intro hz
    have horth : ⟪E (G v), F (K w)⟫_ℂ = 0 :=
      Function.Embedding.inner_extendByZero_eq_zero_of_disjoint _ _
        (disjoint_physical_word_ranges e f h (hR.trans_le hRM)) (G v) (K w)
    have hn := congrArg (fun x ↦ ⟪E (G v), x⟫_ℂ) hz
    rw [inner_add_right, horth, add_zero, inner_zero_right] at hn
    have hezero : E (G v) = 0 := inner_self_eq_zero.mp hn
    have hfzero : F (K w) = 0 := by simpa only [hezero, zero_add] using hz
    exact ⟨(E.toLinearMap.map_eq_zero_iff E.injective).mp hezero,
      (F.toLinearMap.map_eq_zero_iff F.injective).mp hfzero⟩
  · rintro ⟨hv, hw⟩
    rw [hv, hw, map_zero, map_zero, zero_add]

end MPSTensor

end

section

namespace MPSTensor

/-! ### The translation-invariant interactions of the complementary projections -/

/-- The kernel of the operator of the Hamiltonian of the translation-invariant interaction of
the complementary projection of two embedded local spaces is the sum of the embedded kernels of
the two component Hamiltonians. The physical alphabet split is exhaustive, and the range is at
least two.
Source: physical-sector assembly for the SPWC10 finite-prefix investigation. -/
theorem ker_physical_sum_translationInvariant_projector
    {a b R M : ℕ} (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (hR : 2 ≤ R) (hRM : R ≤ M) :
    haveI : NeZero M := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
      (Matrix.toEuclideanLin.symm
        ((S.map
            (Function.Embedding.piCongrRight
              (fun _ : Fin R ↦ Fin.castAddEmb b)).euclideanExtendByZero.toLinearMap ⊔
          T.map
            (Function.Embedding.piCongrRight
              (fun _ : Fin R ↦ Fin.natAddEmb a)).euclideanExtendByZero.toLinearMap)ᗮ
          |>.starProjection.toLinearMap))).hamiltonian) =
      (LinearMap.ker (Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
        (Matrix.toEuclideanLin.symm Sᗮ.starProjection.toLinearMap)).hamiltonian)).map
        (Function.Embedding.piCongrRight
          (fun _ : Fin M ↦ Fin.castAddEmb b)).euclideanExtendByZero.toLinearMap ⊔
      (LinearMap.ker (Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant M
        (Matrix.toEuclideanLin.symm Tᗮ.starProjection.toLinearMap)).hamiltonian)).map
        (Function.Embedding.piCongrRight
          (fun _ : Fin M ↦ Fin.natAddEmb a)).euclideanExtendByZero.toLinearMap := by
  have : NeZero M := ⟨by omega⟩
  let e : Fin a ↪ Fin (a + b) := Fin.castAddEmb b
  let f : Fin b ↪ Fin (a + b) := Fin.natAddEmb a
  have hdisj (i : Fin a) (j : Fin b) : e i ≠ f j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = a + j.val at hv
    have hi := i.isLt
    omega
  let E := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
  let F := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ f)).euclideanExtendByZero
  ext ψ
  constructor
  · intro hψ
    let x : MPVSpace a M := WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.castAdd b (w i))
    let y : MPVSpace b M := WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.natAdd a (w i))
    have hdecomp : ψ = E x + F y :=
      physical_sum_state_decomposition_of_translationInvariant_projector_eq_zero
        S T hR hRM ψ hψ
    have hcomponents := (physical_sector_hamiltonian_translationInvariant_sum_eq_zero_iff
      e f hdisj (by omega) hRM S T x y).mp (hdecomp ▸ hψ)
    rw [hdecomp]
    exact Submodule.add_mem_sup
      (Submodule.mem_map.mpr ⟨x, hcomponents.1, rfl⟩)
      (Submodule.mem_map.mpr ⟨y, hcomponents.2, rfl⟩)
  · intro hψ
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hψ
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.mp hy
    exact (physical_sector_hamiltonian_translationInvariant_sum_eq_zero_iff e f hdisj
      (by omega) hRM S T x' y').mpr ⟨hx', hy'⟩

end MPSTensor

end

end PhysicalSectorProjectorTransport
