/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalSectorKernelSupport
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorPhysicalEmbedding

/-!
# Actual parent projectors on disjoint physical sectors

Disjoint one-letter embeddings give orthogonal physical word sectors at every
positive length. The complementary projection of the sum of two embedded local
spaces therefore restricts to the original complementary projection on each
sector. The statements use the actual embedded spaces and their projections;
no whole-kernel decomposition or dynamical supplier is assumed.

Source context: the physical-sector construction for the finite-prefix
investigation of SPWC10, arXiv:0909.5347, Theorem 5, lines 850–880.
-/

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
    (S.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
        .euclideanExtendByZero.toLinearMap ⊔
      T.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
        .euclideanExtendByZero.toLinearMap)ᗮ.starProjection
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
    le_sup_left (Submodule.mem_map.mpr ⟨S.starProjection v, S.starProjection_apply_mem v, rfl⟩)
  have hres : E v - E (S.starProjection v) ∈ Kᗮ := by
    rw [← E.map_sub, ← Submodule.inf_orthogonal]
    constructor
    · apply (Submodule.mem_orthogonal _ _).mpr
      rintro _ ⟨x, hx, rfl⟩
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

private theorem periodicLocalInteractionES_extend_physical
    (e : Fin a ↪ Fin d) (hRM : R ≤ M)
    (G : MPVSpace a R →ₗ[ℂ] MPVSpace a R)
    (H : MPVSpace d R →ₗ[ℂ] MPVSpace d R)
    (h : ∀ v, H ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
        .euclideanExtendByZero v) =
      (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero (G v))
    (i : Fin M) (v : MPVSpace a M) :
    periodicLocalInteractionES H i
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v) =
      (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
        (periodicLocalInteractionES G i v) := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRM i
  let V := cyclicActiveBlockConfigLinearIsometryEquiv a R hRM i
  let E := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
  let F := ((Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).prodMap
    (Function.Embedding.piCongrRight (fun _ : Fin (M - R) ↦ e))).euclideanExtendByZero
  have hcoord (x : MPVSpace a M) : U (E x) = F (V x) :=
    physical_embedding_cyclic_active_block e hRM i x
  apply U.injective
  calc
    U (periodicLocalInteractionES H i (E v)) =
        ContinuousLinearMap.rightFiberwiseMap (LinearMap.toContinuousLinearMap H) (U (E v)) :=
      cyclicActiveBlock_periodicLocalInteractionES_apply H hRM i (E v)
    _ = ContinuousLinearMap.rightFiberwiseMap (LinearMap.toContinuousLinearMap H) (F (V v)) :=
      congrArg _ (hcoord v)
    _ = F (ContinuousLinearMap.rightFiberwiseMap (LinearMap.toContinuousLinearMap G) (V v)) :=
      ContinuousLinearMap.rightFiberwiseMap_extendByZero _ _ _ _ h (V v)
    _ = F (V (periodicLocalInteractionES G i v)) :=
      congrArg F (cyclicActiveBlock_periodicLocalInteractionES_apply G hRM i v).symm
    _ = U (E (periodicLocalInteractionES G i v)) := (hcoord _).symm

/-- The actual periodic Hamiltonian of the complementary projection of two
embedded sector spaces intertwines with the actual first-sector parent sum.
The local covariance is derived from the spaces themselves, not assumed.
Source: physical-sector assembly for the SPWC10 finite-prefix investigation. -/
theorem physical_sector_projectorHamiltonian_embed
    (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (h : ∀ i j, e i ≠ f j)
    (hR : 0 < R) (hRM : R ≤ M)
    (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (v : MPVSpace a M) :
    periodicInteractionHamiltonianES
        ((S.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
            .euclideanExtendByZero.toLinearMap ⊔
          T.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
            .euclideanExtendByZero.toLinearMap)ᗮ.starProjection.toLinearMap) M
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v) =
      (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
        (periodicInteractionHamiltonianES Sᗮ.starProjection.toLinearMap M v) := by
  simp only [periodicInteractionHamiltonianES, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact periodicLocalInteractionES_extend_physical e hRM _ _
    (physical_sector_parent_projection_embed e f h hR S T) i v

/-- An embedded sector vector is annihilated by the actual combined periodic
parent Hamiltonian exactly when its original vector is annihilated by its own
actual parent sum. The reverse direction uses injectivity of the physical
isometry, rather than an assumed kernel decomposition.
Source: physical-sector assembly for the SPWC10 finite-prefix investigation. -/
theorem physical_sector_projectorHamiltonian_embed_eq_zero_iff
    (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (h : ∀ i j, e i ≠ f j)
    (hR : 0 < R) (hRM : R ≤ M)
    (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (v : MPVSpace a M) :
    periodicInteractionHamiltonianES
        ((S.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
            .euclideanExtendByZero.toLinearMap ⊔
          T.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
            .euclideanExtendByZero.toLinearMap)ᗮ.starProjection.toLinearMap) M
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v) = 0 ↔
      periodicInteractionHamiltonianES Sᗮ.starProjection.toLinearMap M v = 0 := by
  rw [physical_sector_projectorHamiltonian_embed e f h hR hRM S T v]
  let E := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
  exact E.toLinearMap.map_eq_zero_iff E.injective

/-- The actual combined parent annihilates the sum of two sector vectors
exactly when each actual component parent annihilates its own vector. The
component separation is derived from physical orthogonality, not supplied as
a kernel decomposition or an assumed dynamics relation.
Source: physical-sector assembly for the SPWC10 finite-prefix investigation. -/
theorem physical_sector_projectorHamiltonian_sum_eq_zero_iff
    (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (h : ∀ i j, e i ≠ f j)
    (hR : 0 < R) (hRM : R ≤ M)
    (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (v : MPVSpace a M) (w : MPVSpace b M) :
    periodicInteractionHamiltonianES
        ((S.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
            .euclideanExtendByZero.toLinearMap ⊔
          T.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
            .euclideanExtendByZero.toLinearMap)ᗮ.starProjection.toLinearMap) M
        ((Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero v +
          (Function.Embedding.piCongrRight (fun _ : Fin M ↦ f)).euclideanExtendByZero w) = 0 ↔
      periodicInteractionHamiltonianES Sᗮ.starProjection.toLinearMap M v = 0 ∧
        periodicInteractionHamiltonianES Tᗮ.starProjection.toLinearMap M w = 0 := by
  let E := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
  let F := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ f)).euclideanExtendByZero
  let H := periodicInteractionHamiltonianES
    ((S.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e))
        .euclideanExtendByZero.toLinearMap ⊔
      T.map (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f))
        .euclideanExtendByZero.toLinearMap)ᗮ.starProjection.toLinearMap) M
  let G := periodicInteractionHamiltonianES Sᗮ.starProjection.toLinearMap M
  let K := periodicInteractionHamiltonianES Tᗮ.starProjection.toLinearMap M
  have hE : H (E v) = E (G v) := physical_sector_projectorHamiltonian_embed e f h hR hRM S T v
  have hF : H (F w) = F (K w) := by
    simpa only [sup_comm] using physical_sector_projectorHamiltonian_embed f e
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
