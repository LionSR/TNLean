/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbient
import TNLean.MPS.ParentHamiltonian.Martingale.C3Threshold

/-!
# Spectator transport for the open-chain C3 estimate

This file develops the right-spectator map needed to compare the local-volume
operators in Nachtergaele's condition C3 with the fixed-final-volume filtration.
The norm comparison uses an explicit finite fiber decomposition, never
definitional equality between operators on different Hilbert spaces. The exact
intertwining with the concrete fixed-volume projectors is recorded as the
remaining obstruction in `docs/paper-gaps/cpgsv21_martingale_overlap.tex`.

## References

* Nachtergaele, arXiv:cond-mat/9410110, condition C3, lines 1083--1094.
* Nachtergaele, arXiv:cond-mat/9410110, proof of Theorem 2.1(i), lines 1178--1259.
-/

open scoped BigOperators

namespace MPSTensor

/-- Split a configuration on \(n+r\) sites into its first \(n\) active sites and
its final \(r\) right-spectator sites. -/
def rightSpectatorConfigEquiv (d n r : ℕ) :
    Cfg d (n + r) ≃ Cfg d n × Cfg d r :=
  (Fin.appendEquiv n r).symm

@[simp] theorem rightSpectatorConfigEquiv_symm_apply
    (d n r : ℕ) (p : Cfg d n × Cfg d r) :
    (rightSpectatorConfigEquiv d n r).symm p = Fin.appendEquiv n r p :=
  rfl

@[simp] theorem rightSpectatorConfigEquiv_apply_fst
    (d n r : ℕ) (σ : Cfg d (n + r)) (i : Fin n) :
    (rightSpectatorConfigEquiv d n r σ).1 i = σ (Fin.castAdd r i) :=
  rfl

@[simp] theorem rightSpectatorConfigEquiv_apply_snd
    (d n r : ℕ) (σ : Cfg d (n + r)) (j : Fin r) :
    (rightSpectatorConfigEquiv d n r σ).2 j = σ (Fin.natAdd n j) :=
  rfl

/-- The Euclidean-space reindexing that displays the last \(r\) sites as a
finite right-spectator coordinate. -/
noncomputable def rightSpectatorConfigLinearIsometryEquiv (d n r : ℕ) :
    EuclideanSpace ℂ (Cfg d (n + r)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg d n × Cfg d r) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (rightSpectatorConfigEquiv d n r)

@[simp] theorem rightSpectatorConfigLinearIsometryEquiv_apply_apply
    (d n r : ℕ) (v : EuclideanSpace ℂ (Cfg d (n + r)))
    (p : Cfg d n × Cfg d r) :
    rightSpectatorConfigLinearIsometryEquiv d n r v p =
      v (Fin.appendEquiv n r p) := by
  rw [rightSpectatorConfigLinearIsometryEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

@[simp] theorem rightSpectatorConfigLinearIsometryEquiv_symm_apply_apply
    (d n r : ℕ) (v : EuclideanSpace ℂ (Cfg d n × Cfg d r))
    (σ : Cfg d (n + r)) :
    (rightSpectatorConfigLinearIsometryEquiv d n r).symm v σ =
      v (rightSpectatorConfigEquiv d n r σ) := by
  rw [rightSpectatorConfigLinearIsometryEquiv,
    LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

end MPSTensor

namespace ContinuousLinearMap

variable {I S : Type*} [Fintype I] [Fintype S]

/-- The active-coordinate vector obtained by fixing one right spectator. -/
noncomputable def rightFiber (x : EuclideanSpace ℂ (I × S)) (s : S) :
    EuclideanSpace ℂ I :=
  WithLp.toLp 2 fun i => x (i, s)

/-- Apply the same operator independently at every value of a finite right
spectator coordinate. -/
noncomputable def rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × S) →L[ℂ] EuclideanSpace ℂ (I × S) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun p => G (rightFiber x p.2) p.1
      map_add' := by
        intro x y
        apply PiLp.ext
        rintro ⟨i, s⟩
        change (G (rightFiber (x + y) s)) i = _
        rw [show rightFiber (x + y) s = rightFiber x s + rightFiber y s by
          apply PiLp.ext
          intro j
          rfl, map_add]
        rfl
      map_smul' := by
        intro c x
        apply PiLp.ext
        rintro ⟨i, s⟩
        change (G (rightFiber (c • x) s)) i = _
        rw [show rightFiber (c • x) s = c • rightFiber x s by
          apply PiLp.ext
          intro j
          rfl, map_smul]
        rfl }

@[simp] theorem rightFiberwiseMap_apply_apply
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) (i : I) (s : S) :
    rightFiberwiseMap (S := S) G x (i, s) = G (rightFiber x s) i := rfl

@[simp] theorem rightFiber_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) (s : S) :
    rightFiber (rightFiberwiseMap (S := S) G x) s = G (rightFiber x s) := by
  apply PiLp.ext
  intro i
  rfl

/-- Right-spectator extension preserves addition. -/
theorem rightFiberwiseMap_add
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    rightFiberwiseMap (S := S) (G + H) =
      rightFiberwiseMap (S := S) G + rightFiberwiseMap (S := S) H := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

/-- Right-spectator extension preserves subtraction. -/
theorem rightFiberwiseMap_sub
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    rightFiberwiseMap (S := S) (G - H) =
      rightFiberwiseMap (S := S) G - rightFiberwiseMap (S := S) H := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

@[simp] theorem rightFiberwiseMap_zero :
    rightFiberwiseMap (I := I) (S := S) 0 = 0 := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

/-- A vector lies in the kernel of a fiberwise operator exactly when every
right-spectator fiber lies in the kernel of the base operator. -/
theorem mem_ker_rightFiberwiseMap_iff
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) :
    x ∈ LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap ↔
      ∀ s, rightFiber x s ∈ LinearMap.ker G.toLinearMap := by
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx s
    apply PiLp.ext
    intro i
    have hi := congrArg (fun y : EuclideanSpace ℂ (I × S) => y (i, s)) hx
    exact hi
  · intro hx
    apply PiLp.ext
    rintro ⟨i, s⟩
    change G (rightFiber x s) i = 0
    exact congrArg (fun y : EuclideanSpace ℂ I => y i) (hx s)

/-- Right-spectator extension preserves composition. -/
theorem rightFiberwiseMap_comp
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    (rightFiberwiseMap (S := S) G).comp (rightFiberwiseMap (S := S) H) =
      rightFiberwiseMap (S := S) (G.comp H) := by
  apply ContinuousLinearMap.coe_injective
  apply DFunLike.ext _ _
  intro x
  apply PiLp.ext
  rintro ⟨i, s⟩
  rfl

/-- Fiberwise extension preserves symmetry. -/
theorem isSymmetric_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsSymmetric) :
    (rightFiberwiseMap (S := S) G).toLinearMap.IsSymmetric := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  calc
    ∑ i, ∑ s, inner ℂ (rightFiberwiseMap (S := S) G x (i, s)) (y (i, s)) =
        ∑ s, ∑ i, inner ℂ (G (rightFiber x s) i) (rightFiber y s i) := by
      rw [Finset.sum_comm]
      rfl
    _ = ∑ s, ∑ i, inner ℂ (rightFiber x s i) (G (rightFiber y s) i) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← PiLp.inner_apply, ← PiLp.inner_apply]
      exact hG (rightFiber x s) (rightFiber y s)
    _ = ∑ i, ∑ s, inner ℂ (x (i, s))
        (rightFiberwiseMap (S := S) G y (i, s)) := by
      rw [Finset.sum_comm]
      rfl

/-- Fiberwise extension preserves orthogonal projections. -/
theorem isSymmetricProjection_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsSymmetricProjection) :
    (rightFiberwiseMap (S := S) G).toLinearMap.IsSymmetricProjection := by
  refine ⟨?_, isSymmetric_rightFiberwiseMap G hG.isSymmetric⟩
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨i, s⟩
  change G (G (rightFiber x s)) i = G (rightFiber x s) i
  have hs := LinearMap.congr_fun hG.isIdempotentElem.eq (rightFiber x s)
  exact congrArg (fun y : EuclideanSpace ℂ I => y i) hs

/-- The kernel projection of a fiberwise operator is the fiberwise extension
of the base kernel projection. -/
theorem ker_starProjection_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap).starProjection.toLinearMap =
      (rightFiberwiseMap (S := S)
        (LinearMap.ker G.toLinearMap).starProjection).toLinearMap := by
  let U := LinearMap.ker G.toLinearMap
  apply LinearMap.IsSymmetricProjection.ext
    (Submodule.isSymmetricProjection_starProjection _)
    (isSymmetricProjection_rightFiberwiseMap _
      (Submodule.isSymmetricProjection_starProjection U))
  ext x
  constructor
  · intro hx
    rw [Submodule.range_starProjection] at hx
    refine ⟨x, ?_⟩
    apply PiLp.ext
    rintro ⟨i, s⟩
    change U.starProjection (rightFiber x s) i = x (i, s)
    have hs := (mem_ker_rightFiberwiseMap_iff G x).mp hx s
    exact congrArg (fun y : EuclideanSpace ℂ I => y i)
      (U.starProjection_eq_self_iff.mpr hs)
  · rintro ⟨y, rfl⟩
    rw [Submodule.range_starProjection]
    apply (mem_ker_rightFiberwiseMap_iff G _).mpr
    intro s
    change U.starProjection (rightFiber y s) ∈ U
    exact Submodule.starProjection_apply_mem U _

/-- Right-spectator extension does not increase the operator norm. The statement
also covers an empty spectator type. -/
theorem norm_rightFiberwiseMap_le
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖rightFiberwiseMap (S := S) G‖ ≤ ‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun x ↦ ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg G) (norm_nonneg x)),
    mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ p : I × S, ‖rightFiberwiseMap (S := S) G x p‖ ^ 2 =
        ∑ s, ∑ i, ‖G (rightFiber x s) i‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    _ = ∑ s, ‖G (rightFiber x s)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ s, (‖G‖ * ‖rightFiber x s‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg G) (norm_nonneg _))).mpr (G.le_opNorm _)
    _ = ‖G‖ ^ 2 * ∑ p : I × S, ‖x p‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [mul_pow, EuclideanSpace.norm_sq_eq]
      simp only [rightFiber, Finset.mul_sum]

/-- A vector supported at one right-spectator coordinate. -/
noncomputable def singleRightFiber (s : S) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × S) := by
  classical
  exact WithLp.toLp 2 fun p => if p.2 = s then x p.1 else 0

/-- A vector supported on one spectator fiber has the norm of that fiber. -/
theorem norm_singleRightFiber (s : S) (x : EuclideanSpace ℂ I) :
    ‖singleRightFiber s x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Finset.sum_comm]
  classical
  rw [Finset.sum_eq_single s]
  · simp [singleRightFiber]
  · intro t _ hts
    simp [singleRightFiber, hts]
  · simp

/-- On a nonempty spectator space, right-spectator extension preserves the
operator norm exactly. -/
theorem norm_rightFiberwiseMap [Nonempty S]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖rightFiberwiseMap (S := S) G‖ = ‖G‖ := by
  apply le_antisymm (norm_rightFiberwiseMap_le G)
  let s : S := Classical.choice ‹Nonempty S›
  refine ContinuousLinearMap.opNorm_le_bound G (norm_nonneg _) fun x ↦ ?_
  calc
    ‖G x‖ = ‖rightFiberwiseMap (S := S) G (singleRightFiber s x)‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
        EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_prod_type, Finset.sum_comm]
      classical
      symm
      rw [Finset.sum_eq_single s]
      · simp [singleRightFiber, rightFiber]
      · intro t _ hts
        have hfiber : rightFiber (singleRightFiber s x) t = 0 := by
          apply PiLp.ext
          intro i
          change (if t = s then x i else 0) = 0
          simp [hts]
        have hpoint : ∀ i : I,
            rightFiberwiseMap (S := S) G (singleRightFiber s x) (i, t) = 0 := by
          intro i
          rw [rightFiberwiseMap_apply_apply, hfiber, map_zero]
          rfl
        apply Finset.sum_eq_zero
        intro i _
        rw [hpoint i]
        norm_num
      · simp
    _ ≤ ‖rightFiberwiseMap (S := S) G‖ * ‖singleRightFiber s x‖ :=
      (rightFiberwiseMap (S := S) G).le_opNorm _
    _ = ‖rightFiberwiseMap (S := S) G‖ * ‖x‖ := by
      rw [norm_singleRightFiber]

end ContinuousLinearMap

namespace MPSTensor

variable {d D : ℕ}

/-- A nonwrapping local interaction on the first \(n\) sites acts independently
on every configuration of the final \(r\) right-spectator sites. -/
theorem localTermES_conj_rightSpectatorConfigLinearIsometryEquiv
    (A : MPSTensor d D) {n r L : ℕ} (i : Fin n) (hi : i.val + L ≤ n) :
    (rightSpectatorConfigLinearIsometryEquiv d n r).toLinearEquiv.toLinearMap.comp
        ((localTermES A L (Fin.castAdd r i)).comp
          (rightSpectatorConfigLinearIsometryEquiv d n r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.toContinuousLinearMap (localTermES A L i))).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨σ, s⟩
  simp only [LinearMap.comp_apply]
  change localTermES A L (Fin.castAdd r i)
      ((rightSpectatorConfigLinearIsometryEquiv d n r).symm x)
        (Fin.appendEquiv n r (σ, s)) =
    localTermES A L i (ContinuousLinearMap.rightFiber x s) σ
  rw [localTermES_apply A L (Fin.castAdd r i) (by omega),
    localTermES_apply A L i (by omega)]
  have hcfg (ω : Cfg d L) :
      rightSpectatorConfigEquiv d n r
          (cyclicCfg (Fin.pos (Fin.castAdd r i)) L (Fin.castAdd r i) ω
            (Fin.appendEquiv n r (σ, s))) =
        (cyclicCfg (Fin.pos i) L i ω σ, s) := by
    have hival : (Fin.castAdd r i).val = i.val := rfl
    rw [cyclicCfg_eq_contiguousCfg (Fin.pos (Fin.castAdd r i)) (by omega) (by omega),
      cyclicCfg_eq_contiguousCfg (Fin.pos i) (by omega) hi]
    apply Prod.ext
    · funext k
      simp only [rightSpectatorConfigEquiv]
      simp [contiguousCfg, Fin.appendEquiv]
    · funext k
      simp only [rightSpectatorConfigEquiv]
      change contiguousCfg (Fin.castAdd r i).val L ω (Fin.append σ s)
          (Fin.natAdd n k) = s k
      simp only [contiguousCfg]
      split
      · rename_i hwindow
        have hkval : (Fin.natAdd n k).val = n + k.val := rfl
        exfalso
        omega
      · exact Fin.append_right σ s k
  have hrestrict :
      cyclicRestrictES (d := d) (Fin.pos (Fin.castAdd r i)) L (Fin.castAdd r i)
          (Fin.appendEquiv n r (σ, s))
          ((rightSpectatorConfigLinearIsometryEquiv d n r).symm x) =
        cyclicRestrictES (d := d) (Fin.pos i) L i σ
          (ContinuousLinearMap.rightFiber x s) := by
    apply PiLp.ext
    intro ω
    simp only [cyclicRestrictES, LinearMap.coe_withLpMap]
    change ((rightSpectatorConfigLinearIsometryEquiv d n r).symm x)
        (cyclicCfg (Fin.pos (Fin.castAdd r i)) L (Fin.castAdd r i) ω
          (Fin.appendEquiv n r (σ, s))) =
      ContinuousLinearMap.rightFiber x s (cyclicCfg (Fin.pos i) L i ω σ)
    rw [rightSpectatorConfigLinearIsometryEquiv_symm_apply_apply]
    exact congrArg x (hcfg ω)
  have hextract :
      extractWindow L (Fin.castAdd r i) (Fin.appendEquiv n r (σ, s)) =
        extractWindow L i σ := by
    funext j
    have hival : (Fin.castAdd r i).val = i.val := rfl
    have hjL := j.isLt
    have hltSmall : i.val + j.val < n := by omega
    have hltBig : (Fin.castAdd r i).val + j.val < n + r := by omega
    have hbig :
        (⟨((Fin.castAdd r i).val + j.val) % (n + r),
          Nat.mod_lt _ (by omega)⟩ : Fin (n + r)) =
          Fin.castAdd r (⟨i.val + j.val, hltSmall⟩ : Fin n) := by
      apply Fin.ext
      change ((Fin.castAdd r i).val + j.val) % (n + r) = i.val + j.val
      rw [Nat.mod_eq_of_lt hltBig, hival]
    have hsmall :
        (⟨(i.val + j.val) % n, Nat.mod_lt _ (Fin.pos i)⟩ : Fin n) =
          ⟨i.val + j.val, hltSmall⟩ := by
      apply Fin.ext
      change (i.val + j.val) % n = i.val + j.val
      rw [Nat.mod_eq_of_lt hltSmall]
    change Fin.append σ s
        ⟨((Fin.castAdd r i).val + j.val) % (n + r), Nat.mod_lt _ (by omega)⟩ =
      σ ⟨(i.val + j.val) % n, Nat.mod_lt _ (Fin.pos i)⟩
    rw [hbig, Fin.append_left, hsmall]
  rw [hrestrict, hextract]

/-- Before the first full interaction window fits, the fixed-ambient prefix
Hamiltonian vanishes. -/
theorem openPrefixParentHamiltonianES_eq_zero_of_lt
    (A : MPSTensor d D) {L N n : ℕ} (hnL : n < L) :
    openPrefixParentHamiltonianES A L N n = 0 := by
  rw [openPrefixParentHamiltonianES]
  apply Finset.sum_eq_zero
  intro i _
  exfalso
  have hi := i.2
  omega

/-- Before the first full interaction window fits, the fixed-ambient ground
projection is the identity. -/
theorem openPrefixGroundProjectionES_eq_one_of_lt
    (A : MPSTensor d D) {L N n : ℕ} (hnL : n < L) :
    openPrefixGroundProjectionES A L N n = 1 := by
  have hzero := openPrefixParentHamiltonianES_eq_zero_of_lt A (N := N) hnL
  simp only [openPrefixGroundProjectionES, hzero, LinearMap.ker_zero,
    Submodule.starProjection_top']
  rfl

/-- For indices strictly below the C3 endpoint, the fixed-ambient martingale
difference vanishes because both adjacent prefix Hamiltonians are zero. -/
theorem fixedAmbient_martingaleDifference_eq_zero_of_lt
    (A : MPSTensor d D) {l N n : ℕ} (hnl : n < l) :
    (fixedAmbientNestedGroundProjectionsES A (l + 1) N).martingaleDifference n = 0 := by
  rw [FrustrationFree.NestedGroundProjections.martingaleDifference]
  change openPrefixGroundProjectionES A (l + 1) N n -
      openPrefixGroundProjectionES A (l + 1) N (n + 1) = 0
  rw [openPrefixGroundProjectionES_eq_one_of_lt A (by omega),
    openPrefixGroundProjectionES_eq_one_of_lt A (by omega), sub_self]

/-- At the first full-window prefix, the prefix and local-interval Hamiltonians
are the same single local interaction. -/
theorem openPrefixParentHamiltonianES_eq_openSuffixParentHamiltonianES_at_endpoint
    (A : MPSTensor d D) {L N : ℕ} (hL : 0 < L) (hLN : L ≤ N) :
    openPrefixParentHamiltonianES A L N L =
      openSuffixParentHamiltonianES A L L N L := by
  classical
  have hN : 0 < N := lt_of_lt_of_le hL hLN
  let iFin : Fin N := ⟨0, hN⟩
  let i : NonwrappingStart L N := ⟨iFin, by
    change 0 + L ≤ N
    omega⟩
  have hprefix : openPrefixParentHamiltonianES A L N L = localTermES A L i.1 := by
    let i' : OpenPrefixStart L N L := ⟨i, by
      change 0 + L ≤ L
      omega⟩
    let _ : Subsingleton (OpenPrefixStart L N L) :=
      ⟨fun j k => by
        apply Subtype.ext
        apply Subtype.ext
        apply Fin.ext
        have hj := j.2
        have hk := k.2
        omega⟩
    rw [openPrefixParentHamiltonianES, Fintype.sum_subsingleton _ i']
  have hsuffix : openSuffixParentHamiltonianES A L L N L = localTermES A L i.1 := by
    have hfilter :
        Finset.univ.filter (fun j : NonwrappingStart L N =>
          L - L ≤ j.1.val ∧ j.1.val + L ≤ L) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hj
        apply Subtype.ext
        apply Fin.ext
        change j.1.val = 0
        omega
      · intro hji
        subst j
        simp [i, iFin]
    rw [openSuffixParentHamiltonianES, hfilter, Finset.sum_singleton]
  exact hprefix.trans hsuffix.symm

/-- At the endpoint \(n=l\), the local ground projection is the next prefix
ground projection. -/
theorem openIntervalGroundProjectionES_at_endpoint
    (A : MPSTensor d D) {l N : ℕ} (hl : 0 < l) (hlN : l + 1 ≤ N) :
    openIntervalGroundProjectionES A (l + 1) l N l =
      openPrefixGroundProjectionES A (l + 1) N (l + 1) := by
  have hHamiltonian :=
    openPrefixParentHamiltonianES_eq_openSuffixParentHamiltonianES_at_endpoint
      A (L := l + 1) (N := N) (by omega) hlN
  have hker :
      LinearMap.ker (openSuffixParentHamiltonianES A (l + 1) (l + 1) N (l + 1)) =
        LinearMap.ker (openPrefixParentHamiltonianES A (l + 1) N (l + 1)) :=
    congrArg LinearMap.ker hHamiltonian.symm
  simp only [openIntervalGroundProjectionES, openPrefixGroundProjectionES]
  exact congrArg (fun U : Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) =>
    U.starProjection.toLinearMap) hker

/-- Nachtergaele's C3 product vanishes at the endpoint \(n=l\):
\(Q_l E_l = G_{[0,l+1)} (1 - G_{[0,l+1)}) = 0\). -/
theorem openIntervalGroundProjectionES_comp_martingaleDifference_at_endpoint
    (A : MPSTensor d D) {l N : ℕ} (hl : 0 < l) (hlN : l + 1 ≤ N) :
    (openIntervalGroundProjectionES A (l + 1) l N l).comp
        ((fixedAmbientNestedGroundProjectionsES A (l + 1) N).martingaleDifference l) = 0 := by
  rw [FrustrationFree.NestedGroundProjections.martingaleDifference]
  change (openIntervalGroundProjectionES A (l + 1) l N l).comp
      (openPrefixGroundProjectionES A (l + 1) N l -
        openPrefixGroundProjectionES A (l + 1) N (l + 1)) = 0
  rw [openPrefixGroundProjectionES_eq_one_of_lt A (by omega),
    openIntervalGroundProjectionES_at_endpoint A hl hlN,
    LinearMap.comp_sub]
  let P := openPrefixGroundProjectionES A (l + 1) N (l + 1)
  change P * 1 - P * P = 0
  rw [mul_one]
  apply sub_eq_zero.mpr
  simpa only [P, fixedAmbientNestedGroundProjectionsES] using
    ((fixedAmbientNestedGroundProjectionsES A (l + 1) N).isSymmetricProjection (l + 1)
      |>.isIdempotentElem.eq).symm

end MPSTensor
