/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbient
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorMaps
import TNLean.MPS.ParentHamiltonian.Martingale.C3Threshold
import TNLean.MPS.ParentHamiltonian.Martingale.EmbeddedC2
import QICLean.Analysis.IsometricConjugationGap

/-!
# Spectator transport for the open-chain C3 estimate

This file develops the right-spectator map needed to compare the local-volume
operators in Nachtergaele's condition C3 with the fixed-final-volume filtration.
The comparison uses an explicit finite fiber decomposition, never
definitional equality between operators on different Hilbert spaces.  The
resulting conjugacies prepare the fixed-final-volume form of condition C3.

## References

* Nachtergaele, arXiv:cond-mat/9410110, condition C3, lines 1083--1094.
* Nachtergaele, arXiv:cond-mat/9410110, proof of Theorem 2.1(i), lines 1178--1259.

The single-term conjugacy is stated for the terms of the parent interaction on the open chain
(`parentChainInteraction`), and the prefix and interval Hamiltonians are the Hamiltonians of its
restrictions to the windows inside a prefix or an interval.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

/-- Split a configuration on \(n+r\) sites into its first \(n\) active sites and
its final \(r\) right-spectator sites. -/
def rightSpectatorConfigEquiv (d n r : ℕ) :
    Cfg d (n + r) ≃ Cfg d n × Cfg d r :=
  (Fin.appendEquiv n r).symm

/-- Joining active and spectator configurations is the inverse spectator split. -/
@[simp] theorem rightSpectatorConfigEquiv_symm_apply
    (d n r : ℕ) (p : Cfg d n × Cfg d r) :
    (rightSpectatorConfigEquiv d n r).symm p = Fin.appendEquiv n r p :=
  rfl

/-- The active component of the spectator split is the initial coordinate
restriction. -/
@[simp] theorem rightSpectatorConfigEquiv_apply_fst
    (d n r : ℕ) (σ : Cfg d (n + r)) (i : Fin n) :
    (rightSpectatorConfigEquiv d n r σ).1 i = σ (Fin.castAdd r i) :=
  rfl

/-- The spectator component of the split is the final coordinate restriction. -/
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

/-- The spectator-splitting isometry evaluates by joining the two
configurations. -/
@[simp] theorem rightSpectatorConfigLinearIsometryEquiv_apply_apply
    (d n r : ℕ) (v : EuclideanSpace ℂ (Cfg d (n + r)))
    (p : Cfg d n × Cfg d r) :
    rightSpectatorConfigLinearIsometryEquiv d n r v p =
      v (Fin.appendEquiv n r p) := by
  rw [rightSpectatorConfigLinearIsometryEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

/-- The inverse spectator isometry evaluates through the canonical
configuration split. -/
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

namespace MPSTensor

variable {d D : ℕ}

/-- A term of the parent interaction on the open chain of the first \(n\) sites acts
independently on every configuration of the final \(r\) right-spectator sites: under the
spectator split, the term starting at `j` on \(n + r\) sites is the fiberwise extension of the
term starting at `j` on \(n\) sites. -/
theorem toEuclideanLin_parentChainInteraction_term_conj_rightSpectatorConfigLinearIsometryEquiv
    (A : MPSTensor d D) {n r L : ℕ} (j : Fin (n + 1 - L)) :
    (rightSpectatorConfigLinearIsometryEquiv d n r).toLinearEquiv.toLinearMap.comp
        ((Matrix.toEuclideanLin ((parentChainInteraction A L (n + r)).term
            ⟨j.val, by omega⟩)).comp
          (rightSpectatorConfigLinearIsometryEquiv d n r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin ((parentChainInteraction A L n).term j)))).toLinearMap := by
  have hj : j.val + L ≤ n := by omega
  have hj' : j.val + L ≤ n + r := by omega
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨σ, s⟩
  change (Matrix.toEuclideanLin ((parentChainInteraction A L (n + r)).term ⟨j.val, by omega⟩)
      ((rightSpectatorConfigLinearIsometryEquiv d n r).symm x)) (Fin.appendEquiv n r (σ, s)) =
    Matrix.toEuclideanLin ((parentChainInteraction A L n).term j)
      (ContinuousLinearMap.rightFiber x s) σ
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, PiLp.toLp_apply, PiLp.toLp_apply,
    ManyBody.Interaction.translates_term, ManyBody.Interaction.translates_term,
    placeAlong_chainWindow_mulVec_apply hj', placeAlong_chainWindow_mulVec_apply hj]
  have hcfg (ω : Cfg d L) :
      rightSpectatorConfigEquiv d n r (contiguousCfg j.val L ω (Fin.appendEquiv n r (σ, s))) =
        (contiguousCfg j.val L ω σ, s) := by
    apply Prod.ext
    · funext k
      simp only [rightSpectatorConfigEquiv]
      simp [contiguousCfg, Fin.appendEquiv]
    · funext k
      simp only [rightSpectatorConfigEquiv]
      change contiguousCfg j.val L ω (Fin.append σ s) (Fin.natAdd n k) = s k
      simp only [contiguousCfg]
      split
      · rename_i hwindow
        have hkval : (Fin.natAdd n k).val = n + k.val := rfl
        exfalso
        omega
      · exact Fin.append_right σ s k
  have hres : contiguousRestrictₗ j.val L hj' (Fin.appendEquiv n r (σ, s))
      (WithLp.ofLp ((rightSpectatorConfigLinearIsometryEquiv d n r).symm x)) =
      contiguousRestrictₗ j.val L hj σ (WithLp.ofLp (ContinuousLinearMap.rightFiber x s)) := by
    funext ω
    change ((rightSpectatorConfigLinearIsometryEquiv d n r).symm x)
        (contiguousCfg j.val L ω (Fin.appendEquiv n r (σ, s))) =
      x (contiguousCfg j.val L ω σ, s)
    rw [rightSpectatorConfigLinearIsometryEquiv_symm_apply_apply, hcfg]
  have hwin : (fun u ↦ Fin.appendEquiv n r (σ, s) (ManyBody.chainWindow j.val hj' u)) =
      fun u ↦ σ (ManyBody.chainWindow j.val hj u) := by
    funext u
    have hu : ManyBody.chainWindow (N := n + r) j.val hj' u =
        Fin.castAdd r (ManyBody.chainWindow j.val hj u) := Fin.ext (by simp)
    rw [hu]
    exact Fin.append_left σ s _
  rw [hres, hwin]

/-- Under the spectator split, the Hamiltonian of the parent interaction on \(n+r\) sites
restricted to a set of windows inside the first \(n\) sites is the fiberwise extension of the
Hamiltonian of the interaction on \(n\) sites restricted to the same windows. -/
theorem toEuclideanLin_hamiltonian_restrict_parentChainInteraction_conj_rightSpectator
    (A : MPSTensor d D) {L n r : ℕ} (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ k, q k → k + L ≤ n) :
    (rightSpectatorConfigLinearIsometryEquiv d n r).toLinearEquiv.toLinearMap.comp
        ((Matrix.toEuclideanLin ((parentChainInteraction A L (n + r)).restrict
            fun i ↦ q i.val).hamiltonian).comp
          (rightSpectatorConfigLinearIsometryEquiv d n r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
          ((parentChainInteraction A L n).restrict fun i ↦ q i.val).hamiltonian))).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [ManyBody.Interaction.hamiltonian, map_sum, LinearMap.comp_apply, LinearMap.sum_apply,
    ContinuousLinearMap.rightFiberwiseMap_sum, ContinuousLinearMap.toLinearMap_sum]
  refine Fin.sum_eq_sum_of_val_eq _ _ (fun k ha hb ↦ ?_) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
  · by_cases hk : q k
    · rw [ManyBody.Interaction.restrict_term, ManyBody.Interaction.restrict_term, ite_eq_left hk,
        ite_eq_left hk]
      exact LinearMap.congr_fun
        (toEuclideanLin_parentChainInteraction_term_conj_rightSpectatorConfigLinearIsometryEquiv
          A ⟨k, hb⟩) x
    · rw [ManyBody.Interaction.restrict_term, ManyBody.Interaction.restrict_term, ite_eq_right hk,
        ite_eq_right hk]
      simp
  · rw [ManyBody.Interaction.restrict_term, ite_eq_right fun h ↦ by have := hq _ h; omega]
    simp
  · exact absurd i.isLt (by omega)

/-- Conjugating a fixed-ambient prefix Hamiltonian by the canonical
right-spectator isometry gives the fiberwise extension of the same prefix
Hamiltonian in the smaller ambient volume. -/
theorem openPrefixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
    (A : MPSTensor d D) {L n r p : ℕ} (hp : p ≤ n) :
    (rightSpectatorConfigLinearIsometryEquiv d n r).toLinearEquiv.toLinearMap.comp
        ((openPrefixParentHamiltonianES A L (n + r) p).comp
          (rightSpectatorConfigLinearIsometryEquiv d n r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.toContinuousLinearMap
          (openPrefixParentHamiltonianES A L n p))).toLinearMap :=
  toEuclideanLin_hamiltonian_restrict_parentChainInteraction_conj_rightSpectator A
    (fun k ↦ k + L ≤ p) fun k hk ↦ by omega

/-- Conjugating a fixed-ambient suffix-interval Hamiltonian by the canonical
right-spectator isometry gives the fiberwise extension of the same interval
Hamiltonian in the smaller ambient volume. -/
theorem openSuffixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
    (A : MPSTensor d D) {L l n r p : ℕ} (hp : p ≤ n) :
    (rightSpectatorConfigLinearIsometryEquiv d n r).toLinearEquiv.toLinearMap.comp
        ((openSuffixParentHamiltonianES A L l (n + r) p).comp
          (rightSpectatorConfigLinearIsometryEquiv d n r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.toContinuousLinearMap
          (openSuffixParentHamiltonianES A L l n p))).toLinearMap :=
  toEuclideanLin_hamiltonian_restrict_parentChainInteraction_conj_rightSpectator A
    (fun k ↦ p - l ≤ k ∧ k + L ≤ p) fun k hk ↦ by omega

/-- When the prefix is the entire ambient volume, the fixed-ambient prefix
Hamiltonian is the ordinary nonwrapping open parent Hamiltonian. -/
theorem openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES
    (A : MPSTensor d D) (L n : ℕ) :
    openPrefixParentHamiltonianES A L n n = openParentHamiltonianES A L n := by
  rw [openPrefixParentHamiltonianES, ManyBody.Interaction.hamiltonian_restrict,
    Finset.filter_true_of_mem fun i _ ↦ by omega, ManyBody.Interaction.partialHamiltonian_univ]

/-- Under the one-site right-spectator splitting, a fiber is restriction to a
fixed final physical index. -/
theorem rightFiber_rightSpectatorConfigLinearIsometryEquiv_one {n : ℕ}
    (v : EuclideanSpace ℂ (Cfg d (n + 1))) (s : Cfg d 1) :
    WithLp.linearEquiv 2 ℂ (NSiteSpace d n)
        (ContinuousLinearMap.rightFiber
          (rightSpectatorConfigLinearIsometryEquiv d n 1 v) s) =
      restrictLastₗ (s 0)
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d (n + 1)) v) := by
  funext σ
  change v (Fin.append σ s) = v (Fin.snoc σ (s 0))
  rw [Fin.append_right_eq_snoc]

/-- For a block-injective tensor, the kernel of the prefix Hamiltonian in the
one-site-larger volume is the left open-chain ground space. -/
theorem ker_openPrefixParentHamiltonianES_eq_openChainLeftGroundSpaceES
    {A : MPSTensor d D} [NeZero D] {L₀ n : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀n : L₀ + 1 ≤ n) :
    LinearMap.ker (openPrefixParentHamiltonianES A (L₀ + 1) (n + 1) n) =
      openChainLeftGroundSpaceES A n := by
  classical
  ext v
  rw [mem_openChainLeftGroundSpaceES_iff]
  have hconj :=
    openPrefixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
      A (L := L₀ + 1) (n := n) (r := 1) (p := n) le_rfl
  have happly := LinearMap.congr_fun hconj
    (rightSpectatorConfigLinearIsometryEquiv d n 1 v)
  change rightSpectatorConfigLinearIsometryEquiv d n 1
      (openPrefixParentHamiltonianES A (L₀ + 1) (n + 1) n
        ((rightSpectatorConfigLinearIsometryEquiv d n 1).symm
          (rightSpectatorConfigLinearIsometryEquiv d n 1 v))) = _ at happly
  rw [LinearIsometryEquiv.symm_apply_apply] at happly
  rw [LinearMap.mem_ker]
  have hzero :
      openPrefixParentHamiltonianES A (L₀ + 1) (n + 1) n v = 0 ↔
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d 1)
          (LinearMap.toContinuousLinearMap
            (openPrefixParentHamiltonianES A (L₀ + 1) n n))
          (rightSpectatorConfigLinearIsometryEquiv d n 1 v) = 0 := by
    constructor
    · intro hv
      calc
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d 1)
            (LinearMap.toContinuousLinearMap
              (openPrefixParentHamiltonianES A (L₀ + 1) n n))
            (rightSpectatorConfigLinearIsometryEquiv d n 1 v) =
          rightSpectatorConfigLinearIsometryEquiv d n 1
            (openPrefixParentHamiltonianES A (L₀ + 1) (n + 1) n v) := happly.symm
        _ = rightSpectatorConfigLinearIsometryEquiv d n 1 0 :=
          congrArg (rightSpectatorConfigLinearIsometryEquiv d n 1) hv
        _ = 0 := map_zero _
    · intro hv
      apply (rightSpectatorConfigLinearIsometryEquiv d n 1).injective
      rw [map_zero]
      exact happly.trans hv
  rw [hzero]
  change rightSpectatorConfigLinearIsometryEquiv d n 1 v ∈
      LinearMap.ker
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d 1)
          (LinearMap.toContinuousLinearMap
            (openPrefixParentHamiltonianES A (L₀ + 1) n n))).toLinearMap ↔ _
  rw [ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff]
  rw [openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES]
  change (∀ s : Cfg d 1,
      ContinuousLinearMap.rightFiber
          (rightSpectatorConfigLinearIsometryEquiv d n 1 v) s ∈
        LinearMap.ker (openParentHamiltonianES A (L₀ + 1) n)) ↔ _
  rw [ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
    hInj hL₀ hL₀n]
  constructor
  · intro hv j
    have hs := hv (fun _ => j)
    rw [mem_groundSpaceES_iff] at hs
    change WithLp.linearEquiv 2 ℂ (NSiteSpace d n)
        (ContinuousLinearMap.rightFiber
          (rightSpectatorConfigLinearIsometryEquiv d n 1 v) (fun _ => j)) ∈
      groundSpace A n at hs
    rw [rightFiber_rightSpectatorConfigLinearIsometryEquiv_one] at hs
    exact hs
  · intro hv s
    rw [mem_groundSpaceES_iff,
      rightFiber_rightSpectatorConfigLinearIsometryEquiv_one]
    exact hv (s 0)

/-- The suffix interval equal to the full final window contains one term of the parent
interaction, beginning after the prefix of length \(K\). -/
theorem openSuffixParentHamiltonianES_full_window_eq_term (A : MPSTensor d D) {K L : ℕ} :
    openSuffixParentHamiltonianES A L L (K + L) (K + L) =
      Matrix.toEuclideanLin ((parentChainInteraction A L (K + L)).term ⟨K, by omega⟩) := by
  rw [openSuffixParentHamiltonianES,
    hamiltonian_restrict_parentChainInteraction_eq_term A (Nat.le_add_left L K) le_rfl]
  simp only [Nat.add_sub_cancel]

private theorem contiguousRestrictₗ_tail_window {K L : ℕ} (τ : Cfg d (K + L))
    (ψ : NSiteSpace d (K + L)) :
    contiguousRestrictₗ K L le_rfl τ ψ =
      tailRestrictₗ (fun k : Fin K => τ (Fin.castAdd L k)) ψ := by
  funext ω
  change ψ (contiguousCfg K L ω τ) = ψ (Fin.append (fun k : Fin K => τ (Fin.castAdd L k)) ω)
  congr 1
  funext q
  by_cases hq : K ≤ q.val
  · have hsub : q.val - K < L := by omega
    let k : Fin L := ⟨q.val - K, hsub⟩
    have hqeq : q = Fin.natAdd K k := by
      apply Fin.ext
      change q.val = K + (q.val - K)
      omega
    simp only [contiguousCfg, hq, q.isLt, and_self, ↓reduceDIte]
    exact (Fin.append_right (fun k : Fin K => τ (Fin.castAdd L k)) ω k).symm.trans
      (congrArg (Fin.append (fun k : Fin K => τ (Fin.castAdd L k)) ω) hqeq.symm)
  · have hqK : q.val < K := by omega
    let k : Fin K := ⟨q.val, hqK⟩
    have hqeq : q = Fin.castAdd L k := by
      apply Fin.ext
      rfl
    simp only [contiguousCfg, hq]
    exact (congrArg τ hqeq).trans
      ((Fin.append_left (fun k : Fin K => τ (Fin.castAdd L k)) ω k).symm.trans
        (congrArg (Fin.append (fun k : Fin K => τ (Fin.castAdd L k)) ω) hqeq.symm))

/-- The kernel of a full suffix-window Hamiltonian is the corresponding tail
open-chain ground space. -/
theorem ker_openSuffixParentHamiltonianES_eq_openChainTailGroundSpaceES
    (A : MPSTensor d D) {K L : ℕ} (hL : 0 < L) :
    LinearMap.ker (openSuffixParentHamiltonianES A L L (K + L) (K + L)) =
      openChainTailGroundSpaceES A K L := by
  classical
  rw [openSuffixParentHamiltonianES_full_window_eq_term A]
  ext v
  cases isEmpty_or_nonempty (Fin d) with
  | inl hd =>
      let _ : IsEmpty (Fin d) := hd
      let _ : IsEmpty (Cfg d (K + L)) :=
        ⟨fun σ => isEmptyElim (σ ⟨0, by omega⟩)⟩
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      simp
  | inr hd =>
      let _ : Nonempty (Fin d) := hd
      rw [LinearMap.mem_ker, mem_openChainTailGroundSpaceES_iff, Matrix.toLpLin_apply,
        WithLp.toLp_eq_zero, parentChainInteraction_term_mulVec_eq_zero_iff]
      constructor
      · intro hv u
        let τ : Cfg d (K + L) := Fin.append u (fun _ => Classical.choice hd)
        have hτ := hv τ
        have hpref : (fun k : Fin K => τ (Fin.castAdd L k)) = u := by
          funext k
          exact Fin.append_left u (fun _ => Classical.choice hd) k
        rw [contiguousRestrictₗ_tail_window, hpref] at hτ
        exact hτ
      · intro hv τ
        rw [contiguousRestrictₗ_tail_window]
        exact hv (fun k : Fin K => τ (Fin.castAdd L k))

/-- For a block-injective tensor, the kernel of the prefix Hamiltonian that
fills its own volume is the whole open-chain ground space. -/
theorem ker_openPrefixParentHamiltonianES_self_eq_groundSpaceES
    {A : MPSTensor d D} [NeZero D] {L₀ n : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀n : L₀ + 1 ≤ n) :
    LinearMap.ker (openPrefixParentHamiltonianES A (L₀ + 1) n n) =
      groundSpaceES A n := by
  rw [openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES,
    ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective hInj hL₀ hL₀n]

/-- Conjugating an operator by a linear isometry equivalence conjugates its
kernel projection to the kernel projection of the conjugated operator. -/
theorem ker_starProjection_conj_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (G : E →ₗ[ℂ] E) (H : F →ₗ[ℂ] F)
    (hconj : U.toLinearEquiv.toLinearMap.comp
      (G.comp U.symm.toLinearEquiv.toLinearMap) = H) :
    U.toLinearEquiv.toLinearMap.comp
        ((LinearMap.ker G).starProjection.toLinearMap.comp
          U.symm.toLinearEquiv.toLinearMap) =
      (LinearMap.ker H).starProjection.toLinearMap := by
  have hker : LinearMap.ker H = (LinearMap.ker G).map (U.toLinearEquiv : E →ₗ[ℂ] F) :=
    U.ker_eq_map_of_conj G H hconj
  apply LinearMap.ext
  intro x
  change U ((LinearMap.ker G).starProjection (U.symm x)) =
    (LinearMap.ker H).starProjection x
  simp only [hker, Submodule.starProjection_map_apply]

/-- If the right-spectator coordinate isometry conjugates an operator to the
fiberwise extension of an active-volume operator, it conjugates the kernel
projection of the first to the fiberwise extension of the kernel projection of
the second. -/
theorem ker_starProjection_conj_of_rightFiberwiseMap {n r : ℕ}
    (G : EuclideanSpace ℂ (Cfg d (n + r)) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d (n + r)))
    (H : EuclideanSpace ℂ (Cfg d n) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d n))
    (hconj : (rightSpectatorConfigLinearIsometryEquiv d n r).toLinearEquiv.toLinearMap.comp
        (G.comp (rightSpectatorConfigLinearIsometryEquiv d n r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.toContinuousLinearMap H)).toLinearMap) :
    (rightSpectatorConfigLinearIsometryEquiv d n r).toLinearEquiv.toLinearMap.comp
        ((LinearMap.ker G).starProjection.toLinearMap.comp
          (rightSpectatorConfigLinearIsometryEquiv d n r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.ker H).starProjection).toLinearMap := by
  have hproj := ker_starProjection_conj_linearIsometryEquiv _ G _ hconj
  rw [ContinuousLinearMap.ker_starProjection_rightFiberwiseMap] at hproj
  exact hproj

/-- In a fixed larger volume, the prefix ground projection is the fiberwise
extension of the left open-chain ground projection in the active volume. -/
theorem openPrefixGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv
    {A : MPSTensor d D} [NeZero D] {L₀ n r : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀n : L₀ + 1 ≤ n) :
    (rightSpectatorConfigLinearIsometryEquiv d (n + 1) r).toLinearEquiv.toLinearMap.comp
        ((openPrefixGroundProjectionES A (L₀ + 1) ((n + 1) + r) n).comp
          (rightSpectatorConfigLinearIsometryEquiv d (n + 1) r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (openChainLeftGroundProjectionES A n)).toLinearMap := by
  let G := openPrefixParentHamiltonianES A (L₀ + 1) ((n + 1) + r) n
  let H := openPrefixParentHamiltonianES A (L₀ + 1) (n + 1) n
  have hHamiltonian :=
    openPrefixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
      A (L := L₀ + 1) (n := n + 1) (r := r) (p := n) (by omega)
  have hproj := ker_starProjection_conj_of_rightFiberwiseMap G H hHamiltonian
  rw [ker_openPrefixParentHamiltonianES_eq_openChainLeftGroundSpaceES
    hInj hL₀ hL₀n] at hproj
  exact hproj

/-- In a fixed larger volume, the ground projection of the whole active prefix
is the fiberwise extension of the whole open-chain ground projection. -/
theorem openPrefixWholeGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv
    {A : MPSTensor d D} [NeZero D] {L₀ n r : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀n : L₀ + 1 ≤ n) :
    (rightSpectatorConfigLinearIsometryEquiv d n r).toLinearEquiv.toLinearMap.comp
        ((openPrefixGroundProjectionES A (L₀ + 1) (n + r) n).comp
          (rightSpectatorConfigLinearIsometryEquiv d n r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (groundSpaceES A n).starProjection).toLinearMap := by
  let G := openPrefixParentHamiltonianES A (L₀ + 1) (n + r) n
  let H := openPrefixParentHamiltonianES A (L₀ + 1) n n
  have hHamiltonian :=
    openPrefixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
      A (L := L₀ + 1) (n := n) (r := r) (p := n) le_rfl
  have hproj := ker_starProjection_conj_of_rightFiberwiseMap G H hHamiltonian
  rw [show LinearMap.ker H = groundSpaceES A n from
    ker_openPrefixParentHamiltonianES_self_eq_groundSpaceES hInj hL₀ hL₀n] at hproj
  exact hproj

/-- In a fixed larger volume, a full suffix-window ground projection is the
fiberwise extension of the tail open-chain ground projection in the active
volume. -/
theorem openIntervalGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv
    (A : MPSTensor d D) {K l r : ℕ} :
    (rightSpectatorConfigLinearIsometryEquiv d (K + (l + 1)) r).toLinearEquiv.toLinearMap.comp
        ((openIntervalGroundProjectionES A (l + 1) l
          ((K + (l + 1)) + r) (K + l)).comp
          (rightSpectatorConfigLinearIsometryEquiv d
            (K + (l + 1)) r).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (openChainTailGroundProjectionES A K (l + 1))).toLinearMap := by
  have hKl : K + l + 1 = K + (l + 1) := by omega
  let G := openSuffixParentHamiltonianES A (l + 1) (l + 1)
    ((K + (l + 1)) + r) (K + l + 1)
  let H := openSuffixParentHamiltonianES A (l + 1) (l + 1)
    (K + (l + 1)) (K + l + 1)
  have hHamiltonian :=
    openSuffixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
      A (L := l + 1) (l := l + 1) (n := K + (l + 1)) (r := r)
        (p := K + l + 1) (by omega)
  have hproj := ker_starProjection_conj_of_rightFiberwiseMap G H hHamiltonian
  rw [show LinearMap.ker H = openChainTailGroundSpaceES A K (l + 1) by
    simpa only [H, Nat.add_assoc] using
      (ker_openSuffixParentHamiltonianES_eq_openChainTailGroundSpaceES
        A (K := K) (L := l + 1) (by omega))] at hproj
  simpa only [openIntervalGroundProjectionES, openChainTailGroundProjectionES,
    G, hKl] using hproj

end MPSTensor
