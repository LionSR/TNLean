/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian

/-!
# Embedded fixed-window condition C2

When the suffix length equals the interaction length \(L\), the compatible suffix
Hamiltonian contains exactly one nonwrapping local parent interaction. Hence it
is an orthogonal projection and satisfies Nachtergaele's condition C2 with
constant one.

The statements remain generic in \(L\). Setting \(L = l + 1\) and
\(m = n + 1\) gives the source interval
\(\Lambda_{n+1}\setminus\Lambda_{n-l}=[n-l,n+1)\) and
\(\gamma_{l+1}=1\).

## References

* Nachtergaele, arXiv:cond-mat/9410110, condition C2, lines 1043--1058;
  Theorem 2.1(i), lines 1119--1130; proof lines 1240--1248.
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- The interval of length \(L\) ending at \(n\) contains exactly the window of the term
starting at \(n-L\): the restriction of the parent interaction to the windows inside it has that
term as its Hamiltonian. -/
theorem hamiltonian_restrict_parentChainInteraction_eq_term (A : MPSTensor d D)
    {L N n : ℕ} (hLn : L ≤ n) (hnN : n ≤ N) :
    ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian =
      (parentChainInteraction A L N).term ⟨n - L, by omega⟩ := by
  have hfilter :
      (Finset.univ.filter fun i : Fin (N + 1 - L) ↦ n - L ≤ i.val ∧ i.val + L ≤ n) =
        {⟨n - L, by omega⟩} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [ManyBody.Interaction.hamiltonian_restrict, ManyBody.Interaction.partialHamiltonian, hfilter,
    Finset.sum_singleton]

/-- The Hamiltonian of the single window inside an interval of length \(L\) is an orthogonal
projection. -/
theorem isStarProjection_hamiltonian_restrict_parentChainInteraction (A : MPSTensor d D)
    {L N n : ℕ} (hLn : L ≤ n) (hnN : n ≤ N) :
    IsStarProjection ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian := by
  rw [hamiltonian_restrict_parentChainInteraction_eq_term A hLn hnN]
  exact isStarProjection_parentChainInteraction_term A L N _

/-- The operator of the single-window Hamiltonian is the orthogonal projection onto the
orthogonal complement of its kernel. -/
theorem toEuclideanLin_hamiltonian_restrict_parentChainInteraction_eq_starProjection
    (A : MPSTensor d D) {L N n : ℕ} (hLn : L ≤ n) (hnN : n ≤ N) :
    Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian =
      (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
        fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian))ᗮ.starProjection.toLinearMap := by
  have hH := Matrix.isSymmetricProjection_toEuclideanLin_iff.mpr
    (isStarProjection_hamiltonian_restrict_parentChainInteraction A hLn hnN)
  apply hH.ext (Submodule.isSymmetricProjection_starProjection _)
  rw [Submodule.range_starProjection, ← hH.isSymmetric.orthogonal_range,
    Submodule.orthogonal_orthogonal]

/-- The single-window identity \(H=I-G\), where \(G\) is the orthogonal projection onto the
kernel of \(H\). -/
theorem toEuclideanLin_hamiltonian_restrict_parentChainInteraction_eq_id_sub_starProjection
    (A : MPSTensor d D) {L N n : ℕ} (hLn : L ≤ n) (hnN : n ≤ N) :
    Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian =
      LinearMap.id - (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian)).starProjection.toLinearMap := by
  calc
    _ = (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian))ᗮ.starProjection.toLinearMap :=
      toEuclideanLin_hamiltonian_restrict_parentChainInteraction_eq_starProjection A hLn hnN
    _ = (1 - (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian)).starProjection).toLinearMap := by
      rw [Submodule.starProjection_orthogonal']
    _ = _ := rfl

/-- Nachtergaele's condition C2 in Loewner order, with \(\gamma_L=1\). Nachtergaele,
arXiv:cond-mat/9410110, condition C2, lines 1043--1058. -/
theorem parentChainInteraction_C2 (A : MPSTensor d D) {L N n : ℕ} (hLn : L ≤ n)
    (hnN : n ≤ N) :
    LinearMap.id - (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian)).starProjection.toLinearMap ≤
      Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian :=
  (toEuclideanLin_hamiltonian_restrict_parentChainInteraction_eq_id_sub_starProjection
    A hLn hnN).symm.le

/-- Quadratic-form version of condition C2 with \(\gamma_L=1\). Nachtergaele,
arXiv:cond-mat/9410110, condition C2, lines 1043--1058. -/
theorem parentChainInteraction_C2_quadratic_form (A : MPSTensor d D) {L N n : ℕ} (hLn : L ≤ n)
    (hnN : n ≤ N) (v : EuclideanSpace ℂ (Cfg d N)) :
    (⟪((LinearMap.id : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N)) -
        (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian)).starProjection.toLinearMap) v,
        v⟫_ℂ).re ≤
      (⟪Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian v, v⟫_ℂ).re := by
  have hvEq := LinearMap.congr_fun
    (toEuclideanLin_hamiltonian_restrict_parentChainInteraction_eq_id_sub_starProjection
      A hLn hnN) v
  exact (congrArg (fun w => (⟪w, v⟫_ℂ).re) hvEq.symm).le

/-- On the orthogonal complement of its kernel, the single-window Hamiltonian preserves the
norm. -/
theorem norm_toEuclideanLin_hamiltonian_restrict_parentChainInteraction_of_mem_orthogonal_ker
    (A : MPSTensor d D) {L N n : ℕ} (hLn : L ≤ n) (hnN : n ≤ N)
    (v : EuclideanSpace ℂ (Cfg d N))
    (hv : v ∈ (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian))ᗮ) :
    ‖Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
      fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian v‖ = ‖v‖ := by
  rw [toEuclideanLin_hamiltonian_restrict_parentChainInteraction_eq_starProjection A hLn hnN]
  exact Submodule.norm_starProjection_apply _ hv

/-- The single-window Hamiltonian has unit gap: every eigenvalue is `0` or at least `1`. Under
\(L=l+1\) and with endpoint \(m=n+1\), this is \(\gamma_{l+1}=1\) in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(i), lines 1119--1130. -/
theorem unit_gap_hamiltonian_restrict_parentChainInteraction (A : MPSTensor d D) {L N n : ℕ}
    (hLn : L ≤ n) (hnN : n ≤ N) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin ((parentChainInteraction A L N).restrict
        fun i ↦ n - L ≤ i.val ∧ i.val + L ≤ n).hamiltonian) μ →
      μ = 0 ∨ (1 : ℂ) ≤ μ :=
  ManyBody.forall_hasEigenvalue_one_of_isStarProjection
    (isStarProjection_hamiltonian_restrict_parentChainInteraction A hLn hnN)

end MPSTensor
