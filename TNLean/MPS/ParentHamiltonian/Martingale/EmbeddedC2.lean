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

open scoped InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- A suffix whose length equals the interaction length contains exactly the
local term starting at \(n-L\). -/
theorem openSuffixParentHamiltonianES_eq_localTermES (A : MPSTensor d D)
    {L N n : ℕ} (hL : 0 < L) (hLn : L ≤ n) (hnN : n ≤ N) :
    openSuffixParentHamiltonianES A L L N n =
      localTermES A L (⟨n - L, by omega⟩ : Fin N) := by
  have hn : 0 < n := lt_of_lt_of_le hL hLn
  have hstart : n - L < N := lt_of_lt_of_le (Nat.sub_lt hn hL) hnN
  let i : NonwrappingStart L N :=
    ⟨⟨n - L, hstart⟩, by simpa [Nat.sub_add_cancel hLn] using hnN⟩
  have hfilter :
      Finset.univ.filter (fun j : NonwrappingStart L N =>
        n - L ≤ j.1.val ∧ j.1.val + L ≤ n) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hjLower, hjUpper⟩
      apply Subtype.ext
      apply Fin.ext
      exact le_antisymm (Nat.le_sub_of_add_le hjUpper) hjLower
    · intro hji
      subst j
      exact ⟨le_rfl, Nat.sub_add_cancel hLn ▸ le_rfl⟩
  rw [openSuffixParentHamiltonianES, hfilter, Finset.sum_singleton]

/-- The fixed-window suffix Hamiltonian is a symmetric projection. -/
theorem openSuffixParentHamiltonianES_isSymmetricProjection
    (A : MPSTensor d D) {L N n : ℕ} (hL : 0 < L) (hLn : L ≤ n)
    (hnN : n ≤ N) :
    (openSuffixParentHamiltonianES A L L N n).IsSymmetricProjection := by
  rw [openSuffixParentHamiltonianES_eq_localTermES A hL hLn hnN]
  exact localTermES_isSymmetricProjection A L _

/-- The fixed-window suffix Hamiltonian is the orthogonal projection onto the
orthogonal complement of its kernel. -/
theorem openSuffixParentHamiltonianES_eq_orthogonal_starProjection_ker
    (A : MPSTensor d D) {L N n : ℕ} (hL : 0 < L) (hLn : L ≤ n)
    (hnN : n ≤ N) :
    openSuffixParentHamiltonianES A L L N n =
      (LinearMap.ker (openSuffixParentHamiltonianES A L L N n))ᗮ.starProjection.toLinearMap := by
  let H := openSuffixParentHamiltonianES A L L N n
  have hH : H.IsSymmetricProjection :=
    openSuffixParentHamiltonianES_isSymmetricProjection A hL hLn hnN
  apply hH.ext (Submodule.isSymmetricProjection_starProjection (LinearMap.ker H)ᗮ)
  rw [Submodule.range_starProjection]
  have hrangeOrthogonal : (LinearMap.range H)ᗮ = LinearMap.ker H :=
    (LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range
      hH.isIdempotentElem).mp hH.isSymmetric
  calc
    LinearMap.range H = (LinearMap.range H)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal (LinearMap.range H)).symm
    _ = (LinearMap.ker H)ᗮ := congrArg Submodule.orthogonal hrangeOrthogonal

/-- Literal fixed-window identity \(H=I-G\), where \(G\) is the orthogonal
projection onto the kernel of \(H\). -/
theorem openSuffixParentHamiltonianES_eq_id_sub_starProjection_ker
    (A : MPSTensor d D) {L N n : ℕ} (hL : 0 < L) (hLn : L ≤ n)
    (hnN : n ≤ N) :
    openSuffixParentHamiltonianES A L L N n =
      LinearMap.id -
        (LinearMap.ker (openSuffixParentHamiltonianES A L L N n)).starProjection.toLinearMap := by
  let H := openSuffixParentHamiltonianES A L L N n
  calc
    H = (LinearMap.ker H)ᗮ.starProjection.toLinearMap :=
      openSuffixParentHamiltonianES_eq_orthogonal_starProjection_ker A hL hLn hnN
    _ = (1 - (LinearMap.ker H).starProjection).toLinearMap := by
      rw [Submodule.starProjection_orthogonal']
    _ = LinearMap.id - (LinearMap.ker H).starProjection.toLinearMap := rfl

/-- Nachtergaele's condition C2 in Loewner order, with \(\gamma_L=1\). -/
theorem openSuffixParentHamiltonianES_C2 (A : MPSTensor d D)
    {L N n : ℕ} (hL : 0 < L) (hLn : L ≤ n) (hnN : n ≤ N) :
    LinearMap.id -
        (LinearMap.ker (openSuffixParentHamiltonianES A L L N n)).starProjection.toLinearMap ≤
      openSuffixParentHamiltonianES A L L N n := by
  exact (openSuffixParentHamiltonianES_eq_id_sub_starProjection_ker
    A hL hLn hnN).symm.le

/-- Quadratic-form version of condition C2 with \(\gamma_L=1\). -/
theorem openSuffixParentHamiltonianES_C2_quadratic_form (A : MPSTensor d D)
    {L N n : ℕ} (hL : 0 < L) (hLn : L ≤ n) (hnN : n ≤ N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    ((⟪((LinearMap.id : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ]
          EuclideanSpace ℂ (Cfg d N)) -
          (LinearMap.ker (openSuffixParentHamiltonianES A L L N n)).starProjection.toLinearMap) v,
        v⟫_ℂ).re) ≤
      (⟪openSuffixParentHamiltonianES A L L N n v, v⟫_ℂ).re := by
  have hvEq := LinearMap.congr_fun
    (openSuffixParentHamiltonianES_eq_id_sub_starProjection_ker A hL hLn hnN) v
  exact (congrArg (fun w => (⟪w, v⟫_ℂ).re) hvEq.symm).le

/-- On the orthogonal complement of its kernel, the fixed-window suffix
Hamiltonian preserves the norm exactly. -/
theorem openSuffixParentHamiltonianES_norm_eq_of_mem_orthogonal_ker
    (A : MPSTensor d D) {L N n : ℕ} (hL : 0 < L) (hLn : L ≤ n)
    (hnN : n ≤ N) (v : EuclideanSpace ℂ (Cfg d N))
    (hv : v ∈ (LinearMap.ker (openSuffixParentHamiltonianES A L L N n))ᗮ) :
    ‖openSuffixParentHamiltonianES A L L N n v‖ = ‖v‖ := by
  rw [openSuffixParentHamiltonianES_eq_orthogonal_starProjection_ker A hL hLn hnN]
  apply Submodule.norm_starProjection_apply
  exact hv

/-- The fixed-window suffix Hamiltonian has unit gap on the orthogonal
complement of its kernel. Under \(L=l+1\) and with endpoint \(m=n+1\), this is
\(\gamma_{l+1}=1\) in Nachtergaele's Theorem 2.1(i). -/
theorem openSuffixParentHamiltonianES_unit_gap (A : MPSTensor d D)
    {L N n : ℕ} (hL : 0 < L) (hLn : L ≤ n) (hnN : n ≤ N)
    (v : EuclideanSpace ℂ (Cfg d N))
    (hv : v ∈ (LinearMap.ker (openSuffixParentHamiltonianES A L L N n))ᗮ) :
    (1 : ℝ) * ‖v‖ ≤ ‖openSuffixParentHamiltonianES A L L N n v‖ := by
  simpa only [one_mul] using
    (openSuffixParentHamiltonianES_norm_eq_of_mem_orthogonal_ker
      A hL hLn hnN v hv).symm.le

end MPSTensor
