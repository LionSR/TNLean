/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.OrthogonalKernelGap
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.CyclicWindowOpenHamiltonian
import QICLean.Spectral.Gap.EuclideanFiberwiseGap
import TNLean.MPS.ParentHamiltonian.ParentInteraction.FiniteIntervalGapComparison
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.OpenParentGap

/-!
# Finite-range Knabe gap for MPS parent Hamiltonians

An open-chain norm gap on the \(m + R - 1\) sites occupied by \(m\) consecutive
range-\(R\) interactions supplies the local quadratic-form input in the cyclic
finite-range Knabe inequality.  The resulting periodic gap is

\(\delta = (m\gamma - (R - 1)^2)/(m - R + 1)\).

For a primitive MPS, the open-chain martingale estimate provides
\(\gamma = (1 - \varepsilon_l\sqrt{l + 1})^2\) at range \(R = l + 1\).  Choosing \(m\) so that
\(l^2 < m\gamma\) gives a positive periodic gap uniformly for \(N \geq 2m\).
Taking a minimum with the positive bounds at the finitely many shorter lengths
extends any such estimate to all lengths.

## References

* Knabe, J. Stat. Phys. 52, 627 (1988).
* Pérez-García et al., arXiv:quant-ph/0608197, lines 1460--1500.
* Cirac--Perez-García--Schuch--Verstraete, arXiv:2011.12127,
  lines 2184--2188 and 2194--2197.

The arbitrary finite-range coefficient is the TNLean derivation recorded in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`.

## Periodic gaps from open intervals of divisible length

A uniform positive open-chain gap along the lengths \(pM\), for fixed
\(p > 0\), implies a uniform positive periodic gap at every sufficiently large
length. Choose a divisible open interval containing \(m\) local terms with
\(m\gamma > (R-1)^2\), then apply the finite-range Knabe comparison.

This is the transfer needed after Nachtergaele's open-chain estimate,
arXiv:cond-mat/9410110, Theorem 2.1(ii). The finite-range coefficient is the
TNLean derivation in `docs/paper-gaps/knabe88_finite_range_coefficient.tex`.
-/

section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- At a fixed length, the restriction of the parent Hamiltonian to the
orthogonal complement of its kernel has a positive lower norm bound. -/
theorem parentHamiltonianES_exists_gap (A : MPSTensor d D) (R N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ :=
  (parentHamiltonianES A R N).exists_pos_mul_norm_le_of_mem_orthogonal_ker

/-- A periodic parent-Hamiltonian gap for all sufficiently large lengths extends
to all lengths by taking the minimum with finitely many positive bounds. -/
theorem parentHamiltonianES_gap_of_eventual_gap (A : MPSTensor d D) (R M : ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ N : ℕ, M ≤ N → ∀ v ∈ (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ,
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
        γ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ :=
  Nat.exists_pos_forall_of_eventually
    (fun _ _ _ hγδ h v hv ↦ (mul_le_mul_of_nonneg_right hγδ (norm_nonneg v)).trans (h v hv))
    (parentHamiltonianES_exists_gap A R) hδ hGap

/-- A uniform norm gap for the open Hamiltonian on the active sites of a
Knabe window gives the finite-range periodic parent-Hamiltonian gap.

Here \(m\) counts local terms, so the active open volume is exactly
\(W = m + R - 1\).  The hypotheses \(R \leq m\) and \(2m \leq N\) imply \(W \leq N\).
The coefficient is the finite-range cyclic Knabe coefficient derived in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem parentHamiltonianES_gap_of_openParentHamiltonianES_gap
    (A : MPSTensor d D) {R m : ℕ} (hR : 1 ≤ R) (hmR : R ≤ m)
    {γ : ℝ} (hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ)
    (hOpenGap : ∀ u ∈
      (LinearMap.ker (openParentHamiltonianES A R (m + R - 1)))ᗮ,
      γ * ‖u‖ ≤ ‖openParentHamiltonianES A R (m + R - 1) u‖) :
    let δ := ((m : ℝ) * γ - ((R : ℝ) - 1) ^ 2) /
      ((m : ℝ) - (R : ℝ) + 1)
    0 < δ ∧ ∀ N : ℕ, 2 * m ≤ N → ∀ v ∈
      (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ := by
  classical
  dsimp only
  have hm : 0 < m := by omega
  have hγ : 0 < γ := by
    have hsq : 0 ≤ ((R : ℝ) - 1) ^ 2 := sq_nonneg _
    have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hden : 0 < (m : ℝ) - (R : ℝ) + 1 := by exact_mod_cast (by omega : 0 < m - R + 1)
  have hδ : 0 < ((m : ℝ) * γ - ((R : ℝ) - 1) ^ 2) /
      ((m : ℝ) - (R : ℝ) + 1) := div_pos (sub_pos.mpr hnum) hden
  refine ⟨hδ, ?_⟩
  intro N hN v hv
  let δ := ((m : ℝ) * γ - ((R : ℝ) - 1) ^ 2) /
    ((m : ℝ) - (R : ℝ) + 1)
  let _ : NeZero N := ⟨by omega⟩
  have hProj : ∀ s : ZMod N,
      (zmodLocalTermES A R s).IsSymmetricProjection := by
    intro s
    exact localTermES_isSymmetricProjection A R ((ZMod.finEquiv N).symm s)
  have hWindowGap : ∀ s : ZMod N, ∀ x : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪ProjectionGeometry.cyclicWindowSum (zmodLocalTermES A R) m s x,
        x⟫_ℂ).re ≤
      (⟪ProjectionGeometry.cyclicWindowSum (zmodLocalTermES A R) m s x,
        ProjectionGeometry.cyclicWindowSum (zmodLocalTermES A R) m s x⟫_ℂ).re := by
    intro s x
    let W := m + R - 1
    let i := (ZMod.finEquiv N).symm s
    let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega) i
    let G := LinearMap.toContinuousLinearMap (openParentHamiltonianES A R W)
    let B := ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W)) G
    have hFiber : ∀ y : EuclideanSpace ℂ (Cfg d W × Cfg d (N - W)),
        γ * (⟪B y, y⟫_ℂ).re ≤ (⟪B y, B y⟫_ℂ).re :=
      LinearMap.IsPositive.quadraticForm_sq_ge_rightFiberwiseMap_of_norm_gap
        G (openParentHamiltonianES_isPositive A R W) hγ.le hOpenGap
    have hConj := cyclicWindowSum_zmodLocalTermES_conj_cyclicActiveBlock
      A hR hmR hN s
    have hApply : U (ProjectionGeometry.cyclicWindowSum
        (zmodLocalTermES A R) m s x) = B (U x) := by
      have := LinearMap.congr_fun hConj (U x)
      simpa [U, B, G, W, i] using this
    have h := hFiber (U x)
    rwa [← hApply, U.inner_map_map, U.inner_map_map] at h
  exact FrustrationFree.spectralGap_of_martingale_of_finiteDimensional hδ
    (parentHamiltonianES_isPositive A R N) (fun x ↦ by
      have hx := ProjectionGeometry.quadraticForm_sum_projections_of_cyclic_knabe
        (zmodLocalTermES A R) hProj hN hR hmR
        (fun e heR heN s y ↦ zmodLocalTermES_commute_of_oriented_separation
          A heR heN s y)
        (γ := γ) (δ := δ) rfl hnum hWindowGap x
      rwa [sum_zmodLocalTermES_eq_parentHamiltonianES] at hx) v hv

set_option linter.style.longLine false in
/-- A primitive MPS has a positive finite-range Knabe gap for its canonical
range-\(l + 1\) parent Hamiltonian on every periodic chain with \(N \geq 2m\).

The open coefficient is
\(\gamma = (1 - \varepsilon\sqrt{l + 1})^2\), the active Knabe volume is \(m + l\), and
\(m\) is chosen so that \(l^2 < m\gamma\). -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.exists_parentHamiltonianES_gap_of_finiteRangeKnabe
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : Matrix.PosDef ρ) :
    ∃ l : ℕ, ∃ ε : ℝ, ∃ m : ℕ, ∃ δ : ℝ,
      1 < l ∧ Kraus.IsNBlkInjective A l ∧
      0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      l + 1 ≤ m ∧
      δ = ((m : ℝ) * (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 -
          (l : ℝ) ^ 2) / ((m : ℝ) - (l : ℝ)) ∧
      0 < δ ∧
      ∀ N : ℕ, 2 * m ≤ N → ∀ v ∈
        (LinearMap.ker (parentHamiltonianES A (l + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES A (l + 1) N v‖ := by
  obtain ⟨l, ε, hl, hInj, hε, hεlt, hOpenGap⟩ :=
    hP.exists_openParentHamiltonianES_gap hρ
  let γ := (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2
  have hs : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hεs : ε * Real.sqrt ((l + 1 : ℕ) : ℝ) < 1 :=
    (lt_div_iff₀ hs).mp hεlt
  have hγ : 0 < γ := by
    dsimp only [γ]
    positivity
  obtain ⟨n, hn⟩ := exists_lt_nsmul hγ ((l : ℝ) ^ 2)
  let m := n + l + 1
  have hm : l + 1 ≤ m := by omega
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : n ≤ m)
  have hnum : (l : ℝ) ^ 2 < (m : ℝ) * γ := by
    calc
      (l : ℝ) ^ 2 < n • γ := hn
      _ = (n : ℝ) * γ := by simp [nsmul_eq_mul]
      _ ≤ (m : ℝ) * γ := mul_le_mul_of_nonneg_right hnm hγ.le
  let δ := ((m : ℝ) * γ - (l : ℝ) ^ 2) /
    ((m : ℝ) - ((l + 1 : ℕ) : ℝ) + 1)
  have hOpenGap' : ∀ u ∈
      (LinearMap.ker (openParentHamiltonianES A (l + 1) (m + l)))ᗮ,
      γ * ‖u‖ ≤ ‖openParentHamiltonianES A (l + 1) (m + l) u‖ := by
    intro u hu
    apply hOpenGap (m + l) (by omega) u
    rw [← ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
      hInj hl.le (by omega)]
    exact hu
  have hPeriodic := parentHamiltonianES_gap_of_openParentHamiltonianES_gap
    A (R := l + 1) (m := m) (by omega) hm (γ := γ) (by simpa using hnum)
    (by simpa [γ] using hOpenGap')
  refine ⟨l, ε, m, δ, hl, hInj, hε, hεlt, hm, ?_, ?_⟩
  · dsimp only [δ, γ]
    congr 1
    push_cast
    ring
  · simpa [δ, γ] using hPeriodic

end MPSTensor

end

section

open Filter
open scoped Topology

namespace MPSTensor

variable {d D : ℕ}

/-- A positive open-chain gap on all sufficiently large multiples of a fixed
positive integer implies a positive periodic gap at every sufficiently large
length. This applies to the divisible open lengths in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii), using the finite-range comparison in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem exists_parentHamiltonianES_gap_of_eventually_divisible_openParentHamiltonianES_gap
    (A : MPSTensor d D) {p R : ℕ} (hp : 1 ≤ p) (hR : 1 ≤ R)
    {γ : ℝ} (hγ : 0 < γ)
    (hOpen : ∀ᶠ M : ℕ in atTop, ∀ u ∈
      (LinearMap.ker (openParentHamiltonianES A R (p * M)))ᗮ,
      γ * ‖u‖ ≤ ‖openParentHamiltonianES A R (p * M) u‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ v ∈
      (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ := by
  obtain ⟨n, hn⟩ := exists_lt_nsmul hγ (((R : ℝ) - 1) ^ 2)
  obtain ⟨M, hM, hGap⟩ := ((eventually_ge_atTop (n + 2 * R)).and hOpen).exists
  have hMp : M ≤ p * M := by nlinarith
  let m := p * M - R + 1
  have hm : R ≤ m ∧ n ≤ m ∧ m + R - 1 = p * M := by omega
  have hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ := by
    exact hn.trans_le (by simpa only [nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm.2.1) hγ.le)
  obtain ⟨hδ, hPeriodic⟩ := parentHamiltonianES_gap_of_openParentHamiltonianES_gap
    A hR hm.1 hnum (hm.2.2.symm ▸ hGap)
  exact ⟨_, hδ, (eventually_ge_atTop (2 * m)).mono hPeriodic⟩

end MPSTensor

end
