/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.EigenvalueGap
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.CyclicWindowOpenHamiltonian
import QICLean.Spectral.Gap.EuclideanFiberwiseGap
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.OpenParentGap

/-!
# Finite-range Knabe gap for MPS parent Hamiltonians

A gap of the open-chain parent Hamiltonian on the \(m + R - 1\) sites occupied by \(m\)
consecutive range-\(R\) interactions supplies the local quadratic-form input in the cyclic
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

/-- A gap of the Hamiltonians of the parent interaction on all sufficiently large rings extends
to all rings by taking the minimum with finitely many positive bounds. The gap is stated above
the kernel: every eigenvalue is `0` or at least the gap. -/
theorem hamiltonian_parentRingInteraction_gap_of_eventual_gap (A : MPSTensor d D) (R M : ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ (N : ℕ) [NeZero N], M ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (N : ℕ) [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ :=
  Nat.exists_pos_forall_of_eventually
    (P := fun N γ ↦ ∀ [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) μ → μ = 0 ∨ (γ : ℂ) ≤ μ)
    (fun _ _ _ hγδ h _ ↦ ManyBody.forall_hasEigenvalue_mono hγδ h)
    (fun N ↦ by
      by_cases hN : N = 0
      · exact ⟨1, one_pos, fun {hN'} ↦ absurd hN hN'.out⟩
      · have : NeZero N := ⟨hN⟩
        obtain ⟨η, hη, h⟩ := ManyBody.exists_pos_forall_hasEigenvalue
          (posSemidef_hamiltonian_parentRingInteraction A R N)
        exact ⟨η, hη, h⟩) hδ fun N hN _ ↦ hGap N hN

/-- A gap of the open-chain parent Hamiltonian on the active sites of a
Knabe window gives the finite-range gap of the Hamiltonians of the parent interaction on the
rings. Each gap is stated above the kernel: every eigenvalue is `0` or at least the gap.

Here \(m\) counts local terms, so the active open volume is exactly
\(W = m + R - 1\).  The hypotheses \(R \leq m\) and \(2m \leq N\) imply \(W \leq N\).
The coefficient is the finite-range cyclic Knabe coefficient derived in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem hamiltonian_parentRingInteraction_gap_of_hamiltonian_parentChainInteraction_gap
    (A : MPSTensor d D) {R m : ℕ} (hR : 1 ≤ R) (hmR : R ≤ m)
    {γ : ℝ} (hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ)
    (hOpenGap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R (m + R - 1)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    let δ : ℝ := ((m : ℝ) * γ - ((R : ℝ) - 1) ^ 2) /
      ((m : ℝ) - (R : ℝ) + 1)
    0 < δ ∧ ∀ (N : ℕ) (hN : 2 * m ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
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
  intro N hN
  have : NeZero N := ⟨by omega⟩
  have hWN : m + R - 1 ≤ N := by omega
  have hPSD := posSemidef_hamiltonian_parentRingInteraction A R N
  let P : ZMod N → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) := fun s ↦
    Matrix.toEuclideanLin ((parentRingInteraction A R N).term ((ZMod.finEquiv N).symm s))
  have hProj (s : ZMod N) : (P s).IsSymmetricProjection :=
    isSymmetricProjection_toEuclideanLin_parentRingInteraction_term A R _
  have hWindowGap (s : ZMod N) (x : EuclideanSpace ℂ (Cfg d N)) :
      γ * (⟪ProjectionGeometry.cyclicWindowSum P m s x, x⟫_ℂ).re ≤
      (⟪ProjectionGeometry.cyclicWindowSum P m s x,
        ProjectionGeometry.cyclicWindowSum P m s x⟫_ℂ).re := by
    let U := cyclicActiveBlockConfigLinearIsometryEquiv d (m + R - 1) hWN
      ((ZMod.finEquiv N).symm s)
    -- Caching this instance is load-bearing: without it, synthesizing
    -- `ContinuousSMul ℂ` on this Euclidean space times out in the statements below.
    let : T2Space (EuclideanSpace ℂ (Cfg d (m + R - 1))) := inferInstance
    let G : EuclideanSpace ℂ (Cfg d (m + R - 1)) →L[ℂ] EuclideanSpace ℂ (Cfg d (m + R - 1)) :=
      LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (parentChainInteraction A R (m + R - 1)).hamiltonian)
    have hFiber :=
      LinearMap.IsPositive.quadraticForm_sq_ge_rightFiberwiseMap_of_forall_hasEigenvalue
        (S := Cfg d (N - (m + R - 1))) G
        (Matrix.isPositive_toEuclideanLin_iff.mpr
          (posSemidef_hamiltonian_parentChainInteraction A R (m + R - 1))) hγ.le hOpenGap
    have hApply : U (ProjectionGeometry.cyclicWindowSum P m s x) =
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - (m + R - 1))) G (U x) := by
      rw [ManyBody.Interaction.cyclicWindowSum_toEuclideanLin_translationInvariant_term _ hR hWN]
      exact cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply hWN _ _ x
    have h := hFiber (U x)
    rwa [← hApply, U.inner_map_map, U.inner_map_map] at h
  refine FrustrationFree.forall_hasEigenvalue_of_martingale_of_finiteDimensional hδ
    (Matrix.isPositive_toEuclideanLin_iff.mpr hPSD) fun x ↦ ?_
  have hx := ProjectionGeometry.quadraticForm_sum_projections_of_cyclic_knabe P hProj hN hR hmR
    (fun e heR heN s y ↦ by
      have h := congrArg (fun M ↦ Matrix.toEuclideanLin M y)
        (ManyBody.Interaction.commute_translationInvariant_term_finEquiv_symm_add_of_le
          (LinearMap.toMatrix' (parentInteraction A R))
          (LinearMap.toMatrix' (parentInteraction A R)) heR heN s).eq
      simpa only [P, Matrix.toEuclideanLin_mul, LinearMap.comp_apply] using h)
    (γ := γ) rfl hnum hWindowGap x
  rwa [ManyBody.Interaction.sum_toEuclideanLin_translationInvariant_term_finEquiv_symm] at hx

end MPSTensor

namespace Kraus.HasComplementaryFixedPointGap

open MPSTensor

variable {d D : ℕ}

/-- A primitive MPS has a positive finite-range Knabe gap for its canonical
range-\(l + 1\) parent Hamiltonian on every periodic chain with \(N \geq 2m\).

The open coefficient is
\(\gamma = (1 - \varepsilon\sqrt{l + 1})^2\), the active Knabe volume is \(m + l\), and
\(m\) is chosen so that \(l^2 < m\gamma\). -/
theorem exists_hamiltonian_parentRingInteraction_gap_of_finiteRangeKnabe
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : Matrix.PosDef ρ) :
    ∃ l : ℕ, ∃ ε : ℝ, ∃ m : ℕ, ∃ δ : ℝ,
      1 < l ∧ Kraus.IsNBlkInjective A l ∧
      0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      l + 1 ≤ m ∧
      δ = ((m : ℝ) * (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 -
          (l : ℝ) ^ 2) / ((m : ℝ) - (l : ℝ)) ∧
      0 < δ ∧
      ∀ (N : ℕ) [NeZero N], 2 * m ≤ N →
        ∀ μ : ℂ, Module.End.HasEigenvalue
          (Matrix.toEuclideanLin (parentRingInteraction A (l + 1) N).hamiltonian) μ →
            μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨l, ε, hl, hInj, hε, hεlt, hOpenGap⟩ :=
    hP.exists_hamiltonian_parentChainInteraction_gap hρ
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
  have hOpenGap' : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A (l + 1) (m + l)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ := hOpenGap (m + l) (by omega)
  have hPeriodic := hamiltonian_parentRingInteraction_gap_of_hamiltonian_parentChainInteraction_gap
    A (R := l + 1) (m := m) (by omega) hm (γ := γ) (by simpa using hnum) hOpenGap'
  refine ⟨l, ε, m, δ, hl, hInj, hε, hεlt, hm, ?_, ?_⟩
  · dsimp only [δ, γ]
    congr 1
    push_cast
    ring
  · exact ⟨by simpa [δ, γ] using hPeriodic.1,
      fun N _ hN ↦ by simpa [δ, γ] using hPeriodic.2 N hN⟩

end Kraus.HasComplementaryFixedPointGap

end

section

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A positive gap of the open-chain parent Hamiltonians on all sufficiently large multiples of
a fixed positive integer implies a positive gap of the Hamiltonians of the parent interaction on
every sufficiently large ring. Each gap is stated above the kernel: every eigenvalue is `0` or at
least the gap. This applies to the divisible open lengths in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii), using the finite-range comparison in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem exists_hamiltonian_parentRingInteraction_gap_of_eventually_divisible_gap
    (A : MPSTensor d D) {p R : ℕ} (hp : 1 ≤ p) (hR : 1 ≤ R)
    {γ : ℝ} (hγ : 0 < γ)
    (hOpen : ∀ᶠ M : ℕ in atTop, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R (p * M)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ [NeZero N], ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨n, hn⟩ := exists_lt_nsmul hγ (((R : ℝ) - 1) ^ 2)
  obtain ⟨M, hM, hGap⟩ := ((eventually_ge_atTop (n + 2 * R)).and hOpen).exists
  have hMp : M ≤ p * M := by nlinarith
  let m := p * M - R + 1
  have hm : R ≤ m ∧ n ≤ m ∧ m + R - 1 = p * M := by omega
  have hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ := by
    exact hn.trans_le (by simpa only [nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm.2.1) hγ.le)
  obtain ⟨hδ, hPeriodic⟩ :=
    hamiltonian_parentRingInteraction_gap_of_hamiltonian_parentChainInteraction_gap
      A hR hm.1 hnum (hm.2.2.symm ▸ hGap)
  exact ⟨_, hδ, (eventually_ge_atTop (2 * m)).mono fun N hN _ ↦ hPeriodic N hN⟩

end MPSTensor

end
