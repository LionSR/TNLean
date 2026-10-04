/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OneMagnon
import TNLean.Algebra.CycleLaplacianFourier
import TNLean.MPS.ParentHamiltonian.ShortRangeHeisenbergTensor
import TNLean.MPS.ParentHamiltonian.SingletChain

/-!
# A gapless short-range parent Hamiltonian of three normal blocks

The two-site parent interaction of the direct sum of the qubit product-state
blocks \(|0\rangle\), \(|1\rangle\), and \(|+\rangle\) is the singlet
projection. Its periodic Hamiltonian has a nonzero one-magnon eigenvector
with eigenvalue \(1-\cos(2\pi/N)\). These positive eigenvalues tend to zero,
so there is no positive gap uniform over all sufficiently long rings.

This refutes the unrestricted assertion in arXiv:2011.12127, Section IV.C,
lines 2183--2187. The example has interaction range two and simultaneous
injectivity length two, whereas the sufficient-range theorems require a
range strictly larger than that length. See
`docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.
-/

open scoped InnerProductSpace ComplexOrder

namespace MPSTensor

/-- The first Fourier one-magnon vector on the ring. -/
noncomputable def shortRangeHeisenbergMagnon (N : ℕ) [NeZero N] :
    EuclideanSpace ℂ (Cfg 2 N) :=
  WithLp.toLp 2 (SpinChain.oneMagnon (fun j => ZMod.stdAddChar (ZMod.finEquiv N j)))

/-- The Fourier one-magnon vector has coefficient one at the spin configuration
whose unique down spin lies at the zero site, and hence is nonzero. -/
theorem shortRangeHeisenbergMagnon_ne_zero (N : ℕ) [NeZero N] :
    shortRangeHeisenbergMagnon N ≠ 0 := by
  intro h
  have hz := congrArg (fun v : EuclideanSpace ℂ (Cfg 2 N) =>
    v (SpinChain.singleDown ((ZMod.finEquiv N).symm 0))) h
  change SpinChain.oneMagnon (fun j => ZMod.stdAddChar (ZMod.finEquiv N j))
    (SpinChain.singleDown ((ZMod.finEquiv N).symm 0)) = 0 at hz
  exact one_ne_zero (by simpa only [SpinChain.oneMagnon_singleDown,
    RingEquiv.apply_symm_apply, AddChar.map_zero_eq_one] using hz)

/-- On a ring of at least two sites the first Fourier magnon is an eigenvector
of the two-site parent Hamiltonian, with eigenvalue \(1-\cos(2\pi/N)\).
This is the periodic version of the one-magnon recurrence in
Koma--Nachtergaele, arXiv:cond-mat/9512120, Lemma 4, equation (3.13). -/
theorem parentHamiltonianES_shortRangeHeisenbergMagnon {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) :
    parentHamiltonianES shortRangeHeisenbergTensor 2 N (shortRangeHeisenbergMagnon N) =
      (ZMod.cycleFourierGap N : ℂ) • shortRangeHeisenbergMagnon N := by
  apply PiLp.ext
  intro σ
  rw [parentHamiltonianES_apply_of_singlet_parentInteraction shortRangeHeisenbergTensor
    parentInteractionES_shortRangeHeisenbergTensor_two_apply hN]
  change (∑ i : Fin N,
    (SpinChain.oneMagnon (fun j => ZMod.stdAddChar (ZMod.finEquiv N j)) σ -
      SpinChain.oneMagnon (fun j => ZMod.stdAddChar (ZMod.finEquiv N j))
        (σ ∘ Equiv.swap i (cyclicForwardSite i 1)))) / 2 =
    (ZMod.cycleFourierGap N : ℂ) *
      SpinChain.oneMagnon (fun j => ZMod.stdAddChar (ZMod.finEquiv N j)) σ
  simp_rw [← cyclicSuccessorEquiv_apply]
  rw [SpinChain.oneMagnon_edge_sum (cyclicSuccessorEquiv N) (cyclicSuccessorEquiv_ne hN)]
  have hc (j : Fin N) :
      ZMod.stdAddChar (ZMod.finEquiv N j) -
        (ZMod.stdAddChar (ZMod.finEquiv N (cyclicSuccessorEquiv N j)) +
          ZMod.stdAddChar (ZMod.finEquiv N ((cyclicSuccessorEquiv N).symm j))) / 2 =
        (ZMod.cycleFourierGap N : ℂ) * ZMod.stdAddChar (ZMod.finEquiv N j) := by
    simpa only [ZMod.cycleLaplacian, finEquiv_cyclicSuccessorEquiv,
      finEquiv_cyclicSuccessorEquiv_symm] using
      ZMod.cycleLaplacian_stdAddChar (ZMod.finEquiv N j)
  simp_rw [hc]
  exact SpinChain.oneMagnon_smul _ _ _

private theorem norm_gap_le_of_positive_eigenvector {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) {v : E} {η δ : ℝ}
    (hη : 0 < η) (hne : v ≠ 0) (hv : H v = (η : ℂ) • v)
    (hgap : ∀ w ∈ (LinearMap.ker H)ᗮ, δ * ‖w‖ ≤ ‖H w‖) : δ ≤ η := by
  have horth : v ∈ (LinearMap.ker H)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have h := hH w v
    rw [LinearMap.mem_ker.mp hw, inner_zero_left, hv, inner_smul_right] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Complex.ofReal_ne_zero.mpr hη.ne')
  have hnorm : ‖H v‖ = η * ‖v‖ := by
    rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hne)).mp
    (by simpa only [hnorm, mul_comm] using hgap v horth)

/-- The canonical range-two parent Hamiltonian of the three normal product-state
blocks has no positive gap uniform over all sufficiently long periodic chains.
Thus the unrestricted parent-gap assertion of arXiv:2011.12127, Section IV.C,
lines 2183--2187, is false. The canonical normal-block certificates are proved
in `ShortRangeHeisenbergTensor`; the source error is recorded in
`docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`. -/
theorem not_exists_eventual_uniform_gap_shortRangeHeisenbergTensor_two :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES shortRangeHeisenbergTensor 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES shortRangeHeisenbergTensor 2 N v‖ := by
  rintro ⟨δ, hδ, N₀, hgap⟩
  obtain ⟨N, hN₀, hN, hη, hsmall⟩ :=
    ZMod.exists_large_cycleFourierGap_pos_lt hδ N₀
  let : NeZero N := ⟨by omega⟩
  have hbound := norm_gap_le_of_positive_eigenvector
    (parentHamiltonianES shortRangeHeisenbergTensor 2 N)
    (parentHamiltonianES_isPositive shortRangeHeisenbergTensor 2 N).isSymmetric
    hη (shortRangeHeisenbergMagnon_ne_zero N)
    (parentHamiltonianES_shortRangeHeisenbergMagnon hN) (hgap N hN₀)
  exact (not_le_of_gt hsmall) hbound

end MPSTensor
