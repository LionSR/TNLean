/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.SpectralProjection
import TNLean.MPS.Preparation.PositivePartRate

/-!
# Exact transfer stabilization when the subleading spectrum vanishes

For a normal left-canonical tensor with a normalized positive definite fixed
point, vanishing subleading transfer eigenvalues imply exact stabilization
after a finite blocking length. Nilpotent Jordan blocks are allowed, so the
transfer map need not equal its fixed-point projection at one site.

This is the finite-block endpoint of the transfer decomposition used in
arXiv:2307.01696, equations `eq:Ek_decomp` and `eq:B_TM`, and the normalized
normal-tensor setting at lines 413--421. It does not interpret the logarithmic
block prescription at lines 843--852 by substituting zero correlation length.

**Local fix (zero-spectrum endpoint):** The logarithmic block prescription is
replaced by a positive finite length when all subleading eigenvalues vanish.
See `docs/paper-gaps/mswc24_zero_subleading_spectrum_endpoint.tex`.
-/

open scoped Matrix ComplexOrder MatrixOrder

private theorem pow_finrank_eq_zero_of_eigenvalues_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V)
    (h : ∀ z : ℂ, f.HasEigenvalue z → z = 0) :
    f ^ Module.finrank ℂ V = 0 := by
  have htop : f.maxGenEigenspace 0 = ⊤ := by
    apply top_unique
    rw [← f.iSup_maxGenEigenspace_hasEigenvalue_eq_top]
    refine iSup_le fun z => iSup_le fun hz => ?_
    rw [h z hz]
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.genEigenspace_zero_nat] at htop
  exact LinearMap.ker_eq_top.mp htop

namespace MPSTensor

variable {d D : ℕ}

/-- A normal left-canonical tensor with vanishing subleading transfer spectrum
has transfer powers equal to the fixed-point projection for every length at
least the square of its virtual dimension. Nilpotent transients are included.

This gives the exact finite-block endpoint of arXiv:2307.01696,
`eq:Ek_decomp` and `eq:B_TM`, in the normalized normal-tensor setting at
lines 413--421. The additional zero-subleading-spectrum hypothesis selects
that endpoint; zero correlation length alone is not the hypothesis. -/
theorem transferMap_pow_eq_fixedPointProj_of_subleading_eigenvalues_eq_zero
    (A : MPSTensor d D) (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ)
    (hzero : ∀ μ : ℂ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → μ = 0)
    {n : ℕ} (hn : D ^ 2 ≤ n) :
    Kraus.transferMap A ^ n = fixedPointProj σ (by simp [htr]) := by
  classical
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  have htr' : σ.trace ≠ 0 := by simp [htr]
  let N := Kraus.transferMap A - fixedPointProj σ htr'
  have hspec : ∀ z : ℂ, Module.End.HasEigenvalue N z → z = 0 := by
    intro z hz
    have hbound := norm_le_of_hasEigenvalue_transferMap_sub_fixedPointProj A hNT hA hσ htr'
      hfix (lam₂ := 0) (fun μ hμ hμ1 => by rw [hzero μ hμ hμ1]) hz
    exact norm_le_zero_iff.mp (by simpa using hbound.2)
  have hnil : N ^ (D ^ 2) = 0 := by
    simpa [Module.finrank_matrix, pow_two] using
      pow_finrank_eq_zero_of_eigenvalues_eq_zero N hspec
  have hnpos : 1 ≤ n := (Nat.succ_le_of_lt (pow_pos (NeZero.pos D) 2)).trans hn
  rw [pow_eq_fixedPointProj_add_compl_pow (Kraus.transferMap A) htr'
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hA) hfix hnpos]
  change fixedPointProj σ htr' + N ^ n = fixedPointProj σ htr'
  rw [pow_eq_zero_of_le hn hnil, add_zero]

end MPSTensor
