/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedInteractionKernel
import QICLean.Spectral.Eigenvalue.MatrixReindexEuclidean
import TNLean.MPS.ParentHamiltonian.Interaction.EventualKernelOpenGap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicPrimitiveGroundSpace
import TNLean.MPS.CanonicalForm.BNT.Separation

/-!
# Finite-chain gap transfer through physical blocking

A positive original interaction of range \(R>0\) defines a coarse
interaction by taking its complete open Hamiltonian on \(KL\) sites and
regrouping the configurations into \(K\) sites of size \(L\). Provided
\(R+L\leq KL+1\), the coarse open sum on \(N\geq K\) sites contains
all original windows on \(NL\) sites, with multiplicity at most
\(KL+1-R\). A coarse gap above the kernel therefore gives an original gap above the
kernel, divided by that multiplicity: every nonzero eigenvalue is bounded below.

The generic finite-volume comparison requires no tensor or state data.
An exact blocked primitive representation and the eventual original kernel
identity give one gap for every volume divisible by the block length.
For a periodic tensor, that representation is derived from the period.

**Scope restriction (period-divisible volumes):** These uniform conclusions
concern the original volumes whose lengths are multiples of the blocking
length. The gap for all original residue lengths and for general GVBS
presentations remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
The representation hypothesis belongs only to the primitive-family result;
the periodic-tensor result derives its primitive witnesses internally.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.12)--(3.14), lines 1547--1570, and Theorem 1.2.
-/

open MPTensor

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace
open Kraus (blockPhysDim blockTensor)
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d R L K N : ℕ} [NeZero d] [NeZero L]

/-- A coarse open-chain gap transfers to the original volume of length
\(NL\), with divisor \(KL+1-R\). The kernels coincide by the
positive window comparison. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, equations (3.12)--(3.14). -/
theorem hamiltonian_chainTranslates_gap_of_blocked_gap
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hKN : K ≤ N) (hcover : R + L ≤ K * L + 1)
    {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        ((chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian)) z →
        z = 0 ∨ (γ : ℂ) ≤ z) :
    ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin ((chainTranslates R (N * L) h).hamiltonian)) z →
        z = 0 ∨ ((γ / (K * L + 1 - R : ℕ) : ℝ) : ℂ) ≤ z := by
  obtain ⟨hLower, hUpper⟩ :=
    hamiltonian_chainTranslates_blockedInteractionMatrix_comparison h hh hKN hcover
  have hLower' : Matrix.toEuclideanLin ((chainTranslates R (N * L) h).hamiltonian) ≤
      Matrix.toEuclideanLin (Matrix.reindex (Kraus.blockedConfigEquiv d N L)
        (Kraus.blockedConfigEquiv d N L)
        ((chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian)) := by
    rw [LinearMap.le_def, ← map_sub, Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.le_iff.mp hLower
  have hUpper' : Matrix.toEuclideanLin (Matrix.reindex (Kraus.blockedConfigEquiv d N L)
      (Kraus.blockedConfigEquiv d N L)
      ((chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian)) ≤
      ((K * L + 1 - R : ℕ) : ℂ) •
        Matrix.toEuclideanLin ((chainTranslates R (N * L) h).hamiltonian) := by
    rw [← map_smul, LinearMap.le_def, ← map_sub, Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.le_iff.mp hUpper
  have hQ := Matrix.isPositive_toEuclideanLin_iff.mpr
    (hamiltonian_chainTranslates_posSemidef h hh (N * L))
  have hP := LinearMap.nonneg_iff_isPositive.mp
    ((LinearMap.nonneg_iff_isPositive.mpr hQ).trans hLower')
  have hM : 0 < ((K * L + 1 - R : ℕ) : ℝ) := by
    have hL := NeZero.pos L
    exact_mod_cast (show 0 < K * L + 1 - R by omega)
  have hGap' : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (Matrix.reindex (Kraus.blockedConfigEquiv d N L) (Kraus.blockedConfigEquiv d N L)
        ((chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian))) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ := fun μ hμ ↦
    hGap μ ((Matrix.hasEigenvalue_toEuclideanLin_reindex_iff (Kraus.blockedConfigEquiv d N L)
      ((chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian) μ).mp hμ)
  have hTransfer := hP.forall_hasEigenvalue_of_smul_le_of_le_smul hQ
    zero_lt_one hM hM hγ
    (by simpa only [Complex.ofReal_one, one_smul, Complex.ofReal_natCast] using hUpper')
    (smul_le_smul_of_nonneg_left hLower'
      (show (0 : ℂ) ≤ ((K * L + 1 - R : ℕ) : ℝ) by exact_mod_cast hM.le)) hGap'
  simpa only [one_mul] using hTransfer

variable {b D : ℕ} {E : Fin b → ℕ} [∀ j, NeZero (E j)]
/-- An exact blocked primitive representation and eventual original MPS
kernels give a uniform gap above the kernel at every block-divisible volume, including
short volumes with their actual kernels. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 3, equations (3.12)--(3.14). -/
theorem exists_aligned_hamiltonian_chainTranslates_gap_of_blocked_primitive_family
    (A : MPSTensor d D) (μ : Fin b → ℂ)
    (B : ∀ j, MPSTensor (blockPhysDim d L) (E j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (E j)) (Fin (E j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : E j = E i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hJoint : ∀ N, groundSpaceES (blockTensor A L) N =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hcover : R + L ≤ K * L + 1)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R n h).hamiltonian) =
        groundSpaceES A n) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin ((chainTranslates R (N * L) h).hamiltonian)) z →
          z = 0 ∨ (γ : ℂ) ≤ z := by
  have hker' :=
    eventually_ker_hamiltonian_chainTranslates_blockedInteractionMatrix_eq_groundSpaceES
      A h hh (K := K) hcover hker
  obtain ⟨γ, hγ, hGap⟩ := exists_hamiltonian_chainTranslates_gap_of_eventual_kernel
    μ B hμ ρ hP hρ hDistinct (blockedInteractionMatrix h L K)
    (blockedInteractionMatrix_posSemidef h hh L K)
    (hker'.mono fun N hN => hN.trans (hJoint N))
  have hM : 0 < ((K * L + 1 - R : ℕ) : ℝ) := by
    have hL := NeZero.pos L
    exact_mod_cast (show 0 < K * L + 1 - R by omega)
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ ∀ z : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin ((chainTranslates R (N * L) h).hamiltonian)) z →
        z = 0 ∨ (δ : ℂ) ≤ z)
    (fun N δ ε hle hgap ↦ ManyBody.forall_hasEigenvalue_mono hle hgap)
    (fun N ↦ ManyBody.exists_pos_forall_hasEigenvalue
      (hamiltonian_chainTranslates_posSemidef h hh (N * L)))
    (M := K) (δ := γ / (K * L + 1 - R : ℕ)) (div_pos hγ hM) ?_
  intro N hKN
  exact hamiltonian_chainTranslates_gap_of_blocked_gap h hh hKN hcover hγ (hGap N)

/-- A periodic tensor and the eventual original open-chain kernel identity
derive a uniform gap above the kernel at every period-divisible volume. No primitive
sector witnesses are supplied. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and the regrouping at lines 825--836. -/
theorem IsPeriodic.exists_aligned_hamiltonian_chainTranslates_gap_of_eventual_kernel
    {m : ℕ} {A : MPSTensor d D} (hA : IsPeriodic m A)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R n h).hamiltonian) =
        groundSpaceES A n) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ z : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin ((chainTranslates R (N * m) h).hamiltonian)) z →
          z = 0 ∨ (γ : ℂ) ≤ z := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨g, _hg, dim, hdim, B, ρ, hP, hρ, hDistinct, hJoint⟩ :=
    hA.exists_inequivalent_primitive_groundStatePresentation
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hDistinct' : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := hDistinct.forall_ne_transport
  exact exists_aligned_hamiltonian_chainTranslates_gap_of_blocked_primitive_family
    (K := R + 1) A (fun _ => 1) B (fun _ => one_ne_zero)
    ρ hP hρ hDistinct' hJoint h hh
    (by nlinarith [hA.period_pos]) hker
end MPSTensor
