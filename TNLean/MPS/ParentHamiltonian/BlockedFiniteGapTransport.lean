/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedInteractionKernel
import TNLean.Algebra.MatrixReindexGap
import TNLean.MPS.ParentHamiltonian.Martingale.EventualKernelOpenGap
import TNLean.MPS.ParentHamiltonian.PeriodicGroundStatePresentation
import TNLean.MPS.ParentHamiltonian.GaugePhaseSeparationTransport

/-!
# Finite-chain gap transfer through physical blocking

A positive original interaction of range \(R>0\) defines a coarse
interaction by taking its complete open Hamiltonian on \(KL\) sites and
regrouping the configurations into \(K\) sites of size \(L\). Provided
\(R+L\leq KL+1\), the coarse open sum on \(N\geq K\) sites contains
all original windows on \(NL\) sites, with multiplicity at most
\(KL+1-R\). A coarse norm gap therefore gives an original norm gap
with that divisor, on the orthogonal complement of the entire kernel.

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

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace
namespace MPSTensor
variable {d R L K N : ℕ} [NeZero d] [NeZero L]

/-- A coarse open-chain gap transfers to the original volume of length
\(NL\), with divisor \(KL+1-R\). The kernels coincide by the
positive window comparison. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, equations (3.12)--(3.14). -/
theorem openInteractionMatrix_gap_of_blocked_gap
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hK : 0 < K) (hKN : K ≤ N) (hcover : R + L ≤ K * L + 1)
    {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
      (openInteractionMatrix (blockedInteractionMatrix h L K) N)))ᗮ,
      γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
        (openInteractionMatrix (blockedInteractionMatrix h L K) N) v‖) :
    ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
      (openInteractionMatrix h (N * L))))ᗮ,
      (γ / (K * L + 1 - R : ℕ)) * ‖v‖ ≤
        ‖Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) v‖ := by
  obtain ⟨hLower, hUpper⟩ :=
    openInteractionMatrix_blockedInteractionMatrix_comparison h hh hR hK hKN hcover
  have hLower' : Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) ≤
      Matrix.toEuclideanLin (Matrix.reindex (blockedConfigEquiv d N L)
        (blockedConfigEquiv d N L)
        (openInteractionMatrix (blockedInteractionMatrix h L K) N)) := by
    rw [LinearMap.le_def, ← map_sub, Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.le_iff.mp hLower
  have hUpper' : Matrix.toEuclideanLin (Matrix.reindex (blockedConfigEquiv d N L)
      (blockedConfigEquiv d N L)
      (openInteractionMatrix (blockedInteractionMatrix h L K) N)) ≤
      ((K * L + 1 - R : ℕ) : ℂ) •
        Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) := by
    rw [← map_smul, LinearMap.le_def, ← map_sub, Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.le_iff.mp hUpper
  have hQ := Matrix.isPositive_toEuclideanLin_iff.mpr
    (openInteractionMatrix_posSemidef h hh hR (N * L))
  have hP := LinearMap.nonneg_iff_isPositive.mp
    ((LinearMap.nonneg_iff_isPositive.mpr hQ).trans hLower')
  have hM : 0 < ((K * L + 1 - R : ℕ) : ℝ) := by
    have hL := NeZero.pos L
    exact_mod_cast (show 0 < K * L + 1 - R by omega)
  have hGap' := Matrix.norm_gap_toEuclideanLin_reindex
    (blockedConfigEquiv d N L)
    (openInteractionMatrix (blockedInteractionMatrix h L K) N) hGap
  have hTransfer := hP.norm_gap_of_smul_le_of_le_smul hQ
    zero_lt_one hM hM hγ
    (by simpa only [Complex.ofReal_one, one_smul, Complex.ofReal_natCast] using hUpper')
    (smul_le_smul_of_nonneg_left hLower'
      (show (0 : ℂ) ≤ ((K * L + 1 - R : ℕ) : ℝ) by exact_mod_cast hM.le)) hGap'
  simpa only [one_mul] using hTransfer
variable {b D : ℕ} {E : Fin b → ℕ} [∀ j, NeZero (E j)]
/-- An exact blocked primitive representation and eventual original MPS
kernels give a uniform norm gap at every block-divisible volume, including
short volumes with their actual kernels. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 3, equations (3.12)--(3.14). -/
theorem exists_aligned_openInteractionMatrix_gap_of_blocked_primitive_family
    (A : MPSTensor d D) (μ : Fin b → ℂ)
    (B : ∀ j, MPSTensor (blockPhysDim d L) (E j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (E j)) (Fin (E j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : E j = E i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hJoint : ∀ N, groundSpaceES (blockTensor A L) N =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hK : 0 < K) (hcover : R + L ≤ K * L + 1)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) n) =
        groundSpaceES A n) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (openInteractionMatrix h (N * L))))ᗮ,
        γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) v‖ := by
  have hker' :=
    eventually_ker_openInteractionHamiltonianES_blockedInteractionMatrix_eq_groundSpaceES
      A h hh hR hK hcover hker
  obtain ⟨γ, hγ, hGap⟩ := exists_openInteractionMatrix_gap_of_eventual_kernel
    μ B hμ ρ hP hρ hDistinct hK (blockedInteractionMatrix h L K)
    (blockedInteractionMatrix_posSemidef h hh hR L K)
    (hker'.mono fun N hN => hN.trans (hJoint N))
  have hM : 0 < ((K * L + 1 - R : ℕ) : ℝ) := by
    have hL := NeZero.pos L
    exact_mod_cast (show 0 < K * L + 1 - R by omega)
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ ∀ v ∈ (LinearMap.ker
      (Matrix.toEuclideanLin (openInteractionMatrix h (N * L))))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h (N * L)) v‖)
    (fun N δ ε hle hgap v hv ↦
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv))
    (fun N ↦ LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (Matrix.toEuclideanLin (openInteractionMatrix h (N * L))))
    (M := K) (δ := γ / (K * L + 1 - R : ℕ)) (div_pos hγ hM) ?_
  intro N hKN
  apply openInteractionMatrix_gap_of_blocked_gap h hh hR hK hKN hcover hγ
  simpa only [openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix
    (blockedInteractionMatrix h L K) hK hKN] using hGap N
/-- A periodic tensor and the eventual original open-chain kernel identity
derive a uniform norm gap at every period-divisible volume. No primitive
sector witnesses are supplied. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and the regrouping at lines 825--836. -/
theorem IsPeriodic.exists_aligned_openInteractionMatrix_gap_of_eventual_kernel
    {m : ℕ} {A : MPSTensor d D} (hA : IsPeriodic m A)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hR : 0 < R)
    (hker : ∀ᶠ n in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) n) =
        groundSpaceES A n) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (openInteractionMatrix h (N * m))))ᗮ,
        γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (openInteractionMatrix h (N * m)) v‖ := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨g, _hg, dim, hdim, B, ρ, hP, hρ, hDistinct, hJoint⟩ :=
    hA.exists_inequivalent_primitive_groundStatePresentation
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hDistinct' : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := hDistinct.forall_ne_transport
  exact exists_aligned_openInteractionMatrix_gap_of_blocked_primitive_family
    (K := R + 1) A (fun _ => 1) B (fun _ => one_ne_zero)
    ρ hP hρ hDistinct' hJoint h hh hR (by omega)
    (by nlinarith [hA.period_pos]) hker
end MPSTensor
