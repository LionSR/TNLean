/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Hermitian.MatrixScalarIdentity
import TNLean.MPS.Examples.AKLT.AKLT
import TNLean.MPS.Symmetry.StringOrder.StringOrder
import TNLean.MPS.Tensor.Gauge.OnSiteSymmetry
import TNLean.MPS.Tensor.Physical.Blocking
import TNLean.MPS.Tensor.Chain.BlockedChainFT
import TNLean.MPS.Examples.Cluster.Cluster
import TNLean.MPS.Transfer.Correlation.EntanglementSpectrum

/-!
# String order of the AKLT state under its `Z₂ × Z₂` symmetry

This module proves virtual-boundary nondecay for each `Z₂ × Z₂` symmetry twist
of the blocked AKLT tensor. The single-site tensor is not injective, only
normal (`2`-block injective), so the virtual-boundary criterion is applied to
the length-`2` blocked tensor. The unblocked physical endpoint calculation
is in `AKLTPhysicalStringOrder`.

## Main definitions

* `akltBlocked` : the length-`2` blocked AKLT tensor (physical dimension `9`)
* `akltBlockedZ2Z2Action` : the `Z₂ × Z₂` on-site representation on the blocked
  physical space, the Kronecker squares of the two spin-`1` `π`-rotations

## Main results

* `akltBlocked_isInjective` : the blocked tensor is injective
* `aklt_blocked_isOnSiteSymmetric_Z2Z2` : the blocked tensor is on-site symmetric
  under `Z₂ × Z₂`
* `aklt_hasStringOrder` : virtual-boundary nondecay for every `Z₂ × Z₂` twist,
  including the identity, with the maximally mixed boundary state
* `MPSTensor.akltBlocked_even_finrank_eigenspace`,
  `MPSTensor.clusterBlocked_even_finrank_eigenspace`: AKLT and cluster states: doubly degenerate
  entanglement spectrum.

## References

* Affleck, Kennedy, Lieb, Tasaki (1987) — original AKLT construction
* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447 (PRL 2008) —
  string order and local symmetry for finitely correlated states
* RMP review (arXiv:2011.12127) Section III.A
-/

section AKLTStringOrder

open scoped Matrix BigOperators
open Matrix Finset MPSTensor
open Kraus (blockPhysDim blockTensor isNBlkInjective_iff_blockTensor_isInjective)

noncomputable section

namespace MPSTensor

/-! ### The length-`2` blocked AKLT tensor and its string order

The single-site AKLT tensor is not injective, only normal; the string-order
criterion requires injectivity, so it is applied to the length-`2` blocked
tensor.  The on-site `Z₂ × Z₂` symmetry of the single-site tensor lifts to the
blocked tensor through the Kronecker-power action `blockKronAction`. -/

section AKLT

open scoped ComplexOrder MatrixOrder

/-- The length-`2` blocked AKLT tensor (physical dimension `9 = 3²`). -/
noncomputable def akltBlocked : MPSTensor (blockPhysDim 3 2) 2 :=
  blockTensor akltTensor 2

/-- The length-`2` blocked AKLT tensor is injective: its matrices span `M₂(ℂ)`.
This is the blocked-tensor form of `aklt_isNBlkInjective_two`. -/
theorem akltBlocked_isInjective : Kraus.IsInjective akltBlocked :=
  (isNBlkInjective_iff_blockTensor_isInjective akltTensor 2).1 aklt_isNBlkInjective_two

/-- The `Z₂ × Z₂` on-site representation on the blocked AKLT physical space, the
Kronecker square of the two single-site spin-`1` `π`-rotations. -/
noncomputable def akltBlockedZ2Z2Action :
    Multiplicative (ZMod 2 × ZMod 2) →*
      Matrix (Fin (blockPhysDim 3 2)) (Fin (blockPhysDim 3 2)) ℂ :=
  blockKronAction 2 akltZ2Z2Action

/-- The blocked AKLT tensor is on-site symmetric under `Z₂ × Z₂`, with each group
element acting by the Kronecker square of the corresponding spin-`1` `π`-rotation.
The bond gauges are the same anticommuting virtual gauges `σz` and `iσy` as for
the single-site tensor, so the blocked tensor realizes the same non-trivial SPT
phase. -/
theorem aklt_blocked_isOnSiteSymmetric_Z2Z2 :
    IsOnSiteSymmetric akltBlocked akltBlockedZ2Z2Action :=
  isOnSiteSymmetric_blockTensor akltTensor akltZ2Z2Action 2 aklt_isOnSiteSymmetric_Z2Z2

/-! #### Normalization of the blocked AKLT transfer map -/

/-- The single-site AKLT tensor is right-canonical: `∑ Aᵢ Aᵢ† = 1`.  This is the
matrix-identity value of `aklt_transferMap_one`. -/
private theorem aklt_sum_mul_conjTranspose :
    ∑ i : Fin 3, akltTensor i * (akltTensor i)ᴴ = 1 := by
  have h := aklt_transferMap_one
  rw [Kraus.transferMap_apply] at h
  simpa only [Matrix.mul_one] using h

/-- The single-site AKLT tensor is left-canonical: `∑ Aᵢ† Aᵢ = 1`.  Together with
right-canonicity this makes the channel both trace preserving and unital. -/
private theorem aklt_sum_conjTranspose_mul :
    ∑ i : Fin 3, (akltTensor i)ᴴ * akltTensor i = 1 := by
  rw [Fin.sum_univ_three]
  simp only [akltTensor_conjTranspose]
  ext a b
  simp only [akltTensor, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
    mul_neg, neg_mul, neg_neg, Matrix.one_apply]
  have hdiag : (↑(1 / Real.sqrt 3) : ℂ) * ↑(1 / Real.sqrt 3) +
      (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) * ↑(Real.sqrt 2 / Real.sqrt 3) = 1 := by
    have hr : (1 / Real.sqrt 3) * (1 / Real.sqrt 3) +
        (Real.sqrt 2 / Real.sqrt 3) * (Real.sqrt 2 / Real.sqrt 3) = 1 := by
      rw [div_mul_div_comm, div_mul_div_comm, one_mul,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3),
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, hr,
      Complex.ofReal_one]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_ne_zero, zero_ne_one, ite_true, ite_false, mul_zero,
      zero_mul, mul_one, add_zero, zero_add, neg_zero, mul_neg, neg_mul, neg_neg] <;>
    exact hdiag

/-- The blocked AKLT transfer map is unital: `∑ Bᵢ Bᵢ† = 1`.  Right-canonicity of
the single-site letters propagates to length-`2` words. -/
theorem akltBlocked_transferMap_one : Kraus.transferMap akltBlocked 1 = 1 := by
  classical
  rw [Kraus.transferMap_apply]
  simp only [Matrix.mul_one, akltBlocked, Kraus.blockTensor, Kraus.reindexPhysical,
    Kraus.block_apply, Kraus.decodeBlockEquiv_apply]
  rw [Fintype.sum_equiv (Kraus.decodeBlockEquiv 3 2)
    (fun I => Kraus.evalWord akltTensor (List.ofFn (Kraus.decodeBlock 3 2 I)) *
      (Kraus.evalWord akltTensor (List.ofFn (Kraus.decodeBlock 3 2 I)))ᴴ)
    (fun ρ => Kraus.evalWord akltTensor (List.ofFn ρ) * (Kraus.evalWord akltTensor (List.ofFn ρ))ᴴ)
    (fun I => by rw [Kraus.decodeBlockEquiv_apply])]
  exact sum_evalWord_mul_conjTranspose_evalWord akltTensor aklt_sum_mul_conjTranspose 2

/-- The maximally mixed boundary state `Λ = (1/2)·1` is a fixed point of the
blocked adjoint transfer map: `∑ Bᵢ† Λ Bᵢ = Λ`.  Left-canonicity of the
single-site letters propagates to length-`2` words. -/
private theorem akltBlocked_adjoint_fixes_maximallyMixed :
    Kraus.transferMap (fun i => (akltBlocked i)ᴴ) ((1 / 2 : ℂ) • 1) = (1 / 2 : ℂ) • 1 := by
  classical
  have hleft : ∑ i : Fin (blockPhysDim 3 2),
      (akltBlocked i)ᴴ * akltBlocked i = 1 := by
    simpa only [akltBlocked] using
      leftCanonical_blockTensor akltTensor 2 aklt_sum_conjTranspose_mul
  rw [Kraus.transferMap_apply]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]
  rw [← Finset.smul_sum, hleft]

/-- The blocked `Z₂ × Z₂` representation is unitary on every group element.  The
single-site representation is unitary (`aklt_isUnitary_Z2Z2`) and the Kronecker
power preserves unitarity. -/
theorem akltBlockedZ2Z2Action_unitary (g : Multiplicative (ZMod 2 × ZMod 2)) :
    akltBlockedZ2Z2Action g * (akltBlockedZ2Z2Action g)ᴴ = 1 := by
  rw [akltBlockedZ2Z2Action, blockKronAction_apply]
  exact blockKron_mul_conjTranspose 2 (akltZ2Z2Action g) (aklt_isUnitary_Z2Z2 g)

/-- The blocked AKLT tensor has virtual-boundary nondecay for every element of
its `Z₂ × Z₂` symmetry, including the identity.

The tensor is injective and on-site symmetric. The maximally mixed state
`Λ = (1/2)·1` is a faithful trace-one fixed point of the adjoint transfer map,
and the transfer map is unital. These conditions give fixed-twist nondecay
with arbitrary virtual boundary matrices. The physical endpoint condition of
arXiv:0802.0447 is treated separately; see
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`. -/
theorem aklt_hasStringOrder (g : Multiplicative (ZMod 2 × ZMod 2)) :
    HasStringOrder akltBlocked (akltBlockedZ2Z2Action g)
      ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
  hasStringOrder_of_symmetric_injective akltBlocked akltBlocked_isInjective
    akltBlockedZ2Z2Action aklt_blocked_isOnSiteSymmetric_Z2Z2 akltBlockedZ2Z2Action_unitary g
    ((1 / 2 : ℂ) • 1)
    (Matrix.PosDef.smul_one (by norm_num))
    (by rw [Matrix.trace_smul_one]; norm_num)
    akltBlocked_adjoint_fixes_maximallyMixed akltBlocked_transferMap_one

end AKLT

end MPSTensor

end

end AKLTStringOrder

section SPTEntanglementSpectrum

/-!
## AKLT and cluster states: doubly degenerate entanglement spectrum

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
paragraph "Entanglement spectrum and edge modes",
`Papers/2011.12127/TN-Review-main.tex` line 1171: a non-trivial SPT phase has
an entanglement spectrum in which every eigenvalue is degenerate, because the
projective virtual representation has no one-dimensional invariant subspace.
Review: arXiv:2011.12127, Appendix A, "The AKLT state" and "The cluster state".

**Formalized here.** For the length-`2` blocked AKLT tensor and the length-`2`
blocked cluster tensor, both injective, every positive definite fixed point `Λ` of
the adjoint transfer map has only even-dimensional eigenspaces.  The anticommuting
virtual gauges of the two `Z₂` generators (`iσy`, `σz` for AKLT; `σz`, `σx` for
the cluster state) enter through
`MPSTensor.even_finrank_eigenspace_of_anticommuting_gauges`.

### Main results

* `MPSTensor.akltBlocked_even_finrank_eigenspace`
* `MPSTensor.clusterBlocked_even_finrank_eigenspace`

### References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Kraus (blockPhysDim)

namespace MPSTensor

variable {d D : ℕ}

/-- An intertwining relation `Tᵢ R = R Aᵢ` is the gauge relation `Tᵢ = 1 · R Aᵢ R⁻¹`. -/
private lemma eq_one_smul_conj_of_intertwine {T A : Matrix (Fin D) (Fin D) ℂ}
    (R : GL (Fin D) ℂ) (h : T * R = R * A) :
    T = (1 : ℂ) • ((R : Matrix (Fin D) (Fin D) ℂ) * A *
      ((R⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  rw [one_smul, ← h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- **Doubly degenerate entanglement spectrum of the AKLT state.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1171).  Every eigenspace of every positive definite fixed point of the
adjoint transfer map of the blocked AKLT tensor has even dimension. -/
theorem akltBlocked_even_finrank_eigenspace {Λ : Matrix (Fin 2) (Fin 2) ℂ}
    (hΛpos : Λ.PosDef) (hΛfix : Kraus.transferMap (fun i => (akltBlocked i)ᴴ) Λ = Λ)
    (μ : ℂ) : Even (Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' Λ) μ)) := by
  have hgauge (g : Multiplicative (ZMod 2 × ZMod 2)) (I : Fin (blockPhysDim 3 2)) :
      ∑ j, akltBlockedZ2Z2Action g I j • akltBlocked j =
        (1 : ℂ) • ((akltProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ) * akltBlocked I *
          (((akltProjRep.X g)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [one_smul]
    exact twistedTensor_blockTensor_eq_gauge (fun i =>
      by simpa using eq_one_smul_conj_of_intertwine _ (akltTensor_twist_intertwine g i)) 2 I
  exact even_finrank_eigenspace_of_anticommuting_gauges akltBlocked_isInjective
    akltBlocked_transferMap_one hΛpos hΛfix (akltBlockedZ2Z2Action_unitary _)
    (akltBlockedZ2Z2Action_unitary _) one_ne_zero one_ne_zero
    (hgauge (Multiplicative.ofAdd (1, 0))) (hgauge (Multiplicative.ofAdd (0, 1)))
    akltProjRep_generators_anticomm μ

/-- **Doubly degenerate entanglement spectrum of the cluster state.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1171).  Every eigenspace of every positive definite fixed point of the
adjoint transfer map of the blocked cluster tensor has even dimension. -/
theorem clusterBlocked_even_finrank_eigenspace {Λ : Matrix (Fin 2) (Fin 2) ℂ}
    (hΛpos : Λ.PosDef) (hΛfix : Kraus.transferMap (fun i => (clusterBlocked i)ᴴ) Λ = Λ)
    (μ : ℂ) : Even (Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' Λ) μ)) := by
  have hgauge (g : Multiplicative (ZMod 2 × ZMod 2)) (I : Fin 4) :
      ∑ j, clusterZ2Z2Action g I j • clusterBlocked j =
        (1 : ℂ) • ((clusterProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ) * clusterBlocked I *
          (((clusterProjRep.X g)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :=
    eq_one_smul_conj_of_intertwine _ (clusterBlocked_twist_intertwine g I)
  exact even_finrank_eigenspace_of_anticommuting_gauges clusterBlocked_isInjective
    clusterBlocked_transferMap_one hΛpos hΛfix (clusterZ2Z2Action_unitary _)
    (clusterZ2Z2Action_unitary _) one_ne_zero one_ne_zero
    (hgauge (Multiplicative.ofAdd (1, 0))) (hgauge (Multiplicative.ofAdd (0, 1)))
    (by simpa [clusterProjRep, clusterRepX] using cluster_gauge_anticomm) μ

end MPSTensor

end SPTEntanglementSpectrum
