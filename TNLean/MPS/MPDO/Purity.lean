/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.MPS.MPDO.VerticalCF
import TNLean.MPS.Overlap.Basic

/-!
# The doubled-index overlap identity for an MPO tensor

For an MPO tensor `K : MPOTensor d D`, the doubled-index MPS tensor
`K.toMPSTensor` has physical index type `Fin (d * d)`.  This file proves the
project derivation identifying the self-overlap of that doubled-index MPS
family at chain length `N` with the Hilbert--Schmidt trace of the MPO:

```
MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N
  = Matrix.trace (mpo K N * (mpo K N)ᴴ)
```

Both sides are sums over physical configurations: the left side runs over doubled-index
words `Fin N → Fin (d * d)`, while the right side expands to the Frobenius
inner product `∑_{σ,τ} mpo K N σ τ * star (mpo K N σ τ)` over pairs `(σ, τ)`
of ket/bra configurations.  The proof is a finite reindexing along the
product encoding `finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)`, using the
entry formula `MPSTensor.mpv_toMPSTensor_pairConfig`.

**Naming.**  The codebase has no separate purity predicate, so the results are
stated in trace form and in the Frobenius-norm vocabulary of
`TNLean.Algebra.MatrixAux`.  Following the convention of the eta-local
structure paper-gap note
(`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`), the
unnormalized quantity `Matrix.trace (mpo K N * (mpo K N)ᴴ)` is called the
*raw squared Hilbert--Schmidt norm* of the MPO family; it is not a
normalized-state purity, which would require the trace normalization that has
not been established here.

## Main declarations

* `MPOTensor.pairCfgEquiv`: reindexing equivalence between pairs of ket/bra
  configurations and doubled-index configurations.
* `MPOTensor.mpvOverlap_toMPSTensor_self`: the doubled-index overlap identity.
* `MPOTensor.mpvOverlap_toMPSTensor_self_eq_trace_sq`: under the MPDO
  positivity hypothesis, Hermiticity identifies the overlap with
  `Matrix.trace (mpo K N * mpo K N)`.
* `MPOTensor.mpvOverlap_toMPSTensor_self_re_eq_frobenius_norm_sq`: the real
  part of the overlap is the squared Frobenius norm of the MPO.

## Source fidelity

These identities are project infrastructure preparing the Lemma C.5 route of
the eta-local structure paper-gap note
(`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`)
(arXiv:1606.00608, Appendix C.2, Lemma `SALZCL`, lines
1473--1499; Case-I assumptions at lines 1374--1381; cyclic direct-sum form at
lines 1580--1593).  They are not statements from CPSV16, and no Lemma C.5
conclusion is claimed here.
-/

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.Frobenius

namespace MPOTensor

variable {d D : ℕ}

/-- Reindexing equivalence between pairs of ket/bra configurations of a chain
of length `N` and doubled-index configurations: the pair `(σ, τ)` corresponds
to the doubled-index word `n ↦ finProdFinEquiv (σ n, τ n)`.

This is the currying equivalence between functions into a product and pairs of
functions, composed with the pointwise product encoding `finProdFinEquiv`. -/
def pairCfgEquiv (d N : ℕ) :
    ((Fin N → Fin d) × (Fin N → Fin d)) ≃ (Fin N → Fin (d * d)) :=
  (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ ↦ Fin d) (fun _ ↦ Fin d)).symm.trans
    (Equiv.piCongrRight fun _ ↦ (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)))

@[simp] lemma pairCfgEquiv_apply {N : ℕ} (σ τ : Fin N → Fin d) :
    pairCfgEquiv d N (σ, τ) = fun n ↦ finProdFinEquiv (σ n, τ n) := rfl

/-- **Doubled-index overlap identity.**  The self-overlap of the doubled-index
MPS family of an MPO tensor at chain length `N` equals the Hilbert--Schmidt
trace of the MPO:
```
MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N
  = Matrix.trace (mpo K N * (mpo K N)ᴴ).
```

The proof is a finite reindexing: the left side sums over doubled-index words
`Fin N → Fin (d * d)`, the right side expands to the Frobenius inner product
`∑_{σ,τ} mpo K N σ τ * star (mpo K N σ τ)` over pairs of ket/bra
configurations, and `MPSTensor.mpv_toMPSTensor_pairConfig` identifies the
summands along `pairCfgEquiv`.

This is a project derivation preparing the Lemma C.5 route of the eta-local
structure paper-gap note
(`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`)
(arXiv:1606.00608, Appendix C.2, Lemma `SALZCL`, lines 1473--1499); it is not
a claim from CPSV16.  Before trace normalization is established, the right
side is the raw squared Hilbert--Schmidt norm of the MPO family, not a
normalized-state purity. -/
theorem mpvOverlap_toMPSTensor_self (K : MPOTensor d D) (N : ℕ) :
    MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N =
      Matrix.trace (mpo K N * (mpo K N)ᴴ) := by
  have htrace : Matrix.trace (mpo K N * (mpo K N)ᴴ)
      = ∑ σ : Fin N → Fin d, ∑ τ : Fin N → Fin d,
          mpo K N σ τ * star (mpo K N σ τ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [htrace]
  symm
  calc ∑ σ : Fin N → Fin d, ∑ τ : Fin N → Fin d,
          mpo K N σ τ * star (mpo K N σ τ)
      = ∑ p : (Fin N → Fin d) × (Fin N → Fin d),
          MPSTensor.mpv K.toMPSTensor (pairCfgEquiv d N p) *
            star (MPSTensor.mpv K.toMPSTensor (pairCfgEquiv d N p)) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun τ _ ↦ by
          rw [pairCfgEquiv_apply, MPSTensor.mpv_toMPSTensor_pairConfig]
    _ = ∑ ρ : Fin N → Fin (d * d),
          MPSTensor.mpv K.toMPSTensor ρ * star (MPSTensor.mpv K.toMPSTensor ρ) :=
        Fintype.sum_equiv (pairCfgEquiv d N) _ _ fun _ ↦ rfl
    _ = MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N := rfl

/-- **Hermitian corollary.**  For an MPDO, positivity on every nonempty chain
makes the density operator Hermitian, so the raw squared Hilbert--Schmidt norm
identifies with the trace of the square:
```
MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N
  = Matrix.trace (mpo K N * mpo K N).
```

This is a project derivation preparing the Lemma C.5 route of the eta-local
structure paper-gap note
(`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`)
(arXiv:1606.00608, Appendix C.2, Lemma `SALZCL`, lines 1473--1499); it is not
a claim from CPSV16. -/
theorem mpvOverlap_toMPSTensor_self_eq_trace_sq (K : MPOTensor d D) (hK : IsMPDO K)
    {N : ℕ} (hN : 0 < N) :
    MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N =
      Matrix.trace (mpo K N * mpo K N) := by
  rw [mpvOverlap_toMPSTensor_self K N, (hK N hN).isHermitian.eq]

/-- **Frobenius-norm form.**  The real part of the doubled-index self-overlap
is the squared Frobenius norm of the MPO, that is, its raw squared
Hilbert--Schmidt norm in the vocabulary of `TNLean.Algebra.MatrixAux`.

This is a project derivation preparing the Lemma C.5 route of the eta-local
structure paper-gap note
(`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`); it
is not a claim from CPSV16. -/
theorem mpvOverlap_toMPSTensor_self_re_eq_frobenius_norm_sq (K : MPOTensor d D) (N : ℕ) :
    (MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N).re = ‖mpo K N‖ ^ 2 := by
  rw [mpvOverlap_toMPSTensor_self K N, Matrix.trace_mul_comm]
  exact Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq (mpo K N)

end MPOTensor
