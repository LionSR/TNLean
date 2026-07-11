/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.SectorFactorization

/-!
# Cyclic contraction of neighboring sector tensors of a simple MPDO

The cyclic contraction step in Appendix C.2, Lemma C.4 of arXiv:1606.00608
starts from sector tensors $l_k$ and $r_k$ obtained from the inverse map. The
operator joining neighboring sectors is their contraction over the horizontal
virtual index,
\[
  \eta_{k,h}=r_k l_h.
\]
The main result identifies the entries of a closed product of factorized
sector tensors with the product of these neighboring contractions.

No positivity is asserted here.  The positive choice of neighboring
operators in the source is a subsequent consequence of positivity of the
complete projected cyclic product.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemma C.4, lines 1441--1450
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The neighboring operator obtained by contracting the right sector tensor
of sector $k$ with the left sector tensor of sector $h$ over their common
horizontal virtual index:
\[
  (\eta_{k,h})_{(x_R,x_L),(y_R,y_L)}
    = \sum_a (r_k)_a(x_R,y_R)(l_h)_a(x_L,y_L).
\]

Source: arXiv:1606.00608, Appendix C.2, equation (etarl), lines 1441--1445. -/
noncomputable def etaOfSectorTensors
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (hη : EtaStructure ρ)
    (l : (k : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL k)) (Fin (hη.dL k)) ℂ)
    (r : (k : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR k)) (Fin (hη.dR k)) ℂ) :
    etaOperators hη :=
  fun k h => Matrix.of fun x y =>
    ∑ a : Fin D, r k a x.1 y.1 * l h a x.2 y.2

/-- The entries of a neighboring operator are the contractions of its two
sector tensors. -/
@[simp] lemma etaOfSectorTensors_apply
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (hη : EtaStructure ρ)
    (l : (k : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL k)) (Fin (hη.dL k)) ℂ)
    (r : (k : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR k)) (Fin (hη.dR k)) ℂ)
    (k h : Fin hη.m)
    (x y : Fin (hη.dR k) × Fin (hη.dL h)) :
    etaOfSectorTensors hη l r k h x y =
      ∑ a : Fin D, r k a x.1 y.1 * l h a x.2 y.2 :=
  rfl

/-- The scalar cyclic-contraction identity for the neighboring operators.
The cyclic sum over horizontal indices of local tensors which
split into left and right factors equals the product of the neighboring
contractions.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem sum_cyclic_sectorTensor_eq_prod_etaOfSectorTensors
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (hη : EtaStructure ρ)
    (l : (k : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL k)) (Fin (hη.dL k)) ℂ)
    (r : (k : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR k)) (Fin (hη.dR k)) ℂ)
    {N : ℕ} [NeZero N] (k : Fin N → Fin hη.m)
    (iL jL : (n : Fin N) → Fin (hη.dL (k n)))
    (iR jR : (n : Fin N) → Fin (hη.dR (k n))) :
    (∑ g : Fin N → Fin D, ∏ n : Fin N,
        l (k n) (g n) (iL n) (jL n) *
          r (k n) (g (n + 1)) (iR n) (jR n)) =
      ∏ n : Fin N,
        etaOfSectorTensors hη l r (k n) (k (n + 1))
          (iR n, iL (n + 1)) (jR n, jL (n + 1)) := by
  classical
  simp_rw [etaOfSectorTensors_apply]
  rw [Finset.prod_univ_sum
    (fun _ : Fin N => (Finset.univ : Finset (Fin D)))
    (fun n a =>
      r (k n) a (iR n) (jR n) *
        l (k (n + 1)) a (iL (n + 1)) (jL (n + 1)))]
  simp only [Fintype.piFinset_univ]
  refine Fintype.sum_equiv (rotateConfig N D) _ _ fun g => ?_
  simp only [rotateConfig_apply, Function.comp_apply, finRotate_apply]
  let qL : Fin N → ℂ :=
    fun x => l (k x) (g x) (iL x) (jL x)
  let qR : Fin N → ℂ :=
    fun x => r (k x) (g (x + 1)) (iR x) (jR x)
  let qLs : Fin N → ℂ :=
    fun x => l (k (x + 1)) (g (x + 1))
      (iL (x + 1)) (jL (x + 1))
  change (∏ x, qL x * qR x) = ∏ x, qR x * qLs x
  calc
    (∏ x, qL x * qR x) = (∏ x, qL x) * ∏ x, qR x := by
      simpa using (Finset.prod_mul_distrib
        (s := (Finset.univ : Finset (Fin N))) (f := qL) (g := qR))
    _ = (∏ x, qR x) * ∏ x, qL x := mul_comm _ _
    _ = (∏ x, qR x) * ∏ x, qLs x := by
      congr 1
      change (∏ x, qL x) = ∏ x, qL (x + 1)
      simpa only [finRotate_apply] using
        (Equiv.prod_comp (finRotate N) qL).symm
    _ = ∏ x, qR x * qLs x := by
      simpa using (Finset.prod_mul_distrib
        (s := (Finset.univ : Finset (Fin N))) (f := qR) (g := qLs)).symm

/-- **Entrywise cyclic contraction of the neighboring operators.** Fix a cyclic
sequence of sectors and matrix entries in their left and right factors.  The
closed horizontal contraction of the factorized local tensors equals the
product of the corresponding entries of
$\eta_{k_n,k_{n+1}}=r_{k_n}l_{k_{n+1}}$.

This is the scalar-entry form of the all-length cyclic identity used in the
proof of Lemma C.4.  It is valid for every nonempty cycle and does not use a
positivity hypothesis.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem trace_sector_word_eq_prod_etaOfSectorTensors
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (hη : EtaStructure ρ)
    (l : (k : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL k)) (Fin (hη.dL k)) ℂ)
    (r : (k : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR k)) (Fin (hη.dR k)) ℂ)
    {N : ℕ} [NeZero N] (k : Fin N → Fin hη.m)
    (iL jL : (n : Fin N) → Fin (hη.dL (k n)))
    (iR jR : (n : Fin N) → Fin (hη.dR (k n))) :
    Matrix.trace (MPSTensor.evalWord
        (fun n : Fin N => Matrix.of fun a b =>
          l (k n) a (iL n) (jL n) * r (k n) b (iR n) (jR n))
        (List.ofFn id)) =
      ∏ n : Fin N,
        etaOfSectorTensors hη l r (k n) (k (n + 1))
          (iR n, iL (n + 1)) (jR n, jL (n + 1)) := by
  rw [MPSTensor.trace_evalWord_eq_sum_cyclic]
  simpa only [Matrix.of_apply, id_eq] using
    sum_cyclic_sectorTensor_eq_prod_etaOfSectorTensors hη l r k iL jL iR jR

end MPOTensor
