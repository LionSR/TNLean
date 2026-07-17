/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SimpleTensor
import TNLean.MPS.SharedInfra.Scaling

/-!
# Absorbing copy-independent weights into BNT representatives

After proving that the canonical-form weights do not depend on the copy
index, arXiv:1606.00608 absorbs the common weight into each basis-of-normal-
tensors representative. The remaining coefficient is then the natural
multiplicity of that representative, namely its number of horizontal copies.

This file records that coefficient and matrix-product-vector identity. It does
not identify the horizontal copy multiplicity with the number of Markov
sectors used later to construct the physical projectors.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, equation CFK, lines 1660--1665, and equation sigmaNKj,
  lines 1756--1759.
-/

open scoped Matrix BigOperators

namespace MPSTensor.SectorDecomposition

variable {d : ℕ}

/-- The common weight $\mu_j$ of the copies of sector $j$, chosen from its
distinguished first copy. The hypothesis ensures that this choice represents
every copy.

Source: arXiv:1606.00608, Appendix C.2, lines 1646--1665. -/
noncomputable def commonWeight (S : SectorDecomposition d)
    (_hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (j : Fin S.basisCount) : ℂ :=
  S.weight j ⟨0, S.copies_pos j⟩

/-- The representative $\mathcal K_j=\mu_j A_j$ obtained by absorbing the
common copy weight into the $j$-th canonical-form representative.

Source: arXiv:1606.00608, Appendix C.2, equation CFK, lines 1660--1665. -/
noncomputable def commonWeightAbsorbedBasis (S : SectorDecomposition d)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (j : Fin S.basisCount) :
    MPSTensor d (S.basisDim j) :=
  fun i => S.commonWeight hWeight j • S.basis j i

/-- Every copy weight is the chosen common weight when the weights are
copy-independent.

Source: arXiv:1606.00608, Appendix C.2, the argument labelled lemmus,
lines 1646--1658. -/
theorem weight_eq_commonWeight (S : SectorDecomposition d)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (j : Fin S.basisCount)
    (q : Fin (S.copies j)) :
    S.weight j q = S.commonWeight hWeight j :=
  hWeight j q ⟨0, S.copies_pos j⟩

/-- The common copy weight is nonzero.

This is the coefficient nonvanishing used when the source forms
\(m_j=q_j\widetilde m_j\) in the proof of the Markov-sector assignment.

Source: arXiv:1606.00608, Appendix C.2, lines 1646--1665 and 1714--1718. -/
theorem commonWeight_ne_zero (S : SectorDecomposition d)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (j : Fin S.basisCount) :
    S.commonWeight hWeight j ≠ 0 :=
  S.weight_ne_zero j ⟨0, S.copies_pos j⟩

/-- Once the copy weights over sector $j$ agree, its length-$N$ coefficient is
the natural copy multiplicity $r_j$ times $\mu_j^N$:
\[
  \sum_q \mu_{j,q}^N=r_j\mu_j^N.
\]

Source: arXiv:1606.00608, Appendix C.2, equations CFK and sigmaNKj,
lines 1660--1665 and 1756--1759. -/
theorem coeff_eq_copies_mul_commonWeight_pow (S : SectorDecomposition d)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (N : ℕ) (j : Fin S.basisCount) :
    S.coeff N j = (S.copies j : ℂ) * (S.commonWeight hWeight j) ^ N := by
  classical
  simp only [SectorDecomposition.coeff, SectorWeightData.coeff]
  simp_rw [S.weight_eq_commonWeight hWeight j]
  simp

/-- When the copy weights agree, their length-\(N\) sum is nonzero for every
chain length:
\[
  q_j=\sum_q \mu_{j,q}^N=r_j\mu_j^N\ne0.
\]

This discharges the coefficient part of the choice of \(m_j\) in the source.
The independent choice of a nonzero virtual tail contraction remains a
separate step.

Source: arXiv:1606.00608, Appendix C.2, lines 1646--1665 and 1714--1718. -/
theorem coeff_ne_zero_of_weight_copy_independent (S : SectorDecomposition d)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (N : ℕ) (j : Fin S.basisCount) :
    S.coeff N j ≠ 0 := by
  rw [S.coeff_eq_copies_mul_commonWeight_pow hWeight N j]
  apply mul_ne_zero
  · exact_mod_cast (Nat.ne_of_gt (S.copies_pos j))
  · exact pow_ne_zero N (S.commonWeight_ne_zero hWeight j)

/-- Absorbing the common weight into each representative leaves precisely its
natural horizontal copy count as the coefficient of its matrix product
vector:
\[
  \mathcal V_N(S)=\sum_j r_j\,\mathcal V_N(\mathcal K_j),
  \qquad \mathcal K_j=\mu_j A_j.
\]

Source: arXiv:1606.00608, Appendix C.2, equation CFK, lines 1660--1665;
the multiplicity convention is used in equation sigmaNKj, lines 1756--1759. -/
theorem mpv_toTensor_eq_sum_copies_mul_commonWeightAbsorbedBasis
    (S : SectorDecomposition d)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') {N : ℕ} (σ : Fin N → Fin d) :
    mpv S.toTensor σ =
      ∑ j : Fin S.basisCount,
        (S.copies j : ℂ) * mpv (S.commonWeightAbsorbedBasis hWeight j) σ := by
  rw [S.mpv_toTensor_eq_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [S.coeff_eq_copies_mul_commonWeight_pow hWeight N j]
  rw [show mpv (S.commonWeightAbsorbedBasis hWeight j) σ =
      (S.commonWeight hWeight j) ^ N * mpv (S.basis j) σ by
    exact mpv_smul (S.commonWeight hWeight j) (S.basis j) σ]
  ring

end MPSTensor.SectorDecomposition
