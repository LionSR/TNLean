/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourcePeriodicSewing
import TNLean.MPS.MPU.InverseCompatibleWordUnitarity

/-!
# Periodic composition in shared-boundary endpoint coordinates

Group a periodic configuration as $((a,p,b),q)$, with bulk lengths $n,m$.
The ring has $n+m+2$ sites. Let $M$ be the actual periodic MPO pulled back to
these coordinates, and let $\widehat A=A_n\otimes I_m$ be the first endpoint
operator, extended by the identity on the second bulk.
Define $C$ independently by the complementary endpoint contraction $A_m$,
from $b$ to $a$, with the first bulk retained unchanged.

Raw source sewing gives $M=(B_n\otimes I_m)C$. The source-space word
cancellation $A_nB_n=\sigma I$, not the reverse product, then gives
$\widehat A M=\sigma C$. There is exactly one phase.

Source: the local sewing and cancellation referred to in arXiv:2502.20257,
`main.tex` lines 5486–5487, using the construction at lines 5390–5432 and
word contraction extending lines 5444–5487. The two endpoint-inclusive arcs
have lengths $n+2,m+2$ and share both marked boundary sites. We do not identify
this with a disjoint complement of length $(n+m+2)-(n+2)$ or assert the literal
`eq:UUU` under an unresolved boundary convention. No new interval hierarchy,
spatial reflection, or rank-coordinate identification is introduced here.
-/

open scoped ComplexOrder Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- Place grouped coordinates $((a,p,b),q)$ on the ring in order $(a,p,b,q)$.
Source: the shared-boundary sewing associated with arXiv:2502.20257, lines 5486–5487. -/
def sourcePeriodicGroupedConfig (n m : ℕ)
    (x : (Fin d × ((Fin n → Fin d) × Fin d)) × (Fin m → Fin d)) :
    Fin (n + (m + 1) + 1) → Fin d :=
  Fin.cons x.1.1 (Fin.append x.1.2.1 (Fin.cons x.1.2.2 x.2))

/-- The actual periodic MPO in grouped endpoint/bulk coordinates, by submatrix pullback.
Source: the periodic sewing associated with arXiv:2502.20257, lines 5486–5487. -/
noncomputable def inverseCompatibleGroupedMPO (n m : ℕ) :
    Matrix ((Fin d × ((Fin n → Fin d) × Fin d)) × (Fin m → Fin d))
      ((Fin d × ((Fin n → Fin d) × Fin d)) × (Fin m → Fin d)) ℂ :=
  (mpo U (n + (m + 1) + 1)).submatrix
    (sourcePeriodicGroupedConfig n m) (sourcePeriodicGroupedConfig n m)

/-- The first endpoint operator extended by the identity on the other bulk.
Source: the local composition associated with arXiv:2502.20257, lines 5486–5487. -/
noncomputable def inverseCompatibleFirstArcEmbedding (n m : ℕ) :
    Matrix ((Fin ℓ[U] × ((Fin n → Fin d) × Fin ℓ[U])) × (Fin m → Fin d))
      ((Fin d × ((Fin n → Fin d) × Fin d)) × (Fin m → Fin d)) ℂ :=
  inverseCompatibleWordA U T n ⊗ₖ (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)

/-- The independent complementary contraction, retaining the first bulk and traversing
the other arc from the second marked site to the first, with rank order $(s,q,l)$.
Source: the shared-boundary sewing associated with arXiv:2502.20257, lines 5486–5487. -/
noncomputable def inverseCompatibleComplementaryArc (n m : ℕ) :
    Matrix ((Fin ℓ[U] × ((Fin n → Fin d) × Fin ℓ[U])) × (Fin m → Fin d))
      ((Fin d × ((Fin n → Fin d) × Fin d)) × (Fin m → Fin d)) ℂ :=
  fun ((l, p, s), q) ((a', p', b'), q') ↦
    (if p = p' then 1 else 0) * inverseCompatibleWordA U T m (s, q, l) (b', q', a')

/-- Splitting the two marked tensors factors the actual grouped periodic MPO through
the independently defined complementary arc. No simplicity, canonicality, or phase is needed.
Source: raw sewing for arXiv:2502.20257, lines 5486–5487, using lines 5390–5432. -/
theorem inverseCompatibleGroupedMPO_eq_wordB_mul_complementaryArc
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T) (n m : ℕ) :
    inverseCompatibleGroupedMPO U n m =
      (inverseCompatibleWordB U T n ⊗ₖ
        (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)) *
          inverseCompatibleComplementaryArc U T n m := by
  classical
  ext ⟨⟨a, p, b⟩, q⟩ ⟨⟨a', p', b'⟩, q'⟩
  have hsew := mpo_two_marked_entry_eq_sourcePeriodic_sewing U
    (inverseCompatibleX₁ U T) (inverseCompatibleY₁ U T) (sourceX₂ U) (sourceY₂ U)
    (sourceCutM₁_eq_inverseCompatibleX₁_mul_inverseCompatibleY₁ U T hT)
    (sourceCutM₂_eq_sourceX₂_mul_sourceY₂ U) a a' b b' p p' q q'
  change mpo U (n + (m + 1) + 1)
    (Fin.cons a (Fin.append p (Fin.cons b q)))
    (Fin.cons a' (Fin.append p' (Fin.cons b' q'))) = _
  rw [hsew]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, inverseCompatibleComplementaryArc, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq', Fintype.sum_ite_eq,
    Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  rfl

/-- Left composition with the first endpoint operator gives exactly one phase times
the independent complementary operator. The cancellation is on the raw source space.
Source: shared-boundary local composition associated with arXiv:2502.20257,
lines 5486–5487. This does not assert a disjoint-complement version of `eq:UUU`. -/
theorem inverseCompatibleFirstArcEmbedding_mul_groupedMPO
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) (n m : ℕ) :
    inverseCompatibleFirstArcEmbedding U T n m * inverseCompatibleGroupedMPO U n m =
      σ • inverseCompatibleComplementaryArc U T n m := by
  classical
  have hAB := (inverseCompatibleWord_mul_eq_smul_one U T hU hsimple hT σ hσ n).1
  rw [inverseCompatibleGroupedMPO_eq_wordB_mul_complementaryArc U T hT,
    inverseCompatibleFirstArcEmbedding, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
    hAB, Matrix.one_mul, Matrix.smul_kronecker, Matrix.one_kronecker_one,
    Matrix.smul_mul, Matrix.one_mul]

end MPOTensor
