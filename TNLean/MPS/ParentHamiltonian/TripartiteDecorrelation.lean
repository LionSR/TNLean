/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QICLean.Channel.TripartiteDecorrelation

/-!
# Parent-Hamiltonian wrapper for tripartite decorrelation

This file retains the tensor-network-facing ground-space and commuting parent
Hamiltonian layer.  The generic tripartite lifts, marginals, supports, and
decorrelation results are provided by `QICLean.Channel.TripartiteDecorrelation`.

## Main definitions and results

* `TripartiteDecorrelation.HasGroundSpaceIntersection`
* `TripartiteDecorrelation.CommutingParentHamiltonian`
* `TripartiteDecorrelation.HasCommutingParentHamiltonian`
* `TripartiteDecorrelation.parentHamiltonian_iff_decorrelated`
* `TripartiteDecorrelation.parentHamiltonian_iff_observableDecorrelated`

## References

* arXiv:1606.00608, Appendix D.2, lines 2187--2289.
-/

open scoped Matrix MatrixOrder ComplexOrder Kronecker
open Matrix Finset BigOperators

namespace TripartiteDecorrelation

variable {A X B : Type*} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X]
  [Fintype B] [DecidableEq B]

/-- The literal ground-space intersection condition of arXiv:1606.00608,
Appendix D.2, Definition D.2, lines 2205--2218, written for the orthogonal
ground-space projectors. -/
def HasGroundSpaceIntersection
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ)
    (PAX : Matrix (A × X) (A × X) ℂ)
    (PXB : Matrix (X × B) (X × B) ℂ) : Prop :=
  LinearMap.range (Matrix.toLin' P) =
    LinearMap.range (Matrix.toLin' (liftAX PAX)) ⊓
      LinearMap.range (Matrix.toLin' (liftXB PXB))

/-- For commuting orthogonal projectors, the source ground-space intersection
condition is equivalent to the corresponding projector-product identity.

This proves that the range-intersection condition of arXiv:1606.00608,
Appendix D.2, Definition D.2, lines 2205--2218, is equivalent to the identity
in lines 2279--2289 that the tripartite ground-space projector is the product
of the two local ground-space projectors. -/
theorem hasGroundSpaceIntersection_iff_product_eq
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    {PAX : Matrix (A × X) (A × X) ℂ}
    {PXB : Matrix (X × B) (X × B) ℂ}
    (hPherm : P.IsHermitian) (hPidem : P * P = P)
    (hAXherm : PAX.IsHermitian) (hAXidem : PAX * PAX = PAX)
    (hXBherm : PXB.IsHermitian) (hXBidem : PXB * PXB = PXB)
    (hcomm : liftAX PAX * liftXB PXB = liftXB PXB * liftAX PAX) :
    HasGroundSpaceIntersection P PAX PXB ↔ liftAX PAX * liftXB PXB = P := by
  let SAX := liftAX (B := B) PAX
  let SXB := liftXB (A := A) PXB
  have hSAXherm : SAX.IsHermitian := by
    change (liftAX (B := B) PAX)ᴴ = liftAX (B := B) PAX
    rw [conjTranspose_liftAX, hAXherm.eq]
  have hSXBherm : SXB.IsHermitian := by
    change (liftXB (A := A) PXB)ᴴ = liftXB (A := A) PXB
    rw [conjTranspose_liftXB, hXBherm.eq]
  have hSAXidem : SAX * SAX = SAX := by
    rw [← liftAX_mul, hAXidem]
  have hSXBidem : SXB * SXB = SXB := by
    rw [← liftXB_mul, hXBidem]
  have hproductHerm : (SAX * SXB).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hSAXherm.eq,
      hSXBherm.eq, ← hcomm]
  have hproductIdem : (SAX * SXB) * (SAX * SXB) = SAX * SXB := by
    calc
      (SAX * SXB) * (SAX * SXB) = SAX * (SXB * SAX) * SXB := by
        noncomm_ring
      _ = SAX * (SAX * SXB) * SXB := by rw [← hcomm]
      _ = (SAX * SAX) * (SXB * SXB) := by noncomm_ring
      _ = SAX * SXB := by rw [hSAXidem, hSXBidem]
  have hrange := range_mul_eq_inter SAX SXB hSAXidem hSXBidem hcomm
  constructor
  · intro hintersection
    exact hermitian_idempotent_eq_of_range_eq (SAX * SXB) P
      hproductHerm hproductIdem hPherm hPidem (hrange.trans hintersection.symm)
  · intro hproduct
    change LinearMap.range (Matrix.toLin' P) =
      LinearMap.range (Matrix.toLin' SAX) ⊓ LinearMap.range (Matrix.toLin' SXB)
    rw [← hproduct]
    exact hrange

/-- The parent commuting Hamiltonian condition on the explicit tripartite
space, written in terms of the local ground-space projectors.

The Hamiltonian terms of arXiv:1606.00608, Appendix D.2, Definition D.2,
lines 2205--2218, are \(Q_{AX}=1-P_{AX}\) and \(Q_{XB}=1-P_{XB}\).  The
ground-space intersection condition, with hats denoting the full tripartite
lifts, is
\(\operatorname{ran}P=\operatorname{ran}\widehat P_{AX}\cap
\operatorname{ran}\widehat P_{XB}\), as in Definition D.2. -/
structure CommutingParentHamiltonian
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) where
  /-- The orthogonal projector onto \(K_{AX}\), as in arXiv:1606.00608,
  Appendix D.2, lines 2205--2215. -/
  PAX : Matrix (A × X) (A × X) ℂ
  /-- The orthogonal projector onto \(K_{XB}\), as in arXiv:1606.00608,
  Appendix D.2, lines 2205--2215. -/
  PXB : Matrix (X × B) (X × B) ℂ
  /-- The \(AX\) ground-space projector is Hermitian, corresponding to the
  projector assumption in arXiv:1606.00608, Appendix D.2, lines 2205--2208. -/
  hAXherm : PAX.IsHermitian
  /-- The \(AX\) ground-space projector is idempotent, corresponding to the
  projector assumption in arXiv:1606.00608, Appendix D.2, lines 2205--2208. -/
  hAXidem : PAX * PAX = PAX
  /-- The \(XB\) ground-space projector is Hermitian, corresponding to the
  projector assumption in arXiv:1606.00608, Appendix D.2, lines 2205--2208. -/
  hXBherm : PXB.IsHermitian
  /-- The \(XB\) ground-space projector is idempotent, corresponding to the
  projector assumption in arXiv:1606.00608, Appendix D.2, lines 2205--2208. -/
  hXBidem : PXB * PXB = PXB
  /-- The two lifted ground-space projectors commute, equivalently the local
  Hamiltonian projectors commute as required in arXiv:1606.00608,
  Appendix D.2, lines 2207--2214. -/
  hcomm : liftAX PAX * liftXB PXB = liftXB PXB * liftAX PAX
  /-- The range of \(P\) is the intersection of the two lifted local
  ground spaces, as in arXiv:1606.00608, Appendix D.2, lines 2212--2218. -/
  hintersection : HasGroundSpaceIntersection P PAX PXB

/-- The literal ground-space intersection condition of Definition D.2 gives
the projector-product identity used in the proof of Proposition D.3.

Source: arXiv:1606.00608, Appendix D.2, lines 2205--2218 and 2279--2289. -/
theorem CommutingParentHamiltonian.hproduct
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hparent : CommutingParentHamiltonian P)
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    liftAX hparent.PAX * liftXB hparent.PXB = P :=
  (hasGroundSpaceIntersection_iff_product_eq hPherm hPidem
    hparent.hAXherm hparent.hAXidem hparent.hXBherm hparent.hXBidem
    hparent.hcomm).mp hparent.hintersection

/-- Existence of local commuting parent projectors for \(P\), in the sense of
arXiv:1606.00608, Appendix D.2, Definition D.2, lines 2205--2218. -/
def HasCommutingParentHamiltonian
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) : Prop :=
  Nonempty (CommutingParentHamiltonian P)

/-- A parent commuting Hamiltonian on \(AX\) and \(XB\) implies decorrelation
of \(A\) and \(B\).

This is the only-if direction of arXiv:1606.00608, Appendix D.2,
Proposition D.3, lines 2279--2289. -/
theorem CommutingParentHamiltonian.isDecorrelated
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hparent : CommutingParentHamiltonian P)
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    IsDecorrelated P := by
  let SAX := liftAX (B := B) hparent.PAX
  let SXB := liftXB (A := A) hparent.PXB
  have hproduct : SAX * SXB = P := hparent.hproduct hPherm hPidem
  have hrev : SXB * SAX = P := by
    rw [← hparent.hcomm]
    exact hproduct
  have hquad : SXB * P * SAX = P * P := by
    calc
      SXB * P * SAX = SXB * (SAX * SXB) * SAX := by rw [hproduct]
      _ = (SXB * SAX) * (SXB * SAX) := by noncomm_ring
      _ = P * P := by rw [hrev]
  have hmiddle : SXB * (1 - P) * SAX = 0 := by
    calc
      SXB * (1 - P) * SAX = SXB * SAX - SXB * P * SAX := by noncomm_ring
      _ = P - P * P := by rw [hrev, hquad]
      _ = 0 := by rw [hPidem, sub_self]
  intro OA OB
  have hAcomm : SXB * liftA OA = liftA OA * SXB := by
    exact (liftA_comm_liftXB OA hparent.PXB).symm
  have hBcomm : liftB OB * SAX = SAX * liftB OB := by
    exact liftB_comm_liftAX OB hparent.PAX
  calc
    P * liftA OA * (1 - P) * liftB OB * P =
        (SAX * SXB) * liftA OA * (1 - P) * liftB OB * (SAX * SXB) := by
          rw [hproduct]
    _ = SAX * liftA OA * (SXB * (1 - P) * SAX) * liftB OB * SXB := by
      calc
        (SAX * SXB) * liftA OA * (1 - P) * liftB OB * (SAX * SXB) =
            SAX * (SXB * liftA OA) * (1 - P) *
              (liftB OB * SAX) * SXB := by noncomm_ring
        _ = SAX * (liftA OA * SXB) * (1 - P) *
              (SAX * liftB OB) * SXB := by rw [hAcomm, hBcomm]
        _ = SAX * liftA OA * (SXB * (1 - P) * SAX) * liftB OB * SXB := by
          noncomm_ring
    _ = 0 := by rw [hmiddle]; simp

/-- Decorrelation constructs a parent commuting Hamiltonian from the two
marginal support projectors.

This is the if direction of arXiv:1606.00608, Appendix D.2,
Proposition D.3, lines 2225--2277. -/
theorem IsDecorrelated.hasCommutingParentHamiltonian
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) (hdec : IsDecorrelated P) :
    HasCommutingParentHamiltonian P := by
  have hproducts := supportProducts_eq hPherm hPidem hdec
  have hAXherm := (Matrix.partialTraceRight_isHermitian
    (groupAX_isHermitian hPherm)).supportProj_isHermitian
  have hAXidem := (Matrix.partialTraceRight_isHermitian
    (groupAX_isHermitian hPherm)).supportProj_idem
  have hXBherm := (Matrix.partialTraceLeft_isHermitian hPherm).supportProj_isHermitian
  have hXBidem := (Matrix.partialTraceLeft_isHermitian hPherm).supportProj_idem
  exact ⟨
    { PAX := supportAX hPherm
      PXB := supportXB hPherm
      hAXherm := hAXherm
      hAXidem := hAXidem
      hXBherm := hXBherm
      hXBidem := hXBidem
      hcomm := hproducts.2.trans hproducts.1.symm
      hintersection :=
        (hasGroundSpaceIntersection_iff_product_eq hPherm hPidem
          hAXherm hAXidem hXBherm hXBidem
          (hproducts.2.trans hproducts.1.symm)).mpr hproducts.2 }⟩

/-- **Parent commuting Hamiltonian--decorrelation equivalence.**

For an orthogonal projector \(P_{AXB}\), there are commuting parent terms on
\(AX\) and \(XB\) with ground projector \(P_{AXB}\) if and only if regions
\(A\) and \(B\) are decorrelated.  This is arXiv:1606.00608, Appendix D.2,
Proposition D.3, lines 2221--2289. -/
theorem parentHamiltonian_iff_decorrelated
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    HasCommutingParentHamiltonian P ↔ IsDecorrelated P :=
  ⟨fun hparent => hparent.elim fun parent => parent.isDecorrelated hPherm hPidem,
    fun hdec => hdec.hasCommutingParentHamiltonian hPherm hPidem⟩

/-- **Source-facing parent commuting Hamiltonian--decorrelation equivalence.**

For an orthogonal projector \(P_{AXB}\), there are commuting parent terms on
\(AX\) and \(XB\) with ground projector \(P_{AXB}\) if and only if the
Hermitian-observable decorrelation condition of arXiv:1606.00608,
Appendix D.2, Definition D.1, holds.  This is Proposition D.3,
lines 2221--2289. -/
theorem parentHamiltonian_iff_observableDecorrelated
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    HasCommutingParentHamiltonian P ↔ IsObservableDecorrelated P :=
  (parentHamiltonian_iff_decorrelated hPherm hPidem).trans
    isObservableDecorrelated_iff.symm

end TripartiteDecorrelation
