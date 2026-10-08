/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Range-projector cancellation with a supported Gram inverse

A rectangular boundary map can vanish outside a virtual corner. Its Gram
operator therefore has an inverse only on that corner. A self-adjoint support
operator `Q`, the identity `T.comp Q = T`, and a supported inverse equation
`(T.adjoint.comp T).comp H = Q` suffice to recover the orthogonal range
projection. Global injectivity is unnecessary.

For three maps with a common factorization, the product of two range
projections minus the third factors through an exact mixed-Gram residual.
This extends the injective cancellation identity to the supported rectangular
boundaries arising from cyclic sectors of a periodic MPS.

These are algebraic identities reconstructed for the projector comparison in
Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2442--2531.
They assert neither a decay estimate nor a spectral gap.
-/

open scoped InnerProductSpace
namespace ContinuousLinearMap
variable {𝕜 E F G W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] [CompleteSpace W]
/-- The supported-Gram formula for an orthogonal range projection. The support
operator is self-adjoint and acts as the identity through the boundary map;
no injectivity or self-adjointness of the chosen inverse is required.
This is an algebraic prerequisite for Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (ii), lines 2442--2531. -/
theorem comp_supportedGramInverse_adjoint_eq_starProjection
    (T : E →L[𝕜] F) (H Q : E →L[𝕜] E)
    (hQ : Q.adjoint = Q) (hTQ : T.comp Q = T)
    (hGH : (T.adjoint.comp T).comp H = Q) :
    T.comp (H.comp T.adjoint) = T.range.starProjection := by
  have hQadj : Q.comp T.adjoint = T.adjoint := by
    simpa only [adjoint_comp, hQ] using congrArg
      (fun S : E →L[𝕜] F => S.adjoint) hTQ
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨H (T.adjoint x), rfl⟩
  · rw [Submodule.mem_orthogonal']
    rintro _ ⟨y, rfl⟩
    change ⟪x - (T.comp (H.comp T.adjoint)) x, T y⟫_𝕜 = 0
    rw [← T.adjoint_inner_left y]
    suffices T.adjoint (x - (T.comp (H.comp T.adjoint)) x) = 0 by
      rw [this, inner_zero_left]
    rw [map_sub]
    change T.adjoint x - (((T.adjoint.comp T).comp H).comp T.adjoint) x = 0
    rw [hGH, hQadj, sub_self]

/-- Exact mixed-Gram residual for three supported boundary maps with a common
factorization. The inverse associated with the first map is self-adjoint;
the other inverse equations suffice without that assumption. The identity
retains the virtual support operators and does not identify a physical range
projection with a transfer fixed-point projection.
Reconstructed for Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (ii), lines 2442--2531; no norm estimate is asserted. -/
theorem starProjection_comp_sub_of_supportedGramFactorizations
    (T : E →L[𝕜] F) (L : G →L[𝕜] F) (C : W →L[𝕜] F)
    (J₁ : W →L[𝕜] E) (J₂ : W →L[𝕜] G)
    (HT QT : E →L[𝕜] E) (HL QL : G →L[𝕜] G) (HC QC : W →L[𝕜] W)
    (hHT : HT.adjoint = HT) (hQT : QT.adjoint = QT) (hTQ : T.comp QT = T)
    (hGT : (T.adjoint.comp T).comp HT = QT)
    (hQL : QL.adjoint = QL) (hLQ : L.comp QL = L)
    (hGL : (L.adjoint.comp L).comp HL = QL)
    (hQC : QC.adjoint = QC) (hCQ : C.comp QC = C)
    (hGC : (C.adjoint.comp C).comp HC = QC)
    (hTC : T.comp J₁ = C) (hLC : L.comp J₂ = C) :
    T.range.starProjection.comp L.range.starProjection - C.range.starProjection =
      T.comp (HT.comp ((T.adjoint.comp L -
        (T.adjoint.comp T).comp (J₁.comp (HC.comp
          (J₂.adjoint.comp (L.adjoint.comp L))))).comp (HL.comp L.adjoint))) := by
  have hTG : HT.comp (T.adjoint.comp T) = QT := by
    simpa only [adjoint_comp, adjoint_adjoint, hHT, hQT] using
      congrArg (fun S : E →L[𝕜] E => S.adjoint) hGT
  have hQLadj : QL.comp L.adjoint = L.adjoint := by
    simpa only [adjoint_comp, hQL] using congrArg
      (fun S : G →L[𝕜] F => S.adjoint) hLQ
  have hTcancel (y : E) : T (HT (T.adjoint (T y))) = T y := by
    exact congrArg (fun S : E →L[𝕜] F => S y)
      ((congrArg (fun S : E →L[𝕜] E => T.comp S) hTG).trans hTQ)
  have hLcancel (x : F) : L.adjoint (L (HL (L.adjoint x))) = L.adjoint x := by
    exact congrArg (fun S : F →L[𝕜] G => S x)
      ((congrArg (fun S : G →L[𝕜] G => S.comp L.adjoint) hGL).trans hQLadj)
  have hLCadj : J₂.adjoint.comp L.adjoint = C.adjoint := by
    rw [← adjoint_comp, hLC]
  have hsecond : T.comp (HT.comp
      (((T.adjoint.comp T).comp (J₁.comp (HC.comp
        (J₂.adjoint.comp (L.adjoint.comp L))))).comp (HL.comp L.adjoint))) =
      C.comp (HC.comp C.adjoint) := by
    ext x
    simp only [comp_apply, hTcancel, hLcancel]
    change (T.comp J₁) (HC ((J₂.adjoint.comp L.adjoint) x)) = _
    rw [hTC, hLCadj]
  rw [← comp_supportedGramInverse_adjoint_eq_starProjection T HT QT hQT hTQ hGT,
    ← comp_supportedGramInverse_adjoint_eq_starProjection L HL QL hQL hLQ hGL,
    ← comp_supportedGramInverse_adjoint_eq_starProjection C HC QC hQC hCQ hGC]
  simp only [comp_sub, sub_comp]
  rw [hsecond]
  simp only [comp_assoc]
end ContinuousLinearMap
