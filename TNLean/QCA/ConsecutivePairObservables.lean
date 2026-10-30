/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.ConsecutivePairCoordinates
import TNLean.QCA.SiteIndexedSupportAlgebra
import TNLean.QCA.QuasiLocalTranslation

/-!
# Translation in ordered physical pair coordinates

An observable on two consecutive sites keeps its ordered matrix when
translated. Both site coordinates are transported through the actual
finite-region inclusion; no equality of independently selected factor
coordinates is used.

Source: Schumacher--Werner, bruleU/bruleV and translation compatibility,
quant-ph/0405174, lines 980--1001 and 1033--1041; CPSV17, Appendix,
arXiv:1703.09188, lines 2292--2306.
-/

namespace SpinChain

/-- Actual translation preserves the ordered physical matrix of a
consecutive pair, including at negative anchors.
Source: Schumacher--Werner, translation compatibility, lines 1033--1041. -/
theorem quasiLocalTranslation_consecutivePair (d : ℕ) [NeZero d] (t a : ℤ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    quasiLocalTranslation d t
        (matrixToQuasiLocalObservable d ({a, a + 1} : Finset ℤ)
          (Matrix.reindex (consecutivePairConfigEquiv d a)
            (consecutivePairConfigEquiv d a) A)) =
      matrixToQuasiLocalObservable d ({a + t, a + t + 1} : Finset ℤ)
        (Matrix.reindex (consecutivePairConfigEquiv d (a + t))
          (consecutivePairConfigEquiv d (a + t)) A) := by
  classical
  have hregion : translateRegion t ({a, a + 1} : Finset ℤ) =
      ({a + t, a + t + 1} : Finset ℤ) := by
    ext z
    simp only [mem_translateRegion, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp only [matrixToQuasiLocalObservable, StarAlgHom.comp_apply]
  rw [quasiLocalTranslation_quasiLocalObservable,
    ← quasiLocalObservable_localInclusion d hregion.le]
  apply congrArg (quasiLocalObservable d ({a + t, a + t + 1} : Finset ℤ))
  apply CStarMatrix.ext
  intro x y
  have hcomp : (Config.splitEquiv hregion.le x).2 =
      (Config.splitEquiv hregion.le y).2 := by
    funext z
    exact False.elim ((Finset.mem_sdiff.mp z.2).2
      (hregion.ge (Finset.mem_sdiff.mp z.2).1))
  rw [localInclusion_apply, ite_eq_left hcomp, mul_one, localTranslation_apply]
  change A ((consecutivePairConfigEquiv d a).symm
      ((Config.translation d t _).symm (Config.restrict hregion.le x)))
    ((consecutivePairConfigEquiv d a).symm
      ((Config.translation d t _).symm (Config.restrict hregion.le y))) =
    A ((consecutivePairConfigEquiv d (a + t)).symm x)
      ((consecutivePairConfigEquiv d (a + t)).symm y)
  have hcoords (z : Config d ({a + t, a + t + 1} : Finset ℤ)) :
      (consecutivePairConfigEquiv d a).symm
        ((Config.translation d t _).symm (Config.restrict hregion.le z)) =
          (consecutivePairConfigEquiv d (a + t)).symm z := by
    apply Prod.ext
    · change z _ = z _
      congr 1
    · change z _ = z _
      congr 1
      apply Subtype.ext
      simp only [siteTranslation_apply_val]
      omega
  rw [hcoords, hcoords]

end SpinChain
