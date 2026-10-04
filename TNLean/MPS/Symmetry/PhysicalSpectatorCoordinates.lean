/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingBondEtaCyclicCore
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Sector coordinates for a common physical space

The common space consists of an active virtual-pair sector followed by the
two original physical complements. Its neighboring-operator coordinates
have left dimensions \((K,d_0,d_1)\) and right dimensions \((K,1,1)\).
The active pair is read in the tensor's physical order \((l,r)\).

Source context: arXiv:1010.3732, Section II.F.2, equation
eq:1d-sym:jointsym. These coordinates express the additional physical
complements in the sector decomposition used to prove commutation of
neighboring bond penalties.
-/

namespace Matrix

private def sigmaFinThreeEquiv (β : Fin 3 → Type) :
    (Σ q, β q) ≃ (β 0 ⊕ β 1) ⊕ β 2 where
  toFun x := Fin.cases (fun v => Sum.inl (Sum.inl v))
    (Fin.cases (fun v => Sum.inl (Sum.inr v))
      (Fin.cases (fun v => Sum.inr v) (fun q => Fin.elim0 q))) x.1 x.2
  invFun
    | Sum.inl (Sum.inl v) => ⟨0, v⟩
    | Sum.inl (Sum.inr v) => ⟨1, v⟩
    | Sum.inr v => ⟨2, v⟩
  left_inv x := by
    rcases x with ⟨q, v⟩
    fin_cases q <;> rfl
  right_inv x := by
    rcases x with ((v | v) | v) <;> rfl

/-- Three-sector coordinates for the active virtual-pair space and two
physical complements. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
def physicalSpectatorEquiv (K d₀ d₁ : ℕ) :
    EtaSiteIndex 3 ![K, d₀, d₁] ![K, 1, 1] ≃ Fin ((K * K + d₀) + d₁) :=
  (sigmaFinThreeEquiv _).trans
    ((Equiv.sumCongr
      (Equiv.sumCongr ((Equiv.prodComm (Fin K) (Fin K)).trans finProdFinEquiv)
        (Equiv.uniqueProd (Fin d₀) (Fin 1)))
      (Equiv.uniqueProd (Fin d₁) (Fin 1))).trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv))

/-- The active sector uses the physical order of the virtual pair.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorEquiv_active (K d₀ d₁ : ℕ) (r l : Fin K) :
    physicalSpectatorEquiv K d₀ d₁ ⟨0, (r, l)⟩ =
      Fin.castAdd d₁ (Fin.castAdd d₀ (finProdFinEquiv (l, r))) := by
  rfl

/-- The first physical complement occupies the middle summand.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorEquiv_left (K d₀ d₁ : ℕ) (l : Fin d₀) :
    physicalSpectatorEquiv K d₀ d₁ ⟨1, ((0 : Fin 1), l)⟩ =
      Fin.castAdd d₁ (Fin.natAdd (K * K) l) := by
  rfl

/-- The second physical complement occupies the final summand.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalSpectatorEquiv_right (K d₀ d₁ : ℕ) (l : Fin d₁) :
    physicalSpectatorEquiv K d₀ d₁ ⟨2, ((0 : Fin 1), l)⟩ =
      Fin.natAdd (K * K + d₀) l := by
  rfl

end Matrix
