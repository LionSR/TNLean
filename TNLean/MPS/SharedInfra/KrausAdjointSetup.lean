/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.Core.CPPrimitive
import TNLean.QPF.PosDef
import TNLean.Channel.Schwarz.Basic

/-!
# Shared Kraus-adjoint setup for cyclic-sector arguments

This file collects the common conversion from an irreducible TP MPS tensor to
the conjugate-transposed Kraus family used in cyclic-sector decompositions.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

open KadisonSchwarz

/-- From an irreducible TP tensor, derive the conjugate-transposed Kraus family `K`,
its unitality and irreducibility, and a `PosDef` fixed point `ρ` of `Kraus.adjointMap K`.

This bundles the common setup shared by cyclic-sector decomposition arguments. -/
theorem conjTranspose_kraus_setup
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A) :
    ∃ (K : MPSTensor d D)
      (_ : IsUnitalKraus (d := d) (D := D) K)
      (_ : IsIrreducibleMap (transferMap (d := d) (D := D) K))
      (ρ : Matrix (Fin D) (Fin D) ℂ)
      (_ : ρ.PosDef)
      (_ : Kraus.adjointMap K ρ = ρ),
      K = fun i => (A i)ᴴ := by
  classical
  have hDpos : 0 < D := NeZero.pos D
  let K : MPSTensor d D := fun i => (A i)ᴴ
  have hTP' : IsTPKraus (d := d) (D := D) A := by
    simpa [IsTPKraus] using hTP
  have h_unitalK : IsUnitalKraus (d := d) (D := D) K :=
    isUnitalKraus_conjTranspose (d := d) (D := D) (K := A) hTP'
  have hIrrK : IsIrreducibleMap (transferMap (d := d) (D := D) K) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor (d := d) (D := D) A hIrr
  have hCh : IsChannel (transferMap (d := d) (D := D) A) :=
    transferMap_isChannel (d := d) (D := D) A (by simpa using hTP)
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    hCh.exists_posSemidef_fixedPoint (E := transferMap (d := d) (D := D) A) hDpos
  have hIrrAmap : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor (d := d) (D := D) A hIrr
  have hρ_pd : ρ.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible (A := A) (d := d) (D := D)
      hIrrAmap ρ hρ_psd hρ_ne hρ_fix
  have h_adjfix : Kraus.adjointMap K ρ = ρ := by
    simpa [K, Kraus.adjointMap, transferMap_apply, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using hρ_fix
  exact ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩

end MPSTensor
