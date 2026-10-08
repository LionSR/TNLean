/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.FamilyPhysicalReadout
import TNLean.PEPS.Approximation.EffectCircuitDensity
import TNLean.PEPS.Approximation.SourceOnlyReduction
import TNLean.PEPS.Approximation.SourcePhysicalDensity
import TNLean.PEPS.Approximation.PhysicalFirstExchange
import TNLean.PEPS.Approximation.PhysicalDensityPureInput

/-! # Physical output after exchanging retained auxiliary registers

The effect replacement produces the auxiliary registers before the original
physical and private registers. The source-free exchange places the physical
registers first. In orthonormal coordinates this exchange merely reverses the
order of the two discarded factors, so it preserves the physical partial trace.

The exact source operators in the resulting actual chronology therefore give
the previously constructed replacement density, with the same original gate
count and physical error budget. The physical basis is arbitrary, and may be
the labelled tensor basis for unequal original local dimensions. The private
memory is finite-dimensional and has no numerical dimension bound.

Source: polynomial-PEPS, `04-compression.tex`, lines 199–227 and 338–355.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-approximate-physical-physicalfirstreadout-01
TNLean.PEPS.PairEffect.EffectCircuit.physicalDensity_physicalFirstReplacement
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-02
TNLean.PEPS.PairEffect.EffectCircuit.physicalFirstReplacement
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-03
TNLean.PEPS.PairEffect.EffectCircuit.physicalSourceReplacedDensity_physicalFirstReplacement_exact
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-04
TNLean.PEPS.PairEffect.OriginalCircuit.rectangularTraceNorm_physicalFirst_density_sub_le_half
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-05
TNLean.PEPS.PairEffect.SourceCircuit.physicalDensity_physicalFirstOutput
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-06
TNLean.PEPS.PairEffect.exchangedGarbageBasis
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-07
TNLean.PEPS.PairEffect.extendedPhysicalReadout_triple_tmul
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-08
TNLean.PEPS.PairEffect.partialTrace_physicalFirstReadout_exchange
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-09
TNLean.PEPS.PairEffect.physicalFirstReadout
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-10
TNLean.PEPS.PairEffect.physicalFirstReadout_exchange_apply
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-11
TNLean.PEPS.PairEffect.physicalFirstReadout_exchange_outerProduct
Provenance-ID: 8769-approximate-physical-physicalfirstreadout-12
TNLean.PEPS.PairEffect.physicalFirstReadout_tmul
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
open ContinuousLinearMap
variable {P X U V : Type} [Fintype X] [Fintype U] [Fintype V]

/-- The actual auxiliary-private garbage basis after exchanging output blocks.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
def exchangedGarbageBasis (aux priv : Layout P)
    (bAux : OrthonormalBasis U ℂ (Mem aux)) (bPriv : OrthonormalBasis V ℂ (Mem priv)) :
    OrthonormalBasis (U × V) ℂ (Mem (aux ++ priv)) :=
  (bAux.tensorProduct bPriv).map (appendIso aux priv).symm

/-- Product coordinates on the literal physical-first output layout.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
def physicalFirstReadout (aux physical priv : Layout P)
    (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (bAux : OrthonormalBasis U ℂ (Mem aux)) (bPriv : OrthonormalBasis V ℂ (Mem priv)) :
    Mem (physical ++ (aux ++ priv)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (X × (U × V)) :=
  (appendIso physical (aux ++ priv)).trans
    (bPhysical.tensorProduct (exchangedGarbageBasis aux priv bAux bPriv)).repr

/-- The actual physical-first coordinates on a pure three-factor vector.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227. -/
theorem physicalFirstReadout_tmul (aux physical priv : Layout P)
    (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (bAux : OrthonormalBasis U ℂ (Mem aux)) (bPriv : OrthonormalBasis V ℂ (Mem priv))
    (u : Mem aux) (p : Mem physical) (v : Mem priv) (i : X) (j : U) (k : V) :
    physicalFirstReadout aux physical priv bPhysical bAux bPriv
      ((appendIso physical (aux ++ priv)).symm
        (p ⊗ₜ[ℂ] (appendIso aux priv).symm (u ⊗ₜ[ℂ] v))) (i, (j, k)) =
      bPhysical.repr p i * (bAux.repr u j * bPriv.repr v k) := by
  simp only [physicalFirstReadout, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, OrthonormalBasis.tensorProduct_repr_tmul_apply']
  simp only [exchangedGarbageBasis, OrthonormalBasis.map,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply, OrthonormalBasis.tensorProduct_repr_tmul_apply']
  ac_rfl

/-- The original extended readout gives the same entries in private–auxiliary order.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227. -/
theorem extendedPhysicalReadout_triple_tmul (aux physical priv : Layout P)
    (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (bAux : OrthonormalBasis U ℂ (Mem aux)) (bPriv : OrthonormalBasis V ℂ (Mem priv))
    (u : Mem aux) (p : Mem physical) (v : Mem priv) (i : X) (j : U) (k : V) :
    extendedPhysicalReadout bAux.repr
      (isoL ((appendIso physical priv).trans (bPhysical.tensorProduct bPriv).repr))
      ((appendIso aux (physical ++ priv)).symm
        (u ⊗ₜ[ℂ] (appendIso physical priv).symm (p ⊗ₜ[ℂ] v))) (i, (k, j)) =
      bPhysical.repr p i * (bAux.repr u j * bPriv.repr v k) := by
  rw [extendedPhysicalReadout_append_tmul]
  simp only [Matrix.appendAuxiliaryVector, isoL_apply,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    OrthonormalBasis.tensorProduct_repr_tmul_apply']
  ac_rfl

/-- Exchanging the actual output blocks only exchanges the discarded coordinate order.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
theorem physicalFirstReadout_exchange_apply (aux physical priv : Layout P)
    (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (bAux : OrthonormalBasis U ℂ (Mem aux)) (bPriv : OrthonormalBasis V ℂ (Mem priv))
    (z : Mem (aux ++ (physical ++ priv))) (i : X) (j : U) (k : V) :
    physicalFirstReadout aux physical priv bPhysical bAux bPriv
      ((SourceCircuit.exchangeBlocks aux physical priv).eval z) (i, (j, k)) =
      extendedPhysicalReadout bAux.repr
        (isoL ((appendIso physical priv).trans (bPhysical.tensorProduct bPriv).repr))
        z (i, (k, j)) := by
  obtain ⟨q, rfl⟩ := (appendIso aux (physical ++ priv)).symm.surjective z
  induction q using TensorProduct.inductionOn with
  | tmul u pv =>
      obtain ⟨pv, rfl⟩ := (appendIso physical priv).symm.surjective pv
      induction pv using TensorProduct.inductionOn with
      | tmul p v =>
          rw [SourceCircuit.eval_exchangeBlocks_triple_tmul, physicalFirstReadout_tmul,
            extendedPhysicalReadout_triple_tmul]
      | add pv rv hpv hrv =>
          simp only [map_add, TensorProduct.tmul_add, PiLp.add_apply, hpv, hrv]
  | add q r hq hr =>
      simp only [map_add, PiLp.add_apply, hq, hr]
/-- The literal output exchange reindexes only the two discarded coordinates.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
theorem physicalFirstReadout_exchange_outerProduct (aux physical priv : Layout P)
    (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (bAux : OrthonormalBasis U ℂ (Mem aux)) (bPriv : OrthonormalBasis V ℂ (Mem priv))
    (z : Mem (aux ++ (physical ++ priv))) :
    Matrix.euclideanOuterProduct
      (physicalFirstReadout aux physical priv bPhysical bAux bPriv
        ((SourceCircuit.exchangeBlocks aux physical priv).eval z))
      (physicalFirstReadout aux physical priv bPhysical bAux bPriv
        ((SourceCircuit.exchangeBlocks aux physical priv).eval z)) =
      (Matrix.euclideanOuterProduct
        (extendedPhysicalReadout bAux.repr
          (isoL ((appendIso physical priv).trans (bPhysical.tensorProduct bPriv).repr)) z)
        (extendedPhysicalReadout bAux.repr
          (isoL ((appendIso physical priv).trans
            (bPhysical.tensorProduct bPriv).repr)) z)).submatrix
        (Prod.map id (Equiv.prodComm U V)) (Prod.map id (Equiv.prodComm U V)) := by
  ext ⟨i, j, k⟩ ⟨i', j', k'⟩
  simp only [Matrix.euclideanOuterProduct, Matrix.vecMulVec_apply, Matrix.submatrix_apply,
    Prod.map_apply, id_eq, Equiv.prodComm_apply, Pi.star_apply,
    physicalFirstReadout_exchange_apply]
  rfl

/-- Discarding the actual auxiliary and private registers is independent of their order.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
theorem partialTrace_physicalFirstReadout_exchange (aux physical priv : Layout P)
    (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (bAux : OrthonormalBasis U ℂ (Mem aux)) (bPriv : OrthonormalBasis V ℂ (Mem priv))
    (z : Mem (aux ++ (physical ++ priv))) :
    Matrix.partialTraceRight (Matrix.euclideanOuterProduct
      (physicalFirstReadout aux physical priv bPhysical bAux bPriv
        ((SourceCircuit.exchangeBlocks aux physical priv).eval z))
      (physicalFirstReadout aux physical priv bPhysical bAux bPriv
        ((SourceCircuit.exchangeBlocks aux physical priv).eval z))) =
      Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (extendedPhysicalReadout bAux.repr
          (isoL ((appendIso physical priv).trans (bPhysical.tensorProduct bPriv).repr)) z)
        (extendedPhysicalReadout bAux.repr
          (isoL ((appendIso physical priv).trans (bPhysical.tensorProduct bPriv).repr)) z)) := by
  rw [physicalFirstReadout_exchange_outerProduct]
  exact (Matrix.partialTraceRight_submatrix_right (Equiv.prodComm U V) _).symm

namespace SourceCircuit
/-- The physical-first circuit has the physical density of the actual extended readout.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
theorem physicalDensity_physicalFirstOutput {n : Type} [Fintype n]
    (aux physical priv : Layout P) {a : Layout P}
    (w : SourceCircuit a (aux ++ (physical ++ priv)))
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis X ℂ (Mem physical))
    (bAux : OrthonormalBasis U ℂ (Mem aux)) (bPriv : OrthonormalBasis V ℂ (Mem priv))
    (ψ : Mem a) :
    physicalDensity physical (aux ++ priv) (physicalFirstOutput aux physical priv w)
      bIn bPhysical (exchangedGarbageBasis aux priv bAux bPriv)
      (Matrix.euclideanOuterProduct (bIn.repr ψ) (bIn.repr ψ)) =
      Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (extendedPhysicalReadout bAux.repr
          (isoL ((appendIso physical priv).trans (bPhysical.tensorProduct bPriv).repr))
          (w.eval ψ))
        (extendedPhysicalReadout bAux.repr
          (isoL ((appendIso physical priv).trans (bPhysical.tensorProduct bPriv).repr))
          (w.eval ψ))) := by
  simp only [Matrix.euclideanOuterProduct, Pi.star_def, Complex.star_def]
  rw [physicalDensity_pure_input]
  exact partialTrace_physicalFirstReadout_exchange aux physical priv
    bPhysical bAux bPriv (w.eval ψ)

end SourceCircuit
namespace EffectCircuit
/-- The actual replacement circuit followed by the source-free output exchange.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
def physicalFirstReplacement {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    {a : Layout P} (physical priv : Layout P) (w : EffectCircuit a (physical ++ priv))
    (hw : w.IsAllowed) (hb : w.IsExpansionBounded r S) :
    SourceCircuit a (physical ++ (w.auxiliary (stackLength r S δ) ++ priv)) :=
  SourceCircuit.physicalFirstOutput (w.auxiliary (stackLength r S δ)) physical priv
    (w.replacement hδ hw hb)

/-- Exact physical output coordinates of the constructed physical-first replacement.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
theorem physicalDensity_physicalFirstReplacement {n : Type} [Fintype n]
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    {a : Layout P} (physical priv : Layout P) (w : EffectCircuit a (physical ++ priv))
    (hw : w.IsAllowed) (hb : w.IsExpansionBounded r S)
    [FiniteDimensional ℂ (Mem priv).carrier]
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis X ℂ (Mem physical)) (ψ : Mem a) :
    letI := w.finiteDimensional_auxiliary (stackLength r S δ)
    SourceCircuit.physicalDensity physical (w.auxiliary (stackLength r S δ) ++ priv)
      (w.physicalFirstReplacement hδ physical priv hw hb) bIn bPhysical
      (exchangedGarbageBasis (w.auxiliary (stackLength r S δ)) priv
        (stdOrthonormalBasis ℂ (Mem (w.auxiliary (stackLength r S δ))).carrier)
        (stdOrthonormalBasis ℂ (Mem priv).carrier))
      (Matrix.euclideanOuterProduct (bIn.repr ψ) (bIn.repr ψ)) =
      w.replacementPhysicalDensity hδ hw hb
        (isoL ((appendIso physical priv).trans
          (bPhysical.tensorProduct (stdOrthonormalBasis ℂ (Mem priv).carrier)).repr)) ψ := by
  let := w.finiteDimensional_auxiliary (stackLength r S δ)
  exact SourceCircuit.physicalDensity_physicalFirstOutput _ _ _ _ bIn bPhysical
    (stdOrthonormalBasis ℂ (Mem (w.auxiliary (stackLength r S δ))).carrier)
    (stdOrthonormalBasis ℂ (Mem priv).carrier) ψ
/-- Exact source operators in the actual replacement chronology recover its
physical density; the output exchange only changes discarded coordinate order.
Source: polynomial-PEPS, `04-compression.tex`, lines 210–227 and 338–355. -/
theorem physicalSourceReplacedDensity_physicalFirstReplacement_exact
    {n : Type} [Fintype n] {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    {a : Layout P} (physical priv : Layout P) (w : EffectCircuit a (physical ++ priv))
    (hw : w.IsAllowed) (hb : w.IsExpansionBounded r S)
    [FiniteDimensional ℂ (Mem priv).carrier]
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis X ℂ (Mem physical)) (ψ : Mem a) :
    letI := w.finiteDimensional_auxiliary (stackLength r S δ)
    let R := w.physicalFirstReplacement hδ physical priv hw hb
    SourceCircuit.physicalSourceReplacedDensity physical
      (w.auxiliary (stackLength r S δ) ++ priv) R (SourceCircuit.exactSourceMatrix R)
      bIn bPhysical
      (exchangedGarbageBasis (w.auxiliary (stackLength r S δ)) priv
        (stdOrthonormalBasis ℂ (Mem (w.auxiliary (stackLength r S δ))).carrier)
        (stdOrthonormalBasis ℂ (Mem priv).carrier))
      (Matrix.euclideanOuterProduct (bIn.repr ψ) (bIn.repr ψ)) =
      w.replacementPhysicalDensity hδ hw hb
        (isoL ((appendIso physical priv).trans
          (bPhysical.tensorProduct (stdOrthonormalBasis ℂ (Mem priv).carrier)).repr)) ψ := by
  let := w.finiteDimensional_auxiliary (stackLength r S δ)
  dsimp only
  rw [SourceCircuit.physicalSourceReplacedDensity_exact]
  exact w.physicalDensity_physicalFirstReplacement hδ physical priv hw hb bIn bPhysical ψ

end EffectCircuit
namespace OriginalCircuit
/-- The original gate-count budget controls the exact-source physical output
of the constructed physical-first replacement. The input and physical spaces
retain their actual dimensions.
Source: polynomial-PEPS, `04-compression.tex`, lines 199–227 and 338–355. -/
theorem rectangularTraceNorm_physicalFirst_density_sub_le_half
    {n : Type} [Fintype n] [DecidableEq X]
    {r M : ℕ} {S ε : ℝ} (hε : 0 < ε)
    {a : Layout P} (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    (hb : w.IsExpansionBounded r S) (hcount : w.nonprivateCount ≤ M)
    [FiniteDimensional ℂ (Mem priv).carrier]
    (bIn : OrthonormalBasis n ℂ (Mem a))
    (bPhysical : OrthonormalBasis X ℂ (Mem physical)) (ψ : Mem a) (hψ : ‖ψ‖ ≤ 1) :
    let δ := sourceGateBudget ε M
    let m := stackLength r S δ
    letI := w.produce.finiteDimensional_auxiliary m
    let R := w.produce.physicalFirstReplacement (sourceGateBudget_pos hε M)
      physical priv w.isAllowed_produce ((w.isExpansionBounded_produce_iff r S).mpr hb)
    let K := (appendIso physical priv).trans
      (bPhysical.tensorProduct (stdOrthonormalBasis ℂ (Mem priv).carrier)).repr
    Matrix.rectangularTraceNorm
      (SourceCircuit.physicalSourceReplacedDensity physical (w.produce.auxiliary m ++ priv)
        R (SourceCircuit.exactSourceMatrix R) bIn bPhysical
        (exchangedGarbageBasis (w.produce.auxiliary m) priv
          (stdOrthonormalBasis ℂ (Mem (w.produce.auxiliary m)).carrier)
          (stdOrthonormalBasis ℂ (Mem priv).carrier))
        (Matrix.euclideanOuterProduct (bIn.repr ψ) (bIn.repr ψ)) -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (w.eval ψ)) (K (w.eval ψ)))) ≤
      ε / 2 := by
  let := w.produce.finiteDimensional_auxiliary (stackLength r S (sourceGateBudget ε M))
  dsimp only
  rw [EffectCircuit.physicalSourceReplacedDensity_physicalFirstReplacement_exact]
  exact w.rectangularTraceNorm_sourceOnly_density_sub_le_half_of_count_le hε hb hcount
    ((appendIso physical priv).trans
      (bPhysical.tensorProduct (stdOrthonormalBasis ℂ (Mem priv).carrier)).repr) ψ hψ
end OriginalCircuit
end TNLean.PEPS.PairEffect
