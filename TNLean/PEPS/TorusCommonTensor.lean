/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import TNLean.Algebra.ProductFactorUniqueness
import TNLean.PEPS.TorusFourLegTransformation

/-!
# A repeated injective tensor for a translation-invariant PEPS state

For a possibly site-dependent injective tensor on a torus whose two periods
are at least three, exact translation invariance of the state gives a repeated
injective tensor with the same state and the same bond dimensions. Horizontal
and vertical bond dimensions may differ.

The local translation orbit and injectivity of the origin tensor first give
one invertible bond matrix per direction, up to a nonzero scalar. Absorbing
these matrices on the right and down legs, then taking a scalar root at the
fixed torus size, gives exact equality of the represented vectors.

Source: arXiv:1804.04964, lines 1207–1212 and 1891–1899.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS
open TNLean.Lattice

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- An injective translation-invariant state has one actual invertible bond
factor per direction in the common origin-tensor representation. The global
scalar is nonzero and is retained for the final fixed-size root.
Supporting decomposition for arXiv:1804.04964, lines 1891–1894.
This is not yet the repeated-tensor conclusion of the source. -/
theorem exists_torus_uniform_edge_representation
    {A : Tensor (torusGraph width height) d}
    (hInj : A.IsInjective) (hTI : IsTorusTranslationInvariantState A) :
    let hU := torusUniformBondDim_of_isTorusTranslationInvariantState hInj hTI
    let E := torusDirectionPortConfigEquiv A hU
    ∃ Q : (r : Bool) → GL (Fin (if r then A.bondDim (torusUpEdge 0)
        else A.bondDim (torusRightEdge 0))) ℂ,
      ∃ Γ : ℂ, Γ ≠ 0 ∧ stateCoeff A =
        Γ • dependentPhysicalProductFamilyMap
          (fun (_ : TorusVertex width height) (σ : Fin d) x =>
            A.component 0 (E 0 x) σ)
          (independentPortProduct torusOutgoingNeighbor
            (fun r (_ : TorusVertex width height) =>
              (Q r : Matrix
                (Fin (if r then A.bondDim (torusUpEdge 0) else A.bondDim (torusRightEdge 0)))
                (Fin (if r then A.bondDim (torusUpEdge 0) else A.bondDim (torusRightEdge 0)))
                ℂ))) := by
  classical
  let hU := torusUniformBondDim_of_isTorusTranslationInvariantState hInj hTI
  let E := torusDirectionPortConfigEquiv A hU
  let n (r : Bool) := if r then A.bondDim (torusUpEdge 0) else A.bondDim (torusRightEdge 0)
  let Xi := (r : Bool) → Bool → Fin (n r)
  let F : Matrix (Fin d) Xi ℂ := fun σ x => A.component 0 (E 0 x) σ
  obtain ⟨K, hK⟩ := exists_torus_common_local_orbit_incident hInj hTI
  let M := fun p ie => (K p ie : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)
  let R : (TorusVertex width height → Xi) → ℂ := fun x =>
    independentLegEdgeCoefficient A M (fun p => E p (x p))
  have hlocal (p : TorusVertex width height) (η : LocalVirtualConfig A p) (σ : Fin d) :
      A.component p η σ =
        ∑ ξ : LocalVirtualConfig A p,
          (∏ ie, M p ie (η ie) (ξ ie)) * F σ ((E p).symm ξ) := by
    have href (ξ : LocalVirtualConfig A p) : F σ ((E p).symm ξ) =
        A.component 0 (torusFourLegConfigEquiv A hU 0
          ((torusFourLegConfigEquiv A hU p).symm ξ)) σ := by
      let L := fourLegConfigEquivDirectionPorts
        (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0))
      change A.component 0 (torusFourLegConfigEquiv A hU 0
        (L.symm (L ((torusFourLegConfigEquiv A hU p).symm ξ)))) σ = _
      exact congrArg
        (fun y : (i : Fin 4) → Fin (torusFourLegBondDim A i) =>
          A.component 0 (torusFourLegConfigEquiv A hU 0 y) σ)
        (L.symm_apply_apply ((torusFourLegConfigEquiv A hU p).symm ξ))
    calc
      A.component p η σ = _ := hK p η σ
      _ = _ := by
        refine Finset.sum_congr rfl ?_
        intro ξ hξ
        rw [href]
  have hC : stateCoeff A = dependentPhysicalProductFamilyMap
      (fun _ : TorusVertex width height => F) R :=
    stateCoeff_eq_commonPhysicalProductFamilyMap A E (fun x σ => F σ x) M hlocal
  have hF : Function.Injective (Matrix.mulVecLin F) :=
    Matrix.mulVec_injective_iff.mpr
      ((hInj.isVertexInjective 0).comp (E 0) (E 0).injective)
  have hR (a : ZMod width) (b : ZMod height) (x : TorusVertex width height → Xi) :
      R (fun p => x (translateEquiv a b p)) = R x := by
    refine invariant_of_commonPhysicalProductFamilyMap_invariant F hF
      (translateEquiv a b) R ?_ x
    intro σ
    rw [← hC]
    simpa only [translate_apply, translateEquiv_apply] using hTI a b σ
  let B : (r : Bool) → TorusVertex width height → GL (Fin (n r)) ℂ :=
    fun r p => torusNativeIndependentEdgeKernel A hU K (r, p)
  have hNative (x : TorusVertex width height → Xi) : R x =
      independentPortProduct torusOutgoingNeighbor
        (fun r p => (B r p : Matrix (Fin (n r)) (Fin (n r)) ℂ)) x :=
    independentLegEdgeCoefficient_eq_torusNativeProduct A hU K x
  have hB (a : ZMod width) (b : ZMod height) (x : TorusVertex width height → Xi) :
      independentPortProduct torusOutgoingNeighbor
          (fun r p => (B r p : Matrix (Fin (n r)) (Fin (n r)) ℂ))
          (fun p => x (translateEquiv a b p)) =
        independentPortProduct torusOutgoingNeighbor
          (fun r p => (B r p : Matrix (Fin (n r)) (Fin (n r)) ℂ)) x := by
    rw [← hNative, ← hNative]
    exact hR a b x
  have hn (r : Bool) : 0 < n r := by
    cases r
    · exact hInj.bondDim_pos (torusRightEdge 0)
    · exact hInj.bondDim_pos (torusUpEdge 0)
  obtain ⟨α, hα, hscale⟩ :=
    Matrix.GeneralLinearGroup.exists_directional_scalars_of_prod_translate_eq hn B
      (fun t c => torus_prod_translate_eq_of_portProduct_invariant
        (fun r p => (B r p : Matrix (Fin (n r)) (Fin (n r)) ℂ)) hB t c)
  let Γ : ℂ := ∏ z : Bool × TorusVertex width height, α z.1 z.2
  have hΓ : Γ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun z _ => hα z.1 z.2)
  let R₀ : (TorusVertex width height → Xi) → ℂ := independentPortProduct
    torusOutgoingNeighbor (fun r (_ : TorusVertex width height) =>
      (B r 0 : Matrix (Fin (n r)) (Fin (n r)) ℂ))
  have hRR : R = Γ • R₀ := by
    funext x
    rw [hNative]
    change (∏ z : Bool × TorusVertex width height,
      (B z.1 z.2 : Matrix (Fin (n z.1)) (Fin (n z.1)) ℂ)
        (x z.2 z.1 true) (x (torusOutgoingNeighbor z.1 z.2) z.1 false)) =
      Γ * ∏ z : Bool × TorusVertex width height,
        (B z.1 0 : Matrix (Fin (n z.1)) (Fin (n z.1)) ℂ)
          (x z.2 z.1 true) (x (torusOutgoingNeighbor z.1 z.2) z.1 false)
    calc
      _ = ∏ z : Bool × TorusVertex width height,
          α z.1 z.2 * (B z.1 0 : Matrix (Fin (n z.1)) (Fin (n z.1)) ℂ)
            (x z.2 z.1 true) (x (torusOutgoingNeighbor z.1 z.2) z.1 false) := by
        refine Finset.prod_congr rfl ?_
        intro z hz
        exact hscale z.1 z.2 _ _
      _ = _ := Finset.prod_mul_distrib
  refine ⟨fun r => B r 0, Γ, hΓ, ?_⟩
  change stateCoeff A = Γ • dependentPhysicalProductFamilyMap
    (fun _ : TorusVertex width height => F) R₀
  rw [hC, hRR, map_smul]

end TNLean.PEPS

namespace TNLean.PEPS
open TNLean.Lattice

variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- Put the transposed directional bond matrices on right and down and
identity matrices on top and left. Supporting construction for
arXiv:1804.04964, lines 1891–1894. -/
noncomputable def torusUniformBondLegKernel
    (A : Tensor (torusGraph width height) d)
    (Q : (r : Bool) → GL (Fin (if r then A.bondDim (torusUpEdge 0)
      else A.bondDim (torusRightEdge 0))) ℂ) :
    (i : Fin 4) → GL (Fin (torusFourLegBondDim A i)) ℂ :=
  Fin.cases 1 (Fin.cases (glTranspose (Q false))
    (Fin.cases (glTranspose (Q true)) (Fin.cases 1 (fun i => Fin.elim0 i))))

/-- The outgoing reference kernel is the transpose of the directional factor.
Supporting identity for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusFourLegKernelOnPort_uniformBond_out
    (A : Tensor (torusGraph width height) d)
    (Q : (r : Bool) → GL (Fin (if r then A.bondDim (torusUpEdge 0)
      else A.bondDim (torusRightEdge 0))) ℂ) (r : Bool) :
    torusFourLegKernelOnPort A (torusUniformBondLegKernel A Q) r true =
      glTranspose (Q r) := by
  cases r <;> rfl

/-- The incoming reference kernel is the identity.
Supporting identity for arXiv:1804.04964, lines 1891–1894. -/
private theorem torusFourLegKernelOnPort_uniformBond_in
    (A : Tensor (torusGraph width height) d)
    (Q : (r : Bool) → GL (Fin (if r then A.bondDim (torusUpEdge 0)
      else A.bondDim (torusRightEdge 0))) ℂ) (r : Bool) :
    torusFourLegKernelOnPort A (torusUniformBondLegKernel A Q) r false = 1 := by
  cases r <;> rfl

/-- Absorbing a directional factor on its outgoing leg produces that factor
on the actual native edge. Supporting identity for arXiv:1804.04964,
lines 1891–1894. -/
private theorem torusNativeIndependentEdgeKernel_uniformBond
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (Q : (r : Bool) → GL (Fin (if r then A.bondDim (torusUpEdge 0)
      else A.bondDim (torusRightEdge 0))) ℂ)
    (r : Bool) (p : TorusVertex width height) :
    torusNativeIndependentEdgeKernel A hU
        (torusIncidentKernelOfFourLeg A hU (torusUniformBondLegKernel A Q)) (r, p) =
      Q r := by
  have hdouble : glTranspose (glTranspose (Q r)) = Q r := by
    apply Units.ext
    exact Matrix.transpose_transpose _
  calc
    _ = glTranspose
          (torusFourLegKernelOnPort A (torusUniformBondLegKernel A Q) r true) *
        torusFourLegKernelOnPort A (torusUniformBondLegKernel A Q) r false :=
      torusNativeIndependentEdgeKernel_fourLeg A hU (torusUniformBondLegKernel A Q) r p
    _ = glTranspose (glTranspose (Q r)) * 1 :=
      congrArg₂ (fun U V : GL (Fin (if r then A.bondDim (torusUpEdge 0)
          else A.bondDim (torusRightEdge 0))) ℂ => U * V)
        (congrArg glTranspose (torusFourLegKernelOnPort_uniformBond_out A Q r))
        (torusFourLegKernelOnPort_uniformBond_in A Q r)
    _ = _ := by simpa only [mul_one] using hdouble

/-- The explicit absorbed common tensor has exactly the uniform directional
bond representation of its unmodified physical array. This proves the
unscaled state equality, rather than taking it as a reconstruction premise.
Supporting construction for arXiv:1804.04964, lines 1891–1894. -/
theorem stateCoeff_torusFourLegTensor_uniformBondAbsorption
    (A : Tensor (torusGraph width height) d)
    (hU : TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)))
    (Q : (r : Bool) → GL (Fin (if r then A.bondDim (torusUpEdge 0)
      else A.bondDim (torusRightEdge 0))) ℂ)
    (F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ) :
    let L : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) ≃
        ((r : Bool) → Bool → Fin (if r then A.bondDim (torusUpEdge 0)
          else A.bondDim (torusRightEdge 0))) :=
      fourLegConfigEquivDirectionPorts (A.bondDim (torusRightEdge 0))
        (A.bondDim (torusUpEdge 0))
    stateCoeff (torusFourLegTensor A hU
        (fourLegKernelApply A (torusUniformBondLegKernel A Q) F)) =
      dependentPhysicalProductFamilyMap
        (fun (_ : TorusVertex width height) (σ : Fin d) x => F (L.symm x) σ)
        (independentPortProduct torusOutgoingNeighbor
          (fun r (_ : TorusVertex width height) => (Q r : Matrix
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0)))
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ))) := by
  classical
  let Xi4 := (i : Fin 4) → Fin (torusFourLegBondDim A i)
  let XiPort := (r : Bool) → Bool → Fin (if r then A.bondDim (torusUpEdge 0)
    else A.bondDim (torusRightEdge 0))
  let L : Xi4 ≃ XiPort :=
    fourLegConfigEquivDirectionPorts (A.bondDim (torusRightEdge 0))
      (A.bondDim (torusUpEdge 0))
  let E := torusFourLegConfigEquiv A hU
  let P := torusUniformBondLegKernel A Q
  let K := torusIncidentKernelOfFourLeg A hU P
  let M := fun p ie => (K p ie : Matrix (Fin (A.bondDim ie.1))
    (Fin (A.bondDim ie.1)) ℂ)
  let B := torusFourLegTensor A hU (fourLegKernelApply A P F)
  let R4 : (TorusVertex width height → Xi4) → ℂ := fun x =>
    independentLegEdgeCoefficient A M (fun p => E p (x p))
  let Rp : (TorusVertex width height → XiPort) → ℂ := fun x =>
    R4 (fun p => L.symm (x p))
  let R0 : (TorusVertex width height → XiPort) → ℂ := independentPortProduct
    torusOutgoingNeighbor (fun r (_ : TorusVertex width height) => (Q r : Matrix
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0)))
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ))
  have hlocal (p : TorusVertex width height) (η : LocalVirtualConfig A p) (σ : Fin d) :
      B.component p η σ =
        ∑ ξ : LocalVirtualConfig A p,
          (∏ ie, M p ie (η ie) (ξ ie)) * F ((E p).symm ξ) σ :=
    fourLegKernelApply_eq_sum_incident A hU P F p η σ
  have hC : stateCoeff B = dependentPhysicalProductFamilyMap
      (fun (_ : TorusVertex width height) (σ : Fin d) x => F x σ) R4 :=
    stateCoeff_eq_commonPhysicalProductFamilyMap B E F M hlocal
  have hReindex : dependentPhysicalProductFamilyMap
      (fun (_ : TorusVertex width height) (σ : Fin d) x => F (L.symm x) σ) Rp =
        dependentPhysicalProductFamilyMap
          (fun (_ : TorusVertex width height) (σ : Fin d) x => F x σ) R4 :=
    dependentPhysicalProductFamilyMap_reindex_input
      (fun _ : TorusVertex width height => L.symm)
      (fun (_ : TorusVertex width height) (σ : Fin d) x => F x σ) R4
  have hRp : Rp = R0 := by
    funext x
    calc
      Rp x = independentPortProduct torusOutgoingNeighbor
          (fun r p => (torusNativeIndependentEdgeKernel A hU K (r, p) : Matrix
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0)))
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ)) x :=
        independentLegEdgeCoefficient_eq_torusNativeProduct A hU K x
      _ = R0 x := by
        change (∏ z : Bool × TorusVertex width height,
          (torusNativeIndependentEdgeKernel A hU K (z.1, z.2) : Matrix
            (Fin (if z.1 then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0)))
            (Fin (if z.1 then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ)
            (x z.2 z.1 true) (x (torusOutgoingNeighbor z.1 z.2) z.1 false)) =
          ∏ z : Bool × TorusVertex width height,
            (Q z.1 : Matrix
            (Fin (if z.1 then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0)))
            (Fin (if z.1 then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ)
              (x z.2 z.1 true) (x (torusOutgoingNeighbor z.1 z.2) z.1 false)
        refine Finset.prod_congr rfl ?_
        rintro ⟨r, p⟩ hz
        exact congrArg
          (fun Z : GL (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ =>
            (Z : Matrix
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0)))
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ)
            (x p r true) (x (torusOutgoingNeighbor r p) r false))
          (torusNativeIndependentEdgeKernel_uniformBond A hU Q r p)
  calc
    stateCoeff B = _ := hC
    _ = _ := hReindex.symm
    _ = _ := congrArg
      (dependentPhysicalProductFamilyMap
        (fun (_ : TorusVertex width height) (σ : Fin d) x => F (L.symm x) σ)) hRp

/-- A translation-invariant injective PEPS vector on a fixed simple torus
with both periods at least three is represented by a repeated injective tensor
with exactly the original bond dimensions.
Source: arXiv:1804.04964, lines 1207–1212 and 1891–1899. -/
theorem exists_isTorusTranslationInvariant_sameState
    {A : Tensor (torusGraph width height) d}
    (hInj : A.IsInjective) (hTI : IsTorusTranslationInvariantState A) :
    ∃ B : Tensor (torusGraph width height) d,
      B.IsInjective ∧ IsTorusTranslationInvariant B ∧ SameState A B ∧
        B.bondDim = A.bondDim := by
  classical
  let hU := torusUniformBondDim_of_isTorusTranslationInvariantState hInj hTI
  let E := torusFourLegConfigEquiv A hU
  obtain ⟨Q, Γ, hΓ, hRep⟩ := exists_torus_uniform_edge_representation hInj hTI
  let F : ((i : Fin 4) → Fin (torusFourLegBondDim A i)) → Fin d → ℂ :=
    fun x => A.component 0 (E 0 x)
  let P := torusUniformBondLegKernel A Q
  let G := fourLegKernelApply A P F
  let Ψ := dependentPhysicalProductFamilyMap
    (fun (_ : TorusVertex width height) (σ : Fin d) x =>
      A.component 0 (torusDirectionPortConfigEquiv A hU 0 x) σ)
    (independentPortProduct torusOutgoingNeighbor
      (fun r (_ : TorusVertex width height) => (Q r : Matrix
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0)))
            (Fin (if r then A.bondDim (torusUpEdge 0)
              else A.bondDim (torusRightEdge 0))) ℂ)))
  have hOriginal : stateCoeff A = Γ • Ψ := hRep
  have hUnscaled : stateCoeff (torusFourLegTensor A hU G) = Ψ :=
    stateCoeff_torusFourLegTensor_uniformBondAbsorption A hU Q F
  have hN : 0 < Fintype.card (TorusVertex width height) := Fintype.card_pos
  obtain ⟨ρ, hρpow⟩ := IsAlgClosed.exists_pow_nat_eq Γ hN
  have hρ : ρ ≠ 0 := by
    intro hz
    apply hΓ
    rw [← hρpow, hz, zero_pow (Nat.ne_of_gt hN)]
  have hF : LinearIndependent ℂ F :=
    (hInj.isVertexInjective 0).comp (E 0) (E 0).injective
  have hG : LinearIndependent ℂ (fun x => ρ • G x) :=
    linearIndependent_smul_piProductKernel F hF P ρ hρ
  let B := torusFourLegTensor A hU (fun x => ρ • G x)
  have hBInj : B.IsInjective :=
    isInjective_torusFourLegTensor A hU (fun x => ρ • G x) hG hInj.bondDim_pos
  have hBTI : IsTorusTranslationInvariant B :=
    isTorusTranslationInvariant_torusFourLegTensor A hU (fun x => ρ • G x)
  have hSame : SameState A B := by
    intro σ
    calc
      stateCoeff A σ = Γ * Ψ σ := congr_fun hOriginal σ
      _ = ρ ^ Fintype.card (TorusVertex width height) *
          stateCoeff (torusFourLegTensor A hU G) σ :=
        congrArg₂ (fun u v : ℂ => u * v) hρpow.symm (congr_fun hUnscaled σ).symm
      _ = stateCoeff B σ := (stateCoeff_torusFourLegTensor_smul A hU G ρ σ).symm
  exact ⟨B, hBInj, hBTI, hSame, rfl⟩

end TNLean.PEPS
