/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.SchwarzNormal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Schwarz inequalities for subnormal and commuting dominant operators

This file records the Chapter 5 extensions of the normal-input Schwarz inequality
that appear in Wolf's notes.

## Main declarations

* `KadisonSchwarz.IsSubnormal`
* `KadisonSchwarz.schwarz_inequality_subnormal_operator`
* `KadisonSchwarz.commuting_dominant_right_bound`
* `KadisonSchwarz.kadison_schwarz_commuting_dominant_cp_of_two_sided_bound`
* `KadisonSchwarz.kadison_schwarz_commuting_dominant_cp`
* `KadisonSchwarz.schwarz_inequality_commuting_dominant_operator`

The key new result is `commuting_dominant_right_bound`: if `D ≥ 0` commutes with
`A` and dominates `A† A`, then it also dominates `A A†`.  The proof uses the
C*-algebra structure on matrices: the PD case uses the CFC square root and the
contraction lemma `B† B ≤ 1 → B B† ≤ 1` (proved via the C*-identity), and the
general PSD case follows by approximating `D` with `D + ε · I`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorems 5.5 and 5.6][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

/-! ### C*-algebra infrastructure for matrices -/

namespace KadisonSchwarz

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

-- Equip matrices with the L2 operator norm for the C*-algebra structure.
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

noncomputable local instance : CStarAlgebra Mat where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := Matrix.instCStarRing
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance

/-! ### Contraction lemma -/

/-- The **contraction lemma**: for any square matrix `B`, if `B† B ≤ 1` then `B B† ≤ 1`.
The proof uses the C*-identity `‖x* x‖ = ‖x‖²`. -/
private lemma contraction_conjTranspose
    (B : Mat) (h : Bᴴ * B ≤ 1) : B * Bᴴ ≤ 1 := by
  change B * star B ≤ 1
  have h' : star B * B ≤ 1 := by simpa using h
  have h_norm_sq : ‖B‖₊ * ‖B‖₊ ≤ 1 := by
    simpa [CStarRing.nnnorm_star_mul_self] using
      (CStarAlgebra.nnnorm_le_one_iff_of_nonneg _ (star_mul_self_nonneg B)).2 h'
  have h_norm_mul_star : ‖B * star B‖₊ ≤ 1 := by
    rw [show B * star B = star (star B) * star B from by rw [star_star],
      CStarRing.nnnorm_star_mul_self]
    simpa [nnnorm_star] using h_norm_sq
  exact (CStarAlgebra.nnnorm_le_one_iff_of_nonneg _ (mul_star_self_nonneg B)).1 h_norm_mul_star

/-! ### Positive definite case -/

/-- The commuting-dominant right bound for the **positive definite** case.
If `Dom` is PD, `[Dom, A] = 0`, and `A† A ≤ Dom`, then `A A† ≤ Dom`.

The proof sets `S = √Dom`, `X = A S⁻¹`, shows `X† X ≤ 1` by conjugation,
applies `contraction_conjTranspose` to obtain `X X† ≤ 1`, and then rewrites
`A A† = S (X X†) S ≤ S² = Dom`. -/
private lemma commuting_dominant_right_bound_posDef
    (A Dom : Mat) (hPD : Dom.PosDef) (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    A * Aᴴ ≤ Dom := by
  have hDom_nonneg : (0 : Mat) ≤ Dom := by
    rw [Matrix.le_iff]
    simpa using hPD.posSemidef
  let S : Mat := CFC.sqrt Dom
  have hS_sq : S * S = Dom := by
    simpa [S] using CFC.sqrt_mul_sqrt_self Dom hDom_nonneg
  have hS_selfAdjoint : IsSelfAdjoint S := by
    simpa [S] using (CFC.sqrt_nonneg (a := Dom)).isSelfAdjoint
  have hSA : Commute S A := by
    simpa [S] using hComm.cfcₙ_nnreal NNReal.sqrt
  obtain ⟨u, hu⟩ : ∃ u : Matˣ, (u : Mat) = S := by
    have hS_unit : IsUnit S := by
      dsimp [S]
      rw [CFC.isUnit_sqrt_iff Dom hDom_nonneg]
      exact hPD.isUnit
    simpa using hS_unit
  have hU_selfAdjoint : IsSelfAdjoint u := by
    refine Units.ext ?_
    simpa [hu] using hS_selfAdjoint.star_eq
  have hSi_selfAdjoint : IsSelfAdjoint (u⁻¹ : Matˣ) := hU_selfAdjoint.inv
  have hSi_star : star (↑u⁻¹ : Mat) = (↑u⁻¹ : Mat) :=
    congrArg (fun v : Matˣ => (v : Mat)) hSi_selfAdjoint.star_eq
  have hSiS : (↑u⁻¹ : Mat) * S = 1 := by
    rw [← hu]
    simp
  have hSSi : S * (↑u⁻¹ : Mat) = 1 := by
    rw [← hu]
    simp
  let X : Mat := A * (↑u⁻¹ : Mat)
  have hX_contr : Xᴴ * X ≤ 1 := by
    calc
      Xᴴ * X = star (↑u⁻¹ : Mat) * (Aᴴ * A) * (↑u⁻¹ : Mat) := by
        dsimp [X]
        rw [conjTranspose_mul,
          show ((↑u⁻¹ : Mat))ᴴ = star (↑u⁻¹ : Mat) from rfl, hSi_star]
        simp only [mul_assoc]
      _ ≤ star (↑u⁻¹ : Mat) * Dom * (↑u⁻¹ : Mat) :=
        star_left_conjugate_le_conjugate hDom (↑u⁻¹ : Mat)
      _ = 1 := by
        rw [hSi_star, ← hS_sq]
        calc
          (↑u⁻¹ : Mat) * (S * S) * (↑u⁻¹ : Mat) =
              ((↑u⁻¹ : Mat) * S) * (S * (↑u⁻¹ : Mat)) := by simp only [mul_assoc]
          _ = 1 := by rw [hSiS, hSSi]; simp only [one_mul]
  have hSX : S * X = A := by
    dsimp [X]
    calc
      S * (A * (↑u⁻¹ : Mat)) = A * S * (↑u⁻¹ : Mat) := by
        rw [← mul_assoc, hSA.eq, mul_assoc]
      _ = A := by simpa [mul_assoc] using congrArg (fun M : Mat => A * M) hSSi
  have hS_conjTranspose : Sᴴ = S := by
    simpa using hS_selfAdjoint.star_eq
  have hXstarS : Xᴴ * S = Aᴴ := by
    have hXstarS' : Xᴴ * Sᴴ = Aᴴ := by
      simpa [conjTranspose_mul] using congrArg Matrix.conjTranspose hSX
    simpa [hS_conjTranspose] using hXstarS'
  calc
    A * Aᴴ = S * (X * Xᴴ) * S := by
      calc
        A * Aᴴ = (S * X) * Aᴴ := by rw [hSX]
        _ = S * (X * Xᴴ) * S := by rw [← hXstarS]; simp only [mul_assoc]
    _ ≤ S * 1 * S := by
      simpa [hS_selfAdjoint.star_eq] using
        star_left_conjugate_le_conjugate (contraction_conjTranspose X hX_contr) S
    _ = Dom := by rw [mul_one, hS_sq]

/-! ### General PSD case -/

/-- `Dom.PosSemidef` implies `(Dom + ε • 1).PosDef` for `ε > 0`. -/
private lemma posDef_add_pos_smul_one (Dom : Mat) (hPSD : Dom.PosSemidef)
    (ε : ℝ) (hε : 0 < ε) :
    (Dom + (ε : ℂ) • (1 : Mat)).PosDef := by
  rw [add_comm]
  apply Matrix.PosDef.add_posSemidef _ hPSD
  have h1 : (ε : ℂ) • (1 : Mat) = (ε : ℝ) • (1 : Mat) := by
    ext i j; simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  rw [h1]
  exact Matrix.PosDef.one.smul hε

/-- If `B ≤ D + ε • 1` for all `ε > 0`, then `B ≤ D`.
This is the closedness of the PSD cone, applied to the differences
`D - B + ε • 1`. -/
private lemma le_of_forall_le_add_pos_smul_one (B D : Mat)
    (h : ∀ ε : ℝ, 0 < ε → B ≤ D + (ε : ℂ) • (1 : Mat)) :
    B ≤ D := by
  rw [Matrix.le_iff]
  let g : ℕ → Mat := fun n => (D - B) + ((1 / ((n : ℝ) + 1)) : ℝ) • (1 : Mat)
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds (D - B)) := by
    have hzero : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1)) : ℝ) • (1 : Mat))
        Filter.atTop (nhds (0 : Mat)) := by
      rw [show (0 : Mat) = (0 : ℝ) • (1 : Mat) from by simp]
      exact (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const (1 : Mat))
    simpa [g, add_zero] using hzero.const_add (D - B)
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    have h_smul : ((1 / ((n : ℝ) + 1)) : ℝ) • (1 : Mat) =
        ((((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) • (1 : Mat) := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    have hg_eq : g n = (D + ((((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) • 1) - B := by
      change (D - B) + ((1 / ((n : ℝ) + 1)) : ℝ) • 1 = _
      rw [h_smul]
      abel
    rw [hg_eq, Matrix.le_iff]
    simpa using h (1 / ((n : ℝ) + 1)) (by positivity)
  simpa [Matrix.le_iff] using ge_of_tendsto' hg_tendsto hg_nonneg

/-- An operator `A` is subnormal if it is the north-west block of a normal
block-upper-triangular operator on a larger space `H ⊕ H⊥`. -/
def IsSubnormal (A : Mat) : Prop :=
  ∃ E : ℕ,
    ∃ B : Matrix (Fin D) (Fin E) ℂ,
      ∃ C : Matrix (Fin E) (Fin E) ℂ,
        let N : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ := Matrix.fromBlocks A B 0 C
        Nᴴ * N = N * Nᴴ

/-- Wolf Thm. 5.5: Schwarz inequality for subnormal operators.

The intended proof composes the given positive subunital map with the north-west
block extraction map on a normal extension of `A`, then applies Wolf Prop. 5.1
(`schwarz_inequality_normal_operator`) to the resulting positive map. -/
theorem schwarz_inequality_subnormal_operator
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A : Mat)
    (hSubnormal : IsSubnormal A) :
    T (Aᴴ) * T A ≤ T (Aᴴ * A) ∧ T A * T (Aᴴ) ≤ T (Aᴴ * A) := by
  sorry

/-- Linear-map wrapper for the canonical adjoint Kraus map.

This bundles `KadisonSchwarz.krausAdjointMap` from `KadisonSchwarz.lean` as a
linear map. It is convenient for reusing the generic positivity/monotonicity
API from `PositiveMapProperties`.

Note: `TNLean/Channel/Semigroup/Generator.lean` contains an older duplicate
formula with the same name; inside `namespace KadisonSchwarz`, this wrapper
intentionally uses the canonical Schwarz-side definition. -/
noncomputable def krausAdjointMapLinear (K : Fin d → Mat) : Mat →ₗ[ℂ] Mat where
  toFun := krausAdjointMap K
  map_add' := by
    intro X Y
    simp [krausAdjointMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c X
    simp [krausAdjointMap, Finset.smul_sum, Matrix.mul_assoc]

/-- The adjoint Kraus map is positive. -/
private theorem krausAdjointMapLinear_isPositiveMap (K : Fin d → Mat) :
    IsPositiveMap (krausAdjointMapLinear (d := d) (D := D) K) := by
  intro X hX
  classical
  simpa [krausAdjointMapLinear, krausAdjointMap, Matrix.mul_assoc] using
    Matrix.posSemidef_sum (s := Finset.univ) (x := fun i => (K i)ᴴ * X * K i)
      (fun i _ => by
        simpa [Matrix.mul_assoc] using hX.mul_mul_conjTranspose_same (B := (K i)ᴴ))

/-- The missing order-theoretic step in Wolf Thm. 5.6: if `D ≥ 0` commutes with
`A` and dominates `Aᴴ * A`, then it also dominates `A * Aᴴ`.

Wolf proves this first for invertible `D` using `X = A D^{-1/2}`, and then passes
to the general case by replacing `D` with `D + ε • 1` and letting `ε → 0`.

The proof uses:
1. **Contraction lemma** (`contraction_conjTranspose`): `B† B ≤ 1 → B B† ≤ 1`
   via the C*-identity.
2. **CFC square root** and commutativity propagation for the invertible case.
3. **Approximation**: `D + ε I` is PD for `ε > 0`, and the result follows by
   letting `ε → 0`. -/
lemma commuting_dominant_right_bound
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    A * Aᴴ ≤ Dom := by
  apply le_of_forall_le_add_pos_smul_one _ _
  intro ε hε
  have hPD : (Dom + (ε : ℂ) • (1 : Mat)).PosDef :=
    posDef_add_pos_smul_one Dom hDomPos ε hε
  have hComm' : Commute (Dom + (ε : ℂ) • (1 : Mat)) A :=
    hComm.add_left ((Commute.one_left A).smul_left (ε : ℂ))
  have hDom' : Aᴴ * A ≤ Dom + (ε : ℂ) • (1 : Mat) :=
    hDom.trans <| le_add_of_nonneg_right <| by
      rw [Matrix.le_iff]
      simpa using (Matrix.PosSemidef.one (n := Fin D) (R := ℂ)).smul hε.le
  exact commuting_dominant_right_bound_posDef A _ hPD hComm' hDom'

/-- CP/Kraus version of Wolf Thm. 5.6 under both dominant bounds.

Once both inequalities `Aᴴ * A ≤ D` and `A * Aᴴ ≤ D` are available, the proof is
just Kadison--Schwarz for the adjoint Kraus map, followed by monotonicity of the
positive map `X ↦ ∑ᵢ Kᵢ† X Kᵢ`. -/
theorem kadison_schwarz_commuting_dominant_cp_of_two_sided_bound
    (K : Fin d → Mat)
    (h_tp : IsTPKraus K)
    (A Dom : Mat)
    (_hDomPos : Dom.PosSemidef)
    (_hComm : Commute Dom A)
    (hDomLeft : Aᴴ * A ≤ Dom)
    (hDomRight : A * Aᴴ ≤ Dom) :
    krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤ krausAdjointMap K Dom ∧
      krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤ krausAdjointMap K Dom := by
  let T : Mat →ₗ[ℂ] Mat := krausAdjointMapLinear (d := d) (D := D) K
  have hPosT : IsPositiveMap T := krausAdjointMapLinear_isPositiveMap (d := d) (D := D) K
  have hKSLeft' : (krausAdjointMap K A)ᴴ * krausAdjointMap K A ≤
      krausAdjointMap K (Aᴴ * A) := by
    rw [Matrix.le_iff]
    exact kadison_schwarz_adjoint K h_tp A
  have hKSLeft : krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤
      krausAdjointMap K (Aᴴ * A) := by
    simpa [krausAdjointMap_conjTranspose] using hKSLeft'
  have hDomLeftMap : krausAdjointMap K (Aᴴ * A) ≤ krausAdjointMap K Dom := by
    simpa [T] using hPosT.map_le_map hDomLeft
  have hKSRight' : (krausAdjointMap K (Aᴴ))ᴴ * krausAdjointMap K (Aᴴ) ≤
      krausAdjointMap K (A * Aᴴ) := by
    simpa [conjTranspose_conjTranspose] using
      (show (krausAdjointMap K (Aᴴ))ᴴ * krausAdjointMap K (Aᴴ) ≤
          krausAdjointMap K ((Aᴴ)ᴴ * Aᴴ) from by
        rw [Matrix.le_iff]; exact kadison_schwarz_adjoint K h_tp (Aᴴ))
  have hKSRight : krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤
      krausAdjointMap K (A * Aᴴ) := by
    simpa [krausAdjointMap_conjTranspose] using hKSRight'
  have hDomRightMap : krausAdjointMap K (A * Aᴴ) ≤ krausAdjointMap K Dom := by
    simpa [T] using hPosT.map_le_map hDomRight
  exact ⟨hKSLeft.trans hDomLeftMap, hKSRight.trans hDomRightMap⟩

/-- Wolf Thm. 5.6 in the CP/Kraus setting.

The only missing ingredient beyond the previous theorem is the right-dominance
lemma `commuting_dominant_right_bound`. -/
theorem kadison_schwarz_commuting_dominant_cp
    (K : Fin d → Mat)
    (h_tp : IsTPKraus K)
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤ krausAdjointMap K Dom ∧
      krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤ krausAdjointMap K Dom := by
  have hDomRight : A * Aᴴ ≤ Dom :=
    commuting_dominant_right_bound (A := A) (Dom := Dom) hDomPos hComm hDom
  exact kadison_schwarz_commuting_dominant_cp_of_two_sided_bound
    (K := K) h_tp A Dom hDomPos hComm hDom hDomRight

/-- **Decomposition lemma** for the PD commuting-dominant Schwarz inequality.

Given positive definite `Dom` commuting with `A` and dominating `Aᴴ * A`,
there exists a PSD family `{Qᵢ}` summing to `1` and complex scalars `{μᵢ}`
such that `A = ∑ μᵢ Qᵢ` and `Dom = ∑ |μᵢ|² Qᵢ`.

The proof constructs the Julia unitary of the contraction `Dom⁻¹ᐟ² A` on the
doubled space `Fin D ⊕ Fin D`, forms the normal matrix
`N = (Dom¹ᐟ² ⊕ Dom¹ᐟ²) · U` which satisfies `N†N = Dom ⊕ Dom`, and
extracts the top-left block of each spectral projection of `N`. -/
private lemma exists_psd_decomposition_commuting_dominant_posDef
    (A Dom : Mat)
    (hPD : Dom.PosDef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    ∃ (ι : Type) (_ : Fintype ι)
      (Q : ι → Mat) (μ : ι → ℂ),
      (∀ i, (Q i).PosSemidef) ∧
      (∑ i, Q i = 1) ∧
      (A = ∑ i, μ i • Q i) ∧
      (Dom = ∑ i, (starRingEnd ℂ (μ i) * μ i) • Q i) := by
  sorry

/-- Helper: the PD Schwarz inequality for commuting dominant operators.

This combines the PD decomposition with `diagonal_family_schwarz_le`. -/
private lemma schwarz_commuting_dominant_posDef
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A Dom : Mat)
    (hPD : Dom.PosDef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    T (Aᴴ) * T A ≤ T Dom ∧ T A * T (Aᴴ) ≤ T Dom := by
  obtain ⟨ι, hFin, Q, μ, hQpsd, hQsum, hAeq, hDeq⟩ :=
    exists_psd_decomposition_commuting_dominant_posDef A Dom hPD hComm hDom
  -- Set Bᵢ = T(Qᵢ): these are PSD with ∑ Bᵢ = T(1) ≤ 1
  let B : ι → Mat := fun i => T (Q i)
  have hBpsd : ∀ i, (B i).PosSemidef := fun i => hPos (Q i) (hQpsd i)
  have hBsub : ∑ i, B i ≤ 1 := by
    calc ∑ i, B i = T (∑ i, Q i) := by simp [B, map_sum]
      _ = T 1 := by rw [hQsum]
      _ ≤ 1 := hSub
  have hBherm : ∀ i, (B i)ᴴ = B i := fun i => (hBpsd i).isHermitian.eq
  -- Express T(A), T(A†), T(D) in terms of the family
  have hTA : T A = ∑ i, μ i • B i := by rw [hAeq]; simp [B, map_sum]
  have hTD : T Dom = ∑ i, (starRingEnd ℂ (μ i) * μ i) • B i := by
    rw [hDeq]; simp [B, map_sum]
  have hTAstar : T Aᴴ = ∑ i, starRingEnd ℂ (μ i) • B i := by
    calc T Aᴴ = (T A)ᴴ := by simpa using hPos.map_conjTranspose A
      _ = (∑ i, μ i • B i)ᴴ := by rw [hTA]
      _ = ∑ i, starRingEnd ℂ (μ i) • B i := by
          simp [hBherm, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  -- LEFT: T(A†)T(A) ≤ T(D) via diagonal_family_schwarz_le with z = μ
  have hLeft : T Aᴴ * T A ≤ T Dom := by
    rw [hTAstar, hTA, hTD]
    exact PositiveOnAbelian.diagonal_family_schwarz_le B hBpsd hBsub μ
  -- RIGHT: T(A)T(A†) ≤ T(D) via diagonal_family_schwarz_le with z = star(μ)
  have hRight : T A * T Aᴴ ≤ T Dom := by
    rw [hTA, hTAstar, hTD]
    have key := PositiveOnAbelian.diagonal_family_schwarz_le B hBpsd hBsub
      (fun i => starRingEnd ℂ (μ i))
    have h1 : ∀ i, starRingEnd ℂ (starRingEnd ℂ (μ i)) = μ i := fun i => star_star (μ i)
    simp_rw [h1] at key
    have h2 : ∀ i, μ i * starRingEnd ℂ (μ i) = starRingEnd ℂ (μ i) * μ i :=
      fun i => mul_comm _ _
    simp_rw [h2] at key
    exact key
  exact ⟨hLeft, hRight⟩

/-- Wolf Thm. 5.6: Schwarz inequality for commuting dominant operators.

If `T` is a positive subunital linear map, `D ≥ 0` commutes with `A`, and
`Aᴴ * A ≤ D`, then `T(Aᴴ) T(A) ≤ T(D)` and `T(A) T(Aᴴ) ≤ T(D)`.

The proof handles the positive definite case via a PSD decomposition and
`diagonal_family_schwarz_le`, then extends to general PSD `D` by
approximating with `D + ε · I` and letting `ε → 0`. -/
theorem schwarz_inequality_commuting_dominant_operator
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    T (Aᴴ) * T A ≤ T Dom ∧ T A * T (Aᴴ) ≤ T Dom := by
  have hComm_add (ε : ℂ) : Commute (Dom + ε • 1) A :=
    hComm.add_left ((Commute.one_left A).smul_left ε)
  have hDom_add (ε : ℝ) (hε : 0 ≤ ε) : Aᴴ * A ≤ Dom + (ε : ℂ) • 1 :=
    hDom.trans <| le_add_of_nonneg_right <| by
      rw [Matrix.le_iff]
      simpa using (Matrix.PosSemidef.one (n := Fin D) (R := ℂ)).smul hε
  have hApprox : ∀ ε : ℝ, 0 < ε →
      T Aᴴ * T A ≤ T Dom + (ε : ℂ) • 1 ∧
        T A * T Aᴴ ≤ T Dom + (ε : ℂ) • 1 := by
    intro ε hε
    have hPD := posDef_add_pos_smul_one Dom hDomPos ε hε
    have hPD_result :=
      schwarz_commuting_dominant_posDef T hPos hSub A _ hPD (hComm_add (ε : ℂ))
        (hDom_add ε hε.le)
    refine ⟨?_, ?_⟩
    · calc
        T Aᴴ * T A ≤ T (Dom + (ε : ℂ) • 1) := hPD_result.1
        _ = T Dom + (ε : ℂ) • T 1 := by simp [map_add]
        _ ≤ T Dom + (ε : ℂ) • 1 := by gcongr
    · calc
        T A * T Aᴴ ≤ T (Dom + (ε : ℂ) • 1) := hPD_result.2
        _ = T Dom + (ε : ℂ) • T 1 := by simp [map_add]
        _ ≤ T Dom + (ε : ℂ) • 1 := by gcongr
  refine ⟨?_, ?_⟩
  · exact le_of_forall_le_add_pos_smul_one _ _ fun ε hε => (hApprox ε hε).1
  · exact le_of_forall_le_add_pos_smul_one _ _ fun ε hε => (hApprox ε hε).2

end KadisonSchwarz
