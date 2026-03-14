/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.SchwarzNormal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic

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
open Matrix Finset

/-! ### C*-algebra infrastructure for matrices -/

private lemma nnreal_le_one_of_mul_self_le_one (a : NNReal) (h : a * a ≤ 1) : a ≤ 1 := by
  rcases le_total a 1 with h1 | h1
  · exact h1
  · exact (le_mul_of_one_le_left (zero_le a) h1).trans h

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

set_option maxHeartbeats 800000 in
/-- The **contraction lemma**: for any square matrix `B`, if `B† B ≤ 1` then `B B† ≤ 1`.
The proof uses the C*-identity `‖x* x‖ = ‖x‖²`. -/
private lemma contraction_conjTranspose
    (B : Mat) (h : Bᴴ * B ≤ 1) : B * Bᴴ ≤ 1 := by
  show B * star B ≤ 1
  have h' : star B * B ≤ 1 := h
  have h1 : ‖star B * B‖₊ ≤ 1 :=
    (CStarAlgebra.nnnorm_le_one_iff_of_nonneg _ (star_mul_self_nonneg B)).mpr h'
  have hn : ‖B‖₊ ≤ 1 :=
    nnreal_le_one_of_mul_self_le_one _ (CStarRing.nnnorm_star_mul_self (x := B) ▸ h1)
  have h5 : ‖B * star B‖₊ ≤ 1 := by
    rw [show B * star B = star (star B) * star B from by rw [star_star]]
    rw [CStarRing.nnnorm_star_mul_self (x := star B)]
    exact mul_le_one' ((nnnorm_star B) ▸ hn) ((nnnorm_star B) ▸ hn)
  exact (CStarAlgebra.nnnorm_le_one_iff_of_nonneg _ (mul_star_self_nonneg B)).mp h5

/-! ### Positive definite case -/

set_option maxHeartbeats 12800000 in
/-- The commuting-dominant right bound for the **positive definite** case.
If `Dom` is PD, `[Dom, A] = 0`, and `A† A ≤ Dom`, then `A A† ≤ Dom`.

The proof sets `S = √Dom` (CFC square root), `X = A S⁻¹`, shows `X† X ≤ 1`
by conjugation, applies `contraction_conjTranspose` to get `X X† ≤ 1`, and
then reconstitutes `A A† = S (X X†) S ≤ S² = Dom`. -/
private lemma commuting_dominant_right_bound_posDef
    (A Dom : Mat) (hPD : Dom.PosDef) (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    A * Aᴴ ≤ Dom := by
  -- S = √Dom: S² = Dom, star S = S, S invertible, S * A = A * S
  have h0 : (0 : Mat) ≤ Dom := by rw [Matrix.le_iff]; simpa using hPD.posSemidef
  have hSS : CFC.sqrt Dom * CFC.sqrt Dom = Dom := CFC.sqrt_mul_sqrt_self Dom h0
  have hSs : star (CFC.sqrt Dom) = CFC.sqrt Dom :=
    (CFC.sqrt_nonneg (a := Dom)).isSelfAdjoint.star_eq
  have hSA : CFC.sqrt Dom * A = A * CFC.sqrt Dom :=
    ((show Commute Dom A from hComm).cfcₙ_nnreal NNReal.sqrt).eq
  obtain ⟨u, hu⟩ :=
    (show IsUnit (CFC.sqrt Dom) by rw [CFC.isUnit_sqrt_iff Dom h0]; exact hPD.isUnit)
  -- Si = S⁻¹: Si * S = 1, S * Si = 1
  have hSiS : (↑u⁻¹ : Mat) * CFC.sqrt Dom = 1 := by rw [← hu]; simp
  have hSSi : CFC.sqrt Dom * (↑u⁻¹ : Mat) = 1 := by rw [← hu]; simp
  -- star Si = Si (Si is Hermitian)
  have hSis : star (↑u⁻¹ : Mat) = (↑u⁻¹ : Mat) := by
    have h3 : star (↑u⁻¹ : Mat) * CFC.sqrt Dom = 1 := by
      rw [← hSs, ← StarMul.star_mul (CFC.sqrt Dom) (↑u⁻¹ : Mat), hSSi]; exact star_one _
    calc star (↑u⁻¹ : Mat)
        = star (↑u⁻¹ : Mat) * (CFC.sqrt Dom * (↑u⁻¹ : Mat)) := by rw [hSSi, mul_one]
      _ = (star (↑u⁻¹ : Mat) * CFC.sqrt Dom) * (↑u⁻¹ : Mat) := (mul_assoc _ _ _).symm
      _ = (↑u⁻¹ : Mat) := by rw [h3, one_mul]
  -- Si * A = A * Si (inverse commutes)
  have hSiA : (↑u⁻¹ : Mat) * A = A * (↑u⁻¹ : Mat) := by
    have lhs : (↑u⁻¹ : Mat) * A * CFC.sqrt Dom = A := by
      rw [mul_assoc, ← hSA, ← mul_assoc, hSiS, one_mul]
    calc (↑u⁻¹ : Mat) * A
        = (↑u⁻¹ : Mat) * A * (CFC.sqrt Dom * (↑u⁻¹ : Mat)) := by rw [hSSi, mul_one]
      _ = ((↑u⁻¹ : Mat) * A * CFC.sqrt Dom) * (↑u⁻¹ : Mat) := by rw [mul_assoc ((↑u⁻¹ : Mat) * A)]
      _ = A * (↑u⁻¹ : Mat) := by rw [lhs]
  -- X†X ≤ 1: Si * (A†A) * Si ≤ Si * Dom * Si = 1
  have hContr : (A * (↑u⁻¹ : Mat))ᴴ * (A * (↑u⁻¹ : Mat)) ≤ 1 := by
    rw [conjTranspose_mul, show ((↑u⁻¹ : Mat))ᴴ = star (↑u⁻¹ : Mat) from rfl, hSis]
    have : (↑u⁻¹ : Mat) * Aᴴ * (A * (↑u⁻¹ : Mat)) =
        (↑u⁻¹ : Mat) * (Aᴴ * A) * (↑u⁻¹ : Mat) := by simp only [mul_assoc]
    rw [this, show (↑u⁻¹ : Mat) * (Aᴴ * A) * (↑u⁻¹ : Mat) =
        star (↑u⁻¹ : Mat) * (Aᴴ * A) * (↑u⁻¹ : Mat) from by rw [hSis]]
    calc star (↑u⁻¹ : Mat) * (Aᴴ * A) * (↑u⁻¹ : Mat) ≤
          star (↑u⁻¹ : Mat) * Dom * (↑u⁻¹ : Mat) :=
            star_left_conjugate_le_conjugate hDom (↑u⁻¹ : Mat)
      _ = 1 := by rw [hSis, ← hSS]; simp only [mul_assoc]; rw [hSSi, mul_one, hSiS]
  -- A = S * X
  have hA_eq : CFC.sqrt Dom * (A * (↑u⁻¹ : Mat)) = A := by
    rw [← mul_assoc, hSA, mul_assoc, hSSi, mul_one]
  -- AA† = S(XX†)S ≤ S·1·S = Dom
  have hAAstar : A * Aᴴ = CFC.sqrt Dom * ((A * (↑u⁻¹ : Mat)) * (A * (↑u⁻¹ : Mat))ᴴ) *
      CFC.sqrt Dom := by
    conv_lhs => rw [← hA_eq]
    rw [conjTranspose_mul, show (CFC.sqrt Dom)ᴴ = star (CFC.sqrt Dom) from rfl, hSs]
    simp only [mul_assoc]
  rw [hAAstar, show CFC.sqrt Dom * ((A * ↑u⁻¹) * (A * ↑u⁻¹)ᴴ) * CFC.sqrt Dom =
      star (CFC.sqrt Dom) * ((A * ↑u⁻¹) * (A * ↑u⁻¹)ᴴ) * CFC.sqrt Dom from by rw [hSs]]
  calc star (CFC.sqrt Dom) * ((A * ↑u⁻¹) * (A * ↑u⁻¹)ᴴ) * CFC.sqrt Dom ≤
      star (CFC.sqrt Dom) * 1 * CFC.sqrt Dom :=
        star_left_conjugate_le_conjugate (contraction_conjTranspose _ hContr) (CFC.sqrt Dom)
    _ = Dom := by rw [mul_one, hSs, hSS]

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

/-- If `B ≤ D + ε • 1` for all `ε > 0`, and both `B` and `D` are Hermitian, then `B ≤ D`.
This encodes the topological closedness of the PSD cone. -/
private lemma le_of_forall_le_add_pos_smul_one (B D : Mat)
    (hBH : B.IsHermitian) (hDH : D.IsHermitian)
    (h : ∀ ε : ℝ, 0 < ε → B ≤ D + (ε : ℂ) • (1 : Mat)) :
    B ≤ D := by
  rw [Matrix.le_iff]
  have : (D - B).IsHermitian := hDH.sub hBH
  suffices h0 : (0 : Mat) ≤ D - B by simpa using h0
  have hClosed : IsClosed {a : Mat | 0 ≤ a} := CStarAlgebra.isClosed_nonneg
  let g : ℕ → Mat := fun n => (D - B) + ((1 / (n : ℝ)) : ℝ) • (1 : Mat)
  apply hClosed.mem_of_tendsto (b := Filter.atTop) (f := g)
  · show Filter.Tendsto g Filter.atTop (nhds (D - B))
    have : Filter.Tendsto (fun n : ℕ => ((1 / (n : ℝ)) : ℝ) • (1 : Mat))
        Filter.atTop (nhds (0 : Mat)) := by
      rw [show (0 : Mat) = (0 : ℝ) • (1 : Mat) from by simp]
      exact (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).smul_const (1 : Mat)
    simpa [g, add_zero] using this.const_add (D - B)
  · rw [Filter.eventually_atTop]
    refine ⟨1, ?_⟩
    intro n hn
    show g n ∈ {a | 0 ≤ a}
    change 0 ≤ g n
    have h_smul : ((1 / (n : ℝ)) : ℝ) • (1 : Mat) = ((1 / (n : ℝ) : ℝ) : ℂ) • (1 : Mat) := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    have h_eq : g n = (D + ((1 / (n : ℝ) : ℝ) : ℂ) • 1) - B := by
      change (D - B) + ((1 / (n : ℝ)) : ℝ) • 1 = _
      rw [h_smul]
      abel
    rw [h_eq, show (0 : Mat) ≤ _ ↔ (D + (((1 / (n : ℝ) : ℝ) : ℂ)) • 1 - B).PosSemidef from by
      rw [Matrix.le_iff]
      simp, ← Matrix.le_iff]
    exact h (1 / (n : ℝ)) (by positivity)

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

/-- Linear-map wrapper for the adjoint Kraus map.

This is convenient for reusing the generic positivity/monotonicity API from
`PositiveMapProperties`. -/
noncomputable def krausAdjointMapLinear (K : Fin d → Mat) : Mat →ₗ[ℂ] Mat where
  toFun := krausAdjointMap K
  map_add' := by
    intro X Y
    simp [krausAdjointMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c X
    simp [krausAdjointMap, Finset.smul_sum, Matrix.mul_assoc]

/-- The adjoint Kraus map is positive. -/
theorem krausAdjointMapLinear_isPositiveMap (K : Fin d → Mat) :
    IsPositiveMap (krausAdjointMapLinear (d := d) (D := D) K) := by
  intro X hX
  classical
  simpa [krausAdjointMapLinear, krausAdjointMap, Matrix.mul_assoc] using
    Matrix.posSemidef_sum (s := Finset.univ) (x := fun i => (K i)ᴴ * X * K i)
      (fun i _ => by
        simpa [Matrix.mul_assoc] using hX.mul_mul_conjTranspose_same (B := (K i)ᴴ))

set_option maxHeartbeats 12800000 in
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
    (Matrix.isHermitian_mul_conjTranspose_self A) hDomPos.isHermitian
  intro ε hε
  have hPD : (Dom + (ε : ℂ) • (1 : Mat)).PosDef :=
    posDef_add_pos_smul_one Dom hDomPos ε hε
  have hComm' : Commute (Dom + (ε : ℂ) • (1 : Mat)) A := by
    exact hComm.add_left (by
      rw [Commute, SemiconjBy, smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
  have hDom' : Aᴴ * A ≤ Dom + (ε : ℂ) • (1 : Mat) :=
    hDom.trans (le_add_of_nonneg_right (by
      rw [Matrix.le_iff]; simpa using (Matrix.PosSemidef.one (n := Fin D) (R := ℂ)).smul
        (show (0 : ℝ) ≤ ε from le_of_lt hε)))
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
  have hKSLeft' : (krausAdjointMap K A)ᴴ * krausAdjointMap K A ≤ krausAdjointMap K (Aᴴ * A) := by
    rw [Matrix.le_iff]
    exact kadison_schwarz_adjoint K h_tp A
  have hKSLeft : krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤ krausAdjointMap K (Aᴴ * A) := by
    simpa [krausAdjointMap_conjTranspose] using hKSLeft'
  have hDomLeftMap : krausAdjointMap K (Aᴴ * A) ≤ krausAdjointMap K Dom := by
    simpa [T] using hPosT.map_le_map hDomLeft
  have hKSRight' : (krausAdjointMap K (Aᴴ))ᴴ * krausAdjointMap K (Aᴴ) ≤
      krausAdjointMap K (A * Aᴴ) := by
    simpa [conjTranspose_conjTranspose] using
      (show (krausAdjointMap K (Aᴴ))ᴴ * krausAdjointMap K (Aᴴ) ≤ krausAdjointMap K ((Aᴴ)ᴴ * Aᴴ) from by
        rw [Matrix.le_iff]
        exact kadison_schwarz_adjoint K h_tp (Aᴴ))
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

/-- Wolf Thm. 5.6: Schwarz inequality for commuting dominant operators.

The proof follows Wolf's normal-block-matrix construction.  One first proves the
auxiliary order lemma `commuting_dominant_right_bound`, then builds a normal block
matrix `N` with `θ(N) = A` and `θ(Nᴴ * N) = D`, and finally applies Wolf Prop. 5.1
through the composed map `T ∘ θ`. -/
theorem schwarz_inequality_commuting_dominant_operator
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    T (Aᴴ) * T A ≤ T Dom ∧ T A * T (Aᴴ) ≤ T Dom := by
  sorry

end KadisonSchwarz
