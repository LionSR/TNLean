/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSplitting

/-!
# Homogeneous birth and death

Lemma 6.5 of the polynomial-PEPS manuscript changes the owner of a set `T` of raw sites of an
encoded frame from `P∘` to `Q∘`, keeping every hole, its encoding and its tag owner. With
`E = {x : owner x ≠ P∘} ∪ H⁺(F)` and `U = Λ ∖ (T ∪ E)`, the splitting consequence of Lemma 6.4
gives an isometry `V` on `U` and unit vectors `s`, `s'` with `‖𝒱 Ω - s ⊗ s'‖ ≤ L^{-30}` when
`I_Ω(T:E) ≤ L^{-60}`, where `𝒱 = 1_{TE} ⊗ V`. The canonical map of the birth is
`B = 𝒱ᴴ (|s⟩⟨s|_{T B_T} ⊗ 1_{E B_E}) 𝒱`.

This file defines `B` for abstract finite systems, proves that it is a Hermitian contraction with
`‖(B - 1) ψ‖ ≤ ‖𝒱 ψ - s ⊗ s'‖`, factors it as an effect followed by a source of the single
normalized pair vector `s`, and shows that it acts as the identity on `E`. On a sheet it commutes
with every hole encoder supported in `E`, so the same bound holds for the encoded reference
vectors.

## Main definitions

* `EncodedFrame.pairSource`: the map inserting the normalized vector `s` on `T × B_T`.
* `EncodedFrame.birthKernel`, `EncodedFrame.birthEffect`: the map `⟨s| (1_T ⊗ V)` on the
  registers of `T ∪ U`, and its extension by the identity on `E`.
* `EncodedFrame.birthOp`: the canonical map `B` (`eq:birth-map`).
* `EncodedFrame.Frame.changeOwner`, `EncodedFrame.Frame.birthEnv`: the frame after a change of
  the owner of `T`, and the set `E` of `eq:birth-partition`.

## Main results

* `EncodedFrame.birthOp_eq`: `B = 𝒱ᴴ (S Sᴴ) 𝒱`, with `S Sᴴ = |s⟩⟨s|_{T B_T} ⊗ 1_{E B_E}`.
* `EncodedFrame.norm_birthOp_le_one`, `EncodedFrame.birthOp_isHermitian`,
  `EncodedFrame.norm_act_birthOp_sub_le`.
* `EncodedFrame.Frame.birth`, `EncodedFrame.Frame.death`: Lemma 6.5 `lem:birth`.

## Scope

**Scope restriction (monomial structure):** Lemma 6.5 asserts that the birth and the death are
bounded changes in the sense of Theorem 5.2, that is, that they have expansions into allowed
monomials (one normalized pair source, respectively one pair effect, and private contractions)
involving only `P∘` and `Q∘`. Here the canonical map is factored as `B = (𝒱ᴴ S) (Sᴴ 𝒱)`, with
`S` the source of the single normalized pair vector `s`, every other register it acts on lies in
`T ∪ U`, whose old owner is `P∘` and whose new owner is `P∘` or `Q∘`, and `B` acts as the identity
on `E` and on all tags. Reading this factorization as an allowed monomial of Theorem 5.2 needs a
model of operators placed on parties, which the library does not yet have. Documented in
`docs/paper-gaps/polypeps_ownership_change_monomials.tex`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.5 `lem:birth` and its proof,
  `05-frames.tex`, lines 396–456.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

/-! ### The canonical map for abstract systems -/

section Abstract

variable {T E U BT BE : Type*} [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
  [Fintype U] [DecidableEq U] [Fintype BT] [DecidableEq BT] [Fintype BE] [DecidableEq BE]

/-- The map `|s⟩_{T B_T} ⊗ 1_{E B_E}` inserting the vector `s` on `T × B_T`, with the output
coordinates grouped as `(T × E) × (B_T × B_E)`. For a unit vector `s` it is a normalized pair
source.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 416–419. -/
def pairSource (s : T × BT → ℂ) : Matrix ((T × E) × (BT × BE)) (E × BE) ℂ :=
  of fun x y => if (x.1.2, x.2.2) = y then s (x.1.1, x.2.1) else 0

omit [DecidableEq T] [DecidableEq BT] in
theorem pairSource_conjTranspose_mul_self {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) :
    (pairSource (E := E) (BE := BE) s)ᴴ * pairSource (E := E) (BE := BE) s = 1 := by
  ext ⟨e, b⟩ ⟨e', b'⟩
  simp only [mul_apply, conjTranspose_apply, pairSource, of_apply, Fintype.sum_prod_type]
  simp only [apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul, mul_ite, mul_zero, one_apply,
    Prod.mk.injEq]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset E)) (t := (Finset.univ : Finset BT))]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  split_ifs <;> simp_all [dotProduct, Fintype.sum_prod_type]

omit [Fintype T] [DecidableEq T] [Fintype BT] [DecidableEq BT] in
/-- `S s' = s ⊗ s'`. -/
theorem pairSource_mulVec (s : T × BT → ℂ) (s' : E × BE → ℂ) :
    pairSource s *ᵥ s' = tensorPurification s s' := by
  ext x
  simp [pairSource, mulVec, dotProduct, tensorPurification, ite_mul]

omit [DecidableEq T] [DecidableEq BT] in
/-- `Sᴴ (s ⊗ s') = s'` for a unit vector `s`. -/
theorem pairSource_conjTranspose_mulVec_tensorPurification {s : T × BT → ℂ}
    (hs : star s ⬝ᵥ s = 1) (s' : E × BE → ℂ) :
    (pairSource s)ᴴ *ᵥ tensorPurification s s' = s' := by
  rw [← pairSource_mulVec, mulVec_mulVec, pairSource_conjTranspose_mul_self hs, one_mulVec]

omit [Fintype T] [DecidableEq T] [Fintype BT] [DecidableEq BT] in
/-- `S Sᴴ = |s⟩⟨s|_{T B_T} ⊗ 1_{E B_E}`: the middle projector of `eq:birth-map`. -/
theorem pairSource_mul_conjTranspose_apply (s : T × BT → ℂ)
    (x x' : (T × E) × (BT × BE)) :
    (pairSource (E := E) (BE := BE) s * (pairSource (E := E) (BE := BE) s)ᴴ) x x' =
      if (x.1.2, x.2.2) = (x'.1.2, x'.2.2) then
        s (x.1.1, x.2.1) * star (s (x'.1.1, x'.2.1)) else 0 := by
  simp only [mul_apply, conjTranspose_apply, pairSource, of_apply]
  rw [Finset.sum_eq_single (x.1.2, x.2.2) (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
  by_cases h : (x.1.2, x.2.2) = (x'.1.2, x'.2.2)
  · simp [h]
  · have h' : ¬(x'.1.2 = x.1.2 ∧ x'.2.2 = x.2.2) := fun ⟨h1, h2⟩ => h (by rw [h1, h2])
    simp [h, h']

/-- The map `⟨s|_{T B_T} (1_T ⊗ V)` from the registers of `T ∪ U` to `B_E`: apply `V` on `U`
and contract `T` and `B_T` with `⟨s|`.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 416–418. -/
def birthKernel (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) : Matrix BE (T × U) ℂ :=
  of fun b tu => ∑ bt, star (s (tu.1, bt)) * V (bt, b) tu.2

/-- The effect `Sᴴ 𝒱 = (⟨s|_{T B_T} ⊗ 1_{E B_E}) (1_{TE} ⊗ V)`. -/
def birthEffect (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    Matrix (E × BE) ((T × E) × U) ℂ :=
  (pairSource s)ᴴ * ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V)

/-- **The canonical map of a birth (`eq:birth-map`).**
`B = 𝒱ᴴ (|s⟩⟨s|_{T B_T} ⊗ 1_{E B_E}) 𝒱`, written as `(Sᴴ 𝒱)ᴴ (Sᴴ 𝒱)`.

Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 420–426. -/
def birthOp (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    Matrix ((T × E) × U) ((T × E) × U) ℂ :=
  (birthEffect V s)ᴴ * birthEffect V s

omit [Fintype U] [DecidableEq U] [DecidableEq BT] in
/-- **`eq:birth-map`.** `B = 𝒱ᴴ (S Sᴴ) 𝒱` with `𝒱 = 1_{TE} ⊗ V`. -/
theorem birthOp_eq (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    birthOp V s = ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V)ᴴ *
      (pairSource s * (pairSource s)ᴴ) * ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) := by
  rw [birthOp, birthEffect, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

omit [Fintype U] [DecidableEq U] [DecidableEq BT] in
/-- The canonical map is Hermitian. -/
theorem birthOp_isHermitian (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    (birthOp (E := E) V s).IsHermitian := by
  rw [IsHermitian, birthOp, conjTranspose_mul, conjTranspose_conjTranspose]

omit [DecidableEq T] [DecidableEq BT] in
theorem norm_pairSource_le_one {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) :
    ‖pairSource (E := E) (BE := BE) s‖ ≤ 1 :=
  l2_opNorm_le_one_of_conjTranspose_mul_self_le_one (by
    rw [pairSource_conjTranspose_mul_self hs]; exact (IsStarProjection.one _).norm_le)

omit [DecidableEq BT] [DecidableEq BE] in
theorem norm_one_kronecker_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry) :
    ‖(1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V‖ ≤ 1 :=
  l2_opNorm_le_one_of_conjTranspose_mul_self_le_one (by
    rw [IsIsometry.kronecker (1 : Matrix (T × E) (T × E) ℂ) V (by simp [IsIsometry]) hV]
    exact (IsStarProjection.one _).norm_le)

omit [DecidableEq BT] in
theorem norm_birthEffect_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) : ‖birthEffect (E := E) V s‖ ≤ 1 := by
  classical
  have h := norm_pairSource_le_one (E := E) (BE := BE) hs
  rw [← l2_opNorm_conjTranspose] at h
  exact l2_opNorm_mul_le_one h (norm_one_kronecker_le_one hV)

omit [DecidableEq BT] in
/-- **The canonical map is a contraction** (`05-frames.tex`, line 427). -/
theorem norm_birthOp_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) : ‖birthOp (E := E) V s‖ ≤ 1 := by
  classical
  have h := norm_birthEffect_le_one (E := E) hV hs
  have h' := h
  rw [← l2_opNorm_conjTranspose] at h'
  exact l2_opNorm_mul_le_one h' h

omit [DecidableEq BT] in
/-- **Reference error of the canonical map** (`05-frames.tex`, lines 427–433). For an isometry
`V` and unit vectors `s`, and any `s'`, `‖(B - 1) ψ‖ ≤ ‖𝒱 ψ - s ⊗ s'‖`: with `Pr = S Sᴴ`,
`(B - 1) ψ = 𝒱ᴴ (Pr - 1) (𝒱 ψ - s ⊗ s')` because `Pr (s ⊗ s') = s ⊗ s'`. -/
theorem norm_act_birthOp_sub_le {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) (s' : E × BE → ℂ)
    (ψ : EuclideanSpace ℂ ((T × E) × U)) :
    ‖act (birthOp V s) ψ - ψ‖ ≤
      ‖act ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) ψ - WithLp.toLp 2 (tensorPurification s s')‖ := by
  classical
  set 𝒱 := (1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V
  set Pr := pairSource (E := E) (BE := BE) s * (pairSource s)ᴴ
  set ζ : EuclideanSpace ℂ ((T × E) × (BT × BE)) := WithLp.toLp 2 (tensorPurification s s')
  have hiso : 𝒱ᴴ * 𝒱 = 1 :=
    IsIsometry.kronecker (1 : Matrix (T × E) (T × E) ℂ) V (by simp [IsIsometry]) hV
  have hζ : act Pr ζ = ζ := by
    simp only [act, Pr, ζ, ← mulVec_mulVec, pairSource_conjTranspose_mulVec_tensorPurification hs,
      pairSource_mulVec]
  have hproj : IsStarProjection Pr := by
    refine ⟨?_, ?_⟩
    · change Pr * Pr = Pr
      simp only [Pr, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (pairSource s)ᴴ, pairSource_conjTranspose_mul_self hs, Matrix.one_mul]
    · change star Pr = Pr
      simp only [Pr, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have hnorm : ‖Pr - 1‖ ≤ 1 := by
    rw [← norm_neg, neg_sub]
    exact hproj.one_sub.norm_le
  have hV' : ‖𝒱ᴴ‖ ≤ 1 := by
    rw [l2_opNorm_conjTranspose]
    exact norm_one_kronecker_le_one hV
  have key : act (birthOp V s) ψ - ψ = act 𝒱ᴴ (act (Pr - 1) (act 𝒱 ψ - ζ)) := by
    rw [act_sub_right, act_sub, act_sub, hζ, act_one, act_one, sub_self, sub_zero, act_sub_right,
      ← act_mul, ← act_mul, birthOp_eq, ← act_mul, hiso, act_one]
  rw [key]
  refine (norm_act_le_of_norm_le_one hV' _).trans ?_
  exact norm_act_le_of_norm_le_one hnorm _

/-- The coordinates `((t, e), u) ↦ (e, (t, u))`, separating `E` from `T` and `U`. -/
def teuShuffle (T E U : Type*) : (T × E) × U ≃ E × (T × U) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun y := ((y.2.1, y.1), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype U] [DecidableEq U] [DecidableEq BT] in
/-- The effect `Sᴴ 𝒱` is the identity on `E` tensored with the kernel `⟨s| (1_T ⊗ V)` on the
registers of `T ∪ U`. -/
theorem birthEffect_eq_submatrix (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    birthEffect (E := E) V s =
      ((1 : Matrix E E ℂ) ⊗ₖ birthKernel V s).submatrix id (teuShuffle T E U) := by
  ext ⟨e₀, b⟩ ⟨⟨t, e⟩, u⟩
  simp only [birthEffect, birthKernel, pairSource, mul_apply, conjTranspose_apply, of_apply,
    kroneckerMap_apply, one_apply, submatrix_apply, id, teuShuffle, Equiv.coe_fn_mk,
    Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul, one_mul, ite_and]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset E)) (t := (Finset.univ : Finset BT))]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  by_cases he : e = e₀
  · subst he; simp
  · simp [Ne.symm he]

omit [Fintype U] [DecidableEq U] [DecidableEq BT] in
/-- **The canonical map acts as the identity on `E`.** In the coordinates `(e, (t, u))`,
`B = 1_E ⊗ (Kᴴ K)` with `K = ⟨s| (1_T ⊗ V)` the kernel on the registers of `T ∪ U`.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 434–437. -/
theorem birthOp_eq_submatrix (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    birthOp (E := E) V s =
      ((1 : Matrix E E ℂ) ⊗ₖ ((birthKernel V s)ᴴ * birthKernel V s)).submatrix
        (teuShuffle T E U) (teuShuffle T E U) := by
  rw [birthOp, birthEffect_eq_submatrix, conjTranspose_submatrix,
    ← submatrix_mul _ _ _ _ _ Function.bijective_id, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul]

omit [Fintype T] [Fintype E] [DecidableEq E] [Fintype U] in
/-- An operator acting on `E` alone, `(1_T ⊗ R) ⊗ 1_U`, in the coordinates `(e, (t, u))`. -/
theorem one_kronecker_kronecker_one_eq_submatrix (R : Matrix E E ℂ) :
    ((1 : Matrix T T ℂ) ⊗ₖ R) ⊗ₖ (1 : Matrix U U ℂ) =
      (R ⊗ₖ (1 : Matrix (T × U) (T × U) ℂ)).submatrix (teuShuffle T E U) (teuShuffle T E U) := by
  ext ⟨⟨t, e⟩, u⟩ ⟨⟨t', e'⟩, u'⟩
  simp only [kroneckerMap_apply, one_apply, submatrix_apply, teuShuffle, Equiv.coe_fn_mk,
    Prod.mk.injEq]
  by_cases ht : t = t' <;> by_cases hu : u = u' <;> simp [ht, hu]

omit [DecidableEq BT] in
/-- The canonical map commutes with every operator acting on `E` alone. -/
theorem commute_birthOp (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) (R : Matrix E E ℂ) :
    Commute (((1 : Matrix T T ℂ) ⊗ₖ R) ⊗ₖ (1 : Matrix U U ℂ)) (birthOp V s) := by
  rw [one_kronecker_kronecker_one_eq_submatrix, birthOp_eq_submatrix]
  refine Commute.submatrix_equiv ?_ _
  change _ * _ = _ * _
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one]

end Abstract

/-! ### The canonical map on a sheet -/

section Sheet

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {T E : Finset ι} (h : Disjoint T E)

/-- The canonical map `B = 𝒱ᴴ (|s⟩⟨s|_{T B_T} ⊗ 1_{E B_E}) 𝒱` of splitting data, on the raw
registers of the sheet (`eq:birth-map`).

Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 414–426. -/
def sheetBirthOp (σ : SplittingData q T E) : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  (birthOp (E := E → Fin q) σ.V σ.s).submatrix (threeSplit q T E h) (threeSplit q T E h)

theorem sheetBirthOp_isHermitian (σ : SplittingData q T E) : (sheetBirthOp h σ).IsHermitian :=
  (birthOp_isHermitian σ.V σ.s).submatrix _

theorem norm_sheetBirthOp_le_one (σ : SplittingData q T E) : ‖sheetBirthOp h σ‖ ≤ 1 :=
  (norm_submatrix_equiv_le _ _).trans (norm_birthOp_le_one σ.isIsometry σ.star_s)

/-- `‖(B - 1) Ω‖` is at most the splitting error `‖𝒱 Ω - s ⊗ s'‖`
(`05-frames.tex`, lines 427–433). -/
theorem norm_act_sheetBirthOp_sub_le (σ : SplittingData q T E)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ‖act (sheetBirthOp h σ) Ω - Ω‖ ≤ σ.error h Ω := by
  rw [sheetBirthOp, norm_act_submatrix_sub]
  exact norm_act_birthOp_sub_le σ.isIsometry σ.star_s σ.s' _

/-- The canonical map commutes with every operator acting on a subset of `E`; in particular it
commutes with every hole encoder supported in `E` (`05-frames.tex`, lines 434–437). -/
theorem commute_sheetBirthOp (σ : SplittingData q T E) {D : Set ι} (hD : D ⊆ E)
    {R : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hR : R ∈ supportedOperators q D) :
    Commute (sheetBirthOp h σ) R := by
  obtain ⟨R', hR'⟩ := exists_threeSplit_eq_one_kronecker_kronecker_one h hD hR
  have hR₀ := submatrix_symm_submatrix R (threeSplit q T E h).symm
  rw [Equiv.symm_symm] at hR₀
  rw [← hR₀, hR']
  exact Commute.submatrix_equiv (Commute.symm (commute_birthOp σ.V σ.s R')) _

end Sheet

/-! ### Birth and death in an encoded frame -/

section FrameOwnership

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type*}

/-- The frame obtained by changing the owner of the raw registers of `T` to `Q`, keeping every
hole, its encoding and its tag owner. -/
abbrev Frame.changeOwner (F : Frame pos q Party) (T : Finset ι) (Q : Party) :
    Frame pos q Party where
  owner x := if x ∈ T then Q else F.owner x
  holes := F.holes
  disjoint := F.disjoint

open Classical in
/-- The set `E = {x : owner x ≠ P∘} ∪ H⁺(F)` of `eq:birth-partition`. It contains the whole outer
footprint of every hole, even where the raw owner is `P∘`.

Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 400–405 and 454–456. -/
def Frame.birthEnv (F : Frame pos q Party) (P : Party) : Finset ι :=
  Finset.univ.filter fun x => F.owner x ≠ P ∨ x ∈ F.outerHoles

namespace Frame

variable (F : Frame pos q Party) {T : Finset ι} {P Q : Party}

theorem mem_birthEnv {x : ι} : x ∈ F.birthEnv P ↔ F.owner x ≠ P ∨ x ∈ F.outerHoles := by
  classical
  unfold birthEnv
  simp

theorem outerHoles_subset_birthEnv : F.outerHoles ⊆ (F.birthEnv P : Set ι) := fun _ hx =>
  (F.mem_birthEnv).mpr (Or.inr hx)

/-- Every register outside `E` is owned by `P∘`. -/
theorem owner_eq_of_notMem_birthEnv {x : ι} (hx : x ∉ F.birthEnv P) : F.owner x = P := by
  by_contra h
  exact hx ((F.mem_birthEnv).mpr (Or.inl h))

/-- After the change of owner, every register outside `E` is owned by `P∘` or `Q∘`. -/
theorem changeOwner_owner_of_notMem_birthEnv {x : ι} (hx : x ∉ F.birthEnv P) :
    (F.changeOwner T Q).owner x = P ∨ (F.changeOwner T Q).owner x = Q := by
  change (if x ∈ T then Q else F.owner x) = P ∨ (if x ∈ T then Q else F.owner x) = Q
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl (F.owner_eq_of_notMem_birthEnv hx)

/-- `T` and `E` are disjoint when `T` is owned by `P∘` and avoids every outer hole footprint. -/
theorem disjoint_birthEnv (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) : Disjoint T (F.birthEnv P) := by
  rw [Finset.disjoint_left]
  intro x hxT hxE
  rcases (F.mem_birthEnv).mp hxE with h | h
  · exact h (hTP x hxT)
  · exact Set.disjoint_left.mp hTH hxT h

/-- **Lemma 6.5 (homogeneous birth).** In an encoded frame `F`, let `T` be a set of raw sites
owned by `P∘` and disjoint from every outer hole footprint, and let `E` and `U` be as in
`eq:birth-partition`. If `I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data
whose canonical map `B` is a Hermitian contraction, acting as the identity on `E` and on the
tags, with `(1 ⊗ B) K_F = K_{F'} B` for the frame `F'` in which `T` is owned by `Q∘`, and
`‖(1 ⊗ B) Ω_F - Ω_{F'}‖ ≤ L^{-30}`. Every register `B` acts on lies outside `E`, so it is owned
by `P∘` before the birth and by `P∘` or `Q∘` after it (`owner_eq_of_notMem_birthEnv`,
`changeOwner_owner_of_notMem_birthEnv`).

The frames `F` and `F'` differ only in raw owners, and the encoding and the reference vector do
not depend on raw owners (Definition 6.1, `05-frames.tex`, lines 71–82), so `K_{F'} = K_F` and
`Ω_{F'} = Ω_F`; the identity `(1 ⊗ B) K_F = K_{F'} B` says that `B` commutes with the encoding.
The change of owner from `P∘` to `Q∘` is the content of the bounded-change clause, which is not
formalized (see the module docstring).

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–407; proof lines
413–437. -/
theorem birth [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ} (hL : 0 < L)
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      (sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ).IsHermitian ∧
      ‖sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ‖ ≤ 1 ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * F.encoder =
        (F.changeOwner T Q).encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) (F.refVec Ω) -
        (F.changeOwner T Q).refVec Ω‖ ≤ L ^ (-30 : ℤ) := by
  set hTE := F.disjoint_birthEnv hTP hTH
  obtain ⟨σ, hσ⟩ := exists_sheetSplitting_zpow hTE hΩ hL hI
  have hcomm : ∀ t, Commute (sheetBirthOp hTE σ) (rawProd F.holes t) := fun t =>
    commute_sheetBirthOp hTE σ F.outerHoles_subset_birthEnv
      (rawProd_mem_supportedOperators F.holes t)
  refine ⟨σ, hσ, sheetBirthOp_isHermitian hTE σ, norm_sheetBirthOp_le_one hTE σ,
    one_kronecker_mul_frameEncoder hcomm, ?_⟩
  exact (norm_act_one_kronecker_refVec_sub_le F hcomm Ω).trans
    ((norm_act_sheetBirthOp_sub_le hTE σ Ω).trans hσ)

/-- **Lemma 6.5 (homogeneous death).** The reversed operation. Let `F` be the frame *after* the
death, in which `T` is owned by `P∘` and avoids every outer hole footprint, and let the frame
before the death be `F` with `T` owned by `Q∘`. If `I_Ω(T:E) ≤ L^{-60}` for `E` computed in `F`,
the same canonical map `B = Bᴴ`, now with the reverse input and output ownership, satisfies
`(1 ⊗ B) K_{F_before} = K_F B` and `‖(1 ⊗ B) Ω_{F_before} - Ω_F‖ ≤ L^{-30}`.

Since the encoding and the reference vector do not depend on raw owners, this is the statement of
`birth` read in the frame after the death; its content beyond `birth` is that the hypotheses,
and the set `E`, are those of the frame after the death (`05-frames.tex`, lines 407–410).

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 407–410; proof lines
439–446. -/
theorem death [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ} (hL : 0 < L)
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      (sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ).IsHermitian ∧
      ‖sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ‖ ≤ 1 ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * (F.changeOwner T Q).encoder =
        F.encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) ((F.changeOwner T Q).refVec Ω) -
        F.refVec Ω‖ ≤ L ^ (-30 : ℤ) :=
  F.birth (Q := Q) hTP hTH hΩ hL hI

end Frame

end FrameOwnership

end TNLean.PEPS.EncodedFrame
