/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixKroneckerContraction
import TNLean.PEPS.Approximation.HomogeneousOwnership

/-!
# Swapping two sheets and the buffer correction

The proof of Lemma 6.6 of the polynomial-PEPS manuscript works on two copies of a sheet. With
splitting data for disjoint sets `T` and `E` (Lemma 6.4), an isometry `V` from the configurations
of `U = Λ ∖ (T ∪ E)` to `B_T ⊗ B_E` and unit vectors `s`, `s'`, the *buffer correction*
`D_U = (V^{⊗2})ᴴ F_{B_T} V^{⊗2}` acts on the two copies of `U`, where `F_{B_T}` swaps the two
copies of `B_T`. Composed with the swap `F_T` of the two sheets at `T`, it is
`D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T} 𝒱^{⊗2}` with `𝒱 = 1_{TE} ⊗ V`, and on the square `ω^{⊗2}` of a
unit vector it moves by at most `4 ‖𝒱 ω - s ⊗ s'‖`, since `F_{T B_T}` fixes `(s ⊗ s')^{⊗2}`.

## Main definitions

* `EncodedFrame.bufferCorrection`: `D_U` for abstract finite systems.
* `EncodedFrame.sheetSwap`, `EncodedFrame.sheetSwapOp`: the unitary `F_S` swapping the two raw
  sheets at the sites of `S`.
* `EncodedFrame.sheetBufferCorrection`: `D_U` on the raw registers of two sheets.

## Main results

* `EncodedFrame.bufferCorrection_mul_tSwap`: `D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T} 𝒱^{⊗2}`
  (`eq:exchange-net-map`).
* `EncodedFrame.norm_act_bufferCorrection_mul_tSwap_sub_le`: `‖D_U F_T ω^{⊗2} - ω^{⊗2}‖ ≤ 4δ`.
* `EncodedFrame.sheetSwapOp_mul_sheetSwapOp`: `F_A F_Y = F_T` for `Y = T ⊔ A`.
* `EncodedFrame.commute_sheetSwapOp_kronecker`, `EncodedFrame.commute_sheetBufferCorrection`:
  the two corrections commute with products of operators acting away from them.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.6 `lem:exchange`,
  `05-frames.tex`, lines 481–561.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open EuclideanSpace (vecKron)
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

section Kron

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']

/-- A Kronecker product acts factorwise on a product vector: `(A ⊗ B)(x ⊗ y) = (A x) ⊗ (B y)`. -/
omit [Fintype m'] [Fintype n'] in
theorem act_kronecker_vecKron (A : Matrix m' m ℂ) (B : Matrix n' n ℂ) (x : EuclideanSpace ℂ m)
    (y : EuclideanSpace ℂ n) : act (A ⊗ₖ B) (vecKron x y) = vecKron (act A x) (act B y) := by
  ext ⟨i, j⟩
  simp only [vecKron, mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Kron

/-! ### The buffer correction for abstract systems -/

section Buffer

variable {T E U BT BE : Type*} [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
  [Fintype U] [DecidableEq U] [Fintype BT] [DecidableEq BT] [Fintype BE] [DecidableEq BE]

/-- The bijection of two copies of `T × E` exchanging their `T`-components. -/
def tSwap (T E : Type*) : Equiv.Perm ((T × E) × (T × E)) where
  toFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  invFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bijection of two copies of `(T × E) × U` exchanging their `T`-components: the swap
`F_T` of the two sheets at `T`, in the coordinates `((t, e), u)`. -/
def tSwapW (T E U : Type*) : Equiv.Perm (((T × E) × U) × ((T × E) × U)) where
  toFun x := (((x.2.1.1, x.1.1.2), x.1.2), ((x.1.1.1, x.2.1.2), x.2.2))
  invFun x := (((x.2.1.1, x.1.1.2), x.1.2), ((x.1.1.1, x.2.1.2), x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bijection of two copies of `B_T × B_E` exchanging their `B_T`-components. -/
def bufferSwap (BT BE : Type*) : Equiv.Perm ((BT × BE) × (BT × BE)) := tSwap BT BE

/-- The bijection of two copies of `(T × E) × (B_T × B_E)` exchanging their `T`- and
`B_T`-components: the swap `F_{T B_T}`. -/
def tbSwap (T E BT BE : Type*) :
    Equiv.Perm (((T × E) × (BT × BE)) × ((T × E) × (BT × BE))) where
  toFun x := (((x.2.1.1, x.1.1.2), (x.2.2.1, x.1.2.2)), ((x.1.1.1, x.2.1.2), (x.1.2.1, x.2.2.2)))
  invFun x := (((x.2.1.1, x.1.1.2), (x.2.2.1, x.1.2.2)), ((x.1.1.1, x.2.1.2), (x.1.2.1, x.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The buffer correction `D_U = (V^{⊗2})ᴴ F_{B_T} V^{⊗2}`** on the two copies of `U`
(`eq:exchange-buffer-correction`), as an operator on two copies of `(T × E) × U` acting as the
identity on the copies of `T × E`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 503–510. -/
def bufferCorrection (V : Matrix (BT × BE) U ℂ) :
    Matrix (((T × E) × U) × ((T × E) × U)) (((T × E) × U) × ((T × E) × U)) ℂ :=
  ((1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) ⊗ₖ
      ((V ⊗ₖ V)ᴴ * ((bufferSwap BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ) * (V ⊗ₖ V))).submatrix
    (Equiv.prodProdProdComm (T × E) U (T × E) U) (Equiv.prodProdProdComm (T × E) U (T × E) U)

omit [Fintype T] [Fintype E] [Fintype U] in
theorem tSwapW_toMatrix :
    ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ) =
      (((tSwap T E).toPEquiv.toMatrix : Matrix _ _ ℂ) ⊗ₖ
          (1 : Matrix (U × U) (U × U) ℂ)).submatrix
        (Equiv.prodProdProdComm (T × E) U (T × E) U)
        (Equiv.prodProdProdComm (T × E) U (T × E) U) := by
  rw [← PEquiv.toMatrix_refl, ← Equiv.toPEquiv_refl, ← toMatrix_toPEquiv_prodCongr,
    toMatrix_toPEquiv_submatrix]
  rfl

omit [Fintype T] [Fintype E] [Fintype BT] [Fintype BE] in
theorem tbSwap_toMatrix :
    ((tbSwap T E BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ) =
      (((tSwap T E).toPEquiv.toMatrix : Matrix _ _ ℂ) ⊗ₖ
          ((bufferSwap BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ)).submatrix
        (Equiv.prodProdProdComm (T × E) (BT × BE) (T × E) (BT × BE))
        (Equiv.prodProdProdComm (T × E) (BT × BE) (T × E) (BT × BE)) := by
  rw [← toMatrix_toPEquiv_prodCongr, toMatrix_toPEquiv_submatrix]
  rfl

/-- **The net map (`eq:exchange-net-map`).** `D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T} 𝒱^{⊗2}` with
`𝒱 = 1_{TE} ⊗ V`: `F_T` acts outside `U` and commutes through the isometries.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 516–526. -/
theorem bufferCorrection_mul_tSwap (V : Matrix (BT × BE) U ℂ) :
    bufferCorrection (T := T) (E := E) V * ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ) =
      (((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) ⊗ₖ ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V))ᴴ *
        ((tbSwap T E BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ) *
        (((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) ⊗ₖ ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V)) := by
  set F₀ : Matrix ((BT × BE) × (BT × BE)) ((BT × BE) × (BT × BE)) ℂ :=
    (bufferSwap BT BE).toPEquiv.toMatrix
  set G : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ := (tSwap T E).toPEquiv.toMatrix
  have hin : ((1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) ⊗ₖ
        ((V ⊗ₖ V)ᴴ * F₀ * (V ⊗ₖ V))) * (G ⊗ₖ (1 : Matrix (U × U) (U × U) ℂ)) =
      ((1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) ⊗ₖ (V ⊗ₖ V))ᴴ * (G ⊗ₖ F₀) *
        ((1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) ⊗ₖ (V ⊗ₖ V)) := by
    rw [conjTranspose_kronecker (1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) (V ⊗ₖ V),
      conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
  rw [bufferCorrection, tSwapW_toMatrix, tbSwap_toMatrix, kronecker_kronecker_eq_submatrix,
    conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_mul_equiv,
    one_kronecker_one, hin]

theorem norm_bufferCorrection_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry) :
    ‖bufferCorrection (T := T) (E := E) V‖ ≤ 1 := by
  refine (norm_submatrix_equiv_le _ _).trans ((l2_opNorm_one_kronecker_le _).trans ?_)
  have hVV : ‖V ⊗ₖ V‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self_le_one (by
      rw [IsIsometry.kronecker V V hV hV]; exact (IsStarProjection.one _).norm_le)
  have hVV' := hVV
  rw [← l2_opNorm_conjTranspose] at hVV'
  exact l2_opNorm_mul_le_one (l2_opNorm_mul_le_one hVV' (l2_opNorm_toMatrix_toPEquiv_le _)) hVV

/-- `F_{T B_T}` fixes `(s ⊗ s')^{⊗2}`: it exchanges the two identical factors `s`. -/
theorem act_tbSwap_vecKron_tensorPurification (s : T × BT → ℂ) (s' : E × BE → ℂ) :
    act ((tbSwap T E BT BE).toPEquiv.toMatrix)
        (vecKron (WithLp.toLp 2 (tensorPurification s s'))
          (WithLp.toLp 2 (tensorPurification s s'))) =
      vecKron (WithLp.toLp 2 (tensorPurification s s'))
        (WithLp.toLp 2 (tensorPurification s s')) := by
  ext x
  simp only [PEquiv.toMatrix_toPEquiv_mulVec, Function.comp_apply, vecKron, tensorPurification]
  change s (x.2.1.1, x.2.2.1) * s' (x.1.1.2, x.1.2.2) * (s (x.1.1.1, x.1.2.1) *
    s' (x.2.1.2, x.2.2.2)) = _
  ring

omit [DecidableEq T] [DecidableEq BT] [DecidableEq E] [DecidableEq BE] in
theorem norm_toLp_tensorPurification {s : T × BT → ℂ} {s' : E × BE → ℂ}
    (hs : star s ⬝ᵥ s = 1) (hs' : star s' ⬝ᵥ s' = 1) :
    ‖(WithLp.toLp 2 (tensorPurification s s') : EuclideanSpace ℂ _)‖ = 1 := by
  classical
  have h : star (tensorPurification s s') ⬝ᵥ tensorPurification s s' = 1 := by
    rw [← pairSource_mulVec, star_mulVec_dotProduct_mulVec_of_conjTranspose_mul_eq_one
      (pairSource_conjTranspose_mul_self hs) s', hs']
  have h2 := norm_toLp_sq (tensorPurification s s')
  rw [h] at h2
  simp only [Complex.one_re] at h2
  nlinarith [norm_nonneg (WithLp.toLp 2 (tensorPurification s s') : EuclideanSpace ℂ _)]

/-- **The exchange error on the reference (`05-frames.tex`, lines 534–553).** For an isometry
`V`, unit vectors `s`, `s'` and a unit vector `ω` on `(T × E) × U`, with
`δ = ‖𝒱 ω - s ⊗ s'‖`,
`‖D_U F_T ω^{⊗2} - ω^{⊗2}‖ ≤ 4δ`: the squares differ by at most `2δ`, the swap `F_{T B_T}`
fixes `(s ⊗ s')^{⊗2}`, and `‖F_{T B_T} - 1‖ ≤ 2`. -/
theorem norm_act_bufferCorrection_mul_tSwap_sub_le {V : Matrix (BT × BE) U ℂ}
    (hV : V.IsIsometry) {s : T × BT → ℂ} {s' : E × BE → ℂ} (hs : star s ⬝ᵥ s = 1)
    (hs' : star s' ⬝ᵥ s' = 1) {ω : EuclideanSpace ℂ ((T × E) × U)} (hω : ‖ω‖ = 1) :
    ‖act (bufferCorrection (T := T) (E := E) V *
          ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ)) (vecKron ω ω) - vecKron ω ω‖ ≤
      4 * ‖act ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) ω -
        WithLp.toLp 2 (tensorPurification s s')‖ := by
  set 𝒱 := (1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V
  set ζ : EuclideanSpace ℂ ((T × E) × (BT × BE)) := WithLp.toLp 2 (tensorPurification s s')
  set F : Matrix _ _ ℂ := ((tbSwap T E BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ)
  have hiso : 𝒱ᴴ * 𝒱 = 1 :=
    IsIsometry.kronecker (1 : Matrix (T × E) (T × E) ℂ) V (by simp [IsIsometry]) hV
  have hiso2 : (𝒱 ⊗ₖ 𝒱)ᴴ * (𝒱 ⊗ₖ 𝒱) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hiso, one_kronecker_one]
  have hw : ‖act 𝒱 ω‖ = 1 := by
    rw [norm_act_eq_of_gram_eq (B := (1 : Matrix ((T × E) × U) ((T × E) × U) ℂ))
      (by rw [hiso, conjTranspose_one, Matrix.mul_one]), act_one, hω]
  have hζ : ‖ζ‖ = 1 := norm_toLp_tensorPurification hs hs'
  have hF : act F (vecKron ζ ζ) = vecKron ζ ζ := act_tbSwap_vecKron_tensorPurification s s'
  have hFn : ‖F - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(1 : Matrix (((T × E) × (BT × BE)) × ((T × E) × (BT × BE)))
        (((T × E) × (BT × BE)) × ((T × E) × (BT × BE))) ℂ)‖ ≤ 1 :=
      (IsStarProjection.one _).norm_le
    linarith [l2_opNorm_toMatrix_toPEquiv_le (tbSwap T E BT BE)]
  have hV2 : ‖(𝒱 ⊗ₖ 𝒱)ᴴ‖ ≤ 1 := by
    rw [l2_opNorm_conjTranspose]
    exact l2_opNorm_kronecker_le_one (norm_one_kronecker_le_one hV) (norm_one_kronecker_le_one hV)
  have key : act (bufferCorrection (T := T) (E := E) V *
        ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ)) (vecKron ω ω) - vecKron ω ω =
      act (𝒱 ⊗ₖ 𝒱)ᴴ (act (F - 1) (vecKron (act 𝒱 ω) (act 𝒱 ω) - vecKron ζ ζ)) := by
    rw [bufferCorrection_mul_tSwap, act_sub_right, act_sub, act_sub, hF, act_one, act_one,
      sub_self, sub_zero, act_sub_right, ← act_kronecker_vecKron, ← act_mul, ← act_mul, ← act_mul,
      hiso2, act_one]
  rw [key]
  refine (norm_act_le_of_norm_le_one hV2 _).trans ?_
  refine (norm_act_le _ _).trans ?_
  have h2 := EuclideanSpace.norm_vecKron_self_sub_le (act 𝒱 ω) ζ
  rw [hw, hζ] at h2
  nlinarith [norm_nonneg (F - 1), norm_nonneg (act 𝒱 ω - ζ),
    norm_nonneg (vecKron (act 𝒱 ω) (act 𝒱 ω) - vecKron ζ ζ)]

end Buffer

/-! ### Swapping two sheets -/

section SheetSwap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- The bijection of two-sheet raw configurations exchanging the two sheets at the sites of
`S`. -/
def sheetSwap (q : ℕ) (S : Finset ι) : Equiv.Perm ((ι → Fin q) × (ι → Fin q)) where
  toFun r := (fun x => if x ∈ S then r.2 x else r.1 x, fun x => if x ∈ S then r.1 x else r.2 x)
  invFun r := (fun x => if x ∈ S then r.2 x else r.1 x, fun x => if x ∈ S then r.1 x else r.2 x)
  left_inv r := by
    ext x <;> by_cases hx : x ∈ S <;> simp [hx]
  right_inv r := by
    ext x <;> by_cases hx : x ∈ S <;> simp [hx]

/-- The unitary `F_S` swapping the two raw sheets at the positions in `S`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 483–484. -/
def sheetSwapOp (q : ℕ) (S : Finset ι) :
    Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ :=
  (sheetSwap q S).toPEquiv.toMatrix

omit [Fintype ι] in
theorem sheetSwap_symm (S : Finset ι) : (sheetSwap q S).symm = sheetSwap q S := rfl

theorem norm_sheetSwapOp_le_one (S : Finset ι) : ‖sheetSwapOp q S‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- `F_A F_Y = F_T` when `Y` is the disjoint union of `T` and `A`
(`05-frames.tex`, lines 516–520). -/
theorem sheetSwapOp_mul_sheetSwapOp {A Y T : Finset ι} (hT : ∀ x, x ∈ T ↔ x ∈ Y ∧ x ∉ A)
    (hA : A ⊆ Y) : sheetSwapOp q A * sheetSwapOp q Y = sheetSwapOp q T := by
  rw [sheetSwapOp, sheetSwapOp, PEquiv.toMatrix_toPEquiv_mul]
  change ((sheetSwap q Y).toPEquiv.toMatrix : Matrix _ _ ℂ).submatrix (sheetSwap q A)
    (Equiv.refl _) = _
  rw [toMatrix_toPEquiv_submatrix, sheetSwapOp]
  congr 2
  ext r x
  · by_cases hxA : x ∈ A
    · simp [sheetSwap, hxA, hA hxA, (hT x).not.mpr (fun h => h.2 hxA)]
    · by_cases hxY : x ∈ Y <;> simp [sheetSwap, hxA, hxY, hT x]
  · by_cases hxA : x ∈ A
    · simp [sheetSwap, hxA, hA hxA, (hT x).not.mpr (fun h => h.2 hxA)]
    · by_cases hxY : x ∈ Y <;> simp [sheetSwap, hxA, hxY, hT x]

/-- In the coordinates of `sheetSplit S`, swapping the sheets at `S` swaps the `S`-parts. -/
theorem sheetSplit_sheetSwap_fst (S : Finset ι) (r : (ι → Fin q) × (ι → Fin q)) :
    sheetSplit q S (sheetSwap q S r).1 = ((sheetSplit q S r.2).1, (sheetSplit q S r.1).2) := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · simp [sheetSwap, v.2]
  · simp [sheetSwap, Finset.mem_compl.mp v.2]

theorem sheetSplit_sheetSwap_snd (S : Finset ι) (r : (ι → Fin q) × (ι → Fin q)) :
    sheetSplit q S (sheetSwap q S r).2 = ((sheetSplit q S r.1).1, (sheetSplit q S r.2).2) := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · simp [sheetSwap, v.2]
  · simp [sheetSwap, Finset.mem_compl.mp v.2]

/-- The product of an operator acting off `S` and an operator acting on `S`, in the coordinates
of `sheetSplit S`. -/
theorem mul_submatrix_sheetSplit {S : Finset ι} {O I : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    {O' : Matrix (↥Sᶜ → Fin q) (↥Sᶜ → Fin q) ℂ} {I' : Matrix (S → Fin q) (S → Fin q) ℂ}
    (hO : O.submatrix (sheetSplit q S).symm (sheetSplit q S).symm = 1 ⊗ₖ O')
    (hI : I.submatrix (sheetSplit q S).symm (sheetSplit q S).symm = I' ⊗ₖ 1) :
    (O * I).submatrix (sheetSplit q S).symm (sheetSplit q S).symm = I' ⊗ₖ O' := by
  rw [← submatrix_mul_equiv _ _ _ (sheetSplit q S).symm, hO, hI, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

theorem apply_eq_submatrix_apply {m n : Type*} (M : Matrix m m ℂ) (e : m ≃ n) (x y : m) :
    M x y = M.submatrix e.symm e.symm (e x) (e y) := by
  simp

/-- The swap of the sheets at `S` commutes with every product `R₁ ⊗ R₂` of operators acting off
`S`. -/
theorem commute_sheetSwapOp_kronecker {S : Finset ι} {D : Set ι} (hD : Disjoint D (S : Set ι))
    {R₁ R₂ : Matrix (ι → Fin q) (ι → Fin q) ℂ} (h₁ : R₁ ∈ supportedOperators q D)
    (h₂ : R₂ ∈ supportedOperators q D) : Commute (sheetSwapOp q S) (R₁ ⊗ₖ R₂) := by
  obtain ⟨R₁', hR₁'⟩ := exists_one_kronecker_of_mem_supportedOperators hD h₁
  obtain ⟨R₂', hR₂'⟩ := exists_one_kronecker_of_mem_supportedOperators hD h₂
  change _ * _ = _ * _
  rw [sheetSwapOp, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, sheetSwap_symm]
  ext ⟨y₁, y₂⟩ ⟨r₁, r₂⟩
  simp only [submatrix_apply, kroneckerMap_apply, id]
  simp only [apply_eq_submatrix_apply R₁ (sheetSplit q S), apply_eq_submatrix_apply R₂
    (sheetSplit q S)]
  rw [hR₁', hR₂']
  simp only [kroneckerMap_apply, sheetSplit_sheetSwap_fst, sheetSplit_sheetSwap_snd]
  ring

end SheetSwap

/-! ### The buffer correction and the swap of `T` on two sheets -/

section SheetBuffer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {T E : Finset ι} (h : Disjoint T E)

/-- The coordinates `threeSplit T E` on both sheets. -/
abbrev threeSplit₂ : (ι → Fin q) × (ι → Fin q) ≃
    (((T → Fin q) × (E → Fin q)) × (↥(T ∪ E)ᶜ → Fin q)) ×
      (((T → Fin q) × (E → Fin q)) × (↥(T ∪ E)ᶜ → Fin q)) :=
  (threeSplit q T E h).prodCongr (threeSplit q T E h)

/-- The buffer correction `D_U` of splitting data on the raw registers of the two sheets
(`eq:exchange-buffer-correction`). It acts on the two copies of `U = (T ∪ E)ᶜ` alone. -/
def sheetBufferCorrection (σ : SplittingData q T E) :
    Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ :=
  (bufferCorrection (T := T → Fin q) (E := E → Fin q) σ.V).submatrix (threeSplit₂ h)
    (threeSplit₂ h)

-- Two copies of the configurations `((t, e), u)` of three regions form a fourfold product of
-- function types; synthesizing their decidable equality exceeds the default instance size.
set_option synthInstance.maxSize 512 in
theorem norm_sheetBufferCorrection_le_one (σ : SplittingData q T E) :
    ‖sheetBufferCorrection h σ‖ ≤ 1 :=
  (norm_submatrix_equiv_le _ _).trans (norm_bufferCorrection_le_one σ.isIsometry)

set_option synthInstance.maxSize 512 in
/-- In the coordinates `threeSplit T E` of both sheets, swapping the sheets at `T` exchanges the
`T`-components. -/
theorem sheetSwapOp_eq_submatrix :
    sheetSwapOp q T = (((tSwapW (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).toPEquiv.toMatrix :
      Matrix _ _ ℂ)).submatrix (threeSplit₂ h) (threeSplit₂ h) := by
  have he : (threeSplit₂ h).symm.trans ((sheetSwap q T).trans (threeSplit₂ h)) =
      tSwapW (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q) := by
    refine Equiv.ext fun w => ?_
    obtain ⟨⟨⟨t₁, e₁⟩, u₁⟩, ⟨⟨t₂, e₂⟩, u₂⟩⟩ := w
    have hE : ∀ v : E, (v : ι) ∉ T := fun v hv => Finset.disjoint_left.mp h hv v.2
    have hU : ∀ v : ↥(T ∪ E)ᶜ, (v : ι) ∉ T := fun v hv =>
      Finset.mem_compl.mp v.2 (Finset.mem_union_left E hv)
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
      funext v <;> simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
        Prod.map_fst, Prod.map_snd, threeSplit_apply_fst_fst, threeSplit_apply_fst_snd,
        threeSplit_apply_snd, sheetSwap, Equiv.coe_fn_mk, tSwapW]
    · rw [ite_eq_left v.2]; exact threeSplit_symm_apply_of_mem_left h _ _ _ v.2
    · rw [ite_eq_right (hE v)]; exact threeSplit_symm_apply_of_mem_right h _ _ _ v.2
    · rw [ite_eq_right (hU v)]
      exact threeSplit_symm_apply_of_notMem h _ _ _ (Finset.mem_compl.mp v.2)
    · rw [ite_eq_left v.2]; exact threeSplit_symm_apply_of_mem_left h _ _ _ v.2
    · rw [ite_eq_right (hE v)]; exact threeSplit_symm_apply_of_mem_right h _ _ _ v.2
    · rw [ite_eq_right (hU v)]
      exact threeSplit_symm_apply_of_notMem h _ _ _ (Finset.mem_compl.mp v.2)
  have hsub := toMatrix_toPEquiv_submatrix (sheetSwap q T) (threeSplit₂ h).symm
    (threeSplit₂ h).symm
  rw [Equiv.symm_symm, he] at hsub
  rw [← hsub, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  rfl

/-- The buffer correction commutes with every product `R₁ ⊗ R₂` of operators acting on `T ∪ E`,
in particular with the encoders of both sheets when all holes lie in `T ∪ E`
(`05-frames.tex`, lines 514–515). -/
theorem commute_sheetBufferCorrection (σ : SplittingData q T E)
    {R₁ R₂ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hR₁ : R₁ ∈ supportedOperators q (↑(T ∪ E) : Set ι))
    (hR₂ : R₂ ∈ supportedOperators q (↑(T ∪ E) : Set ι)) :
    Commute (sheetBufferCorrection h σ) (R₁ ⊗ₖ R₂) := by
  obtain ⟨R₁', hR₁'⟩ := exists_threeSplit_eq_kronecker_one h hR₁
  obtain ⟨R₂', hR₂'⟩ := exists_threeSplit_eq_kronecker_one h hR₂
  have hR := submatrix_symm_submatrix (R₁ ⊗ₖ R₂) (threeSplit₂ h).symm
  rw [Equiv.symm_symm] at hR
  have hform : (R₁ ⊗ₖ R₂).submatrix (threeSplit₂ h).symm (threeSplit₂ h).symm =
      ((R₁' ⊗ₖ R₂') ⊗ₖ (1 : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
        ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)).submatrix (Equiv.prodProdProdComm _ _ _ _)
        (Equiv.prodProdProdComm _ _ _ _) := by
    rw [← one_kronecker_one, ← kronecker_kronecker_eq_submatrix, ← hR₁', ← hR₂']
    rfl
  rw [← hR, hform, sheetBufferCorrection, bufferCorrection]
  refine Commute.submatrix_equiv (Commute.submatrix_equiv ?_ _) _
  change _ * _ = _ * _
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.one_mul]

end SheetBuffer

end TNLean.PEPS.EncodedFrame
