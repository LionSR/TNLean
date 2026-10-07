/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.HomogeneousOwnership

/-!
# Exchanging assignments between two sheets

Lemma 6.6 of the polynomial-PEPS manuscript exchanges, inside a plane region `Y`, the raw
ownership assignments and the encoded holes (with their tag owners) of two encoded frames. Every
hole's outer square lies on one side of `∂Y`. With a party `P∘`,
`Z = {x : the two old raw owners of x are not both P∘} ∪ H⁺(F₁) ∪ H⁺(F₂)`, `T = Z ∩ Y`,
`E = Z ∖ Y` and `U = Λ ∖ Z`, if `I_Ω(T:E) ≤ L^{-60}` the exchange is implemented by a register
renaming `ℛ` followed by the private swap `F_A` of the two sheets at `A = Y ∩ U` and the private
buffer correction `D_U = (V^{⊗2})ᴴ F_{B_T} V^{⊗2}` on the two copies of `U`, with reference
error at most `4 L^{-30}`.

## Main definitions

* `EncodedFrame.sheetSwap`, `EncodedFrame.sheetSwapOp`: the unitary `F_S` swapping the two raw
  sheets at the sites of `S`.
* `EncodedFrame.TwoSheetExchange`: two frames whose holes are listed as the holes outside `Y`
  followed by the holes inside `Y`, and the exchanged frames.
* `EncodedFrame.TwoSheetExchange.rename`: the renaming `ℛ`.
* `EncodedFrame.bufferSwap`, `EncodedFrame.bufferCorrection`: `F_{B_T}` and `D_U`.
* `EncodedFrame.TwoSheetExchange.exchangeOp`: the implemented map `C = D_U F_A ℛ`.

## Main results

* `EncodedFrame.TwoSheetExchange.rename_mul_encoder`: `ℛ K_in = K_out F_{Y ∩ Λ}`
  (`eq:exchange-intertwining`).
* `EncodedFrame.bufferCorrection_mul_tSwap`: `D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T} 𝒱^{⊗2}`
  (`eq:exchange-net-map`).
* `EncodedFrame.TwoSheetExchange.exchangeOp_mul_encoder`: `C K_in = K_out D_U F_T`
  (`eq:exchange-exact-map`).
* `EncodedFrame.TwoSheetExchange.exchange`,
  `EncodedFrame.TwoSheetExchange.exists_exchange_ofFrames`: Lemma 6.6 `lem:exchange`, for the
  grouped hole lists and for hole lists in any order.

## Scope

**Scope restriction (monomial structure):** Lemma 6.6 asserts that the exchange is implemented
by private contractions and register renaming, using `P∘` and the owners of the renamed registers
and tags, and is therefore a bounded change in the sense of Theorem 5.2. Here `C = D_U F_A ℛ` is
constructed, `D_U` and `F_A` act on the raw registers of `U` alone, which `P∘` holds on both
sheets before and after the exchange, and `ℛ` keeps every register at its party. Reading this as
an allowed monomial of Theorem 5.2 needs a model of operators placed on parties, which the library
does not yet have. Documented in `docs/paper-gaps/polypeps_ownership_change_monomials.tex`.

The source condition that every hole's outer square lies on one side of `∂Y` is recorded through
the physical samples of the outer squares, which it implies. `TwoSheetExchange` lists the holes of
each frame as those outside `Y` followed by those inside `Y`; `exists_exchange_ofFrames` treats
frames whose holes are listed in any order, through the canonical identification of tag orderings
of Definition 6.1.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.6 `lem:exchange` and its proof,
  `05-frames.tex`, lines 458–570.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

-- Two copies of the configurations `((t, e), u)` of three regions are a fourfold product of
-- function types; synthesizing their decidable equality exceeds the default instance size.
set_option synthInstance.maxSize 512

noncomputable section

namespace TNLean.PEPS.EncodedFrame

/-! ### Two copies -/

section TwoCopies

/-- The coordinates `((a, b), (c, d)) ↦ ((a, c), (b, d))` of two copies of a product. -/
def pairShuffle (α β γ δ : Type*) : (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable {α β γ δ α' β' γ' δ' : Type*}

/-- `(A₁ ⊗ B₁) ⊗ (A₂ ⊗ B₂)` is `(A₁ ⊗ A₂) ⊗ (B₁ ⊗ B₂)` in shuffled coordinates. -/
theorem kronecker_kronecker_eq_submatrix (A₁ : Matrix α α' ℂ) (B₁ : Matrix β β' ℂ)
    (A₂ : Matrix γ γ' ℂ) (B₂ : Matrix δ δ' ℂ) :
    (A₁ ⊗ₖ B₁) ⊗ₖ (A₂ ⊗ₖ B₂) =
      ((A₁ ⊗ₖ A₂) ⊗ₖ (B₁ ⊗ₖ B₂)).submatrix (pairShuffle α β γ δ) (pairShuffle α' β' γ' δ') := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
  simp only [kroneckerMap_apply, submatrix_apply, pairShuffle, Equiv.coe_fn_mk]
  ring

/-- The product vector `x ⊗ y`. -/
def vecKron {m n : Type*} (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (m × n) :=
  WithLp.toLp 2 fun p => x p.1 * y p.2

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']

omit [Fintype m'] [Fintype n'] in
theorem act_kronecker_vecKron (A : Matrix m' m ℂ) (B : Matrix n' n ℂ) (x : EuclideanSpace ℂ m)
    (y : EuclideanSpace ℂ n) : act (A ⊗ₖ B) (vecKron x y) = vecKron (act A x) (act B y) := by
  ext ⟨i, j⟩
  simp only [vecKron, mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [Fintype m] [Fintype n] in
theorem vecKron_sub_left (x x' : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    vecKron x y - vecKron x' y = vecKron (x - x') y := by
  ext ⟨i, j⟩
  simp [vecKron, sub_mul]

omit [Fintype m] [Fintype n] in
theorem vecKron_sub_right (x : EuclideanSpace ℂ m) (y y' : EuclideanSpace ℂ n) :
    vecKron x y - vecKron x y' = vecKron x (y - y') := by
  ext ⟨i, j⟩
  simp [vecKron, mul_sub]

/-- `‖x ⊗ y‖ = ‖x‖ ‖y‖`. -/
theorem norm_vecKron (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    ‖vecKron x y‖ = ‖x‖ * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  congr 1
  simp only [vecKron, Fintype.sum_prod_type, norm_mul, mul_pow, Finset.sum_mul_sum]

/-- `‖x ⊗ x - y ⊗ y‖ ≤ ‖x - y‖ (‖x‖ + ‖y‖)`. -/
theorem norm_vecKron_self_sub_le (x y : EuclideanSpace ℂ m) :
    ‖vecKron x x - vecKron y y‖ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have h : vecKron x x - vecKron y y = vecKron (x - y) x + vecKron y (x - y) := by
    rw [← vecKron_sub_left, ← vecKron_sub_right]
    abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_vecKron, norm_vecKron]
  linarith [mul_comm ‖y‖ ‖x - y‖]

variable [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n']

omit [DecidableEq m'] in
/-- `‖1 ⊗ B‖ ≤ ‖B‖`. -/
theorem l2_opNorm_one_kronecker_le (B : Matrix m' n ℂ) :
    ‖(1 : Matrix m m ℂ) ⊗ₖ B‖ ≤ ‖B‖ := by
  have h : (1 : Matrix m m ℂ) ⊗ₖ B =
      reindex (Equiv.prodComm m' m) (Equiv.prodComm n m) (B ⊗ₖ (1 : Matrix m m ℂ)) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [kroneckerMap_apply, mul_comm]
  rw [h]
  exact (l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_kronecker_one_le B)

omit [DecidableEq m'] [DecidableEq n'] in
/-- `‖A ⊗ B‖ ≤ ‖A‖ ‖B‖`. -/
theorem l2_opNorm_kronecker_le (A : Matrix m' m ℂ) (B : Matrix n' n ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  classical
  have h : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n' n' ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ B) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h]
  exact (l2_opNorm_mul _ _).trans (mul_le_mul (l2_opNorm_kronecker_one_le A)
    (l2_opNorm_one_kronecker_le B) (norm_nonneg _) (norm_nonneg _))

omit [DecidableEq m'] [DecidableEq n'] in
theorem l2_opNorm_kronecker_le_one {A : Matrix m' m ℂ} {B : Matrix n' n ℂ} (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1) : ‖A ⊗ₖ B‖ ≤ 1 :=
  (l2_opNorm_kronecker_le A B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])

omit [DecidableEq m] in
/-- The matrix of a bijection of coordinates is a contraction. -/
theorem l2_opNorm_toMatrix_toPEquiv_le (f : m ≃ n) :
    ‖(f.toPEquiv.toMatrix : Matrix m n ℂ)‖ ≤ 1 := by
  have h : (f.toPEquiv.toMatrix : Matrix m n ℂ) = reindex f.symm (Equiv.refl n) 1 := by
    rw [← Matrix.mul_one (f.toPEquiv.toMatrix : Matrix m n ℂ), PEquiv.toMatrix_toPEquiv_mul]
    rfl
  rw [h]
  exact (l2_opNorm_reindex_le _ _ _).trans (IsStarProjection.one _).norm_le

omit [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m] [DecidableEq n] in
/-- The matrix of a product of bijections is the Kronecker product of their matrices. -/
theorem toMatrix_toPEquiv_prodCongr (f : m ≃ m') (g : n ≃ n') :
    ((f.prodCongr g).toPEquiv.toMatrix : Matrix (m × n) (m' × n') ℂ) =
      (f.toPEquiv.toMatrix : Matrix m m' ℂ) ⊗ₖ (g.toPEquiv.toMatrix : Matrix n n' ℂ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    kroneckerMap_apply, Equiv.prodCongr_apply, Prod.map, Prod.mk.injEq]
  by_cases h₁ : f i = k <;> by_cases h₂ : g j = l <;> simp [h₁, h₂]

omit [Fintype m] [Fintype n] [DecidableEq m] in
/-- Relabelling the coordinates of the matrix of a bijection. -/
theorem toMatrix_toPEquiv_submatrix {l l' : Type*} [DecidableEq l'] (f : m ≃ n) (e₁ : l ≃ m)
    (e₂ : l' ≃ n) :
    (f.toPEquiv.toMatrix : Matrix m n ℂ).submatrix e₁ e₂ =
      ((e₁.trans (f.trans e₂.symm)).toPEquiv.toMatrix : Matrix l l' ℂ) := by
  ext i j
  simp only [submatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.trans_apply,
    Option.mem_some_iff, Equiv.symm_apply_eq]

end TwoCopies

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
    (pairShuffle (T × E) U (T × E) U) (pairShuffle (T × E) U (T × E) U)

omit [Fintype T] [Fintype E] [Fintype U] in
theorem tSwapW_toMatrix :
    ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ) =
      (((tSwap T E).toPEquiv.toMatrix : Matrix _ _ ℂ) ⊗ₖ
          (1 : Matrix (U × U) (U × U) ℂ)).submatrix
        (pairShuffle (T × E) U (T × E) U) (pairShuffle (T × E) U (T × E) U) := by
  rw [← PEquiv.toMatrix_refl, ← Equiv.toPEquiv_refl, ← toMatrix_toPEquiv_prodCongr,
    toMatrix_toPEquiv_submatrix]
  rfl

omit [Fintype T] [Fintype E] [Fintype BT] [Fintype BE] in
theorem tbSwap_toMatrix :
    ((tbSwap T E BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ) =
      (((tSwap T E).toPEquiv.toMatrix : Matrix _ _ ℂ) ⊗ₖ
          ((bufferSwap BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ)).submatrix
        (pairShuffle (T × E) (BT × BE) (T × E) (BT × BE))
        (pairShuffle (T × E) (BT × BE) (T × E) (BT × BE)) := by
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
  have h2 := norm_vecKron_self_sub_le (act 𝒱 ω) ζ
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

theorem norm_sheetBufferCorrection_le_one (σ : SplittingData q T E) :
    ‖sheetBufferCorrection h σ‖ ≤ 1 :=
  (norm_submatrix_equiv_le _ _).trans (norm_bufferCorrection_le_one σ.isIsometry)

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
        ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)).submatrix (pairShuffle _ _ _ _)
        (pairShuffle _ _ _ _) := by
    rw [← one_kronecker_one, ← kronecker_kronecker_eq_submatrix, ← hR₁', ← hR₂']
    rfl
  rw [← hR, hform, sheetBufferCorrection, bufferCorrection]
  refine Commute.submatrix_equiv (Commute.submatrix_equiv ?_ _) _
  change _ * _ = _ * _
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.one_mul]

end SheetBuffer

/-! ### Exchange data -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type*}

/-- **Data of Lemma 6.6.** Two encoded frames on two sheets and the physical sample `Y ∩ Λ` of a
plane region `Y`. The holes of each frame are listed as the holes whose outer squares lie outside
`Y`, followed by those whose outer squares lie inside `Y`: every hole's entire outer square lies on
one side of `∂Y`. Since encodings of holes with disjoint footprints commute, this ordering is the
canonical identification of tag orderings of Definition 6.1. The source condition concerns the
outer squares in the plane; only its consequence for their physical samples is recorded.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 461–464. -/
structure TwoSheetExchange (pos : ι → ℝ × ℝ) (q : ℕ) (Party : Type*) where
  /-- The raw owners of the first sheet. -/
  owner₁ : ι → Party
  /-- The raw owners of the second sheet. -/
  owner₂ : ι → Party
  /-- The holes of the first frame outside `Y`. -/
  out₁ : List (Hole pos q Party)
  /-- The holes of the first frame inside `Y`. -/
  in₁ : List (Hole pos q Party)
  /-- The holes of the second frame outside `Y`. -/
  out₂ : List (Hole pos q Party)
  /-- The holes of the second frame inside `Y`. -/
  in₂ : List (Hole pos q Party)
  /-- The physical sample `Y ∩ Λ` of the region. -/
  region : Finset ι
  disjoint₁ : PairwiseDisjointOuter ((out₁ ++ in₁).map Hole.patch)
  disjoint₂ : PairwiseDisjointOuter ((out₂ ++ in₂).map Hole.patch)
  /-- The outer squares of the holes inside `Y` lie in `Y`. -/
  inside : ∀ h ∈ in₁ ++ in₂, (h.patch.outer : Set ι) ⊆ region
  /-- The outer squares of the holes outside `Y` avoid `Y`. -/
  outside : ∀ h ∈ out₁ ++ out₂, Disjoint (h.patch.outer : Set ι) region

/-- Holes outside and inside `Y` have disjoint outer footprints. -/
theorem pairwiseDisjointOuter_append {o i : List (Hole pos q Party)} {Y : Finset ι}
    (ho : PairwiseDisjointOuter (o.map Hole.patch)) (hi : PairwiseDisjointOuter (i.map Hole.patch))
    (hoY : ∀ h ∈ o, Disjoint (h.patch.outer : Set ι) Y)
    (hiY : ∀ h ∈ i, (h.patch.outer : Set ι) ⊆ Y) :
    PairwiseDisjointOuter ((o ++ i).map Hole.patch) := by
  rw [PairwiseDisjointOuter, List.map_append, List.pairwise_append]
  refine ⟨ho, hi, ?_⟩
  intro a ha b hb
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ha
  obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hb
  rw [← Finset.disjoint_coe]
  exact Set.disjoint_of_subset_right (hiY h' hh') (hoY h hh)

theorem footprint_mono {l l' : List (SquarePatch pos q)} (h : ∀ p ∈ l, p ∈ l') :
    footprint l ⊆ footprint l' := fun _ ⟨p, hp, hx⟩ => ⟨p, h p hp, hx⟩

/-- The operator acting as `G` on the raw registers of two sheets and as the identity on the
tags of two lists of holes. -/
def liftTags {l₁ l₂ : List (Hole pos q Party)}
    (G : Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ) :
    Matrix ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q)))
      ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q))) ℂ :=
  ((1 : Matrix (TagSpace l₁ × TagSpace l₂) (TagSpace l₁ × TagSpace l₂) ℂ) ⊗ₖ G).submatrix
    (pairShuffle _ _ _ _) (pairShuffle _ _ _ _)

theorem norm_liftTags_le {l₁ l₂ : List (Hole pos q Party)}
    (G : Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ) :
    ‖liftTags (l₁ := l₁) (l₂ := l₂) G‖ ≤ ‖G‖ :=
  (norm_submatrix_equiv_le _ _).trans (l2_opNorm_one_kronecker_le G)

/-- A two-sheet raw operator commuting with every product of raw parts of the two encodings
passes through the product `K₁ ⊗ K₂` of the encodings. -/
theorem liftTags_mul_kronecker [NeZero q] {l₁ l₂ : List (Hole pos q Party)}
    {G : Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ}
    (hG : ∀ a b, Commute G (rawProd l₁ a ⊗ₖ rawProd l₂ b)) :
    liftTags G * (frameEncoder l₁ ⊗ₖ frameEncoder l₂) =
      (frameEncoder l₁ ⊗ₖ frameEncoder l₂) * G := by
  have hK : frameEncoder l₁ ⊗ₖ frameEncoder l₂ =
      (stack fun t : TagSpace l₁ × TagSpace l₂ => rawProd l₁ t.1 ⊗ₖ rawProd l₂ t.2).submatrix
        (pairShuffle _ _ _ _) (Equiv.refl _) := by
    ext ⟨⟨a, x⟩, ⟨b, y⟩⟩ ⟨r₁, r₂⟩
    rfl
  set S : TagSpace l₁ × TagSpace l₂ → Matrix ((ι → Fin q) × (ι → Fin q))
    ((ι → Fin q) × (ι → Fin q)) ℂ := fun t => rawProd l₁ t.1 ⊗ₖ rawProd l₂ t.2
  have hS : ((1 : Matrix (TagSpace l₁ × TagSpace l₂) (TagSpace l₁ × TagSpace l₂) ℂ) ⊗ₖ G) *
      stack S = stack S * G := one_kronecker_mul_stack fun t => hG t.1 t.2
  rw [hK, liftTags]
  rw [submatrix_mul_equiv]
  rw [hS]
  conv_rhs => rw [← submatrix_id_id G, ← Equiv.coe_refl, submatrix_mul_equiv]

namespace TwoSheetExchange

variable (X : TwoSheetExchange pos q Party)

/-- The first frame `F₁`. -/
abbrev frame₁ : Frame pos q Party := ⟨X.owner₁, X.out₁ ++ X.in₁, X.disjoint₁⟩

/-- The second frame `F₂`. -/
abbrev frame₂ : Frame pos q Party := ⟨X.owner₂, X.out₂ ++ X.in₂, X.disjoint₂⟩

theorem disjoint_new₁ : PairwiseDisjointOuter ((X.out₁ ++ X.in₂).map Hole.patch) :=
  pairwiseDisjointOuter_append X.disjoint₁.left X.disjoint₂.right
    (fun h hh => X.outside h (List.mem_append_left _ hh))
    (fun h hh => X.inside h (List.mem_append_right _ hh))

theorem disjoint_new₂ : PairwiseDisjointOuter ((X.out₂ ++ X.in₁).map Hole.patch) :=
  pairwiseDisjointOuter_append X.disjoint₂.left X.disjoint₁.right
    (fun h hh => X.outside h (List.mem_append_right _ hh))
    (fun h hh => X.inside h (List.mem_append_left _ hh))

/-- The first frame after the exchange: inside `Y` it carries the raw ownership assignment and
the holes, with their tag owners, of the second frame (`05-frames.tex`, lines 462–464). -/
abbrev newFrame₁ : Frame pos q Party :=
  ⟨fun x => if x ∈ X.region then X.owner₂ x else X.owner₁ x, X.out₁ ++ X.in₂, X.disjoint_new₁⟩

/-- The second frame after the exchange. -/
abbrev newFrame₂ : Frame pos q Party :=
  ⟨fun x => if x ∈ X.region then X.owner₁ x else X.owner₂ x, X.out₂ ++ X.in₁, X.disjoint_new₂⟩

/-- The renaming of registers: inside `Y`, the raw registers of the two sheets and the tags of the
holes exchange their sheet names; every register keeps its party (`05-frames.tex`, lines
485–489). -/
def renameEquiv : X.frame₁.Layout × X.frame₂.Layout ≃ X.newFrame₁.Layout × X.newFrame₂.Layout where
  toFun y :=
    let a₁ := tagAppendEquiv X.out₁ X.in₁ y.1.1
    let a₂ := tagAppendEquiv X.out₂ X.in₂ y.2.1
    let r := sheetSwap q X.region (y.1.2, y.2.2)
    (((tagAppendEquiv X.out₁ X.in₂).symm (a₁.1, a₂.2), r.1),
      ((tagAppendEquiv X.out₂ X.in₁).symm (a₂.1, a₁.2), r.2))
  invFun y :=
    let a₁ := tagAppendEquiv X.out₁ X.in₂ y.1.1
    let a₂ := tagAppendEquiv X.out₂ X.in₁ y.2.1
    let r := sheetSwap q X.region (y.1.2, y.2.2)
    (((tagAppendEquiv X.out₁ X.in₁).symm (a₁.1, a₂.2), r.1),
      ((tagAppendEquiv X.out₂ X.in₂).symm (a₂.1, a₁.2), r.2))
  left_inv y := by
    obtain ⟨⟨τ₁, x₁⟩, ⟨τ₂, x₂⟩⟩ := y
    have h := (sheetSwap q X.region).symm_apply_apply (x₁, x₂)
    simp only [Equiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
    rw [sheetSwap_symm] at h
    simp only [h]
  right_inv y := by
    obtain ⟨⟨τ₁, x₁⟩, ⟨τ₂, x₂⟩⟩ := y
    have h := (sheetSwap q X.region).symm_apply_apply (x₁, x₂)
    simp only [Equiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
    rw [sheetSwap_symm] at h
    simp only [h]

/-- **The renaming `ℛ`** between the two-sheet layouts before and after the exchange. -/
def rename : Matrix (X.newFrame₁.Layout × X.newFrame₂.Layout)
    (X.frame₁.Layout × X.frame₂.Layout) ℂ :=
  X.renameEquiv.symm.toPEquiv.toMatrix

theorem norm_rename_le_one : ‖X.rename‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- The raw part of the encoding of the holes outside `Y` acts off `Y`. -/
theorem exists_out_form [NeZero q] {o : List (Hole pos q Party)}
    (ho : ∀ h ∈ o, h ∈ X.out₁ ++ X.out₂) (a : TagSpace o) :
    ∃ O' : Matrix (↥X.regionᶜ → Fin q) (↥X.regionᶜ → Fin q) ℂ,
      (rawProd o a).submatrix (sheetSplit q X.region).symm (sheetSplit q X.region).symm =
        1 ⊗ₖ O' :=
  exists_one_kronecker_of_mem_supportedOperators
    (disjoint_footprint_of_forall fun p hp => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact X.outside h (ho h hh))
    (rawProd_mem_supportedOperators o a)

/-- The raw part of the encoding of the holes inside `Y` acts on `Y`. -/
theorem exists_in_form [NeZero q] {i : List (Hole pos q Party)}
    (hi : ∀ h ∈ i, h ∈ X.in₁ ++ X.in₂) (a : TagSpace i) :
    ∃ I' : Matrix (X.region → Fin q) (X.region → Fin q) ℂ,
      (rawProd i a).submatrix (sheetSplit q X.region).symm (sheetSplit q X.region).symm =
        I' ⊗ₖ 1 :=
  exists_kronecker_one_of_mem_supportedOperators
    (supportedOperators_mono (fun x hx => by
      obtain ⟨p, hp, hx⟩ := hx
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact X.inside h (hi h hh) hx)
    (rawProd_mem_supportedOperators i a))

/-- **Exact intertwining identity (`eq:exchange-intertwining`).** `ℛ K_in = K_out F_{Y ∩ Λ}`,
where `K_in` and `K_out` are the products of the two frames' encoders before and after the
exchange. Every hole lies on one side of `∂Y`, so for every selected radius its raw squares and
its tag change sheet together.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 482–498. -/
theorem rename_mul_encoder [NeZero q] :
    X.rename * (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) =
      (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) * sheetSwapOp q X.region := by
  rw [rename, PEquiv.toMatrix_toPEquiv_mul, sheetSwapOp, PEquiv.mul_toMatrix_toPEquiv,
    sheetSwap_symm]
  ext ⟨⟨τ₁, x₁⟩, ⟨τ₂, x₂⟩⟩ ⟨r₁, r₂⟩
  obtain ⟨O₁, hO₁⟩ := X.exists_out_form (fun h hh => List.mem_append_left _ hh)
    (tagAppendEquiv X.out₁ X.in₂ τ₁).1
  obtain ⟨O₂, hO₂⟩ := X.exists_out_form (fun h hh => List.mem_append_right _ hh)
    (tagAppendEquiv X.out₂ X.in₁ τ₂).1
  obtain ⟨I₁, hI₁⟩ := X.exists_in_form (fun h hh => List.mem_append_left _ hh)
    (tagAppendEquiv X.out₂ X.in₁ τ₂).2
  obtain ⟨I₂, hI₂⟩ := X.exists_in_form (fun h hh => List.mem_append_right _ hh)
    (tagAppendEquiv X.out₁ X.in₂ τ₁).2
  simp only [submatrix_apply, kroneckerMap_apply, id, Frame.encoder, frameEncoder, stack_apply,
    renameEquiv, Equiv.coe_fn_symm_mk]
  rw [rawProd_append, rawProd_append, rawProd_append, rawProd_append]
  simp only [Equiv.apply_symm_apply]
  rw [apply_eq_submatrix_apply (_ * _) (sheetSplit q X.region),
    mul_submatrix_sheetSplit hO₁ hI₁,
    apply_eq_submatrix_apply (rawProd X.out₂ _ * rawProd X.in₂ _) (sheetSplit q X.region),
    mul_submatrix_sheetSplit hO₂ hI₂,
    apply_eq_submatrix_apply (rawProd X.out₁ _ * rawProd X.in₂ _) (sheetSplit q X.region),
    mul_submatrix_sheetSplit hO₁ hI₂,
    apply_eq_submatrix_apply (rawProd X.out₂ _ * rawProd X.in₁ _) (sheetSplit q X.region),
    mul_submatrix_sheetSplit hO₂ hI₁]
  simp only [kroneckerMap_apply, sheetSplit_sheetSwap_fst, sheetSplit_sheetSwap_snd]
  ring

/-! ### The partition and the exchange map -/

variable (P : Party)

open Classical in
/-- The set `Z = {x : the two old raw owners of x are not both P∘} ∪ H⁺(F₁) ∪ H⁺(F₂)`
(`eq:exchange-Z`).

Polynomial-PEPS manuscript, Lemma 6.6, `05-frames.tex`, lines 466–470. -/
def exchangeEnv : Finset ι :=
  Finset.univ.filter fun x =>
    ¬(X.owner₁ x = P ∧ X.owner₂ x = P) ∨ x ∈ X.frame₁.outerHoles ∨ x ∈ X.frame₂.outerHoles

/-- `T = Z ∩ Y` (`eq:exchange-partition`). -/
def tSet : Finset ι := X.exchangeEnv P ∩ X.region

/-- `E = Z ∖ Y` (`eq:exchange-partition`). -/
def eSet : Finset ι := X.exchangeEnv P \ X.region

/-- `A = Y ∩ U = Y ∖ Z`, where the private swap `F_A` acts (`05-frames.tex`, line 512). -/
def aSet : Finset ι := X.region \ X.exchangeEnv P

theorem mem_exchangeEnv {x : ι} : x ∈ X.exchangeEnv P ↔
    ¬(X.owner₁ x = P ∧ X.owner₂ x = P) ∨ x ∈ X.frame₁.outerHoles ∨ x ∈ X.frame₂.outerHoles := by
  classical
  unfold exchangeEnv
  simp

theorem disjoint_tSet_eSet : Disjoint (X.tSet P) (X.eSet P) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [tSet, eSet, Finset.mem_inter, Finset.mem_sdiff] at hx hx'
  exact hx'.2 hx.2

theorem tSet_union_eSet : X.tSet P ∪ X.eSet P = X.exchangeEnv P := by
  ext x
  simp only [tSet, eSet, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem mem_tSet_iff (x : ι) : x ∈ X.tSet P ↔ x ∈ X.region ∧ x ∉ X.aSet P := by
  simp only [tSet, aSet, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem aSet_subset_region : X.aSet P ⊆ X.region := Finset.sdiff_subset

/-- `A` lies in `U = Λ ∖ Z`. -/
theorem aSet_subset_compl : X.aSet P ⊆ (X.tSet P ∪ X.eSet P)ᶜ := by
  intro x hx
  rw [tSet_union_eSet, Finset.mem_compl]
  exact (Finset.mem_sdiff.mp hx).2

/-- Every register of `U = Λ ∖ Z` is raw and held by `P∘` on both sheets, before the exchange
(`05-frames.tex`, lines 500–501). -/
theorem owner_eq_of_notMem_exchangeEnv {x : ι} (hx : x ∉ X.exchangeEnv P) :
    X.owner₁ x = P ∧ X.owner₂ x = P := by
  by_contra h
  exact hx ((X.mem_exchangeEnv P).mpr (Or.inl h))

/-- Every register of `U` is held by `P∘` on both sheets after the exchange as well. -/
theorem newOwner_eq_of_notMem_exchangeEnv {x : ι} (hx : x ∉ X.exchangeEnv P) :
    X.newFrame₁.owner x = P ∧ X.newFrame₂.owner x = P := by
  obtain ⟨h₁, h₂⟩ := X.owner_eq_of_notMem_exchangeEnv P hx
  change (if x ∈ X.region then X.owner₂ x else X.owner₁ x) = P ∧
    (if x ∈ X.region then X.owner₁ x else X.owner₂ x) = P
  split_ifs <;> exact ⟨by assumption, by assumption⟩

/-- The renaming keeps every register at its party: the new owner of the register of the first
sheet at `x ∈ Y` is the old owner of the second sheet there (`05-frames.tex`, lines 487–489). -/
theorem newFrame₁_owner_of_mem {x : ι} (hx : x ∈ X.region) :
    X.newFrame₁.owner x = X.owner₂ x := ite_eq_left hx

theorem newFrame₂_owner_of_mem {x : ι} (hx : x ∈ X.region) :
    X.newFrame₂.owner x = X.owner₁ x := ite_eq_left hx

theorem footprint_new₁_subset :
    footprint ((X.out₁ ++ X.in₂).map Hole.patch) ⊆ (↑(X.tSet P ∪ X.eSet P) : Set ι) := by
  rw [tSet_union_eSet, List.map_append, footprint_append]
  rintro x (hx | hx)
  · exact (X.mem_exchangeEnv P).mpr (Or.inr (Or.inl (footprint_mono (fun p hp => by
      simp only [Frame.patches, List.map_append, List.mem_append]; exact Or.inl hp) hx)))
  · exact (X.mem_exchangeEnv P).mpr (Or.inr (Or.inr (footprint_mono (fun p hp => by
      simp only [Frame.patches, List.map_append, List.mem_append]; exact Or.inr hp) hx)))

theorem footprint_new₂_subset :
    footprint ((X.out₂ ++ X.in₁).map Hole.patch) ⊆ (↑(X.tSet P ∪ X.eSet P) : Set ι) := by
  rw [tSet_union_eSet, List.map_append, footprint_append]
  rintro x (hx | hx)
  · exact (X.mem_exchangeEnv P).mpr (Or.inr (Or.inr (footprint_mono (fun p hp => by
      simp only [Frame.patches, List.map_append, List.mem_append]; exact Or.inl hp) hx)))
  · exact (X.mem_exchangeEnv P).mpr (Or.inr (Or.inl (footprint_mono (fun p hp => by
      simp only [Frame.patches, List.map_append, List.mem_append]; exact Or.inr hp) hx)))

/-- **The implemented map `C = D_U F_A ℛ`.** First rename the sheets inside `Y`, then apply the
private swap `F_A` and then the private buffer correction `D_U`, in this order; both act on raw
registers of `U` alone and as the identity on the tags.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 485–489 and 512–527. -/
def exchangeOp (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    Matrix (X.newFrame₁.Layout × X.newFrame₂.Layout) (X.frame₁.Layout × X.frame₂.Layout) ℂ :=
  liftTags (l₁ := X.out₁ ++ X.in₂) (l₂ := X.out₂ ++ X.in₁)
    (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.aSet P)) * X.rename

theorem norm_exchangeOp_le_one (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    ‖X.exchangeOp P σ‖ ≤ 1 :=
  l2_opNorm_mul_le_one ((norm_liftTags_le _).trans (l2_opNorm_mul_le_one
    (norm_sheetBufferCorrection_le_one _ σ) (norm_sheetSwapOp_le_one _))) X.norm_rename_le_one

/-- The corrections `D_U` and `F_A` commute with the raw parts of the encoders after the
exchange: they act on `U`, away from every hole of both sheets (`05-frames.tex`, lines
514–515). -/
theorem commute_correction [NeZero q] (σ : SplittingData q (X.tSet P) (X.eSet P))
    (a : TagSpace (X.out₁ ++ X.in₂)) (b : TagSpace (X.out₂ ++ X.in₁)) :
    Commute (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.aSet P))
      (rawProd (X.out₁ ++ X.in₂) a ⊗ₖ rawProd (X.out₂ ++ X.in₁) b) := by
  have h₁ := supportedOperators_mono (X.footprint_new₁_subset P)
    (rawProd_mem_supportedOperators _ a)
  have h₂ := supportedOperators_mono (X.footprint_new₂_subset P)
    (rawProd_mem_supportedOperators _ b)
  refine Commute.mul_left (commute_sheetBufferCorrection _ σ h₁ h₂)
    (commute_sheetSwapOp_kronecker ?_ h₁ h₂)
  exact Finset.disjoint_coe.mpr (Finset.disjoint_of_subset_right (X.aSet_subset_compl P)
    disjoint_compl_right)

/-- **The net map on the sheets (`eq:exchange-net-map`).** `D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T}
𝒱^{⊗2}`, in the coordinates `((t, e), u)` of both sheets.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 516–526. -/
theorem sheetBufferCorrection_mul_sheetSwapOp (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.tSet P) =
      Matrix.submatrix ((((1 : Matrix _ _ ℂ) ⊗ₖ σ.V) ⊗ₖ ((1 : Matrix _ _ ℂ) ⊗ₖ σ.V))ᴴ *
          ((tbSwap (X.tSet P → Fin q) (X.eSet P → Fin q) (X.tSet P → Fin q)
            ((X.eSet P → Fin q) ⊕ (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q))).toPEquiv.toMatrix :
              Matrix _ _ ℂ) *
          (((1 : Matrix _ _ ℂ) ⊗ₖ σ.V) ⊗ₖ ((1 : Matrix _ _ ℂ) ⊗ₖ σ.V)))
        (threeSplit₂ (X.disjoint_tSet_eSet P)) (threeSplit₂ (X.disjoint_tSet_eSet P)) := by
  rw [sheetSwapOp_eq_submatrix (X.disjoint_tSet_eSet P), sheetBufferCorrection,
    submatrix_mul_equiv, bufferCorrection_mul_tSwap]

/-- **The exact map (`eq:exchange-exact-map`).** `C K_in = K_out D_U F_T`, and
`D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T} 𝒱^{⊗2}` (`sheetBufferCorrection_mul_sheetSwapOp`).

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 512–532. -/
theorem exchangeOp_mul_encoder [NeZero q] (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    X.exchangeOp P σ * (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) =
      (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) *
        (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.tSet P)) := by
  rw [exchangeOp, Matrix.mul_assoc, rename_mul_encoder, ← Matrix.mul_assoc]
  rw [show X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder =
    frameEncoder (X.out₁ ++ X.in₂) ⊗ₖ frameEncoder (X.out₂ ++ X.in₁) from rfl,
    liftTags_mul_kronecker (X.commute_correction P σ), Matrix.mul_assoc, Matrix.mul_assoc,
    sheetSwapOp_mul_sheetSwapOp (X.mem_tSet_iff P) (X.aSet_subset_region P)]

/-- **Lemma 6.6 (two-sheet exchange).** Consider two encoded frames and a region `Y` such that
every hole's entire outer square lies on one side of `∂Y`. Inside `Y`, exchange the two raw
ownership assignments and the two lists of encoded holes, with their tag owners. Let `P∘` be a
party and `Z`, `T`, `E`, `U` as in `eq:exchange-Z` and `eq:exchange-partition`. If
`I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data such that the map
`C = D_U F_A ℛ`, a register renaming followed by a private swap and a private buffer correction
on the registers of `U` (all held by `P∘` before and after, `owner_eq_of_notMem_exchangeEnv`,
`newOwner_eq_of_notMem_exchangeEnv`), is a contraction with
`C K_in = K_out D_U F_T` and
`‖C (Ω_{F₁} ⊗ Ω_{F₂}) - Ω_{F₁'} ⊗ Ω_{F₂'}‖ ≤ 4 L^{-30}`. No raw register is transferred: the
renaming keeps every register at its party (`newFrame₁_owner_of_mem`).

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 460–479; proof
lines 481–561. -/
theorem exchange [NeZero q] {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hL : 0 < L)
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω (X.tSet P) (X.eSet P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q (X.tSet P) (X.eSet P),
      σ.error (X.disjoint_tSet_eSet P) Ω ≤ L ^ (-30 : ℤ) ∧
      ‖X.exchangeOp P σ‖ ≤ 1 ∧
      X.exchangeOp P σ * (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) =
        (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) *
          (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.tSet P)) ∧
      ‖act (X.exchangeOp P σ) (vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω)) -
        vecKron (X.newFrame₁.refVec Ω) (X.newFrame₂.refVec Ω)‖ ≤ 4 * L ^ (-30 : ℤ) := by
  set h := X.disjoint_tSet_eSet P
  obtain ⟨σ, hσ⟩ := exists_sheetSplitting_zpow h hΩ hL hI
  refine ⟨σ, hσ, X.norm_exchangeOp_le_one P σ, X.exchangeOp_mul_encoder P σ, ?_⟩
  have hKout : ‖X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder‖ ≤ 1 :=
    l2_opNorm_kronecker_le_one X.newFrame₁.norm_encoder_le_one X.newFrame₂.norm_encoder_le_one
  have hin : vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω) =
      act (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) (vecKron Ω Ω) :=
    (act_kronecker_vecKron _ _ _ _).symm
  have hout : vecKron (X.newFrame₁.refVec Ω) (X.newFrame₂.refVec Ω) =
      act (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) (vecKron Ω Ω) :=
    (act_kronecker_vecKron _ _ _ _).symm
  rw [hin, hout, ← act_mul, X.exchangeOp_mul_encoder P σ, act_mul, ← act_sub_right]
  refine (norm_act_le_of_norm_le_one hKout _).trans ?_
  rw [sheetSwapOp_eq_submatrix h, sheetBufferCorrection, submatrix_mul_equiv,
    norm_act_submatrix_sub]
  set ω : EuclideanSpace ℂ _ := WithLp.toLp 2 (splitVec h Ω)
  have hω : (WithLp.toLp 2 (⇑(vecKron Ω Ω) ∘ (threeSplit₂ h).symm) : EuclideanSpace ℂ _) =
      vecKron ω ω := rfl
  have hω1 : ‖ω‖ = 1 := by
    have h2 := norm_toLp_sq (splitVec h Ω)
    rw [star_splitVec_dotProduct_splitVec h hΩ, Complex.one_re] at h2
    nlinarith [norm_nonneg ω]
  rw [hω]
  refine (norm_act_bufferCorrection_mul_tSwap_sub_le σ.isIsometry σ.star_s σ.star_s' hω1).trans ?_
  have he : ‖act ((1 : Matrix _ _ ℂ) ⊗ₖ σ.V) ω - WithLp.toLp 2 (tensorPurification σ.s σ.s')‖ =
      σ.error h Ω := rfl
  rw [he]
  linarith

/-! ### Frames with holes in any order -/

/-- Whether the outer footprint of a hole fails to lie in `Y`. -/
def outsideRegion (Y : Finset ι) (h : Hole pos q Party) : Bool := !decide (h.patch.outer ⊆ Y)

/-- **Exchange data of two arbitrary frames.** For encoded frames `F₁`, `F₂` and the physical
sample `Y` of a region such that every hole's outer footprint lies in `Y` or avoids it, list the
holes of each frame as those outside `Y` followed by those inside `Y`, keeping their relative
order. This is a reordering of the tags of each frame.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 461–464. -/
def ofFrames (F₁ F₂ : Frame pos q Party) (Y : Finset ι)
    (hside : ∀ h ∈ F₁.holes ++ F₂.holes,
      (h.patch.outer : Set ι) ⊆ Y ∨ Disjoint (h.patch.outer : Set ι) Y) :
    TwoSheetExchange pos q Party where
  owner₁ := F₁.owner
  owner₂ := F₂.owner
  out₁ := F₁.holes.filter (outsideRegion Y)
  in₁ := F₁.holes.filter fun h => !outsideRegion Y h
  out₂ := F₂.holes.filter (outsideRegion Y)
  in₂ := F₂.holes.filter fun h => !outsideRegion Y h
  region := Y
  disjoint₁ := F₁.disjoint.perm ((List.filter_append_perm _ _).symm.map _) fun h => Disjoint.symm h
  disjoint₂ := F₂.disjoint.perm ((List.filter_append_perm _ _).symm.map _) fun h => Disjoint.symm h
  inside h hh := by
    rcases List.mem_append.mp hh with hh | hh <;>
    · have := (List.mem_filter.mp hh).2
      simp only [outsideRegion, Bool.not_not, decide_eq_true_eq] at this
      exact Finset.coe_subset.mpr this
  outside h hh := by
    rcases List.mem_append.mp hh with hh | hh
    · have h₁ := List.mem_filter.mp hh
      simp only [outsideRegion, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        at h₁
      exact (hside h (List.mem_append_left _ h₁.1)).resolve_left
        fun h' => h₁.2 (Finset.coe_subset.mp h')
    · have h₁ := List.mem_filter.mp hh
      simp only [outsideRegion, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        at h₁
      exact (hside h (List.mem_append_right _ h₁.1)).resolve_left
        fun h' => h₁.2 (Finset.coe_subset.mp h')

theorem mem_footprint_perm {l l' : List (Hole pos q Party)} (hp : l.Perm l') {x : ι} :
    x ∈ footprint (l.map Hole.patch) ↔ x ∈ footprint (l'.map Hole.patch) :=
  ⟨fun ⟨p, hp', hx⟩ => ⟨p, (hp.map _).subset hp', hx⟩,
    fun ⟨p, hp', hx⟩ => ⟨p, (hp.map _).symm.subset hp', hx⟩⟩

/-- For two arbitrary frames, the set `Z` of `eq:exchange-Z` is computed from the frames
themselves. -/
theorem mem_ofFrames_exchangeEnv (F₁ F₂ : Frame pos q Party) (Y : Finset ι)
    (hside : ∀ h ∈ F₁.holes ++ F₂.holes,
      (h.patch.outer : Set ι) ⊆ Y ∨ Disjoint (h.patch.outer : Set ι) Y) (P : Party) {x : ι} :
    x ∈ (ofFrames F₁ F₂ Y hside).exchangeEnv P ↔
      ¬(F₁.owner x = P ∧ F₂.owner x = P) ∨ x ∈ F₁.outerHoles ∨ x ∈ F₂.outerHoles := by
  rw [mem_exchangeEnv]
  exact Iff.or Iff.rfl (Iff.or (mem_footprint_perm (List.filter_append_perm _ _))
    (mem_footprint_perm (List.filter_append_perm _ _)))

/-- **Lemma 6.6 (two-sheet exchange), frames with holes in any order.** Let `F₁`, `F₂` be encoded
frames and `Y` the physical sample of a region such that every hole's outer footprint lies in `Y`
or avoids it. With `Z`, `T`, `E` computed from the two frames (`mem_ofFrames_exchangeEnv`), if
`I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, some contraction `C` from the two-sheet layout of
`F₁`, `F₂` to that of the exchanged frames satisfies
`‖C (Ω_{F₁} ⊗ Ω_{F₂}) - Ω_{F₁'} ⊗ Ω_{F₂'}‖ ≤ 4 L^{-30}`. It is the implemented map `exchangeOp`
after the canonical identification of tag orderings (`exists_tagEquiv_of_perm`).

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 74–75 and 460–479;
proof lines 481–561. -/
theorem exists_exchange_ofFrames [NeZero q] (F₁ F₂ : Frame pos q Party) (Y : Finset ι)
    (hside : ∀ h ∈ F₁.holes ++ F₂.holes,
      (h.patch.outer : Set ι) ⊆ Y ∨ Disjoint (h.patch.outer : Set ι) Y) (P : Party)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ} (hL : 0 < L)
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω
      ((ofFrames F₁ F₂ Y hside).tSet P) ((ofFrames F₁ F₂ Y hside).eSet P) ≤ L ^ (-60 : ℤ)) :
    ∃ C : Matrix ((ofFrames F₁ F₂ Y hside).newFrame₁.Layout ×
        (ofFrames F₁ F₂ Y hside).newFrame₂.Layout) (F₁.Layout × F₂.Layout) ℂ,
      ‖C‖ ≤ 1 ∧
      ‖act C (vecKron (F₁.refVec Ω) (F₂.refVec Ω)) -
        vecKron ((ofFrames F₁ F₂ Y hside).newFrame₁.refVec Ω)
          ((ofFrames F₁ F₂ Y hside).newFrame₂.refVec Ω)‖ ≤ 4 * L ^ (-30 : ℤ) := by
  set X := ofFrames F₁ F₂ Y hside
  obtain ⟨σ, -, hC, -, herr⟩ := X.exchange P hΩ hL hI
  obtain ⟨e₁, he₁⟩ := exists_tagEquiv_of_perm F₁.disjoint (List.filter_append_perm
    (outsideRegion Y) F₁.holes).symm
  obtain ⟨e₂, he₂⟩ := exists_tagEquiv_of_perm F₂.disjoint (List.filter_append_perm
    (outsideRegion Y) F₂.holes).symm
  set G : F₁.Layout × F₂.Layout ≃ X.frame₁.Layout × X.frame₂.Layout :=
    (e₁.prodCongr (Equiv.refl _)).prodCongr (e₂.prodCongr (Equiv.refl _))
  have hK : F₁.encoder ⊗ₖ F₂.encoder = (X.frame₁.encoder ⊗ₖ X.frame₂.encoder).submatrix G id := by
    rw [Frame.encoder, Frame.encoder, ← frameEncoder_submatrix_of_rawProd_eq e₁ he₁,
      ← frameEncoder_submatrix_of_rawProd_eq e₂ he₂]
    rfl
  refine ⟨X.exchangeOp P σ * (G.symm.toPEquiv.toMatrix : Matrix _ _ ℂ),
    l2_opNorm_mul_le_one hC (l2_opNorm_toMatrix_toPEquiv_le _), ?_⟩
  have hv : act (G.symm.toPEquiv.toMatrix : Matrix _ _ ℂ) (vecKron (F₁.refVec Ω) (F₂.refVec Ω)) =
      vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω) := by
    rw [Frame.refVec, Frame.refVec, Frame.refVec, Frame.refVec, ← act_kronecker_vecKron,
      ← act_kronecker_vecKron, ← act_mul, hK, PEquiv.toMatrix_toPEquiv_mul, submatrix_submatrix]
    simp
  rw [act_mul, hv]
  exact herr

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
