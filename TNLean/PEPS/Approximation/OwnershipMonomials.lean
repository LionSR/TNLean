/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrontRegisters
import TNLean.PEPS.Approximation.TwoSheetExchange

/-!
# Births, deaths and exchange corrections as allowed monomials

Lemma 6.5 of the polynomial-PEPS manuscript asserts that a homogeneous birth is a bounded change
involving only `P∘` and `Q∘`: at `P∘` apply `V` on `U` and contract `T B_T` with `⟨s|`, supply
the normalized pair state `s` on `T B_T` with `T` now held by `Q∘` and `B_T` still held by `P∘`,
and apply `Vᴴ` to `B_T B_E` at `P∘`.  The death uses one normalized pair effect `⟨s|` on `T B_T`
held by `Q∘` and `P∘` instead.  Lemma 6.6 asserts that the corrections of a two-sheet exchange
are private contractions at `P∘`.

This file writes these procedures as allowed monomials on a party layout
(`TNLean.PEPS.Approximation.PartyWord`, `TNLean.PEPS.Approximation.PartyLayout`) and proves that
their operators are the canonical maps of `TNLean.PEPS.Approximation.HomogeneousOwnership` and
`TNLean.PEPS.Approximation.TwoSheetExchange`.

The raw registers of `T` and those of `U` are written as one register each, and the remaining
registers (those of `E`, the tags, and any other sheet) form an arbitrary layout `ℓ`, untouched
by the monomial.  This grouping is a convention, as for the pair effects of
`PairEffect.PartyChain`: the registers of `T`, and those of `U`, have a single owner before and
after the change (`Frame.owner_eq_of_notMem_birthEnv`,
`TwoSheetExchange.owner_eq_of_notMem_exchangeEnv`), and regrouping registers of one party is a
private unitary.

## Main definitions

* `EncodedFrame.birthWord`, `EncodedFrame.birthPrivateWord` : the birth, for `Q∘ ≠ P∘` and for
  `Q∘ = P∘`.
* `EncodedFrame.deathChain`, `EncodedFrame.deathPrivateChain` : the death.
* `EncodedFrame.correctionWord` : a private contraction on two registers of one party.

## Main results

* `EncodedFrame.pairHeadIso_birthWord_eval`, `EncodedFrame.pairHeadIso_deathChain_eval` : the
  operator of the birth and of the death is `Kᴴ K ⊗ 1` with `K = ⟨s| (1_T ⊗ V)`, the canonical
  map `B = 1_E ⊗ Kᴴ K` of `eq:birth-map` on the registers of `T ∪ U`.
* `EncodedFrame.Frame.birth_monomial`, `EncodedFrame.Frame.death_monomial` : Lemma 6.5
  `lem:birth`, including the bounded-change clause.
* `EncodedFrame.TwoSheetExchange.exchange_correction_monomial` : the corrections `D_U F_A` of
  Lemma 6.6 form one private contraction at `P∘`.

## Scope

**Scope restriction (renaming of an exchange):** Lemma 6.6 implements the exchange by private
contractions and a register renaming.  Here the corrections `D_U F_A` are proved to be one private
contraction at `P∘` on the registers of `U` of both sheets
(`TwoSheetExchange.exchange_correction_monomial`), and the renaming `ℛ` is the canonical
identification of tensor factors `TwoSheetExchange.renameEquiv`, which keeps every register at its
party.  Writing `ℛ` as a word of exchanges of tensor factors needs a layout with one register per
site and per tag, which is not formalized.  Documented in
`docs/paper-gaps/polypeps_ownership_change_monomials.tex`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.5 `lem:birth` and Lemma 6.6
  `lem:exchange`, `05-frames.tex`, lines 396–570; allowed monomials, `04-compression.tex`,
  lines 32–35.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

open PairEffect

/-! ### The birth and the death for abstract systems -/

section Abstract

variable {Party : Type} {T U BT BE : Type} [Fintype T] [DecidableEq T] [Fintype U]
  [DecidableEq U] [Fintype BT] [DecidableEq BT] [Fintype BE] [DecidableEq BE]

/-- **The birth as a monomial.** On the registers `T` and `U` of `P∘`: the private contraction
`⟨s| (1_T ⊗ V)` at `P∘` from `T U` to `B_E`, the normalized pair source `s` on a fresh register
`T` of `Q∘` and a fresh register `B_T` of `P∘`, and the private contraction `Vᴴ` at `P∘` from
`B_T B_E` to `U`.  The registers `ℓ` are untouched.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 413–419. -/
def birthWord {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ)
    (ℓ : Layout Party) :
    Word (⟨P, euc T⟩ :: ⟨P, euc U⟩ :: ℓ) (⟨Q, euc T⟩ :: ⟨P, euc U⟩ :: ℓ) :=
  .comp (.comp (Word.localMap (ℓ₁ := [⟨P, euc T⟩, ⟨P, euc U⟩]) (ℓ₂ := [⟨P, euc BE⟩]) P
      owner_of_mem_two owner_of_mem_one (matLocal₂₁ P (birthKernel V s)) ℓ)
      (.source hQP (euc T) (euc BT) (pairVec (WithLp.toLp 2 s)) (⟨P, euc BE⟩ :: ℓ)))
    (.frame ⟨Q, euc T⟩ (Word.localMap (ℓ₁ := [⟨P, euc BT⟩, ⟨P, euc BE⟩]) (ℓ₂ := [⟨P, euc U⟩])
      P owner_of_mem_two owner_of_mem_one (matLocal₂₁ P Vᴴ) ℓ))

/-- **The birth when the two owners agree**: the private contraction `Kᴴ K` at `P∘`
(`05-frames.tex`, lines 447–449). -/
def birthPrivateWord (P : Party) (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) (ℓ : Layout Party) :
    Word (⟨P, euc T⟩ :: ⟨P, euc U⟩ :: ℓ) (⟨P, euc T⟩ :: ⟨P, euc U⟩ :: ℓ) :=
  Word.localMap (ℓ₁ := [⟨P, euc T⟩, ⟨P, euc U⟩]) (ℓ₂ := [⟨P, euc T⟩, ⟨P, euc U⟩]) P
    owner_of_mem_two owner_of_mem_two (matLocal₂₂ P ((birthKernel V s)ᴴ * birthKernel V s)) ℓ

/-- **The death as a monomial.** On the register `T` of `Q∘` and the register `U` of `P∘`: the
private isometry `V` at `P∘` from `U` to `B_T B_E`, the normalized pair effect `⟨s|` on `T` of
`Q∘` and `B_T` of `P∘`, and the private contraction `(1_T ⊗ Vᴴ)(|s⟩ ⊗ 1)` at `P∘` from `B_E` to
`T U`, which reinserts `s` wholly at `P∘` and applies `Vᴴ`.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 439–446. -/
def deathChain {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ)
    (ℓ : Layout Party) :
    PartyChain (⟨Q, euc T⟩ :: ⟨P, euc U⟩ :: ℓ) (⟨P, euc T⟩ :: ⟨P, euc U⟩ :: ℓ) :=
  .effect hQP T BT (⟨P, euc BE⟩ :: ℓ)
    (.frame ⟨Q, euc T⟩ (Word.localMap (ℓ₁ := [⟨P, euc U⟩]) (ℓ₂ := [⟨P, euc BT⟩, ⟨P, euc BE⟩])
      P owner_of_mem_one owner_of_mem_two (matLocal₁₂ P V) ℓ))
    (WithLp.toLp 2 s)
    (.final (Word.localMap (ℓ₁ := [⟨P, euc BE⟩]) (ℓ₂ := [⟨P, euc T⟩, ⟨P, euc U⟩]) P
      owner_of_mem_one owner_of_mem_two (matLocal₁₂ P (birthKernel V s)ᴴ) ℓ))

/-- **The death when the two owners agree**: the private contraction `Kᴴ K` at `P∘`. -/
def deathPrivateChain (P : Party) (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ)
    (ℓ : Layout Party) :
    PartyChain (⟨P, euc T⟩ :: ⟨P, euc U⟩ :: ℓ) (⟨P, euc T⟩ :: ⟨P, euc U⟩ :: ℓ) :=
  .final (birthPrivateWord P V s ℓ)

/-! #### Norms -/

omit [DecidableEq BT] [DecidableEq BE] in
theorem norm_birthKernel_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) : ‖birthKernel V s‖ ≤ 1 := by
  classical
  have h : birthKernel V s = reindex (Equiv.punitProd BE)
      ((Equiv.prodPUnit T).prodCongr (Equiv.refl U)) (birthEffect (E := Unit) V s) := by
    ext b ⟨t, u⟩
    rw [birthEffect_eq_submatrix]
    simp [teuShuffle]
  rw [h]
  exact (l2_opNorm_reindex_le _ _ _).trans (norm_birthEffect_le_one hV hs)

omit [DecidableEq BT] [DecidableEq BE] in
theorem norm_le_one_of_isIsometry {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry) : ‖V‖ ≤ 1 :=
  l2_opNorm_le_one_of_conjTranspose_mul_self_le_one (by
    rw [show Vᴴ * V = 1 from hV]; exact (IsStarProjection.one _).norm_le)

omit [DecidableEq T] [DecidableEq BT] in
theorem norm_toLp_of_star_dotProduct {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) :
    ‖(WithLp.toLp 2 s : EuclideanSpace ℂ (T × BT))‖ = 1 := by
  have h2 := norm_toLp_sq s
  rw [hs, Complex.one_re] at h2
  nlinarith [norm_nonneg (WithLp.toLp 2 s : EuclideanSpace ℂ (T × BT))]

theorem isAllowed_birthWord {P Q : Party} (hQP : Q ≠ P) {V : Matrix (BT × BE) U ℂ}
    (hV : V.IsIsometry) {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) (ℓ : Layout Party) :
    (birthWord hQP V s ℓ).IsAllowed :=
  ⟨⟨(norm_matLocal₂₁_le _ _).trans (norm_birthKernel_le_one hV hs),
      (norm_pairVec _).trans (norm_toLp_of_star_dotProduct hs)⟩,
    (norm_matLocal₂₁_le _ _).trans ((l2_opNorm_conjTranspose V).trans_le
      (norm_le_one_of_isIsometry hV))⟩

omit [DecidableEq BT] [DecidableEq BE] in
theorem isAllowed_birthPrivateWord (P : Party) {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) (ℓ : Layout Party) :
    (birthPrivateWord P V s ℓ).IsAllowed := by
  classical
  refine (norm_matLocal₂₂_le _ _).trans ?_
  have h := norm_birthKernel_le_one hV hs
  have h' := h
  rw [← l2_opNorm_conjTranspose] at h'
  exact l2_opNorm_mul_le_one h' h

omit [DecidableEq BT] [DecidableEq T] in
theorem isAllowed_deathChain {P Q : Party} (hQP : Q ≠ P) {V : Matrix (BT × BE) U ℂ}
    (hV : V.IsIsometry) {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) (ℓ : Layout Party) :
    (deathChain hQP V s ℓ).IsAllowed := by
  classical
  exact ⟨(norm_matLocal₁₂_le _ _).trans (norm_le_one_of_isIsometry hV),
    norm_toLp_of_star_dotProduct hs,
    (norm_matLocal₁₂_le _ _).trans ((l2_opNorm_conjTranspose _).trans_le
      (norm_birthKernel_le_one hV hs))⟩

/-! #### Operators -/

/-- The operator `η ↦ Σ (t ⊗ Vᴴ (b ⊗ k))` obtained by preparing `η = Σ t ⊗ b` next to `k` and
applying `Vᴴ` to `b ⊗ k`. -/
def sourceThenAdjoint (V : Matrix (BT × BE) U ℂ) (k : EuclideanSpace ℂ BE) :
    EuclideanSpace ℂ T ⊗[ℂ] EuclideanSpace ℂ BT →L[ℂ] EuclideanSpace ℂ (T × U) :=
  isoL (pairIso T U) ∘L
    (matL Vᴴ ∘L isoL (pairIso BT BE) ∘L appendRight k).lTensor (EuclideanSpace ℂ T)

omit [DecidableEq T] [DecidableEq U] in
/-- Preparing the pair vector `s` next to `k` and applying `Vᴴ` gives `Kᴴ k` with
`K = ⟨s| (1_T ⊗ V)`. -/
theorem sourceThenAdjoint_pairVec (V : Matrix (BT × BE) U ℂ) (k : EuclideanSpace ℂ BE)
    (η : EuclideanSpace ℂ (T × BT)) :
    sourceThenAdjoint V k (pairVec η) = matL (birthKernel V η.ofLp)ᴴ k := by
  suffices h : ∀ x : EuclideanSpace ℂ T ⊗[ℂ] EuclideanSpace ℂ BT,
      sourceThenAdjoint V k x = matL (birthKernel V (pairIso T BT x).ofLp)ᴴ k by
    rw [h, pairVec, LinearIsometryEquiv.apply_symm_apply]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      have h : sourceThenAdjoint V k (a ⊗ₜ b) =
          pairIso T U (a ⊗ₜ matL Vᴴ (pairIso BT BE (b ⊗ₜ k))) :=
        rfl
      rw [h]
      ext ⟨t, u⟩
      simp only [pairIso_tmul_apply, matL_apply, mulVec, dotProduct, conjTranspose_apply,
        birthKernel, of_apply, star_sum, star_mul, star_star, Fintype.sum_prod_type,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      ring
  | add x y hx hy =>
      rw [map_add, hx, hy, ← _root_.add_apply, ← matL_add, ← conjTranspose_add]
      congr 3
      ext b tu
      simp only [birthKernel, of_apply, Matrix.add_apply, map_add, WithLp.ofLp_add, Pi.add_apply,
        star_add, add_mul, ← Finset.sum_add_distrib]

omit [DecidableEq T] [DecidableEq U] in
/-- Preparing the pair vector next to `k ⊗ w` and applying `Vᴴ` at `P∘`. -/
theorem pairHeadIso_frame_localMap_source {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ)
    (ℓ : Layout Party) (k : EuclideanSpace ℂ BE) (w : Mem ℓ)
    (η : EuclideanSpace ℂ T ⊗[ℂ] EuclideanSpace ℂ BT) :
    pairHeadIso ℓ ((Word.frame ⟨Q, euc T⟩ (Word.localMap (ℓ₁ := [⟨P, euc BT⟩, ⟨P, euc BE⟩])
      (ℓ₂ := [⟨P, euc U⟩]) P owner_of_mem_two owner_of_mem_one (matLocal₂₁ P Vᴴ) ℓ)).eval
        ((Word.source hQP (euc T) (euc BT) η (⟨P, euc BE⟩ :: ℓ)).eval (k ⊗ₜ w))) =
      sourceThenAdjoint V k η ⊗ₜ w := by
  rw [Word.eval_source, ContinuousLinearMap.comp_apply, appendLeft_apply]
  induction η using TensorProduct.inductionOn with
  | tmul a b =>
      have hb : appendIso [⟨P, euc BT⟩, ⟨P, euc BE⟩] ℓ (b ⊗ₜ (k ⊗ₜ w)) =
          (twoIso P P BT BE).symm (pairIso BT BE (b ⊗ₜ k)) ⊗ₜ w := by
        rw [twoIso_symm_pairIso]
        exact appendIso_two_tmul (⟨P, euc BT⟩ : Reg Party) ⟨P, euc BE⟩ ℓ b k w
      rw [assocL_tmul, Word.eval_frame, lTensor_tmul,
        ← (appendIso [⟨P, euc BT⟩, ⟨P, euc BE⟩] ℓ).symm_apply_apply (b ⊗ₜ (k ⊗ₜ w)), hb,
        eval_localMap₂₁, pairHeadIso_tmul]
      rfl
  | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, map_add, hx, hy, map_add,
      TensorProduct.add_tmul]

/-- **The birth monomial has the canonical operator.** On the registers of `T ∪ U`, identified
with `ℂ^{T × U}` before and after, the birth word acts as `Kᴴ K ⊗ 1` with `K = ⟨s| (1_T ⊗ V)`;
by `birthOp_eq_submatrix` this is the canonical map `B = 1_E ⊗ Kᴴ K` of `eq:birth-map`.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 413–426. -/
theorem pairHeadIso_birthWord_eval {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ)
    (s : T × BT → ℂ) (ℓ : Layout Party) (z : Mem (⟨P, euc T⟩ :: ⟨P, euc U⟩ :: ℓ)) :
    pairHeadIso ℓ ((birthWord hQP V s ℓ).eval z) =
      (matL ((birthKernel V s)ᴴ * birthKernel V s)).rTensor (Mem ℓ) (pairHeadIso ℓ z) := by
  obtain ⟨y, rfl⟩ : ∃ y : EuclideanSpace ℂ (T × U) ⊗[ℂ] Mem ℓ, z = (pairHeadIso ℓ).symm y :=
    ⟨pairHeadIso ℓ z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  induction y using TensorProduct.inductionOn with
  | tmul v w =>
      have hz : (pairHeadIso (p := P) (q := P) ℓ).symm (v ⊗ₜ w) =
          (appendIso [⟨P, euc T⟩, ⟨P, euc U⟩] ℓ).symm ((twoIso P P T U).symm v ⊗ₜ w) := by
        rw [LinearIsometryEquiv.symm_apply_eq, appendIso_two_symm]
      rw [hz, birthWord, Word.eval_comp, ContinuousLinearMap.comp_apply, Word.eval_comp,
        ContinuousLinearMap.comp_apply, eval_localMap₂₁, pairHeadIso_frame_localMap_source,
        sourceThenAdjoint_pairVec, rTensor_tmul, matL_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The contraction `b ⊗ e ↦ ⟨η, t ⊗ b⟩ e` of `B_T ⊗ B_E` against the pair bra `⟨η|` next to
`t`. -/
def effectNext (η : EuclideanSpace ℂ (T × BT)) (t : EuclideanSpace ℂ T) :
    EuclideanSpace ℂ BT ⊗[ℂ] EuclideanSpace ℂ BE →L[ℂ] EuclideanSpace ℂ BE :=
  isoL (TensorProduct.lidIsometry ℂ (EuclideanSpace ℂ BE)) ∘L
    (innerSL ℂ η ∘L isoL (pairIso T BT) ∘L appendLeft t).rTensor (EuclideanSpace ℂ BE)

omit [DecidableEq T] [DecidableEq U] [DecidableEq BT] [DecidableEq BE] in
theorem effectNext_apply (η : EuclideanSpace ℂ (T × BT)) (t : EuclideanSpace ℂ T)
    (y : EuclideanSpace ℂ BT ⊗[ℂ] EuclideanSpace ℂ BE) (be : BE) :
    effectNext η t y be = ∑ i : T × BT, star (η i) * t i.1 * pairIso BT BE y (i.2, be) := by
  induction y using TensorProduct.inductionOn with
  | tmul b e =>
      simp only [effectNext, ContinuousLinearMap.comp_apply, rTensor_tmul, isoL_apply,
        appendLeft_apply, innerSL_apply_apply, TensorProduct.lidIsometry_apply,
        TensorProduct.lid_tmul, PiLp.smul_apply, smul_eq_mul, pairIso_tmul_apply,
        PiLp.inner_apply, RCLike.inner_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [RCLike.star_def]
      ring
  | add x y hx hy =>
      rw [map_add, PiLp.add_apply, hx, hy, map_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PiLp.add_apply]
      ring

omit [DecidableEq BT] [DecidableEq BE] in
/-- The death word on `T ⊗ U`: applying `V` and the pair effect `⟨η|` at `t ⊗ u` gives
`K (t ⊗ u)` with `K = ⟨η| (1_T ⊗ V)`. -/
theorem effectNext_matL (V : Matrix (BT × BE) U ℂ) (η : EuclideanSpace ℂ (T × BT))
    (t : EuclideanSpace ℂ T) (u : EuclideanSpace ℂ U) :
    effectNext η t ((pairIso BT BE).symm (matL V u)) =
      matL (birthKernel V η.ofLp) (pairIso T U (t ⊗ₜ u)) := by
  ext be
  rw [effectNext_apply, LinearIsometryEquiv.apply_symm_apply, matL_apply]
  simp only [matL_apply, mulVec, dotProduct, birthKernel, of_apply, pairIso_tmul_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun bt _ => ?_
  ring

omit [DecidableEq BT] in
/-- **The death monomial has the canonical operator.** On the registers of `T ∪ U`, identified
with `ℂ^{T × U}` before and after, the death acts as `Kᴴ K ⊗ 1` with `K = ⟨s| (1_T ⊗ V)`, the
same canonical map as the birth, with the reverse input and output ownership.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 439–446. -/
theorem pairHeadIso_deathChain_eval {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ)
    (s : T × BT → ℂ) (ℓ : Layout Party) (z : Mem (⟨Q, euc T⟩ :: ⟨P, euc U⟩ :: ℓ)) :
    pairHeadIso ℓ ((deathChain hQP V s ℓ).toEffectChain.eval z) =
      (matL ((birthKernel V s)ᴴ * birthKernel V s)).rTensor (Mem ℓ) (pairHeadIso ℓ z) := by
  induction z using tmul₃_induction with
  | tmul t u w =>
      have hstep : ∀ y : EuclideanSpace ℂ BT ⊗[ℂ] EuclideanSpace ℂ BE,
          pairHeadIso ℓ ((Word.localMap (ℓ₁ := [⟨P, euc BE⟩]) (ℓ₂ := [⟨P, euc T⟩, ⟨P, euc U⟩]) P
            owner_of_mem_one owner_of_mem_two (matLocal₁₂ P (birthKernel V s)ᴴ) ℓ).eval
            (effectMap (WithLp.toLp 2 s) (Mem (⟨P, euc BE⟩ :: ℓ))
              (pairHeadIso (⟨P, euc BE⟩ :: ℓ) (t ⊗ₜ (appendIso [⟨P, euc BT⟩, ⟨P, euc BE⟩] ℓ).symm
                ((twoIso P P BT BE).symm (pairIso BT BE y) ⊗ₜ w))))) =
            matL (birthKernel V s)ᴴ (effectNext (WithLp.toLp 2 s) t y) ⊗ₜ w := by
        intro y
        induction y using TensorProduct.inductionOn with
        | tmul b e =>
            have hb : (appendIso [⟨P, euc BT⟩, ⟨P, euc BE⟩] ℓ).symm
                ((twoIso P P BT BE).symm (pairIso BT BE (b ⊗ₜ e)) ⊗ₜ w) =
                (b ⊗ₜ (e ⊗ₜ w) : Mem (⟨P, euc BT⟩ :: ⟨P, euc BE⟩ :: ℓ)) := by
              rw [LinearIsometryEquiv.symm_apply_eq, twoIso_symm_pairIso]
              exact (appendIso_two_tmul (⟨P, euc BT⟩ : Reg Party) ⟨P, euc BE⟩ ℓ b e w).symm
            rw [hb, pairHeadIso_tmul, effectMap_tmul, map_smul, eval_localMap₁₂,
              LinearIsometryEquiv.map_smul, appendIso_two_symm]
            simp only [effectNext, ContinuousLinearMap.comp_apply, rTensor_tmul, isoL_apply,
              appendLeft_apply, innerSL_apply_apply, TensorProduct.lidIsometry_apply,
              TensorProduct.lid_tmul, map_smul, TensorProduct.smul_tmul']
        | add x y hx hy =>
            simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add, hx, hy]
      have hV := eval_localMap₁₂ P V ℓ owner_of_mem_one owner_of_mem_two u w
      change pairHeadIso ℓ ((Word.localMap (ℓ₁ := [⟨P, euc BE⟩]) (ℓ₂ := [⟨P, euc T⟩, ⟨P, euc U⟩]) P
            owner_of_mem_one owner_of_mem_two (matLocal₁₂ P (birthKernel V s)ᴴ) ℓ).eval
            (effectMap (WithLp.toLp 2 s) (Mem (⟨P, euc BE⟩ :: ℓ))
              (pairHeadIso (⟨P, euc BE⟩ :: ℓ) (t ⊗ₜ (Word.localMap (ℓ₁ := [⟨P, euc U⟩])
                (ℓ₂ := [⟨P, euc BT⟩, ⟨P, euc BE⟩]) P owner_of_mem_one owner_of_mem_two
                (matLocal₁₂ P V) ℓ).eval (u ⊗ₜ w))))) = _
      rw [hV, ← LinearIsometryEquiv.apply_symm_apply (pairIso BT BE) (matL V u), hstep,
        effectNext_matL, pairHeadIso_tmul, rTensor_tmul, matL_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [DecidableEq BT] [DecidableEq BE] in
/-- The private birth acts as `Kᴴ K ⊗ 1`. -/
theorem pairHeadIso_birthPrivateWord_eval (P : Party) (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ)
    (ℓ : Layout Party) (z : Mem (⟨P, euc T⟩ :: ⟨P, euc U⟩ :: ℓ)) :
    pairHeadIso ℓ ((birthPrivateWord P V s ℓ).eval z) =
      (matL ((birthKernel V s)ᴴ * birthKernel V s)).rTensor (Mem ℓ) (pairHeadIso ℓ z) :=
  pairHeadIso_eval_localMap₂₂ P _ ℓ _ _ z

/-! #### Parties and pair resources -/

theorem usesOnly_birthWord {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ)
    (s : T × BT → ℂ) (ℓ : Layout Party) : (birthWord hQP V s ℓ).UsesOnly {P, Q} := by
  simp [birthWord, Word.UsesOnly]

theorem sourceCount_birthWord {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ)
    (s : T × BT → ℂ) (ℓ : Layout Party) : (birthWord hQP V s ℓ).sourceCount = 1 :=
  rfl

omit [DecidableEq BT] [DecidableEq BE] in
theorem usesOnly_birthPrivateWord (P : Party) (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ)
    (ℓ : Layout Party) : (birthPrivateWord P V s ℓ).UsesOnly {P} :=
  Set.mem_singleton P

omit [DecidableEq BT] [DecidableEq BE] in
theorem sourceCount_birthPrivateWord (P : Party) (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ)
    (ℓ : Layout Party) : (birthPrivateWord P V s ℓ).sourceCount = 0 :=
  rfl

omit [DecidableEq BT] [DecidableEq T] in
theorem usesOnly_deathChain {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ)
    (s : T × BT → ℂ) (ℓ : Layout Party) : (deathChain hQP V s ℓ).UsesOnly {P, Q} := by
  simp [deathChain, PartyChain.UsesOnly, Word.UsesOnly]

omit [DecidableEq BT] [DecidableEq T] in
theorem counts_deathChain {P Q : Party} (hQP : Q ≠ P) (V : Matrix (BT × BE) U ℂ)
    (s : T × BT → ℂ) (ℓ : Layout Party) :
    (deathChain hQP V s ℓ).sourceCount = 0 ∧ (deathChain hQP V s ℓ).toEffectChain.effectCount = 1 :=
  ⟨rfl, rfl⟩

end Abstract

/-! ### Birth and death in an encoded frame -/

section FrameMonomial

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}

/-- The canonical map of a birth on the sheet is `1_E ⊗ Kᴴ K` with `K = ⟨s| (1_T ⊗ V)`, in the
coordinates `(e, (t, u))` (`birthOp_eq_submatrix`). -/
theorem sheetBirthOp_eq_submatrix {T E : Finset ι} (h : Disjoint T E) (σ : SplittingData q T E) :
    sheetBirthOp h σ =
      ((1 : Matrix (E → Fin q) (E → Fin q) ℂ) ⊗ₖ
          ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).submatrix
        (teuShuffle _ _ _ ∘ threeSplit q T E h) (teuShuffle _ _ _ ∘ threeSplit q T E h) := by
  rw [sheetBirthOp, birthOp_eq_submatrix, submatrix_submatrix]

namespace Frame

variable (F : Frame pos q Party) {T : Finset ι} {P Q : Party}

/-- The monomial of a birth or a death on the registers of `T` and `U`. -/
theorem exists_birthWord {T E : Finset ι} (P Q : Party) (σ : SplittingData q T E)
    (ℓ : PairEffect.Layout Party) :
    ∃ w : Word (⟨P, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ E)ᶜ → Fin q)⟩ :: ℓ)
        (⟨Q, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ E)ᶜ → Fin q)⟩ :: ℓ),
      w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
      ∀ z, pairHeadIso ℓ (w.eval z) =
        (matL ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).rTensor (Mem ℓ)
          (pairHeadIso ℓ z) := by
  by_cases hQP : Q = P
  · subst hQP
    exact ⟨birthPrivateWord Q σ.V σ.s ℓ, isAllowed_birthPrivateWord Q σ.isIsometry σ.star_s ℓ,
      Set.mem_insert Q _, (sourceCount_birthPrivateWord Q σ.V σ.s ℓ).trans_le zero_le_one,
      pairHeadIso_birthPrivateWord_eval Q σ.V σ.s ℓ⟩
  · exact ⟨birthWord hQP σ.V σ.s ℓ, isAllowed_birthWord hQP σ.isIsometry σ.star_s ℓ,
      usesOnly_birthWord hQP σ.V σ.s ℓ, (sourceCount_birthWord hQP σ.V σ.s ℓ).le,
      pairHeadIso_birthWord_eval hQP σ.V σ.s ℓ⟩

/-- The monomial of a death on the registers of `T` and `U`. -/
theorem exists_deathChain {T E : Finset ι} (P Q : Party) (σ : SplittingData q T E)
    (ℓ : PairEffect.Layout Party) :
    ∃ M : PartyChain (⟨Q, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ E)ᶜ → Fin q)⟩ :: ℓ)
        (⟨P, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ E)ᶜ → Fin q)⟩ :: ℓ),
      M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧ M.toEffectChain.effectCount ≤ 1 ∧
      ∀ z, pairHeadIso ℓ (M.toEffectChain.eval z) =
        (matL ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).rTensor (Mem ℓ)
          (pairHeadIso ℓ z) := by
  by_cases hQP : Q = P
  · subst hQP
    exact ⟨deathPrivateChain Q σ.V σ.s ℓ, isAllowed_birthPrivateWord Q σ.isIsometry σ.star_s ℓ,
      Set.mem_insert Q _, rfl, zero_le_one, pairHeadIso_birthPrivateWord_eval Q σ.V σ.s ℓ⟩
  · exact ⟨deathChain hQP σ.V σ.s ℓ, isAllowed_deathChain hQP σ.isIsometry σ.star_s ℓ,
      usesOnly_deathChain hQP σ.V σ.s ℓ, (counts_deathChain hQP σ.V σ.s ℓ).1,
      (counts_deathChain hQP σ.V σ.s ℓ).2.le, pairHeadIso_deathChain_eval hQP σ.V σ.s ℓ⟩

/-- **Lemma 6.5 (homogeneous birth), with the bounded-change clause.** In an encoded frame `F`,
let `T` be a set of raw sites owned by `P∘` and disjoint from every outer hole footprint, and let
`E` and `U = Λ ∖ (T ∪ E)` be as in `eq:birth-partition`. If `I_Ω(T:E) ≤ L^{-60}` for a unit vector
`Ω`, there are splitting data such that:

* the canonical map `B` is `1_E ⊗ Kᴴ K` with `K = ⟨s| (1_T ⊗ V)` on the registers of `T ∪ U`,
  satisfies `(1 ⊗ B) K_F = K_{F'} B` for the frame `F'` in which `T` is owned by `Q∘`, and
  `‖(1 ⊗ B) Ω_F - Ω_{F'}‖ ≤ L^{-30}`;
* the registers of `U` are owned by `P∘` before and after the birth, and those of `T` by `P∘`
  before and by `Q∘` after;
* the birth is a bounded change involving only `P∘` and `Q∘`: for every layout `ℓ` of the other
  registers, `Kᴴ K ⊗ 1` is the operator of an allowed word with at most one normalized pair
  source, from the layout with `T` and `U` held by `P∘` to the layout with `T` held by `Q∘`; for
  `Q∘ ≠ P∘` it is a private contraction at `P∘`, one pair source between `Q∘` and `P∘`, and a
  private contraction at `P∘` (`birthWord`).

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–407; proof lines
413–437 and 447–449. -/
theorem birth_monomial [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ =
        ((1 : Matrix (F.birthEnv P → Fin q) (F.birthEnv P → Fin q) ℂ) ⊗ₖ
          ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).submatrix
          (teuShuffle _ _ _ ∘ threeSplit q T (F.birthEnv P) (F.disjoint_birthEnv hTP hTH))
          (teuShuffle _ _ _ ∘ threeSplit q T (F.birthEnv P) (F.disjoint_birthEnv hTP hTH)) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * F.encoder =
        (F.changeOwner T Q).encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) (F.refVec Ω) -
        (F.changeOwner T Q).refVec Ω‖ ≤ L ^ (-30 : ℤ) ∧
      (∀ x ∉ T ∪ F.birthEnv P, F.owner x = P ∧ (F.changeOwner T Q).owner x = P) ∧
      (∀ x ∈ T, (F.changeOwner T Q).owner x = Q) ∧
      ∀ ℓ : PairEffect.Layout Party,
        ∃ w : Word (⟨P, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩ :: ℓ)
            (⟨Q, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩ :: ℓ),
          w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
          ∀ z, pairHeadIso ℓ (w.eval z) =
            (matL ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).rTensor (Mem ℓ)
              (pairHeadIso ℓ z) := by
  obtain ⟨σ, hσ, -, -, hK, herr⟩ := F.birth (Q := Q) hTP hTH hΩ hI
  refine ⟨σ, hσ, sheetBirthOp_eq_submatrix _ σ, hK, herr, fun x hx => ?_, fun x hx => ?_,
    fun ℓ => exists_birthWord P Q σ ℓ⟩
  · have hxE : x ∉ F.birthEnv P := fun h => hx (Finset.mem_union_right _ h)
    have hxT : x ∉ T := fun h => hx (Finset.mem_union_left _ h)
    refine ⟨F.owner_eq_of_notMem_birthEnv hxE, ?_⟩
    change (if x ∈ T then Q else F.owner x) = P
    simp only [hxT, ↓reduceIte]
    exact F.owner_eq_of_notMem_birthEnv hxE
  · change (if x ∈ T then Q else F.owner x) = Q
    simp only [hx, ↓reduceIte]

/-- **Lemma 6.5 (homogeneous death), with the bounded-change clause.** Let `F` be the frame
*after* the death, in which `T` is owned by `P∘` and avoids every outer hole footprint, and let
the frame before the death be `F` with `T` owned by `Q∘`. If `I_Ω(T:E) ≤ L^{-60}` for `E`
computed in `F`, there are splitting data such that the canonical map `B = 1_E ⊗ Kᴴ K`, with the
reverse input and output ownership, satisfies `(1 ⊗ B) K_{F_before} = K_F B` and
`‖(1 ⊗ B) Ω_{F_before} - Ω_F‖ ≤ L^{-30}`, and is a bounded change involving only `P∘` and
`Q∘`: for every layout `ℓ` of the other registers, `Kᴴ K ⊗ 1` is the operator of an allowed
monomial without pair sources and with at most one normalized pair effect, from the layout with
`T` held by `Q∘` and `U` by `P∘` to the layout with both held by `P∘`; for `Q∘ ≠ P∘` it is a
private contraction at `P∘`, one pair effect between `Q∘` and `P∘`, and a private contraction at
`P∘` (`deathChain`).

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 407–410; proof lines
439–449. -/
theorem death_monomial [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ =
        ((1 : Matrix (F.birthEnv P → Fin q) (F.birthEnv P → Fin q) ℂ) ⊗ₖ
          ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).submatrix
          (teuShuffle _ _ _ ∘ threeSplit q T (F.birthEnv P) (F.disjoint_birthEnv hTP hTH))
          (teuShuffle _ _ _ ∘ threeSplit q T (F.birthEnv P) (F.disjoint_birthEnv hTP hTH)) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * (F.changeOwner T Q).encoder =
        F.encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) ((F.changeOwner T Q).refVec Ω) -
        F.refVec Ω‖ ≤ L ^ (-30 : ℤ) ∧
      (∀ x ∉ T ∪ F.birthEnv P, F.owner x = P ∧ (F.changeOwner T Q).owner x = P) ∧
      (∀ x ∈ T, (F.changeOwner T Q).owner x = Q) ∧
      ∀ ℓ : PairEffect.Layout Party,
        ∃ M : PartyChain (⟨Q, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩ :: ℓ)
            (⟨P, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩ :: ℓ),
          M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧
          M.toEffectChain.effectCount ≤ 1 ∧
          ∀ z, pairHeadIso ℓ (M.toEffectChain.eval z) =
            (matL ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).rTensor (Mem ℓ)
              (pairHeadIso ℓ z) := by
  obtain ⟨σ, hσ, hB, hK, herr, hown, hT, -⟩ := F.birth_monomial (Q := Q) hTP hTH hΩ hI
  exact ⟨σ, hσ, hB, hK, herr, hown, hT, fun ℓ => exists_deathChain P Q σ ℓ⟩

end Frame

end FrameMonomial

/-! ### The corrections of a two-sheet exchange -/

section Correction

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- The bijection of two copies of the configurations of a set `S` of sites exchanging them at
the sites of `A`. -/
def partSwap (q : ℕ) (S A : Finset ι) : Equiv.Perm ((S → Fin q) × (S → Fin q)) where
  toFun r := (fun v => if (v : ι) ∈ A then r.2 v else r.1 v,
    fun v => if (v : ι) ∈ A then r.1 v else r.2 v)
  invFun r := (fun v => if (v : ι) ∈ A then r.2 v else r.1 v,
    fun v => if (v : ι) ∈ A then r.1 v else r.2 v)
  left_inv r := by
    ext v <;> by_cases hv : (v : ι) ∈ A <;> simp [hv]
  right_inv r := by
    ext v <;> by_cases hv : (v : ι) ∈ A <;> simp [hv]

variable {T E : Finset ι} (h : Disjoint T E)

-- The buffer of two copies of `B_T × B_E` is a fourfold product of function types;
-- synthesizing its decidable equality exceeds the default instance size.
set_option synthInstance.maxSize 512 in
/-- **The corrections of an exchange on the two copies of `U`.** The matrix
`W = (V^{⊗2})ᴴ F_{B_T} V^{⊗2} F_A` of `D_U F_A` on the two copies of `U = Λ ∖ (T ∪ E)`, for
`A ⊆ U`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 503–515. -/
def correctionMatrix (σ : SplittingData q T E) (A : Finset ι) :
    Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ :=
  (σ.V ⊗ₖ σ.V)ᴴ *
      ((bufferSwap (T → Fin q) ((E → Fin q) ⊕ (↥(T ∪ E)ᶜ → Fin q))).toPEquiv.toMatrix :
        Matrix _ _ ℂ) * (σ.V ⊗ₖ σ.V) *
    ((partSwap q (T ∪ E)ᶜ A).toPEquiv.toMatrix : Matrix _ _ ℂ)

set_option synthInstance.maxSize 512 in
theorem norm_correctionMatrix_le_one (σ : SplittingData q T E) (A : Finset ι) :
    ‖correctionMatrix σ A‖ ≤ 1 := by
  have hVV : ‖σ.V ⊗ₖ σ.V‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self_le_one (by
      rw [IsIsometry.kronecker σ.V σ.V σ.isIsometry σ.isIsometry]
      exact (IsStarProjection.one _).norm_le)
  have hVV' := hVV
  rw [← l2_opNorm_conjTranspose] at hVV'
  exact l2_opNorm_mul_le_one (l2_opNorm_mul_le_one (l2_opNorm_mul_le_one hVV'
    (l2_opNorm_toMatrix_toPEquiv_le _)) hVV) (l2_opNorm_toMatrix_toPEquiv_le _)

-- Two copies of the configurations `((t, e), u)` of three regions form a fourfold product of
-- function types; synthesizing their decidable equality exceeds the default instance size.
set_option synthInstance.maxSize 512 in
/-- In the coordinates `threeSplit T E` of both sheets, swapping the sheets at `A ⊆ U` exchanges
the `A`-parts of the two copies of `U`. -/
theorem sheetSwapOp_eq_submatrix_of_subset {A : Finset ι} (hA : A ⊆ (T ∪ E)ᶜ) :
    sheetSwapOp q A =
      (((1 : Matrix (((T → Fin q) × (E → Fin q)) × ((T → Fin q) × (E → Fin q)))
          (((T → Fin q) × (E → Fin q)) × ((T → Fin q) × (E → Fin q))) ℂ) ⊗ₖ
        ((partSwap q (T ∪ E)ᶜ A).toPEquiv.toMatrix : Matrix _ _ ℂ)).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)).submatrix
        (threeSplit₂ h) (threeSplit₂ h) := by
  have hAT : ∀ v : T, (v : ι) ∉ A := fun v hv =>
    Finset.mem_compl.mp (hA hv) (Finset.mem_union_left E v.2)
  have hAE : ∀ v : E, (v : ι) ∉ A := fun v hv =>
    Finset.mem_compl.mp (hA hv) (Finset.mem_union_right T v.2)
  have he : (threeSplit₂ (q := q) h).symm.trans ((sheetSwap q A).trans (threeSplit₂ h)) =
      (Equiv.prodProdProdComm _ _ _ _).trans
        (((Equiv.refl _).prodCongr (partSwap q (T ∪ E)ᶜ A)).trans
          (Equiv.prodProdProdComm _ _ _ _).symm) := by
    refine Equiv.ext fun w => ?_
    obtain ⟨⟨⟨t₁, e₁⟩, u₁⟩, ⟨⟨t₂, e₂⟩, u₂⟩⟩ := w
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
      funext v <;> simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
        Prod.map_fst, Prod.map_snd, threeSplit_apply_fst_fst, threeSplit_apply_fst_snd,
        threeSplit_apply_snd, sheetSwap, Equiv.coe_fn_mk, partSwap, Equiv.prodProdProdComm,
        Equiv.coe_fn_symm_mk, Equiv.refl_apply]
    · rw [ite_eq_right (hAT v)]; exact threeSplit_symm_apply_of_mem_left h _ _ _ v.2
    · rw [ite_eq_right (hAE v)]; exact threeSplit_symm_apply_of_mem_right h _ _ _ v.2
    · by_cases hv : (v : ι) ∈ A <;> simp only [hv, ↓reduceIte] <;>
        exact threeSplit_symm_apply_of_notMem h _ _ _ (Finset.mem_compl.mp v.2)
    · rw [ite_eq_right (hAT v)]; exact threeSplit_symm_apply_of_mem_left h _ _ _ v.2
    · rw [ite_eq_right (hAE v)]; exact threeSplit_symm_apply_of_mem_right h _ _ _ v.2
    · by_cases hv : (v : ι) ∈ A <;> simp only [hv, ↓reduceIte] <;>
        exact threeSplit_symm_apply_of_notMem h _ _ _ (Finset.mem_compl.mp v.2)
  have key : ((sheetSwap q A).toPEquiv.toMatrix : Matrix _ _ ℂ).submatrix (threeSplit₂ h).symm
      (threeSplit₂ h).symm =
      ((1 : Matrix (((T → Fin q) × (E → Fin q)) × ((T → Fin q) × (E → Fin q)))
          (((T → Fin q) × (E → Fin q)) × ((T → Fin q) × (E → Fin q))) ℂ) ⊗ₖ
        ((partSwap q (T ∪ E)ᶜ A).toPEquiv.toMatrix : Matrix _ _ ℂ)).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _) := by
    rw [toMatrix_toPEquiv_submatrix, Equiv.symm_symm, he, ← PEquiv.toMatrix_refl,
      ← Equiv.toPEquiv_refl, ← toMatrix_toPEquiv_prodCongr, toMatrix_toPEquiv_submatrix]
  rw [← key, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  rfl

set_option synthInstance.maxSize 512 in
/-- **The corrections of an exchange act on the two copies of `U` alone.** For `A ⊆ U`,
`D_U F_A = 1 ⊗ W` with `W = correctionMatrix σ A`, in the coordinates in which the two copies of
`T × E` come first.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 503–515. -/
theorem sheetBufferCorrection_mul_sheetSwapOp_eq (σ : SplittingData q T E) {A : Finset ι}
    (hA : A ⊆ (T ∪ E)ᶜ) :
    sheetBufferCorrection h σ * sheetSwapOp q A =
      (((1 : Matrix (((T → Fin q) × (E → Fin q)) × ((T → Fin q) × (E → Fin q)))
          (((T → Fin q) × (E → Fin q)) × ((T → Fin q) × (E → Fin q))) ℂ) ⊗ₖ
        correctionMatrix σ A).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)).submatrix
        (threeSplit₂ h) (threeSplit₂ h) := by
  rw [sheetSwapOp_eq_submatrix_of_subset h hA, sheetBufferCorrection, bufferCorrection,
    submatrix_mul_equiv, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]
  rfl

end Correction

/-- **The corrections as a private contraction.** A private contraction at `P∘` on two
registers `ℂ^U` of `P∘`, given by a matrix `W`. -/
def correctionWord {Party : Type} {U : Type} [Fintype U] [DecidableEq U] (P : Party)
    (W : Matrix (U × U) (U × U) ℂ) (ℓ : PairEffect.Layout Party) :
    Word (⟨P, euc U⟩ :: ⟨P, euc U⟩ :: ℓ) (⟨P, euc U⟩ :: ⟨P, euc U⟩ :: ℓ) :=
  Word.localMap (ℓ₁ := [⟨P, euc U⟩, ⟨P, euc U⟩]) (ℓ₂ := [⟨P, euc U⟩, ⟨P, euc U⟩]) P
    owner_of_mem_two owner_of_mem_two (matLocal₂₂ P W) ℓ

namespace TwoSheetExchange

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}
  (X : TwoSheetExchange pos q Party) (P : Party)

set_option synthInstance.maxSize 512 in
/-- **Lemma 6.6 (two-sheet exchange): the corrections are a private contraction at `P∘`.** For
splitting data of the exchange partition, the corrections `D_U F_A` of the implemented map
`C = D_U F_A ℛ` are `1 ⊗ W` with `W = correctionMatrix σ A` acting on the two copies of `U`, the
registers of `U` are held by `P∘` on both sheets before and after the exchange, and for every
layout `ℓ` of the other registers `W ⊗ 1` is the operator of one allowed private contraction at
`P∘` on the two registers `ℂ^U` of `P∘`.  The renaming `ℛ` is the identification of tensor
factors `renameEquiv`, which keeps every register at its party.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 474–479; proof
lines 485–515 and 556–561. -/
theorem exchange_correction_monomial (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.aSet P) =
      (((1 : Matrix (((X.tSet P → Fin q) × (X.eSet P → Fin q)) ×
            ((X.tSet P → Fin q) × (X.eSet P → Fin q)))
          (((X.tSet P → Fin q) × (X.eSet P → Fin q)) ×
            ((X.tSet P → Fin q) × (X.eSet P → Fin q))) ℂ) ⊗ₖ
        correctionMatrix σ (X.aSet P)).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)).submatrix
        (threeSplit₂ (X.disjoint_tSet_eSet P)) (threeSplit₂ (X.disjoint_tSet_eSet P)) ∧
      (∀ x ∉ X.tSet P ∪ X.eSet P, (X.owner₁ x = P ∧ X.owner₂ x = P) ∧
        (X.newFrame₁.owner x = P ∧ X.newFrame₂.owner x = P)) ∧
      ∀ ℓ : PairEffect.Layout Party,
        ∃ w : Word (⟨P, euc (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q)⟩ ::
              ⟨P, euc (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q)⟩ :: ℓ)
            (⟨P, euc (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q)⟩ ::
              ⟨P, euc (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q)⟩ :: ℓ),
          w.IsAllowed ∧ w.UsesOnly {P} ∧ w.sourceCount = 0 ∧
          ∀ z, pairHeadIso ℓ (w.eval z) =
            (matL (correctionMatrix σ (X.aSet P))).rTensor (Mem ℓ) (pairHeadIso ℓ z) := by
  refine ⟨sheetBufferCorrection_mul_sheetSwapOp_eq _ σ (X.aSet_subset_compl P), fun x hx => ?_,
    fun ℓ => ⟨correctionWord P (correctionMatrix σ (X.aSet P)) ℓ,
      (norm_matLocal₂₂_le _ _).trans (norm_correctionMatrix_le_one σ _), Set.mem_singleton P, rfl,
      pairHeadIso_eval_localMap₂₂ P _ ℓ _ _⟩⟩
  rw [tSet_union_eSet] at hx
  exact ⟨X.owner_eq_of_notMem_exchangeEnv P hx, X.newOwner_eq_of_notMem_exchangeEnv P hx⟩

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
