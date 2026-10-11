/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.EffectCircuitReplacement

/-! # Operator error for elimination of pair effects

The replacement circuit is compared with the original circuit tensored with
one fixed normalized auxiliary vector. Its operator error is at most twice
the gate budget times the original number of expanded gate occurrences.

Source: polynomial-PEPS, `04-compression.tex`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace EffectCircuit
/-- The original chronological circuit with the fixed auxiliary preparation
at every expanded gate occurrence, without rescaling its original operator.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
def referenceEval (m : ℕ) : {a b : Layout P} → (w : EffectCircuit a b) →
    Mem a →L[ℂ] Mem (w.auxiliary m ++ b)
  | _, _, .id a => .id ℂ (Mem a)
  | _, _, .comp w v => castOutputMap (List.append_assoc _ _ _).symm
      (retainMap (w.auxiliary m) (v.referenceEval m) ∘L w.referenceEval m)
  | _, _, .localMap p ha hb A tail => (Word.localMap p ha hb A tail).eval
  | _, _, @EffectCircuit.gate _ _ _ owner a b L tail =>
      castOutputMap (gate_auxiliary_layout owner m L tail)
        (gateMemoryMap owner a (gateOut m L) tail
          ((prepGate m L).eval ∘L PairEffect.gate (toGate L)))
  | _, _, .swap t u tail => (Word.swap t u tail).eval
  | _, _, .frame t w => (SourceCircuit.exchangeBlocks [t] (w.auxiliary m) _).eval ∘L
      (w.referenceEval m).lTensor t.space

/-- The original circuit with normalized fixed auxiliaries remains a contraction.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem norm_referenceEval_le_one {a b : Layout P} (w : EffectCircuit a b)
    (hw : w.IsAllowed) (m : ℕ) : ‖w.referenceEval m‖ ≤ 1 := by
  induction w with
  | id => exact norm_id_le
  | @comp a b d w v ihw ihv =>
      exact (norm_castOutputMap
        (List.append_assoc (w.auxiliary m) (v.auxiliary m) d).symm
        (retainMap (w.auxiliary m) (v.referenceEval m) ∘L w.referenceEval m)).trans_le
          (norm_comp_le_one ((norm_retainMap_le _ _).trans (ihv hw.2)) (ihw hw.1))
  | localMap p ha hb A tail =>
      exact Word.norm_eval_le_one (.localMap p ha hb A tail) hw
  | @gate C _ owner a b L tail =>
      exact (norm_castOutputMap (gate_auxiliary_layout owner m L tail)
        (gateMemoryMap owner a (gateOut m L) tail
          ((prepGate m L).eval ∘L PairEffect.gate (toGate L)))).trans_le
            ((norm_gateMemoryMap_le _ _ _ _ _).trans
              (norm_comp_le_one (Word.norm_eval_le_one _ (isAllowed_prepGate m L hw.1)) hw.2))
  | swap t u tail => exact Word.norm_eval_le_one (.swap t u tail) trivial
  | frame t w ih =>
      exact norm_comp_le_one
        (SourceCircuit.norm_eval_le_one _ (SourceCircuit.isAllowed_exchangeBlocks _ _ _))
        ((norm_lTensor_le _ _).trans (ih hw))
end EffectCircuit

/-- The spectator vector is arbitrary, including vectors entangled with other memories.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 210–217. -/
theorem gateMemoryMap_tmul {C : Type} (owner : C ↪ P) (a b : Layout C)
    (tail : Layout P) (A : Mem a →L[ℂ] Mem b) (x : Mem a) (y : Mem tail) :
    gateMemoryMap owner a b tail A
      ((appendIso (Layout.mapOwner owner a) tail).symm
        (Layout.mapOwnerIso owner a x ⊗ₜ[ℂ] y)) =
      (appendIso (Layout.mapOwner owner b) tail).symm
        (Layout.mapOwnerIso owner b (A x) ⊗ₜ[ℂ] y) := by
  simp only [gateMemoryMap, comp_apply, isoL_apply,
    LinearIsometryEquiv.apply_symm_apply, rTensor_tmul,
    LinearIsometryEquiv.symm_apply_apply]

private theorem memCongr_apply_heq {a b : Layout P} (h : a = b) (x : Mem a) :
    HEq (Layout.memCongr h x) x := by
  cases h
  rfl

private theorem mapOwner_apply_heq {C : Type} (owner : C → P)
    {a b : Layout C} (h : a = b) {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq (Layout.mapOwnerIso owner a x) (Layout.mapOwnerIso owner b y) := by
  cases h
  cases hxy
  rfl

/-- Relabelling the owners of a pure preparation preserves its independently
prepared source vector. Source: polynomial-PEPS 04-compression.tex, lines 103–112. -/
theorem preparation_mapOwner_heq {C : Type} (owner : C → P)
    {a b : Layout C} (w : Word a b) (hw : w.IsPreparation) (x : Mem a) :
    HEq (Layout.mapOwnerIso owner b (w.eval x))
      ((appendIso (Layout.mapOwner owner w.sources.layout) (Layout.mapOwner owner a)).symm
        (Layout.mapOwnerIso owner w.sources.layout w.sources.vector ⊗ₜ[ℂ]
          Layout.mapOwnerIso owner a x)) := by
  have he := w.eval_isPreparation_heq hw x
  rw [SourceInventory.eval_prepare_eq_appendIso_symm] at he
  have hm := mapOwner_apply_heq owner (w.output_of_isPreparation hw) he
  exact hm.trans ((memCongr_apply_heq (Layout.mapOwner_append owner w.sources.layout a)
    (Layout.mapOwnerIso owner (w.sources.layout ++ a)
      ((appendIso w.sources.layout a).symm (w.sources.vector ⊗ₜ[ℂ] x)))).symm.trans
    (heq_of_eq (Layout.mapOwnerIso_append_tmul owner w.sources.layout a w.sources.vector x)))

private theorem append_tmul_heq {a a' b b' : Layout P} (ha : a = a') (hb : b = b')
    {x : Mem a} {x' : Mem a'} {y : Mem b} {y' : Mem b'}
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((appendIso a b).symm (x ⊗ₜ[ℂ] y))
      ((appendIso a' b').symm (x' ⊗ₜ[ℂ] y')) := by
  cases ha
  cases hb
  cases hx
  cases hy
  rfl

/-- The ideal replacement of one actual gate prepares precisely the recorded
auxiliary sources and leaves every spectator vector arbitrary.
Source: polynomial-PEPS 04-compression.tex, lines 103–112 and 210–217. -/
theorem gateMemoryMap_auxiliary_tmul {C : Type} [Fintype C]
    (owner : C ↪ P) {a b : Layout C} (m : ℕ) (L : PartyGate a b) (tail : Layout P)
    (h : Layout.mapOwner owner (gateOut m L) ++ tail =
      Layout.mapOwner owner (prepGate m L).sources.layout ++ (Layout.mapOwner owner b ++ tail))
    (x : Mem a) (y : Mem tail) :
    Layout.memCongr h
      (gateMemoryMap owner a (gateOut m L) tail ((prepGate m L).eval ∘L gate (toGate L))
        ((appendIso (Layout.mapOwner owner a) tail).symm
          (Layout.mapOwnerIso owner a x ⊗ₜ[ℂ] y))) =
      (appendIso (Layout.mapOwner owner (prepGate m L).sources.layout)
        (Layout.mapOwner owner b ++ tail)).symm
          (Layout.mapOwnerIso owner (prepGate m L).sources.layout
            (prepGate m L).sources.vector ⊗ₜ[ℂ]
            (EffectCircuit.gate owner L tail).eval
              ((appendIso (Layout.mapOwner owner a) tail).symm
                (Layout.mapOwnerIso owner a x ⊗ₜ[ℂ] y))) := by
  have hb : Layout.mapOwner owner (gateOut m L) =
      Layout.mapOwner owner (prepGate m L).sources.layout ++ Layout.mapOwner owner b := by
    exact (congrArg (Layout.mapOwner owner)
      ((prepGate m L).output_of_isPreparation (isPreparation_prepGate m L))).trans
      (Layout.mapOwner_append owner _ _)
  rw [show (EffectCircuit.gate owner L tail).eval =
    gateMemoryMap owner a b tail (gate (toGate L)) from rfl,
    gateMemoryMap_tmul, gateMemoryMap_tmul]
  have hp := preparation_mapOwner_heq owner (prepGate m L)
    (isPreparation_prepGate m L) (gate (toGate L) x)
  have he := append_tmul_heq hb rfl hp (HEq.rfl : HEq y y)
  exact eq_of_heq ((memCongr_apply_heq h _).trans (he.trans
    (appendIso_assoc_symm_heq
      (Layout.mapOwner owner (prepGate m L).sources.layout)
      (Layout.mapOwner owner b) tail
      (Layout.mapOwnerIso owner (prepGate m L).sources.layout (prepGate m L).sources.vector)
      (Layout.mapOwnerIso owner b (gate (toGate L) x)) y).symm))

/-- As an operator identity, the ideal replacement is the original gate tensored
with its actual fresh auxiliary vector. This holds on all input vectors, without
any tensor factorization hypothesis.
Source: polynomial-PEPS 04-compression.tex, lines 103–112 and 210–217. -/
theorem gateMemoryMap_auxiliary_identity {C : Type} [Fintype C]
    (owner : C ↪ P) {a b : Layout C} (m : ℕ) (L : PartyGate a b) (tail : Layout P)
    (h : Layout.mapOwner owner (gateOut m L) ++ tail =
      Layout.mapOwner owner (prepGate m L).sources.layout ++ (Layout.mapOwner owner b ++ tail)) :
    isoL (Layout.memCongr h) ∘L
      gateMemoryMap owner a (gateOut m L) tail ((prepGate m L).eval ∘L gate (toGate L)) =
      isoL (appendIso (Layout.mapOwner owner (prepGate m L).sources.layout)
        (Layout.mapOwner owner b ++ tail)).symm ∘L
          appendLeft (Layout.mapOwnerIso owner (prepGate m L).sources.layout
            (prepGate m L).sources.vector) ∘L (EffectCircuit.gate owner L tail).eval := by
  have he : (isoL (Layout.memCongr h) ∘L
      gateMemoryMap owner a (gateOut m L) tail ((prepGate m L).eval ∘L gate (toGate L))) ∘L
        isoL (appendIso (Layout.mapOwner owner a) tail).symm =
      (isoL (appendIso (Layout.mapOwner owner (prepGate m L).sources.layout)
        (Layout.mapOwner owner b ++ tail)).symm ∘L
          appendLeft (Layout.mapOwnerIso owner (prepGate m L).sources.layout
            (prepGate m L).sources.vector) ∘L (EffectCircuit.gate owner L tail).eval) ∘L
        isoL (appendIso (Layout.mapOwner owner a) tail).symm := by
    apply clm_ext_tmul
    intro x y
    simpa only [comp_apply, isoL_apply, appendLeft_apply,
      LinearIsometryEquiv.apply_symm_apply] using
      gateMemoryMap_auxiliary_tmul owner m L tail h
        ((Layout.mapOwnerIso owner a).symm x) y
  ext z
  simpa only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply] using
    DFunLike.congr_fun he (appendIso (Layout.mapOwner owner a) tail z)

/-- The two-factor telescoping inequality for contractions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600. -/
theorem norm_comp_sub_comp_le_one (E F G : HSpace)
    (A C : E →L[ℂ] F) (B D : F →L[ℂ] G) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ‖B ∘L A - D ∘L C‖ ≤ ‖A - C‖ + ‖B - D‖ := by
  have he : B ∘L A - D ∘L C = B ∘L (A - C) + (B - D) ∘L C := by
    simp only [comp_sub, sub_comp]
    abel
  rw [he]
  calc
    _ ≤ ‖B ∘L (A - C)‖ + ‖(B - D) ∘L C‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖A - C‖ + ‖B - D‖ * ‖C‖ :=
      add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ ≤ 1 * ‖A - C‖ + ‖B - D‖ * 1 := add_le_add
      (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hC (norm_nonneg _))
    _ = ‖A - C‖ + ‖B - D‖ := by rw [one_mul, mul_one]
private theorem memory_congr_of_heq {a b : Layout P} (h : a = b)
    {x : Mem a} {y : Mem b} (hxy : HEq x y) : Layout.memCongr h x = y := by
  cases h
  cases hxy
  rfl

/-- A singleton block contains only the indicated vector and a terminal scalar unit. -/
theorem appendIso_singleton_symm_tmul (r : Reg P) (tail : Layout P)
    (x : r.space) (y : Mem tail) :
    (appendIso [r] tail).symm ((x ⊗ₜ[ℂ] (1 : ℂ)) ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] y := by
  change x ⊗ₜ[ℂ] ((appendIso [] tail).symm ((1 : ℂ) ⊗ₜ[ℂ] y)) = x ⊗ₜ[ℂ] y
  simp only [appendIso, LinearIsometryEquiv.symm_symm, TensorProduct.lidIsometry_apply,
    TensorProduct.lid_tmul, one_smul]

/-- Move a retained register behind the auxiliary block in the actual circuit order. -/
theorem SourceCircuit.exchangeHead_tmul (r : Reg P) (rs tail : Layout P)
    (x : r.space) (γ : Mem rs) (y : Mem tail) :
    (exchangeBlocks [r] rs tail).eval (x ⊗ₜ[ℂ] (appendIso rs tail).symm (γ ⊗ₜ[ℂ] y)) =
      (appendIso rs (r :: tail)).symm (γ ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y)) := by
  rw [eval_exchangeBlocks]
  have he := Word.eval_exchangeBlocks_appendIso_symm [r] rs tail
    (x ⊗ₜ[ℂ] (1 : ℂ)) γ y
  rw [appendIso_singleton_symm_tmul r (rs ++ tail) x _,
    appendIso_singleton_symm_tmul r tail x y] at he
  exact he
namespace EffectCircuit
/-- The chronological reference circuit is exactly the original circuit tensored
with its independently prepared auxiliary vector. No input factorization is assumed.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem referenceEval_apply {a b : Layout P} (w : EffectCircuit a b) (m : ℕ) (x : Mem a) :
    w.referenceEval m x = (appendIso (w.auxiliary m) b).symm
      (w.auxiliaryVector m ⊗ₜ[ℂ] w.eval x) := by
  induction w with
  | id => exact (one_smul ℂ x).symm
  | @comp a b d w v ihw ihv =>
      change Layout.memCongr (List.append_assoc (w.auxiliary m) (v.auxiliary m) d).symm
        (retainMap (w.auxiliary m) (v.referenceEval m) (w.referenceEval m x)) =
        (appendIso (w.auxiliary m ++ v.auxiliary m) d).symm
          ((appendIso (w.auxiliary m) (v.auxiliary m)).symm
            (w.auxiliaryVector m ⊗ₜ[ℂ] v.auxiliaryVector m) ⊗ₜ[ℂ] v.eval (w.eval x))
      rw [ihw x, retainMap_tmul, ihv (w.eval x)]
      exact memory_congr_of_heq _ (appendIso_assoc_symm_heq _ _ _ _ _ _)
  | localMap => exact (one_smul ℂ _).symm
  | @gate C _ owner a b L tail =>
      exact DFunLike.congr_fun
        (gateMemoryMap_auxiliary_identity owner m L tail (gate_auxiliary_layout owner m L tail)) x
  | swap => exact (one_smul ℂ _).symm
  | frame r w ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v =>
          change (SourceCircuit.exchangeBlocks [r] (w.auxiliary m) _).eval
            ((w.referenceEval m).lTensor r.space (u ⊗ₜ[ℂ] v)) = _
          rw [lTensor_tmul, ih v]
          exact SourceCircuit.exchangeHead_tmul r _ _ u _ _
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
end EffectCircuit
/-- Layout transport preserves the difference between the actual circuit map
and a comparison operator on the same literal output registers. -/
theorem SourceCircuit.norm_eval_castLayouts_sub {a b b' : Layout P}
    (w : SourceCircuit a b) (h : b = b') (B : Mem a →L[ℂ] Mem b) :
    ‖(w.castLayouts rfl h).eval - castOutputMap h B‖ = ‖w.eval - B‖ := by
  rw [SourceCircuit.eval_castLayouts]
  change ‖castOutputMap h w.eval - castOutputMap h B‖ = _
  rw [← castOutputMap_sub, norm_castOutputMap]

namespace EffectCircuit
/-- Replacing the actual chronological expanded gates changes their complete
memory operator by at most the sum of the derived gate errors.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem norm_replacement_sub_reference_le {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    {a b : Layout P} (w : EffectCircuit a b) (hw : w.IsAllowed)
    (hb : w.IsExpansionBounded r S) :
    ‖(w.replacement hδ hw hb).eval - w.referenceEval (stackLength r S δ)‖ ≤
      2 * δ * w.expandedGateCount := by
  let m := stackLength r S δ
  induction w with
  | id a =>
      change ‖ContinuousLinearMap.id ℂ (Mem a).carrier -
        ContinuousLinearMap.id ℂ (Mem a).carrier‖ ≤ 2 * δ * (0 : ℕ)
      simp only [sub_self, norm_zero, Nat.cast_zero, mul_zero, le_refl]
  | @comp a b d w v ihw ihv =>
      apply (SourceCircuit.norm_eval_castLayouts_sub
        (SourceCircuit.comp (w.replacement hδ hw.1 hb.1)
          ((v.replacement hδ hw.2 hb.2).frameList (w.auxiliary m)))
        (List.append_assoc (w.auxiliary m) (v.auxiliary m) d).symm
        (retainMap (w.auxiliary m) (v.referenceEval m) ∘L w.referenceEval m)).trans_le
      change ‖((v.replacement hδ hw.2 hb.2).frameList (w.auxiliary m)).eval ∘L
        (w.replacement hδ hw.1 hb.1).eval -
          retainMap (w.auxiliary m) (v.referenceEval m) ∘L w.referenceEval m‖ ≤ _
      rw [SourceCircuit.eval_frameList]
      have hcomp := norm_comp_sub_comp_le_one
        (Mem a) (Mem (w.auxiliary m ++ b)) (Mem (w.auxiliary m ++ (v.auxiliary m ++ d)))
        (w.replacement hδ hw.1 hb.1).eval (w.referenceEval m)
        (retainMap (w.auxiliary m) (v.replacement hδ hw.2 hb.2).eval)
        (retainMap (w.auxiliary m) (v.referenceEval m))
        ((norm_retainMap_le _ _).trans (SourceCircuit.norm_eval_le_one _
          (v.isAllowed_replacement hδ hw.2 hb.2))) (w.norm_referenceEval_le_one hw.1 m)
      have hret : ‖retainMap (w.auxiliary m) (v.replacement hδ hw.2 hb.2).eval -
          retainMap (w.auxiliary m) (v.referenceEval m)‖ ≤
          ‖(v.replacement hδ hw.2 hb.2).eval - v.referenceEval m‖ := by
        rw [← retainMap_sub]
        exact norm_retainMap_le _ _
      calc
        _ ≤ _ := hcomp
        _ ≤ 2 * δ * w.expandedGateCount + 2 * δ * v.expandedGateCount :=
          add_le_add (ihw hw.1 hb.1) (hret.trans (ihv hw.2 hb.2))
        _ = _ := by rw [expandedGateCount, Nat.cast_add]; ring
  | localMap p hIn hOut A tail =>
      change ‖(Word.localMap p hIn hOut A tail).eval - (Word.localMap p hIn hOut A tail).eval‖ ≤
        2 * δ * (0 : ℕ)
      simp only [sub_self, norm_zero, Nat.cast_zero, mul_zero, le_refl]
  | @gate C _ owner a b L tail =>
      let G := Classical.choose (exists_prepared_effectReplacement_uniform hδ L
        (fun q hq => ⟨hw.1 q hq, hb.1 q hq⟩) hw.2 hb.2)
      have hGe := Classical.choose_spec (exists_prepared_effectReplacement_uniform hδ L
        (fun q hq => ⟨hw.1 q hq, hb.1 q hq⟩) hw.2 hb.2)
      apply (SourceCircuit.norm_eval_castLayouts_sub
        (SourceCircuit.gate owner G tail) (gate_auxiliary_layout owner m L tail)
        (gateMemoryMap owner a (gateOut m L) tail
          ((prepGate m L).eval ∘L PairEffect.gate (toGate L)))).trans_le
      change ‖gateMemoryMap owner a (gateOut m L) tail G.eval -
        gateMemoryMap owner a (gateOut m L) tail
          ((prepGate m L).eval ∘L PairEffect.gate (toGate L))‖ ≤ 2 * δ * (1 : ℕ)
      rw [← gateMemoryMap_sub, Nat.cast_one, mul_one]
      exact (norm_gateMemoryMap_le _ _ _ _ _).trans hGe.2
  | swap t u tail =>
      change ‖(Word.swap t u tail).eval - (Word.swap t u tail).eval‖ ≤ 2 * δ * (0 : ℕ)
      simp only [sub_self, norm_zero, Nat.cast_zero, mul_zero, le_refl]
  | @frame t a b w ih =>
      let E := (SourceCircuit.exchangeBlocks [t] (w.auxiliary m) b).eval
      change ‖E ∘L ((w.replacement hδ hw hb).eval).lTensor t.space -
        E ∘L (w.referenceEval m).lTensor t.space‖ ≤ 2 * δ * w.expandedGateCount
      rw [← comp_sub, ← lTensor_sub]
      calc
        _ ≤ ‖E‖ * ‖((w.replacement hδ hw hb).eval - w.referenceEval m).lTensor t.space‖ :=
          opNorm_comp_le _ _
        _ ≤ 1 * ‖((w.replacement hδ hw hb).eval - w.referenceEval m).lTensor t.space‖ :=
          mul_le_mul_of_nonneg_right (SourceCircuit.norm_eval_le_one _
            (SourceCircuit.isAllowed_exchangeBlocks _ _ _)) (norm_nonneg _)
        _ ≤ ‖(w.replacement hδ hw hb).eval - w.referenceEval m‖ := by
          rw [one_mul]
          exact norm_lTensor_le _ _
        _ ≤ _ := ih hw hb
end EffectCircuit
end TNLean.PEPS.PairEffect
