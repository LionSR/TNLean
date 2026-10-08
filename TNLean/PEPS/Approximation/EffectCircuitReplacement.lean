/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.EffectCircuitPreparation

/-!
# Source-only replacement with retained auxiliary registers

Each original nonprivate occurrence is replaced by a prepared-source expansion.
The auxiliary registers of preceding occurrences remain spectators.
Source: polynomial-PEPS, `04-compression.tex`, lines 199–229.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-effectcircuitreplacement-01
TNLean.PEPS.PairEffect.EffectCircuit.IsExpansionBounded
Provenance-ID: 8769-source-resource-effectcircuitreplacement-02
TNLean.PEPS.PairEffect.EffectCircuit.auxiliary
Provenance-ID: 8769-source-resource-effectcircuitreplacement-03
TNLean.PEPS.PairEffect.EffectCircuit.auxiliaryVector
Provenance-ID: 8769-source-resource-effectcircuitreplacement-04
TNLean.PEPS.PairEffect.EffectCircuit.expandedGateCount
Provenance-ID: 8769-source-resource-effectcircuitreplacement-05
TNLean.PEPS.PairEffect.EffectCircuit.isAllowed_replacement
Provenance-ID: 8769-source-resource-effectcircuitreplacement-06
TNLean.PEPS.PairEffect.EffectCircuit.norm_auxiliaryVector
Provenance-ID: 8769-source-resource-effectcircuitreplacement-07
TNLean.PEPS.PairEffect.EffectCircuit.replacement
Provenance-ID: 8769-source-resource-effectcircuitreplacement-08
TNLean.PEPS.PairEffect.SourceCircuit.eval_frameList
Provenance-ID: 8769-source-resource-effectcircuitreplacement-09
TNLean.PEPS.PairEffect.SourceCircuit.isAllowed_exchangeBlocks
Provenance-ID: 8769-source-resource-effectcircuitreplacement-10
TNLean.PEPS.PairEffect.appendIso_assoc_symm_heq
Provenance-ID: 8769-source-resource-effectcircuitreplacement-11
TNLean.PEPS.PairEffect.castOutputMap
Provenance-ID: 8769-source-resource-effectcircuitreplacement-12
TNLean.PEPS.PairEffect.castOutputMap_sub
Provenance-ID: 8769-source-resource-effectcircuitreplacement-13
TNLean.PEPS.PairEffect.exists_prepared_effectReplacement_native
Provenance-ID: 8769-source-resource-effectcircuitreplacement-14
TNLean.PEPS.PairEffect.exists_prepared_effectReplacement_uniform
Provenance-ID: 8769-source-resource-effectcircuitreplacement-15
TNLean.PEPS.PairEffect.gateMemoryMap
Provenance-ID: 8769-source-resource-effectcircuitreplacement-16
TNLean.PEPS.PairEffect.gateMemoryMap_sub
Provenance-ID: 8769-source-resource-effectcircuitreplacement-17
TNLean.PEPS.PairEffect.gate_auxiliary_layout
Provenance-ID: 8769-source-resource-effectcircuitreplacement-18
TNLean.PEPS.PairEffect.norm_castOutputMap
Provenance-ID: 8769-source-resource-effectcircuitreplacement-19
TNLean.PEPS.PairEffect.norm_gateMemoryMap_le
Provenance-ID: 8769-source-resource-effectcircuitreplacement-20
TNLean.PEPS.PairEffect.norm_retainMap_le
Provenance-ID: 8769-source-resource-effectcircuitreplacement-21
TNLean.PEPS.PairEffect.replacementCoefficients
Provenance-ID: 8769-source-resource-effectcircuitreplacement-22
TNLean.PEPS.PairEffect.retainMap
Provenance-ID: 8769-source-resource-effectcircuitreplacement-23
TNLean.PEPS.PairEffect.retainMap_sub
Provenance-ID: 8769-source-resource-effectcircuitreplacement-24
TNLean.PEPS.PairEffect.retainMap_tmul
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}

namespace EffectCircuit
/-- The actual auxiliary register occurrences retained in chronological order.
Source: polynomial-PEPS 04-compression.tex, lines 199–217. -/
def auxiliary (m : ℕ) : {a b : Layout P} → EffectCircuit a b → Layout P
  | _, _, .id _ => []
  | _, _, .comp w v => w.auxiliary m ++ v.auxiliary m
  | _, _, .localMap .. => []
  | _, _, @EffectCircuit.gate _ _ _ owner _ _ L _ =>
      Layout.mapOwner owner (prepGate m L).sources.layout
  | _, _, .swap .. => []
  | _, _, .frame _ w => w.auxiliary m

/-- Count the original expanded gate occurrences before replacing their effects.
Source: polynomial-PEPS 04-compression.tex, lines 199–217. -/
def expandedGateCount : {a b : Layout P} → EffectCircuit a b → ℕ
  | _, _, .id _ => 0
  | _, _, .comp w v => w.expandedGateCount + v.expandedGateCount
  | _, _, .localMap .. => 0
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ _ _ => 1
  | _, _, .swap .. => 0
  | _, _, .frame _ w => w.expandedGateCount

/-- Bounds on the original monomial expansions, before the insertion averages
are expanded. No restriction is imposed on private memory dimensions.
Source: polynomial-PEPS 04-compression.tex, lines 199–208. -/
def IsExpansionBounded (r : ℕ) (S : ℝ) : {a b : Layout P} → EffectCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsExpansionBounded r S ∧ v.IsExpansionBounded r S
  | _, _, .localMap .. => True
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ L _ =>
      (∀ q ∈ L, q.2.toEffectChain.effectCount ≤ r) ∧ (L.map fun q => ‖q.1‖).sum ≤ S
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsExpansionBounded r S
end EffectCircuit
/-- One rescaling factor is applied to every branch of this original gate occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 210–212. -/
def replacementCoefficients {C : Type} {a b : Layout C}
    (m : ℕ) (δ : ℝ) (L : PartyGate a b) : Fin (wordList m L).length → ℂ :=
  fun i => (((1 + δ)⁻¹ : ℝ) : ℂ) * ((wordList m L).get i).1

/-- The actual prepared gate approximates the original gate followed by its
fixed auxiliary preparation, in the literal output register space.
Source: polynomial-PEPS 04-compression.tex, lines 199–212. -/
theorem exists_prepared_effectReplacement_native {C : Type} [Finite C]
    {a b : Layout C} {m r : ℕ} (hm : m ≠ 0) (L : PartyGate a b)
    (hL : ∀ q ∈ L, q.2.IsAllowed ∧ q.2.toEffectChain.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) {δ : ℝ}
    (hδ : r / Real.sqrt m * (L.map fun q => ‖q.1‖).sum ≤ δ) :
    ∃ G : PreparedSourceGate (replacementCoefficients m δ L) a (gateOut m L),
      isoL (gateIso m L) ∘L G.eval =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m (toGate L) ∧
      ‖G.eval - (prepGate m L).eval ∘L gate (toGate L)‖ ≤ 2 * δ := by
  obtain ⟨G, he, herr⟩ := exists_prepared_effectReplacement hm L hL hG hδ
  refine ⟨G, he, ?_⟩
  have hprep : isoL (gateIso m L) ∘L (prepGate m L).eval =
      appendRight (inventoryVector m (toGate L)) :=
    ContinuousLinearMap.ext (fun x => gateIso_prepGate m L x)
  rw [← (gateIso m L).toLinearIsometry.norm_toContinuousLinearMap_comp,
    comp_sub, ← comp_assoc, hprep]
  exact herr

/-- Choose the stack length from the original effect and coefficient bounds.
The resulting actual prepared gate retains every original monomial occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 199–212. -/
theorem exists_prepared_effectReplacement_uniform {C : Type} [Finite C]
    {a b : Layout C} {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (L : PartyGate a b)
    (hL : ∀ q ∈ L, q.2.IsAllowed ∧ q.2.toEffectChain.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) (hS : (L.map fun q => ‖q.1‖).sum ≤ S) :
    ∃ G : PreparedSourceGate (replacementCoefficients (stackLength r S δ) δ L)
        a (gateOut (stackLength r S δ) L),
      isoL (gateIso (stackLength r S δ) L) ∘L G.eval =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) (toGate L) ∧
      ‖G.eval - (prepGate (stackLength r S δ) L).eval ∘L gate (toGate L)‖ ≤ 2 * δ := by
  have hsum : 0 ≤ (L.map fun q => ‖q.1‖).sum := List.sum_nonneg fun x hx => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  have hle : r / Real.sqrt (stackLength r S δ) * (L.map fun q => ‖q.1‖).sum ≤ δ :=
    (mul_le_mul_of_nonneg_left hS (by positivity)).trans
      (stackLength_spec r (hsum.trans hS) hδ)
  exact exists_prepared_effectReplacement_native (stackLength_ne_zero r S δ) L hL hG hle
namespace EffectCircuit
/-- Replace the actual chronological gates, retaining each preceding auxiliary
register as a spectator. No evaluation or approximation identity is input data.
Source: polynomial-PEPS 04-compression.tex, lines 199–217. -/
def replacement {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) :
    {a b : Layout P} → (w : EffectCircuit a b) → w.IsAllowed → w.IsExpansionBounded r S →
      SourceCircuit a (w.auxiliary (stackLength r S δ) ++ b)
  | _, _, .id a, _, _ => .id a
  | _, _, .comp w v, hw, hb =>
      (SourceCircuit.comp (w.replacement hδ hw.1 hb.1)
        ((v.replacement hδ hw.2 hb.2).frameList (w.auxiliary (stackLength r S δ)))).castLayouts
          rfl (List.append_assoc _ _ _).symm
  | _, _, .localMap p ha hb A tail, _, _ => .localMap p ha hb A tail
  | _, _, @EffectCircuit.gate _ C _ owner a b L tail, hw, hb => by
      let G := Classical.choose (exists_prepared_effectReplacement_uniform hδ L
        (fun q hq => ⟨hw.1 q hq, hb.1 q hq⟩) hw.2 hb.2)
      exact (SourceCircuit.gate owner G tail).castLayouts rfl (by
        rw [(prepGate (stackLength r S δ) L).output_of_isPreparation
          (isPreparation_prepGate _ L), Layout.mapOwner_append, List.append_assoc]
        rfl)
  | _, _, .swap r s tail, _, _ => .swap r s tail
  | _, _, .frame t w, hw, hb =>
      .comp (.frame t (w.replacement hδ hw hb))
        (SourceCircuit.exchangeBlocks [t] (w.auxiliary (stackLength r S δ)) _)
end EffectCircuit
namespace SourceCircuit
/-- Reordering retained and original registers is an allowed exact operation.
Source: polynomial-PEPS 04-compression.tex, lines 210–217. -/
theorem isAllowed_exchangeBlocks (a b tail : Layout P) :
    (exchangeBlocks a b tail).IsAllowed :=
  isAllowed_ofLocalWord _ _ (Word.isAllowed_exchangeBlocks a b tail)
end SourceCircuit

namespace EffectCircuit
/-- The constructed replacement consists of allowed source-prepared gates and
exact private operations, with the original participating parties unchanged.
Source: polynomial-PEPS 04-compression.tex, lines 199–217. -/
theorem isAllowed_replacement {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    {a b : Layout P} (w : EffectCircuit a b) (hw : w.IsAllowed)
    (hb : w.IsExpansionBounded r S) : (w.replacement hδ hw hb).IsAllowed := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      exact (SourceCircuit.isAllowed_castLayouts _ _ _).mpr
        ⟨ihw hw.1 hb.1, SourceCircuit.isAllowed_frameList _ (ihv hw.2 hb.2) _⟩
  | localMap => exact hw
  | @gate C _ owner a b L tail =>
      simp only [replacement, SourceCircuit.isAllowed_castLayouts]
      trivial
  | swap => trivial
  | frame t w ih =>
      exact ⟨ih hw hb, SourceCircuit.isAllowed_exchangeBlocks _ _ _⟩

/-- The fixed auxiliary vector of the original chronological gate occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 103–112 and 210–217. -/
def auxiliaryVector (m : ℕ) : {a b : Layout P} → (w : EffectCircuit a b) →
    Mem (w.auxiliary m)
  | _, _, .id _ => (1 : ℂ)
  | _, _, .comp w v => (appendIso (w.auxiliary m) (v.auxiliary m)).symm
      (w.auxiliaryVector m ⊗ₜ[ℂ] v.auxiliaryVector m)
  | _, _, .localMap .. => (1 : ℂ)
  | _, _, @EffectCircuit.gate _ _ _ owner _ _ L _ =>
      Layout.mapOwnerIso owner (prepGate m L).sources.layout (prepGate m L).sources.vector
  | _, _, .swap .. => (1 : ℂ)
  | _, _, .frame _ w => w.auxiliaryVector m

/-- Every retained auxiliary factor is normalized. Private operations contribute
only the scalar unit and impose no dimension bound.
Source: polynomial-PEPS 04-compression.tex, lines 103–112 and 210–217. -/
theorem norm_auxiliaryVector {a b : Layout P} (w : EffectCircuit a b)
    (hw : w.IsAllowed) (m : ℕ) : ‖w.auxiliaryVector m‖ = 1 := by
  induction w with
  | id => change ‖(1 : ℂ)‖ = 1; exact norm_one
  | comp w v ihw ihv =>
      change ‖(appendIso (w.auxiliary m) (v.auxiliary m)).symm
        (w.auxiliaryVector m ⊗ₜ[ℂ] v.auxiliaryVector m)‖ = 1
      rw [(appendIso (w.auxiliary m) (v.auxiliary m)).symm.norm_map,
        TensorProduct.norm_tmul, ihw hw.1, ihv hw.2, one_mul]
  | localMap => change ‖(1 : ℂ)‖ = 1; exact norm_one
  | @gate C _ owner a b L tail =>
      exact (Layout.mapOwnerIso owner _).norm_map _ |>.trans
        (SourceInventory.norm_vector _ (Word.isNormalized_sources _ (isAllowed_prepGate m L hw.1)))
  | swap => change ‖(1 : ℂ)‖ = 1; exact norm_one
  | frame t w ih => exact ih hw
end EffectCircuit
/-- Retain an arbitrary preceding memory while an operator acts on the tail. -/
def retainMap {a b : Layout P} (rs : Layout P) (A : Mem a →L[ℂ] Mem b) :
    Mem (rs ++ a) →L[ℂ] Mem (rs ++ b) :=
  isoL (appendIso rs b).symm ∘L A.lTensor (Mem rs) ∘L isoL (appendIso rs a)

/-- The retained tensor factor is untouched by the actual operator. -/
theorem retainMap_tmul {a b : Layout P} (rs : Layout P) (A : Mem a →L[ℂ] Mem b)
    (x : Mem rs) (y : Mem a) :
    retainMap rs A ((appendIso rs a).symm (x ⊗ₜ[ℂ] y)) =
      (appendIso rs b).symm (x ⊗ₜ[ℂ] A y) := by
  simp only [retainMap, comp_apply, isoL_apply, LinearIsometryEquiv.apply_symm_apply,
    lTensor_tmul]

/-- Framing by register occurrences is exactly tensoring by their joint identity. -/
theorem SourceCircuit.eval_frameList {a b : Layout P} (w : SourceCircuit a b)
    (rs : Layout P) : (w.frameList rs).eval = retainMap rs w.eval := by
  have he : (w.frameList rs).eval ∘L isoL (appendIso rs a).symm =
      retainMap rs w.eval ∘L isoL (appendIso rs a).symm := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact (w.eval_frameList_tmul rs x y).trans (retainMap_tmul rs w.eval x y).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  ext z
  simpa only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply] using
    DFunLike.congr_fun he (appendIso rs a z)

/-- Retaining an arbitrary memory cannot increase the operator norm. -/
theorem norm_retainMap_le {a b : Layout P} (rs : Layout P) (A : Mem a →L[ℂ] Mem b) :
    ‖retainMap rs A‖ ≤ ‖A‖ := by
  change ‖isoL (appendIso rs b).symm ∘L
    (A.lTensor (Mem rs) ∘L isoL (appendIso rs a))‖ ≤ ‖A‖
  rw [(appendIso rs b).symm.toLinearIsometry.norm_toContinuousLinearMap_comp]
  calc
    _ ≤ ‖A.lTensor (Mem rs)‖ * ‖isoL (appendIso rs a)‖ := opNorm_comp_le _ _
    _ ≤ ‖A.lTensor (Mem rs)‖ * 1 := mul_le_mul_of_nonneg_left
      (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _)
    _ ≤ ‖A‖ := by rw [mul_one]; exact norm_lTensor_le _ _

/-- Retaining spectators preserves subtraction of actual operators. -/
theorem retainMap_sub {a b : Layout P} (rs : Layout P) (A B : Mem a →L[ℂ] Mem b) :
    retainMap rs (A - B) = retainMap rs A - retainMap rs B := by
  simp only [retainMap, lTensor_sub, comp_sub, sub_comp]
private theorem cons_tensor_heq (r : Reg P) {a b : Layout P} (h : a = b)
    (u : r.space) {x : Mem a} {y : Mem b} (hxy : HEq x y) :
    HEq (u ⊗ₜ[ℂ] x) (u ⊗ₜ[ℂ] y) := by
  cases h
  cases hxy
  rfl

private theorem memory_add_heq {a b : Layout P} (h : a = b)
    {x y : Mem a} {x' y' : Mem b} (hx : HEq x x') (hy : HEq y y') :
    HEq (x + y) (x' + y') := by
  cases h
  cases hx
  cases hy
  rfl

/-- Associating three adjacent register lists changes no vector or occurrence. -/
theorem appendIso_assoc_symm_heq (a b c : Layout P)
    (x : Mem a) (y : Mem b) (z : Mem c) :
    HEq ((appendIso a (b ++ c)).symm (x ⊗ₜ[ℂ] (appendIso b c).symm (y ⊗ₜ[ℂ] z)))
      ((appendIso (a ++ b) c).symm ((appendIso a b).symm (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)) := by
  induction a with
  | nil =>
      change HEq (x • (appendIso b c).symm (y ⊗ₜ[ℂ] z))
        ((appendIso b c).symm ((x • y) ⊗ₜ[ℂ] z))
      rw [← TensorProduct.smul_tmul', map_smul]
  | cons r a ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v => exact cons_tensor_heq r (List.append_assoc a b c).symm u (ih v)
      | add x y hx hy =>
          simp only [TensorProduct.add_tmul, map_add]
          exact memory_add_heq (List.append_assoc (r :: a) b c).symm hx hy
/-- Transport only the output along an equality of actual register lists. -/
def castOutputMap {a b b' : Layout P} (h : b = b') (A : Mem a →L[ℂ] Mem b) :
    Mem a →L[ℂ] Mem b' := isoL (Layout.memCongr h) ∘L A

/-- Output identification preserves the operator norm. -/
theorem norm_castOutputMap {a b b' : Layout P} (h : b = b') (A : Mem a →L[ℂ] Mem b) :
    ‖castOutputMap h A‖ = ‖A‖ :=
  (Layout.memCongr h).toLinearIsometry.norm_toContinuousLinearMap_comp

/-- Output identification is linear in the actual operator. -/
theorem castOutputMap_sub {a b b' : Layout P} (h : b = b')
    (A B : Mem a →L[ℂ] Mem b) : castOutputMap h (A - B) = castOutputMap h A - castOutputMap h B :=
  comp_sub _ _ _

private theorem norm_isometric_sandwich_le {E F G H : HSpace}
    (e : F ≃ₗᵢ[ℂ] G) (f : H ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] F) :
    ‖isoL e ∘L A ∘L isoL f‖ ≤ ‖A‖ := by
  rw [e.toLinearIsometry.norm_toContinuousLinearMap_comp]
  calc
    _ ≤ ‖A‖ * ‖isoL f‖ := opNorm_comp_le _ _
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left
      (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _)
    _ = ‖A‖ := mul_one _

/-- The actual gate map at its recorded owners and original spectator registers. -/
def gateMemoryMap {C : Type} (owner : C ↪ P) (a b : Layout C) (tail : Layout P)
    (A : Mem a →L[ℂ] Mem b) :
    Mem (Layout.mapOwner owner a ++ tail) →L[ℂ] Mem (Layout.mapOwner owner b ++ tail) :=
  isoL (appendIso (Layout.mapOwner owner b) tail).symm ∘L
    (isoL (Layout.mapOwnerIso owner b) ∘L A ∘L
      isoL (Layout.mapOwnerIso owner a).symm).rTensor (Mem tail) ∘L
      isoL (appendIso (Layout.mapOwner owner a) tail)

/-- Owner coordinates and spectator identities cannot increase a gate norm. -/
theorem norm_gateMemoryMap_le {C : Type} (owner : C ↪ P) (a b : Layout C)
    (tail : Layout P) (A : Mem a →L[ℂ] Mem b) : ‖gateMemoryMap owner a b tail A‖ ≤ ‖A‖ :=
  (norm_isometric_sandwich_le
    (E := HSpace.of (Mem (Layout.mapOwner owner a) ⊗[ℂ] Mem tail))
    (F := HSpace.of (Mem (Layout.mapOwner owner b) ⊗[ℂ] Mem tail))
    (G := Mem (Layout.mapOwner owner b ++ tail))
    (H := Mem (Layout.mapOwner owner a ++ tail)) _ _ _).trans
      ((norm_rTensor_le _ _).trans (norm_isometric_sandwich_le
        (E := Mem a) (F := Mem b) (G := Mem (Layout.mapOwner owner b))
        (H := Mem (Layout.mapOwner owner a)) _ _ A))

/-- The actual owner and spectator construction preserves gate subtraction. -/
theorem gateMemoryMap_sub {C : Type} (owner : C ↪ P) (a b : Layout C)
    (tail : Layout P) (A B : Mem a →L[ℂ] Mem b) :
    gateMemoryMap owner a b tail (A - B) =
      gateMemoryMap owner a b tail A - gateMemoryMap owner a b tail B := by
  simp only [gateMemoryMap, comp_sub, sub_comp, rTensor_sub]

/-- The literal auxiliary output layout of one original gate. -/
theorem gate_auxiliary_layout {C : Type} (owner : C ↪ P)
    {a b : Layout C} (m : ℕ) (L : PartyGate a b) (tail : Layout P) :
    Layout.mapOwner owner (gateOut m L) ++ tail =
      Layout.mapOwner owner (prepGate m L).sources.layout ++
        (Layout.mapOwner owner b ++ tail) := by
  exact (congrArg (fun d => Layout.mapOwner owner d ++ tail)
    ((prepGate m L).output_of_isPreparation (isPreparation_prepGate m L))).trans
      (by rw [Layout.mapOwner_append, List.append_assoc])
end TNLean.PEPS.PairEffect
