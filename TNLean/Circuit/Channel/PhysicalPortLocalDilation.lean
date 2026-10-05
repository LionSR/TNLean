/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.RegisterEnvironment
import TNLean.Circuit.Channel.PhysicalPortEmbedding
import Mathlib.Algebra.BigOperators.Fin

/-!
# Placing a fresh-environment dilation at its original spatial site

Both the selected old wires and every newly appended environment wire belong to one
specified spatial site. The unitary dilation therefore costs no intersite layer.
The reduced-channel identity is proved on all original-wire operators.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

noncomputable section

variable {d m W A : ℕ}

/-- A channel on `m` local qudits needs only `2*m` fresh local qudits, independent of
its supplied Kraus indexing. All fresh qudits start in the zero basis state; the original
`m`-qudit output factor is retained. -/
theorem exists_qudit_freshEnvironment_unitary {d m : ℕ} [NeZero d]
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ))
    (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix.unitaryGroup ((Fin m → Fin d) × (Fin (2 * m) → Fin d)) ℂ,
      ∀ X : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ,
        Φ X = partialTraceRight
          ((U : Matrix ((Fin m → Fin d) × (Fin (2 * m) → Fin d))
            ((Fin m → Fin d) × (Fin (2 * m) → Fin d)) ℂ) *
            freshEnvironmentInput (0 : Fin (2 * m) → Fin d) X * Uᴴ) := by
  apply exists_freshEnvironment_unitary_of_equiv finFunctionFinEquiv finFunctionFinEquiv Φ hΦ
  exact le_of_eq (by rw [two_mul, pow_add])

/-- Select the original local register and all fresh environment wires. -/
def selectedEnvironmentEmbedding (e : Fin m ↪ Fin W) (A : ℕ) :
    Fin (m + A) ↪ Fin (W + A) :=
  finSumFinEquiv.symm.toEmbedding.trans
    ((e.sumMap (Function.Embedding.refl (Fin A))).trans finSumFinEquiv.toEmbedding)

@[simp] theorem selectedEnvironmentEmbedding_old (e : Fin m ↪ Fin W) (i : Fin m) :
    selectedEnvironmentEmbedding e A (Fin.castAdd A i) = Fin.castAdd A (e i) := by
  simp [selectedEnvironmentEmbedding]

@[simp] theorem selectedEnvironmentEmbedding_new (e : Fin m ↪ Fin W) (i : Fin A) :
    selectedEnvironmentEmbedding e A (Fin.natAdd m i) = Fin.natAdd W i := by
  simp [selectedEnvironmentEmbedding]

/-- Selection keeps the entire fresh environment and restricts only the old system. -/
theorem append_comp_selectedEnvironment (e : Fin m ↪ Fin W)
    (x : Fin W → Fin d) (a : Fin A → Fin d) :
    Fin.append x a ∘ selectedEnvironmentEmbedding e A = Fin.append (x ∘ e) a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

private theorem agreeOff_selectedEnvironment (e : Fin m ↪ Fin W)
    (x y : Fin W → Fin d) (a b : Fin A → Fin d) :
    AgreeOff (selectedEnvironmentEmbedding e A) (Fin.append x a) (Fin.append y b) ↔
      AgreeOff e x y := by
  constructor
  · intro h i hi
    have hz : ∀ j, selectedEnvironmentEmbedding e A j ≠ Fin.castAdd A i := by
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · intro heq
        have hv := congrArg (@Fin.val (W + A)) heq
        simp only [selectedEnvironmentEmbedding_old, Fin.val_castAdd] at hv
        exact hi l (Fin.ext hv)
      · intro heq
        have hv := congrArg (@Fin.val (W + A)) heq
        simp only [selectedEnvironmentEmbedding_new, Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
    simpa only [Fin.append_left] using h (Fin.castAdd A i) hz
  · intro h j hj
    revert hj
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · intro hi
      have he : ∀ l, e l ≠ i := by
        intro l heq
        apply hi (Fin.castAdd A l)
        simp [heq]
      simpa only [Fin.append_left] using h i he
    · intro hi
      exact (hi (Fin.natAdd m i) (selectedEnvironmentEmbedding_new e i)).elim

/-- Each initialized environment block of the placed joint operator is the placement
of the corresponding local block. No restriction is imposed on other input wires. -/
theorem environmentKraus_selectedEnvironment (e : Fin m ↪ Fin W)
    (U : Matrix ((Fin m → Fin d) × (Fin A → Fin d))
      ((Fin m → Fin d) × (Fin A → Fin d)) ℂ) (a b : Fin A → Fin d) :
    environmentKraus
      (appendMatrixSplit W A d
        (embedOp (selectedEnvironmentEmbedding e A) ((appendMatrixSplit m A d).symm U))) a b =
      embedOp e (environmentKraus U a b) := by
  classical
  ext x y
  change embedOp (selectedEnvironmentEmbedding e A) ((appendMatrixSplit m A d).symm U)
    (Fin.append x b) (Fin.append y a) = _
  simp only [embedOp_apply, agreeOff_selectedEnvironment,
    append_comp_selectedEnvironment, append_comp_selectedEnvironment]
  congr 1
  change U (appendConfigurationSplit m A d (Fin.append (x ∘ e) b))
    (appendConfigurationSplit m A d (Fin.append (y ∘ e) a)) = _
  rw [appendConfigurationSplit_append, appendConfigurationSplit_append]
  rfl

/-- Place a local dilation at selected old wires and all fresh wires, then discard
only those fresh wires. The resulting channel is the placement of the local reduced map. -/
theorem reduced_selectedEnvironment [NeZero d] (e : Fin m ↪ Fin W)
    (U : Matrix ((Fin m → Fin d) × (Fin A → Fin d))
      ((Fin m → Fin d) × (Fin A → Fin d)) ℂ) :
    discardAppendedEnvironment W A d ∘ₗ
      singleKrausMap
        (embedOp (selectedEnvironmentEmbedding e A) ((appendMatrixSplit m A d).symm U)) ∘ₗ
      appendEnvironmentInput W A d =
      registerChannelLift e
        (partialTraceRightLM ∘ₗ singleKrausMap U ∘ₗ
          freshEnvironmentInput (0 : Fin A → Fin d)) := by
  have hlocal : partialTraceRightLM ∘ₗ singleKrausMap U ∘ₗ
      freshEnvironmentInput (0 : Fin A → Fin d) =
      rectangularKrausMap (environmentKraus U 0) := by
    apply LinearMap.ext
    exact partialTrace_freshEnvironmentInput U 0
  rw [hlocal, registerChannelLift_kraus]
  apply LinearMap.ext
  intro X
  change discardAppendedEnvironment W A d
    (_ * appendEnvironmentInput W A d X * _) = _
  rw [discardAppendedEnvironment_conj, partialTrace_freshEnvironmentInput]
  have hblocks : environmentKraus
      (appendMatrixSplit W A d
        (embedOp (selectedEnvironmentEmbedding e A) ((appendMatrixSplit m A d).symm U))) 0 =
      fun b => embedOp e (environmentKraus U 0 b) := by
    funext b
    exact environmentKraus_selectedEnvironment e U 0 b
  rw [hblocks]

variable {N : ℕ} [NeZero N] [NeZero d]

/-- A fresh-environment dilation of a channel within one spatial site is an actual
zero-intersite-depth unitary on that site's enlarged memory. -/
theorem exists_selected_onsite_dilation (P : PhysicalPortLayout N W) (i : Fin N)
    (e : Fin m ↪ Fin W) (he : ∀ j, P.site (e j) = i)
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ))
    (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix (Fin (W + 2 * m) → Fin d) (Fin (W + 2 * m) → Fin d) ℂ,
      IsPhysicalPortUnitary (P.append (fun _ : Fin (2 * m) => i)) 0 U ∧
      discardAppendedEnvironment W (2 * m) d ∘ₗ singleKrausMap U ∘ₗ
        appendEnvironmentInput W (2 * m) d = registerChannelLift e Φ := by
  obtain ⟨V, hV⟩ := exists_qudit_freshEnvironment_unitary Φ hΦ
  let R := appendMatrixSplit m (2 * m) d
  let U := embedOp (selectedEnvironmentEmbedding e (2 * m))
    (R.symm (V : Matrix ((Fin m → Fin d) × (Fin (2 * m) → Fin d))
      ((Fin m → Fin d) × (Fin (2 * m) → Fin d)) ℂ))
  refine ⟨U, ?_, ?_⟩
  · apply IsPhysicalPortUnitary.onsite i
    · apply embedOp_mem_unitary (selectedEnvironmentEmbedding e (2 * m)).injective
      exact Matrix.reindex_mem_unitaryGroup
        (appendConfigurationSplit m (2 * m) d).symm V V.property
    · apply supportedOperators_mono _
        (embedOp_mem_supportedOperators (selectedEnvironmentEmbedding e (2 * m)).injective _)
      rintro _ ⟨j, rfl⟩
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · rw [selectedEnvironmentEmbedding_old]
        change Fin.addCases P.site (fun _ => i) (Fin.castAdd (2 * m) (e l)) = i
        simpa only [Fin.addCases_left] using he l
      · rw [selectedEnvironmentEmbedding_new]
        change Fin.addCases P.site (fun _ => i) (Fin.natAdd W l) = i
        simp
  · have hlocal : partialTraceRightLM ∘ₗ
        singleKrausMap (V : Matrix ((Fin m → Fin d) × (Fin (2 * m) → Fin d))
      ((Fin m → Fin d) × (Fin (2 * m) → Fin d)) ℂ) ∘ₗ
        freshEnvironmentInput (0 : Fin (2 * m) → Fin d) = Φ := by
      apply LinearMap.ext
      intro X
      exact (hV X).symm
    change discardAppendedEnvironment W (2 * m) d ∘ₗ
      singleKrausMap (embedOp (selectedEnvironmentEmbedding e (2 * m)) (R.symm V)) ∘ₗ
      appendEnvironmentInput W (2 * m) d = _
    rw [reduced_selectedEnvironment, hlocal]

/-- Enumerate exactly the original qudit wires belonging to one spatial site. -/
def PhysicalPortLayout.siteRegister (P : PhysicalPortLayout N W) (i : Fin N) :
    Fin (Fintype.card {j // P.site j = i}) ↪ Fin W :=
  (Fintype.equivFin {j // P.site j = i}).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

omit [NeZero N] in
@[simp] theorem PhysicalPortLayout.site_siteRegister
    (P : PhysicalPortLayout N W) (i : Fin N)
    (j : Fin (Fintype.card {j // P.site j = i})) : P.site (P.siteRegister i j) = i :=
  ((Fintype.equivFin {j // P.site j = i}).symm j).property

omit [NeZero N] in
/-- The local enumeration includes every wire of its site and no wire of any other site. -/
theorem PhysicalPortLayout.range_siteRegister (P : PhysicalPortLayout N W) (i : Fin N) :
    Set.range (P.siteRegister i) = P.site ⁻¹' {i} := by
  ext j
  constructor
  · rintro ⟨a, rfl⟩
    exact P.site_siteRegister i a
  · intro hj
    refine ⟨Fintype.equivFin {j // P.site j = i} ⟨j, hj⟩, ?_⟩
    simp [PhysicalPortLayout.siteRegister]

private theorem exists_localKraus {r : ℕ} (e : Fin m ↪ Fin W)
    (K : Fin r → Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
    (hs : ∀ a, K a ∈ supportedOperators d (Set.range e))
    (hnorm : ∑ a, (K a)ᴴ * K a = 1) :
    ∃ A : Fin r → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ,
      (∀ a, K a = embedOp e (A a)) ∧ ∑ a, (A a)ᴴ * A a = 1 := by
  choose A hA using fun a => exists_embedOp_eq_of_mem_supportedOperators e.injective (hs a)
  refine ⟨A, hA, ?_⟩
  apply embedOp_injective e.injective (Nat.pos_of_ne_zero (NeZero.ne d))
  let E : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ :=
    { toFun := embedOp e
      map_add' := embedOp_add e
      map_smul' := fun z X => embedOp_smul e z X }
  change E (∑ a, (A a)ᴴ * A a) = E 1
  rw [map_sum]
  change (∑ a, embedOp e ((A a)ᴴ * A a)) = embedOp e 1
  simp_rw [← embedOp_mul e.injective, ← embedOp_conjTranspose, ← hA]
  rw [embedOp_one]
  exact hnorm

/-- Every supported onsite Kraus operation admits a fresh-local-environment unitary
realization. Environment size depends only on the site's wire count, not Kraus count. -/
theorem exists_onsite_appended_dilation {r : ℕ}
    (P : PhysicalPortLayout N W) (i : Fin N)
    (K : Fin r → Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
    (hs : ∀ a, K a ∈ supportedOperators d (P.site ⁻¹' {i}))
    (hnorm : ∑ a, (K a)ᴴ * K a = 1) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary (P.append owner) 0 U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d = rectangularKrausMap K := by
  let e := P.siteRegister i
  obtain ⟨L, hL, hnormL⟩ := exists_localKraus e K
    (fun a => by simpa only [e, P.range_siteRegister i] using hs a) hnorm
  obtain ⟨U, hU, heq⟩ := exists_selected_onsite_dilation P i e
    (P.site_siteRegister i) (rectangularKrausMap L)
    (rectangularKrausMap_isKrausCPTP L hnormL)
  refine ⟨2 * Fintype.card {j // P.site j = i}, fun _ => i, U, hU, ?_⟩
  rw [heq, registerChannelLift_kraus]
  congr 1
  funext a
  exact (hL a).symm

end

end QuantumCircuit
