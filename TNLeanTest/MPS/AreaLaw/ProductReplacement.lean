/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CopyMPSFactor
import TNLean.MPS.AreaLaw.CopyErrorAmplification
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Zero bond bound, zero target, and standard-axiom checks for product replacement. -/

open TNLean.MPS.AreaLaw
open scoped Matrix

-- A one-site vector has no internal bond condition, even at bond bound zero.
-- Product replacement must retain this case and allow a zero product target.
example {q : ℕ} {ψ : EuclideanSpace ℂ (Fin 1 → Fin q)} (hψ : ‖ψ‖ = 1) (k : ℕ) :
    ∃ χ : EuclideanSpace ℂ (Fin 1 → Fin q),
      IsOpenMPS 1 q 0 (fun x ↦ χ x) ∧ ‖χ‖ = 1 := by
  have hmps : IsOpenMPS 1 q 0 (fun x ↦ ψ x) := by
    apply isOpenMPS_of_internal_cutMatrix_rank_le
    omega
  obtain ⟨χ, u, v, hχ, hn, _⟩ := hmps.exists_product_overlap_ge hψ k 0 0
  exact ⟨χ, hχ, hn⟩

-- A zero target factors at every cut, without requiring target normalization.
example {L q D : ℕ} {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q D (fun x ↦ ψ x)) (hn : ‖ψ‖ = 1) (S : Finset ℕ) :
    ∃ χ : EuclideanSpace ℂ (Fin L → Fin q),
      IsOpenMPS L q D (fun x ↦ χ x) ∧ ‖χ‖ = 1 ∧
      ∀ k ∈ S, (cutMatrix χ k).rank ≤ 1 := by
  obtain ⟨χ, hm, hχ, _, _, hr⟩ := hψ.exists_rank_one_at_product_cuts (ξ := 0) hn S
    (fun k _ ↦ ⟨0, 0, by ext ij; simp [Matrix.euclideanTensorVector]⟩)
  exact ⟨χ, hm, hχ, hr⟩

-- The empty tensor product has unit norm, even when the local space is empty.
example (L q : ℕ) (η : Fin 0 → EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖copyProduct η‖ = 1 := by
  simp [norm_copyProduct]

-- A small literal product error supplies the single-factor amplification bound.
example {K L q : ℕ} {η : EuclideanSpace ℂ (Fin L → Fin q)}
    (hη : ‖η‖ = 1) (θ : Fin K → EuclideanSpace ℂ (Fin L → Fin q))
    (hθ : ∀ i, ‖θ i‖ = 1) (hK : 1 ≤ K) {δ : ℝ} (hδ : δ < 1 / 8)
    (herror : Real.optimizedPureTraceError
      (‖inner ℂ (copyProduct (fun _ : Fin K ↦ η)) (copyProduct θ)‖ ^ 2) ≤ δ) :
    ∃ i, Real.sqrt ((K : ℝ) / 4) *
      Real.optimizedPureTraceError (‖inner ℂ η (θ i)‖ ^ 2) ≤ δ := by
  obtain ⟨i, _, hi⟩ := exists_copy_optimizedPureTraceError_le hη θ hθ hK
    (herror.trans_lt (by linarith))
  exact ⟨i, hi.trans herror⟩

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``TNLean.MPS.AreaLaw.rank_cutMatrix_le_of_product_mem_ranges,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.of_product_mem_cut_ranges,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.exists_product_overlap_ge,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.exists_rank_one_at_product_cuts,
    ``TNLean.MPS.AreaLaw.norm_copyProduct,
    ``TNLean.MPS.AreaLaw.copyProduct_factors_at_boundary,
    ``TNLean.MPS.AreaLaw.inner_copyProduct,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.exists_rank_one_at_copy_boundaries,
    ``TNLean.MPS.AreaLaw.sq_norm_inner_copyProduct,
    ``TNLean.MPS.AreaLaw.exists_copy_optimizedPureTraceError_le,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_intervalSlice_le,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.intervalSlice,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.of_intervalSlice_eq_mul,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.copyProduct_factor]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
