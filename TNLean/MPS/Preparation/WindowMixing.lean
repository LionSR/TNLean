/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousChoiResidual
import TNLean.MPS.Chain.Interval
import QICLean.Channel.FixedPoint.Cesaro

/-!
# Ordered mixing from actual fixed-window minorization

A fixed-width minorization of actual ordered windows yields quantitative convergence towards
site-dependent density resets. Compatible densities are obtained from a whole-ring stationary
density and propagated backwards through suffixes. The minorizing densities themselves need
not be stationary, common, or faithful. Only nonwrapping windows in the selected cut occur.

**Scope restriction (local minorization):** this is an additional quantitative sufficient
condition for arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS", not a
consequence of its qualitative finite-correlation definition. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`. Rectangular bonds are not covered here.

## References

* Wolf, *Quantum Channels & Operations*, Theorems 6.11 and 8.17, and Eq. (8.86).
* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace MPSPreparation

/-- A trace-preserving tensor chain has compatible density matrices at its cuts. The cut
at `N` equals the cut at zero, and each actual nonwrapping interval transports its right
endpoint density to its left endpoint density. No faithful stationary state is required. -/
theorem exists_compatible_density_family {d D N : ℕ} [NeZero D]
    (A : MPSChainTensor d D N)
    (htp : ∀ i, IsTracePreservingMap (Kraus.transferMap (A i))) :
    ∃ σ : ℕ → Matrix (Fin D) (Fin D) ℂ,
      (∀ i, (σ i).PosSemidef ∧ (σ i).trace = 1) ∧ σ N = σ 0 ∧
      ∀ a n (h : a + n ≤ N),
        Kraus.transferMap (MPSChainTensor.blockTensor (A.interval a n h)) (σ (a + n)) = σ a := by
  classical
  let T := Kraus.transferMap (MPSChainTensor.blockTensor A)
  obtain ⟨ρ, hρ, hρne, hfix⟩ := IsPositiveMap.exists_posSemidef_fixedPoint
    (E := T) (fun X hX => Kraus.transferMap_pos _ hX)
    (MPSChainTensor.trace_transferMap_blockTensor A htp)
    (Nat.pos_of_ne_zero (NeZero.ne D))
  have hρtr : ρ.trace ≠ 0 := fun h => hρne (hρ.trace_eq_zero_iff.mp h)
  let θ := ρ.trace⁻¹ • ρ
  have hθ : θ.PosSemidef := hρ.smul (inv_nonneg_of_nonneg hρ.trace_nonneg)
  have hθtr : θ.trace = 1 := by simp [θ, hρtr]
  have hθfix : T θ = θ := by simp [θ, map_smul, hfix]
  let Es := List.ofFn fun i => Kraus.transferMap (A i)
  let σ := fun a => (Es.drop a).prod θ
  have hprod : ∀ Ts : List (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ S ∈ Ts, IsPositiveMap S ∧ IsTracePreservingMap S) →
      ∀ X, X.PosSemidef → X.trace = 1 → (Ts.prod X).PosSemidef ∧ (Ts.prod X).trace = 1 := by
    intro Ts
    induction Ts with
    | nil => intro h X hX ht; exact ⟨hX, ht⟩
    | cons S Ts ih =>
      intro h X hX ht
      obtain ⟨hp, htr⟩ := ih (fun E hE => h E (by simp [hE])) X hX ht
      exact ⟨(h S (by simp)).1 _ hp, ((h S (by simp)).2 _).trans htr⟩
  have hσ : ∀ a, (σ a).PosSemidef ∧ (σ a).trace = 1 := by
    intro a
    apply hprod (Es.drop a) _ θ hθ hθtr
    intro S hS
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hS)
    exact ⟨fun X hX => Kraus.transferMap_pos _ hX, htp i⟩
  refine ⟨σ, hσ, ?_, fun a n h => ?_⟩
  · have hzero : σ 0 = θ := by
      simpa [σ, Es, T, MPSChainTensor.transferMap_blockTensor] using hθfix
    rw [hzero]
    have hdrop : Es.drop N = [] := List.drop_eq_nil_iff.mpr (by simp [Es])
    change (Es.drop N).prod θ = θ
    rw [hdrop]
    rfl
  · rw [MPSChainTensor.transferMap_interval]
    change ((Es.drop a).take n).prod ((Es.drop (a + n)).prod θ) = (Es.drop a).prod θ
    change (((Es.drop a).take n).prod * (Es.drop (a + n)).prod) θ = _
    rw [← List.prod_append, List.drop_take_append_drop]

/-- A fixed-width Choi minorization of each actual nonwrapping window bounds the whole
chain Gram error by the number of complete windows. The final shorter block uses only
trace preservation and complete positivity. Window-dependent minorizers are allowed. -/
theorem norm_gram_blockTensor_sub_transport_le_of_window_domination
    {d D N : ℕ} (A : MPSChainTensor d D N) (s : ℕ) (_hs : 0 < s) (δ : ℝ)
    (htp : ∀ i, IsTracePreservingMap (Kraus.transferMap (A i)))
    (hwindow : ∀ a (ha : a + s ≤ N), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.blockTensor (A.interval a s ha))) ≥
          ((δ : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) :
    ‖(physicalMatrix (MPSChainTensor.blockTensor A))ᴴ *
        physicalMatrix (MPSChainTensor.blockTensor A) -
      (Kraus.transferMap (MPSChainTensor.blockTensor A) ρ)ᵀ ⊗ₖ
        (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤ 2 * D * (1 - δ) ^ (N / s) := by
  classical
  have := Matrix.neZero_of_trace_eq_one hρtr
  let m := N / s
  let ℓ : Fin (m + 1) → ℕ := fun j => if j = Fin.last m then N % s else s
  have hsum : ∑ j, ℓ j = N := by
    rw [Fin.sum_univ_castSucc]
    simp only [ℓ, Fin.castSucc_ne_last, ite_false, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ite_true]
    simpa only [m, Nat.mul_comm] using Nat.div_add_mod N s
  have hoffset (j : Fin (m + 1)) : blockOffset ℓ j.val = j.val * s := by
    have hj : j.val ≤ m := by omega
    rw [← blockOffset_castSucc ℓ hj]
    simpa only [ℓ, Fin.castSucc_ne_last, ite_false] using blockOffset_const s hj
  have hbound (j : Fin m) : j.val * s + s ≤ N := by
    have hj : j.val + 1 ≤ m := j.isLt
    calc j.val * s + s = (j.val + 1) * s := by ring
      _ ≤ m * s := Nat.mul_le_mul_right s hj
      _ ≤ N := Nat.div_mul_le_self N s
  choose τ hτ using fun j : Fin m => hwindow (j.val * s) (hbound j)
  let ω : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ := fun j =>
    if h : j.val < m then τ ⟨j.val, h⟩ else ρ
  let e : Fin (m + 1) → ℝ := fun j => if j = Fin.last m then 0 else δ
  have hωtr : ∀ j, (ω j).trace = 1 := by
    intro j
    dsimp [ω]
    split_ifs with hj
    · exact (hτ ⟨j.val, hj⟩).2.1
    · exact hρtr
  have heq (j : Fin (m + 1)) (hj : j ≠ Fin.last m) :
      Kraus.transferMap (chainBlockTensor A hsum j) =
        Kraus.transferMap (MPSChainTensor.blockTensor
          (A.interval (j.val * s) s (hbound ⟨j.val, by
            have := j.isLt
            have := Fin.val_ne_of_ne hj
            simp only [Fin.val_last] at this
            omega⟩))) := by
    have hℓ : ℓ j = s := by simp [ℓ, hj]
    simp only [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
    congr 1
    apply List.ext_getElem
    · simp [hℓ]
    · intro i hi hi'
      simp only [List.getElem_ofFn]
      congr 2
      apply Fin.ext
      simp [blockSite_val, hoffset]
  have hc : ∀ j, ChoiRectangular.choiMatrix (Kraus.transferMap (chainBlockTensor A hsum j)) ≥
      ((e j : ℂ) / D) • (ω j ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    intro j
    by_cases hj : j = Fin.last m
    · simp only [e, hj, ite_true, Complex.ofReal_zero, zero_div, zero_smul]
      exact ((ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef _).1
        (isCPMap_of_krausMapLM _)).nonneg
    · have hv : j.val < m := by
        have := j.isLt
        have := Fin.val_ne_of_ne hj
        simp only [Fin.val_last] at this
        omega
      simpa only [e, hj, ite_false, ω, dite_eq_left hv, heq j hj] using (hτ ⟨j.val, hv⟩).2.2
  have hb := norm_gram_blockTensor_sub_transport_le_of_choi_domination A ℓ hsum e ω hωtr
    (fun j X => MPSChainTensor.trace_transferMap_blockTensor _ (fun i => htp _) X)
    hc ρ hρ hρtr
  have heprod : ∏ j, (1 - e j) = (1 - δ) ^ m := by
    rw [Fin.prod_univ_castSucc]
    simp [e]
  rwa [heprod] at hb

/-- Uniform actual-window minorization produces compatible reset references and a
transfer-matrix rate. The prefactor is fixed by `D` before the physical dimension, chain,
window width, minorization strength, and reference family are chosen. -/
theorem exists_norm_transferMatrix_interval_sub_le_of_window_domination
    (D : ℕ) [NeZero D] :
    ∃ K : ℝ, 0 < K ∧ ∀ {d N : ℕ} (A : MPSChainTensor d D N)
      (s : ℕ), 0 < s → ∀ δ : ℝ,
      (∀ i, IsTracePreservingMap (Kraus.transferMap (A i))) →
      (∀ a (ha : a + s ≤ N), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
        τ.PosSemidef ∧ τ.trace = 1 ∧
        ChoiRectangular.choiMatrix (Kraus.transferMap
          (MPSChainTensor.blockTensor (A.interval a s ha))) ≥
            ((δ : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) →
      ∃ σ : ℕ → Matrix (Fin D) (Fin D) ℂ,
        (∀ i, (σ i).PosSemidef ∧ (σ i).trace = 1) ∧ σ N = σ 0 ∧
        ∀ a n (h : a + n ≤ N),
        ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (A.interval a n h))) -
          transferMatrix (Kraus.transferMap (fixedPointTensor (σ a)))‖ ≤
            K * (1 - δ) ^ (n / s) := by
  obtain ⟨Kr, hKr, hconv⟩ := exists_norm_transferMatrix_sub_le_gram_uniform_reference D
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
  refine ⟨Kr * (2 * D), by positivity, fun {d N} A s hs δ htp hwindow => ?_⟩
  obtain ⟨σ, hσ, hcyc, htransport⟩ := exists_compatible_density_family A htp
  refine ⟨σ, hσ, hcyc, fun a n h => ?_⟩
  let B := A.interval a n h
  have hBtp : ∀ i, IsTracePreservingMap (Kraus.transferMap (B i)) := fun i => htp _
  have hBwindow : ∀ b (hb : b + s ≤ n), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.blockTensor (B.interval b s hb))) ≥
          ((δ : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    intro b hb
    dsimp only [B]
    rw [MPSChainTensor.interval_interval]
    exact hwindow (a + b) (by omega)
  have hg := norm_gram_blockTensor_sub_transport_le_of_window_domination B s hs δ hBtp
    hBwindow (σ (a + n)) (hσ _).1 (hσ _).2
  change ‖(physicalMatrix (MPSChainTensor.blockTensor B))ᴴ *
      physicalMatrix (MPSChainTensor.blockTensor B) -
      (Kraus.transferMap (MPSChainTensor.blockTensor (A.interval a n h)) (σ (a + n)))ᵀ ⊗ₖ
        (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤ _ at hg
  rw [htransport] at hg
  exact (hconv (σ a) (hσ a).1 (MPSChainTensor.blockTensor B)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hg hKr.le)

end MPSPreparation
