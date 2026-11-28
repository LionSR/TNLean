/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.Inhomogeneous.InhomogeneousDoeblin
import TNLean.MPS.Tensor.Chain.Interval
import QICLean.Channel.FixedPoint.MeanErgodic.Cesaro
import QICLean.Analysis.Real.GeometricOrderPolynomialBound
import TNLean.MPS.Preparation.Inhomogeneous.VaryingReferencePreparation

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

## Physical preparation from a local window criterion

Trace-preserving actual site tensors and a uniform Choi minorization on every fixed-width
nonwrapping window imply eventual physical logarithmic-depth preparation. The reference
densities and global mixing rate are derived rather than supplied. The window minorizers
may vary with the ring and position and may be singular.

**Scope restriction (local minorization):** this is an explicit local quantitative sufficient
condition for arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS". It does
not derive a rate from that paragraph's qualitative convergence definition. Bond spaces
remain square with a fixed dimension; see `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

### References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
* Wolf, *Quantum Channels & Operations*, Theorem 8.17 and Eq. (8.86) (the local Choi criterion).
-/

section

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
        Kraus.transferMap (MPSChainTensor.eval (A.interval a n h)) (σ (a + n)) = σ a := by
  classical
  let T := Kraus.transferMap (MPSChainTensor.eval A)
  obtain ⟨ρ, hρ, hρne, hfix⟩ := IsPositiveMap.exists_posSemidef_fixedPoint
    (E := T) (fun X hX => Kraus.transferMap_pos _ hX)
    (MPSChainTensor.trace_transferMap_eval A htp)
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
      simpa [σ, Es, T, MPSChainTensor.transferMap_eval] using hθfix
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
theorem norm_gram_block_sub_transport_le_of_window_domination
    {d D N : ℕ} (A : MPSChainTensor d D N) (s : ℕ) (_hs : 0 < s) (δ : ℝ)
    (htp : ∀ i, IsTracePreservingMap (Kraus.transferMap (A i)))
    (hwindow : ∀ a (ha : a + s ≤ N), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.eval (A.interval a s ha))) ≥
          ((δ : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) :
    ‖(physicalMatrix (MPSChainTensor.eval A))ᴴ *
        physicalMatrix (MPSChainTensor.eval A) -
      (Kraus.transferMap (MPSChainTensor.eval A) ρ)ᵀ ⊗ₖ
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
        Kraus.transferMap (MPSChainTensor.eval
          (A.interval (j.val * s) s (hbound ⟨j.val, by
            have := j.isLt
            have := Fin.val_ne_of_ne hj
            simp only [Fin.val_last] at this
            omega⟩))) := by
    have hℓ : ℓ j = s := by simp [ℓ, hj]
    simp only [chainBlockTensor, MPSChainTensor.transferMap_eval]
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
  have hb := norm_gram_block_sub_transport_le_of_choi_domination A ℓ hsum e ω hωtr
    (fun j X => MPSChainTensor.trace_transferMap_eval _ (fun i => htp _) X)
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
          (MPSChainTensor.eval (A.interval a s ha))) ≥
            ((δ : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) →
      ∃ σ : ℕ → Matrix (Fin D) (Fin D) ℂ,
        (∀ i, (σ i).PosSemidef ∧ (σ i).trace = 1) ∧ σ N = σ 0 ∧
        ∀ a n (h : a + n ≤ N),
        ‖transferMatrix (Kraus.transferMap (MPSChainTensor.eval (A.interval a n h))) -
          transferMatrix (Kraus.transferMap (fixedPointTensor (σ a)))‖ ≤
            K * (1 - δ) ^ (n / s) := by
  obtain ⟨Kr, hKr, hconv⟩ := exists_norm_gram_transferMatrix_sub_le D
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
  refine ⟨Kr * (2 * D), by positivity, fun {d N} A s hs δ htp hwindow => ?_⟩
  obtain ⟨σ, hσ, hcyc, htransport⟩ := exists_compatible_density_family A htp
  refine ⟨σ, hσ, hcyc, fun a n h => ?_⟩
  let B := A.interval a n h
  have hBtp : ∀ i, IsTracePreservingMap (Kraus.transferMap (B i)) := fun i => htp _
  have hBwindow : ∀ b (hb : b + s ≤ n), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.eval (B.interval b s hb))) ≥
          ((δ : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    intro b hb
    dsimp only [B]
    rw [MPSChainTensor.interval_interval]
    exact hwindow (a + b) (by omega)
  have hg := norm_gram_block_sub_transport_le_of_window_domination B s hs δ hBtp
    hBwindow (σ (a + n)) (hσ _).1 (hσ _).2
  change ‖(physicalMatrix (MPSChainTensor.eval B))ᴴ *
      physicalMatrix (MPSChainTensor.eval B) -
      (Kraus.transferMap (MPSChainTensor.eval (A.interval a n h)) (σ (a + n)))ᵀ ⊗ₖ
        (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤ _ at hg
  rw [htransport] at hg
  exact (hconv (MPSChainTensor.eval B) (σ a) (hσ a).1).2.trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hg hKr.le)

end MPSPreparation

end

section

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace MPSPreparation

/-- A fixed-width local Choi minorization criterion gives eventual physical logarithmic-depth
preparation of the original tensor family. Actual sites preserve trace, and every actual
nonwrapping window of `s ≥ 1` sites has normalized Choi matrix at least `(η/D) (τ ⊗ I)` for
some density matrix `τ`. The density may depend on the ring and window and may be singular.
For `η > 0`, the actual window at length `s` forces `η ≤ 1`; compatible references and
uniform ordered mixing are derived internally.

The cutoff is at least `s`. No cyclic-wrap window, supplied global rate, common stationary
state, faithful reference, or short-ring nonzero premise is required. The endpoint `η = 1`
is handled by weakening to `η/2` before taking a logarithm. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_window_domination
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    (s : ℕ) (hs : 0 < s) {η : ℝ} (hη : 0 < η)
    (htp : ∀ (N : ℕ) (i : Fin N), IsTracePreservingMap (Kraus.transferMap (A N i)))
    (hwindow : ∀ (N a : ℕ) (ha : a + s ≤ N), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.eval ((A N).interval a s ha))) ≥
          ((η : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) :
    ∃ N₀ : ℕ, s ≤ N₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace (Fin d) N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth (Geometry.ring N) T (fun x => ψ x) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨τ₀, hτ₀, hτ₀tr, _⟩ := hwindow s 0 (by omega)
  have := Matrix.neZero_of_trace_eq_one hτ₀tr
  have hη1 : η ≤ 1 := by
    have hg := norm_gram_block_sub_transport_le_of_window_domination
      (A s) s hs η (htp s) (hwindow s) τ₀ hτ₀ hτ₀tr
    have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
    have hp : 0 ≤ 2 * D * (1 - η) :=
      (norm_nonneg _).trans (by simpa only [Nat.div_self hs, pow_one] using hg)
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (mul_pos two_pos hD)).mp hp)
  have hρhalf : 1 / 2 ≤ 1 - η / 2 := by linarith
  have hρ0 : 0 < 1 - η / 2 := by linarith
  have hρ1 : 1 - η / 2 < 1 := by linarith
  let r := -Real.log (1 - η / 2) / s
  have hr : 0 < r := div_pos (neg_pos.mpr (Real.log_neg hρ0 hρ1)) (Nat.cast_pos.mpr hs)
  have hweak : ∀ (N a : ℕ) (ha : a + s ≤ N), ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (Kraus.transferMap
        (MPSChainTensor.eval ((A N).interval a s ha))) ≥
          (((η / 2 : ℝ) : ℂ) / D) • (τ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    intro N a ha
    obtain ⟨τ, hτ, htr, hc⟩ := hwindow N a ha
    refine ⟨τ, hτ, htr, le_trans ?_ hc⟩
    apply Matrix.le_iff.mpr
    rw [← sub_smul]
    apply (hτ.kronecker Matrix.PosSemidef.one).smul
    have heq : (η : ℂ) / D - ((η / 2 : ℝ) : ℂ) / D = ((η / (2 * D) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq]
    exact Complex.zero_le_real.mpr (by positivity)
  obtain ⟨K, hK, hmix⟩ := exists_norm_transferMatrix_interval_sub_le_of_window_domination D
  choose σ hσ hcyc hm using fun N => hmix (A N) s hs (η / 2) (htp N) (hweak N)
  have happrox := exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_varying_reference
    d D hd A (fun N j => σ N j.val) (fun N _ j => (hσ N j.val).1)
    (fun N _ j => (hσ N j.val).2) (2 * K) r (by positivity) hr
  have hm' : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M) (hj : 0 < ℓ j),
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor
          (σ N (blockSite hN j ⟨0, hj⟩).val)))‖ ≤
        (2 * K) * Real.exp (-(r * ℓ j)) := by
    intro N _ M ℓ hN j hj
    have hbound : blockOffset ℓ j.val + ℓ j ≤ N := by
      have hb := blockOffset_mono ℓ j.isLt
      rw [blockOffset_of_le ℓ le_rfl, hN, blockOffset_succ ℓ j] at hb
      exact hb
    have h := hm N (blockOffset ℓ j.val) (ℓ j) hbound
    have hg := Real.pow_nat_div_le_two_mul_exp s (ℓ j) hs (1 - η / 2) hρhalf hρ1
    have hfinal := h.trans (mul_le_mul_of_nonneg_left hg hK.le)
    simpa only [MPSChainTensor.transferMap_eval, MPSChainTensor.interval,
      blockSite, Nat.add_zero, mul_assoc, mul_left_comm K 2] using hfinal
  obtain ⟨N₀, C, hC⟩ := happrox hm'
  refine ⟨max s N₀, le_max_left _ _, C, fun ε hε hε1 N _ hN => ?_⟩
  exact hC ε hε hε1 N ((le_max_right s N₀).trans hN)

end MPSPreparation

end
