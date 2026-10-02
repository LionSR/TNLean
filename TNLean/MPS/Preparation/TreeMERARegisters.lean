/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthLogBound
import TNLean.MPS.Preparation.RegisterTreeState
import TNLean.MPS.Preparation.TreeMERA

/-!
# Normal MPS as finite-range MERA, with registers of `s` sites

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, paragraph "Connection to MERA") read the
tree-RG circuit of eq. (16) as a finite-range MERA with `O(log log N)` layers and conclude that,
within the approximation error, normal translation-invariant MPS are finite-range MERA with
`O(log log N)` layers. `TNLean.MPS.Preparation.TreeMERA` proves this for tensors whose two-site
blocked tensor is injective. This file removes that hypothesis: the finest isometries of the MERA
write two *registers* of `s` sites, where `s` is a length from which on the blocked tensors are
injective, as in the source's picture, which starts from a blocked tensor.

## The MERA on registers

A `MPSPreparation.BinaryMERA (d^s) D k`, with `d^s = blockPhysDim d s`, has its finest isometry
`ℂ^{D²} → ℂ^{d^s} ⊗ ℂ^{d^s}`, that is, from one site to two neighbouring registers of `s` sites;
the coarse isometries and the disentanglers are those of `BinaryMERA`. Its state on
`M 2^{k+1}` registers, read on the `M s 2^{k+1}` sites (`MPSPreparation.registerCfgEquiv`), is
`MPSPreparation.BinaryMERA.registerState`.

The tree-RG MERA of the `s`-site blocked tensor `B` of `A` (`MPSPreparation.treeMERA`) needs only
that the two-site blocked tensor of `B`, that is `A` blocked over `2s` sites, is injective, which
holds when `A` blocked over `s` sites is. Blocking `B` over `2^{k+1}` sites is blocking `A` over
`s 2^{k+1}` sites, so the state of this MERA is the approximating state of eq. (10) with block
length `q = s 2^{k+1}` (`MPSPreparation.approximatingMPVState_eq_registerState_treeMERA`), and
the approximation error of `A` itself applies, with no transport of the gauge data to `B`.

## Main results

* `MPSPreparation.approximatingMPVState_eq_registerState_treeMERA` — the approximating state of
  eq. (10) for `q = s 2^{k+1}` is the state of the tree-RG MERA of `A` blocked over `s` sites.
* `MPSPreparation.exists_registerState_treeMERA_approximationError_le` and
  `MPSPreparation.exists_registerState_treeMERA_approximationError_le_and_le_logb` — in the gauge
  of eq. (5), the error is at most `ε` once `s 2^{k+1} ≥ ξ log(C N/ε)`, and the least such `k`
  satisfies `k ≤ log₂(max 1 (ξ log(C N/ε)))`.
* `MPSPreparation.exists_binaryMERA_registerState_approximationError_le` — **every normal tensor**
  `A`: there are `s₀ ≥ 1`, `ξ > 0` and `C > 0` such that for every `s ≥ s₀`, `ε > 0` and `M ≥ 1`
  some binary finite-range MERA with registers of `s` sites and
  `k + 1 ≤ log₂(max 1 (ξ log(C N/ε))) + 1` isometry layers has error at most `ε` against the
  normalized state `|φ_N(A)⟩`, `N = M s 2^{k+1}`.

**Scope restriction (chain length):** the chain lengths are `N = M s 2^{k+1}`, with `k` given by
the threshold, not every fixed `N` and `ε`: the MERA has `M` complete binary trees of equal
registers. Documented in `docs/paper-gaps/mswc24_tree_mera_scope.tex`.

## References

* arXiv:2307.01696, eqs. (5), (10) and (16), Lemma 1'(i), and paragraphs "The tree-RG circuit"
  and "Connection to MERA".
-/

open Matrix MPSTensor
open scoped ComplexOrder InnerProductSpace

namespace MPSPreparation

variable {d D s k : ℕ}

/-! ### The state on the sites of the registers -/

/-- The configurations of `M` blocks of `s q` sites, read as configurations of `M` blocks of `q`
registers of `s` sites. -/
noncomputable def registerCfgEquiv (d s q M : ℕ) :
    Cfg d (M * (s * q)) ≃ Cfg (blockPhysDim d s) (M * q) :=
  ((blockedConfigEquiv d M (s * q)).symm.trans
    (Equiv.piCongrRight fun _ => directIteratedBlockEquiv d s q)).trans
    (blockedConfigEquiv (blockPhysDim d s) M q)

namespace BinaryMERA

variable (𝓜 : BinaryMERA (blockPhysDim d s) D k)

/-- The **state of a MERA on registers of `s` sites**, read on the `N = M s 2^{k+1}` sites: the
state of the MERA on `M 2^{k+1}` sites of dimension `d^s`, each site a register of `s` sites. -/
noncomputable def registerState [NeZero D] (M : ℕ) : MPVSpace d (M * (s * 2 ^ (k + 1))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (registerCfgEquiv d s (2 ^ (k + 1)) M).symm
    (𝓜.state M)

/-- The amplitude of the state on registers at a configuration of the sites: the amplitude of
the MERA at the configuration of the registers of every block. -/
theorem registerState_apply [NeZero D] (M : ℕ) (τ : Cfg d (M * (s * 2 ^ (k + 1)))) :
    𝓜.registerState M τ = 𝓜.amplitude fun j => directIteratedBlockEquiv d s (2 ^ (k + 1))
      ((blockedConfigEquiv d M (s * 2 ^ (k + 1))).symm τ j) := by
  rw [registerState, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Equiv.symm_symm, state_apply]
  simp [registerCfgEquiv]
  rfl

/-- The state of a MERA on registers is a unit vector. -/
theorem norm_registerState [NeZero D] (M : ℕ) : ‖𝓜.registerState M‖ = 1 := by
  rw [registerState, LinearIsometryEquiv.norm_map, norm_state]

end BinaryMERA

/-! ### The tree-RG MERA on registers -/

/-- **The approximating state is the state of a MERA on registers** (arXiv:2307.01696,
paragraph "Connection to MERA", with eqs. (10) and (16)). Let `A` blocked over `s` sites be
injective, let `σ ≥ 0` with `Tr σ = 1`, and let `u` be a unitary with `u |0⟩|0⟩ = |ω⟩`. For block
length `q = s 2^{k+1}` and `M ≥ 1` blocks, the approximating state `|φ'_N⟩ = V^{⊗M} |Ω⟩` of
eq. (10) is the state, read on the sites, of the tree-RG MERA with `k + 1` isometry layers of
`A` blocked over `s` sites. -/
theorem approximatingMPVState_eq_registerState_treeMERA [NeZero D] (A : MPSTensor d D)
    (hs : Kraus.IsInjective (blockTensor A s)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (k M : ℕ) [NeZero M]
    (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ) (hu0 : ∀ p, u p (0, 0) = fixedPointPair σ p) :
    approximatingMPVState A σ (s * 2 ^ (k + 1)) M =
      (treeMERA (blockTensor A s) (isInjective_blockTensor_two hs) k u hu).registerState M := by
  have hq : Kraus.IsInjective (blockTensor A (s * 2 ^ (k + 1))) := by
    rw [mul_comm]
    exact blockTensor_isInjective_mul_of_blockTensor_isInjective A (pow_pos two_pos _) hs
  rw [(inner_approximatingMPVState_mpvState A hq hσ htr M).1]
  set 𝓜 := treeMERA (blockTensor A s) (isInjective_blockTensor_two hs) k u hu
  have htop : 𝓜.topPair = fixedPointPair σ := funext hu0
  have htree : 𝓜.treeMatrix = polarIsoMatrix (blockTensor (blockTensor A s) (2 ^ (k + 1))) :=
    (binaryTreeMatrix_treeLayers k _).trans (polarIsoMatrix_blockTensor_eq_treeIsoMatrix k _).symm
  ext τ
  rw [approximatingMPVStateRaw_apply, BinaryMERA.registerState_apply, BinaryMERA.amplitude, htop,
    htree, mpv_approximatingTensor]
  refine Finset.sum_congr rfl fun x _ => congrArg (· * _) (Finset.prod_congr rfl fun j _ => ?_)
  rw [polarIsoMatrix_blockTensor_blockTensor, ← directIteratedBlockEquiv_symm_apply,
    Equiv.symm_apply_apply]

/-- **Normal MPS are finite-range MERA on registers, within `ε`** (arXiv:2307.01696, paragraph
"Connection to MERA"). Let `A` be normal, in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`,
`Tr σ = 1` of eq. (5), and let `0 < t < 1` bound the moduli of the eigenvalues of `E_A` other than
`1`, with `ξ = -1/log t`. Then there is `C > 0` such that for every `s ≥ 1` with `A` blocked over
`s` sites injective, every unitary `u` with `u |0⟩|0⟩ = |ω⟩`, every `ε > 0`, and every `k` and
`M ≥ 1` with `ξ log(C N/ε) ≤ s 2^{k+1}`, `N = M s 2^{k+1}`, the state of the tree-RG MERA with
`k + 1` isometry layers of `A` blocked over `s` sites, read on the `N` sites, has error
`1 - |⟨ψ|φ_N⟩| ≤ ε` against the normalized state `|φ_N⟩` of `A`.

The error bound is `exists_approximationError_le_mul` at `γ = 1/2`, with rate `e^{-q/ξ}`; that
theorem strengthens Lemma 1'(i) of the source, which is stated for `0 < γ < 1/2` with rate
`e^{-γq/ξ}`. The constant `C` does not depend on `s`. -/
theorem exists_registerState_treeMERA_approximationError_le [NeZero D] (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 0 < s → ∀ (hs : Kraus.IsInjective (blockTensor A s))
      (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ), (∀ p, u p (0, 0) = fixedPointPair σ p) →
      ∀ ε : ℝ, 0 < ε → ∀ (k M : ℕ) [NeZero M],
        correlationLength (t : ℂ) * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε) ≤
            s * 2 ^ (k + 1) →
          1 - ‖⟪(treeMERA (blockTensor A s) (isInjective_blockTensor_two hs) k u hu).registerState
            M, normalizedMPVState A (M * (s * 2 ^ (k + 1)))⟫_ℂ‖ ≤ ε := by
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hξ : 0 < correlationLength (t : ℂ) :=
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])
  obtain ⟨K, hK, herr⟩ := exists_approximationError_le_mul A hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm.symm)
    (γ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨K, hK, fun s hs0 hs u hu hu0 ε hε k M _ hk => ?_⟩
  rw [← approximatingMPVState_eq_registerState_treeMERA A hs hσ.posSemidef htr k M u hu hu0]
  refine (herr _ M).trans ?_
  set ξ := correlationLength (t : ℂ)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hq1 : (1 : ℝ) ≤ s * 2 ^ (k + 1) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hs0) (one_le_pow₀ one_le_two)
  have hexp : Real.exp (-(2 * (1 / 2 : ℝ)) * ((s * 2 ^ (k + 1) : ℕ) : ℝ) / ξ) =
      Real.exp (-((s : ℝ) * 2 ^ (k + 1) / ξ)) := by
    push_cast
    ring_nf
  rw [hexp]
  exact mul_mul_exp_neg_div_le_of_mul_log_le hK hM1 hq1 hξ hε (by exact_mod_cast hk)

/-- **The number of layers is `O(log log(N/ε))`, with registers** (arXiv:2307.01696, paragraph
"Connection to MERA": "a finite-range MERA with $O(\log \log N)$ layers"). In the setting of
`exists_registerState_treeMERA_approximationError_le`, for every `s ≥ 1` with `A` blocked over `s`
sites injective, every unitary `u` with `u |0⟩|0⟩ = |ω⟩`, every `ε > 0` and every `M ≥ 1` there
is `k` such that, with `N = M s 2^{k+1}` and `x = ξ log(C N/ε)`, the threshold `x ≤ s 2^{k+1}`
holds, the tree-RG MERA with `k + 1` isometry layers on registers of `s` sites has error at most
`ε`, and `k ≤ log₂(max 1 x)`. The exponent `k` is the least one with the threshold. -/
theorem exists_registerState_treeMERA_approximationError_le_and_le_logb [NeZero D]
    (A : MPSTensor d D) (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 0 < s → ∀ (hs : Kraus.IsInjective (blockTensor A s))
      (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ), (∀ p, u p (0, 0) = fixedPointPair σ p) →
      ∀ ε : ℝ, 0 < ε → ∀ (M : ℕ) [NeZero M], ∃ k : ℕ,
        correlationLength (t : ℂ) * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε) ≤
            s * 2 ^ (k + 1) ∧
        1 - ‖⟪(treeMERA (blockTensor A s) (isInjective_blockTensor_two hs) k u hu).registerState
            M, normalizedMPVState A (M * (s * 2 ^ (k + 1)))⟫_ℂ‖ ≤ ε ∧
        (k : ℝ) ≤ Real.logb 2 (max 1
          (correlationLength (t : ℂ) * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε))) := by
  obtain ⟨C, hC, h⟩ := exists_registerState_treeMERA_approximationError_le A hN hA hσ htr hfix
    ht0 ht1 hlam
  refine ⟨C, hC, fun s hs0 hs u hu hu0 ε hε M _ => ?_⟩
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨k, hk, hlog⟩ := exists_mul_log_le_mul_two_pow_and_le_logb
    (correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])) hC
    (M := (M : ℝ)) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)) hε (s := (s : ℝ))
    (by exact_mod_cast hs0)
  exact ⟨k, hk, h s hs0 hs u hu hu0 ε hε k M hk, hlog⟩

/-- **Normal MPS are finite-range MERA with `O(log log(N/ε))` layers, for the chain lengths
`N = M s 2^{k+1}`** (a scope restriction of arXiv:2307.01696, paragraph "Connection to MERA":
"Hence, within the approximation error $\eps$", normal TI-MPS are contained in the finite-range
MERA with `O(log log N)` layers, which is not restricted to these lengths; see
`docs/paper-gaps/mswc24_tree_mera_scope.tex`). For every normal tensor `A` with
`D ≥ 1` there are `s₀ ≥ 1`, `ξ > 0` and `C > 0` with the following property. For every register
length `s ≥ s₀`, every `ε > 0` and every `M ≥ 1` there are `k` and a binary finite-range MERA
with `k + 1` isometry layers, whose finest isometries write registers of `s` sites, such that
`k ≤ log₂(max 1 (ξ log(C N/ε)))` and its state, read on the `N = M s 2^{k+1}` sites, has error
`1 - |⟨ψ|φ_N⟩| ≤ ε` against the normalized state `|φ_N⟩` of `A`.

The MERA is the tree-RG MERA of the gauge-equivalent rescaling `B` of `A` in the gauge of eq. (5)
(`exists_normalGaugeData`), blocked over `s` sites, with a disentangler preparing the pairs of the
fixed-point state (`exists_disentangler_fixedPointPair`); `s₀` is a length from which on the
blocked tensors of `B` are injective, and the rescaling changes `|φ_N⟩` by a phase only. -/
theorem exists_binaryMERA_registerState_approximationError_le [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) :
    ∃ s₀ : ℕ, 0 < s₀ ∧ ∃ ξ C : ℝ, 0 < ξ ∧ 0 < C ∧ ∀ s : ℕ, s₀ ≤ s → ∀ ε : ℝ, 0 < ε →
      ∀ (M : ℕ) [NeZero M], ∃ (k : ℕ) (𝓜 : BinaryMERA (blockPhysDim d s) D k),
        (k : ℝ) ≤ Real.logb 2 (max 1 (ξ * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε))) ∧
        1 - ‖⟪𝓜.registerState M, normalizedMPVState A (M * (s * 2 ^ (k + 1)))⟫_ℂ‖ ≤ ε := by
  obtain ⟨B, ζ, σ, t, L, hζ, hmpv, hNB, hLC, hσ, htr, hfix, ht0, ht1, hlam, hnorm, hinj⟩ :=
    exists_normalGaugeData hA
  obtain ⟨C, hC, h⟩ := exists_registerState_treeMERA_approximationError_le_and_le_logb B hNB hLC
    hσ htr hfix ht0 ht1 fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm
  obtain ⟨u, hu, hu0⟩ := exists_disentangler_fixedPointPair hσ.posSemidef htr
  refine ⟨L + 1, L.succ_pos, correlationLength (t : ℂ), C,
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm]), hC, fun s hs ε hε M _ => ?_⟩
  have hsB := hinj s (by omega)
  obtain ⟨k, -, herr, hk⟩ := h s (by omega) hsB u hu hu0 ε hε M
  refine ⟨k, treeMERA (blockTensor B s) (isInjective_blockTensor_two hsB) k u hu, hk, ?_⟩
  rwa [← norm_inner_normalizedMPVState_of_mpv_eq hζ (hmpv _)]

end MPSPreparation
