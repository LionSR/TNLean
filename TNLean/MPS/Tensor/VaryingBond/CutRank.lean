/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Chain.BlockTensor
import TNLean.MPS.Tensor.VaryingBond.IsometricChain
import TNLean.MPS.Tensor.VaryingBond.OpenMPS

/-!
# Cut ranks of open-chain states and minimal bond dimensions

For a vector `ψ` on `N` sites and a cut after `k` sites, the cut matrix
`ManyBody.cutMatrix (interval N 0 k) ψ` of QICLean has rows indexed by the configurations of the
left block `interval N 0 k` of the sites `p < k` and columns indexed by the configurations of the
remaining sites; its entry at `(σ, τ)` is the coefficient of `ψ` at the configuration glued from
`σ` and `τ`. Its rank `ManyBody.cutRank (interval N 0 k) ψ` is the Schmidt rank of `ψ` across the
cut, the rank of the reduced density operator `ρ_k` of arXiv:quant-ph/0608197, lines 456--458.

## Main results

* `MPSPreparation.eval_cutEquiv_symm` — an ordered matrix product splits at the cut.
* `OBCChainTensor.cutRank_coeff_le` — every open-boundary representation has bond `k` at least
  the cut rank at `k`.
* `MPSPreparation.cutRank_le_pow`, `MPSPreparation.cutRank_le_pow_sub`,
  `MPSPreparation.cutRank_le_pow_half` — the cut rank at `k` is at most `d^{min(N, k)}`,
  `d^{N-k}` and `d^{⌊N/2⌋}`.

The converse, a representation whose bonds are exactly the cut ranks, is
`OBCChainTensor.exists_coeff_eq_of_cutRank_le` in
`TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentation`.

## References

* Pérez-García, Verstraete, Wolf, Cirac, *Matrix product state representations*,
  arXiv:quant-ph/0608197, lines 419--458 and 1574--1577 of
  `Papers/quant-ph_0608197/MPSarchive.tex`.
* Schön, Solano, Verstraete, Cirac, Wolf, *Sequential generation of entangled
  multiqubit states*, arXiv:quant-ph/0501096, lines 200--202 of
  `References/quant-ph_0501096/PhotoMPS.tex` ("simple rank considerations").
-/

open scoped BigOperators Matrix ComplexConjugate

namespace MPSPreparation

open MPSChainTensor (eval)
open ManyBody (interval mem_interval)

variable {d N : ℕ}

/-- The cut rank at `k` is at most `d^{min(N, k)}`, the number of configurations of the left
block. -/
theorem cutRank_le_pow (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    ManyBody.cutRank (interval N 0 k) ψ ≤ d ^ min N k := by
  simpa [ManyBody.card_interval_zero] using ManyBody.cutRank_le_pow_card (D := interval N 0 k) ψ

/-- The cut rank at `k` is at most `d^{N-k}`, the number of configurations of the last
`N - k` sites. -/
theorem cutRank_le_pow_sub (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    ManyBody.cutRank (interval N 0 k) ψ ≤ d ^ (N - k) := by
  have h := ManyBody.cutRank_le_pow_card_compl (D := interval N 0 k) ψ
  rwa [Finset.card_compl, Fintype.card_fin, ManyBody.card_interval_zero,
    show N - min N k = N - k by omega] at h

/-- Every cut rank of a vector on `N` sites is at most `d^{⌊N/2⌋}`, the bound of
arXiv:quant-ph/0608197, Theorem `thm:OBC-Vidal` (lines 431--434). -/
theorem cutRank_le_pow_half [NeZero d] (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    ManyBody.cutRank (interval N 0 k) ψ ≤ d ^ (N / 2) := by
  have hd : 0 < d := NeZero.pos d
  by_cases h : k ≤ N / 2
  · exact (cutRank_le_pow ψ k).trans (Nat.pow_le_pow_right hd (by omega))
  · exact (cutRank_le_pow_sub ψ k).trans (Nat.pow_le_pow_right hd (by omega))

/-- **Splitting an ordered matrix product at the cut after `k` sites.** At the configuration
glued from `σ` on the left block and `τ` on the remaining sites, the product is the product of
the first `k` factors, read from `σ`, times the product of the last `N - k`, read from `τ`. -/
theorem eval_cutEquiv_symm {D : ℕ} (M : MPSChainTensor d D N) {k : ℕ} (hk : k ≤ N)
    (σ : ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k))
    (τ : ManyBody.ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) :
    eval M ((ManyBody.cutEquiv _ (interval N 0 k)).symm (σ, τ)) =
      (List.ofFn fun p : Fin k =>
          M (Fin.castLE hk p)
            (σ ⟨Fin.castLE hk p, mem_interval.mpr ⟨Nat.zero_le _, p.isLt⟩⟩)).prod *
        (List.ofFn fun q : Fin (N - k) => M ⟨k + q.val, by omega⟩
          (τ ⟨⟨k + q.val, by omega⟩, fun h => by
            have := (mem_interval.mp h).2
            simp at this⟩)).prod := by
  rw [MPSChainTensor.eval_eq_prod_ofFn, List.ofFn_congr (show N = k + (N - k) by omega),
    List.ofFn_add, List.prod_append]
  refine congrArg₂ _ (congrArg _ (congrArg List.ofFn (funext fun p => ?_)))
    (congrArg _ (congrArg List.ofFn (funext fun q => ?_)))
  · have hp : (Fin.cast (show N = k + (N - k) by omega).symm
        (Fin.castLE (Nat.le_add_right k (N - k)) p)) = Fin.castLE hk p := Fin.ext rfl
    rw [hp, ManyBody.cutEquiv_symm_apply_mem (v := Fin.castLE hk p) _ _
      (mem_interval.mpr ⟨Nat.zero_le _, p.isLt⟩)]
  · have hq : (Fin.cast (show N = k + (N - k) by omega).symm (Fin.natAdd k q)) =
        ⟨k + q.val, by omega⟩ := Fin.ext rfl
    rw [hq, ManyBody.cutEquiv_symm_apply_not_mem (v := (⟨k + q.val, by omega⟩ : Fin N)) _ _
      (fun h => by have := (mem_interval.mp h).2; simp at this)]

/-- A nonzero vector has cut rank one at the cut `0`. -/
theorem cutRank_zero_eq_one {ψ : (Fin N → Fin d) → ℂ} (hψ : ψ ≠ 0) :
    ManyBody.cutRank (interval N 0 0) ψ = 1 :=
  le_antisymm (by simpa using cutRank_le_pow ψ 0) (ManyBody.cutRank_pos hψ)

/-- A nonzero vector has cut rank one at the cut `N`. -/
theorem cutRank_self_eq_one {ψ : (Fin N → Fin d) → ℂ} (hψ : ψ ≠ 0) :
    ManyBody.cutRank (interval N 0 N) ψ = 1 :=
  le_antisymm (by simpa using cutRank_le_pow_sub ψ N) (ManyBody.cutRank_pos hψ)

end MPSPreparation

namespace OBCChainTensor

open MPSPreparation
open ManyBody (interval mem_interval)

variable {d D N : ℕ}

/-- A product of square matrices whose first factor vanishes on the rows `γ ≥ a` vanishes on
those rows; an empty product vanishes off the diagonal. -/
private theorem prod_ofFn_apply_eq_zero : ∀ (m : ℕ) (f : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (a : ℕ), (∀ h : 0 < m, IsRowSupportedBelow a (f ⟨0, h⟩)) → (m = 0 → 1 ≤ a) →
    ∀ γ z : Fin D, a ≤ γ.val → z.val = 0 → (List.ofFn f).prod γ z = 0
  | 0, _, _, _, ha, γ, z, hγ, hz => by
    have hne : γ ≠ z := fun h => by
      have := ha rfl
      rw [h] at hγ
      omega
    simp [Matrix.one_apply_ne hne]
  | m + 1, f, a, hf, _, γ, z, hγ, _ => by
    rw [List.ofFn_succ, List.prod_cons]
    exact (hf (Nat.succ_pos m)).mul _ γ z hγ

/-- **Cut ranks bound the bond dimensions.** In every open-boundary representation of a vector,
bond `k` has dimension at least the cut rank at `k`: the cut matrix factors through the bond
space at `k`.

This is the converse of the item "any state for which `max_m rank(ρ_m) ≤ D` can be written as a
MPS of bond dimension `D`" of arXiv:quant-ph/0608197 (lines 456--458), which the source does not
state; together with that item it gives the "minimal resources" of the recipe (lines
1574--1577). -/
theorem cutRank_coeff_le (B : OBCChainTensor d D N) (k : Fin (N + 1)) :
    ManyBody.cutRank (interval N 0 k) B.coeff ≤ B.bondDim k := by
  classical
  have hD := B.bondBound_pos
  have hk : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
  let L : ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) →
      Matrix (Fin D) (Fin D) ℂ := fun σ =>
    (List.ofFn fun p : Fin k => zeroPad B (Fin.castLE hk p)
      (σ ⟨Fin.castLE hk p, mem_interval.mpr ⟨Nat.zero_le _, p.isLt⟩⟩)).prod
  let R : ManyBody.ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) →
      Matrix (Fin D) (Fin D) ℂ := fun τ =>
    (List.ofFn fun q : Fin (N - k) => zeroPad B ⟨k + q.val, by omega⟩
      (τ ⟨⟨k + q.val, by omega⟩, fun h => by have := (mem_interval.mp h).2; simp at this⟩)).prod
  have hR : ∀ τ (γ : Fin D), B.bondDim k ≤ γ.val → R τ γ ⟨0, hD⟩ = 0 := by
    intro τ γ hγ
    refine prod_ofFn_apply_eq_zero _ _ (B.bondDim k) (fun h α β hα => ?_) (fun h => ?_) γ _ hγ rfl
    · have hcs : (⟨k + 0, by omega⟩ : Fin N).castSucc = k := Fin.ext (by simp)
      refine Matrix.zeroPad_apply_eq_zero _ fun hlt => ?_
      rw [hcs] at hlt
      omega
    · have hkN : k = Fin.last N := Fin.ext (by simp; omega)
      rw [hkN, B.right_dim]
  have hfac : ManyBody.cutMatrix (interval N 0 k) B.coeff =
      Matrix.of (fun σ (β : Fin (B.bondDim k)) => L σ ⟨0, hD⟩ (Fin.castLE (B.bondDim_le k) β)) *
        Matrix.of fun β τ => R τ (Fin.castLE (B.bondDim_le k) β) ⟨0, hD⟩ := by
    ext σ τ
    rw [Matrix.mul_apply, Fin.sum_castLE_extend_zero _ (B.bondDim_le k)]
    simp only [ManyBody.cutMatrix_apply, coeff_eq_eval_zeroPad, eval_cutEquiv_symm _ hk,
      Matrix.mul_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    split_ifs with hγ
    · rfl
    · exact mul_eq_zero_of_right _ (hR τ γ (not_lt.mp hγ))
  rw [ManyBody.cutRank, hfac]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans (Fintype.card_fin _).le)

end OBCChainTensor
