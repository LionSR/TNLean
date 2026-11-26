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
* `OBCChainTensor.exists_coeff_eq_of_cutRank_le` — conversely, a nonzero vector on a chain of
  positive length whose cut ranks are at most `D` has an open-boundary representation with
  common bound `D` whose bond `k` is exactly the cut rank at `k`, and in which every site except
  the last satisfies `∑_i A_i^† A_i = 1` (every site, when the vector is normalized).
* `MPSPreparation.cutRank_le_pow`, `MPSPreparation.cutRank_le_pow_sub`,
  `MPSPreparation.cutRank_le_pow_half` — the cut rank at `k` is at most `d^{min(N, k)}`,
  `d^{N-k}` and `d^{⌊N/2⌋}`.

The representation of `exists_coeff_eq_of_cutRank_le` is built by successive Schmidt
decompositions of `ψ` itself (arXiv:quant-ph/0608197, lines 444--447): bond `k` is an
orthonormal basis of the column space of the cut matrix at `k`, and the column space at `k + 1`,
restricted to a fixed last letter, lies in the column space at `k`. This proves the item "any
state for which `max_m rank(ρ_m) ≤ D` can be written as a MPS of bond dimension `D`"
(lines 456--458) and the minimality of the resources in the "recipe" of
arXiv:quant-ph/0608197, lines 1574--1577.

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

/-- The cut after `k` sites has `min N k` sites before it. -/
private theorem card_interval_zero (N k : ℕ) : (interval N 0 k).card = min N k := by
  rw [← Fin.card_filter_val_lt]
  simp [interval]

/-- The cut rank at `k` is at most `d^{min(N, k)}`, the number of configurations of the left
block. -/
theorem cutRank_le_pow (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    ManyBody.cutRank (interval N 0 k) ψ ≤ d ^ min N k := by
  simpa [card_interval_zero] using ManyBody.cutRank_le_pow_card (D := interval N 0 k) ψ

/-- The cut rank at `k` is at most `d^{N-k}`, the number of configurations of the last
`N - k` sites. -/
theorem cutRank_le_pow_sub (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    ManyBody.cutRank (interval N 0 k) ψ ≤ d ^ (N - k) := by
  have h := ManyBody.cutRank_le_pow_card_compl (D := interval N 0 k) ψ
  rwa [Finset.card_compl, Fintype.card_fin, card_interval_zero,
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

/-! ### Successive Schmidt decompositions -/

namespace MPSPreparation

open ManyBody (interval mem_interval)

variable {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)

/-- No site lies before the cut `0`. -/
private instance isEmpty_interval_zero : IsEmpty {v : Fin N // v ∈ interval N 0 0} :=
  ⟨fun v ↦ absurd (mem_interval.mp v.2).2 (Nat.not_lt_zero _)⟩

/-- The column space of the cut matrix at `k`, in the Euclidean space of the left block. -/
private noncomputable def cutSpace (k : ℕ) : Submodule ℂ
    (EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k))) :=
  Submodule.span ℂ (Set.range fun τ =>
    WithLp.toLp 2 fun σ => ManyBody.cutMatrix (interval N 0 k) ψ σ τ)

private theorem finrank_cutSpace (k : ℕ) :
    Module.finrank ℂ (cutSpace ψ k) = ManyBody.cutRank (interval N 0 k) ψ := by
  rw [ManyBody.cutRank, Matrix.rank_eq_finrank_span_cols, cutSpace,
    ← LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ
      (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) → ℂ)),
    Submodule.map_span, ← Set.range_comp]
  rfl

omit ψ in
/-- The configuration of the left block after `k + 1` sites that agrees with `σ` before the
site `k` and carries `i` at it. -/
private def extendLeft {k : ℕ}
    (σ : ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) (i : Fin d) :
    ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)) :=
  fun v => if h : v.1.val < k then σ ⟨v.1, mem_interval.mpr ⟨Nat.zero_le _, h⟩⟩ else i

omit ψ in
/-- For `k < N`, the configurations of the left block after `k + 1` sites are the pairs of a
letter at the site `k` and a configuration of the left block after `k` sites. -/
private def extendLeftEquiv {k : ℕ} (hk : k < N) :
    Fin d × ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) ≃
      ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)) where
  toFun x := extendLeft x.2 x.1
  invFun w := (w ⟨⟨k, hk⟩, mem_interval.mpr ⟨Nat.zero_le _, Nat.lt_succ_self k⟩⟩,
    fun v => w ⟨v.1, mem_interval.mpr ⟨Nat.zero_le _, by
      have := (mem_interval.mp v.2).2
      omega⟩⟩)
  left_inv x := by
    refine Prod.ext ?_ (funext fun v => ?_)
    · simp [extendLeft]
    · have hv := (mem_interval.mp v.2).2
      simp [extendLeft, hv]
  right_inv w := by
    funext v
    simp only [extendLeft]
    split_ifs with h
    · rfl
    · exact congrArg w (Subtype.ext (Fin.ext (by
        have := (mem_interval.mp v.2).2
        show k = v.1.val
        omega)))

/-- Restriction of a vector on the left block after `k + 1` sites to the left block after `k`
sites, at a fixed letter on the site `k`. -/
private def sliceLast {k : ℕ} (i : Fin d) :
    EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1))) →ₗ[ℂ]
      EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) where
  toFun w := WithLp.toLp 2 fun σ => w (extendLeft σ i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit ψ in
/-- The configuration of the sites `p ≥ k` with letter `i` at `k` followed by `τ`. -/
private def consTail {k : ℕ} (i : Fin d)
    (τ : ManyBody.ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1))) :
    ManyBody.ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) :=
  fun v => if h : v.1.val = k then i else τ ⟨v.1, fun hv => by
    have h1 := (mem_interval.mp hv).2
    have h2 : ¬ v.1.val < k := fun h' => v.2 (mem_interval.mpr ⟨Nat.zero_le _, h'⟩)
    omega⟩

omit ψ in
private theorem cutEquiv_symm_extendLeft {k : ℕ}
    (σ : ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) (i : Fin d)
    (τ : ManyBody.ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1))) :
    (ManyBody.cutEquiv _ (interval N 0 (k + 1))).symm (extendLeft σ i, τ) =
      (ManyBody.cutEquiv _ (interval N 0 k)).symm (σ, consTail i τ) := by
  funext p
  by_cases h1 : p.val < k
  · rw [ManyBody.cutEquiv_symm_apply_mem (v := p) _ _ (mem_interval.mpr ⟨Nat.zero_le _, by omega⟩),
      ManyBody.cutEquiv_symm_apply_mem (v := p) _ _ (mem_interval.mpr ⟨Nat.zero_le _, h1⟩)]
    simp [extendLeft, h1]
  · have h1' : p ∉ interval N 0 k := fun h => h1 ((mem_interval.mp h).2)
    rw [ManyBody.cutEquiv_symm_apply_not_mem _ _ h1']
    by_cases h3 : p.val = k
    · rw [ManyBody.cutEquiv_symm_apply_mem (v := p) _ _
        (mem_interval.mpr ⟨Nat.zero_le _, by omega⟩)]
      simp [extendLeft, consTail, h3]
    · have h2 : p ∉ interval N 0 (k + 1) := fun h => by have := (mem_interval.mp h).2; omega
      rw [ManyBody.cutEquiv_symm_apply_not_mem _ _ h2]
      simp [consTail, h3]

/-- The column space at `k + 1`, restricted to a fixed last letter, lies in the column space at
`k`: a column of the cut matrix at `k + 1` at fixed letter `i` on site `k` is a column of the cut
matrix at `k`. -/
private theorem sliceLast_mem {k : ℕ} (i : Fin d)
    {w : EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)))}
    (hw : w ∈ cutSpace ψ (k + 1)) : sliceLast i w ∈ cutSpace ψ k := by
  have hle : cutSpace ψ (k + 1) ≤ (cutSpace ψ k).comap (sliceLast i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨τ, rfl⟩
    refine Submodule.subset_span ⟨consTail i τ, ?_⟩
    change (WithLp.toLp 2 fun σ => ψ ((ManyBody.cutEquiv _ (interval N 0 k)).symm
        (σ, consTail i τ))) =
      WithLp.toLp 2 fun σ => ψ ((ManyBody.cutEquiv _ (interval N 0 (k + 1))).symm
        (extendLeft σ i, τ))
    simp only [cutEquiv_symm_extendLeft]
  exact hle hw

/-- The orthonormal basis of the column space at `k`. -/
private noncomputable abbrev cutBasis (k : ℕ) := stdOrthonormalBasis ℂ (cutSpace ψ k)

/-- The site matrices of the successive Schmidt decompositions:
`A_k(i)_{ββ'} = ⟨e^{(k)}_β, e^{(k+1)}_{β'}(· i)⟩`. -/
private noncomputable def cutSite (k : ℕ) (i : Fin d) :
    Matrix (Fin (Module.finrank ℂ (cutSpace ψ k))) (Fin (Module.finrank ℂ (cutSpace ψ (k + 1))))
      ℂ :=
  fun β β' => inner ℂ (cutBasis ψ k β).1 (sliceLast i (cutBasis ψ (k + 1) β').1)

/-- Expansion of a basis vector at `k + 1` in the basis at `k`. -/
private theorem cutBasis_extendLeft (k : ℕ) (i : Fin d)
    (β' : Fin (Module.finrank ℂ (cutSpace ψ (k + 1))))
    (σ : ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) :
    (cutBasis ψ (k + 1) β').1 (extendLeft σ i) =
      ∑ β, (cutBasis ψ k β).1 σ * cutSite ψ k i β β' := by
  let x : cutSpace ψ k := ⟨sliceLast i (cutBasis ψ (k + 1) β').1,
    sliceLast_mem ψ i (cutBasis ψ (k + 1) β').2⟩
  have h := congrArg (fun w : cutSpace ψ k => w.1 σ) ((cutBasis ψ k).sum_repr' x)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
  rw [WithLp.ofLp_sum, Finset.sum_apply] at h
  calc (cutBasis ψ (k + 1) β').1 (extendLeft σ i)
      = x.1 σ := rfl
    _ = _ := h.symm
    _ = _ := Finset.sum_congr rfl fun β _ => by simp [cutSite, x, mul_comm]

omit ψ in
private theorem sum_inner_sliceLast {k : ℕ} (hk : k < N)
    (a b : EuclideanSpace ℂ
      (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)))) :
    ∑ i, inner ℂ (sliceLast i a) (sliceLast i b) = inner ℂ a b := by
  simp only [PiLp.inner_apply]
  rw [← (extendLeftEquiv hk).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The site matrices of the successive Schmidt decompositions before the last site satisfy
`∑_i A_i^† A_i = 1`. -/
private theorem sum_conjTranspose_mul_cutSite {k : ℕ} (hk : k < N) :
    ∑ i, (cutSite ψ k i)ᴴ * cutSite ψ k i = 1 := by
  ext β' β''
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hi : ∀ i, ∑ β, star (cutSite ψ k i β β') * cutSite ψ k i β β'' =
      inner ℂ (sliceLast i (cutBasis ψ (k + 1) β').1)
        (sliceLast i (cutBasis ψ (k + 1) β'').1) := by
    intro i
    let x' : cutSpace ψ k := ⟨_, sliceLast_mem ψ i (cutBasis ψ (k + 1) β').2⟩
    let x'' : cutSpace ψ k := ⟨_, sliceLast_mem ψ i (cutBasis ψ (k + 1) β'').2⟩
    have h := (cutBasis ψ k).sum_inner_mul_inner x' x''
    rw [Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [cutSite, Submodule.coe_inner, RCLike.star_def, inner_conj_symm]
    rfl
  simp only [hi, sum_inner_sliceLast hk]
  rw [← Submodule.coe_inner, orthonormal_iff_ite.mp (cutBasis ψ (k + 1)).orthonormal,
    Matrix.one_apply]

variable {ψ}

private theorem finrank_cutSpace_zero (hψ : ψ ≠ 0) : Module.finrank ℂ (cutSpace ψ 0) = 1 :=
  (finrank_cutSpace ψ 0).trans (cutRank_zero_eq_one hψ)

/-- The value of the unit basis vector of the one-dimensional column space at the cut `0`. -/
private noncomputable def cutPhase (hψ : ψ ≠ 0) : ℂ :=
  (cutBasis ψ 0 ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩).1 default

private theorem star_cutPhase_mul_self (hψ : ψ ≠ 0) : star (cutPhase hψ) * cutPhase hψ = 1 := by
  have h := (orthonormal_iff_ite.mp (cutBasis ψ 0).orthonormal)
    ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩
    ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩
  simp only [↓reduceIte, Submodule.coe_inner, PiLp.inner_apply, Fintype.sum_unique,
    RCLike.inner_apply] at h
  rw [cutPhase, mul_comm]
  exact h

/-- The open chain of the successive Schmidt decompositions of a nonzero vector, with bond `k`
the column space of the cut matrix at `k`. -/
private noncomputable def cutChain {D n : ℕ} {ψ : (Fin (n + 1) → Fin d) → ℂ} (hψ : ψ ≠ 0)
    (hD : ∀ k : Fin (n + 2), ManyBody.cutRank (interval (n + 1) 0 k) ψ ≤ D) :
    OBCChainTensor d D (n + 1) where
  bondDim k := Module.finrank ℂ (cutSpace ψ k)
  bondDim_le k := (finrank_cutSpace ψ k).trans_le (hD k)
  left_dim := finrank_cutSpace_zero hψ
  right_dim := (finrank_cutSpace ψ (n + 1)).trans (cutRank_self_eq_one hψ)
  tensor p i := cutSite ψ p i

/-- The prefix products of the chain of successive Schmidt decompositions are the basis vectors
of the column spaces, up to the phase at the cut `0`. -/
private theorem cutChain_prefix {D n : ℕ} {ψ : (Fin (n + 1) → Fin d) → ℂ} (hψ : ψ ≠ 0)
    (hD : ∀ k : Fin (n + 2), ManyBody.cutRank (interval (n + 1) 0 k) ψ ≤ D)
    (σ : Fin (n + 1) → Fin d) :
    ∀ (k : ℕ) (hk : k ≤ n + 1) (γ : Fin D),
      (List.ofFn fun p : Fin k => OBCChainTensor.zeroPad (cutChain hψ hD) (Fin.castLE hk p)
          (σ (Fin.castLE hk p))).prod ⟨0, (cutChain hψ hD).bondBound_pos⟩ γ =
        if h : γ.val < Module.finrank ℂ (cutSpace ψ k) then
          star (cutPhase hψ) * (cutBasis ψ k ⟨γ.val, h⟩).1 fun v => σ v.1
        else 0
  | 0, hk, γ => by
    have h1 := finrank_cutSpace_zero hψ
    rw [List.ofFn_zero, List.prod_nil]
    by_cases hγ : γ.val = 0
    · have hγ' : γ.val < Module.finrank ℂ (cutSpace ψ 0) := by omega
      rw [dite_eq_left hγ', show (⟨0, _⟩ : Fin D) = γ from Fin.ext hγ.symm, Matrix.one_apply_eq,
        ← star_cutPhase_mul_self hψ]
      congr 2
      have h0 : (⟨γ.val, hγ'⟩ : Fin (Module.finrank ℂ (cutSpace ψ 0))) = ⟨0, by omega⟩ :=
        Fin.ext hγ
      rw [h0, cutPhase]
      exact congrArg _ (Subsingleton.elim _ _)
    · rw [dite_eq_right (by omega), Matrix.one_apply_ne fun h => hγ (by rw [← h])]
  | k + 1, hk, γ' => by
    have ih := cutChain_prefix hψ hD σ k (by omega)
    rw [List.ofFn_succ', List.prod_concat, Matrix.mul_apply]
    have hσ : (fun v : {v // v ∈ interval (n + 1) 0 (k + 1)} => σ v.1) =
        extendLeft (fun v : {v // v ∈ interval (n + 1) 0 k} => σ v.1) (σ ⟨k, by omega⟩) := by
      funext v
      simp only [extendLeft]
      split_ifs with h
      · rfl
      · exact congrArg σ (Fin.ext (by
          have := (mem_interval.mp v.2).2
          show v.1.val = k
          omega))
    have ih' : ∀ γ : Fin D, (List.ofFn fun p : Fin k => OBCChainTensor.zeroPad (cutChain hψ hD)
        (Fin.castLE hk p.castSucc) (σ (Fin.castLE hk p.castSucc))).prod
          ⟨0, (cutChain hψ hD).bondBound_pos⟩ γ = _ := ih
    simp only [ih']
    have hZ : ∀ x : Fin D, OBCChainTensor.zeroPad (cutChain hψ hD) (Fin.castLE hk (Fin.last k))
        (σ (Fin.castLE hk (Fin.last k))) x γ' =
          Matrix.zeroPad D (cutSite ψ k (σ ⟨k, by omega⟩)) x γ' := fun x => rfl
    simp only [hZ]
    split_ifs with hγ'
    · rw [hσ, cutBasis_extendLeft, Finset.mul_sum, Fin.sum_castLE_extend_zero _
        ((finrank_cutSpace ψ k).trans_le (hD ⟨k, by omega⟩))]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with hx
      · rw [Matrix.zeroPad_apply_of_lt _ hx hγ', mul_assoc]
      · simp
    · refine Finset.sum_eq_zero fun x _ => ?_
      rw [Matrix.zeroPad_apply_eq_zero _ (fun h => hγ' h.2), mul_zero]

end MPSPreparation

namespace OBCChainTensor

open MPSPreparation
open ManyBody (interval mem_interval)

variable {d : ℕ}

/-- **Representation with the cut ranks as bond dimensions.** A nonzero vector on a chain of
positive length whose cut ranks are all at most `D` has an open-boundary representation with
common bound `D` whose bond `k` has dimension exactly the cut rank at `k`, and in which every
site except the last satisfies `∑_i A_i^† A_i = 1`; when the vector is normalized, the last site
satisfies it as well.

The construction is the successive Schmidt decompositions of arXiv:quant-ph/0608197,
lines 444--447, and proves the item "any state for which `max_m rank(ρ_m) ≤ D` can be written as
a MPS of bond dimension `D`" (lines 456--458); with `OBCChainTensor.cutRank_coeff_le` the bond
dimensions are the least possible at every cut simultaneously, the "minimal resources" of
lines 1574--1577. -/
theorem exists_coeff_eq_of_cutRank_le {D n : ℕ} {ψ : (Fin (n + 1) → Fin d) → ℂ} (hψ : ψ ≠ 0)
    (hD : ∀ k : Fin (n + 2), ManyBody.cutRank (interval (n + 1) 0 k) ψ ≤ D) :
    ∃ B : OBCChainTensor d D (n + 1), B.coeff = ψ ∧
      (∀ k, B.bondDim k = ManyBody.cutRank (interval (n + 1) 0 k) ψ) ∧
      (∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B.tensor p i)ᴴ * B.tensor p i = 1) ∧
      (star ψ ⬝ᵥ ψ = 1 → ∑ i, (B.tensor (Fin.last n) i)ᴴ * B.tensor (Fin.last n) i = 1) := by
  classical
  -- The configurations of `n + 1` sites are the configurations of the full left block.
  let ρ : (Fin (n + 1) → Fin d) ≃
      ManyBody.RegionConfig (fun _ : Fin (n + 1) ↦ Fin d) (interval (n + 1) 0 (n + 1)) :=
    { toFun := fun σ v => σ v.1
      invFun := fun x p => x ⟨p, mem_interval.mpr ⟨Nat.zero_le _, p.isLt⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hr : Module.finrank ℂ (cutSpace ψ (n + 1)) = 1 :=
    (finrank_cutSpace ψ (n + 1)).trans (cutRank_self_eq_one hψ)
  have h1 : 0 < Module.finrank ℂ (cutSpace ψ (n + 1)) := by omega
  let e := (cutBasis ψ (n + 1) ⟨0, h1⟩).1
  -- The coefficient of the chain of successive Schmidt decompositions.
  have hC : ∀ σ, (cutChain hψ hD).coeff σ = star (cutPhase hψ) * e (ρ σ) := fun σ => by
    have h := cutChain_prefix hψ hD σ (n + 1) le_rfl ⟨0, (cutChain hψ hD).bondBound_pos⟩
    rw [dite_eq_left h1] at h
    rw [coeff_eq_eval_zeroPad, MPSChainTensor.eval_eq_prod_ofFn]
    exact h
  -- The vector is a multiple of the unit vector spanning the column space at the cut `n + 1`.
  let τ₀ : ManyBody.ComplConfig (fun _ : Fin (n + 1) ↦ Fin d) (interval (n + 1) 0 (n + 1)) :=
    fun v => absurd (mem_interval.mpr ⟨Nat.zero_le _, v.1.isLt⟩) v.2
  let ψ' : EuclideanSpace ℂ
      (ManyBody.RegionConfig (fun _ : Fin (n + 1) ↦ Fin d) (interval (n + 1) 0 (n + 1))) :=
    WithLp.toLp 2 fun σ =>
    ManyBody.cutMatrix (interval (n + 1) 0 (n + 1)) ψ σ τ₀
  have hmem : ψ' ∈ cutSpace ψ (n + 1) := Submodule.subset_span ⟨τ₀, rfl⟩
  have hρ : ∀ σ, ψ σ = ψ' (ρ σ) := fun σ => by
    change ψ σ = ψ ((ManyBody.cutEquiv _ (interval (n + 1) 0 (n + 1))).symm (ρ σ, τ₀))
    congr 1
    funext p
    exact (ManyBody.cutEquiv_symm_apply_mem (ρ σ) τ₀
      (mem_interval.mpr ⟨Nat.zero_le _, p.isLt⟩)).symm
  let c₀ : ℂ := inner ℂ e ψ'
  have hψσ : ∀ σ, ψ' σ = c₀ * e σ := fun σ => by
    have h := congrArg (fun w : cutSpace ψ (n + 1) => w.1 σ)
      ((cutBasis ψ (n + 1)).sum_repr' ⟨ψ', hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single ⟨0, h1⟩] at h
    · exact h.symm
    · intro β _ hβ
      exact absurd (Fin.ext (by have := β.isLt; omega)) hβ
    · simp
  let c : ℂ := cutPhase hψ * c₀
  refine ⟨(cutChain hψ hD).smulSite (Fin.last n) c, ?_, fun k => finrank_cutSpace ψ k,
    fun p hp => ?_, fun hn => ?_⟩
  · rw [coeff_smulSite]
    funext σ
    rw [Pi.smul_apply, hC, hρ, hψσ, smul_eq_mul]
    linear_combination (c₀ * e (ρ σ)) * star_cutPhase_mul_self hψ
  · change ∑ i, (if p = Fin.last n then c • cutSite ψ p i else cutSite ψ p i)ᴴ *
      (if p = Fin.last n then c • cutSite ψ p i else cutSite ψ p i) = 1
    simp only [hp, ↓reduceIte]
    exact sum_conjTranspose_mul_cutSite ψ p.isLt
  · have he : ∑ σ, star (e (ρ σ)) * e (ρ σ) = 1 := by
      have h := (orthonormal_iff_ite.mp (cutBasis ψ (n + 1)).orthonormal) ⟨0, h1⟩ ⟨0, h1⟩
      simp only [↓reduceIte, Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply] at h
      rw [← h]
      exact (ρ.sum_comp fun x => star (e x) * e x).trans
        (Finset.sum_congr rfl fun x _ => mul_comm _ _)
    have hcc : star c * c = 1 := by
      have hn' : star c₀ * c₀ = 1 := by
        rw [← hn, dotProduct]
        simp only [Pi.star_apply, hρ, hψσ, star_mul']
        rw [← mul_one (star c₀ * c₀), ← he, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
      simp only [c, star_mul']
      linear_combination (star c₀ * c₀) * star_cutPhase_mul_self hψ + hn'
    change ∑ i, (if Fin.last n = Fin.last n then c • cutSite ψ n i else cutSite ψ n i)ᴴ *
      (if Fin.last n = Fin.last n then c • cutSite ψ n i else cutSite ψ n i) = 1
    simp only [↓reduceIte, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, ← Finset.smul_sum, sum_conjTranspose_mul_cutSite ψ (Nat.lt_succ_self n)]
    rw [mul_comm, hcc, one_smul]

end OBCChainTensor
