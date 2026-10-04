/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.BlockTensor
import TNLean.MPS.Preparation.IsometricChain

/-!
# Cut ranks of open-chain states and minimal bond dimensions

For a vector `ψ` on `N` sites and a cut `k ≤ N`, the cut matrix
`(σ, τ) ↦ ψ(σ τ)` has rows indexed by the configurations `σ` of the first `k`
sites and columns indexed by the configurations `τ` of the remaining `N - k`
sites. Its rank is the Schmidt rank of `ψ` across the cut, the rank of the
reduced density operator `ρ_k` of arXiv:quant-ph/0608197, lines 456--458. In the
bipartite language of QICLean, `cutRank ψ k` is `Matrix.schmidtRank` of the vector
`(σ, τ) ↦ ψ(σ τ)` on the product of the two configuration spaces; the chain-indexed
form is kept here because the cut moves along the chain.

## Main definitions

* `MPSPreparation.cutConfig` — the configuration `σ τ` of `N` sites.
* `MPSPreparation.cutMatrix`, `MPSPreparation.cutRank` — the cut matrix and its rank.

## Main results

* `OBCChainTensor.cutRank_coeff_le` — every open-boundary representation has bond `k` at least
  the cut rank at `k`.
* `OBCChainTensor.exists_coeff_eq_of_cutRank_le` — conversely, a nonzero vector on a chain of
  positive length whose cut ranks are at most `D` has an open-boundary representation with
  common bound `D` whose bond `k` is exactly the cut rank at `k`, and in which every site except
  the last satisfies `∑_i A_i^† A_i = 1` (every site, when the vector is normalized).
* `MPSPreparation.cutRank_le_pow`, `MPSPreparation.cutRank_le_pow_sub`,
  `MPSPreparation.cutRank_le_pow_half` — the cut rank at `k` is at most `d^k`, `d^{N-k}` and
  `d^{⌊N/2⌋}`.

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

variable {d N : ℕ}

/-- The configuration of `N` sites whose first `k` sites carry `σ` and whose remaining
`N - k` sites carry `τ`. -/
def cutConfig {k : ℕ} (σ : Fin k → Fin d) (τ : Fin (N - k) → Fin d) : Fin N → Fin d :=
  fun p => if h : p.val < k then σ ⟨p.val, h⟩ else τ ⟨p.val - k, by have := p.isLt; omega⟩

/-- The cut matrix of `ψ` at the cut `k`: its entry at the configuration `σ` of the first `k`
sites and the configuration `τ` of the remaining `N - k` sites is `ψ(σ τ)`. Its rank is the rank
of the reduced density operator `ρ_k` of arXiv:quant-ph/0608197, lines 456--458. -/
def cutMatrix (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    Matrix (Fin k → Fin d) (Fin (N - k) → Fin d) ℂ :=
  fun σ τ => ψ (cutConfig σ τ)

/-- The rank of the cut matrix of `ψ` at the cut `k`, the Schmidt rank of `ψ` across the cut
(arXiv:quant-ph/0608197, lines 456--458: the rank of `ρ_k`). -/
noncomputable def cutRank (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) : ℕ :=
  (cutMatrix ψ k).rank

/-- The cut rank at `k` is at most `d^k`, the number of configurations of the first `k` sites. -/
theorem cutRank_le_pow (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) : cutRank ψ k ≤ d ^ k := by
  simpa [cutRank] using (cutMatrix ψ k).rank_le_card_height

/-- The cut rank at `k` is at most `d^{N-k}`, the number of configurations of the last
`N - k` sites. -/
theorem cutRank_le_pow_sub (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) : cutRank ψ k ≤ d ^ (N - k) := by
  simpa [cutRank] using (cutMatrix ψ k).rank_le_card_width

/-- Every cut rank of a vector on `N` sites is at most `d^{⌊N/2⌋}`, the bound of
arXiv:quant-ph/0608197, Theorem `thm:OBC-Vidal` (lines 431--434). -/
theorem cutRank_le_pow_half [NeZero d] (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    cutRank ψ k ≤ d ^ (N / 2) := by
  have hd : 0 < d := NeZero.pos d
  by_cases h : k ≤ N / 2
  · exact (cutRank_le_pow ψ k).trans (Nat.pow_le_pow_right hd h)
  · exact (cutRank_le_pow_sub ψ k).trans (Nat.pow_le_pow_right hd (by omega))

/-- Splitting an ordered matrix product at the cut `k`. -/
theorem eval_cutConfig {D : ℕ} (M : MPSChainTensor d D N) {k : ℕ} (hk : k ≤ N)
    (σ : Fin k → Fin d) (τ : Fin (N - k) → Fin d) :
    eval M (cutConfig σ τ) =
      (List.ofFn fun p : Fin k => M (Fin.castLE hk p) (σ p)).prod *
        (List.ofFn fun q : Fin (N - k) => M ⟨k + q.val, by omega⟩ (τ q)).prod := by
  rw [MPSChainTensor.eval_eq_prod_ofFn, List.ofFn_congr (show N = k + (N - k) by omega),
    List.ofFn_add, List.prod_append]
  refine congrArg₂ _ (congrArg _ (congrArg List.ofFn (funext fun p => ?_)))
    (congrArg _ (congrArg List.ofFn (funext fun q => ?_)))
  · have hp : (Fin.cast (show N = k + (N - k) by omega).symm
        (Fin.castLE (Nat.le_add_right k (N - k)) p)) = Fin.castLE hk p := Fin.ext rfl
    rw [hp]
    simp [cutConfig, p.isLt]
  · have hq : (Fin.cast (show N = k + (N - k) by omega).symm (Fin.natAdd k q)) =
        ⟨k + q.val, by omega⟩ := Fin.ext rfl
    rw [hq]
    simp [cutConfig]

/-- Every configuration of `N` sites is cut at `k ≤ N` into its first `k` and its last
`N - k` sites. -/
theorem cutConfig_restrict {k : ℕ} (hk : k ≤ N) (c : Fin N → Fin d) :
    cutConfig (fun p : Fin k => c (Fin.castLE hk p)) (fun q => c ⟨k + q.val, by omega⟩) = c := by
  funext p
  by_cases hp : p.val < k
  · simp [cutConfig, hp]
  · simp only [cutConfig, hp, dite_false]
    congr 1
    ext
    simp only
    omega

/-- Nonzero vectors have positive cut ranks at every cut `k ≤ N`. -/
theorem cutRank_pos {ψ : (Fin N → Fin d) → ℂ} (hψ : ψ ≠ 0) {k : ℕ} (hk : k ≤ N) :
    0 < cutRank ψ k := by
  obtain ⟨c, hc⟩ : ∃ c, ψ c ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (funext h)
  have hne : cutMatrix ψ k ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 fun p => c (Fin.castLE hk p)) fun q => c ⟨k + q.val, by omega⟩
    simp only [cutMatrix, cutConfig_restrict, Matrix.zero_apply] at this
    exact hc this
  rw [cutRank, Nat.pos_iff_ne_zero, Matrix.rank_eq_finrank_span_cols]
  intro h
  rw [Submodule.finrank_eq_zero, Submodule.span_eq_bot] at h
  exact hne (funext fun σ => funext fun τ => congrFun (h _ ⟨τ, rfl⟩) σ)

/-- A nonzero vector has cut rank one at the cut `0`. -/
theorem cutRank_zero_eq_one {ψ : (Fin N → Fin d) → ℂ} (hψ : ψ ≠ 0) : cutRank ψ 0 = 1 :=
  le_antisymm (by simpa using cutRank_le_pow ψ 0) (cutRank_pos hψ (Nat.zero_le N))

/-- A nonzero vector has cut rank one at the cut `N`. -/
theorem cutRank_self_eq_one {ψ : (Fin N → Fin d) → ℂ} (hψ : ψ ≠ 0) : cutRank ψ N = 1 :=
  le_antisymm (by simpa using cutRank_le_pow_sub ψ N) (cutRank_pos hψ le_rfl)

end MPSPreparation

namespace OBCChainTensor

open MPSPreparation

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
    cutRank B.coeff k ≤ B.bondDim k := by
  classical
  have hD := B.bondBound_pos
  have hk : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
  let L : (Fin k → Fin d) → Matrix (Fin D) (Fin D) ℂ := fun σ =>
    (List.ofFn fun p : Fin k => zeroPad B (Fin.castLE hk p) (σ p)).prod
  let R : (Fin (N - k) → Fin d) → Matrix (Fin D) (Fin D) ℂ := fun τ =>
    (List.ofFn fun q : Fin (N - k) => zeroPad B ⟨k + q.val, by omega⟩ (τ q)).prod
  have hR : ∀ τ (γ : Fin D), B.bondDim k ≤ γ.val → R τ γ ⟨0, hD⟩ = 0 := by
    intro τ γ hγ
    refine prod_ofFn_apply_eq_zero _ _ (B.bondDim k) (fun h α β hα => ?_) (fun h => ?_) γ _ hγ rfl
    · have hcs : (⟨k + 0, by omega⟩ : Fin N).castSucc = k := Fin.ext (by simp)
      refine Matrix.zeroPad_apply_eq_zero _ fun hlt => ?_
      rw [hcs] at hlt
      omega
    · have hkN : k = Fin.last N := Fin.ext (by simp; omega)
      rw [hkN, B.right_dim]
  have hfac : cutMatrix B.coeff k =
      Matrix.of (fun σ (β : Fin (B.bondDim k)) => L σ ⟨0, hD⟩ (Fin.castLE (B.bondDim_le k) β)) *
        Matrix.of fun β τ => R τ (Fin.castLE (B.bondDim_le k) β) ⟨0, hD⟩ := by
    ext σ τ
    rw [Matrix.mul_apply, Fin.sum_castLE_extend_zero _ (B.bondDim_le k)]
    simp only [cutMatrix, coeff_eq_eval_zeroPad, eval_cutConfig _ hk, Matrix.mul_apply,
      Matrix.of_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    split_ifs with hγ
    · rfl
    · exact mul_eq_zero_of_right _ (hR τ γ (not_lt.mp hγ))
  rw [cutRank, hfac]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans (Fintype.card_fin _).le)

end OBCChainTensor

/-! ### Successive Schmidt decompositions -/

namespace MPSPreparation

variable {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)

/-- The column space of the cut matrix at `k`, in the Euclidean space of the first `k` sites. -/
private noncomputable def cutSpace (k : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin k → Fin d)) :=
  Submodule.span ℂ (Set.range fun τ => WithLp.toLp 2 fun σ => cutMatrix ψ k σ τ)

private theorem finrank_cutSpace (k : ℕ) : Module.finrank ℂ (cutSpace ψ k) = cutRank ψ k := by
  rw [cutRank, Matrix.rank_eq_finrank_span_cols, cutSpace,
    ← LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ ((Fin k → Fin d) → ℂ)),
    Submodule.map_span, ← Set.range_comp]
  rfl

/-- Restriction of a vector on `k + 1` sites to the first `k` sites, at a fixed letter on the
last of them. -/
private def sliceLast {k : ℕ} (i : Fin d) :
    EuclideanSpace ℂ (Fin (k + 1) → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin k → Fin d) where
  toFun w := WithLp.toLp 2 fun σ => w (Fin.snoc σ i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The configuration of the last `N - k` sites with first letter `i` followed by `τ`. -/
private def consTail {k : ℕ} (i : Fin d) (τ : Fin (N - (k + 1)) → Fin d) : Fin (N - k) → Fin d :=
  fun q => if h : q.val = 0 then i else τ ⟨q.val - 1, by have := q.isLt; omega⟩

omit ψ in
private theorem cutConfig_snoc {k : ℕ} (σ : Fin k → Fin d) (i : Fin d)
    (τ : Fin (N - (k + 1)) → Fin d) :
    cutConfig (Fin.snoc σ i : Fin (k + 1) → Fin d) τ = cutConfig σ (consTail i τ) := by
  funext p
  simp only [cutConfig, consTail]
  by_cases h1 : p.val < k
  · have h2 : p.val < k + 1 := by omega
    simp [h1, h2, Fin.snoc]
  · by_cases h3 : p.val = k
    · simp [h3, Fin.snoc]
    · have h2 : ¬ p.val < k + 1 := by omega
      have h4 : p.val - k ≠ 0 := by omega
      simp only [h1, h2, h4, dite_false, Nat.sub_sub]

/-- The column space at `k + 1`, restricted to a fixed last letter, lies in the column space at
`k`: a column of the cut matrix at `k + 1` at fixed letter `i` on site `k` is a column of the cut
matrix at `k`. -/
private theorem sliceLast_mem {k : ℕ} (i : Fin d) {w : EuclideanSpace ℂ (Fin (k + 1) → Fin d)}
    (hw : w ∈ cutSpace ψ (k + 1)) : sliceLast i w ∈ cutSpace ψ k := by
  have hle : cutSpace ψ (k + 1) ≤ (cutSpace ψ k).comap (sliceLast i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨τ, rfl⟩
    refine Submodule.subset_span ⟨consTail i τ, ?_⟩
    change (WithLp.toLp 2 fun σ => ψ (cutConfig σ (consTail i τ))) =
      WithLp.toLp 2 fun σ => ψ (cutConfig (Fin.snoc σ i : Fin (k + 1) → Fin d) τ)
    simp only [cutConfig_snoc]
  exact hle hw

/-- The orthonormal basis of the column space at `k`. -/
private noncomputable abbrev cutBasis (k : ℕ) := stdOrthonormalBasis ℂ (cutSpace ψ k)

/-- The site matrices of the successive Schmidt decompositions:
`A_k(i)_{ββ'} = ⟨e^{(k)}_β, e^{(k+1)}_{β'}(· i)⟩`. -/
private noncomputable def cutSite (k : ℕ) (i : Fin d) :
    Matrix (Fin (Module.finrank ℂ (cutSpace ψ k))) (Fin (Module.finrank ℂ (cutSpace ψ (k + 1))))
      ℂ :=
  fun β β' => inner ℂ (cutBasis ψ k β : EuclideanSpace ℂ (Fin k → Fin d))
    (sliceLast i (cutBasis ψ (k + 1) β' : EuclideanSpace ℂ (Fin (k + 1) → Fin d)))

/-- Expansion of a basis vector at `k + 1` in the basis at `k`. -/
private theorem cutBasis_snoc (k : ℕ) (i : Fin d) (β' : Fin (Module.finrank ℂ (cutSpace ψ (k + 1))))
    (σ : Fin k → Fin d) :
    (cutBasis ψ (k + 1) β' : EuclideanSpace ℂ (Fin (k + 1) → Fin d)) (Fin.snoc σ i) =
      ∑ β, (cutBasis ψ k β : EuclideanSpace ℂ (Fin k → Fin d)) σ * cutSite ψ k i β β' := by
  let x : cutSpace ψ k := ⟨sliceLast i (cutBasis ψ (k + 1) β' : _), sliceLast_mem ψ i (by simp)⟩
  have h := congrArg (fun w : cutSpace ψ k => (w : EuclideanSpace ℂ (Fin k → Fin d)) σ)
    ((cutBasis ψ k).sum_repr' x)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
  rw [WithLp.ofLp_sum, Finset.sum_apply] at h
  calc (cutBasis ψ (k + 1) β' : EuclideanSpace ℂ (Fin (k + 1) → Fin d)) (Fin.snoc σ i)
      = (x : EuclideanSpace ℂ (Fin k → Fin d)) σ := rfl
    _ = _ := h.symm
    _ = _ := Finset.sum_congr rfl fun β _ => by simp [cutSite, x, mul_comm]

private theorem sum_inner_sliceLast {k : ℕ} (a b : EuclideanSpace ℂ (Fin (k + 1) → Fin d)) :
    ∑ i, inner ℂ (sliceLast i a) (sliceLast i b) = inner ℂ a b := by
  simp only [PiLp.inner_apply]
  rw [← (Fin.snocEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The site matrices of the successive Schmidt decompositions satisfy `∑_i A_i^† A_i = 1`. -/
private theorem sum_conjTranspose_mul_cutSite (k : ℕ) :
    ∑ i, (cutSite ψ k i)ᴴ * cutSite ψ k i = 1 := by
  ext β' β''
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hi : ∀ i, ∑ β, star (cutSite ψ k i β β') * cutSite ψ k i β β'' =
      inner ℂ (sliceLast i (cutBasis ψ (k + 1) β' : EuclideanSpace ℂ (Fin (k + 1) → Fin d)))
        (sliceLast i (cutBasis ψ (k + 1) β'' : EuclideanSpace ℂ (Fin (k + 1) → Fin d))) := by
    intro i
    let x' : cutSpace ψ k := ⟨_, sliceLast_mem ψ i (cutBasis ψ (k + 1) β').2⟩
    let x'' : cutSpace ψ k := ⟨_, sliceLast_mem ψ i (cutBasis ψ (k + 1) β'').2⟩
    have h := (cutBasis ψ k).sum_inner_mul_inner x' x''
    rw [Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [cutSite, Submodule.coe_inner, RCLike.star_def, inner_conj_symm]
    rfl
  simp only [hi, sum_inner_sliceLast]
  rw [← Submodule.coe_inner, orthonormal_iff_ite.mp (cutBasis ψ (k + 1)).orthonormal,
    Matrix.one_apply]


variable {ψ}

private theorem finrank_cutSpace_zero (hψ : ψ ≠ 0) : Module.finrank ℂ (cutSpace ψ 0) = 1 :=
  (finrank_cutSpace ψ 0).trans (cutRank_zero_eq_one hψ)

/-- The value of the unit basis vector of the one-dimensional column space at the cut `0`. -/
private noncomputable def cutPhase (hψ : ψ ≠ 0) : ℂ :=
  (cutBasis ψ 0 ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩ :
    EuclideanSpace ℂ (Fin 0 → Fin d)) Fin.elim0

private theorem star_cutPhase_mul_self (hψ : ψ ≠ 0) : star (cutPhase hψ) * cutPhase hψ = 1 := by
  have h := (orthonormal_iff_ite.mp (cutBasis ψ 0).orthonormal)
    ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩
    ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩
  simp only [↓reduceIte, Submodule.coe_inner, PiLp.inner_apply, Fintype.sum_unique,
    RCLike.inner_apply] at h
  rw [cutPhase, show (Fin.elim0 : Fin 0 → Fin d) = default from Subsingleton.elim _ _]
  rw [mul_comm]
  exact h

/-- The open chain of the successive Schmidt decompositions of a nonzero vector, with bond `k`
the column space of the cut matrix at `k`. -/
private noncomputable def cutChain {D n : ℕ} {ψ : (Fin (n + 1) → Fin d) → ℂ} (hψ : ψ ≠ 0)
    (hD : ∀ k : Fin (n + 2), cutRank ψ k ≤ D) : OBCChainTensor d D (n + 1) where
  bondDim k := Module.finrank ℂ (cutSpace ψ k)
  bondDim_le k := (finrank_cutSpace ψ k).trans_le (hD k)
  left_dim := finrank_cutSpace_zero hψ
  right_dim := (finrank_cutSpace ψ (n + 1)).trans (cutRank_self_eq_one hψ)
  tensor p i := cutSite ψ p i

/-- The prefix products of the chain of successive Schmidt decompositions are the basis vectors
of the column spaces, up to the phase at the cut `0`. -/
private theorem cutChain_prefix {D n : ℕ} {ψ : (Fin (n + 1) → Fin d) → ℂ} (hψ : ψ ≠ 0)
    (hD : ∀ k : Fin (n + 2), cutRank ψ k ≤ D) (σ : Fin (n + 1) → Fin d) :
    ∀ (k : ℕ) (hk : k ≤ n + 1) (γ : Fin D),
      (List.ofFn fun p : Fin k => OBCChainTensor.zeroPad (cutChain hψ hD) (Fin.castLE hk p)
          (σ (Fin.castLE hk p))).prod ⟨0, (cutChain hψ hD).bondBound_pos⟩ γ =
        if h : γ.val < Module.finrank ℂ (cutSpace ψ k) then
          star (cutPhase hψ) * (cutBasis ψ k ⟨γ.val, h⟩ : EuclideanSpace ℂ (Fin k → Fin d))
            fun p => σ (Fin.castLE hk p)
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
    have hσ : (fun p : Fin (k + 1) => σ (Fin.castLE hk p)) =
        Fin.snoc (fun p : Fin k => σ (Fin.castLE (by omega) p)) (σ ⟨k, by omega⟩) := by
      funext p
      refine Fin.lastCases ?_ (fun p => ?_) p
      · simp only [Fin.snoc_last]
        rfl
      · simp only [Fin.snoc_castSucc]
        rfl
    have ih' : ∀ γ : Fin D, (List.ofFn fun p : Fin k => OBCChainTensor.zeroPad (cutChain hψ hD)
        (Fin.castLE hk p.castSucc) (σ (Fin.castLE hk p.castSucc))).prod
          ⟨0, (cutChain hψ hD).bondBound_pos⟩ γ = _ := ih
    simp only [ih']
    have hZ : ∀ x : Fin D, OBCChainTensor.zeroPad (cutChain hψ hD) (Fin.castLE hk (Fin.last k))
        (σ (Fin.castLE hk (Fin.last k))) x γ' =
          Matrix.zeroPad D (cutSite ψ k (σ ⟨k, by omega⟩)) x γ' := fun x => rfl
    simp only [hZ]
    split_ifs with hγ'
    · rw [hσ, cutBasis_snoc, Finset.mul_sum, Fin.sum_castLE_extend_zero _
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
    (hD : ∀ k : Fin (n + 2), cutRank ψ k ≤ D) :
    ∃ B : OBCChainTensor d D (n + 1), B.coeff = ψ ∧ (∀ k, B.bondDim k = cutRank ψ k) ∧
      (∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B.tensor p i)ᴴ * B.tensor p i = 1) ∧
      (star ψ ⬝ᵥ ψ = 1 → ∑ i, (B.tensor (Fin.last n) i)ᴴ * B.tensor (Fin.last n) i = 1) := by
  classical
  let E := EuclideanSpace ℂ (Fin (n + 1) → Fin d)
  have hr : Module.finrank ℂ (cutSpace ψ (n + 1)) = 1 :=
    (finrank_cutSpace ψ (n + 1)).trans (cutRank_self_eq_one hψ)
  have h1 : 0 < Module.finrank ℂ (cutSpace ψ (n + 1)) := by omega
  let e : E := cutBasis ψ (n + 1) ⟨0, h1⟩
  -- The coefficient of the chain of successive Schmidt decompositions.
  have hC : ∀ σ, (cutChain hψ hD).coeff σ = star (cutPhase hψ) * e σ := fun σ => by
    have h := cutChain_prefix hψ hD σ (n + 1) le_rfl ⟨0, (cutChain hψ hD).bondBound_pos⟩
    rw [dite_eq_left h1] at h
    rw [coeff_eq_eval_zeroPad, MPSChainTensor.eval_eq_prod_ofFn]
    exact h
  -- The vector is a multiple of the unit vector spanning the column space at the cut `n + 1`.
  have hmem : WithLp.toLp 2 ψ ∈ cutSpace ψ (n + 1) := by
    refine Submodule.subset_span ⟨fun q => (by have := q.isLt; omega : False).elim, ?_⟩
    dsimp only
    congr 1
    funext σ
    simp only [cutMatrix]
    congr 1
    funext p
    simp [cutConfig, p.isLt]
  let c₀ : ℂ := inner ℂ e (WithLp.toLp 2 ψ)
  have hψσ : ∀ σ, ψ σ = c₀ * e σ := fun σ => by
    have h := congrArg (fun w : cutSpace ψ (n + 1) => (w : E) σ)
      ((cutBasis ψ (n + 1)).sum_repr' ⟨WithLp.toLp 2 ψ, hmem⟩)
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
    rw [Pi.smul_apply, hC, hψσ, smul_eq_mul]
    linear_combination (c₀ * e σ) * star_cutPhase_mul_self hψ
  · change ∑ i, (if p = Fin.last n then c • cutSite ψ p i else cutSite ψ p i)ᴴ *
      (if p = Fin.last n then c • cutSite ψ p i else cutSite ψ p i) = 1
    simp only [hp, ↓reduceIte]
    exact sum_conjTranspose_mul_cutSite ψ p
  · have he : ∑ σ, star (e σ) * e σ = 1 := by
      have h := (orthonormal_iff_ite.mp (cutBasis ψ (n + 1)).orthonormal) ⟨0, h1⟩ ⟨0, h1⟩
      simp only [↓reduceIte, Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply] at h
      rw [← h]
      exact Finset.sum_congr rfl fun σ _ => mul_comm _ _
    have hcc : star c * c = 1 := by
      have hn' : star c₀ * c₀ = 1 := by
        rw [← hn, dotProduct]
        simp only [Pi.star_apply, hψσ, star_mul']
        rw [← mul_one (star c₀ * c₀), ← he, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
      simp only [c, star_mul']
      linear_combination (star c₀ * c₀) * star_cutPhase_mul_self hψ + hn'
    change ∑ i, (if Fin.last n = Fin.last n then c • cutSite ψ n i else cutSite ψ n i)ᴴ *
      (if Fin.last n = Fin.last n then c • cutSite ψ n i else cutSite ψ n i) = 1
    simp only [↓reduceIte, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, ← Finset.smul_sum, sum_conjTranspose_mul_cutSite]
    rw [mul_comm, hcc, one_smul]

end OBCChainTensor
