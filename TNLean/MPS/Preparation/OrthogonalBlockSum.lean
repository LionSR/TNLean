/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrthogonalSumPolar

/-!
# Direct sums of blocks with orthogonal states

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") write a tensor that is not normal as a direct sum of normal
blocks, `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S2)). This file treats the case in
which every multiplicity is `m_j = 1`: `Aⁱ = ⊕ⱼ μⱼ A_jⁱ`, with the block `j` placed on the bond
coordinates `ι_j : Fin D_j → Fin D` (`MPSTensor.blockSum`). It evaluates the ingredients of the
approximating state of eq. (S7) under the hypothesis that the `q`-site states of distinct blocks
are orthogonal, `B_jᴴ B_{j'} = 0` for the blocked tensors `B_j` of the blocks.

* The blocked tensor of `A` is `B = ∑ⱼ μⱼ^q B_j K_jᴴ`, where `K_j = E_j ⊗ E_j` embeds the bond
  pairs of block `j` (`physicalMatrix_blockTensor_blockSum`); by
  `Matrix.polarIso_sum_of_orthogonal` its partial isometry is `V = ∑ⱼ V_j K_jᴴ`.
* The state `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of eq. (S7), with the pairs of the blocks embedded along
  `ι_j`, is `∑ⱼ αⱼ |φ_M(V_j P_{j,∞})⟩`: each block contributes the approximating state of the
  normal case (`nonNormalApproxVector_blockSum`).
* The target is `|φ_N(A)⟩ = ∑ⱼ μⱼ^N |φ_N(A_j)⟩` (`mpv_blockSum`).
* The states of distinct blocks entering these sums are orthogonal (`mpvOverlap_eq_zero`).

**Scope restriction (multiplicity one, orthogonal blocks):** the source's eq. (S5) is used only
for `m_j = 1` and under the orthogonality of the `q`-site states of distinct blocks, which the
source does not assume and without which eq. (S5) fails. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex` and
`docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`.

## Main declarations

* `MPSTensor.coordEmbedding`, `MPSTensor.pairEmbedding` — the coordinate isometries `E_j` and
  `K_j = E_j ⊗ E_j`.
* `MPSTensor.blockSum` — the direct sum `⊕ⱼ μⱼ A_j`.
* `MPSTensor.evalWord_blockSum`, `MPSTensor.mpv_blockSum` — words and states of the sum.
* `MPSTensor.physicalMatrix_blockTensor_blockSum` — its blocked tensor.
* `MPSTensor.polarIso_blockTensor_blockSum` — the partial isometry of its blocked tensor.
* `MPSTensor.nonNormalApproxVector_blockSum` — the unnormalized state of eq. (S7).
* `MPSTensor.mpvOverlap_eq_zero` — tensors whose physical matrices have orthogonal columns
  generate orthogonal states.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7).
-/

open scoped BigOperators Matrix ComplexOrder Kronecker
open Matrix

namespace MPSTensor

variable {d D b : ℕ}

/-! ### Coordinate embeddings -/

/-- The coordinate isometry `E : ℂ^{D'} → ℂ^D`, `|a⟩ ↦ |ι a⟩`. -/
def coordEmbedding {D' : ℕ} (ι : Fin D' → Fin D) : Matrix (Fin D) (Fin D') ℂ :=
  of fun x a => if x = ι a then 1 else 0

/-- `E_ιᴴ E_ι'` has the entry `1` where `ι a = ι' a'` and `0` elsewhere. -/
theorem conjTranspose_coordEmbedding_mul_apply {D' D'' : ℕ} (ι : Fin D' → Fin D)
    (ι' : Fin D'' → Fin D) (a : Fin D') (a' : Fin D'') :
    ((coordEmbedding ι)ᴴ * coordEmbedding ι') a a' = if ι a = ι' a' then 1 else 0 := by
  rw [mul_apply, Finset.sum_eq_single (ι a)]
  · by_cases h : ι a = ι' a' <;> simp [coordEmbedding, conjTranspose_apply, h]
  · intro x _ hx
    simp [coordEmbedding, conjTranspose_apply, hx]
  · simp

/-- An injective coordinate map gives an isometry, `E_ιᴴ E_ι = 1`. -/
theorem conjTranspose_coordEmbedding_mul_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) : (coordEmbedding ι)ᴴ * coordEmbedding ι = 1 := by
  ext a a'
  rw [conjTranspose_coordEmbedding_mul_apply, one_apply]
  exact if_congr hι.eq_iff rfl rfl

/-- Coordinate maps with disjoint ranges give isometries with orthogonal ranges. -/
theorem conjTranspose_coordEmbedding_mul_eq_zero {D' D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a a', ι a ≠ ι' a') :
    (coordEmbedding ι)ᴴ * coordEmbedding ι' = 0 := by
  ext a a'
  rw [conjTranspose_coordEmbedding_mul_apply, zero_apply, if_neg (h a a')]

/-- The isometry `K = E_ι ⊗ E_ι` embedding the bond pairs `ℂ^{D'} ⊗ ℂ^{D'}` of a block into the
bond pairs of the direct sum; these index the columns of the physical matrix. -/
def pairEmbedding {D' : ℕ} (ι : Fin D' → Fin D) : Matrix (Fin D × Fin D) (Fin D' × Fin D') ℂ :=
  coordEmbedding ι ⊗ₖ coordEmbedding ι

theorem pairEmbedding_apply {D' : ℕ} (ι : Fin D' → Fin D) (p : Fin D × Fin D)
    (r : Fin D' × Fin D') : pairEmbedding ι p r = if p = (ι r.1, ι r.2) then 1 else 0 := by
  rcases p with ⟨x, y⟩
  rcases r with ⟨a, c⟩
  simp only [pairEmbedding, kroneckerMap_apply, coordEmbedding, of_apply, Prod.mk.injEq]
  by_cases h1 : x = ι a <;> by_cases h2 : y = ι c <;> simp [h1, h2]

theorem conjTranspose_pairEmbedding_mul_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) : (pairEmbedding ι)ᴴ * pairEmbedding ι = 1 := by
  rw [pairEmbedding, conjTranspose_kronecker, ← mul_kronecker_mul,
    conjTranspose_coordEmbedding_mul_self hι, one_kronecker_one]

theorem conjTranspose_pairEmbedding_mul_eq_zero {D' D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a a', ι a ≠ ι' a') :
    (pairEmbedding ι)ᴴ * pairEmbedding ι' = 0 := by
  rw [pairEmbedding, pairEmbedding, conjTranspose_kronecker, ← mul_kronecker_mul,
    conjTranspose_coordEmbedding_mul_eq_zero h, zero_kronecker]

/-! ### The direct sum of blocks of multiplicity one -/

variable {Dj : Fin b → ℕ}

/-- The direct sum `Aⁱ = ⊕ⱼ μⱼ A_jⁱ` of blocks `A_j`, each of multiplicity one, with the block
`j` placed on the bond coordinates `ι_j`: arXiv:2307.01696, Supplemental Material, eq. (S2),
for `m_j = 1`. -/
def blockSum (Aj : (j : Fin b) → MPSTensor d (Dj j)) (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (μ : Fin b → ℂ) : MPSTensor d D :=
  fun i => ∑ j, μ j • (coordEmbedding (ι j) * Aj j i * (coordEmbedding (ι j))ᴴ)

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- A nonempty word of the direct sum is the direct sum of the words of the blocks:
`A^{w} = ⊕ⱼ μⱼ^{|w|} A_j^{w}`. -/
theorem evalWord_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (μ : Fin b → ℂ) :
    ∀ w : List (Fin d), w ≠ [] →
      Kraus.evalWord (blockSum Aj ι μ) w =
        ∑ j, μ j ^ w.length •
          (coordEmbedding (ι j) * Kraus.evalWord (Aj j) w * (coordEmbedding (ι j))ᴴ)
  | [], h => absurd rfl h
  | [i], _ => by simp [blockSum]
  | i :: i' :: w, _ => by
    rw [Kraus.evalWord_cons, evalWord_blockSum hι hdisj μ (i' :: w) (List.cons_ne_nil _ _),
      blockSum, sum_mul_sum_of_mul_eq_zero fun j j' h => by
        rw [smul_mul_smul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc (coordEmbedding (ι j))ᴴ,
          conjTranspose_coordEmbedding_mul_eq_zero (hdisj j j' h)]
        simp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (coordEmbedding (ι j))ᴴ, conjTranspose_coordEmbedding_mul_self (hι j),
      Matrix.one_mul, Kraus.evalWord_cons, List.length_cons, pow_succ']
    simp only [Matrix.mul_assoc]

/-- The periodic state of the direct sum on `N ≥ 1` sites:
`|φ_N(A)⟩ = ∑ⱼ μⱼ^N |φ_N(A_j)⟩` (arXiv:2307.01696, Supplemental Material, eqs. (S3) and (S4),
for `m_j = 1`, where `βⱼ = μⱼ^N`). -/
theorem mpv_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (μ : Fin b → ℂ) {N : ℕ} (hN : N ≠ 0)
    (s : Fin N → Fin d) : mpv (blockSum Aj ι μ) s = ∑ j, μ j ^ N * mpv (Aj j) s := by
  have hw : List.ofFn s ≠ [] := by simpa [List.ofFn_eq_nil_iff] using hN
  rw [mpv_eq, coeff_eq, evalWord_blockSum hι hdisj μ _ hw, trace_sum, List.length_ofFn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_smul, trace_mul_comm, ← Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_self (hι j),
    Matrix.one_mul, smul_eq_mul, mpv_eq, coeff_eq]

/-- The physical matrix of the `q`-site blocked tensor of the direct sum, for `q ≥ 1`:
`B = ∑ⱼ μⱼ^q B_j K_jᴴ`, where `B_j` is the blocked tensor of the block `j` and `K_j` embeds its
bond pairs. -/
theorem physicalMatrix_blockTensor_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (μ : Fin b → ℂ) {q : ℕ} (hq : q ≠ 0) :
    physicalMatrix (blockTensor (blockSum Aj ι μ) q) =
      ∑ j, μ j ^ q • (physicalMatrix (blockTensor (Aj j) q) * (pairEmbedding (ι j))ᴴ) := by
  ext w p
  have hw : Kraus.wordOfBlock d q w ≠ [] := by
    rw [← List.length_pos_iff, Kraus.length_wordOfBlock]; omega
  simp only [physicalMatrix, blockTensor, Kraus.blockTensor]
  rw [evalWord_blockSum hι hdisj μ _ hw, Kraus.length_wordOfBlock, Matrix.sum_apply,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_apply, smul_apply, mul_apply, mul_apply, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [conjTranspose_apply, pairEmbedding_apply, coordEmbedding, of_apply, Prod.mk.injEq]
  by_cases h1 : p.1 = ι j a <;> by_cases h2 : p.2 = ι j c <;> simp [h1, h2]

/-! ### The approximating state -/

/-- The tensor power of a product is the product of the tensor powers. -/
theorem tensorPower_mul {ι₁ ι₂ ι₃ : Type*} [Fintype ι₂] (M : ℕ) (X : Matrix ι₁ ι₂ ℂ)
    (Y : Matrix ι₂ ι₃ ℂ) :
    tensorPower M X * tensorPower M Y = tensorPower M (X * Y) := by
  ext s t
  simp only [mul_apply, tensorPower, of_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun τ _ => (Finset.prod_mul_distrib).symm

/-- An embedded pair is supported on the image of the embedding: it vanishes when either leg
lies outside the range of `ι`. -/
theorem embedPair_eq_zero {D' : ℕ} {ι : Fin D' → Fin D} (ω : Fin D' × Fin D' → ℂ)
    {p : Fin D × Fin D} (hp : p.1 ∉ Set.range ι ∨ p.2 ∉ Set.range ι) : embedPair ι ω p = 0 := by
  refine Finset.sum_eq_zero fun x _ => if_neg fun h => ?_
  rcases hp with hp | hp
  · exact hp ⟨x.1, congrArg Prod.fst h⟩
  · exact hp ⟨x.2, congrArg Prod.snd h⟩

/-- The product of embedded pairs is the tensor power of the pair embedding applied to the
product of the original pairs: `⊗ₖ |ι_* ω⟩ = K^{⊗M} ⊗ₖ |ω⟩`, read on the site coordinates
`(L_k, R_k)` (arXiv:2307.01696, eq. (S7): `|Ω_j⟩ = ⊗ₖ |ω_j⟩_{R_k L_{k+1}}`). -/
theorem pairProductState_embedPair_eq_mulVec {D' M : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) (ω : Fin D' × Fin D' → ℂ) :
    pairProductState (N := M) (embedPair ι ω) =
      tensorPower M (pairEmbedding ι) *ᵥ pairProductState ω := by
  funext x
  simp only [mulVec, dotProduct, tensorPower, of_apply, pairEmbedding_apply]
  by_cases hx : ∃ x₀ : Fin M → Fin D' × Fin D', x = fun k => (ι (x₀ k).1, ι (x₀ k).2)
  · obtain ⟨x₀, rfl⟩ := hx
    rw [Finset.sum_eq_single x₀]
    · simp only [if_true, Finset.prod_const_one, one_mul]
      exact pairProductState_embedPair hι ω x₀
    · intro y _ hy
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hy
      refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ k) (if_neg fun h => hk ?_)) _
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact (Prod.ext (hι h1) (hι h2)).symm
    · simp
  · rw [Finset.sum_eq_zero fun y _ => ?_]
    · -- Some leg of some site lies outside the range of `ι`.
      have hleg : ∃ k, (x k).1 ∉ Set.range ι ∨ (x k).2 ∉ Set.range ι := by
        by_contra hne
        push_neg at hne
        choose f hf using fun k => (hne k).1
        choose g hg using fun k => (hne k).2
        exact hx ⟨fun k => (f k, g k), funext fun k => Prod.ext (hf k).symm (hg k).symm⟩
      obtain ⟨k, hk⟩ := hleg
      rw [pairProductState]
      rcases hk with hk | hk
      · refine Finset.prod_eq_zero (Finset.mem_univ ((finRotate M).symm k)) ?_
        refine embedPair_eq_zero ω (Or.inr ?_)
        simpa using hk
      · exact Finset.prod_eq_zero (Finset.mem_univ k) (embedPair_eq_zero ω (Or.inl hk))
    · refine mul_eq_zero_of_left ?_ _
      have hne : x ≠ fun k => (ι (y k).1, ι (y k).2) := fun h => hx ⟨y, h⟩
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- `V^{⊗M}` applied to the product of the pairs of `σ` is the periodic state of the tensor
`V P_∞` of the normal case (arXiv:2307.01696, eqs. (9) and (10)). -/
theorem tensorPower_polarIso_mulVec_pairProductState {n D' : ℕ} (B : MPSTensor n D')
    (σ : Matrix (Fin D') (Fin D') ℂ) (M : ℕ) [NeZero M] (τ : Fin M → Fin n) :
    (tensorPower M (polarIso (physicalMatrix B)) *ᵥ pairProductState (fixedPointPair σ)) τ =
      mpv (approximatingTensor B σ) τ := by
  rw [mpv_approximatingTensor]
  simp only [mulVec, dotProduct, tensorPower, of_apply]
  symm
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _ fun _ => rfl

/-- The partial isometry of the `q`-site blocked tensor of a direct sum with positive weights
and orthogonal `q`-site block states is `V = ∑ⱼ V_j K_jᴴ` (arXiv:2307.01696, Supplemental
Material, eq. (S5), for multiplicity one under the orthogonality that the source omits). -/
theorem polarIso_blockTensor_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') {μ : Fin b → ℝ} (hμ : ∀ j, 0 < μ j)
    {q : ℕ} (hq : q ≠ 0)
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) :
    polarIso (physicalMatrix (blockTensor (blockSum Aj ι fun j => (μ j : ℂ)) q)) =
      ∑ j, polarIso (physicalMatrix (blockTensor (Aj j) q)) * (pairEmbedding (ι j))ᴴ := by
  rw [physicalMatrix_blockTensor_blockSum hι hdisj _ hq]
  have h := (polarIso_sum_of_orthogonal horth (c := fun j => μ j ^ q)
    (fun j => pow_pos (hμ j) q) (K := fun j => pairEmbedding (ι j))
    (fun j => conjTranspose_pairEmbedding_mul_self (hι j))
    (fun j j' h => conjTranspose_pairEmbedding_mul_eq_zero (hdisj j j' h))).1
  simpa only [Complex.ofReal_pow] using h

/-- **The approximating state of a direct sum of orthogonal blocks.** For the direct sum
`⊕ⱼ μⱼ A_j` with `μⱼ > 0` whose blocks have orthogonal `q`-site states, the unnormalized state
`V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of arXiv:2307.01696, Supplemental Material, eq. (S7), formed from the
pairs of `σ_j` embedded along `ι_j`, is `∑ⱼ αⱼ |φ_M(V_j P_{j,∞})⟩`, the combination of the
approximating states of the normal case for the blocks. -/
theorem nonNormalApproxVector_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') {μ : Fin b → ℝ} (hμ : ∀ j, 0 < μ j)
    {q : ℕ} (hq : q ≠ 0)
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (M : ℕ) [NeZero M] (α : Fin b → ℂ)
    (τ : Fin M → Fin (blockPhysDim d q)) :
    nonNormalApproxVector (blockSum Aj ι fun j => (μ j : ℂ)) q M α
        (fun j => embedPair (ι j) (fixedPointPair (σ j))) τ =
      ∑ j, α j * mpv (approximatingTensor (blockTensor (Aj j) q) (σ j)) τ := by
  have hV := polarIso_blockTensor_blockSum hι hdisj hμ hq horth
  have hVK : ∀ j, polarIso (physicalMatrix (blockTensor (blockSum Aj ι fun j => (μ j : ℂ)) q)) *
      pairEmbedding (ι j) = polarIso (physicalMatrix (blockTensor (Aj j) q)) := fun j => by
    rw [hV, Finset.sum_mul, Finset.sum_eq_single j]
    · rw [Matrix.mul_assoc, conjTranspose_pairEmbedding_mul_self (hι j), Matrix.mul_one]
    · intro j' _ hj'
      rw [Matrix.mul_assoc, conjTranspose_pairEmbedding_mul_eq_zero (hdisj j' j hj'),
        Matrix.mul_zero]
    · simp
  have hstate : nonNormalFixedPointState (M := M) α
      (fun j => embedPair (ι j) (fixedPointPair (σ j))) =
      ∑ j, α j • (tensorPower M (pairEmbedding (ι j)) *ᵥ pairProductState (fixedPointPair (σ j)))
      := by
    funext x
    simp only [nonNormalFixedPointState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      pairProductState_embedPair_eq_mulVec (hι _)]
  rw [nonNormalApproxVector, hstate, mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, mulVec_mulVec, tensorPower_mul, hVK,
    tensorPower_polarIso_mulVec_pairProductState]

/-! ### Orthogonality of states -/

/-- The physical matrix of a tensor with rotated physical index is the rotation times the
physical matrix. -/
theorem physicalMatrix_rotatePhysical {m n D' : ℕ} (V : Matrix (Fin m) (Fin n) ℂ)
    (F : MPSTensor n D') : physicalMatrix (rotatePhysical V F) = V * physicalMatrix F := by
  ext i p
  simp [physicalMatrix, rotatePhysical, mul_apply, Matrix.sum_apply]

/-- **Orthogonal states.** If the physical matrices of two tensors have orthogonal columns,
`(Y)ᴴ X = 0`, i.e. `∑ᵢ conj(Yⁱ_{a'c'}) Xⁱ_{ac} = 0`, then the mixed transfer map vanishes and
the periodic states on `M ≥ 1` sites are orthogonal: `∑_s φ_M(X)(s) conj(φ_M(Y)(s)) = 0`. -/
theorem mpvOverlap_eq_zero {n D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂] {X : MPSTensor n D₁}
    {Y : MPSTensor n D₂} (h : (physicalMatrix Y)ᴴ * physicalMatrix X = 0) {M : ℕ}
    (hM : M ≠ 0) : mpvOverlap X Y M = 0 := by
  have hmix : Kraus.mixedMapLM X Y = 0 := by
    ext ρ a a'
    have hij : ∀ a c a' c', ∑ i, X i a c * star (Y i a' c') = 0 := fun a c a' c' => by
      have := congrFun (congrFun h (a', c')) (a, c)
      simpa [mul_apply, physicalMatrix, conjTranspose_apply, mul_comm] using this
    simp only [Kraus.mixedMapLM_apply, LinearMap.zero_apply, zero_apply, Matrix.sum_apply,
      mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    calc ∑ i, X i a c * ρ c c' * star (Y i a' c') = ρ c c' * ∑ i, X i a c * star (Y i a' c') := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hij, mul_zero]
  rw [← trace_mixedMapLM_rect_pow_eq_mpvOverlap, hmix, zero_pow hM, map_zero]

/-- The physical matrices of the approximating tensors `V_j P_{j,∞}` of blocks with orthogonal
blocked tensors have orthogonal columns: `(V_j F_j)ᴴ (V_{j'} F_{j'}) = 0`. -/
theorem conjTranspose_physicalMatrix_approximatingTensor_mul {n D₁ D₂ : ℕ}
    {B₁ : MPSTensor n D₁} {B₂ : MPSTensor n D₂}
    (h : (physicalMatrix B₁)ᴴ * physicalMatrix B₂ = 0) (σ₁ : Matrix (Fin D₁) (Fin D₁) ℂ)
    (σ₂ : Matrix (Fin D₂) (Fin D₂) ℂ) :
    (physicalMatrix (approximatingTensor B₁ σ₁))ᴴ * physicalMatrix (approximatingTensor B₂ σ₂) =
      0 := by
  simp only [approximatingTensor, physicalMatrix_rotatePhysical, polarIsoMatrix,
    conjTranspose_mul, conjTranspose_submatrix]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.submatrix _ _ _),
    submatrix_mul _ _ _ id _ Function.bijective_id, conjTranspose_polarIso_mul_polarIso_eq_zero h]
  simp

/-- The approximating tensor `V_j P_{j,∞}` of one block and the blocked tensor of another block
with orthogonal blocked tensors have orthogonal physical columns. -/
theorem conjTranspose_physicalMatrix_approximatingTensor_mul_blocked {n D₁ D₂ : ℕ}
    {B₁ : MPSTensor n D₁} {B₂ : MPSTensor n D₂}
    (h : (physicalMatrix B₁)ᴴ * physicalMatrix B₂ = 0) (σ₁ : Matrix (Fin D₁) (Fin D₁) ℂ) :
    (physicalMatrix (approximatingTensor B₁ σ₁))ᴴ * physicalMatrix B₂ = 0 := by
  simp only [approximatingTensor, physicalMatrix_rotatePhysical, polarIsoMatrix,
    conjTranspose_mul, conjTranspose_submatrix]
  rw [Matrix.mul_assoc, ← submatrix_id_id (physicalMatrix B₂),
    submatrix_mul _ _ _ id _ Function.bijective_id, conjTranspose_polarIso_mul_eq_zero h]
  simp

end MPSTensor
