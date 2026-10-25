/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProductCutIteration
import TNLean.Algebra.CyclicInsertion

/-!
# Products of consecutive copies on a chain

The sites of a chain of length `K * L` are grouped into `K` consecutive blocks
of length `L`. The product of block vectors is defined on these literal site
coordinates, rather than identified with a tensor product by an assumption.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 421–479.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw

variable {K L q : ℕ}

/-- Configurations on consecutive blocks, in the order `L * i + j`. -/
def copyConfigurationEquiv (K L q : ℕ) :
    (Fin (K * L) → Fin q) ≃ (Fin K → Fin L → Fin q) where
  toFun σ i j := σ (finProdFinEquiv (i, j))
  invFun τ s := τ (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2
  left_inv σ := funext fun s ↦ congrArg σ (finProdFinEquiv.apply_symm_apply s)
  right_inv τ := by funext i j; simp

/-- The product of the supplied block vectors on `K * L` consecutive sites. -/
def copyProduct (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    EuclideanSpace ℂ (Fin (K * L) → Fin q) :=
  WithLp.toLp 2 fun σ ↦ EuclideanSpace.piTensor η (copyConfigurationEquiv K L q σ)

/-- The norm of a block product is the product of the block norms. -/
theorem norm_copyProduct (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖copyProduct η‖ = ∏ i, ‖η i‖ := by
  rw [← EuclideanSpace.norm_piTensor η]
  simp only [EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp (copyConfigurationEquiv K L q)
    (fun σ ↦ ‖EuclideanSpace.piTensor η σ‖ ^ 2)

/-- A site lies before a copy boundary exactly when its block does. -/
private theorem copySite_mem_leftBlock_iff (i : Fin K) (j : Fin L) (t : ℕ) :
    finProdFinEquiv (i, j) ∈ leftBlock (K * L) (t * L) ↔ i.val < t := by
  rw [mem_leftBlock]
  change j.val + L * i.val < t * L ↔ i.val < t
  constructor
  · intro h
    by_contra hi
    have ht : t ≤ i.val := Nat.le_of_not_gt hi
    nlinarith [Nat.mul_le_mul_right L ht]
  · intro hi
    have ht : i.val + 1 ≤ t := hi
    nlinarith [Nat.mul_le_mul_right L ht, j.isLt]

/-- A literal block product factors at every boundary between copies.
Source: arXiv:0705.0292v2, lines 421–470. -/
theorem copyProduct_factors_at_boundary
    (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) (t : ℕ) :
    ∃ (a : EuclideanSpace ℂ
        (Entropy.RegionConfig (fun _ : Fin (K * L) ↦ q) (leftBlock (K * L) (t * L))))
      (b : EuclideanSpace ℂ
        ((i : {i : Fin (K * L) // i ∉ leftBlock (K * L) (t * L)}) → Fin q)),
      Entropy.cutVector (leftBlock (K * L) (t * L)) (copyProduct η) =
        Matrix.euclideanTensorVector a b := by
  classical
  let a : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin (K * L) ↦ q) (leftBlock (K * L) (t * L))) :=
    WithLp.toLp 2 fun σ ↦ ∏ i : Fin K, if h : i.val < t then
      η i (fun j ↦ σ ⟨finProdFinEquiv (i, j), (copySite_mem_leftBlock_iff i j t).mpr h⟩)
    else 1
  let b : EuclideanSpace ℂ
      ((i : {i : Fin (K * L) // i ∉ leftBlock (K * L) (t * L)}) → Fin q) :=
    WithLp.toLp 2 fun σ ↦ ∏ i : Fin K, if h : i.val < t then 1 else
      η i (fun j ↦ σ ⟨finProdFinEquiv (i, j),
        fun hm ↦ h ((copySite_mem_leftBlock_iff i j t).mp hm)⟩)
  refine ⟨a, b, ?_⟩
  ext xy
  change (∏ i : Fin K, η i (fun j ↦
    (Entropy.cutEquiv (fun _ : Fin (K * L) ↦ q) (leftBlock (K * L) (t * L))).symm xy
      (finProdFinEquiv (i, j)))) = _
  change _ = a xy.1 * b xy.2
  dsimp only [a, b]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : i.val < t
  · simp only [dite_eq_left h, mul_one]
    apply congrArg (η i)
    funext j
    exact Entropy.cutEquiv_symm_apply_mem (n := fun _ : Fin (K * L) ↦ q) xy.1 xy.2
      ((copySite_mem_leftBlock_iff i j t).mpr h)
  · simp only [dite_eq_right h, one_mul]
    apply congrArg (η i)
    funext j
    exact Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin (K * L) ↦ q) xy.1 xy.2
      (fun hm ↦ h ((copySite_mem_leftBlock_iff i j t).mp hm))

/-- Inner products of literal block products factor over the blocks. -/
theorem inner_copyProduct (η θ : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    inner ℂ (copyProduct η) (copyProduct θ) = ∏ i, inner ℂ (η i) (θ i) := by
  rw [← EuclideanSpace.inner_piTensor η θ]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  exact Equiv.sum_comp (copyConfigurationEquiv K L q)
    (fun σ ↦ EuclideanSpace.piTensor θ σ * star (EuclideanSpace.piTensor η σ))

/-- Against a literal product target, a normalized MPS admits a replacement with
rank at most one at every copy boundary and with no smaller overlap.
Source: arXiv:0705.0292v2, lines 421–470. -/
theorem IsOpenMPS.exists_rank_one_at_copy_boundaries {D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin (K * L) → Fin q)}
    (hψ : IsOpenMPS (K * L) q D (fun x ↦ ψ x)) (hnorm : ‖ψ‖ = 1)
    (η : Fin K → EuclideanSpace ℂ (Fin L → Fin q)) :
    ∃ χ : EuclideanSpace ℂ (Fin (K * L) → Fin q),
      IsOpenMPS (K * L) q D (fun x ↦ χ x) ∧ ‖χ‖ = 1 ∧
      ‖inner ℂ (copyProduct η) ψ‖ ≤ ‖inner ℂ (copyProduct η) χ‖ ∧
      (∀ j, (cutMatrix χ j).rank ≤ (cutMatrix ψ j).rank) ∧
      ∀ t ≤ K, (cutMatrix χ (t * L)).rank ≤ 1 := by
  classical
  let S := (Finset.range (K + 1)).image (fun t ↦ t * L)
  have hf : ∀ k ∈ S,
      ∃ a b, Entropy.cutVector (leftBlock (K * L) k) (copyProduct η) =
        Matrix.euclideanTensorVector a b := by
    intro k hk
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hk
    exact copyProduct_factors_at_boundary η t
  obtain ⟨χ, hm, hn, ho, hr, hb⟩ := hψ.exists_rank_one_at_product_cuts hnorm S hf
  refine ⟨χ, hm, hn, ho, hr, fun t ht ↦ hb (t * L) ?_⟩
  exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩

/-- Every two-by-two minor of a matrix of rank at most one vanishes. -/
private theorem cross_mul_eq_of_rank_le_one {α β : Type*} [Fintype β]
    (C : Matrix α β ℂ) (hr : C.rank ≤ 1) (a a₀ : α) (b b₀ : β) :
    C a b * C a₀ b₀ = C a b₀ * C a₀ b := by
  obtain ⟨U, V, hUV⟩ := Matrix.exists_mul_eq_of_rank_le C hr
  rw [← hUV]
  simp only [Matrix.mul_apply, Fin.sum_univ_one]
  ring

/-- Join the first n block coordinates of x to the remaining coordinates of y. -/
private def spliceBlocks {K : ℕ} {α : Type*} (n : ℕ) (x y : Fin K → α) : Fin K → α :=
  fun i ↦ if i.val < n then x i else y i

/-- Raw product factors are obtained by changing one coordinate of a fixed
configuration with nonzero coefficient. -/
private theorem factors_of_cross_mul {K : ℕ} {α : Type*}
    (f : (Fin K → α) → ℂ) (x₀ : Fin K → α) (hx₀ : f x₀ ≠ 0)
    (hcross : ∀ n x y,
      f x * f y = f (spliceBlocks n x y) * f (spliceBlocks n y x))
    (x : Fin K → α) :
    f x = f x₀ * ∏ i : Fin K, f (Function.update x₀ i (x i)) / f x₀ := by
  have hpartial : ∀ n (hn : n ≤ K),
      f (spliceBlocks n x x₀) = f x₀ *
        ∏ i : Fin n, f (Function.update x₀ ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
          (x ⟨i.val, lt_of_lt_of_le i.isLt hn⟩)) / f x₀ := by
    intro n
    induction n with
    | zero =>
      intro hn
      have hz : spliceBlocks 0 x x₀ = x₀ := by funext i; simp [spliceBlocks]
      rw [hz]
      simp
    | succ n ih =>
      intro hn
      let i : Fin K := ⟨n, by omega⟩
      have hleft : spliceBlocks n (spliceBlocks (n + 1) x x₀) x₀ =
          spliceBlocks n x x₀ := by
        funext j
        by_cases hj : j.val < n
        · simp [spliceBlocks, hj, show j.val < n + 1 by omega]
        · simp [spliceBlocks, hj]
      have hright : spliceBlocks n x₀ (spliceBlocks (n + 1) x x₀) =
          Function.update x₀ i (x i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [spliceBlocks, i]
        · have hjn : j.val ≠ n := fun h ↦ hji (Fin.ext h)
          by_cases hj : j.val < n
          · simp [spliceBlocks, hj, hji]
          · simp [spliceBlocks, hj, show ¬j.val < n + 1 by omega, hji]
      have hc := hcross n (spliceBlocks (n + 1) x x₀) x₀
      rw [hleft, hright, ih (by omega)] at hc
      rw [Fin.prod_univ_castSucc]
      apply mul_right_cancel₀ hx₀
      rw [hc]
      simp [i, mul_assoc, hx₀]
  have hfull : spliceBlocks K x x₀ = x := by
    funext i
    simp [spliceBlocks, i.isLt]
  simpa only [hfull] using hpartial K le_rfl

/-- Normalizing every factor of a unit product vector preserves that vector. -/
private theorem exists_unit_factors_of_piTensor_norm_one {K : ℕ} {α : Type*} [Fintype α]
    (v : Fin K → EuclideanSpace ℂ α) (hv : ‖EuclideanSpace.piTensor v‖ = 1) :
    ∃ u : Fin K → EuclideanSpace ℂ α,
      (∀ i, ‖u i‖ = 1) ∧ EuclideanSpace.piTensor u = EuclideanSpace.piTensor v := by
  have hprod : (∏ i, ‖v i‖) = 1 := by rw [← EuclideanSpace.norm_piTensor, hv]
  have hnonzero : ∀ i, ‖v i‖ ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp (by rw [hprod]; norm_num)) i (Finset.mem_univ i)
  let u : Fin K → EuclideanSpace ℂ α := fun i ↦ (‖v i‖ : ℂ)⁻¹ • v i
  refine ⟨u, ?_, ?_⟩
  · intro i
    simp [u, norm_smul, hnonzero i]
  · have hprodC : (∏ i, (‖v i‖ : ℂ)) = 1 := by exact_mod_cast hprod
    have hprodInv : (∏ i, (‖v i‖ : ℂ)⁻¹) = 1 := by
      rw [Finset.prod_inv_distrib, hprodC, inv_one]
    change EuclideanSpace.piTensorMultilinear (fun i ↦ (‖v i‖ : ℂ)⁻¹ • v i) = _
    rw [EuclideanSpace.piTensorMultilinear.map_smul_univ, hprodInv, one_smul]
    rfl

/-- Prefix rank-one identities force a normalized vector to be a product of
normalized block factors. The first factor carries the global phase. -/
private theorem exists_unit_factors_of_cross_mul {K : ℕ} {α : Type*} [Fintype α]
    (hK : 0 < K) (Ψ : EuclideanSpace ℂ (Fin K → α)) (hΨ : ‖Ψ‖ = 1)
    (hcross : ∀ n x y, Ψ x * Ψ y =
      Ψ (spliceBlocks n x y) * Ψ (spliceBlocks n y x)) :
    ∃ u : Fin K → EuclideanSpace ℂ α,
      (∀ i, ‖u i‖ = 1) ∧ EuclideanSpace.piTensor u = Ψ := by
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp
    ((WithLp.ofLp_eq_zero (x := Ψ)).not.mpr (norm_ne_zero_iff.mp (by simp [hΨ])))
  let v : Fin K → EuclideanSpace ℂ α := fun i ↦
    WithLp.toLp 2 fun a ↦ Ψ (Function.update x₀ i a) / Ψ x₀
  have hfactor : Ψ = Ψ x₀ • EuclideanSpace.piTensor v := by
    ext x
    change Ψ x = Ψ x₀ * ∏ i, Ψ (Function.update x₀ i (x i)) / Ψ x₀
    exact factors_of_cross_mul (fun x ↦ Ψ x) x₀ hx₀ hcross x
  let i₀ : Fin K := ⟨0, hK⟩
  let w : Fin K → EuclideanSpace ℂ α := Function.update v i₀ (Ψ x₀ • v i₀)
  have hw : EuclideanSpace.piTensor w = Ψ := by
    change EuclideanSpace.piTensorMultilinear (Function.update v i₀ (Ψ x₀ • v i₀)) = Ψ
    rw [EuclideanSpace.piTensorMultilinear.map_update_smul, Function.update_eq_self]
    exact hfactor.symm
  obtain ⟨u, hu, hprod⟩ := exists_unit_factors_of_piTensor_norm_one w (by rw [hw, hΨ])
  exact ⟨u, hu, hprod.trans hw⟩

/-- Join two chain configurations at one numbered cut. -/
private def spliceSites {T q : ℕ} (k : ℕ) (σ τ : Fin T → Fin q) : Fin T → Fin q :=
  fun i ↦ if i.val < k then σ i else τ i

/-- A cut matrix entry is the coefficient of the corresponding joined configuration. -/
private theorem cutMatrix_restrictions {T q : ℕ} (ψ : EuclideanSpace ℂ (Fin T → Fin q))
    (k : ℕ) (σ τ : Fin T → Fin q) :
    cutMatrix ψ k (fun i ↦ σ i.1) (fun i ↦ τ i.1) = ψ (spliceSites k σ τ) := by
  rw [cutMatrix_apply]
  apply congrArg ψ
  funext i
  by_cases hi : i.val < k
  · rw [Entropy.cutEquiv_symm_apply_mem _ _ (mem_leftBlock.mpr hi)]
    simp [spliceSites, hi]
  · rw [Entropy.cutEquiv_symm_apply_not_mem _ _ (mt mem_leftBlock.mp hi)]
    simp [spliceSites, hi]

/-- A rank-one physical cut gives the cross-multiplication identity for joined words. -/
private theorem cross_mul_eq_of_cut_rank_le_one {T q : ℕ} (ψ : EuclideanSpace ℂ (Fin T → Fin q))
    (k : ℕ) (hk : (cutMatrix ψ k).rank ≤ 1) (σ τ : Fin T → Fin q) :
    ψ σ * ψ τ = ψ (spliceSites k σ τ) * ψ (spliceSites k τ σ) := by
  have hc := cross_mul_eq_of_rank_le_one (cutMatrix ψ k) hk
    (fun i ↦ σ i.1) (fun i ↦ τ i.1) (fun i ↦ σ i.1) (fun i ↦ τ i.1)
  have hself : ∀ x : Fin T → Fin q, spliceSites k x x = x := by
    intro x
    funext i
    simp [spliceSites]
  simpa only [cutMatrix_restrictions, hself] using hc

/-- Joining configurations at a physical block boundary agrees with joining their blocks. -/
private theorem spliceSites_blockConfig {K L q : ℕ} (n : ℕ)
    (x y : Fin K → Fin L → Fin q) :
    spliceSites (n * L) ((copyConfigurationEquiv K L q).symm x)
      ((copyConfigurationEquiv K L q).symm y) =
      (copyConfigurationEquiv K L q).symm (spliceBlocks n x y) := by
  funext s
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective s
  have hboundary := copySite_mem_leftBlock_iff i j n
  simp only [mem_leftBlock] at hboundary
  simp only [spliceSites, copyConfigurationEquiv, Equiv.coe_fn_symm_mk,
    Equiv.symm_apply_apply, spliceBlocks, hboundary]
  split <;> rfl

/-- A unit chain vector with rank-one cuts at every copy boundary is a literal
product of normalized block vectors. The block length may be zero.
Source: arXiv:0705.0292v2, lines 421–470. -/
theorem exists_unit_block_factors {K L q : ℕ} (hK : 0 < K)
    (ψ : EuclideanSpace ℂ (Fin (K * L) → Fin q)) (hψ : ‖ψ‖ = 1)
    (hcuts : ∀ n, 0 < n → n < K → (cutMatrix ψ (n * L)).rank ≤ 1) :
    ∃ u : Fin K → EuclideanSpace ℂ (Fin L → Fin q),
      (∀ i, ‖u i‖ = 1) ∧ ψ = copyProduct u := by
  let Ψ : EuclideanSpace ℂ (Fin K → Fin L → Fin q) :=
    WithLp.toLp 2 fun x ↦ ψ ((copyConfigurationEquiv K L q).symm x)
  have hn : ‖Ψ‖ = 1 := by
    calc
      ‖Ψ‖ = ‖ψ‖ := by
        simp only [EuclideanSpace.norm_eq]
        congr 1
        exact Equiv.sum_comp (copyConfigurationEquiv K L q).symm (fun σ ↦ ‖ψ σ‖ ^ 2)
      _ = 1 := hψ
  have hr : ∀ n, (cutMatrix ψ (n * L)).rank ≤ 1 := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      rw [Nat.zero_mul]
      exact rank_cutMatrix_zero_le ψ
    · by_cases hnK : n < K
      · exact hcuts n (Nat.pos_of_ne_zero hn0) hnK
      · exact rank_cutMatrix_le_one_of_le (Nat.mul_le_mul_right L (Nat.le_of_not_gt hnK)) ψ
  have hc : ∀ n x y, Ψ x * Ψ y = Ψ (spliceBlocks n x y) * Ψ (spliceBlocks n y x) := by
    intro n x y
    have h := cross_mul_eq_of_cut_rank_le_one ψ (n * L) (hr n)
      ((copyConfigurationEquiv K L q).symm x) ((copyConfigurationEquiv K L q).symm y)
    rw [spliceSites_blockConfig, spliceSites_blockConfig] at h
    exact h
  obtain ⟨u, hu, hfactor⟩ := exists_unit_factors_of_cross_mul hK Ψ hn hc
  refine ⟨u, hu, ?_⟩
  ext σ
  have h := congrArg (fun z ↦ z ((copyConfigurationEquiv K L q) σ)) hfactor
  change EuclideanSpace.piTensor u ((copyConfigurationEquiv K L q) σ) =
    ψ ((copyConfigurationEquiv K L q).symm ((copyConfigurationEquiv K L q) σ)) at h
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

end TNLean.MPS.AreaLaw
