/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBlockingResiduals
import TNLean.MPS.MPU.FiniteChainConjugation

/-!
# Residual blocks on anchored finite chains

A finite interval of integer sites may begin or end inside a globally aligned
block. The interval has a residual prefix, a possibly empty sequence of
complete blocks, and a residual suffix. The statements below identify the
ordered integer sites and their configurations with these three words. The
finite-chain MPO entry is then the trace of the corresponding three matrix
products. Intervals shorter than the next block boundary have no complete
middle block and are included.

This is a coefficient-level identification; it does not establish stability
of finite-chain conjugations or the QCA property.

## References

* arXiv:1703.09188, equation `eq:appendix-1` and Appendix, lines 2300--2320.
* arXiv:1606.00608, Appendix C.4, lines 1952--2017.
-/

namespace SpinChain

/-- Number of sites from `a` to the next globally aligned block boundary. -/
def nextBlockPrefix (a : ℤ) (L : ℕ) : ℕ := ((-a) % (L : ℤ)).toNat

/-- The residual prefix is shorter than a complete block. -/
theorem nextBlockPrefix_lt (a : ℤ) {L : ℕ} (hL : 0 < L) :
    nextBlockPrefix a L < L := by
  have hpos : (0 : ℤ) < L := by exact_mod_cast hL
  have hnonneg := Int.emod_nonneg (-a) (by omega : (L : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos (-a) hpos
  unfold nextBlockPrefix
  omega

/-- Adding the residual prefix reaches a globally aligned block boundary. -/
theorem nextBlockPrefix_aligned (a : ℤ) {L : ℕ} (hL : 0 < L) :
    (L : ℤ) ∣ a + nextBlockPrefix a L := by
  have hnonneg : 0 ≤ (-a) % (L : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt hL)
  have hcast : (nextBlockPrefix a L : ℤ) = (-a) % (L : ℤ) := by
    simp [nextBlockPrefix, Int.toNat_of_nonneg hnonneg]
  rw [hcast]
  refine ⟨-((-a) / (L : ℤ)), ?_⟩
  have hdiv := Int.emod_add_mul_ediv (-a) (L : ℤ)
  rw [mul_neg]
  omega

/-- An arbitrary anchored interval has a residual prefix, complete globally
aligned blocks, and a residual suffix. If it ends before the next block
boundary, the entire interval is the prefix and there are no complete blocks. -/
theorem exists_anchored_interval_decomposition
    (a : ℤ) (N L : ℕ) (hL : 0 < L) :
    ∃ p m s : ℕ,
      p < L ∧ s < L ∧ N = p + (m * L + s) ∧
      (0 < m → (L : ℤ) ∣ a + p) ∧
      (N < nextBlockPrefix a L → p = N ∧ m = 0 ∧ s = 0) := by
  let q := nextBlockPrefix a L
  let p := min N q
  let m := (N - p) / L
  let s := (N - p) % L
  refine ⟨p, m, s, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (Nat.min_le_right _ _) (nextBlockPrefix_lt a hL)
  · exact Nat.mod_lt _ hL
  · have hmod := Nat.mod_add_div (N - p) L
    have hp : p ≤ N := Nat.min_le_left _ _
    dsimp [m, s]
    rw [mul_comm ((N - p) / L) L]
    omega
  · intro hm
    have hpq : p = q := by
      by_contra hne
      have hNq : N < q := by
        have : p = N ∨ p = q := min_choice N q
        omega
      simp [p, Nat.min_eq_left (le_of_lt hNq), m] at hm
    rw [hpq]
    exact nextBlockPrefix_aligned a hL
  · intro hNq
    have hpN : p = N := Nat.min_eq_left (le_of_lt hNq)
    simp [m, s, hpN]

/-- The finite-chain configuration equivalence reads a site in its ordered position. -/
theorem finiteChainConfigEquiv_apply_site
    (d N : ℕ) (a : ℤ) (σ : Fin N → Fin d) (k : Fin N) :
    finiteChainConfigEquiv d N a σ (finiteChainSiteEquiv a N k) = σ k := by
  change σ ((finiteChainSiteEquiv a N).symm ((finiteChainSiteEquiv a N) k)) = σ k
  rw [Equiv.symm_apply_apply]

/-- Integer sites in a finite chain occur in increasing order from its anchor. -/
theorem finiteChainRegion_sort (a : ℤ) (N : ℕ) :
    (finiteChainRegion a N).sort =
      (List.range N).map (fun n : ℕ => a + n) := by
  let f : ℕ ↪ ℤ := Nat.castEmbedding.trans (addLeftEmbedding a)
  have hf : StrictMonoOn (f : ℕ → ℤ) (Finset.range N) := by
    intro x hx y hy hxy
    simp only [f, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    exact add_lt_add_right (Int.ofNat_lt.mpr hxy) a
  have hs := hf.map_finsetSort f (Finset.range N)
  have hN : (a + (N : ℤ) - a).toNat = N := by omega
  rw [finiteChainRegion, Int.Ico_eq_finset_map, hN]
  change (Finset.map f (Finset.range N)).sort = _
  rw [← hs, Finset.sort_range]
  congr 1

/-- The site at position `k` has integer coordinate `a + k`. -/
theorem finiteChainSiteEquiv_val (a : ℤ) (N : ℕ) (k : Fin N) :
    ((finiteChainSiteEquiv a N k : finiteChainRegion a N) : ℤ) = a + k := by
  change (finiteChainRegion a N).orderEmbOfFin (card_finiteChainRegion a N) k = _
  rw [Finset.orderEmbOfFin_apply]
  simp [finiteChainRegion_sort]

/-- The configuration on an anchored integer interval obtained by concatenating
the residual prefix, flattened complete blocks, and residual suffix. -/
noncomputable def anchoredResidualConfig (d N L p m s : ℕ) (a : ℤ)
    (hN : N = p + (m * L + s))
    (i₀ : Fin p → Fin d)
    (i₁ : Fin m → Fin (MPSTensor.blockPhysDim d L))
    (i₂ : Fin s → Fin d) : Config d (finiteChainRegion a N) :=
  finiteChainConfigEquiv d N a
    (fun k =>
      Fin.append i₀ (Fin.append (MPSTensor.blockedConfigEquiv d m L i₁) i₂)
        (Fin.cast hN k))

/-- The ordered residual-prefix, complete-block, and residual-suffix words
give all configurations on the anchored interval, without repetition. -/
noncomputable def anchoredResidualConfigEquiv
    (d N L p m s : ℕ) (a : ℤ) (hN : N = p + (m * L + s)) :
    (((Fin p → Fin d) × (Fin m → Fin (MPSTensor.blockPhysDim d L))) ×
      (Fin s → Fin d)) ≃ Config d (finiteChainRegion a N) :=
  ((Equiv.prodCongr
      (Equiv.prodCongr (Equiv.refl _) (MPSTensor.blockedConfigEquiv d m L))
      (Equiv.refl _)).trans
    (Equiv.prodCongr (Fin.appendEquiv p (m * L)) (Equiv.refl _))).trans
    (Fin.appendEquiv (p + m * L) s) |>.trans
    (Equiv.arrowCongr (finCongr (Nat.add_assoc p (m * L) s)) (Equiv.refl _)) |>.trans
    (Equiv.arrowCongr (finCongr hN.symm) (Equiv.refl _)) |>.trans
    (finiteChainConfigEquiv d N a)

/-- The configuration equivalence acts by the stated three-word concatenation. -/
theorem anchoredResidualConfigEquiv_apply
    (d N L p m s : ℕ) (a : ℤ) (hN : N = p + (m * L + s))
    (i₀ : Fin p → Fin d)
    (i₁ : Fin m → Fin (MPSTensor.blockPhysDim d L))
    (i₂ : Fin s → Fin d) :
    anchoredResidualConfigEquiv d N L p m s a hN ((i₀, i₁), i₂) =
      anchoredResidualConfig d N L p m s a hN i₀ i₁ i₂ := by
  simp [anchoredResidualConfigEquiv, anchoredResidualConfig,
    Equiv.arrowCongr, Fin.appendEquiv, Function.comp_def, Fin.append_assoc]

/-- Reading an anchored residual configuration agrees with the concatenated word. -/
theorem anchoredResidualConfig_apply_site (d N L p m s : ℕ) (a : ℤ)
    (hN : N = p + (m * L + s))
    (i₀ : Fin p → Fin d)
    (i₁ : Fin m → Fin (MPSTensor.blockPhysDim d L))
    (i₂ : Fin s → Fin d) (k : Fin (p + (m * L + s))) :
    anchoredResidualConfig d N L p m s a hN i₀ i₁ i₂
        (finiteChainSiteEquiv a N (Fin.cast hN.symm k)) =
      Fin.append i₀ (Fin.append (MPSTensor.blockedConfigEquiv d m L i₁) i₂) k := by
  rw [anchoredResidualConfig, finiteChainConfigEquiv_apply_site]
  simp

/-- A residue inside a complete middle block is still inside the finite interval. -/
theorem middle_index_lt {N L p m s : ℕ}
    (hN : N = p + (m * L + s)) (t : Fin m) (r : Fin L) :
    p + (t * L + r) < N := by
  have ht : t.val + 1 ≤ m := Nat.succ_le_of_lt t.isLt
  have hmul := Nat.mul_le_mul_right L ht
  rw [Nat.add_mul] at hmul
  have hr := r.isLt
  omega

/-- The middle-block coordinate agrees with the global integer quotient and residue. -/
theorem aligned_middle_site_coord {a b : ℤ} {N L p m s : ℕ}
    [NeZero L] (hN : N = p + (m * L + s))
    (halign : a + p = b * L) (t : Fin m) (r : Fin L) :
    ((finiteChainSiteEquiv a N
        ⟨p + (t * L + r), middle_index_lt hN t r⟩ : finiteChainRegion a N) : ℤ) =
      (Int.divModEquiv L).symm (b + t, r) := by
  rw [finiteChainSiteEquiv_val]
  change (a + ((p + (t * L + r) : ℕ) : ℤ)) = (b + (t : ℤ)) * L + r
  push_cast
  rw [← add_assoc, halign]
  ring

/-- Entrywise evaluation of the finite-chain MPO under its configuration reindexing. -/
theorem finiteChainMPOMatrix_apply_config
    {d D : ℕ} (U : MPOTensor d D) (N : ℕ) (a : ℤ)
    (x y : Config d (finiteChainRegion a N)) :
    finiteChainMPOMatrix U N a x y =
      MPOTensor.mpo U N
        ((finiteChainConfigEquiv d N a).symm x)
        ((finiteChainConfigEquiv d N a).symm y) := by
  rfl

/-- The finite-chain MPO entry at anchored residual configurations is the
corresponding periodic MPO entry. -/
theorem finiteChainMPOMatrix_apply_anchoredResidualConfig
    {d D : ℕ} (U : MPOTensor d D)
    (a : ℤ) (N L p m s : ℕ) (hN : N = p + (m * L + s))
    (i₀ j₀ : Fin p → Fin d)
    (i₁ j₁ : Fin m → Fin (MPSTensor.blockPhysDim d L))
    (i₂ j₂ : Fin s → Fin d) :
    finiteChainMPOMatrix U N a
        (anchoredResidualConfig d N L p m s a hN i₀ i₁ i₂)
        (anchoredResidualConfig d N L p m s a hN j₀ j₁ j₂) =
      MPOTensor.mpo U N
        (fun k => Fin.append i₀
          (Fin.append (MPSTensor.blockedConfigEquiv d m L i₁) i₂)
          (Fin.cast hN k))
        (fun k => Fin.append j₀
          (Fin.append (MPSTensor.blockedConfigEquiv d m L j₁) j₂)
          (Fin.cast hN k)) := by
  rw [finiteChainMPOMatrix_apply_config]
  simp only [anchoredResidualConfig, Equiv.symm_apply_apply]

/-- The finite-chain MPO entry at an arbitrary integer anchor is the trace of
its original-site prefix, complete blocked middle, and original-site suffix.
No divisibility assumption on the interval length is needed. -/
theorem finiteChainMPOMatrix_anchoredResidualTrace
    {d D : ℕ} (U : MPOTensor d D)
    (a : ℤ) (L p m s : ℕ)
    (i₀ j₀ : Fin p → Fin d)
    (i₁ j₁ : Fin m → Fin (MPSTensor.blockPhysDim d L))
    (i₂ j₂ : Fin s → Fin d) :
    finiteChainMPOMatrix U (p + (m * L + s)) a
        (anchoredResidualConfig d (p + (m * L + s)) L p m s a rfl i₀ i₁ i₂)
        (anchoredResidualConfig d (p + (m * L + s)) L p m s a rfl j₀ j₁ j₂) =
      Matrix.trace
        (MPOTensor.evalWord U (List.ofFn i₀) (List.ofFn j₀) *
          MPOTensor.evalWord (MPOTensor.blockTensor U L)
            (List.ofFn i₁) (List.ofFn j₁) *
          MPOTensor.evalWord U (List.ofFn i₂) (List.ofFn j₂)) := by
  rw [finiteChainMPOMatrix_apply_anchoredResidualConfig]
  simpa using MPOTensor.mpo_apply_prefix_blockTensor_suffix U L p m s
    i₀ j₀ i₁ j₁ i₂ j₂

/-- The trace of the original-site residual words surrounding the complete
blocked word. This notation retains both residual matrix factors. -/
noncomputable def anchoredResidualWordTrace {d D : ℕ} (U : MPOTensor d D) (L : ℕ)
    {p m s : ℕ}
    (i j : ((Fin p → Fin d) × (Fin m → Fin (MPSTensor.blockPhysDim d L))) ×
      (Fin s → Fin d)) : ℂ :=
  Matrix.trace
    (MPOTensor.evalWord U (List.ofFn i.1.1) (List.ofFn j.1.1) *
      MPOTensor.evalWord (MPOTensor.blockTensor U L)
        (List.ofFn i.1.2) (List.ofFn j.1.2) *
      MPOTensor.evalWord U (List.ofFn i.2) (List.ofFn j.2))

/-- The anchored-coordinate matrix coefficient is exactly the residual-word
trace, including when the complete-block word is empty. -/
theorem finiteChainMPOMatrix_anchoredResidualConfigEquiv
    {d D : ℕ} (U : MPOTensor d D) (a : ℤ) (L p m s : ℕ)
    (i j : ((Fin p → Fin d) × (Fin m → Fin (MPSTensor.blockPhysDim d L))) ×
      (Fin s → Fin d)) :
    finiteChainMPOMatrix U (p + (m * L + s)) a
        (anchoredResidualConfigEquiv d (p + (m * L + s)) L p m s a rfl i)
        (anchoredResidualConfigEquiv d (p + (m * L + s)) L p m s a rfl j) =
      anchoredResidualWordTrace U L i j := by
  rcases i with ⟨⟨i₀, i₁⟩, i₂⟩
  rcases j with ⟨⟨j₀, j₁⟩, j₂⟩
  rw [anchoredResidualConfigEquiv_apply, anchoredResidualConfigEquiv_apply]
  exact finiteChainMPOMatrix_anchoredResidualTrace U a L p m s
    i₀ j₀ i₁ j₁ i₂ j₂

/-- A coefficient of finite-chain conjugation is a sum over intermediate
configurations. The matrix of the included local observable is its matrix on
the restricted configurations, with equality imposed on the complementary
sites. This displays the two MPO coefficients to which the residual-word
identity can be applied after choosing coordinates for the intermediate
configurations.

Source context: arXiv:1703.09188, equation `eq:appendix-1`, lines
2300--2306, and local inclusion, lines 2285--2292. -/
theorem finiteChainConjugation_localInclusion_apply_entry
    {d D : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    {N : ℕ} (hN : 1 < N) (a : ℤ) {Λ : Finset ℤ}
    (hΛ : Λ ⊆ finiteChainRegion a N) (A : LocalAlgebra d Λ)
    (x y : Config d (finiteChainRegion a N)) :
    (finiteChainConjugation hU hN a (localInclusion hΛ A)) x y =
      ∑ w : Config d (finiteChainRegion a N),
        (∑ z : Config d (finiteChainRegion a N),
          finiteChainMPOMatrix U N a x z *
            (A (Config.restrict hΛ z) (Config.restrict hΛ w) *
              if (Config.splitEquiv hΛ z).2 = (Config.splitEquiv hΛ w).2
                then 1 else 0)) *
          star (finiteChainMPOMatrix U N a y w) := by
  rw [finiteChainConjugation_apply]
  simp only [CStarMatrix.mul_apply, localInclusion_apply, CStarMatrix.star_apply]

/-- An included local observable, conjugated on an anchored finite chain,
has an exact coefficient sum over residual prefix, complete-block, and
residual suffix configurations. Both MPO coefficients retain their original-
site residual traces. No boundary stabilization is asserted.

Source context: arXiv:1703.09188, equation `eq:appendix-1`, lines
2300--2306, with the finite-word blocking of arXiv:1606.00608,
Appendix C.4, lines 1952--2017. -/
theorem finiteChainConjugation_localInclusion_anchoredResidualTrace
    {d D : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    (a : ℤ) (L p m s : ℕ) (hN : 1 < p + (m * L + s))
    {Λ : Finset ℤ} (hΛ : Λ ⊆ finiteChainRegion a (p + (m * L + s)))
    (A : LocalAlgebra d Λ)
    (i j : ((Fin p → Fin d) × (Fin m → Fin (MPSTensor.blockPhysDim d L))) ×
      (Fin s → Fin d)) :
    let e := anchoredResidualConfigEquiv d (p + (m * L + s)) L p m s a rfl
    (finiteChainConjugation hU hN a (localInclusion hΛ A)) (e i) (e j) =
      ∑ w : ((Fin p → Fin d) ×
          (Fin m → Fin (MPSTensor.blockPhysDim d L))) × (Fin s → Fin d),
        (∑ z : ((Fin p → Fin d) ×
            (Fin m → Fin (MPSTensor.blockPhysDim d L))) × (Fin s → Fin d),
          anchoredResidualWordTrace U L i z *
            (A (Config.restrict hΛ (e z)) (Config.restrict hΛ (e w)) *
              if (Config.splitEquiv hΛ (e z)).2 =
                  (Config.splitEquiv hΛ (e w)).2 then 1 else 0)) *
          star (anchoredResidualWordTrace U L j w) := by
  dsimp only
  rw [finiteChainConjugation_localInclusion_apply_entry hU hN a hΛ A]
  rw [← Equiv.sum_comp
    (anchoredResidualConfigEquiv d (p + (m * L + s)) L p m s a rfl)]
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [← Equiv.sum_comp
    (anchoredResidualConfigEquiv d (p + (m * L + s)) L p m s a rfl)]
  simp only [finiteChainMPOMatrix_anchoredResidualConfigEquiv]

end SpinChain
