/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteFiniteHeisenberg
import TNLean.MPS.MPU.FiniteChainConjugation
import TNLean.QCA.SingletonGeneration

/-!
# Canonical buffered local action of supplied MPU standard form

The actual finite MPU conjugation agrees on arbitrary finite supported
regions in any two sufficiently buffered integer intervals. The proof
identifies the explicit finite configuration maps with canonical local
inclusions, derives the full central-interval action, and then uses
finite tensor generation of the one-site algebras.

Source: arXiv:1703.09188, StandardForm/SF lines 603--622 and the finite
conjugation limit eq:appendix-1, lines 2300--2306.

**Scope restriction (supplied standard form):** These results consume
actual MPU unitarity, a positive block length and supplied two-site
standard-form data. They derive forward buffering compatibility. The
inverse family, standard-form construction from bare MPU data, source
bond-dimension radius, and completion remain separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

open scoped Matrix

namespace SpinChain

private theorem bufferedWindow_middle (d n p s : ℕ)
    (pre : Fin p → Fin d) (suf : Fin s → Fin d) (mid : Fin n → Fin d) :
    (fun i : Fin n ↦ MPOTensor.bufferedWindowConfigEquiv d n p s ((pre, suf), mid)
      ⟨p + i.val, by omega⟩) = mid := by
  funext i
  change Fin.append pre (Fin.append mid suf) ((i.castAdd s).natAdd p) = mid i
  simp only [Fin.append_right, Fin.append_left]

private theorem bufferedWindow_outside_eq_iff (d n p s : ℕ)
    (pre pre' : Fin p → Fin d) (suf suf' : Fin s → Fin d)
    (mid mid' : Fin n → Fin d) :
    (∀ i : Fin (p + (n + s)), ¬ (p ≤ i.val ∧ i.val < p + n) →
      MPOTensor.bufferedWindowConfigEquiv d n p s ((pre, suf), mid) i =
        MPOTensor.bufferedWindowConfigEquiv d n p s ((pre', suf'), mid') i) ↔
      (pre, suf) = (pre', suf') := by
  change (∀ i : Fin (p + (n + s)), ¬ (p ≤ i.val ∧ i.val < p + n) →
    Fin.append pre (Fin.append mid suf) i =
      Fin.append pre' (Fin.append mid' suf') i) ↔ _
  constructor
  · intro h
    apply Prod.ext
    · funext i
      have hi := h (i.castAdd (n + s)) (by
        simp only [Fin.val_castAdd]
        omega)
      simpa only [Fin.append_left] using hi
    · funext i
      have hi := h ((i.natAdd n).natAdd p) (by
        simp only [Fin.val_natAdd]
        omega)
      simpa only [Fin.append_right] using hi
  · intro h
    have hp := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    cases hp
    cases hs
    intro i
    refine Fin.addCases (fun j _ ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left]
    · refine Fin.addCases (fun j hj ↦ ?_) (fun j _ ↦ ?_) j
      · exfalso
        apply hj
        simp only [Fin.val_natAdd, Fin.val_castAdd]
        omega
      · simp only [Fin.append_right]

/-- The complete original-site buffering coordinates agree with the
canonical local-algebra inclusion on integer intervals.
Source: arXiv:1703.09188, Appendix, lines 2292--2295. -/
theorem intervalCoordinates_localInclusion_eq_bufferedWindowMatrix
    (d n p s : ℕ) (a : ℤ) (A : LocalAlgebra d (finiteChainRegion a n)) :
    intervalCoordinates d (a - p) (p + (n + s))
      (localInclusion (show finiteChainRegion a n ⊆
        finiteChainRegion (a - p) (p + (n + s)) by
          simpa only [Nat.add_assoc] using finiteChainRegion_subset_expanded a n p s) A) =
      MPOTensor.bufferedWindowMatrix d n p s (intervalCoordinates d a n A) := by
  classical
  ext row col
  obtain ⟨⟨⟨pre, suf⟩, mid⟩, rfl⟩ :=
    (MPOTensor.bufferedWindowConfigEquiv d n p s).surjective row
  obtain ⟨⟨⟨pre', suf'⟩, mid'⟩, rfl⟩ :=
    (MPOTensor.bufferedWindowConfigEquiv d n p s).surjective col
  have h := intervalCoordinates_localInclusion_apply d a n p s A
  simp only [Nat.add_assoc] at h
  rw [h]
  simp only [bufferedWindow_middle, bufferedWindow_outside_eq_iff,
    MPOTensor.bufferedWindowMatrix, Matrix.reindex_apply, Equiv.symm_apply_apply,
    Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [mul_comm]

/-- Actual finite-chain conjugation of a fixed standard-form window is
independent of every original-site buffer and of the ambient chain length.
The equality is in the existing algebraic local algebra, using canonical
local inclusions, rather than an assumed compatible action.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem finiteChainLocalObservable_originalSiteHeisenbergWindow
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU) (k p s : ℕ)
    (hN : 1 < p + (3 * (2 * k) + s)) (a : ℤ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    finiteChainLocalObservable hU hN (a - p)
      (show finiteChainRegion a (3 * (2 * k)) ⊆
        finiteChainRegion (a - p) (p + (3 * (2 * k) + s)) by
          simpa only [Nat.add_assoc] using
            finiteChainRegion_subset_expanded a (3 * (2 * k)) p s)
      ((intervalCoordinates d a (3 * (2 * k))).symm
        (MPOTensor.originalSiteHeisenbergInputWindow d k A)) =
      localObservable d (finiteChainRegion a (3 * (2 * k)))
        ((intervalCoordinates d a (3 * (2 * k))).symm
          (MPOTensor.originalSiteHeisenbergOutputWindow k u v A)) := by
  classical
  let hΛ : finiteChainRegion a (3 * (2 * k)) ⊆
      finiteChainRegion (a - p) (p + (3 * (2 * k) + s)) := by
    simpa only [Nat.add_assoc] using
      finiteChainRegion_subset_expanded a (3 * (2 * k)) p s
  have hconj : finiteChainConjugation hU hN (a - p)
      (localInclusion hΛ ((intervalCoordinates d a (3 * (2 * k))).symm
        (MPOTensor.originalSiteHeisenbergInputWindow d k A))) =
      localInclusion hΛ ((intervalCoordinates d a (3 * (2 * k))).symm
        (MPOTensor.originalSiteHeisenbergOutputWindow k u v A)) := by
    apply (intervalCoordinates d (a - p) (p + (3 * (2 * k) + s))).injective
    simp only [finiteChainConjugation_apply, map_mul, map_star,
      intervalCoordinates_finiteChainMPOMatrix,
      intervalCoordinates_localInclusion_eq_bufferedWindowMatrix,
      StarAlgEquiv.apply_symm_apply, Matrix.star_eq_conjTranspose]
    exact MPOTensor.mpo_bufferedWindow_conjugation hU k p s hN S A
  change localObservable d _ (finiteChainConjugation hU hN (a - p)
    (localInclusion hΛ _)) = _
  rw [hconj, localObservable_localInclusion]


/-- The input-window algebra is exactly the canonical full algebra of
its central \(2k\) consecutive original sites. In particular the window
formula applies to every observable there. Source: arXiv:1703.09188,
StandardForm and eq:appendix-1, lines 603--622 and 2300--2306. -/
theorem intervalCoordinates_centralInclusion_originalSiteHeisenbergInputWindow
    (d k : ℕ) (a : ℤ)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    intervalCoordinates d a (3 * (2 * k))
      (localInclusion (show finiteChainRegion (a + (2 * k : ℕ)) (2 * k) ⊆
        finiteChainRegion a (3 * (2 * k)) by
          intro x hx
          simp only [finiteChainRegion, Finset.mem_Ico] at *
          omega)
        ((intervalCoordinates d (a + (2 * k : ℕ)) (2 * k)).symm
          (Matrix.reindex (MPOTensor.originalSiteHeisenbergCentreEquiv d k)
            (MPOTensor.originalSiteHeisenbergCentreEquiv d k) A))) =
      MPOTensor.originalSiteHeisenbergInputWindow d k A := by
  classical
  let e := MPOTensor.originalSiteHeisenbergInputWindowEquiv d k
  ext row col
  obtain ⟨⟨ex, c⟩, rfl⟩ := e.surjective row
  obtain ⟨⟨ex', c'⟩, rfl⟩ := e.surjective col
  have h := intervalCoordinates_localInclusion_apply d (a + (2 * k : ℕ))
    (2 * k) (2 * k) (2 * k)
    ((intervalCoordinates d (a + (2 * k : ℕ)) (2 * k)).symm
      (Matrix.reindex (MPOTensor.originalSiteHeisenbergCentreEquiv d k)
        (MPOTensor.originalSiteHeisenbergCentreEquiv d k) A))
  have ha : a + (2 * k : ℕ) - (2 * k : ℕ) = a := by omega
  have hlen : (2 * k + 2 * k) + 2 * k = 3 * (2 * k) := by omega
  rw [ha, hlen] at h
  rw [h]
  simp only [StarAlgEquiv.apply_symm_apply, e,
    MPOTensor.originalSiteHeisenbergInputWindowEquiv_middle,
    MPOTensor.originalSiteHeisenbergInputWindowEquiv_outside_eq_iff,
    MPOTensor.originalSiteHeisenbergInputWindow, Matrix.reindex_apply,
    Equiv.symm_apply_apply, Matrix.rightKroneckerEmbed_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [mul_comm]


/-- Every observable on the complete central interval has a fixed
algebraic-local output under actual finite-chain MPU conjugation, for
all original-site buffers. No compatibility assertion is supplied.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306, restricted
here to one complete central interval. -/
theorem exists_finiteChainLocalObservable_central_interval
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU) (k : ℕ) (a : ℤ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    (B : LocalAlgebra d (finiteChainRegion (a + (2 * k : ℕ)) (2 * k))) :
    ∃ C : LocalAlgebra d (finiteChainRegion a (3 * (2 * k))),
      ∀ (p s : ℕ) (hN : 1 < p + (3 * (2 * k) + s)),
        finiteChainLocalObservable hU hN (a - p)
          (show finiteChainRegion (a + (2 * k : ℕ)) (2 * k) ⊆
            finiteChainRegion (a - p) (p + (3 * (2 * k) + s)) by
              intro x hx
              simp only [finiteChainRegion, Finset.mem_Ico] at *
              omega) B = localObservable d (finiteChainRegion a (3 * (2 * k))) C := by
  classical
  let E := MPOTensor.originalSiteHeisenbergCentreEquiv d k
  let A := Matrix.reindex E.symm E.symm
    (intervalCoordinates d (a + (2 * k : ℕ)) (2 * k) B)
  have hA : Matrix.reindex E E A =
      intervalCoordinates d (a + (2 * k : ℕ)) (2 * k) B := by
    ext row col
    simp [A, Matrix.reindex_apply]
  let hcentral : finiteChainRegion (a + (2 * k : ℕ)) (2 * k) ⊆
      finiteChainRegion a (3 * (2 * k)) := by
    intro x hx
    simp only [finiteChainRegion, Finset.mem_Ico] at *
    omega
  have hinput : (intervalCoordinates d a (3 * (2 * k))).symm
      (MPOTensor.originalSiteHeisenbergInputWindow d k A) = localInclusion hcentral B := by
    apply (intervalCoordinates d a (3 * (2 * k))).injective
    rw [StarAlgEquiv.apply_symm_apply]
    have h := intervalCoordinates_centralInclusion_originalSiteHeisenbergInputWindow d k a A
    change intervalCoordinates d a (3 * (2 * k))
      (localInclusion hcentral ((intervalCoordinates d (a + (2 * k : ℕ)) (2 * k)).symm
        (Matrix.reindex E E A))) = _ at h
    rw [hA, StarAlgEquiv.symm_apply_apply] at h
    exact h.symm
  refine ⟨(intervalCoordinates d a (3 * (2 * k))).symm
    (MPOTensor.originalSiteHeisenbergOutputWindow k u v A), ?_⟩
  intro p s hN
  let hwindow : finiteChainRegion a (3 * (2 * k)) ⊆
      finiteChainRegion (a - p) (p + (3 * (2 * k) + s)) := by
    simpa only [Nat.add_assoc] using
      finiteChainRegion_subset_expanded a (3 * (2 * k)) p s
  have h := finiteChainLocalObservable_originalSiteHeisenbergWindow hU k p s hN a S A
  rw [hinput, finiteChainLocalObservable_localInclusion] at h
  exact h



private theorem localAlgebraHom_ext_singletons {d : ℕ} [NeZero d] {Λ : Finset ℤ}
    (f g : LocalAlgebra d Λ →⋆ₐ[ℂ] AlgebraicLocalAlgebra d)
    (h : ∀ (x : ℤ) (hx : x ∈ Λ) (A : LocalAlgebra d {x}),
      f (localInclusion (Finset.singleton_subset_iff.mpr hx) A) =
        g (localInclusion (Finset.singleton_subset_iff.mpr hx) A)) : f = g := by
  classical
  let S := StarAlgHom.equalizer f g
  have hsingle : ∀ (x : ℤ), x ∈ Λ → (localObservable d {x}).range ≤
      S.map (localObservable d Λ) := by
    intro x hx z hz
    obtain ⟨A, rfl⟩ := hz
    refine StarSubalgebra.mem_map.mpr
      ⟨localInclusion (Finset.singleton_subset_iff.mpr hx) A, h x hx A, ?_⟩
    exact localObservable_localInclusion d _ A
  ext A
  have hmem : localObservable d Λ A ∈ S.map (localObservable d Λ) :=
    range_localObservable_le_of_singletons Λ (S.map (localObservable d Λ)) hsingle ⟨A, rfl⟩
  obtain ⟨X, hX, hEq⟩ := hmem
  have hXA : X = A := localObservable_injective d Λ hEq
  exact StarAlgHom.mem_equalizer f g A |>.mp (hXA ▸ hX)


private theorem exists_central_interval_output_of_bounds
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU) (k : ℕ) (a : ℤ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    (B : LocalAlgebra d (finiteChainRegion (a + (2 * k : ℕ)) (2 * k))) :
    ∃ C : LocalAlgebra d (finiteChainRegion a (3 * (2 * k))),
      ∀ (b : ℤ) (N : ℕ) (hN : 1 < N) (hl : b ≤ a)
        (hr : a + (3 * (2 * k) : ℕ) ≤ b + N),
        finiteChainLocalObservable hU hN b
          (show finiteChainRegion (a + (2 * k : ℕ)) (2 * k) ⊆ finiteChainRegion b N by
            intro x hx
            simp only [finiteChainRegion, Finset.mem_Ico] at *
            omega) B = localObservable d (finiteChainRegion a (3 * (2 * k))) C := by
  classical
  obtain ⟨C, hC⟩ := exists_finiteChainLocalObservable_central_interval hU k a S B
  refine ⟨C, ?_⟩
  intro b N hN hl hr
  let p := (a - b).toNat
  let s := (b + N - (a + (3 * (2 * k) : ℕ))).toNat
  have ha : a - p = b := by dsimp [p]; omega
  have hlen : p + (3 * (2 * k) + s) = N := by dsimp [p, s]; omega
  simpa only [ha, hlen] using hC p s (show 1 < p + (3 * (2 * k) + s) by omega)

/-- Actual finite-chain MPU conjugation agrees on an arbitrary supported
region in any two intervals containing its \(4k\) buffer. The finite
standard form is supplied, while compatibility is the conclusion.
The radius is expressed in terms of that supplied block length; the
source bond-dimension radius and inverse/completion assembly remain
separate. Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem finiteChainLocalObservable_eq_of_twoSiteStandardForm_buffers
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    (Λ : Finset ℤ) (b₁ b₂ : ℤ) (N₁ N₂ : ℕ) (hN₁ : 1 < N₁) (hN₂ : 1 < N₂)
    (hΛ₁ : Λ ⊆ finiteChainRegion b₁ N₁) (hΛ₂ : Λ ⊆ finiteChainRegion b₂ N₂)
    (hb₁ : ∀ x ∈ Λ, b₁ ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ b₁ + N₁)
    (hb₂ : ∀ x ∈ Λ, b₂ ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ b₂ + N₂) :
    finiteChainLocalObservable hU hN₁ b₁ hΛ₁ =
      finiteChainLocalObservable hU hN₂ b₂ hΛ₂ := by
  classical
  have hd : d ≠ 0 := by
    intro hd
    have hpos := S.phys_pos
    simp [MPSTensor.blockPhysDim_eq_pow, hd, hk.ne'] at hpos
  let : NeZero d := ⟨hd⟩
  apply localAlgebraHom_ext_singletons
  intro x hx A
  let a := x - (2 * k : ℕ)
  let hsingle : ({x} : Finset ℤ) ⊆ finiteChainRegion (a + (2 * k : ℕ)) (2 * k) := by
    intro y hy
    have hyx := Finset.mem_singleton.mp hy
    subst y
    simp only [finiteChainRegion, Finset.mem_Ico]
    dsimp [a]
    omega
  obtain ⟨C, hC⟩ := exists_central_interval_output_of_bounds hU k a S
    (localInclusion hsingle A)
  have hleft₁ : b₁ ≤ a := (hb₁ x hx).1
  have hleft₂ : b₂ ≤ a := (hb₂ x hx).1
  have hright₁ : a + (3 * (2 * k) : ℕ) ≤ b₁ + N₁ := by
    have h := (hb₁ x hx).2
    dsimp [a]
    omega
  have hright₂ : a + (3 * (2 * k) : ℕ) ≤ b₂ + N₂ := by
    have h := (hb₂ x hx).2
    dsimp [a]
    omega
  have h₁ := hC b₁ N₁ hN₁ hleft₁ hright₁
  have h₂ := hC b₂ N₂ hN₂ hleft₂ hright₂
  have hcompose : ∀ {N : ℕ} (b : ℤ) (hN : 1 < N)
      (hcentral : finiteChainRegion (a + (2 * k : ℕ)) (2 * k) ⊆ finiteChainRegion b N)
      (hΛ : Λ ⊆ finiteChainRegion b N),
      finiteChainLocalObservable hU hN b hcentral (localInclusion hsingle A) =
        finiteChainLocalObservable hU hN b hΛ
          (localInclusion (Finset.singleton_subset_iff.mpr hx) A) := by
    intro N b hN hcentral hΛ
    rw [finiteChainLocalObservable_localInclusion,
      finiteChainLocalObservable_localInclusion]

  rw [hcompose b₁ hN₁ _ hΛ₁] at h₁
  rw [hcompose b₂ hN₂ _ hΛ₂] at h₂
  exact h₁.trans h₂.symm

end SpinChain
