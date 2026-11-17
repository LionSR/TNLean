/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.RelativeLowEnergyCloseness
import QICLean.Representation.CoherentSymbolFunction
import TNLean.Circuit.SupportedFunctionalCalculus
import TNLean.Lattice.HardTruncation
import TNLean.MPS.AreaLaw.ALVV.SpectralProjector
import TNLean.MPS.AreaLaw.IndependentFiveRegionResidual

/-!
# A good spectral projector after hard truncation of three regions

Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Corollary `c:goodagsphardtrunc`
(lines 979–1005), combine hard truncation (Definition `def:hard-trunc`, Lemma `lem:hard-trunc`)
with the Chebyshev projector at two cuts (Theorem `thm:Cheby-AGSP`). They cut a chain of
positive contractions `0 ≤ hᵢ ≤ 1` into five consecutive regions: three bulks and two windows
of `2ℓ` bonds about the cuts. Truncating the three bulks at height `t` above their ground
energies and taking `k = ℓ²` gives `D = (dℓ)^{O(ℓ)}` and
`Δ = e^{−Ω(ℓ² √(η₁ − η₀) / √(t + ℓ))}`. It also gives eigenvalue shifts exponentially small
in `t − η` (eq. `e:specclose`) and closeness `δ` of the low-energy spaces (eq. `e:setclose`).

This file states that corollary for the actual truncated chain, in two theorems. The regional
minima, the common unit regional ground vector and the centred ground energy are constructed,
not assumed, and the ground space may be degenerate.
* `exists_three_bulk_hard_truncation_spectral_comparison` gives eqs. `e:specclose` and
  `e:setclose`, from the residual of the three-bulk truncation
  (`TNLean.MPS.AreaLaw.exists_five_region_independent_truncation_residual`). It also writes the
  truncated Hamiltonian in the two-window form `eq:H-mid-cut`, with norm at most `3t + 4ℓ`.
* `exists_two_window_chebyshev_projector_degree_sq` applies
  `exists_two_window_chebyshev_spectral_projector` to any Hamiltonian of that form, at degree
  `ℓ²` and with any upper bound `u` on `‖H‖`. For the truncated Hamiltonian
  `u = 3t + 4ℓ`, which gives the source's `D` and `Δ`.

**Local fix (explicit constants, cutoff, spectral conditions):**
* The `O`- and `Ω`-constants are explicit:
  * the cutoff is `19 + η ≤ t`;
  * the eigenvalue and residual error is `ξ = 288 e^{11/8} e^{−(t−η)/8}`;
  * the window count of the closeness enlargement is the ceiling;
  * the contraction is `Δ = 4 exp(−4ℓ² √((η₁ − η₀)/(3t + 4ℓ − η₀)))`;
  * the two-cut rank is `(qℓ²)^{17(ℓ + ⌊ℓ²/(2ℓ)⌋)}`.
* With `t > η` alone the truncated-side estimate fails, so a cutoff is needed:
  https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.
* The spectral conditions are the closed ones, and positivity of the filter is not asserted.
* The slope near `η₀` and the additional `+1` of the word count are those of Theorem 4.2:
  https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf,
  https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf,
  https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_near_ground_slope.pdf and
  https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
* Two-window form needs `a + 2ℓ ≤ b` and `b + 2ℓ ≤ L − 1`, so both windows consist of `2ℓ`
  bonds of the chain.
-/

open Matrix Polynomial TNLean.Lattice TNLean.Lattice.Sheet QuantumCircuit
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ALVV

/-- The `2ℓ` bonds of a window starting at bond `c`, listed by their offset, sum to the bonds
with index in `[c, c + 2ℓ)`. Auxiliary to ALVV, arXiv:1602.08828v2, `c:goodagsphardtrunc`,
lines 979–1005. -/
private theorem sum_window_bonds {L q ℓ c : ℕ} (hc : c + 2 * ℓ ≤ L - 1)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    ∑ r : Fin (2 * ℓ), h ⟨c + r.val, by omega⟩ =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦ c ≤ i.val ∧ i.val < c + 2 * ℓ), h i := by
  refine Finset.sum_bij' (fun r _ ↦ ⟨c + r.val, by omega⟩)
    (fun i hi ↦ ⟨i.val - c, by simp only [Finset.mem_filter] at hi; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro r _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i _
    exact Finset.mem_univ _
  · intro r _
    ext
    simp
  · intro i hi
    simp only [Finset.mem_filter] at hi
    ext
    simp only
    omega
  · intro r _
    rfl

/-- A matrix that is Hermitian after subtracting a real multiple of the identity is Hermitian.
Auxiliary to ALVV, arXiv:1602.08828v2, `c:goodagsphardtrunc`, lines 979–1005. -/
private theorem isHermitian_of_posSemidef_sub_smul {n : Type*} [DecidableEq n]
    {M : Matrix n n ℂ} {c : ℝ} (hM : (M - (c : ℂ) • 1).PosSemidef) : M.IsHermitian := by
  have hc : ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  simpa using hM.isHermitian.add hc

/-- The additive rearrangement of the five centred regional terms into two windows and three
bulks. Auxiliary to ALVV, arXiv:1602.08828v2, `c:goodagsphardtrunc`, lines 979–1005. -/
private theorem five_region_rearrange {G : Type*} [AddCommGroup G]
    (X0 A1 X2 A3 X4 Y s0 s1 s2 s3 s4 : G) :
    X0 - s0 + (A1 - s1) + (X2 - s2) + (A3 - s3) + (X4 - s4) + Y =
      A1 + A3 + Y + (X0 - (s0 + s1 + s3) + (X2 - s2) + (X4 - s4)) := by
  abel

/-- **Corollary 4.6, spectral part: hard truncation of three regions** (ALVV,
arXiv:1602.08828v2, Corollary `c:goodagsphardtrunc`, lines 979–1005, eqs. `e:specclose` and
`e:setclose`).

Let `0 ≤ hᵢ ≤ 1` be nearest-neighbour terms of a chain of `L` qudits of dimension `q`. Cut the
chain into three bulks and two windows of `2ℓ` bonds starting at the bonds `a` and `b`, with
`a + 2ℓ ≤ b` and `b + 2ℓ ≤ L − 1`.
* The original Hamiltonian `H` and its hard truncation `H̃` are both centred at the sum of the
  five actual regional minima. `H̃` truncates the three bulks at height `t ≥ 0` above their own
  minima.
* Constructed, not assumed: the regional minima, a common unit regional ground vector, and the
  centred ground energy `E₀ ∈ [0, 4]` of `H`.

Then:
* `H̃ ≤ H` and `‖H̃‖ ≤ 3t + 4ℓ`.
* `H̃` is the sum of the `2ℓ` two-site terms of each window and of three bulk operators
  supported on the three bulks, which is the form `eq:H-mid-cut` of Theorem 4.2.
* For every `η ≥ 0` with `19 + η ≤ t`, put `ξ = 288 e^{11/8} e^{−(t−η)/8}`:
  * the ordered eigenvalues of `H̃` below `E₀ + η` lie at most `ξ` below those of `H`
    (eq. `e:specclose`);
  * the ground energies satisfy `E₀′ ≤ E₀ ≤ E₀′ + ξ`;
  * if `η > 0`, then for every `δ > 0` the low-energy spaces are `δ`-close in both directions
    after the window is enlarged to `η′ = η + ξ + 2ξ √(⌈η/(2ξ)⌉/δ)` (eq. `e:setclose`).

The Chebyshev projector of `H̃` at degree `ℓ²` is
`exists_two_window_chebyshev_projector_degree_sq`.

**Local fix (explicit constants and cutoff):** the constant and the cutoff are explicit, and a
cutoff is needed because the truncated-side estimate fails for `t > η` alone; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf. -/
theorem exists_three_bulk_hard_truncation_spectral_comparison
    (L q a b ell : ℕ) (t : ℝ) (hq : 0 < q) (hell : 1 ≤ ell) (ht0 : 0 ≤ t)
    (hab : a + 2 * ell ≤ b) (hbL : b + 2 * ell ≤ L - 1)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let I : Fin 5 → Finset (Fin (L - 1)) := fun j ↦
      Finset.univ.filter (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun j ↦ ∑ i ∈ I j, h i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ J, h i
    let K : Finset (Fin 5) := {0, 2, 4}
    let jmin : Fin (Fintype.card (Fin L → Fin q)) :=
      ⟨Fintype.card (Fin L → Fin q) - 1,
        Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨fun _ ↦ (Fin.mk (0 : ℕ) hq : Fin q)⟩) one_pos⟩
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x : (Fin L → Fin q) → ℂ),
      let S := ∑ j, e j
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := (∑ i, h i) - (S : ℂ) • 1
      let Ht : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        (∑ j, ((if j ∈ K then cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
          (e j : ℂ) • 1)) + Y
      let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
          Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        Sum.elim (Sum.elim
          (fun r ↦ h ⟨a + r.val, (Nat.add_lt_add_left r.isLt a).trans_le
            (hab.trans ((Nat.le_add_right b (2 * ell)).trans hbL))⟩)
          (fun r ↦ h ⟨b + r.val, (Nat.add_lt_add_left r.isLt b).trans_le hbL⟩))
          ![cfc (fun r : ℝ ↦ min r (e 0 + t)) (A 0) - ((e 0 + e 1 + e 3 : ℝ) : ℂ) • 1,
            cfc (fun r : ℝ ↦ min r (e 2 + t)) (A 2) - (e 2 : ℂ) • 1,
            cfc (fun r : ℝ ↦ min r (e 4 + t)) (A 4) - (e 4 : ℂ) • 1]
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      Ht = ∑ α, F α ∧
      (∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
        (interval L (a + r.val) (a + r.val + 2) : Set (Fin L))) ∧
      (∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
        (interval L (b + r.val) (b + r.val + 2) : Set (Fin L))) ∧
      F (Sum.inr 0) ∈ supportedOperators q (interval L 0 (a + 1) : Set (Fin L)) ∧
      F (Sum.inr 1) ∈ supportedOperators q (interval L (a + 2 * ell) (b + 1) : Set (Fin L)) ∧
      F (Sum.inr 2) ∈ supportedOperators q (interval L (b + 2 * ell) L : Set (Fin L)) ∧
      ∃ (hH : H.IsHermitian) (hHt : Ht.IsHermitian),
        let bH := (isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
          finrank_euclideanSpace
        let bHt := (isSymmetric_toEuclideanLin_iff.mpr hHt).eigenvectorBasis
          finrank_euclideanSpace
        let E0' := hHt.eigenvalues₀ jmin
        hH.eigenvalues₀ jmin = E0 ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧ Ht ≤ H ∧
        ‖Ht‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
        ∀ η : ℝ, 0 ≤ η → 19 + η ≤ t →
          let ξ : ℝ := (288 * Real.exp (11 / 8)) * Real.exp (-(t - η) / 8)
          (∀ i, hHt.eigenvalues₀ i ≤ E0 + η →
            hHt.eigenvalues₀ i ≤ hH.eigenvalues₀ i ∧
              hH.eigenvalues₀ i ≤ hHt.eigenvalues₀ i + ξ) ∧
          E0' ≤ E0 ∧ E0 ≤ E0' + ξ ∧
          (0 < η → ∀ δ : ℝ, 0 < δ →
            let η' : ℝ := η + ξ + 2 * ξ * Real.sqrt ((⌈η / (2 * ξ)⌉₊ : ℝ) / δ)
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bHt hHt.eigenvalues₀ (E0' + η'))
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E0 + η)) ∧
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E0 + η'))
              (Submodule.spectralSpanLE bHt hHt.eigenvalues₀ (E0' + η))) := by
  intro k I A J Y K jmin
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low, hE0ge, hE0le4,
      hnorm, hres⟩ :=
    TNLean.MPS.AreaLaw.exists_five_region_independent_truncation_residual
      L q a b ell t hq hell ht0 (by omega) (by omega) h hs h0 h1
  obtain ⟨_, _, hAs, hApos, hYpos, _, _, hHsum⟩ :=
    TNLean.MPS.AreaLaw.five_region_original_bond_data L q (a + 1) (a + 2 * ell) (b + 1)
      (b + 2 * ell) (by omega) (by omega) (by omega) (by omega) h hs h0 h1
  refine ⟨e, E0, x, ?_⟩
  intro S H Ht F
  let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
  have hAh (j : Fin 5) : (A j).IsHermitian := (hApos j).1.isHermitian
  have hX (j : Fin 5) :
      (if j ∈ K then cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) ≤ A j := by
    split_ifs
    · exact (hAh j).energyTruncation_le (e j + t)
    · exact le_rfl
  have hHB : H = (∑ j, (A j - (e j : ℂ) • 1)) + Y := by
    change (∑ i, h i) - ((∑ j, e j : ℝ) : ℂ) • 1 = _
    rw [← hcenter]
    simp only [Finset.notMem_empty, ite_false]
    rfl
  have hle : Ht ≤ H := by
    rw [hHB]
    change (∑ j, ((if j ∈ K then cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
      (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))) + Y ≤ _
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) ↦
      sub_le_sub_right (hX j) ((e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
    exact add_le_add_left hsum Y
  have hH : H.IsHermitian := by
    rw [hHB]
    exact isHermitian_of_posSemidef_sub_smul (by simpa only [Finset.notMem_empty, ite_false]
      using hE0low)
  have hHt : Ht.IsHermitian := by
    have hterm (j : Fin 5) : ((if j ∈ K then cfc (fun r : ℝ ↦ min r (e j + t)) (A j)
        else A j) - (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).IsHermitian := by
      have hc : ((e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).IsHermitian := by
        simp [IsHermitian, conjTranspose_smul]
      refine IsHermitian.sub ?_ hc
      split_ifs
      · exact isHermitian_energyTruncation (A j) (e j + t)
      · exact hAh j
    have hsum : (∑ j, ((if j ∈ K then cfc (fun r : ℝ ↦ min r (e j + t)) (A j)
        else A j) - (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))).IsHermitian :=
      isHermitian_iff_isSelfAdjoint.mpr (isSelfAdjoint_sum Finset.univ fun j _ ↦
        isHermitian_iff_isSelfAdjoint.mp (hterm j))
    exact hsum.add hYpos.isHermitian
  have hBH : (∑ j, ((if j ∈ (∅ : Finset (Fin 5)) then cfc (fun r : ℝ ↦ min r (e j + t)) (A j)
      else A j) - (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))) + Y = H := by
    simp only [Finset.notMem_empty, ite_false]
    exact hHB.symm
  have hlastH : hH.eigenvalues₀ jmin = E0 := by
    have hz' : H *ᵥ z = (E0 : ℂ) • z := by rw [← hBH]; exact hz
    have hlow' : (H - (E0 : ℂ) • 1).PosSemidef := by rw [← hBH]; exact hE0low
    have hmin : minEigenvalue hH = E0 := by
      simpa using hH.minEigenvalue_eq_add_of_centered_ground 0 E0 z hzunit
        (by simpa using hz') (by simpa using hlow')
    exact hH.eigenvalues₀_last_eq_minEigenvalue.trans hmin
  have hresidual (η : ℝ) (hη : 0 ≤ η) (ht : 19 + η ≤ t) :
      ‖(ι H - ι Ht).domRestrict
          (Submodule.spectralSpanLE
            ((isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis finrank_euclideanSpace)
            hH.eigenvalues₀ (E0 + η))‖ ≤
          (288 * Real.exp (11 / 8)) * Real.exp (-(t - η) / 8) ∧
      ‖(ι H - ι Ht).domRestrict
          (Submodule.spectralSpanLE
            ((isSymmetric_toEuclideanLin_iff.mpr hHt).eigenvectorBasis finrank_euclideanSpace)
            hHt.eigenvalues₀ (E0 + η))‖ ≤
          (288 * Real.exp (11 / 8)) * Real.exp (-(t - η) / 8) := by
    have r1 := hres ∅ η hη ht hH.eigenvectorBasis hH.eigenvalues (fun j ↦ by
      beta_reduce; rw [hBH]; exact hH.toEuclideanCLM_eigenvectorBasis j)
    have r2 := hres K η hη ht hHt.eigenvectorBasis hHt.eigenvalues (fun j ↦
      hHt.toEuclideanCLM_eigenvectorBasis j)
    beta_reduce at r1 r2
    rw [hBH, map_sub, hH.spectralSpanLE_eigenvectorBasis_eq] at r1
    rw [hBH, map_sub, hHt.spectralSpanLE_eigenvectorBasis_eq] at r2
    exact ⟨r1, r2⟩
  have hwin : ∑ r, F (Sum.inl (Sum.inl r)) + ∑ r, F (Sum.inl (Sum.inr r)) = A 1 + A 3 + Y := by
    simp only [F, Sum.elim_inl, Sum.elim_inr]
    rw [sum_window_bonds (c := a) (by omega) h, sum_window_bonds (c := b) hbL h]
    have k1 : k (Fin.castSucc 1) = a + 1 := rfl
    have k2 : k (Fin.succ 1) = a + 2 * ell := rfl
    have k3 : k (Fin.castSucc 3) = b + 1 := rfl
    have k4 : k (Fin.succ 3) = b + 2 * ell := rfl
    simp only [A, I, Y, J, Finset.sum_filter, ← Finset.sum_add_distrib, k1, k2, k3, k4]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> first | (exfalso; omega) | simp
  have hdecomp : Ht = ∑ α, F α := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hwin, Fin.sum_univ_three]
    simp only [Ht, F, Fin.sum_univ_five, K, Sum.elim_inr]
    simp (config := { decide := true }) only [ite_true, ite_false, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
    push_cast
    simp only [add_smul]
    exact five_region_rearrange _ _ _ _ _ _ _ _ _ _ _
  have hsupp : (∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
        (interval L (a + r.val) (a + r.val + 2) : Set (Fin L))) ∧
      (∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
        (interval L (b + r.val) (b + r.val + 2) : Set (Fin L))) ∧
      F (Sum.inr 0) ∈ supportedOperators q (interval L 0 (a + 1) : Set (Fin L)) ∧
      F (Sum.inr 1) ∈ supportedOperators q (interval L (a + 2 * ell) (b + 1) : Set (Fin L)) ∧
      F (Sum.inr 2) ∈ supportedOperators q (interval L (b + 2 * ell) L : Set (Fin L)) := by
    have hbulk (j : Fin 5) (c : ℝ) (lo hi : ℕ)
        (hR : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A j) (interval L lo hi)) :
        cfc (fun r : ℝ ↦ min r (e j + t)) (A j) - (c : ℂ) • 1 ∈
          supportedOperators q (interval L lo hi : Set (Fin L)) :=
      sub_mem (cfc_mem_supportedOperators _ (mem_supportedOperators_of_isSupportedOn hR))
        (Submodule.smul_mem _ _ (one_mem_supportedOperators _))
    exact ⟨fun r ↦ mem_supportedOperators_of_isSupportedOn (hs _),
      fun r ↦ mem_supportedOperators_of_isSupportedOn (hs _),
      hbulk 0 _ _ _ (hAs 0), hbulk 2 _ _ _ (hAs 2), hbulk 4 _ _ _ (hAs 4)⟩
  beta_reduce at hnorm
  refine ⟨hxunit, hx, hlo, hdecomp, hsupp.1, hsupp.2.1, hsupp.2.2.1, hsupp.2.2.2.1,
    hsupp.2.2.2.2, hH, hHt, ?_⟩
  intro bH bHt E0'
  refine ⟨hlastH, hE0ge, hE0le4, hle, hnorm, ?_⟩
  intro η hη ht ξ
  obtain ⟨hrH, hrF⟩ := hresidual η hη ht
  have hξ : 0 < ξ := by positivity
  have hg1 : E0' ≤ E0 := hlastH ▸ hHt.eigenvalues₀_mono hH hle jmin
  have hg2 : E0 ≤ E0' + ξ := by
    have := hH.eigenvalues₀_le_add_of_norm_domRestrict_low_le hHt (E0 + η) ξ hrF jmin
      (by linarith)
    rwa [hlastH] at this
  refine ⟨fun i hi ↦ ⟨hHt.eigenvalues₀_mono hH hle i,
    hH.eigenvalues₀_le_add_of_norm_domRestrict_low_le hHt (E0 + η) ξ hrF i hi⟩, hg1, hg2, ?_⟩
  intro hη0 δ hδ
  have hgen := hH.groundEnergy_compare_and_isCloseTo_spectralSpanLE_of_norm_domRestrict_le
    hHt hle η ξ δ hη0 hξ hδ
  dsimp only at hgen
  rw [hlastH] at hgen
  obtain ⟨_, _, c1, c2⟩ := hgen hrH hrF
  exact ⟨c1, c2⟩

/-- The two-cut rank `(qℓ²)^{17(ℓ + ⌊ℓ²/(2ℓ)⌋)}` is at most `(qℓ)^{68ℓ}`, the form
`D = (dℓ)^{O(ℓ)}` of ALVV, arXiv:1602.08828v2, `c:goodagsphardtrunc`, lines 979–1005. -/
private theorem two_cut_rank_degree_sq_le {q ℓ : ℕ} (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ) :
    (q * (ℓ * ℓ)) ^ (17 * (ℓ + ℓ * ℓ / (2 * ℓ))) ≤ (q * ℓ) ^ (68 * ℓ) := by
  have hbase : q * (ℓ * ℓ) ≤ (q * ℓ) ^ 2 := by
    have : q * (ℓ * ℓ) ≤ q * q * (ℓ * ℓ) :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left q (by omega))
    calc q * (ℓ * ℓ) ≤ q * q * (ℓ * ℓ) := this
      _ = (q * ℓ) ^ 2 := by ring
  have hdiv : ℓ * ℓ / (2 * ℓ) ≤ ℓ := Nat.div_le_of_le_mul (by nlinarith)
  have hexp : 17 * (ℓ + ℓ * ℓ / (2 * ℓ)) ≤ 34 * ℓ := by omega
  have hpos : 1 ≤ (q * ℓ) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hq hℓ)
  calc (q * (ℓ * ℓ)) ^ (17 * (ℓ + ℓ * ℓ / (2 * ℓ)))
      ≤ ((q * ℓ) ^ 2) ^ (17 * (ℓ + ℓ * ℓ / (2 * ℓ))) := Nat.pow_le_pow_left hbase _
    _ ≤ ((q * ℓ) ^ 2) ^ (34 * ℓ) := Nat.pow_le_pow_right hpos hexp
    _ = (q * ℓ) ^ (68 * ℓ) := by rw [← pow_mul]; ring_nf

/-- **Corollary 4.6, projector part: the Chebyshev projector at degree `ℓ²`** (ALVV,
arXiv:1602.08828v2, Corollary `c:goodagsphardtrunc`, lines 979–1005, applying
Theorem `thm:Cheby-AGSP`, lines 809–853, with `k = ℓ²`).

Let `H = ∑ α, F α` be a Hermitian Hamiltonian of the two-window form `eq:H-mid-cut`, with
`‖H‖ ≤ u` and `η₀ < η₁ ≤ u`. The truncated Hamiltonian of
`exists_three_bulk_hard_truncation_spectral_comparison` has this form, with `u = 3t + 4ℓ`.
Then there is one real polynomial `p` of degree `ℓ²` with `p(η₀) = 1` such that `K = p(H)`:
* is a spectral projector for `(H, η₀, η₁)` with
  `Δ = 4 exp(−4ℓ² √((η₁ − η₀)/(u − η₀)))`. For `u = 3t + 4ℓ` this is
  `Δ = e^{−Ω(ℓ² √(η₁ − η₀)/√(t + ℓ))}`.
* keeps every eigenvalue `λ ≤ η₁` at least `1 − ℓ² |λ − η₀| / √((η₁ − η₀)(u − η₀))`;
* has operator Schmidt rank across both middle cuts at most `(qℓ²)^{17(ℓ + ⌊ℓ²/(2ℓ)⌋)}`, and
  hence at most `(qℓ)^{68ℓ}`. This is the bound `D = (dℓ)^{O(ℓ)}`.

**Local fix (closed spectral conditions, positivity, slope, word count):** inherited from
`exists_two_window_chebyshev_spectral_projector`; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf,
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf,
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_near_ground_slope.pdf and
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf. -/
theorem exists_two_window_chebyshev_projector_degree_sq
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1) (hℓ : 1 ≤ ℓ) (hq : 1 ≤ q)
    (hH : (∑ α, F α).IsHermitian) {u η₀ η₁ : ℝ} (hnorm : ‖∑ α, F α‖ ≤ u)
    (h01 : η₀ < η₁) (h1u : η₁ ≤ u) :
    let H := ∑ α, F α
    let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
    let eig := hS.eigenvalues finrank_euclideanSpace
    let Δ := 4 * Real.exp (-4 * ((ℓ * ℓ : ℕ) : ℝ) * Real.sqrt ((η₁ - η₀) / (u - η₀)))
    ∃ p : Polynomial ℝ, p.natDegree = ℓ * ℓ ∧ p.eval η₀ = 1 ∧
      let K := aeval H (p.map (algebraMap ℝ ℂ))
      Submodule.IsSpectralProjector (Matrix.toEuclideanCLM (𝕜 := ℂ) K)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) H) (hS.eigenvectorBasis finrank_euclideanSpace) eig
        (fun j ↦ p.eval (eig j)) η₀ η₁ Δ ∧
      (∀ j, eig j ≤ η₁ →
        1 - ((ℓ * ℓ : ℕ) : ℝ) * |eig j - η₀| / √((η₁ - η₀) * (u - η₀)) ≤ p.eval (eig j)) ∧
      (∀ δ : Fin 2,
        let J := interval L (a + ℓ + δ.val) (b + ℓ + 1)
        operatorSchmidtRank (K.reindex (sheetSplit q J) (sheetSplit q J)) ≤
            (q * (ℓ * ℓ)) ^ (17 * (ℓ + ℓ * ℓ / (2 * ℓ))) ∧
          operatorSchmidtRank (K.reindex (sheetSplit q J) (sheetSplit q J)) ≤
            (q * ℓ) ^ (68 * ℓ)) := by
  intro H hS eig Δ
  have hupper : ∀ j, (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH).eigenvalues
      finrank_euclideanSpace j ≤ u := by
    intro j
    have habs := hH.abs_eigenvalues_le (Fintype.equivOfCardEq (Fintype.card_fin _) j)
    simp only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] at habs
    exact (le_abs_self _).trans (habs.trans hnorm)
  have hk : 1 ≤ ℓ * ℓ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨p, hdeg, hp0, hK, hnear, hrank, -⟩ :=
    exists_two_window_chebyshev_spectral_projector F hleft hright hL hM hR hab hb hℓ hH
      (ℓ * ℓ) hk h01 h1u hupper
  refine ⟨p, hdeg, hp0, hK, hnear, fun δ ↦ ⟨hrank δ, (hrank δ).trans ?_⟩⟩
  exact two_cut_rank_degree_sq_le hq hℓ

end TNLean.MPS.AreaLaw.ALVV
