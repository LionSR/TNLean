/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.GoodProjectorHardTruncation

/-!
# Corollary 4.6 as one statement

Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Corollary `c:goodagsphardtrunc`
(lines 979–1005), hard-truncate the three bulks of a chain cut into five regions at height `t`
and apply the Chebyshev projector of Theorem 4.2 (`thm:Cheby-AGSP`, lines 809–853) to the
truncated Hamiltonian at degree `k = ℓ²`. The corollary asserts, for the same truncated
Hamiltonian, the spectral comparisons `e:specclose` and `e:setclose` with the original chain and
a projector with `D = (dℓ)^{O(ℓ)}` and `Δ = e^{−Ω(ℓ² √(η₁ − η₀) / √(t + ℓ))}`.

`GoodProjectorHardTruncation` proves the spectral part for the actual truncated chain and the
projector part for every Hamiltonian of the two-window form. This file joins them into one
statement about the same truncated Hamiltonian `Ht`: its spectral comparison with `H`, and for
every `η₀ < η₁ ≤ 3t + 4ℓ` a real polynomial `p` of degree `ℓ²` with `p(η₀) = 1` such that
`p(Ht)` is a spectral projector for `(Ht, η₀, η₁)` with
`Δ = 4 exp(−4ℓ² √((η₁ − η₀)/(3t + 4ℓ − η₀)))` and operator Schmidt rank at most `(qℓ)^{68ℓ}`
across both middle cuts.

**Local fix (explicit constants, cutoff, spectral conditions):** the constants, the cutoff
`19 + η ≤ t` of the spectral comparison, the closed spectral conditions and the slope near `η₀`
are those of `GoodProjectorHardTruncation`, which records them. The cutoff corrects the printed
condition `t > η`, under which the truncated-side estimate is false; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
-/

open ManyBody (interval)

open Matrix Polynomial TNLean.Lattice TNLean.Lattice.Sheet QuantumCircuit
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ALVV

/-- The Chebyshev projector at degree `ℓ²` of a matrix equal to a Hamiltonian of the two-window
form. Auxiliary to ALVV, arXiv:1602.08828v2, `c:goodagsphardtrunc`, lines 979–1005. -/
private theorem exists_degree_sq_projector_of_eq_two_window
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + r.val) (a + r.val + 2) : Finset (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + r.val) (b + r.val + 2) : Finset (Fin L)))
    (hL : F (Sum.inr 0) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L 0 (a + 1) : Finset (Fin L)))
    (hM : F (Sum.inr 1) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + 2 * ℓ) (b + 1) : Finset (Fin L)))
    (hR : F (Sum.inr 2) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + 2 * ℓ) L : Finset (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1) (hℓ : 1 ≤ ℓ) (hq : 1 ≤ q)
    (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (hMF : M = ∑ α, F α)
    (hMh : M.IsHermitian) {u η₀ η₁ : ℝ} (hnorm : ‖M‖ ≤ u) (h01 : η₀ < η₁) (h1u : η₁ ≤ u) :
    ∃ p : Polynomial ℝ, p.natDegree = ℓ * ℓ ∧ p.eval η₀ = 1 ∧
      Submodule.IsSpectralProjector
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (aeval M (p.map (algebraMap ℝ ℂ))))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
        ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hMh).eigenvectorBasis finrank_euclideanSpace)
        ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hMh).eigenvalues finrank_euclideanSpace)
        (fun j ↦ p.eval ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hMh).eigenvalues
          finrank_euclideanSpace j)) η₀ η₁
        (4 * Real.exp (-4 * ((ℓ * ℓ : ℕ) : ℝ) * Real.sqrt ((η₁ - η₀) / (u - η₀)))) ∧
      ∀ δ : Fin 2,
        operatorSchmidtRank ((aeval M (p.map (algebraMap ℝ ℂ))).reindex
          (sheetSplit q (interval L (a + ℓ + δ.val) (b + ℓ + 1)))
          (sheetSplit q (interval L (a + ℓ + δ.val) (b + ℓ + 1)))) ≤ (q * ℓ) ^ (68 * ℓ) := by
  subst hMF
  obtain ⟨p, hdeg, hp0, hK, -, hrank⟩ := exists_two_window_chebyshev_projector_degree_sq F
    hleft hright hL hM hR hab hb hℓ hq hMh hnorm h01 h1u
  exact ⟨p, hdeg, hp0, hK, fun δ ↦ (hrank δ).2⟩

/-- **Corollary 4.6: a good projector after hard truncation of three regions** (ALVV,
arXiv:1602.08828v2, Corollary `c:goodagsphardtrunc`, lines 979–1005). Under the hypotheses of
`exists_three_bulk_hard_truncation_spectral_comparison`, its truncated Hamiltonian `Ht`
satisfies all the conclusions of that theorem, and in addition, for every `η₀ < η₁ ≤ 3t + 4ℓ`,
there is a real polynomial `p` of degree `ℓ²` with `p(η₀) = 1` such that `p(Ht)` is a spectral
projector for `(Ht, η₀, η₁)` with `Δ = 4 exp(−4ℓ² √((η₁ − η₀)/(3t + 4ℓ − η₀)))` and operator
Schmidt rank at most `(qℓ)^{68ℓ}` across both middle cuts. This is the form `D = (dℓ)^{O(ℓ)}`,
`Δ = e^{−Ω(ℓ² √(η₁ − η₀)/√(t + ℓ))}` of the source, under the local fix of this module. -/
theorem exists_three_bulk_hard_truncation_good_projector
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
      (∀ r, F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
        (interval L (a + r.val) (a + r.val + 2) : Finset (Fin L))) ∧
      (∀ r, F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
        (interval L (b + r.val) (b + r.val + 2) : Finset (Fin L))) ∧
      F (Sum.inr 0) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
          (interval L 0 (a + 1) : Finset (Fin L)) ∧
      F (Sum.inr 1) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
          (interval L (a + 2 * ell) (b + 1) : Finset (Fin L)) ∧
      F (Sum.inr 2) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
          (interval L (b + 2 * ell) L : Finset (Fin L)) ∧
      ∃ (hH : H.IsHermitian) (hHt : Ht.IsHermitian),
        let bH := (isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
          finrank_euclideanSpace
        let bHt := (isSymmetric_toEuclideanLin_iff.mpr hHt).eigenvectorBasis
          finrank_euclideanSpace
        let E0' := hHt.eigenvalues₀ jmin
        let eigHt := (isSymmetric_toEuclideanLin_iff.mpr hHt).eigenvalues finrank_euclideanSpace
        hH.eigenvalues₀ jmin = E0 ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧ Ht ≤ H ∧
        ‖Ht‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
        (∀ η : ℝ, 0 ≤ η → 19 + η ≤ t →
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
              (Submodule.spectralSpanLE bHt hHt.eigenvalues₀ (E0' + η)))) ∧
        ∀ η₀ η₁ : ℝ, η₀ < η₁ → η₁ ≤ 3 * t + 4 * (ell : ℝ) →
          ∀ Δ : ℝ, Δ = 4 * Real.exp (-4 * ((ell * ell : ℕ) : ℝ) *
            Real.sqrt ((η₁ - η₀) / (3 * t + 4 * (ell : ℝ) - η₀))) →
          ∃ p : Polynomial ℝ, p.natDegree = ell * ell ∧ p.eval η₀ = 1 ∧
            Submodule.IsSpectralProjector
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (aeval Ht (p.map (algebraMap ℝ ℂ))))
              (Matrix.toEuclideanCLM (𝕜 := ℂ) Ht)
              bHt eigHt (fun j ↦ p.eval (eigHt j)) η₀ η₁
              Δ ∧
            ∀ δ : Fin 2,
              operatorSchmidtRank ((aeval Ht (p.map (algebraMap ℝ ℂ))).reindex
                (sheetSplit q (interval L (a + ell + δ.val) (b + ell + 1)))
                (sheetSplit q (interval L (a + ell + δ.val) (b + ell + 1)))) ≤
                (q * ell) ^ (68 * ell)   := by
  intro k I A J Y K jmin
  obtain ⟨e, E0, x, hrest⟩ := exists_three_bulk_hard_truncation_spectral_comparison
    L q a b ell t hq hell ht0 hab hbL h hs h0 h1
  refine ⟨e, E0, x, ?_⟩
  intro S H Ht F
  obtain ⟨hx, hxe, hpos, hHtF, hleft, hright, hL0, hM, hR, hH, hHt, hrest⟩ := hrest
  obtain ⟨hE0, hE00, hE04, hle, hnorm, hspec⟩ := hrest
  refine ⟨hx, hxe, hpos, hHtF, hleft, hright, hL0, hM, hR, hH, hHt,
    hE0, hE00, hE04, hle, hnorm, hspec, ?_⟩
  intro η₀ η₁ h01 h1u Δ hΔ
  subst hΔ
  exact exists_degree_sq_projector_of_eq_two_window F hleft hright hL0 hM hR hab hbL hell
    (by omega) Ht hHtF hHt hnorm h01 h1u

end TNLean.MPS.AreaLaw.ALVV
