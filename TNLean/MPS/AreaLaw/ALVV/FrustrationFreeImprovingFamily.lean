/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ChebyshevViability
import QICLean.Analysis.LowEnergyCoordinates
import QICLean.Analysis.MatrixTensorCoordinates
import QICLean.Analysis.SupportProjectionOrder
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Analysis.WeightedProjection
import QICLean.Channel.FiniteProductOperatorSchmidt
import TNLean.Algebra.CommonKernelSpectralGap
import TNLean.Circuit.SupportedFunctionalCalculus
import TNLean.MPS.AreaLaw.ALVV.FrustrationFreeThreeRegion
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import TNLean.MPS.AreaLaw.ShortRegionViableFamily
import TNLean.MPS.AreaLaw.TwoWindowPolynomialRank

/-!
# The improving family for a frustration-free chain

This file proves the existence form of ALVV, arXiv:1602.08828v2, Theorem `t:aisff`,
lines 1580–1609. Take a nearest-neighbour chain with terms `0 ≤ h_i ≤ 1`, ground space
`G = ker H` and gap `γ`, and a prescribed interval `M`. Then there are `D²` operators `A_i` on
`M`, with `D = 2^{O(u³/g)}` for `u = 1 + log d + log (1/g)` and `g = min (γ, 1)`, and a `Δ`
with `D¹² Δ ≤ 10⁻⁵`, such that every `δ`-viable subspace `S` for `G` with `δ < 1` gives a
`Δ / (1 - δ)²`-viable span of the `A_i S`. Each `A_i` has operator Schmidt rank at most
`(d² + 4)^{ℓ² + 1}` at every cut inside `M`; this is the least open-boundary bond dimension of a
matrix product operator for `A_i`, and its logarithm is `O(u⁵/g²)`.

The construction follows the proof. Each term is replaced by its range projection (line 1457).
The three bulk regions around two windows of `2ℓ` bonds are replaced at once by
Definition 5.10 (lines 1597–1599). The Chebyshev filter of degree `ℓ²` of the replaced chain is
the spectral projector, and the operators `A_i` are slices of that filter over the complement
of `M`, so their interior ranks are those of the filter (line 1606). A short interval uses
configuration matrix units. The running-time clause is not formalized.

**Local fix (norm of the replaced chain and bond dimension):** The proof at line 1599 states
that the replaced chain has norm `O(1)`; its untruncated windows give norm up to `4ℓ + 6`, which
is the bound used here, with the printed choice `ℓ = Θ̃(γ⁻¹ log² d)`. The proof at line 1606
states bond dimension `O(d^k)`; the argument gives `(d² + 4)^{k+1}`, which still has the
theorem's form `2^{Õ(γ⁻² log⁵ d)}`. See `docs/paper-gaps/alvv16_ff_truncated_norm.tex`.

**Local fix (viability boundary):** As for Theorem `t:ais`, the improvement is stated for
viability error `δ < 1`, where `Δ / (1 - δ)²` is defined; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
-/

open scoped InnerProductSpace TensorProduct Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator
open Matrix

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw TNLean.Lattice

section Cuts

variable {L q m : ℕ}

private theorem coe_interval_subset_compl {c x y : ℕ} (hcx : c ≤ x) :
    (interval L x y : Set (Fin L)) ⊆ ((interval L 0 c)ᶜ : Finset (Fin L)) := by
  intro i hi
  simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe, mem_interval] at hi ⊢
  omega

private theorem coe_interval_subset_left {c x y : ℕ} (hyc : y ≤ c) :
    (interval L x y : Set (Fin L)) ⊆ (interval L 0 c : Finset (Fin L)) :=
  Finset.coe_subset.mpr (interval_mono (Nat.zero_le x) hyc)

/-- An operator supported on `[x, y)` lies on one side of the cut after the first `c` sites
when the interval ends by `c` or starts at or after `c`. -/
private theorem mem_supportedOperators_side {X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    {c x y : ℕ} (hX : X ∈ QuantumCircuit.supportedOperators q (interval L x y : Set (Fin L)))
    (hxy : y ≤ c ∨ c ≤ x) :
    X ∈ QuantumCircuit.supportedOperators q (interval L 0 c : Set (Fin L)) ∨
      X ∈ QuantumCircuit.supportedOperators q
        (((interval L 0 c)ᶜ : Finset (Fin L)) : Set (Fin L)) :=
  hxy.imp (fun h ↦ QuantumCircuit.supportedOperators_mono (coe_interval_subset_left h) hX)
    fun h ↦ QuantumCircuit.supportedOperators_mono (coe_interval_subset_compl h) hX

/-- A nearest-neighbour bond has operator Schmidt rank at most `q²` at every cut. -/
private theorem rank_bond_le {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hq : 1 ≤ q)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (i c : ℕ) :
    operatorSchmidtRank ((bondTermExtension h i).reindex (sheetSplit q (interval L 0 c))
      (sheetSplit q (interval L 0 c))) ≤ q ^ 2 := by
  rw [← operatorSchmidtRank_cutOperator_eq]
  exact ((bondTermExtension_supported hsupp i).operatorSchmidtRank_cutOperator_le_pow_card
    hq).trans (Nat.pow_le_pow_right hq ((card_interval_le _ _).trans (by omega)))

/-- A cut inside a window: the crossing bond carries the rank, every other term of the
three-region family lies on one side. -/
private theorem rank_window_cut_le {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hq : 1 ≤ q)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {a b ℓ c : ℕ} (hab : a + 2 * ℓ ≤ b)
    (hwin : (a + 1 ≤ c ∧ c ≤ a + 2 * ℓ) ∨ (b + 1 ≤ c ∧ c ≤ b + 2 * ℓ))
    (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) :
    operatorSchmidtRank ((Polynomial.aeval (∑ α, threeRegionFamily h a b ℓ α) P).reindex
        (sheetSplit q (interval L 0 c)) (sheetSplit q (interval L 0 c))) ≤
      (q ^ 2 + 2) ^ (k + 1) := by
  obtain ⟨hWL, hWR, hPL, hPM, hPR⟩ := threeRegionFamily_supported hq hsupp a b ℓ
  rcases hwin with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hB : operatorSchmidtRank ((threeRegionFamily h a b ℓ
        (Sum.inl (Sum.inl ⟨c - 1 - a, by omega⟩))).reindex (sheetSplit q (interval L 0 c))
        (sheetSplit q (interval L 0 c))) ≤ q ^ 2 := rank_bond_le hq hsupp (a + (c - 1 - a)) c
    refine operatorSchmidtRank_aeval_sum_le_pow_of_bulk (interval L 0 c)
      (threeRegionFamily h a b ℓ) (Sum.inl (Sum.inl ⟨c - 1 - a, by omega⟩)) ?_ hB k P hdeg
    rintro ((r | r) | j) hr
    · have hne : r.val ≠ c - 1 - a := fun h ↦
        hr (congrArg (fun x ↦ Sum.inl (Sum.inl x)) (Fin.ext h))
      exact mem_supportedOperators_side (hWL r) (by omega)
    · exact mem_supportedOperators_side (hWR r) (by omega)
    · fin_cases j
      · exact mem_supportedOperators_side hPL (by omega)
      · exact mem_supportedOperators_side hPM (by omega)
      · exact mem_supportedOperators_side hPR (by omega)
  · have hB : operatorSchmidtRank ((threeRegionFamily h a b ℓ
        (Sum.inl (Sum.inr ⟨c - 1 - b, by omega⟩))).reindex (sheetSplit q (interval L 0 c))
        (sheetSplit q (interval L 0 c))) ≤ q ^ 2 := rank_bond_le hq hsupp (b + (c - 1 - b)) c
    refine operatorSchmidtRank_aeval_sum_le_pow_of_bulk (interval L 0 c)
      (threeRegionFamily h a b ℓ) (Sum.inl (Sum.inr ⟨c - 1 - b, by omega⟩)) ?_ hB k P hdeg
    rintro ((r | r) | j) hr
    · exact mem_supportedOperators_side (hWL r) (by have := r.isLt; omega)
    · have hne : r.val ≠ c - 1 - b := fun h ↦
        hr (congrArg (fun x ↦ Sum.inl (Sum.inr x)) (Fin.ext h))
      exact mem_supportedOperators_side (hWR r) (by omega)
    · fin_cases j
      · exact mem_supportedOperators_side hPL (by omega)
      · exact mem_supportedOperators_side hPM (by omega)
      · exact mem_supportedOperators_side hPR (by omega)

/-- **Rank of the filter at every cut.** Every polynomial of degree at most `k` in the
three-region replacement has operator Schmidt rank at most `(q² + 4)^{k+1}` at every cut of the
chain. ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, item 4, lines 825–826, applied in
the proof of Theorem `t:aisff`, line 1606, with the regional rank `q² + 2` of
`rank_regionTermMatrix_le` and a crossing bond of rank `q²` in the windows. -/
theorem operatorSchmidtRank_aeval_threeRegion_cut_le
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {a b ℓ : ℕ} (hab : a + 2 * ℓ ≤ b)
    (k : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) (c : ℕ) :
    operatorSchmidtRank ((Polynomial.aeval (∑ α, threeRegionFamily h a b ℓ α) P).reindex
        (sheetSplit q (interval L 0 c)) (sheetSplit q (interval L 0 c))) ≤
      (q ^ 2 + 4) ^ (k + 1) := by
  classical
  obtain ⟨hWL, hWR, hPL, hPM, hPR⟩ := threeRegionFamily_supported hq hsupp a b ℓ
  have hreg (x y : ℕ) := rank_regionTermMatrix_le hq (bondTermExtension_supported hsupp) x y m c
  have hmono : ∀ B, B ≤ q ^ 2 + 2 → (B + 2) ^ (k + 1) ≤ (q ^ 2 + 4) ^ (k + 1) :=
    fun B hB ↦ Nat.pow_le_pow_left (by omega) _
  by_cases h1 : c ≤ a
  · convert (operatorSchmidtRank_aeval_two_window_left_cut_le _ hWL hWR hPM hPR (by omega) h1
      (hreg 0 a) k P hdeg).trans (hmono _ le_rfl)
  by_cases h2 : c ≤ a + 2 * ℓ
  · exact (rank_window_cut_le hq hsupp hab (Or.inl ⟨by omega, h2⟩) k P hdeg).trans
      (Nat.pow_le_pow_left (by omega) _)
  by_cases h3 : c ≤ b
  · convert (operatorSchmidtRank_aeval_two_window_middle_cut_le _ hWL hWR hPL hPR (by omega) h3
      (hreg (a + 2 * ℓ) b) k P hdeg).trans (hmono _ le_rfl)
  by_cases h4 : c ≤ b + 2 * ℓ
  · exact (rank_window_cut_le hq hsupp hab (Or.inr ⟨by omega, h4⟩) k P hdeg).trans
      (Nat.pow_le_pow_left (by omega) _)
  · convert (operatorSchmidtRank_aeval_two_window_right_cut_le _ hWL hWR hPL hPM (by omega)
      (by omega) (hreg (b + 2 * ℓ) m) k P hdeg).trans (hmono _ le_rfl)

/-- **Rank of the filter across the prescribed interval.** For `k = ℓ²`, the filter has
operator Schmidt rank at most `D² = (q ℓ²)^{44ℓ}` across `(J, Jᶜ)`, for every set of sites `J`
containing the effective region `[a + ℓ, b + ℓ + 1)` with a collar of at most `2ℓ` sites.
ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, item 5, lines 831–832, and
Proposition 5.7, lines 1311–1333, in the proof of Theorem `t:aisff`, line 1604. -/
theorem operatorSchmidtRank_aeval_threeRegion_region_le
    {h : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hq : 1 ≤ q)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) {a b ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hab : a + 2 * ℓ ≤ b)
    (hb : b + 2 * ℓ ≤ L - 1) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ ℓ ^ 2)
    (J : Finset (Fin L)) (hsub : interval L (a + ℓ) (b + ℓ + 1) ⊆ J)
    (hcollar : (J \ interval L (a + ℓ) (b + ℓ + 1)).card ≤ 2 * ℓ) :
    operatorSchmidtRank ((Polynomial.aeval (∑ α, threeRegionFamily h a b ℓ α) P).reindex
        (sheetSplit q J) (sheetSplit q J)) ≤ ((q * ℓ ^ 2) ^ (22 * ℓ)) ^ 2 := by
  classical
  obtain ⟨hWL, hWR, hPL, hPM, hPR⟩ := threeRegionFamily_supported hq hsupp a b ℓ
  set J0 := interval L (a + ℓ) (b + ℓ + 1) with hJ0
  have hk : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓ
  have htwo := operatorSchmidtRank_aeval_two_window_le_pow _ hWL hWR hPL hPM hPR hab hb hℓ
    (ℓ ^ 2) hk P hdeg 0
  have hchange := FiniteProduct.operatorSchmidtRank_splitEquiv_le q J0 J
    (Polynomial.aeval (∑ α, threeRegionFamily h a b ℓ α) P)
  have hsymm : symmDiff J0 J = J \ J0 := by
    rw [symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.sup_eq_union,
      Finset.empty_union]
  rw [hsymm] at hchange
  have hdiv : ℓ ^ 2 / (2 * ℓ) ≤ ℓ := Nat.div_le_of_le_mul (by nlinarith)
  set B := q * ℓ ^ 2 with hB
  have hqB : q ≤ B := by simpa only [hB, mul_one] using Nat.mul_le_mul_left q hk
  have hB1 : 1 ≤ B := hq.trans hqB
  have hJ0' : interval L (a + ℓ + (0 : Fin 2).val) (b + ℓ + 1) = J0 := by
    simp only [Fin.val_zero, Nat.add_zero, hJ0]
  rw [hJ0'] at htwo
  have htwo0 : operatorSchmidtRank ((Polynomial.aeval (∑ α, threeRegionFamily h a b ℓ α)
      P).reindex (sheetSplit q J0) (sheetSplit q J0)) ≤ B ^ (17 * (ℓ + ℓ ^ 2 / (2 * ℓ))) := by
    convert htwo
  have htwo' : operatorSchmidtRank ((Polynomial.aeval (∑ α, threeRegionFamily h a b ℓ α)
      P).reindex (sheetSplit q J0) (sheetSplit q J0)) ≤ B ^ (34 * ℓ) :=
    htwo0.trans (Nat.pow_le_pow_right hB1 (by omega))
  have hcol : q ^ (2 * (J \ J0).card) ≤ B ^ (4 * ℓ) :=
    (Nat.pow_le_pow_left hqB _).trans (Nat.pow_le_pow_right hB1 (by omega))
  calc _ ≤ q ^ (2 * (J \ J0).card) * operatorSchmidtRank
        ((Polynomial.aeval (∑ α, threeRegionFamily h a b ℓ α) P).reindex
          (sheetSplit q J0) (sheetSplit q J0)) := hchange
    _ ≤ B ^ (4 * ℓ) * B ^ (34 * ℓ) := Nat.mul_le_mul hcol htwo'
    _ ≤ (B ^ (22 * ℓ)) ^ 2 := by
      rw [← pow_add, ← pow_mul]
      exact Nat.pow_le_pow_right hB1 (by omega)

end Cuts

section Family

/-- The bond count on a short region fits the bound of the long-region filter. -/
private theorem sq_pow_le_bond (q ℓ : ℕ) (hℓ : 4 ≤ ℓ) :
    (q ^ (4 * ℓ)) ^ 2 ≤ (q ^ 2 + 4) ^ (ℓ ^ 2 + 1) := by
  calc (q ^ (4 * ℓ)) ^ 2 = (q ^ 2) ^ (4 * ℓ) := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (q ^ 2 + 4) ^ (4 * ℓ) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (q ^ 2 + 4) ^ (ℓ ^ 2 + 1) := Nat.pow_le_pow_right (by positivity) (by nlinarith)

/-- The logarithm of the bond-dimension bound is `O(u⁵ / g²)`, the form `2^{Õ(γ⁻² log⁵ d)}` of
ALVV, arXiv:1602.08828v2, Theorem `t:aisff`, line 1586. -/
private theorem log_bond_le (A : ℝ) (hA : 1 ≤ A) (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : 0 < g)
    (hg1 : g ≤ 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hupper : (ℓ : ℝ) ≤ (A + 1) * (1 + Real.log d + Real.log (1 / g)) ^ 2 / g) :
    Real.log (((d ^ 2 + 4) ^ (ℓ ^ 2 + 1) : ℕ) : ℝ) ≤
      4 * (A + 1) ^ 2 / g ^ 2 * (1 + Real.log d + Real.log (1 / g)) ^ 5 := by
  set u := 1 + Real.log d + Real.log (1 / g) with hu
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).2 hg1)
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hlog : Real.log ((d : ℝ) ^ 2 + 4) ≤ 2 * u := by
    have h4 : (d : ℝ) ^ 2 + 4 ≤ 2 * (d : ℝ) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < (d : ℝ) ^ 2 + 4 := by positivity
    calc Real.log ((d : ℝ) ^ 2 + 4) ≤ Real.log (2 * (d : ℝ) ^ 2) := Real.log_le_log hpos h4
      _ = Real.log 2 + 2 * Real.log d := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
      _ ≤ 2 * u := by
        have := Real.log_two_lt_d9
        rw [hu]
        linarith
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set X := (A + 1) * u ^ 2 / g with hX
  have hsq : ((ℓ : ℝ) ^ 2 + 1) ≤ 2 * X ^ 2 := by nlinarith
  have hcast : (((d ^ 2 + 4) ^ (ℓ ^ 2 + 1) : ℕ) : ℝ) = ((d : ℝ) ^ 2 + 4) ^ (ℓ ^ 2 + 1) := by
    push_cast
    ring
  rw [hcast, Real.log_pow]
  have hlog0 : 0 ≤ Real.log ((d : ℝ) ^ 2 + 4) := Real.log_nonneg (by nlinarith)
  calc ((ℓ ^ 2 + 1 : ℕ) : ℝ) * Real.log ((d : ℝ) ^ 2 + 4) ≤ (2 * X ^ 2) * (2 * u) := by
        push_cast
        exact mul_le_mul hsq hlog hlog0 (by positivity)
    _ = 4 * (A + 1) ^ 2 / g ^ 2 * u ^ 5 := by
        rw [hX]
        field_simp
        ring

/-- A polynomial commutes with conjugation by a linear isometric equivalence. -/
private theorem aeval_conj_linearIsometryEquiv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (Tm : E ≃ₗᵢ[ℂ] F) (X : E →L[ℂ] E) (Q : Polynomial ℂ) :
    Polynomial.aeval (Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L X ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap) Q =
      Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L Polynomial.aeval X Q ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap :=
  Polynomial.aeval_algHom_apply
    Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom X Q

/-- A polynomial commutes with the Euclidean operator of a matrix. -/
private theorem aeval_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (Q : Polynomial ℂ) :
    Polynomial.aeval (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) X) Q =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) (Polynomial.aeval X Q) :=
  Polynomial.aeval_algHom_apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)).toAlgEquiv.toAlgHom X Q

/-- The squared Chebyshev contraction of the long-interval family, in the form of the scalar
parameter budget. -/
private theorem chebyshev_contraction_eq (ℓ : ℕ) (g : ℝ) (hℓ : 1 ≤ ℓ) :
    (2 * Real.exp (-2 * ((ℓ ^ 2 : ℕ) : ℝ) * Real.sqrt ((g / 20 - 0) / (10 * ℓ - 0)))) ^ 2 =
      4 * Real.exp (-(4 * (ℓ : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / (160 * ℓ)))) := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have harg : (g / 20 - 0) / (10 * (ℓ : ℝ) - 0) = (4 * g / 5) / (160 * ℓ) := by
    field_simp
    ring
  rw [harg, mul_pow, ← Real.exp_nat_mul]
  push_cast
  ring_nf

set_option maxHeartbeats 400000 in
-- The long case unfolds the tensor coordinates of the middle region several times.
/-- The improving family on an interval longer than `4ℓ`. ALVV, arXiv:1602.08828v2, proof of
Theorem `t:aisff`, lines 1592–1607: the three-region replacement, its Chebyshev filter of
degree `ℓ²`, and the slices of the filter over the complement of the interval. -/
private theorem exists_long_frustrationFree_family
    (L q p r ℓ a b d : ℕ) (hqd : q = d) (hq : 2 ≤ q) (hell : 1 ≤ ℓ) (hab : a + 2 * ℓ ≤ b)
    (hb : b + 2 * ℓ ≤ L - 1) (hsub : interval L (a + ℓ) (b + ℓ + 1) ⊆ interval L p r)
    (hcollar : (interval L p r \ interval L (a + ℓ) (b + ℓ + 1)).card ≤ 2 * ℓ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (hh : ∀ i, IsStarProjection (h i)) (g : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hgap : ∀ y ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ,
      g * ‖y‖ ^ 2 ≤ Complex.re ⟪y, chainOperator h y⟫_ℂ)
    (G₀ : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (hG₀ : LinearMap.ker (chainOperator h).toLinearMap = G₀)
    (htrade : ∀ R : ℝ, 0 < R → R ≤ 2 * 80 * (ℓ : ℝ) →
      ((((d * ℓ ^ 2) ^ (22 * ℓ) : ℕ) : ℝ)) ^ 12 *
        (4 * Real.exp (-(4 * (ℓ : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R)))) ≤ 1 / 100000) :
    let D : ℕ := (d * ℓ ^ 2) ^ (22 * ℓ)
    let J := interval L p r
    let tau := (sheetSplit q J).trans (Equiv.prodComm (J → Fin q) (↥Jᶜ → Fin q))
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (↥Jᶜ → Fin q) ℂ).tensorProduct
      (EuclideanSpace.basisFun (J → Fin q) ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (↥Jᶜ → Fin q)) (EuclideanSpace ℂ (J → Fin q)))
    let EM := EuclideanSpace ℂ (J → Fin q)
    let EE := EuclideanSpace ℂ (↥Jᶜ → Fin q)
    let G := G₀.map
      (Tm.toLinearEquiv : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] EM ⊗[ℂ] EE)
    let cut : ℕ → Finset ↥J := fun c ↦
      Finset.univ.filter fun v : ↥J ↦ (v : Fin L) ∈ interval L 0 c
    ∃ (W : Fin (D ^ 2) → Matrix (J → Fin q) (J → Fin q) ℂ) (Δ : ℝ),
      0 < Δ ∧ (D : ℝ) ^ 12 * Δ ≤ 1 / 100000 ∧
      (∀ j c, operatorSchmidtRank ((W j).reindex (sheetSplit q (cut c))
        (sheetSplit q (cut c))) ≤ (d ^ 2 + 4) ^ (ℓ ^ 2 + 1)) ∧
      ∀ (S : Submodule ℂ EM) (δ : ℝ), Submodule.IsViable (F := EE) δ S G → δ < 1 →
        Submodule.IsViable (F := EE) (Δ / (1 - δ) ^ 2)
          (⨆ j, S.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j) :
            EM →ₗ[ℂ] EM)) G := by
  subst hqd hG₀
  intro D J tau U Phi Tm EM EE G cut
  classical
  have hq1 : 1 ≤ q := by omega
  set Ht : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    ∑ α, threeRegionFamily h a b ℓ α
  set C := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
  have hpos : (C Ht).IsPositive := isPositive_toEuclideanCLM_threeRegion hq1 hh hs a b ℓ
  have hsymC : (Matrix.toEuclideanLin Ht).IsSymmetric := hpos.isSelfAdjoint.isSymmetric
  have hHerm : Ht.IsHermitian := Matrix.isSymmetric_toEuclideanLin_iff.mp hsymC
  set v := hHerm.eigenvectorBasis
  set lam := hHerm.eigenvalues
  have hv : ∀ i, Ht.toEuclideanLin (v i) = (lam i : ℂ) • v i :=
    hHerm.toEuclideanLin_eigenvectorBasis
  have hvC : ∀ i, C Ht (v i) = (lam i : ℂ) • v i := hv
  have hker := ker_threeRegion hq1 hh hs a b ℓ
  have hlam_eq : ∀ i, lam i = Complex.re ⟪v i, C Ht (v i)⟫_ℂ := by
    intro i
    rw [hvC, inner_smul_right, inner_self_eq_norm_sq_to_K, v.orthonormal.norm_eq_one i]
    simp
  have hlam_nonneg : ∀ i, 0 ≤ lam i := fun i ↦ by
    rw [hlam_eq]
    exact hpos.re_inner_nonneg_right (v i)
  have hlam_gap : ∀ i, 0 < lam i → g / 15 ≤ lam i := by
    intro i hi
    have hmem : v i ∈ (LinearMap.ker (Matrix.toEuclideanLin Ht))ᗮ := by
      rw [LinearMap.orthogonal_ker, hsymC.adjoint_eq]
      refine ⟨(lam i : ℂ)⁻¹ • v i, ?_⟩
      have hne : (lam i : ℂ) ≠ 0 := by exact_mod_cast hi.ne'
      change C Ht ((lam i : ℂ)⁻¹ • v i) = v i
      rw [map_smul, hvC, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hmem' : v i ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ := by
      rw [← hker]
      exact hmem
    have h3 := threeRegion_gap hq1 hh hs hg hgap hab hb (v.orthonormal.norm_eq_one i) hmem'
    rw [← hlam_eq] at h3
    have h15 := gap_ratio_le hg hg1
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at h15
    exact h15.trans h3
  have hcluster : Submodule.spectralSpanLE v lam 0 = Submodule.spectralSpanLE v lam (g / 20) := by
    ext x
    simp only [Submodule.mem_spectralSpanLE_iff]
    constructor
    · intro hx j hj
      exact hx j (lt_trans (by positivity) hj)
    · intro hx j hj
      exact hx j (by linarith [hlam_gap j hj])
  have hspan0 : Submodule.spectralSpanLE v lam 0 =
      LinearMap.ker (chainOperator h).toLinearMap := by
    rw [← hker]
    ext x
    rw [Submodule.mem_spectralSpanLE_iff, LinearMap.mem_ker]
    have hrepr (j) := OrthonormalBasis.repr_apply_of_eigen v lam (H := Ht.toEuclideanLin) hv x j
    constructor
    · intro hx
      apply v.repr.injective
      ext j
      change v.repr (Ht.toEuclideanLin x) j = v.repr 0 j
      rw [hrepr, map_zero]
      by_cases hj : 0 < lam j
      · simp [hx j hj]
      · have : lam j = 0 := le_antisymm (not_lt.mp hj) (hlam_nonneg j)
        simp [this]
    · intro hx j hj
      have h0 : v.repr (Ht.toEuclideanLin x) j = 0 := by
        rw [show Ht.toEuclideanLin x = 0 from hx, map_zero]
        rfl
      rw [hrepr] at h0
      have hne : (lam j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
      exact (mul_eq_zero.mp h0).resolve_left hne
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hell
  have hnorm : ‖Ht‖ ≤ 10 * (ℓ : ℝ) := (norm_threeRegion_le hq1 hh hs a b ℓ).trans (by linarith)
  obtain ⟨hK, hgapK, hupperK, hmapK⟩ :=
    exists_canonical_isometric_spectral_data Ht hHerm v lam hv 0 (g / 20) (10 * ℓ)
      hcluster hnorm Tm
  let Hm : EM ⊗[ℂ] EE →L[ℂ] EM ⊗[ℂ] EE :=
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L C Ht ∘L
      Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hHm : (Hm : EM ⊗[ℂ] EE →ₗ[ℂ] EM ⊗[ℂ] EE).IsSymmetric := hK
  obtain ⟨p₀, hpdeg, -, hproj⟩ := Submodule.exists_isSpectralProjector_chebyshev Hm hHm rfl
    (ℓ ^ 2) (a := 0) (b := g / 20) (u := 10 * ℓ) (by positivity) (by linarith) hupperK
  obtain ⟨hKT, hKTo, hlow, hhigh⟩ := hproj.contract hgapK
  have hT : Submodule.span ℂ (hHm.eigenvectorBasis rfl '' {j | hHm.eigenvalues rfl j ≤ 0}) =
      G := by
    have h0 := (hmapK 0).symm
    rw [hspan0] at h0
    exact h0
  rw [hT] at hKT hKTo hlow hhigh
  set Qc := p₀.map (algebraMap ℝ ℂ)
  have hQdeg : Qc.natDegree ≤ ℓ ^ 2 := Polynomial.natDegree_map_le.trans hpdeg.le
  set P := Polynomial.aeval Ht Qc
  have hfilter : Polynomial.aeval Hm Qc =
      Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L C P ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [aeval_conj_linearIsometryEquiv, aeval_toEuclideanCLM]
  obtain ⟨N, e, M, hN, hdec⟩ := exists_regionalSlice_decomposition J P
  let slice : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ := fun r ↦
    regionalSlice J P (e r).1 (e r).2
  have hconj := Matrix.toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum tau M slice P hdec
  have hKdec : Polynomial.aeval Hm Qc = ∑ r, TensorProduct.mapL
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (slice r))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥Jᶜ → Fin q) (M r)) := hfilter.trans hconj
  have hNle : N ≤ D ^ 2 := by
    rw [hN]
    exact operatorSchmidtRank_aeval_threeRegion_region_le hq1 hs hell hab hb Qc hQdeg J hsub
      hcollar
  obtain ⟨f, B, hBf, hBzero, hspanB⟩ := Submodule.exists_clm_family_extension_of_card_le
    (by simpa only [Fintype.card_fin] using hNle)
    (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (slice r))
  refine ⟨fun j ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q)).symm (B j),
    (2 * Real.exp (-2 * ((ℓ ^ 2 : ℕ) : ℝ) * Real.sqrt ((g / 20 - 0) / (10 * ℓ - 0)))) ^ 2,
    by positivity, ?_, ?_, ?_⟩
  · rw [chebyshev_contraction_eq ℓ g hell]
    exact htrade (160 * ℓ) (mul_pos (by norm_num) (by exact_mod_cast hell))
      (le_of_eq (by ring))
  · intro j c
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      simp only [hBf, StarAlgEquiv.symm_apply_apply]
      exact (operatorSchmidtRank_regionalSlice_le J (interval L 0 c) P _ _).trans
        (operatorSchmidtRank_aeval_threeRegion_cut_le hq1 hs hab (ℓ ^ 2) Qc hQdeg c)
    · simp only [hBzero j hj, map_zero, Matrix.reindex_apply, Matrix.submatrix_zero]
      exact (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition (r := 0)
        ⟨Fin.elim0, Fin.elim0, by simp⟩).trans (Nat.zero_le _)
  · intro S δ hS hδ
    have hgrow := (Submodule.IsViable.map_of_tensor_decomposition (M := EM) (R := EE)
      (T := G) (K := Polynomial.aeval Hm Qc) hS
      (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (slice r))
      (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥Jᶜ → Fin q) (M r))
      hKdec hδ (sq_nonneg _) hKT hKTo hlow hhigh).2
    have hspan : (⨆ j, S.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q)
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q)).symm (B j)) : EM →ₗ[ℂ] EM)) =
        ⨆ r, S.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (slice r) :
          EM →ₗ[ℂ] EM) := by
      simpa only [StarAlgEquiv.apply_symm_apply] using hspanB S
    rw [hspan]
    exact hgrow

/-- A family that improves every viable subspace when the regional space has dimension at most
one: the identity, extended by zero. -/
private theorem exists_small_space_family {EM EE : Type*} [NormedAddCommGroup EM]
    [InnerProductSpace ℂ EM] [FiniteDimensional ℂ EM] [NormedAddCommGroup EE]
    [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (hEM : Module.finrank ℂ EM ≤ 1) {M : ℕ} (hM : 1 ≤ M) :
    ∃ B : Fin M → EM →L[ℂ] EM, ∀ (T : Submodule ℂ (EM ⊗[ℂ] EE)) (S : Submodule ℂ EM)
      (δ Δ : ℝ), Submodule.IsViable δ S T → δ < 1 → 0 ≤ Δ →
        Submodule.IsViable Δ (⨆ j, S.map (B j : EM →ₗ[ℂ] EM)) T := by
  obtain ⟨-, B, -, -, hspan⟩ := Submodule.exists_clm_family_extension_of_card_le (ι := Unit)
    (by simpa only [Fintype.card_unit] using hM) (fun _ ↦ (1 : EM →L[ℂ] EM))
  refine ⟨B, fun T S δ Δ hS hδ hΔ ↦ ?_⟩
  by_cases hT : T = ⊥
  · subst hT
    unfold Submodule.IsViable
    apply Submodule.isCloseTo_iff.mpr
    intro v hv
    have hv0 : v = 0 := by simpa using hv
    subst hv0
    simp
  · have hS0 : S ≠ ⊥ := Submodule.isViable_ne_bot_of_target_ne_bot hS hδ hT
    have hStop : S = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 : 1 ≤ Module.finrank ℂ S := Submodule.one_le_finrank_iff.mpr hS0
      have h2 := Submodule.finrank_le S
      omega
    have htop : (⨆ j, S.map (B j : EM →ₗ[ℂ] EM)) = ⊤ := by
      rw [hspan S, hStop]
      simp only [ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, Submodule.map_id,
        iSup_const]
    rw [htop]
    exact Submodule.isViable_top Δ hΔ T

/-- The improving family for projector terms with a prescribed kernel; the range-projection
reduction of ALVV, arXiv:1602.08828v2, line 1457, is applied in
`exists_frustrationFree_improving_family`. -/
private theorem exists_improving_family_core :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
          (interval L i.val (i.val + 2))) →
        (∀ i, IsStarProjection (h i)) →
      ∀ (γ : ℝ) (G₀ : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))), 0 < γ →
        LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (∑ i, h i)).toLinearMap = G₀ →
        (∀ y ∈ G₀ᗮ, γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y, Matrix.toEuclideanCLM (𝕜 := ℂ)
          (n := Fin L → Fin q) (∑ i, h i) y⟫_ℂ) →
      let g := min γ 1
      let d := max q 2
      let u : ℝ := 1 + Real.log (d : ℝ) + Real.log (1 / g)
      let ℓ : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (d * ℓ ^ 2) ^ (22 * ℓ)
      let J := interval L p r
      let tau := (sheetSplit q J).trans (Equiv.prodComm (J → Fin q) (↥Jᶜ → Fin q))
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (↥Jᶜ → Fin q) ℂ).tensorProduct
        (EuclideanSpace.basisFun (J → Fin q) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (↥Jᶜ → Fin q)) (EuclideanSpace ℂ (J → Fin q)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ (↥Jᶜ → Fin q)
      let G := G₀.map (Tm.toLinearEquiv :
        EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] EM ⊗[ℂ] EE)
      let cut : ℕ → Finset ↥J := fun c ↦
        Finset.univ.filter fun v : ↥J ↦ (v : Fin L) ∈ interval L 0 c
      Real.log (D : ℝ) ≤ 22 * (A + 1) * (6 + 2 * Real.log (A + 1)) / g * u ^ 3 ∧
      Real.log (((d ^ 2 + 4) ^ (ℓ ^ 2 + 1) : ℕ) : ℝ) ≤ 4 * (A + 1) ^ 2 / g ^ 2 * u ^ 5 ∧
      ∃ (W : Fin (D ^ 2) → Matrix (J → Fin q) (J → Fin q) ℂ) (Δ : ℝ),
        0 < Δ ∧ (D : ℝ) ^ 12 * Δ ≤ 1 / 100000 ∧
        (∀ j c, operatorSchmidtRank ((W j).reindex (sheetSplit q (cut c))
          (sheetSplit q (cut c))) ≤ (d ^ 2 + 4) ^ (ℓ ^ 2 + 1)) ∧
        ∀ (S : Submodule ℂ EM) (δ : ℝ), Submodule.IsViable (F := EE) δ S G → δ < 1 →
          Submodule.IsViable (F := EE) (Δ / (1 - δ) ^ 2)
            (⨆ j, S.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j) :
              EM →ₗ[ℂ] EM)) G := by
  obtain ⟨A, hA, hA21, -, -, hall⟩ := Real.exists_dg_scalar_parameters 80 0 (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro L q p r hpr hrL h hs hh γ G₀ hγ hG₀ hgap g d u ℓ D J tau U Phi Tm EM EE G cut
  have hd : 2 ≤ d := le_max_right q 2
  have hg : 0 < g := lt_min hγ one_pos
  have hg1 : g ≤ 1 := min_le_right γ 1
  obtain ⟨-, hupper, hellA, -, hlogD, htrade, -⟩ := hall d g hd hg hg1
  have hell : 21 ≤ ℓ := by exact_mod_cast hA21.trans hellA
  refine ⟨hlogD, log_bond_le A hA d hd g hg hg1 ℓ (by omega) hupper, ?_⟩
  have hDpos : 0 < D := pow_pos (Nat.mul_pos (by omega) (pow_pos (by omega) 2)) _
  have hcutcard : ∀ c, (cut c).card ≤ J.card := fun c ↦
    (Finset.card_filter_le _ _).trans (by simp)
  have hsmall : ∀ (X : Matrix (J → Fin q) (J → Fin q) ℂ) c,
      operatorSchmidtRank (X.reindex (sheetSplit q (cut c)) (sheetSplit q (cut c))) ≤
        (q ^ (cut c).card) ^ 2 := by
    intro X c
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using
      operatorSchmidtRank_le_card_sq (X.reindex (sheetSplit q (cut c)) (sheetSplit q (cut c)))
  have hbond1 : 1 ≤ (d ^ 2 + 4) ^ (ℓ ^ 2 + 1) := Nat.one_le_pow _ _ (by positivity)
  by_cases hq1 : q ≤ 1
  · have hEM : Module.finrank ℂ EM ≤ 1 := by
      change Module.finrank ℂ (EuclideanSpace ℂ (J → Fin q)) ≤ 1
      rw [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      exact pow_le_one₀ (Nat.zero_le _) hq1
    obtain ⟨B, hB⟩ := exists_small_space_family (EE := EE) hEM (M := D ^ 2)
      (Nat.one_le_pow _ _ hDpos)
    have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
    refine ⟨fun j ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q)).symm (B j),
      1 / (100000 * (D : ℝ) ^ 12), by positivity, ?_, ?_, ?_⟩
    · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    · intro j c
      refine (hsmall _ c).trans (le_trans ?_ hbond1)
      exact pow_le_one₀ (Nat.zero_le _) (pow_le_one₀ (Nat.zero_le _) hq1)
    · intro S δ hS hδ
      simpa only [StarAlgEquiv.apply_symm_apply] using hB G S δ _ hS hδ (by positivity)
  have hq : 2 ≤ q := by omega
  have hdq : d = q := max_eq_left hq
  by_cases hshort : r - p ≤ 4 * ℓ
  · have hJ : J.card ≤ 4 * ℓ := (card_interval_le p r).trans hshort
    obtain ⟨Af, Δ, hΔ, hbudget, himprove⟩ :=
      exists_short_actual_region_improving_family_of_count_base (F := EE) L q d ℓ J hq
        (le_max_left q 2) (by omega) hJ
    refine ⟨fun j ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q)).symm (Af j), Δ, hΔ,
      hbudget, ?_, ?_⟩
    · intro j c
      refine (hsmall _ c).trans ?_
      calc (q ^ (cut c).card) ^ 2 ≤ (q ^ (4 * ℓ)) ^ 2 :=
            Nat.pow_le_pow_left (Nat.pow_le_pow_right (by omega) ((hcutcard c).trans hJ)) 2
        _ ≤ (q ^ 2 + 4) ^ (ℓ ^ 2 + 1) := sq_pow_le_bond q ℓ (by omega)
        _ = (d ^ 2 + 4) ^ (ℓ ^ 2 + 1) := by rw [hdq]
    · intro S δ hS hδ
      simpa only [StarAlgEquiv.apply_symm_apply] using himprove G S δ hS hδ
  · have hlong : 4 * ℓ < r - p := by omega
    obtain ⟨-, -, hab, hb, -, -, -, -, -, -, -, hsub, hcollar⟩ :=
      inward_effective_cuts L ℓ p r (by omega) hpr hrL hlong
    have hker : LinearMap.ker (chainOperator h).toLinearMap = G₀ := by
      rw [chainOperator_eq_toEuclideanCLM_sum, hG₀]
    have hgapC : ∀ y ∈ (LinearMap.ker (chainOperator h).toLinearMap)ᗮ,
        g * ‖y‖ ^ 2 ≤ Complex.re ⟪y, chainOperator h y⟫_ℂ := by
      intro y hy
      rw [hker] at hy
      rw [chainOperator_eq_toEuclideanCLM_sum]
      have h1 := hgap y hy
      have h2 : g * ‖y‖ ^ 2 ≤ γ * ‖y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left γ 1) (sq_nonneg _)
      exact h2.trans h1
    obtain ⟨W, Δ, hΔ, hbudget, hbond, himprove⟩ := exists_long_frustrationFree_family L q p r ℓ
      _ _ d hdq.symm hq (by omega) hab hb hsub hcollar h hs hh g hg hg1 hgapC G₀ hker htrade
    exact ⟨W, Δ, hΔ, hbudget, hbond, himprove⟩

/-- **Efficient improving family for a frustration-free chain, existence form.** Arad, Landau,
Vazirani and Vidick, arXiv:1602.08828v2, Theorem `t:aisff`, lines 1580–1609.

Let `H = ∑ hᵢ` be a nearest-neighbour chain of `L` sites of local dimension `q`, with
`0 ≤ hᵢ ≤ 1` (Assumption (FF), lines 267–286), and let `γ > 0` bound its quadratic form from
below on the orthogonal complement of its ground space `ker H`. Fix an interval `M = [p, r)`.
There is one universal constant `A ≥ 1`, chosen before all data, such that with `g = min (γ, 1)`,
`d = max (q, 2)`, `u = 1 + log d + log (1/g)`, `ℓ = ⌈A u² / g⌉` and `D = (d ℓ²)^{22ℓ}`:

* `log D ≤ 22 (A + 1)(6 + 2 log (A + 1)) u³ / g`, the source's `D = 2^{Õ(γ⁻¹ log³ d)}`;
* there are `D²` operators `W j` on `M` and `Δ > 0` with `D¹² Δ ≤ 10⁻⁵`, such that every
  subspace `S` of the space of `M` that is `δ`-viable for the ground space, with `δ < 1`, gives a
  `Δ / (1 - δ)²`-viable span of the `W j S`;
* at every cut of `M`, each `W j` has operator Schmidt rank at most `(d² + 4)^{ℓ² + 1}`, the
  least bond dimension of an open-boundary matrix product operator for `W j` at that cut, and
  `log ((d² + 4)^{ℓ² + 1}) ≤ 4 (A + 1)² u⁵ / g²`, the source's `2^{Õ(γ⁻² log⁵ d)}`.

Uniqueness of the ground state and frustration freeness are not needed; with a unique ground
state `Γ` the ground space is the source's `span {Γ}`. The terms are not assumed to be
projectors: each is replaced by its range projection, as at line 1457. The formula uses
`d = max (q, 2)` so that it is meaningful for every local dimension; for `q ≥ 2` it is `q`.
The running-time clause is not formalized.

**Local fix (viability boundary):** the improvement is stated for `δ < 1`, where
`Δ / (1 - δ)²` is defined; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf. -/
theorem exists_frustrationFree_improving_family :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
          (interval L i.val (i.val + 2))) →
        (∀ i, 0 ≤ h i) → (∀ i, h i ≤ 1) →
      ∀ γ : ℝ, 0 < γ →
      let H := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i)
      (∀ y ∈ (LinearMap.ker H.toLinearMap)ᗮ, γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y, H y⟫_ℂ) →
      let g := min γ 1
      let d := max q 2
      let u : ℝ := 1 + Real.log (d : ℝ) + Real.log (1 / g)
      let ℓ : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (d * ℓ ^ 2) ^ (22 * ℓ)
      let J := interval L p r
      let tau := (sheetSplit q J).trans (Equiv.prodComm (J → Fin q) (↥Jᶜ → Fin q))
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (↥Jᶜ → Fin q) ℂ).tensorProduct
        (EuclideanSpace.basisFun (J → Fin q) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (↥Jᶜ → Fin q)) (EuclideanSpace ℂ (J → Fin q)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ (↥Jᶜ → Fin q)
      let G := (LinearMap.ker H.toLinearMap).map (Tm.toLinearEquiv :
        EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] EM ⊗[ℂ] EE)
      let cut : ℕ → Finset ↥J := fun c ↦
        Finset.univ.filter fun v : ↥J ↦ (v : Fin L) ∈ interval L 0 c
      Real.log (D : ℝ) ≤ 22 * (A + 1) * (6 + 2 * Real.log (A + 1)) / g * u ^ 3 ∧
      Real.log (((d ^ 2 + 4) ^ (ℓ ^ 2 + 1) : ℕ) : ℝ) ≤ 4 * (A + 1) ^ 2 / g ^ 2 * u ^ 5 ∧
      ∃ (W : Fin (D ^ 2) → Matrix (J → Fin q) (J → Fin q) ℂ) (Δ : ℝ),
        0 < Δ ∧ (D : ℝ) ^ 12 * Δ ≤ 1 / 100000 ∧
        (∀ j c, operatorSchmidtRank ((W j).reindex (sheetSplit q (cut c))
          (sheetSplit q (cut c))) ≤ (d ^ 2 + 4) ^ (ℓ ^ 2 + 1)) ∧
        ∀ (S : Submodule ℂ EM) (δ : ℝ), Submodule.IsViable (F := EE) δ S G → δ < 1 →
          Submodule.IsViable (F := EE) (Δ / (1 - δ) ^ 2)
            (⨆ j, S.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j) :
              EM →ₗ[ℂ] EM)) G := by
  obtain ⟨A, hA, hcore⟩ := exists_improving_family_core
  refine ⟨A, hA, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 γ hγ H hgap
  have hpsd (i : Fin (L - 1)) : (h i).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (h0 i)
  let P : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun i ↦ (hpsd i).supportProj
  have hPp : ∀ i, IsStarProjection (P i) := fun i ↦
    (hpsd i).isHermitian.isStarProjection_supportProj
  have hPs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (P i)
      (interval L i.val (i.val + 2)) := by
    intro i
    have hmem := QuantumCircuit.cfc_mem_supportedOperators
      (fun x : ℝ ↦ if x ≠ 0 then 1 else 0)
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i))
    rw [← (hpsd i).isHermitian.supportProj_eq_cfc] at hmem
    exact QuantumCircuit.isSupportedOn_of_mem_supportedOperators hmem
  have hzero (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (x : EuclideanSpace ℂ (Fin L → Fin q)) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) X x = 0 ↔ X *ᵥ x.ofLp = 0 := by
    rw [← WithLp.ofLp_eq_zero, Matrix.ofLp_toEuclideanCLM]
  have hker : LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (∑ i, P i)).toLinearMap = LinearMap.ker H.toLinearMap := by
    ext x
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, H]
    rw [hzero, hzero]
    exact Matrix.PosSemidef.sum_supportProj_mulVec_eq_zero_iff hpsd x.ofLp
  have hle : (∑ i, h i) ≤ ∑ i, P i := Finset.sum_le_sum fun i _ ↦
    (hpsd i).le_supportProj_of_norm_le_one
      ((CStarAlgebra.norm_le_one_iff_of_nonneg (h i) (h0 i)).mpr (h1 i))
  have hform (y : EuclideanSpace ℂ (Fin L → Fin q)) :
      Complex.re ⟪y, H y⟫_ℂ ≤ Complex.re ⟪y, Matrix.toEuclideanCLM (𝕜 := ℂ)
        (n := Fin L → Fin q) (∑ i, P i) y⟫_ℂ := by
    have hpos := ContinuousLinearMap.le_def.mp (Matrix.toEuclideanCLM_le_of_le hle)
    have := hpos.re_inner_nonneg_right y
    simp only [_root_.sub_apply, inner_sub_right, map_sub] at this
    change 0 ≤ RCLike.re _ - RCLike.re _ at this
    simp only [RCLike.re_to_complex] at this
    linarith
  exact hcore L q p r hpr hrL P hPs hPp γ (LinearMap.ker H.toLinearMap) hγ hker
    (fun y hy ↦ (hgap y hy).trans (hform y))

end Family

end TNLean.MPS.AreaLaw.ALVV
