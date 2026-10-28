/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hamiltonian
import TNLean.MPS.AreaLaw.OpenMPS
import TNLean.Algebra.ToEuclideanLinApply
import TNLean.MPS.AreaLaw.Hastings.PartCommutators
import QICLean.Analysis.PhysicalPowerFilterLowerGap
import QICLean.Algebra.FiniteSumPowers
import QICLean.Entropy.SupportedOperatorSchmidtWords

/-!
# The power approximate ground-state projector on a nearest-neighbour chain

Landau, Vazirani and Vidick consider `H = ∑_{i=1}^{n-1} H_i` on `n` qudits of dimension `d`,
with `H_i` acting on the sites `{i, i + 1}` and `0 ≤ H_i ≤ 1`, a unique ground state `Γ` of
energy `ε₀` and gap `ε = ε₁ - ε₀`. Their approximate ground-state projector is
`A = ((1 - H/n) / (1 - ε₀/n))^m`. Here the chain has `L` sites `0, …, L - 1` with local
dimension `q`, and the bonds are indexed by `Fin (L - 1)`: bond `i` acts on the sites `i` and
`i + 1`.

The spectral statements are the chain form of the QICLean estimates for a finite sum of positive
contractions: `A` is positive semidefinite, has norm one and fixes `Γ`; on unit vectors
orthogonal to `Γ` its quadratic form is at most `((1 - ε₁/n) / (1 - ε₀/n))^m`; and
`‖A - |Γ⟩⟨Γ|‖ ≤ η` as soon as `m ≥ ((n - ε₀)/ε) log (1/η)`. The gap enters only through the
inequality `H - ε₀ ≥ ε (1 - |Γ⟩⟨Γ|)`, so `ε` may be any positive lower bound on the gap.

The expansion writes `A` as `C^m n^{-m} ∑_I P_I` over the words `I` of length `m` in the
letters `P_i = 1 - H_i`, and the rank estimate bounds the operator Schmidt rank of `P_I` across
the cut between the sites `i` and `i + 1` by `q^{2k}` when `P_i` occurs at most `k` times in `I`.

**Local fix (padding letter):** the printed expansion `eq:a-exp` sums over words in the
`n` letters `{1, …, n}` although `H` has only `n - 1` terms. It is read with `H_n = 0`, so
`P_n = 1`; then `∑_{i=1}^n P_i = n - H` and the identity is exact. Here the letters are indexed
by `Fin L`, and the letter `L - 1` is the identity. The normalization divides by the number of
sites, so the spectral statements and the expansion take `0 < L`, the source's chains of
`n ≥ 1` qudits. Documented in `docs/paper-gaps/lvv13_power_expansion_padding.tex`.

## Main definitions

* `TNLean.MPS.AreaLaw.bondSupport`: the support `{i, i + 1}` of bond `i`.
* `TNLean.MPS.AreaLaw.ChainHamiltonian.ofBonds`: a family of bond terms as a range-one chain
  Hamiltonian, so that the viable-set results apply to it.
* `TNLean.MPS.AreaLaw.paddedBond`, `TNLean.MPS.AreaLaw.bondComplement`,
  `TNLean.MPS.AreaLaw.bondComplementWord`: the bond terms padded by `H_{L-1} = 0`, the letters
  `P_i = 1 - H_i` and the words `P_I`.
* `TNLean.MPS.AreaLaw.powerProjector`: the operator `((1 - H/n) / (1 - ε₀/n))^m`.

## Main results

* `TNLean.MPS.AreaLaw.posSemidef_powerProjector`, `TNLean.MPS.AreaLaw.norm_powerProjector`,
  `TNLean.MPS.AreaLaw.powerProjector_apply_ground`: positivity, norm one and `AΓ = Γ`.
* `TNLean.MPS.AreaLaw.norm_inner_powerProjector_le`: equation `e:cutdown`.
* `TNLean.MPS.AreaLaw.norm_powerProjector_sub_le`: the logarithmic choice of `m`.
* `TNLean.MPS.AreaLaw.powerProjector_eq_sum_bondComplementWord`: equation `eq:a-exp`.
* `TNLean.MPS.AreaLaw.operatorSchmidtRank_cutOperator_bondComplementWord_le`: the rank bound
  behind equation `e:decomp`.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`: the
  Hamiltonian and its gap, lines 209–216 and 283–290; the decomposition `e:decomp`, lines
  584–588; the operator `A`, lines 599–600; its properties and `e:cutdown`, lines 602–604; the
  expansion `eq:a-exp`, lines 606–609.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-! ### Bond terms as a range-one chain Hamiltonian -/

/-- The support `{i, i + 1}` of the bond `i` of the chain of `L` sites. -/
def bondSupport (i : Fin (L - 1)) : ChainSupport L 1 :=
  ⟨interval L i (i + 2), ⟨⟨i, by omega⟩, mem_interval.mpr ⟨le_rfl, by simp⟩⟩,
    fun x hx y hy ↦ by
      rw [mem_interval] at hx hy
      omega⟩

/-- Distinct bonds have distinct supports. -/
theorem bondSupport_injective : Function.Injective (bondSupport (L := L)) := by
  intro i j hij
  have hi : (⟨i, by omega⟩ : Fin L) ∈ (bondSupport j).1 := by
    rw [← hij]
    exact mem_interval.mpr ⟨le_rfl, by simp⟩
  have hj : (⟨j, by omega⟩ : Fin L) ∈ (bondSupport i).1 := by
    rw [hij]
    exact mem_interval.mpr ⟨le_rfl, by simp⟩
  simp only [bondSupport, mem_interval] at hi hj
  exact Fin.ext (by omega)

/-- A sum of positive semidefinite bond terms selected by their support is positive
semidefinite; these sums are the terms of `ChainHamiltonian.ofBonds`. -/
private theorem posSemidef_sum_bondSupport_ite
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (X : ChainSupport L 1) :
    (∑ i, if bondSupport i = X then h i else 0).PosSemidef :=
  posSemidef_sum _ fun i _ ↦ by
    split_ifs
    exacts [h0 i, PosSemidef.zero]

/-- A family of bond terms `H_i`, supported on `{i, i + 1}` with `0 ≤ H_i ≤ 1`, as a range-one
chain Hamiltonian of interaction norm at most one. The term at the support `{i, i + 1}` is
`H_i`, and the single-site terms vanish. This is the Hamiltonian of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 209–211 and 283. -/
noncomputable def ChainHamiltonian.ofBonds
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1) : ChainHamiltonian L q 1 1 where
  term X := ∑ i, if bondSupport i = X then h i else 0
  supported X := TNLean.Lattice.isSupportedOn_sum _ fun i _ ↦ by
    split_ifs with hX
    · rw [← hX]
      exact hs i
    · exact ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ _ _ _ ↦ rfl⟩
  hermitian X := (posSemidef_sum_bondSupport_ite h h0 X).isHermitian
  norm_le X := by
    classical
    let S := Finset.univ.filter fun i ↦ bondSupport i = X
    have hcard : S.card ≤ 1 := Finset.card_le_one.mpr fun i hi j hj ↦
      bondSupport_injective ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    rw [← Finset.sum_filter]
    calc
      ‖∑ i ∈ S, h i‖ ≤ ∑ _ ∈ S, (1 : ℝ) := norm_sum_le_of_le S fun i _ ↦
          (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i).nonneg).mpr (h1 i)
      _ ≤ 1 := by simpa using (show (S.card : ℝ) ≤ 1 by exact_mod_cast hcard)

/-- The Hamiltonian of `ChainHamiltonian.ofBonds` is the sum of the bond terms. -/
theorem ChainHamiltonian.ofBonds_operator
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1) :
    (ChainHamiltonian.ofBonds h hs h0 h1).operator = ∑ i, h i := by
  simp only [ChainHamiltonian.operator, ChainHamiltonian.ofBonds]
  rw [Finset.sum_comm]
  simp

/-- The terms of `ChainHamiltonian.ofBonds` are positive semidefinite. -/
theorem ChainHamiltonian.posSemidef_ofBonds_term
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1) (X : ChainSupport L 1) :
    ((ChainHamiltonian.ofBonds h hs h0 h1).term X).PosSemidef :=
  posSemidef_sum_bondSupport_ite h h0 X

/-! ### The power projector -/

/-- The approximate ground-state projector `A = ((1 - H/n) / (1 - ε₀/n))^m` of Landau,
Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 599–600, with `n` sites. -/
noncomputable def powerProjector {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (n : ℕ) (E₀ : ℝ) (m : ℕ) : Matrix ι ι ℂ :=
  ((1 - E₀ / n)⁻¹ • (1 - (n : ℝ)⁻¹ • H)) ^ m

/-- With `L - 1` bonds, one more than their number is the number of sites. -/
private theorem card_bonds_add_one (hL : 0 < L) :
    (((Fintype.card (Fin (L - 1)) + 1 : ℕ) : ℝ)) = L := by
  rw [Fintype.card_fin, Nat.sub_add_cancel hL]

/-- The three properties of `A` at line 602, from the QICLean estimate for sums of positive
contractions with a lower bound on the gap. -/
private theorem powerProjector_spec (hL : 0 < L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) (m : ℕ) :
    (powerProjector (∑ i, h i) L E₀ m).PosSemidef ∧ ‖powerProjector (∑ i, h i) L E₀ m‖ = 1 ∧
      toEuclideanLin (powerProjector (∑ i, h i) L E₀ m) Γ = Γ := by
  obtain ⟨hΓ, hHΓ, hgap⟩ := isGappedGroundState_iff.mp hgs
  have hspec := power_filter_exp_spec_of_posSemidef_terms h h0 h1 hΓ hHΓ hgap hΔ m
  simp only [card_bonds_add_one hL] at hspec
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩

/-- The power projector is positive semidefinite. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 602. -/
theorem posSemidef_powerProjector (hL : 0 < L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) (m : ℕ) :
    (powerProjector (∑ i, h i) L E₀ m).PosSemidef :=
  (powerProjector_spec hL h h0 h1 hgs hΔ m).1

/-- The power projector has operator norm one. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 602. -/
theorem norm_powerProjector (hL : 0 < L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) (m : ℕ) :
    ‖powerProjector (∑ i, h i) L E₀ m‖ = 1 :=
  (powerProjector_spec hL h h0 h1 hgs hΔ m).2.1

/-- The power projector fixes the ground state, `AΓ = Γ`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 602. -/
theorem powerProjector_apply_ground (hL : 0 < L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) (m : ℕ) :
    toEuclideanLin (powerProjector (∑ i, h i) L E₀ m) Γ = Γ :=
  (powerProjector_spec hL h h0 h1 hgs hΔ m).2.2

/-- **Equation `e:cutdown`.** For every unit vector `ψ` orthogonal to the ground state,
`|⟨ψ, A ψ⟩| ≤ ((1 - ε₁/n) / (1 - ε₀/n))^m` with `ε₁ = ε₀ + Δ`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 603. Here `Δ` is any positive lower bound on the gap. -/
theorem norm_inner_powerProjector_le (hL : 0 < L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) (m : ℕ)
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)} (hψ : ‖ψ‖ = 1) (horth : ⟪Γ, ψ⟫_ℂ = 0) :
    ‖⟪ψ, toEuclideanLin (powerProjector (∑ i, h i) L E₀ m) ψ⟫_ℂ‖ ≤
      ((1 - (E₀ + Δ) / L) / (1 - E₀ / L)) ^ m := by
  obtain ⟨hΓ, hHΓ, hgap⟩ := isGappedGroundState_iff.mp hgs
  set H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
  set N : ℝ := (L : ℝ)
  set P : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))
  have hH : H.IsHermitian := (posSemidef_sum Finset.univ fun i _ ↦ h0 i).isHermitian
  have hHu : H ≤ ((L - 1 : ℕ) : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) := by
    simpa only [H, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul] using
      Finset.sum_le_card_nsmul Finset.univ h 1 fun i _ ↦ h1 i
  have hcardN : ((L - 1 : ℕ) : ℝ) < N := by
    simp only [N, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hL.ne'), Nat.cast_one]
    linarith
  -- The excited vector `ψ` gives `ε₀ + Δ ≤ L - 1`.
  have hexc : E₀ + Δ ≤ ((L - 1 : ℕ) : ℝ) := by
    have hlow := PosSemidef.gap_le hgap ψ
    rw [hψ, horth, norm_zero] at hlow
    have hup := (isPositive_toEuclideanLin_iff.mpr
      (Matrix.le_iff.mp hHu)).re_inner_nonneg_right ψ
    rw [map_sub, LinearMap.sub_apply, inner_sub_right, map_sub] at hup
    have hc : RCLike.re ⟪ψ, toEuclideanLin (((L - 1 : ℕ) : ℝ) •
        (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) ψ⟫_ℂ = ((L - 1 : ℕ) : ℝ) := by
      rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, toEuclideanLin_one_apply,
        inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
      simp
    rw [hc] at hup
    norm_num at hlow
    change Δ ≤ RCLike.re ⟪ψ, toEuclideanLin H ψ⟫_ℂ - E₀ at hlow
    linarith
  have hbound : ∀ t ∈ spectrum ℝ H, t ≤ ((L - 1 : ℕ) : ℝ) :=
    (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hHu)
  have hspectrum : ∀ t ∈ spectrum ℝ H, t = E₀ ∨ t ∈ Set.Icc (E₀ + Δ) N := by
    intro t ht
    obtain ⟨k, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ ht
    exact (GaussianFilter.eigenvector_ground_or_gap hH hΓ hHΓ hgap hΔ k).elim
      (fun hg ↦ Or.inl hg.1)
      (fun he ↦ Or.inr ⟨by linarith [he.1], (hbound _ ht).trans hcardN.le⟩)
  have h01 : E₀ < E₀ + Δ := lt_add_of_pos_right E₀ hΔ
  have h1N : E₀ + Δ ≤ N := hexc.trans hcardN.le
  obtain ⟨-, -, -, -, -, -, -, herror, -, -⟩ :=
    hH.power_approximates_isolated_energy_projection h01 h1N hspectrum m
  rw [hH.complement_spectralProjectionGE_eq_rankOne hΓ hHΓ hgap hΔ] at herror
  have hN : 0 < N := Nat.cast_pos.mpr hL
  have hd : 0 < N - E₀ := by linarith
  have hbase : (1 - E₀ / N)⁻¹ • (1 - N⁻¹ • H) =
      (N - E₀)⁻¹ • (N • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) - H) := by
    have hden : 1 - E₀ / N = (N - E₀) / N := one_sub_div hN.ne'
    rw [hden, inv_div]
    simp [smul_sub, smul_smul, div_eq_mul_inv, mul_comm, hN.ne']
  have hratio : (1 - (E₀ + Δ) / N) / (1 - E₀ / N) = (N - (E₀ + Δ)) / (N - E₀) := by
    rw [one_sub_div hN.ne', one_sub_div hN.ne', div_div_div_cancel_right₀ hN.ne']
  have hA : powerProjector H L E₀ m =
      ((N - E₀)⁻¹ • (N • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) - H)) ^ m := by
    rw [← hbase]
    rfl
  rw [hA, hratio]
  set K := ((N - E₀)⁻¹ • (N • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) - H)) ^ m
  have hPψ : toEuclideanLin P ψ = 0 := by
    simp [P, toEuclideanLin_vecMulVec_star_self_apply, horth]
  have hn : ‖toEuclideanLin (K - P) ψ‖ ≤ ‖K - P‖ * ‖ψ‖ :=
    (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (K - P)).le_opNorm ψ
  have hn' : ‖toEuclideanLin K ψ‖ ≤ ‖K - P‖ := by
    simpa only [map_sub, LinearMap.sub_apply, hPψ, sub_zero, hψ, mul_one] using hn
  have hinner : ‖⟪ψ, toEuclideanLin K ψ⟫_ℂ‖ ≤ ‖toEuclideanLin K ψ‖ := by
    simpa only [hψ, one_mul] using norm_inner_le_norm ψ (toEuclideanLin K ψ)
  exact hinner.trans (hn'.trans herror)

/-- **The logarithmic choice of `m`.** If `m ≥ ((n - ε₀)/Δ) log (1/η)` for some `η > 0`, then
`‖A - |Γ⟩⟨Γ|‖ ≤ η`. Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 602–603,
where `m = Θ((n/ε) log (q(n)/c_ε))` makes the bound `e:cutdown` at most `c_ε/(2 q(n))`. Here
`Δ` is any positive lower bound on the gap. -/
theorem norm_powerProjector_sub_le (hL : 0 < L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) {η : ℝ} (hη : 0 < η) (m : ℕ)
    (hm : ((L - E₀) / Δ) * Real.log (1 / η) ≤ m) :
    ‖powerProjector (∑ i, h i) L E₀ m - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
      η := by
  obtain ⟨hΓ, hHΓ, hgap⟩ := isGappedGroundState_iff.mp hgs
  have hm' : ((((Fintype.card (Fin (L - 1)) + 1 : ℕ) : ℝ) - E₀) / Δ) *
      Real.log (1 / η) ≤ (m : ℝ) := by
    rwa [card_bonds_add_one hL]
  have hthr := norm_power_filter_sub_ground_le_of_lower_gap_log_threshold h h0 h1 hΓ hHΓ hgap
    hΔ hη m hm'
  simp only [card_bonds_add_one hL] at hthr
  exact hthr

/-! ### The expansion into words -/

/-- The bond terms padded by a zero term at the last site: `H_i` for `i < L - 1` and `0` for
`i = L - 1`. This is the reading `H_n = 0` of the sum in Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 606–609. -/
noncomputable def paddedBond (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (i : Fin L) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  if hi : i.val < L - 1 then h ⟨i, hi⟩ else 0

/-- The letters `P_i = 1 - H_i` of the expansion, with `P_{L-1} = 1`. Landau, Vazirani and
Vidick, arXiv:1307.5143v1, `algo53.tex`, line 606. -/
noncomputable def bondComplement (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (i : Fin L) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  1 - paddedBond h i

/-- The ordered product `P_I = P_{i_1} ⋯ P_{i_m}` of a word `I`. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, line 608. -/
noncomputable def bondComplementWord
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) {m : ℕ} (I : Fin m → Fin L) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  (List.ofFn fun j ↦ bondComplement h (I j)).prod

/-- Padding by a zero term does not change the sum of the bond terms. -/
theorem sum_paddedBond (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    ∑ i, paddedBond h i = ∑ i, h i := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE (Nat.sub_le L 1)) (Fin.castLE_injective _) _ _
    (fun i hi ↦ ?_) (fun i ↦ ?_)
  · have : ¬i.val < L - 1 := fun hlt ↦ hi ⟨⟨i, hlt⟩, Fin.ext rfl⟩
    simp [paddedBond, this]
  · simp [paddedBond]

/-- **Equation `eq:a-exp`.** `A = C^m n^{-m} ∑_{I} P_I` with `C = 1/(1 - ε₀/n)`, the sum
running over all words `I` of length `m` in the `n` letters, the last of which is the identity.
Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 606–609. -/
theorem powerProjector_eq_sum_bondComplementWord (hL : 0 < L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) (m : ℕ) :
    powerProjector (∑ i, h i) L E₀ m =
      ((((1 - E₀ / L)⁻¹ : ℝ) : ℂ) ^ m / (L : ℂ) ^ m) •
        ∑ I : Fin m → Fin L, bondComplementWord h I := by
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have hexp := Fintype.smul_sub_average_pow_eq_sum_ordered_words (paddedBond h)
    (((1 - E₀ / L)⁻¹ : ℝ) : ℂ) m
  rw [Fintype.card_fin, sum_paddedBond, div_pow] at hexp
  have hA : powerProjector (∑ i, h i) L E₀ m =
      ((((1 - E₀ / L)⁻¹ : ℝ) : ℂ) • (1 - (L : ℂ)⁻¹ • ∑ i, h i)) ^ m := by
    rw [powerProjector, ← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    rfl
  rw [hA, hexp]
  rfl

/-! ### The rank of a word across a cut -/

/-- The support of the letter `P_i`: the sites `{i, i + 1}` of a bond, and no site for the
padding letter. -/
private def letterSupport (L : ℕ) (i : Fin L) : Finset (Fin L) :=
  if i.val < L - 1 then interval L i (i + 2) else ∅

/-- The letter `P_i` is supported on the sites of its bond. -/
private theorem isSupportedOn_bondComplement
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (i : Fin L) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (bondComplement h i) (letterSupport L i) := by
  by_cases hi : i.val < L - 1
  · simp only [bondComplement, paddedBond, letterSupport, hi, dite_true, ite_true]
    exact (Entropy.isSupportedOn_one _).sub (hs ⟨i, hi⟩)
  · simp only [bondComplement, paddedBond, letterSupport, hi, dite_false, ite_false, sub_zero]
    exact Entropy.isSupportedOn_one _

/-- A letter meets both sides of the cut after the sites `0, …, b` exactly when it is the bond
`b`, and then it has one site on the left. -/
private theorem letterSupport_crossing (b : Fin (L - 1)) (t : Fin L) :
    (¬(letterSupport L t ⊆ leftBlock L (b + 1) ∨ Disjoint (letterSupport L t) (leftBlock L (b + 1)))
      ↔ t.val = b.val) ∧
    (t.val = b.val → (letterSupport L t ∩ leftBlock L (b + 1)).card = 1) := by
  have hb := b.isLt
  by_cases ht : t.val < L - 1
  · simp only [letterSupport, ht, ite_true]
    refine ⟨⟨fun hc ↦ ?_, fun htb ↦ ?_⟩, fun htb ↦ ?_⟩
    · by_contra hne
      apply hc
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · left
        intro x hx
        rw [mem_interval] at hx
        rw [mem_leftBlock]
        omega
      · right
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [mem_interval] at hx
        rw [mem_leftBlock] at hx'
        omega
    · let y : Fin L := ⟨t.val + 1, by omega⟩
      have hy : y ∈ interval L t (t + 2) := mem_interval.mpr ⟨by simp [y], by simp [y]⟩
      have ht' : t ∈ interval L t (t + 2) := mem_interval.mpr ⟨le_rfl, by omega⟩
      rintro (hsub | hdisj)
      · have := mem_leftBlock.mp (hsub hy)
        simp only [y] at this
        omega
      · exact Finset.disjoint_left.mp hdisj ht' (mem_leftBlock.mpr (by omega))
    · refine Finset.card_eq_one.mpr ⟨t, ?_⟩
      ext x
      simp only [Finset.mem_inter, mem_interval, mem_leftBlock, Finset.mem_singleton,
        Fin.ext_iff]
      omega
  · simp only [letterSupport, ht, ite_false, Finset.empty_subset, true_or, not_true_eq_false,
      false_iff]
    refine ⟨by omega, fun htb ↦ by omega⟩

/-- The sum of the left counts of the crossing occurrences is the number of occurrences of
the bond `b`. -/
private theorem sum_crossing_eq_countP (b : Fin (L - 1)) (w : List (Fin L)) :
    ((w.filter fun t ↦ ¬(letterSupport L t ⊆ leftBlock L (b + 1) ∨
        Disjoint (letterSupport L t) (leftBlock L (b + 1)))).map
      fun t ↦ (letterSupport L t ∩ leftBlock L (b + 1)).card).sum =
      w.countP fun t ↦ t.val = b.val := by
  rw [List.countP_eq_length_filter]
  rw [List.filter_congr (q := fun t ↦ decide (t.val = b.val))
    (fun t _ ↦ decide_eq_decide.mpr (letterSupport_crossing b t).1)]
  rw [List.map_congr_left (g := fun _ ↦ 1) (fun t ht ↦
    (letterSupport_crossing b t).2 (by simpa using (List.mem_filter.mp ht).2))]
  simp

/-- **The rank bound behind equation `e:decomp`.** If the letter `P_b` occurs at most `k` times
in a word `I`, then `P_I` has operator Schmidt rank at most `q^{2k}` across the cut between the
sites `b` and `b + 1`, the cut crossed only by the bond `b`. Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`algo53.tex`, lines 584–588. -/
theorem operatorSchmidtRank_cutOperator_bondComplementWord_le
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (b : Fin (L - 1)) {m k : ℕ} (I : Fin m → Fin L)
    (hk : (Finset.univ.filter fun j ↦ (I j).val = b.val).card ≤ k) :
    Matrix.operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L (b + 1)) (bondComplementWord h I)) ≤ q ^ (2 * k) := by
  classical
  have hword : bondComplementWord h I = ((List.ofFn I).map (bondComplement h)).prod := by
    rw [bondComplementWord, List.map_ofFn]
    rfl
  have hrank := Entropy.operatorSchmidtRank_cutOperator_list_prod_le (q := q)
    (leftBlock L (b + 1)) (letterSupport L) (bondComplement h)
    (isSupportedOn_bondComplement h hs) (List.ofFn I)
  rw [← hword, sum_crossing_eq_countP] at hrank
  have hcount : (List.ofFn I).countP (fun t ↦ t.val = b.val) =
      (Finset.univ.filter fun j ↦ (I j).val = b.val).card := by
    rw [List.ofFn_eq_map, List.countP_map,
      show ((fun t : Fin L ↦ decide (t.val = b.val)) ∘ I) = fun j ↦ decide ((I j).val = b.val)
        from rfl, ← (List.nodup_finRange m).card_eq_countP, List.toFinset_finRange]
  rw [hcount] at hrank
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hb := b.isLt
    have : IsEmpty ((v : {v // v ∈ leftBlock L (b + 1)}) → Fin 0) :=
      ⟨fun f ↦ (f ⟨⟨0, by omega⟩, mem_leftBlock.mpr (by simp)⟩).elim0⟩
    exact (Matrix.operatorSchmidtRank_le_card_of_blocks_mem_span _
      (fun i : Fin 0 ↦ i.elim0) fun i _ ↦ isEmptyElim i).trans (by simp)
  · exact hrank.trans (Nat.pow_le_pow_right hq (by omega))

end TNLean.MPS.AreaLaw
