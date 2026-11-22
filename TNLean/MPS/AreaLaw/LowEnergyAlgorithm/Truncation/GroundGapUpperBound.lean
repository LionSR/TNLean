/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Eigenvalue.EuclideanEigenvectorBasis
import QICLean.Spectral.LowEnergy.Coordinates
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.ManyBody.Entropy.Filter.ChainEnergy
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Sites.Lattice.Chain
/-!
# The gap above a degenerate ground space is logarithmic in its dimension

Assumption (DG) of Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2,
source lines 275–279, asks for a gap `γ` above a ground space of dimension
`r`, for a nearest-neighbour chain with terms `0 ≤ h_i ≤ 1` (source lines 267
and 806). The local normalization does not force `γ ≤ 1`, but it does force
`q ^ m ≤ r` for every natural `m < γ`, where `q` is the local dimension.

The argument is variational. Write the chain as its first `L - m` sites and
its last `m` sites. Some slice `φ` of a ground vector along a fixed
configuration of the last `m` sites has energy at most the ground energy for
the terms supported on the first `L - m` sites. Every product `φ ⊗ χ` then has
energy at most the ground energy plus `m`, since at most `m` terms meet the
last `m` sites. These products form a space of dimension `q ^ m`; if it were
larger than the ground space, it would contain a nonzero vector orthogonal to
the ground space, whose energy is at least the ground energy plus `γ`.

## Main results

* `TNLean.MPS.AreaLaw.ALVV.pow_le_finrank_ground_of_lt_gap`: `m < γ` implies
  `m < L` and `q ^ m ≤ r`.
* `TNLean.MPS.AreaLaw.ALVV.gap_le_one_of_finrank_lt`: if `r < q`, in particular
  for a unique ground state, then `γ ≤ 1`.
* `TNLean.MPS.AreaLaw.ALVV.gap_le_one_add_log_div_log`: `γ ≤ 1 + log r / log q`.

These are used to compare the capped-gap estimates with the printed large-gap
expression; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
-/

open ManyBody (interval mem_interval)

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
open Matrix

namespace TNLean.MPS.AreaLaw.ALVV

/-- A subspace on which the quadratic form of `T` stays below `μ + c` has
dimension at most that of `G`, when the form is at least `μ + γ` on the
orthogonal complement of `G` and `c < γ`. This is the variational step of
the gap bound for ALVV, arXiv:1602.08828v2, Assumption (DG), lines 275–279. -/
theorem finrank_le_finrank_of_quadratic_window
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (G V : Submodule ℂ E) {μ γ c : ℝ} (hc : c < γ)
    (hG : ∀ w ∈ Gᗮ, (μ + γ) * ‖w‖ ^ 2 ≤ (inner ℂ w (T w)).re)
    (hV : ∀ v ∈ V, (inner ℂ v (T v)).re ≤ (μ + c) * ‖v‖ ^ 2) :
    Module.finrank ℂ V ≤ Module.finrank ℂ G := by
  have hdisj : V ⊓ Gᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    by_contra hw0
    have hpos : 0 < (γ - c) * ‖w‖ ^ 2 :=
      mul_pos (sub_pos.2 hc) (by positivity)
    have h1 := hG w hw.2
    have h2 := hV w hw.1
    nlinarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V Gᗮ
  rw [hdisj, finrank_bot, add_zero] at hsum
  have hle := Submodule.finrank_le (V ⊔ Gᗮ)
  have hG' := Submodule.finrank_add_finrank_orthogonal G
  omega

/-- The quadratic form of a Hermitian matrix with a gap `γ` above its least
spectral value `μ` is at least `μ + γ` on the orthogonal complement of the
closed spectral span at `μ`. ALVV, arXiv:1602.08828v2, Assumption (DG),
lines 275–279. -/
theorem mul_norm_sq_le_re_inner_of_mem_orthogonal_ground
    {σ : Type*} [Fintype σ] [DecidableEq σ] {H : Matrix σ σ ℂ} (hH : H.IsHermitian)
    {mu gamma : ℝ} (hgap : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z)
    {w : EuclideanSpace ℂ σ}
    (hw : w ∈ (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu)ᗮ) :
    (mu + gamma) * ‖w‖ ^ 2 ≤
      (inner ℂ w ((toEuclideanCLM (𝕜 := ℂ) (n := σ) H).toLinearMap w)).re := by
  classical
  set b := hH.eigenvectorBasis
  set a := hH.eigenvalues
  have hE : ∀ j, (toEuclideanCLM (𝕜 := ℂ) (n := σ) H).toLinearMap (b j) = (a j : ℂ) • b j :=
    fun j ↦ hH.toEuclideanCLM_eigenvectorBasis j
  have hsum := b.re_inner_apply_eq_sum_of_eigen a _ hE w
  have hnorm : ‖w‖ ^ 2 = ∑ j, ‖b.repr w j‖ ^ 2 := by
    rw [← b.repr.norm_map w, EuclideanSpace.norm_sq_eq]
  have hzero : ∀ j, a j ≤ mu → b.repr w j = 0 := by
    intro j hj
    rw [OrthonormalBasis.repr_apply_apply]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_image_of_mem b (show j ∈ {j | a j ≤ mu} from hj))) hw
  rw [hsum, hnorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  by_cases hj : a j ≤ mu
  · simp [hzero j hj]
  · rcases hgap (a j) (hH.eigenvalues_mem_spectrum_real j) with h | h
    · exact absurd h.le hj
    · exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

section Slices

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/-- The squared norm of a vector on a product splits into its slices. -/
theorem star_dotProduct_self_eq_sum_slices (w : α × β → ℂ) :
    star w ⬝ᵥ w = ∑ b, star (fun a ↦ w (a, b)) ⬝ᵥ fun a ↦ w (a, b) := by
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq α] in
/-- The quadratic form of `M ⊗ 1` splits into the quadratic forms of `M` on the
slices. -/
theorem star_dotProduct_kronecker_one_mulVec_eq_sum_slices (M : Matrix α α ℂ)
    (w : α × β → ℂ) :
    star w ⬝ᵥ ((M ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ w) =
      ∑ b, star (fun a ↦ w (a, b)) ⬝ᵥ (M *ᵥ fun a ↦ w (a, b)) := by
  have hmul : ∀ p : α × β, ((M ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ w) p =
      (M *ᵥ fun a ↦ w (a, p.2)) p.1 := by
    rintro ⟨a, b⟩
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  simp only [dotProduct, Pi.star_apply, hmul, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- **Product slices of bounded energy.** Let `M ⊗ 1 + N` act on a product,
with `0 ≤ N ≤ c`. If a nonzero `Ψ` has energy at most `μ`, then some nonzero
slice `φ` of `Ψ` makes every product `φ ⊗ χ` have energy at most `μ + c`.
This is the slice step of the gap bound for ALVV, arXiv:1602.08828v2,
Assumption (DG), lines 275–279. -/
theorem exists_slice_product_energy_le (M : Matrix α α ℂ)
    (N : Matrix (α × β) (α × β) ℂ) (hN0 : N.PosSemidef) {c mu : ℝ}
    (hN1 : ((c : ℂ) • (1 : Matrix (α × β) (α × β) ℂ) - N).PosSemidef)
    (Ψ : α × β → ℂ) (hΨ : Ψ ≠ 0)
    (hE : (star Ψ ⬝ᵥ ((M ⊗ₖ (1 : Matrix β β ℂ) + N) *ᵥ Ψ)).re ≤
      mu * (star Ψ ⬝ᵥ Ψ).re) :
    ∃ φ : α → ℂ, φ ≠ 0 ∧ ∀ χ : β → ℂ,
      (star (fun p : α × β ↦ φ p.1 * χ p.2) ⬝ᵥ
          ((M ⊗ₖ (1 : Matrix β β ℂ) + N) *ᵥ fun p : α × β ↦ φ p.1 * χ p.2)).re ≤
        (mu + c) * (star (fun p : α × β ↦ φ p.1 * χ p.2) ⬝ᵥ
          fun p : α × β ↦ φ p.1 * χ p.2).re := by
  classical
  set s : β → ℝ := fun b ↦
    (star (fun a ↦ Ψ (a, b)) ⬝ᵥ (M *ᵥ fun a ↦ Ψ (a, b))).re
  set n : β → ℝ := fun b ↦ (star (fun a ↦ Ψ (a, b)) ⬝ᵥ fun a ↦ Ψ (a, b)).re
  have hNre : ∀ w : α × β → ℂ, 0 ≤ (star w ⬝ᵥ (N *ᵥ w)).re := fun w ↦
    (Complex.nonneg_iff.mp (hN0.dotProduct_mulVec_nonneg w)).1
  have hsplit : ∀ w : α × β → ℂ, star w ⬝ᵥ ((M ⊗ₖ (1 : Matrix β β ℂ) + N) *ᵥ w) =
      star w ⬝ᵥ ((M ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ w) + star w ⬝ᵥ (N *ᵥ w) := by
    intro w
    rw [add_mulVec, dotProduct_add]
  have hsum : ∑ b, s b ≤ ∑ b, mu * n b := by
    have h := hE
    rw [hsplit, Complex.add_re, star_dotProduct_kronecker_one_mulVec_eq_sum_slices,
      star_dotProduct_self_eq_sum_slices, Complex.re_sum, Complex.re_sum] at h
    rw [← Finset.mul_sum]
    linarith [hNre Ψ]
  obtain ⟨b, hb0, hb⟩ : ∃ b, (fun a ↦ Ψ (a, b)) ≠ 0 ∧ s b ≤ mu * n b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hΨ
    have hlt : ∑ b, mu * n b < ∑ b, s b := by
      refine Finset.sum_lt_sum (fun b _ ↦ ?_) ⟨p.2, Finset.mem_univ _, ?_⟩
      · by_cases hzero : (fun a ↦ Ψ (a, b)) = 0
        · have hs : s b = 0 := by simp only [s, hzero, star_zero, zero_dotProduct,
            Complex.zero_re]
          have hn : n b = 0 := by simp only [n, hzero, star_zero, zero_dotProduct,
            Complex.zero_re]
          rw [hs, hn, mul_zero]
        · exact (hcon b hzero).le
      · refine hcon p.2 fun hzero ↦ hp ?_
        simpa using congrFun hzero p.1
    linarith
  refine ⟨fun a ↦ Ψ (a, b), hb0, fun χ ↦ ?_⟩
  set φ : α → ℂ := fun a ↦ Ψ (a, b)
  set v : α × β → ℂ := fun p ↦ φ p.1 * χ p.2
  have hslice : ∀ b', (fun a ↦ v (a, b')) = χ b' • φ := by
    intro b'
    funext a
    simp only [v, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hconj : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  have hleft : (star v ⬝ᵥ ((M ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ v)).re =
      ∑ b', ‖χ b'‖ ^ 2 * s b := by
    rw [star_dotProduct_kronecker_one_mulVec_eq_sum_slices, Complex.re_sum]
    refine Finset.sum_congr rfl fun b' _ ↦ ?_
    rw [hslice, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, hconj, Complex.re_ofReal_mul]
  have hnorm : (star v ⬝ᵥ v).re = ∑ b', ‖χ b'‖ ^ 2 * n b := by
    rw [star_dotProduct_self_eq_sum_slices, Complex.re_sum]
    refine Finset.sum_congr rfl fun b' _ ↦ ?_
    rw [hslice, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hconj, Complex.re_ofReal_mul]
  have hright : (star v ⬝ᵥ (N *ᵥ v)).re ≤ c * (star v ⬝ᵥ v).re := by
    have h := (Complex.nonneg_iff.mp (hN1.dotProduct_mulVec_nonneg v)).1
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
      Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at h
    linarith
  have hleft_le : (star v ⬝ᵥ ((M ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ v)).re ≤
      mu * (star v ⬝ᵥ v).re := by
    rw [hleft, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ ↦ ?_
    have hχ : 0 ≤ ‖χ b'‖ ^ 2 := sq_nonneg _
    nlinarith
  rw [hsplit, Complex.add_re]
  linarith

end Slices

/-- A nearest-neighbour term has the stated support. -/
private theorem interval_subset_interval_zero {L c : ℕ} {i : ℕ} (hi : i + 2 ≤ c) :
    interval L i (i + 2) ⊆ interval L 0 c := by
  intro v hv
  rw [mem_interval] at hv ⊢
  omega

/-- At most `L - c` of the nearest-neighbour terms meet the last `L - c` sites. -/
private theorem card_filter_not_le_le (L c : ℕ) (hc : c ≤ L) :
    (Finset.univ.filter fun i : Fin (L - 1) ↦ ¬ i.val + 2 ≤ c).card ≤ L - c := by
  have h := Finset.card_le_card_of_injOn (t := Finset.range (L - c))
    (s := Finset.univ.filter fun i : Fin (L - 1) ↦ ¬ i.val + 2 ≤ c)
    (fun i : Fin (L - 1) ↦ i.val + 1 - c)
    (by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      rw [Finset.mem_coe, Finset.mem_range]
      change i.val + 1 - c < L - c
      have := i.isLt
      have hi' := hi.2
      omega)
    (by
      intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_filter] at hi hj
      have hval : i.val + 1 - c = j.val + 1 - c := hij
      exact Fin.ext (by omega))
  simpa using h

/-- **The gap is at most logarithmic in the ground-space dimension.** For a
nearest-neighbour chain of `L` sites with terms `0 ≤ h_i ≤ 1`, a gap `γ` above
the least spectral value `μ`, and ground space `G`, every natural `m < γ`
satisfies `m < L` and `q ^ m ≤ dim G`. The positive-contraction normalization
and the gap are those of ALVV, arXiv:1602.08828v2, lines 267, 806 and
Assumption (DG), lines 275–279; the source states no bound on `γ`. -/
theorem pow_le_finrank_ground_of_lt_gap :
    ∀ (L q : ℕ) (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      ∀ m : ℕ, (m : ℝ) < gamma → m < L ∧ q ^ m ≤ Module.finrank ℂ G := by
  classical
  intro L q Φ h0 h1 mu nu gamma H hH hmu hnu hmunu hgap G
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  set Hc := (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) H).toLinearMap
  -- The ground space misses an eigenvector at `nu`, so it is proper.
  have hGlt : Module.finrank ℂ G < q ^ L := by
    obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hnu
    have hnot : hH.eigenvectorBasis j ∉ G := by
      intro hmem
      have h0' := (Submodule.mem_spectralSpanLE_iff _ _ _ _).mp hmem j (by rw [hj]; exact hmunu)
      simp [OrthonormalBasis.repr_self] at h0'
    have hne : G ≠ ⊤ := fun htop ↦ hnot (htop ▸ Submodule.mem_top)
    have := Submodule.finrank_lt hne
    simpa [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin] using this
  -- The main estimate for cuts with `m ≤ L`.
  have hmain : ∀ m : ℕ, m ≤ L → (m : ℝ) < gamma → q ^ m ≤ Module.finrank ℂ G := by
    intro m hmL hmγ
    set c := L - m with hc
    set B : Finset (Fin L) := interval L 0 c
    set e := ManyBody.cutEquiv (fun _ ↦ Fin q) B
    set S : Finset (Fin (L - 1)) := Finset.univ.filter fun i ↦ i.val + 2 ≤ c
    let cut : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ →
        Matrix ((({v // v ∈ B}) → Fin q) × (({v // v ∉ B}) → Fin q))
          ((({v // v ∈ B}) → Fin q) × (({v // v ∉ B}) → Fin q)) ℂ :=
      fun X ↦ ManyBody.cutOperator (X := fun _ ↦ Fin q) B X
    have hcut_sum : ∀ (s : Finset (Fin (L - 1))),
        cut (Φ.partialHamiltonian s) = ∑ i ∈ s, cut (Φ.term i) := by
      intro s
      exact map_sum (reindexLinearEquiv ℂ ℂ e e) _ s
    have hcut_psd : ∀ X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ, X.PosSemidef →
        (cut X).PosSemidef := fun X hX ↦ hX.submatrix _
    have hcut_one : cut 1 = 1 := submatrix_one_equiv e.symm
    obtain ⟨σ₀⟩ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, by omega⟩⟩
    set y₀ := (e σ₀).2
    -- Left part in Kronecker form.
    set M := ∑ i ∈ S, fun x x' ↦ cut (Φ.term i) (x, y₀) (x', y₀)
    have hleft : cut (Φ.partialHamiltonian S) = M ⊗ₖ (1 : Matrix _ _ ℂ) := by
      rw [hcut_sum]
      have hterm : ∀ i ∈ S, cut (Φ.term i) =
          (fun x x' ↦ cut (Φ.term i) (x, y₀) (x', y₀)) ⊗ₖ (1 : Matrix _ _ ℂ) := by
        intro i hi
        exact ManyBody.IsSupportedOn.cutOperator_eq_kronecker_one (Φ.mem i)
          (interval_subset_interval_zero (Finset.mem_filter.mp hi).2) y₀
      rw [Finset.sum_congr rfl hterm]
      ext p p'
      simp only [kroneckerMap, Matrix.of_apply, Matrix.sum_apply, M, Finset.sum_apply,
        Finset.sum_mul]
    -- Right part bounded by the number of right terms.
    set N := cut (Φ.partialHamiltonian Sᶜ)
    have hN0 : N.PosSemidef :=
      hcut_psd _ (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i))
    have hcard : (Sᶜ).card ≤ m := by
      have := card_filter_not_le_le L c (by omega)
      rw [Finset.compl_filter]
      omega
    have hNle : ∑ i ∈ Sᶜ, Φ.term i ≤ ((m : ℝ) : ℂ) • (1 : Matrix (Fin L → Fin q) _ ℂ) := by
      calc ∑ i ∈ Sᶜ, Φ.term i ≤ ∑ _i ∈ Sᶜ, (1 : Matrix (Fin L → Fin q) _ ℂ) :=
            Finset.sum_le_sum fun i _ ↦ h1 i
        _ = ((Sᶜ).card : ℂ) • (1 : Matrix (Fin L → Fin q) _ ℂ) := by
            rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
        _ ≤ ((m : ℝ) : ℂ) • (1 : Matrix (Fin L → Fin q) _ ℂ) := by
            rw [Matrix.le_iff, ← sub_smul]
            refine Matrix.PosSemidef.one.smul ?_
            have : ((Sᶜ).card : ℝ) ≤ m := by exact_mod_cast hcard
            rw [show ((m : ℝ) : ℂ) - ((Sᶜ).card : ℂ) = (((m : ℝ) - (Sᶜ).card : ℝ) : ℂ) by
              push_cast; ring]
            exact Complex.zero_le_real.mpr (by linarith)
    have hN1 : (((m : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) - N).PosSemidef := by
      have h' := hcut_psd _ (Matrix.le_iff.mp hNle)
      have hlin : cut (((m : ℝ) : ℂ) • (1 : Matrix (Fin L → Fin q) _ ℂ) - ∑ i ∈ Sᶜ, Φ.term i) =
          ((m : ℝ) : ℂ) • cut 1 - N :=
        rfl
      rwa [hlin, hcut_one] at h'
    have hHc : cut H = M ⊗ₖ (1 : Matrix _ _ ℂ) + N := by
      rw [← hleft]
      change cut (∑ i, Φ.term i) = cut (∑ i ∈ S, Φ.term i) + cut (∑ i ∈ Sᶜ, Φ.term i)
      rw [← Finset.sum_add_sum_compl S Φ.term]
      exact map_add (reindexLinearEquiv ℂ ℂ e e) _ _
    -- A nonzero ground vector and its energy.
    have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
    obtain ⟨ψ, hψG, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hGne
    have hψE : (inner ℂ ψ (Hc ψ)).re ≤ mu * ‖ψ‖ ^ 2 :=
      Submodule.re_inner_apply_le_of_mem_spectralSpanLE hH.eigenvectorBasis hH.eigenvalues Hc
        (fun j ↦ hH.toEuclideanCLM_eigenvectorBasis j) mu hψG
    -- Quadratic forms in cut coordinates.
    have hform : ∀ x : EuclideanSpace ℂ (Fin L → Fin q),
        (inner ℂ x (Hc x)).re =
          (star (fun p ↦ x (e.symm p)) ⬝ᵥ (cut H *ᵥ fun p ↦ x (e.symm p))).re := by
      intro x
      have h' := Entropy.inner_cutOperator (n := fun _ : Fin L ↦ q) B H x
      have hl : inner ℂ x (Hc x) = inner ℂ x (toEuclideanLin H x) := rfl
      rw [hl, ← h', EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rfl
    have hnormc : ∀ x : EuclideanSpace ℂ (Fin L → Fin q),
        ‖x‖ ^ 2 = (star (fun p ↦ x (e.symm p)) ⬝ᵥ fun p ↦ x (e.symm p)).re := by
      intro x
      rw [← Entropy.norm_cutVector (n := fun _ : Fin L ↦ q) B x, @norm_sq_eq_re_inner ℂ,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rfl
    set Ψ : _ → ℂ := fun p ↦ ψ (e.symm p)
    have hΨ0 : Ψ ≠ 0 := by
      intro hzero
      apply hψ0
      ext x
      simpa [Ψ] using congrFun hzero (e x)
    have hΨE : (star Ψ ⬝ᵥ ((M ⊗ₖ (1 : Matrix _ _ ℂ) + N) *ᵥ Ψ)).re ≤
        mu * (star Ψ ⬝ᵥ Ψ).re := by
      rw [← hHc, ← hform, ← hnormc]
      exact hψE
    obtain ⟨φ, hφ0, hφ⟩ := exists_slice_product_energy_le M N hN0 hN1 Ψ hΨ0 hΨE
    -- The product space in the original coordinates.
    let T : ((({v // v ∉ B}) → Fin q) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
      { toFun := fun χ ↦ WithLp.toLp 2 fun x ↦ φ (e x).1 * χ (e x).2
        map_add' := by
          intro χ χ'
          ext x
          simp [mul_add]
        map_smul' := by
          intro t χ
          ext x
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.smul_apply]
          ring }
    have hT : ∀ χ, (fun p ↦ T χ (e.symm p)) = fun p ↦ φ p.1 * χ p.2 := by
      intro χ
      funext p
      simp [T]
    have hTinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro χ hχ
      rw [LinearMap.mem_ker] at hχ
      obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hφ0
      funext y
      have h' := congrFun (hT χ) (a₀, y)
      rw [hχ] at h'
      simp only [PiLp.zero_apply, Pi.zero_apply] at h' ⊢
      exact (mul_eq_zero.mp h'.symm).resolve_left ha₀
    have hrange : Module.finrank ℂ (LinearMap.range T) = q ^ m := by
      rw [LinearMap.finrank_range_of_inj hTinj, Module.finrank_fintype_fun_eq_card,
        Fintype.card_pi]
      simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
      have hB : B.card = c := by
        have : B = Finset.univ.filter fun i : Fin L ↦ i.val < c := by
          ext i
          simp [B, mem_interval]
        rw [this, Fin.card_filter_val_lt]
        omega
      omega
    rw [← hrange]
    refine finrank_le_finrank_of_quadratic_window Hc G (LinearMap.range T)
      (μ := mu) (c := m) hmγ
      (fun w hw ↦ mul_norm_sq_le_re_inner_of_mem_orthogonal_ground hH hgap hw) ?_
    rintro _ ⟨χ, rfl⟩
    rw [hform, hnormc, hT, hHc]
    exact hφ χ
  intro m hmγ
  have hmL : m < L := by
    by_contra hLm
    push Not at hLm
    have hLγ : (L : ℝ) < gamma := lt_of_le_of_lt (by exact_mod_cast hLm) hmγ
    have := hmain L le_rfl hLγ
    omega
  exact ⟨hmL, hmain m hmL.le hmγ⟩

/-- **A ground space of dimension below the local dimension has gap at most
one.** In particular a unique ground state has gap at most one, so the capped
gap `min γ 1` of the formal estimates is the gap itself. ALVV,
arXiv:1602.08828v2, Assumption (DG), lines 275–279. -/
theorem gap_le_one_of_finrank_lt (L q : ℕ)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    Module.finrank ℂ G < q → gamma ≤ 1 := by
  intro H hH hmu hnu hmunu hgap G hlt
  by_contra hγ
  push Not at hγ
  have := (pow_le_finrank_ground_of_lt_gap L q Φ h0 h1 mu nu gamma hmu hnu hmunu hgap 1
    (by exact_mod_cast hγ)).2
  rw [pow_one] at this
  exact (not_le.mpr hlt) this

/-- **Logarithmic gap bound.** The gap above the ground space of dimension `r`
satisfies `γ ≤ 1 + log r / log q`. ALVV, arXiv:1602.08828v2, Assumption (DG),
lines 275–279, together with the normalization `0 ≤ h_i ≤ 1` of lines 267
and 806. -/
theorem gap_le_one_add_log_div_log (L q : ℕ)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    gamma ≤ 1 + Real.log (Module.finrank ℂ G : ℝ) / Real.log q := by
  intro H hH hmu hnu hmunu hgap G
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hr : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hlogr : 0 ≤ Real.log (Module.finrank ℂ G : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hr)
  rcases le_or_gt gamma 0 with hγ | hγ
  · have := div_nonneg hlogr hlogq.le
    linarith
  set m := ⌈gamma⌉₊ - 1
  have hceil : 1 ≤ ⌈gamma⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hγ).ne'
  have hm : (m : ℝ) = ⌈gamma⌉₊ - 1 := by
    rw [Nat.cast_sub hceil, Nat.cast_one]
  have hmγ : (m : ℝ) < gamma := by
    rw [hm]
    linarith [Nat.ceil_lt_add_one hγ.le]
  have hpow := (pow_le_finrank_ground_of_lt_gap L q Φ h0 h1 mu nu gamma hmu hnu hmunu hgap
    m hmγ).2
  have hlog : (m : ℝ) * Real.log q ≤ Real.log (Module.finrank ℂ G : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have hdiv : (m : ℝ) ≤ Real.log (Module.finrank ℂ G : ℝ) / Real.log q :=
    (le_div_iff₀ hlogq).mpr hlog
  have hceil_le : gamma ≤ ⌈gamma⌉₊ := Nat.le_ceil gamma
  linarith

end TNLean.MPS.AreaLaw.ALVV
