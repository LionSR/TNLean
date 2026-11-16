/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FundamentalTheoremGatesSupplied
import TNLean.MPS.MPU.TimeReversalSignInvariance

/-!
# Continuity of standard-form gates modulo local unitaries

Corollary `coruvSF` of arXiv:1703.09188 (lines 867--910) chooses continuous
standard-form gates along a continuous path of MPU tensors. Its first step
is that any pointwise choice of gates is continuous modulo the local
unitaries `G = U(ℓ) × U(r)` acting by `u ↦ (x ⊗ y) u`.

The proof follows the last paragraph of
`docs/paper-gaps/mpu_standard_form_path_cross_section.tex`. Unitary gates lie
in a compact set. If the gates at `q_n → p` stayed away from the orbit of
the gates at `p`, a convergent subsequence would have a limit pair whose
circuits on rings of two and three blocks are the limits of the circuits at
`q_n`, hence the circuits at `p`. The Fundamental Theorem for gate pairs
(`exists_gate_gauges_of_twoSiteCircuit_eq`) then places the limit in the
orbit, a contradiction. No canonical form, simplicity, or standard-form data
for the limit is needed: only that the gates are unitary and that their
two- and three-block circuits vary continuously.

## Main results

* `MPOTensor.isCompact_setOf_isUnitaryBetween`.
* `MPOTensor.continuous_twoSiteCircuit`.
* `MPOTensor.eventually_exists_gate_gauge_sub_mem`: continuity of the gates
  modulo local unitaries.
-/

open scoped Matrix Kronecker Topology
open Filter

namespace MPOTensor

variable {d ℓ r : ℕ}

/-- The rectangular unitaries between two finite coordinate spaces form a
compact set. -/
theorem isCompact_setOf_isUnitaryBetween {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    IsCompact {A : Matrix m n ℂ | A.IsUnitaryBetween} := by
  have hbox : IsCompact (Set.univ.pi fun _ : m ↦ Set.univ.pi fun _ : n ↦
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {A : Matrix m n ℂ | Aᴴ * A = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
        continuous_const
    have h2 : IsClosed {A : Matrix m n ℂ | A * Aᴴ = 1} :=
      isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
        continuous_const
    exact h1.inter h2
  · rintro (A : Matrix m n ℂ) hA
    have hAA : A * Aᴴ = 1 := hA.2
    refine Set.mem_univ_pi.mpr fun i ↦ Set.mem_univ_pi.mpr fun j ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hrow : ∑ k, A i k * star (A i k) = 1 := by
      have := congrFun (congrFun hAA i) i
      rwa [Matrix.mul_apply, Matrix.one_apply_eq] at this
    have hsum : ∑ k, ‖A i k‖ ^ 2 = 1 := by
      have : ∑ k, (A i k * star (A i k)) = ((∑ k, ‖A i k‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast; ring
      rw [this] at hrow
      exact_mod_cast hrow
    have hle : ‖A i j‖ ^ 2 ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun k ↦ ‖A i k‖ ^ 2) (fun k _ ↦ by positivity)
        (Finset.mem_univ j)
    nlinarith [norm_nonneg (A i j)]

/-- The circuit of a gate pair on a ring of `N` two-site blocks depends
continuously on the gates. -/
theorem continuous_twoSiteCircuit (N : ℕ) [NeZero N] :
    Continuous fun g : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ ×
        Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ ↦
      twoSiteShiftedLayer (N := N) g.2 * twoSiteUnshiftedLayer (N := N) g.1 := by
  refine Continuous.matrix_mul ?_ ?_
  · refine continuous_matrix fun i h ↦ ?_
    exact continuous_finsetProd _ fun x _ ↦
      (continuous_apply _).comp ((continuous_apply _).comp continuous_snd)
  · refine continuous_matrix fun h j ↦ ?_
    exact continuous_finsetProd _ fun x _ ↦
      (continuous_apply _).comp ((continuous_apply _).comp continuous_fst)

/-- **Gates are continuous modulo local unitaries.** Let `q ↦ (u q, v q)` be
unitary gate pairs whose circuits on rings of two and three blocks are
continuous at `p`. Then for every neighbourhood `W` of `0`, every `q` near
`p` has unitaries `x, y` with `u q - (x ⊗ y) u p ∈ W`.

Source: arXiv:1703.09188, Corollary `coruvSF`, lines 867--910, first step of
the proof; the argument is the one in the last paragraph of
`docs/paper-gaps/mpu_standard_form_path_cross_section.tex`. -/
theorem eventually_exists_gate_gauge_sub_mem {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [NeZero ℓ] [NeZero r]
    (u : P → Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : P → Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : ∀ q, (u q).IsUnitaryBetween) (hv : ∀ q, (v q).IsUnitaryBetween) (p : P)
    (h₂ : ContinuousAt (fun q ↦
      twoSiteShiftedLayer (N := 2) (v q) * twoSiteUnshiftedLayer (N := 2) (u q)) p)
    (h₃ : ContinuousAt (fun q ↦
      twoSiteShiftedLayer (N := 3) (v q) * twoSiteUnshiftedLayer (N := 3) (u q)) p)
    {W : Set (Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)} (hW : W ∈ 𝓝 0) :
    ∀ᶠ q in 𝓝 p, ∃ (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ),
      u q - ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u p ∈ W := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨qs, hqs, hbad⟩ := frequently_iff_seq_forall.mp hcon
  have hK : IsCompact ({A : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ | A.IsUnitaryBetween} ×ˢ
      {B : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ | B.IsUnitaryBetween}) :=
    isCompact_setOf_isUnitaryBetween.prod isCompact_setOf_isUnitaryBetween
  have : FirstCountableTopology (Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin ℓ × Fin r → Fin d × Fin d → ℂ))
  have : FirstCountableTopology (Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin d × Fin d → Fin r × Fin ℓ → ℂ))
  obtain ⟨⟨u', v'⟩, hmem, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq (x := fun n ↦ (u (qs n), v (qs n))) (fun n ↦ ⟨hu _, hv _⟩)
  have hqφ : Tendsto (qs ∘ φ) atTop (𝓝 p) := hqs.comp hφ.tendsto_atTop
  -- The limit pair has the circuits of the gates at `p`.
  have hcirc : ∀ (N : ℕ) [NeZero N],
      ContinuousAt (fun q ↦
        twoSiteShiftedLayer (N := N) (v q) * twoSiteUnshiftedLayer (N := N) (u q)) p →
      twoSiteShiftedLayer (N := N) v' * twoSiteUnshiftedLayer (N := N) u' =
        twoSiteShiftedLayer (N := N) (v p) * twoSiteUnshiftedLayer (N := N) (u p) := by
    intro N _ hc
    have h1 := ((continuous_twoSiteCircuit (d := d) (ℓ := ℓ) (r := r) N).tendsto
      (u', v')).comp hlim
    have h2 := hc.tendsto.comp hqφ
    exact tendsto_nhds_unique h1 h2
  obtain ⟨x, y, hx, -⟩ := exists_gate_gauges_of_twoSiteCircuit_eq (hu p) hmem.1 (hv p)
    (hcirc 2 h₂) (hcirc 3 h₃)
  have hconv : Tendsto (fun n ↦ u (qs (φ n)) -
      ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u p) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ u (qs (φ n))) atTop (𝓝 u') :=
      (continuous_fst.tendsto (u', v')).comp hlim
    have hx' : u' = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u p :=
      hx
    rw [hx'] at h1
    have := h1.sub_const
      (((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u p)
    rwa [sub_self] at this
  obtain ⟨n, hn⟩ := (hconv.eventually hW).exists
  exact hbad (φ n) ⟨x, y, hn⟩

/-- The periodic operator of a fixed length depends continuously on the tensor. -/
theorem continuous_mpo {D : ℕ} (N : ℕ) : Continuous fun W : MPOTensor d D ↦ mpo W N :=
  continuous_matrix fun σ τ ↦ by
    simp only [mpo_apply, mpoMatrixEntry]
    exact (continuous_evalWord (List.ofFn σ) (List.ofFn τ)).matrix_trace

/-- **Standard-form gates along a path are continuous modulo local
unitaries.** Let `q ↦ 𝒰(q)` be a continuous path of tensors, not necessarily in
canonical form, and fix a blocking length `k`. Suppose that at every `q` the
gates `u q, v q` are those of a standard form of the two-site block of some
tensor `𝒱` with the same periodic operators as the `k`-site block of `𝒰(q)`,
for instance of its canonical representative. Then for every neighbourhood `W`
of `0`, every `q` near `p` has unitaries `x, y` with
`u q - (x ⊗ y) u p ∈ W`. The choices at different points are unrelated.

Source: arXiv:1703.09188, Corollary `coruvSF`, lines 867--910 ("not
necessarily in CF", lines 869--875), first step of the proof; see
`docs/paper-gaps/mpu_standard_form_path_cross_section.tex`. -/
theorem eventually_exists_gate_gauge_sub_mem_of_path {D : ℕ} {P : Type*}
    [TopologicalSpace P] [FirstCountableTopology P]
    {U : P → MPOTensor d D} (hU : Continuous U) (k : ℕ)
    (u : P → Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ)
    (v : P → Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ)
    (hrep : ∀ q, ∃ (D' : ℕ) (V : MPOTensor (MPSTensor.blockPhysDim d k) D'),
      (∀ N : ℕ, 0 < N → mpo V N = mpo (blockTensor (U q) k) N) ∧
        Nonempty (TwoSiteStandardFormData (MPOTensor.blockTwo V) (u q) (v q)))
    (p : P) {W : Set (Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ)}
    (hW : W ∈ 𝓝 0) :
    ∀ᶠ q in 𝓝 p, ∃ (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ),
      u q - ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u p ∈ W := by
  obtain ⟨D₀, V₀, -, ⟨S₀⟩⟩ := hrep p
  have : NeZero ℓ := ⟨S₀.left_pos.ne'⟩
  have : NeZero r := ⟨S₀.right_pos.ne'⟩
  have hu : ∀ q, (u q).IsUnitaryBetween := fun q ↦ by
    obtain ⟨_, _, -, ⟨S⟩⟩ := hrep q
    exact S.u_unitary
  have hv : ∀ q, (v q).IsUnitaryBetween := fun q ↦ by
    obtain ⟨_, _, -, ⟨S⟩⟩ := hrep q
    exact S.v_unitary
  -- Each circuit is a fixed reindexing of a periodic operator of the blocked path.
  have hcont : ∀ (N : ℕ) [NeZero N], ContinuousAt (fun q ↦
      twoSiteShiftedLayer (N := N) (v q) * twoSiteUnshiftedLayer (N := N) (u q)) p := by
    intro N _
    have heq : (fun q ↦
        twoSiteShiftedLayer (N := N) (v q) * twoSiteUnshiftedLayer (N := N) (u q)) =
        fun q ↦ Matrix.reindex (twoSitePairConfigEquiv _ N).symm
          (twoSitePairConfigEquiv _ N).symm
          (mpo (MPOTensor.blockTwo (blockTensor (U q) k)) N) := by
      funext q
      obtain ⟨_, V, hV, ⟨S⟩⟩ := hrep q
      rw [← S.mpo_eq_shifted_mul_unshifted,
        mpo_blockTwo_eq_of_mpo_eq hV N (Nat.pos_of_ne_zero (NeZero.ne N))]
    rw [heq]
    exact (((continuous_mpo N).comp (continuous_blockTwo.comp
      ((continuous_blockTensor k).comp hU))).matrix_reindex _ _).continuousAt
  exact eventually_exists_gate_gauge_sub_mem u v hu hv p (hcont 2) (hcont 3) hW

end MPOTensor
