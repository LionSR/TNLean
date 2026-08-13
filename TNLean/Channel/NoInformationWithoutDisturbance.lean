/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.POVM

/-!
# No information without disturbance

This file formalizes the proposition *No information without disturbance* of
[M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels],
`Notes/WolfNoteTexSource/ch02_representations.tex`, line 154.

An instrument is a family of completely positive maps `{T α : M_d → M_d}` whose sum is
trace preserving. If the instrument causes no disturbance on average, that is if
`∑ α, T α = id`, then every component is a nonnegative multiple `T α = c α · id` of the
identity, and hence the probability `tr[T α ρ]` of the outcome `α` equals `c α` for every
`ρ` of unit trace: the outcome statistics carry no information about the input. The
theorems below assume complete positivity of the components and `∑ α, T α = id`, which is
Wolf's hypothesis, and nothing more.

The proof is Wolf's. Under the Choi–Jamiolkowski correspondence the hypothesis reads
`|Ω⟩⟨Ω| = ∑ α, τ α`, where `τ α` is the Choi matrix of `T α`. Complete positivity makes
each `τ α` positive semidefinite, so the identity above is a decomposition of the pure
state `|Ω⟩⟨Ω|` into positive parts; each part is dominated by `|Ω⟩⟨Ω|` and a matrix
dominated by a rank-one positive matrix is a nonnegative multiple of it. Injectivity of
the Choi correspondence transports the conclusion back to the maps.

## Main results

* `Channel.exists_nonneg_smul_id_of_isCPMap_of_sum_eq_id` — each component of a
  no-disturbance instrument is a nonnegative multiple of the identity.
* `Channel.exists_nonneg_weights_of_isCPMap_of_sum_eq_id` — the multipliers are
  nonnegative and sum to one.
* `Channel.exists_nonneg_forall_trace_map_eq_of_isCPMap_of_sum_eq_id` — the outcome
  probability `tr[T α ρ]` is a constant, the same for every `ρ` of unit trace.
* `Instrument.exists_nonneg_forall_probability_eq_of_total_eq_id` — the same conclusion
  for the instrument structure of `TNLean.Channel.POVM`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2, proposition
  "No information without disturbance"][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Channel

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-! ### Rigidity of the maximally entangled projector -/

/-- A positive semidefinite bipartite matrix dominated by the maximally entangled
projector `|Ω⟩⟨Ω|` is a nonnegative multiple of that projector.

This is the rank-one rigidity step of Wolf's argument, obtained from
`Matrix.PosSemidef.eq_nonneg_smul_vecMulVec_of_le_smul_vecMulVec` by relabelling the
bipartite index set `Fin D × Fin D` as `Fin (D * D)`. -/
theorem exists_nonneg_smul_omegaProj_of_le_omegaProj
    {A : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ} (hA : A.PosSemidef)
    (hle : A ≤ Matrix.omegaProj D) :
    ∃ a : ℂ, 0 ≤ a ∧ A = a • Matrix.omegaProj D := by
  classical
  let e : Fin D × Fin D ≃ Fin (D * D) := finProdFinEquiv
  let ψ : Fin (D * D) → ℂ := Matrix.omegaVec D ∘ e.symm
  have hvec : (Matrix.omegaProj D).submatrix e.symm e.symm = Matrix.vecMulVec ψ (star ψ) := by
    ext i j
    simp [Matrix.omegaProj, Matrix.vecMulVec_apply, ψ]
  have hAsub : (A.submatrix e.symm e.symm).PosSemidef := hA.submatrix _
  have hsub : (Matrix.omegaProj D - A).submatrix e.symm e.symm =
      (Matrix.omegaProj D).submatrix e.symm e.symm - A.submatrix e.symm e.symm := rfl
  have hdom : A.submatrix e.symm e.symm ≤ (1 : ℂ) • Matrix.vecMulVec ψ (star ψ) := by
    rw [Matrix.le_iff, one_smul, ← hvec, ← hsub]
    exact (Matrix.le_iff.mp hle).submatrix _
  obtain ⟨a, ha, haeq⟩ :=
    Matrix.PosSemidef.eq_nonneg_smul_vecMulVec_of_le_smul_vecMulVec hAsub ψ hdom
  rw [← hvec] at haeq
  refine ⟨a, ha, ?_⟩
  ext i j
  simpa using congrArg (fun M => M (e i) (e j)) haeq

/-! ### No information without disturbance -/

/-- **No information without disturbance** (Wolf, Chapter 2, line 154), component form.

If a family of completely positive maps `T α : M_d → M_d` sums to the identity, then
every component is a nonnegative multiple of the identity. -/
theorem exists_nonneg_smul_id_of_isCPMap_of_sum_eq_id [NeZero D]
    {T : ι → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hCP : ∀ α, IsCPMap (T α)) (hsum : ∑ α, T α = LinearMap.id) (α : ι) :
    ∃ c : ℝ, 0 ≤ c ∧ T α = (c : ℂ) • LinearMap.id := by
  classical
  have hpsd : ∀ β, (ChoiJamiolkowski.choiMatrix (T β)).PosSemidef := fun β =>
    (ChoiJamiolkowski.cp_iff_choi_posSemidef (T β)).mp (hCP β)
  have hchoisum : ∑ β, ChoiJamiolkowski.choiMatrix (T β) = Matrix.omegaProj D := by
    have hmap : ChoiJamiolkowski.choiMatrix (∑ β, T β) =
        ∑ β, ChoiJamiolkowski.choiMatrix (T β) :=
      map_sum (ChoiJamiolkowski.choiMatrixLinearMap (D := D)) T Finset.univ
    rw [← hmap, hsum, ChoiJamiolkowski.choiMatrix_id]
  have hle : ChoiJamiolkowski.choiMatrix (T α) ≤ Matrix.omegaProj D := by
    rw [← hchoisum]
    exact Finset.single_le_sum (fun β _ => (hpsd β).nonneg) (Finset.mem_univ α)
  obtain ⟨a, ha, haeq⟩ := exists_nonneg_smul_omegaProj_of_le_omegaProj (hpsd α) hle
  obtain ⟨hre, him⟩ := Complex.le_def.mp ha
  have hareal : (a.re : ℂ) = a := Complex.ext (by simp) (by simpa using him)
  refine ⟨a.re, by simpa using hre, ChoiJamiolkowski.choiMatrix_injective ?_⟩
  rw [ChoiJamiolkowski.choiMatrix_smul, ChoiJamiolkowski.choiMatrix_id, hareal, haeq]

/-- **No information without disturbance** (Wolf, Chapter 2, line 154), with the
normalization of the multipliers.

The multipliers `c α` of a no-disturbance instrument are nonnegative and sum to one. -/
theorem exists_nonneg_weights_of_isCPMap_of_sum_eq_id [NeZero D]
    {T : ι → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hCP : ∀ α, IsCPMap (T α)) (hsum : ∑ α, T α = LinearMap.id) :
    ∃ c : ι → ℝ, (∀ α, 0 ≤ c α) ∧ (∀ α, T α = (c α : ℂ) • LinearMap.id) ∧ ∑ α, c α = 1 := by
  classical
  choose c hc0 hcid using exists_nonneg_smul_id_of_isCPMap_of_sum_eq_id hCP hsum
  have hDne : ((D : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  refine ⟨c, hc0, hcid, ?_⟩
  have happ : ∑ α, T α (1 : Matrix (Fin D) (Fin D) ℂ) = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simpa using congrArg (fun L => L (1 : Matrix (Fin D) (Fin D) ℂ)) hsum
  have htrace : (∑ α, (c α : ℂ)) * (D : ℂ) = (D : ℂ) := by
    have := congrArg Matrix.trace happ
    simpa [hcid, Matrix.trace_sum, Matrix.trace_smul, Finset.sum_mul] using this
  have hone : (∑ α, (c α : ℂ)) = 1 :=
    mul_right_cancel₀ hDne (by rw [one_mul]; exact htrace)
  exact_mod_cast hone

/-- **No information without disturbance** (Wolf, Chapter 2, line 154), probability form.

For a no-disturbance instrument the probability `tr[T α ρ]` of the outcome `α` is a
nonnegative constant, the same for every `ρ` of unit trace: the outcome carries no
information about the input. -/
theorem exists_nonneg_forall_trace_map_eq_of_isCPMap_of_sum_eq_id [NeZero D]
    {T : ι → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hCP : ∀ α, IsCPMap (T α)) (hsum : ∑ α, T α = LinearMap.id) (α : ι) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.trace = 1 → (T α ρ).trace = (c : ℂ) := by
  obtain ⟨c, hc0, hcid⟩ := exists_nonneg_smul_id_of_isCPMap_of_sum_eq_id hCP hsum α
  refine ⟨c, hc0, fun ρ hρ => ?_⟩
  rw [hcid]
  simp [Matrix.trace_smul, hρ]

end Channel

/-- **No information without disturbance** for an instrument (Wolf, Chapter 2, line 154).

If the average map of an instrument is the identity, then each outcome probability is a
nonnegative constant, the same for every input of unit trace: the measurement returns no
information about the input. -/
theorem Instrument.exists_nonneg_forall_probability_eq_of_total_eq_id
    {D n : ℕ} [NeZero D] (I : Instrument D n) (hI : I.total = LinearMap.id) (i : Fin n) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.trace = 1 → I.probability i ρ = (c : ℂ) :=
  Channel.exists_nonneg_forall_trace_map_eq_of_isCPMap_of_sum_eq_id I.cp hI i
