/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.VaryingOBCBoundaryStates

/-!
# The state line of a varying-bond open parent Hamiltonian

The actual parent-projector kernel supplies the adjacent coefficient sections.
Canonical adjoint reconstruction along the whole chain then reduces every kernel
vector to a scalar multiple of the actual open-chain state. The state itself has
unit norm, derived from the sitewise canonical equations and singleton endpoints.

**Scope restriction (adjacent open chains):** the physical alphabet is common to
the sites throughout this module, and the chain length is at least two in
`exists_smul_obcScalarState_of_obcParentHamiltonian_apply_eq_zero`,
`ker_obcParentHamiltonian_eq_span` and `finrank_ker_obcParentHamiltonian_eq_one`.
The statements concern the actual ground-state line and allow scalar phase
freedom of normalized vectors.
The scope and remaining unrestricted source question are recorded in
`docs/paper-gaps/pgvwc07_open_parent_domain.tex`.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 and proof,
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 1195–1237.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace Matrix

variable {d : ℕ}

/-- The actual open-chain state, obtained by reading the singleton endpoint entry
of the ordered rectangular product. No state or canonical supplier is assumed.
Source: PGVWC07, Theorem 9, lines 1195–1205. -/
noncomputable def obcScalarState (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    (N : ℕ) (hleft : b 0 = 1) (hright : b N = 1) :
    EuclideanSpace ℂ (Fin N → Fin d) :=
  WithLp.toLp 2 fun w ↦ Kraus.rectangularEval b (fun k : Fin N ↦ A k.val) w
    (Fin.cast hleft.symm 0) (Fin.cast hright.symm 0)

/-- The coefficients of the actual scalar-endpoint open chain.
Source: PGVWC07, Theorem 9, lines 1195–1205. -/
@[simp] theorem obcScalarState_apply (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    (N : ℕ) (hleft : b 0 = 1) (hright : b N = 1) (w : Fin N → Fin d) :
    obcScalarState b A N hleft hright w =
      Kraus.rectangularEval b (fun k : Fin N ↦ A k.val) w
        (Fin.cast hleft.symm 0) (Fin.cast hright.symm 0) := rfl

/-- Sitewise canonical row-isometry and singleton endpoint bonds normalize the
actual open-chain state. This proves nonvanishing rather than assuming it.
Source: PGVWC07, canonical form and Theorem 9 proof, lines 1195–1237. -/
theorem norm_obcScalarState_eq_one (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    (N : ℕ) (hleft : b 0 = 1) (hright : b N = 1)
    (hA : ∀ k < N, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (b k)) _ ℂ)) :
    ‖obcScalarState b A N hleft hright‖ = 1 := by
  classical
  let _ : Unique (Fin (b N)) := Equiv.unique (finCongr hright)
  let l : Fin (b 0) := Fin.cast hleft.symm 0
  let r : Fin (b N) := Fin.cast hright.symm 0
  have hrow := obc_rectangularEval_row_isometry b A N hA
  have hd : (default : Fin (b N)) = r := Subsingleton.elim _ _
  have hentry : ∑ w : Fin N → Fin d,
      ‖Kraus.rectangularEval b (fun k : Fin N ↦ A k.val) w l r‖ ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix (Fin (b 0)) (Fin (b 0)) ℂ ↦ (M l l).re) hrow
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_unique, hd, Complex.re_sum, Matrix.one_apply_eq, Complex.one_re] at h
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using h
  have hsq : ‖obcScalarState b A N hleft hright‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact hentry
  nlinarith [norm_nonneg (obcScalarState b A N hleft hright)]

/-- Every vector in the actual open parent-Hamiltonian kernel is a scalar multiple
of the represented state. Pair sections are derived from that kernel equation.
Source: PGVWC07, Theorem 9 proof, equation unique-OBC and scalar endpoints,
lines 1212–1237. -/
theorem exists_smul_obcScalarState_of_obcParentHamiltonian_apply_eq_zero (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N : ℕ} (hN : 2 ≤ N) (hleft : b 0 = 1) (hright : b N = 1)
    (hA : ∀ k < N, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (b k)) _ ℂ))
    (hC1 : ∀ k < N, Submodule.span ℂ (Set.range (A k)) = ⊤)
    (ψ : EuclideanSpace ℂ (Fin N → Fin d)) (hzero : obcParentHamiltonian b A N ψ = 0) :
    ∃ c : ℂ, ψ = c • obcScalarState b A N hleft hright := by
  classical
  let f : List (Fin d) → ℂ := Function.extend List.ofFn (fun w ↦ ψ w) 0
  have hf (w : Fin N → Fin d) : f (List.ofFn w) = ψ w :=
    List.ofFn_injective.extend_apply (fun w ↦ ψ w) 0 w
  have hpair := obcParentHamiltonian_pair_sections_of_apply_eq_zero b A ψ f hf hzero
  obtain ⟨c, hc⟩ := obc_scalar_reconstruction_of_adjacent_pair_sections
    b A hN hleft hright hA hC1 f hpair
  refine ⟨c, ?_⟩
  ext w
  simpa only [hf, PiLp.smul_apply, smul_eq_mul, obcScalarState_apply] using hc w

/-- With singleton endpoint bonds, the unit boundary trace state is exactly the
actual open-chain state, with no endpoint normalization factor.
Source: PGVWC07, Theorem 9 proof, scalar boundary at lines 1233–1237. -/
theorem obcBoundaryState_one_eq_obcScalarState (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    (N : ℕ) (hleft : b 0 = 1) (hright : b N = 1) :
    obcBoundaryState b A N (fun _ _ ↦ 1) = obcScalarState b A N hleft hright := by
  classical
  let _ : Unique (Fin (b 0)) := Equiv.unique (finCongr hleft)
  let _ : Unique (Fin (b N)) := Equiv.unique (finCongr hright)
  ext w
  change Matrix.trace (Matrix.of (fun _ _ ↦ (1 : ℂ)) *
    Kraus.rectangularEval b (fun k : Fin N ↦ A k.val) w) = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_unique, one_mul,
    obcScalarState_apply]
  congr 1

/-- The actual canonical open-chain state has zero energy for its actual parent
Hamiltonian. No local annihilation equation is supplied as a hypothesis.
Source: PGVWC07, Theorem 9, lines 1195–1217. -/
theorem obcParentHamiltonian_apply_obcScalarState (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    (N : ℕ) (hleft : b 0 = 1) (hright : b N = 1) :
    obcParentHamiltonian b A N (obcScalarState b A N hleft hright) = 0 := by
  rw [← obcBoundaryState_one_eq_obcScalarState b A N hleft hright]
  exact obcParentHamiltonian_apply_obcBoundaryState b A N _

/-- The actual varying-bond open parent Hamiltonian has exactly the represented
state line as its kernel, at every length with an adjacent pair. Sitewise C1,
canonical row-isometry and singleton endpoints are the source's data; no kernel,
local section, boundary reconstruction or ground-state supplier is assumed.
Source: PGVWC07, Theorem 9 and proof, lines 1195–1237. -/
theorem ker_obcParentHamiltonian_eq_span (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N : ℕ} (hN : 2 ≤ N) (hleft : b 0 = 1) (hright : b N = 1)
    (hA : ∀ k < N, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (b k)) _ ℂ))
    (hC1 : ∀ k < N, Submodule.span ℂ (Set.range (A k)) = ⊤) :
    LinearMap.ker (obcParentHamiltonian b A N) =
      Submodule.span ℂ {obcScalarState b A N hleft hright} := by
  ext ψ
  constructor
  · intro hψ
    obtain ⟨c, rfl⟩ := exists_smul_obcScalarState_of_obcParentHamiltonian_apply_eq_zero
      b A hN hleft hright hA hC1 ψ hψ
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · intro hψ
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hψ
    change obcParentHamiltonian b A N (c • obcScalarState b A N hleft hright) = 0
    rw [map_smul, obcParentHamiltonian_apply_obcScalarState b A N hleft hright, smul_zero]

/-- The actual varying-bond open parent has a one-dimensional ground kernel.
Its spanning state is proved normalized from the original canonical equations.
Source: PGVWC07, Theorem 9 and proof, lines 1195–1237. -/
theorem finrank_ker_obcParentHamiltonian_eq_one (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N : ℕ} (hN : 2 ≤ N) (hleft : b 0 = 1) (hright : b N = 1)
    (hA : ∀ k < N, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (b k)) _ ℂ))
    (hC1 : ∀ k < N, Submodule.span ℂ (Set.range (A k)) = ⊤) :
    Module.finrank ℂ (LinearMap.ker (obcParentHamiltonian b A N)) = 1 := by
  rw [ker_obcParentHamiltonian_eq_span b A hN hleft hright hA hC1]
  apply finrank_span_singleton
  intro hzero
  have hnorm := norm_obcScalarState_eq_one b A N hleft hright hA
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

end Matrix
