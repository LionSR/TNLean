/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingForm
import TNLean.MPS.MPDO.TopologicalMultiplicityEnergy
import TNLean.MPS.MPDO.TopologicalTerminalSpectral

/-!
# Commuting Gibbs Hamiltonian for the topological MPDO form

The positive multiplicity factor in the recursive normal form is a product of
strictly positive one-site diagonal weights.  This file writes that product as
the Gibbs factor of a translation-invariant commuting nearest-neighbor
Hamiltonian and combines it with the terminal spectral projectors.

The two-site local term depends only on its first site.  Its periodic translates
therefore sum to the one-site logarithms, while still giving the two-site
presentation used in the source definition of a nearest-neighbor Hamiltonian.

All Hamiltonians and spectral projectors constructed here act on the retained
vertical coordinates.  The exact sitewise reconstruction of the physical MPDO
does not yet give a physical-space Hamiltonian or physical-space projectors.
See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 1013--1016
-/

open scoped Matrix BigOperators Kronecker ComplexOrder

noncomputable section

namespace MPOTensor

variable {d N : ℕ}

/-- Embedding a diagonal two-site operator which depends only on its first
site gives the corresponding diagonal one-site operator on the periodic
chain.

Source: arXiv:1606.00608, Definition 4.8, lines 831--847, and the
translation-invariant Hamiltonian at lines 1013--1016. -/
theorem embedLocalOperator_twoSite_first_diagonal
    (hN : 2 ≤ N) (i : Fin N) (f : Fin d → ℂ) :
    embedLocalOperator (d := d) 2 N hN i
        (Matrix.diagonal fun x : Fin 2 → Fin d ↦
          f (x ⟨0, by omega⟩)) =
      Matrix.diagonal fun σ : Fin N → Fin d ↦ f (σ i) := by
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    simp only [embedLocalOperator_apply, Matrix.diagonal_apply_eq]
    rw [if_pos]
    · congr 2
      apply Fin.ext
      simp [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt]
    · exact MPSTensor.replaceWindow_extractWindow 2 hN i σ
  · simp only [embedLocalOperator_apply]
    by_cases hAgree : AgreesOutsideWindow (d := d) 2 hN i σ τ
    · rw [if_pos hAgree]
      have hWindow :
          MPSTensor.extractWindow 2 i σ ≠
            MPSTensor.extractWindow 2 i τ := by
        intro hWindow
        have hτ :
            MPSTensor.replaceWindow 2 hN i τ
                (MPSTensor.extractWindow 2 i σ) = τ := by
          rw [hWindow]
          exact MPSTensor.replaceWindow_extractWindow 2 hN i τ
        exact hστ (hAgree.symm.trans hτ)
      simp [hWindow, hστ]
    · rw [if_neg hAgree]
      simp [hστ]

end MPOTensor

namespace MPOTensor.BNTFusionTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-- The terminal spectral family has at most the physical one-site dimension.

Source: arXiv:1606.00608, the range `i = 1, ..., d` in the theorem at
lines 1013--1016.  The proof embeds one terminal mode per BNT label into a
positive multiplicity copy and then uses the rank of the vertical
coisometry. -/
theorem terminalSpectralIndex_card_le_physicalDim
    (H : BNTFusionTensorClause M) :
    Fintype.card H.TerminalSpectralIndex ≤ d := by
  let e := verticalCopyCoordinateEquiv H.bondDim H.multiplicity
  let g : H.TerminalSpectralIndex →
      ((p : H.VerticalCopy) × Fin (H.bondDim p.1)) :=
    fun s ↦ ⟨⟨s.1, ⟨0, H.multiplicity_pos s.1⟩⟩, s.2⟩
  let f : H.TerminalSpectralIndex → Fin H.verticalRetainedDim :=
    fun s ↦ e.symm (g s)
  have hf : Function.Injective f := by
    apply e.symm.injective.comp
    intro s t hst
    rcases s with ⟨α, k⟩
    rcases t with ⟨β, l⟩
    simp only [g] at hst
    cases hst
    rfl
  have hterminal :
      Fintype.card H.TerminalSpectralIndex ≤ H.verticalRetainedDim := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  have hretained : H.verticalRetainedDim ≤ d := by
    calc
      H.verticalRetainedDim =
          (1 : Matrix (Fin H.verticalRetainedDim)
            (Fin H.verticalRetainedDim) ℂ).rank := by
        rw [Matrix.rank_one, Fintype.card_fin]
      _ = (H.verticalCoisometry * H.verticalCoisometryᴴ).rank := by
        rw [H.coisometry]
      _ ≤ H.verticalCoisometry.rank :=
        Matrix.rank_mul_le_left H.verticalCoisometry
          H.verticalCoisometryᴴ
      _ ≤ d := by
        simpa only [Fintype.card_fin] using
          Matrix.rank_le_card_width H.verticalCoisometry
  exact hterminal.trans hretained

/-- Embed the terminal spectral sectors into the paper's `d`-element
single-site index.

Source: arXiv:1606.00608, the range `i = 1, ..., d` at
lines 1013--1016. -/
def terminalSpectralEmbedding (H : BNTFusionTensorClause M) :
    H.TerminalSpectralIndex ↪ Fin d :=
  (Fintype.equivFin H.TerminalSpectralIndex).toEmbedding.trans
    (Fin.castLEEmb H.terminalSpectralIndex_card_le_physicalDim)

private theorem sum_extend_embedding_zero
    {S T A : Type*} [Fintype S] [Fintype T]
    [AddCommMonoid A]
    (e : S ↪ T) (f : S → A) :
    ∑ t : T, Function.extend e f (fun _ ↦ 0) t = ∑ s : S, f s := by
  classical
  calc
    ∑ t : T, Function.extend e f (fun _ ↦ 0) t =
        ∑ t ∈ Finset.univ.image e,
          Function.extend e f (fun _ ↦ 0) t := by
      symm
      apply Finset.sum_subset (Finset.image_subset_iff.mpr fun _ _ ↦
        Finset.mem_univ _)
      intro t _ ht
      rw [Function.extend_apply']
      intro h
      obtain ⟨s, hs⟩ := h
      exact ht (Finset.mem_image.mpr
        ⟨s, Finset.mem_univ _, hs⟩)
    _ = ∑ s : S, Function.extend e f (fun _ ↦ 0) (e s) := by
      rw [Finset.sum_image e.injective.injOn]
    _ = ∑ s : S, f s := by
      apply Finset.sum_congr rfl
      intro s _
      exact e.injective.extend_apply f (fun _ ↦ 0) s

private theorem sum_extend_smul_mul_zero
    {S T I : Type*} [Fintype S] [Fintype T] [Fintype I]
    (e : S ↪ T) (a : S → ℂ) (P : S → Matrix I I ℂ)
    (G : Matrix I I ℂ) :
    ∑ t : T,
        Function.extend e a (fun _ ↦ 0) t •
          (Function.extend e P (fun _ ↦ 0) t * G) =
      ∑ s : S, a s • (P s * G) := by
  classical
  let f : S → Matrix I I ℂ := fun s ↦ a s • (P s * G)
  have hfun :
      (fun t : T ↦
        Function.extend e a (fun _ ↦ 0) t •
          (Function.extend e P (fun _ ↦ 0) t * G)) =
        Function.extend e f (fun _ ↦ 0) := by
    funext t
    by_cases ht : ∃ s, e s = t
    · obtain ⟨s, rfl⟩ := ht
      simp only [e.injective.extend_apply, f]
    · rw [Function.extend_apply' _ _ _ ht,
        Function.extend_apply' _ _ _ ht,
        Function.extend_apply' _ _ _ ht]
      simp
  rw [hfun, sum_extend_embedding_zero e f]

/-- The all-label multiplicity factor is the diagonal product of its
one-site weights.

Source: arXiv:1606.00608, lines 999--1002 and 1013--1016.

**Scope restriction (retained vertical coordinates):** This factor acts on
the retained nonzero vertical sectors.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem topologicalMultiplicityWeightFactorSucc_eq_diagonal
    (H : BNTFusionTensorClause M) (N : ℕ) :
    H.topologicalMultiplicityWeightFactorSucc N =
      Matrix.diagonal fun x :
          Fin (N + 1) → Fin H.verticalRetainedDim ↦
        ∏ n, H.retainedMultiplicityWeightEntry (x n) := by
  ext x y
  obtain ⟨⟨p, u⟩, rfl⟩ :=
    (H.verticalCopyChainEquiv N).symm.surjective x
  obtain ⟨⟨q, v⟩, rfl⟩ :=
    (H.verticalCopyChainEquiv N).symm.surjective y
  simp only [topologicalMultiplicityWeightFactorSucc,
    verticalMultiplicityChainWeight, retainedMultiplicityWeightEntry,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]
  by_cases hpq : p = q
  · subst q
    rw [Matrix.blockDiagonal'_apply_eq]
    by_cases huv : u = v
    · subst v
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        Matrix.diagonal_apply_eq, if_true, mul_one]
      apply Finset.prod_congr rfl
      intro n _
      rw [H.verticalCopyChainEquiv_symm_apply]
      rw [Equiv.apply_symm_apply]
    · have hSigma :
          (⟨p, u⟩ : H.VerticalCopyChainIndex N) ≠ ⟨p, v⟩ := by
        intro h
        cases h
        exact huv rfl
      have hChain :
          (H.verticalCopyChainEquiv N).symm ⟨p, u⟩ ≠
            (H.verticalCopyChainEquiv N).symm ⟨p, v⟩ :=
        (H.verticalCopyChainEquiv N).symm.injective.ne hSigma
      rw [Matrix.smul_apply, Matrix.one_apply, if_neg huv, smul_zero,
        Matrix.diagonal_apply_ne _ hChain]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpq,
      Matrix.diagonal_apply_ne]
    intro h
    exact hpq (Sigma.mk.inj_iff.mp
      ((H.verticalCopyChainEquiv N).symm.injective h)).1

/-- The translation-invariant two-site term.  It acts as the logarithmic
one-site energy on the first site and as the identity on the second.

Source: arXiv:1606.00608, the nearest-neighbor Hamiltonian at
lines 1013--1016.

**Scope restriction (retained vertical coordinates):** This local term acts
on the retained nonzero vertical sectors.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
def topologicalGibbsLocalTerm (H : BNTFusionTensorClause M) :
    Matrix (Fin 2 → Fin H.verticalRetainedDim)
      (Fin 2 → Fin H.verticalRetainedDim) ℂ :=
  Matrix.diagonal fun x ↦
    (H.retainedMultiplicityEnergyEntry (x ⟨0, by omega⟩) : ℂ)

/-- The translation-invariant two-site Gibbs term is Hermitian.

Source: arXiv:1606.00608, the nearest-neighbor Hamiltonian at
lines 1013--1016.

**Scope restriction (retained vertical coordinates):** This theorem concerns
the retained local term.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem topologicalGibbsLocalTerm_isHermitian
    (H : BNTFusionTensorClause M) :
    H.topologicalGibbsLocalTerm.IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext x
  simp [retainedMultiplicityEnergyEntry]

/-- The periodic translation-invariant nearest-neighbor Hamiltonian on a
retained chain of length `N + 2`.

Source: arXiv:1606.00608, `H_N = sum_i h_{i,i+1}` at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** This Hamiltonian acts
on the retained nonzero vertical sectors.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** Definition
4.8 defines the local operator on two spins, so the present source-facing
construction starts at length two.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
def topologicalGibbsHamiltonianSuccSucc
    (H : BNTFusionTensorClause M) (N : ℕ) :
    Matrix (Fin (N + 2) → Fin H.verticalRetainedDim)
      (Fin (N + 2) → Fin H.verticalRetainedDim) ℂ :=
  ∑ i : Fin (N + 2),
    MPOTensor.embedLocalOperator 2 (N + 2) (by omega) i
      H.topologicalGibbsLocalTerm

/-- The terminal eigenvalue family, zero-padded to the paper's `d`-element
index.

Source: arXiv:1606.00608, the coefficients `lambda_i` with
`i = 1, ..., d` at lines 1013--1016. -/
def physicalIndexedTerminalEigenvalue
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (i : Fin d) : ℝ :=
  Function.extend H.terminalSpectralEmbedding
    (H.terminalEigenvalue hM) (fun _ ↦ 0) i

/-- The transported terminal projectors, zero-padded to the paper's
`d`-element index.

Source: arXiv:1606.00608, the projectors `P_i^(N)` with
`i = 1, ..., d` at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** The index is padded
to the physical one-site dimension, but each projector still acts on the
retained chain.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
def physicalIndexedTopologicalSpectralProjectorSucc
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (N : ℕ) (i : Fin d) :
    Matrix (Fin (N + 1) → Fin H.verticalRetainedDim)
      (Fin (N + 1) → Fin H.verticalRetainedDim) ℂ :=
  Function.extend H.terminalSpectralEmbedding
    (H.topologicalSpectralProjectorSucc hM N) (fun _ ↦ 0) i

/-- The zero-padded terminal eigenweights remain nonnegative.

Source: arXiv:1606.00608, lines 1010--1016. -/
theorem physicalIndexedTerminalEigenvalue_nonneg
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (i : Fin d) :
    0 ≤ H.physicalIndexedTerminalEigenvalue hM i := by
  classical
  by_cases hi : ∃ s, H.terminalSpectralEmbedding s = i
  · obtain ⟨s, rfl⟩ := hi
    simpa only [physicalIndexedTerminalEigenvalue,
      H.terminalSpectralEmbedding.injective.extend_apply] using
      H.terminalEigenvalue_nonneg hM s
  · rw [physicalIndexedTerminalEigenvalue,
      Function.extend_apply' _ _ _ hi]

/-- Every zero-padded physical-index retained projector is an orthogonal projection.

Source: arXiv:1606.00608, lines 1010--1016.

**Scope restriction (retained vertical coordinates):** These projections act
on the retained chain.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem physicalIndexedTopologicalSpectralProjectorSucc_isOrthogonalProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    (N : ℕ) (i : Fin d) :
    (H.physicalIndexedTopologicalSpectralProjectorSucc hM N i).IsHermitian ∧
      H.physicalIndexedTopologicalSpectralProjectorSucc hM N i *
          H.physicalIndexedTopologicalSpectralProjectorSucc hM N i =
        H.physicalIndexedTopologicalSpectralProjectorSucc hM N i := by
  classical
  by_cases hi : ∃ s, H.terminalSpectralEmbedding s = i
  · obtain ⟨s, rfl⟩ := hi
    simpa only [physicalIndexedTopologicalSpectralProjectorSucc,
      H.terminalSpectralEmbedding.injective.extend_apply] using
      H.topologicalSpectralProjectorSucc_isOrthogonalProjection
        hM hLI N s
  · rw [physicalIndexedTopologicalSpectralProjectorSucc,
      Function.extend_apply' _ _ _ hi]
    exact ⟨Matrix.isHermitian_zero, by simp⟩

/-- Every translated local Hamiltonian term is diagonal in retained
coordinates.

Source: arXiv:1606.00608, the translated local terms at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** These translated
terms act on the retained chain.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem topologicalGibbsBondSuccSucc_eq_diagonal
    (H : BNTFusionTensorClause M) (N : ℕ) (i : Fin (N + 2)) :
    MPOTensor.embedLocalOperator 2 (N + 2) (by omega) i
        H.topologicalGibbsLocalTerm =
      Matrix.diagonal fun σ :
          Fin (N + 2) → Fin H.verticalRetainedDim ↦
        (H.retainedMultiplicityEnergyEntry (σ i) : ℂ) := by
  unfold topologicalGibbsLocalTerm
  simpa only using
    (MPOTensor.embedLocalOperator_twoSite_first_diagonal
      (d := H.verticalRetainedDim) (by omega) i
      (fun r ↦ (H.retainedMultiplicityEnergyEntry r : ℂ)))

/-- Periodic translates of the local Hamiltonian term commute pairwise.

Source: arXiv:1606.00608, `[h_{i-1,i},h_{i,i+1}] = 0` at
lines 1013--1016.

**Scope restriction (retained vertical coordinates):** The commutation
statement concerns translated terms on the retained chain.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem topologicalGibbsBondSuccSucc_commute
    (H : BNTFusionTensorClause M) (N : ℕ)
    (i j : Fin (N + 2)) :
    Commute
      (MPOTensor.embedLocalOperator 2 (N + 2) (by omega) i
        H.topologicalGibbsLocalTerm)
      (MPOTensor.embedLocalOperator 2 (N + 2) (by omega) j
        H.topologicalGibbsLocalTerm) := by
  rw [H.topologicalGibbsBondSuccSucc_eq_diagonal N i,
    H.topologicalGibbsBondSuccSucc_eq_diagonal N j]
  exact Matrix.commute_diagonal _ _

/-- The retained periodic Hamiltonian is diagonal, with one logarithmic energy per
site.

Source: arXiv:1606.00608, `H_N = sum_i h_{i,i+1}` at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** This diagonal formula
is for the retained Hamiltonian.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem topologicalGibbsHamiltonianSuccSucc_eq_diagonal
    (H : BNTFusionTensorClause M) (N : ℕ) :
    H.topologicalGibbsHamiltonianSuccSucc N =
      Matrix.diagonal fun σ :
          Fin (N + 2) → Fin H.verticalRetainedDim ↦
        ∑ i, (H.retainedMultiplicityEnergyEntry (σ i) : ℂ) := by
  unfold topologicalGibbsHamiltonianSuccSucc
  simp_rw [H.topologicalGibbsBondSuccSucc_eq_diagonal]
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq]
  · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hστ]

/-- The exponential of the negative retained Hamiltonian is exactly the
multiplicity-weight factor.

Source: arXiv:1606.00608, the identification of `e^{-H_N}` in the
decomposition at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** This exponential
identity is on the retained chain.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** The source
local term is defined on two spins.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem exp_neg_topologicalGibbsHamiltonianSuccSucc
    (H : BNTFusionTensorClause M) (N : ℕ) :
    NormedSpace.exp (-H.topologicalGibbsHamiltonianSuccSucc N) =
      H.topologicalMultiplicityWeightFactorSucc (N + 1) := by
  rw [H.topologicalGibbsHamiltonianSuccSucc_eq_diagonal,
    Matrix.diagonal_neg, Matrix.exp_diagonal,
    H.topologicalMultiplicityWeightFactorSucc_eq_diagonal]
  congr 1
  funext σ
  rw [Pi.coe_exp]
  change NormedSpace.exp
      (-(∑ i, (H.retainedMultiplicityEnergyEntry (σ i) : ℂ))) =
    ∏ n, H.retainedMultiplicityWeightEntry (σ n)
  rw [← Finset.sum_neg_distrib, NormedSpace.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  have hentry := congrArg
    (fun A : Matrix (Fin H.verticalRetainedDim)
        (Fin H.verticalRetainedDim) ℂ ↦ A (σ i) (σ i))
    H.exp_neg_retainedMultiplicityEnergy
  simpa [retainedMultiplicityEnergy, retainedMultiplicityOperator,
    Matrix.exp_diagonal] using hentry

/-- Every transported terminal spectral projector commutes with the retained
Gibbs factor.

Source: arXiv:1606.00608, `[P_i,e^{-H}] = 0` at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** Both factors act on
the retained chain.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** The source
local term is defined on two spins.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem topologicalSpectralProjectorSucc_commutes_gibbsFactor
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (N : ℕ) (s : H.TerminalSpectralIndex) :
    H.topologicalSpectralProjectorSucc hM (N + 1) s *
        NormedSpace.exp (-H.topologicalGibbsHamiltonianSuccSucc N) =
      NormedSpace.exp (-H.topologicalGibbsHamiltonianSuccSucc N) *
        H.topologicalSpectralProjectorSucc hM (N + 1) s := by
  rw [H.exp_neg_topologicalGibbsHamiltonianSuccSucc]
  exact
    (H.topologicalMultiplicityWeightFactorSucc_commutes_spectralProjector
      hM (N + 1) s).symm

/-- Every zero-padded physical-index projector commutes with the retained
Gibbs factor.

Source: arXiv:1606.00608, `[P_i,e^{-H}] = 0` for
`i = 1, ..., d` at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** The physical index
pads a family of projectors that still acts on the retained chain.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** The source
local term is defined on two spins.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem physicalIndexedTopologicalSpectralProjectorSucc_commutes_gibbsFactor
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (N : ℕ) (i : Fin d) :
    H.physicalIndexedTopologicalSpectralProjectorSucc hM (N + 1) i *
        NormedSpace.exp (-H.topologicalGibbsHamiltonianSuccSucc N) =
      NormedSpace.exp (-H.topologicalGibbsHamiltonianSuccSucc N) *
        H.physicalIndexedTopologicalSpectralProjectorSucc hM
          (N + 1) i := by
  classical
  by_cases hi : ∃ s, H.terminalSpectralEmbedding s = i
  · obtain ⟨s, rfl⟩ := hi
    simpa only [physicalIndexedTopologicalSpectralProjectorSucc,
      H.terminalSpectralEmbedding.injective.extend_apply] using
      H.topologicalSpectralProjectorSucc_commutes_gibbsFactor hM N s
  · rw [physicalIndexedTopologicalSpectralProjectorSucc,
      Function.extend_apply' _ _ _ hi]
    simp

/-- The retained recursive density operator is the terminal-eigenvalue
weighted sum of its topological projectors times the Gibbs factor.

Source: arXiv:1606.00608, the density formula at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** This equality is for
the retained density operator.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** The source
local term is defined on two spins.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem topologicalDensityOperatorSucc_eq_sum_projector_mul_gibbsFactor
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (N : ℕ) :
    H.topologicalDensityOperatorSucc (N + 1) =
      ∑ s : H.TerminalSpectralIndex,
        (H.terminalEigenvalue hM s : ℂ) •
          (H.topologicalSpectralProjectorSucc hM (N + 1) s *
            NormedSpace.exp
              (-H.topologicalGibbsHamiltonianSuccSucc N)) := by
  rw [H.topologicalDensityOperatorSucc_eq_sum_terminalSpectralProjector
    hM (N + 1)]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [H.exp_neg_topologicalGibbsHamiltonianSuccSucc]
  exact
    H.topologicalMultiplicityWeightFactorSucc_commutes_spectralProjector
      hM (N + 1) s

/-- The retained density formula with exactly `d` summands, obtained by
zero-padding the terminal spectral family.

Source: arXiv:1606.00608, the displayed density formula with
`i = 1, ..., d` at lines 1013--1016.

**Scope restriction (retained vertical coordinates):** This equality is for
the retained density operator, although the spectral family is padded to
`Fin d`.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** The source
local term is defined on two spins.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem topologicalDensityOperatorSucc_eq_sum_physicalIndexedProjector_mul_gibbsFactor
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (N : ℕ) :
    H.topologicalDensityOperatorSucc (N + 1) =
      ∑ i : Fin d,
        (H.physicalIndexedTerminalEigenvalue hM i : ℂ) •
          (H.physicalIndexedTopologicalSpectralProjectorSucc
              hM (N + 1) i *
            NormedSpace.exp
              (-H.topologicalGibbsHamiltonianSuccSucc N)) := by
  rw [H.topologicalDensityOperatorSucc_eq_sum_projector_mul_gibbsFactor
    hM N]
  have hCoe (i : Fin d) :
      (H.physicalIndexedTerminalEigenvalue hM i : ℂ) =
        Function.extend H.terminalSpectralEmbedding
          (fun s ↦ (H.terminalEigenvalue hM s : ℂ))
          (fun _ ↦ 0) i := by
    classical
    by_cases hi : ∃ s, H.terminalSpectralEmbedding s = i
    · obtain ⟨s, rfl⟩ := hi
      simp only [physicalIndexedTerminalEigenvalue,
        H.terminalSpectralEmbedding.injective.extend_apply]
    · rw [physicalIndexedTerminalEigenvalue,
        Function.extend_apply' _ _ _ hi,
        Function.extend_apply' _ _ _ hi]
      exact Complex.ofReal_zero
  simp_rw [hCoe]
  exact (sum_extend_smul_mul_zero
    H.terminalSpectralEmbedding
    (fun s ↦ (H.terminalEigenvalue hM s : ℂ))
    (H.topologicalSpectralProjectorSucc hM (N + 1))
    (NormedSpace.exp
      (-H.topologicalGibbsHamiltonianSuccSucc N))).symm

/-- Applying the adjoint sitewise vertical map to the Gibbs/projector sum
reconstructs the physical MPDO density operator exactly.

Source: arXiv:1606.00608, the local-equivalence statement at line 999 and
the density formula at lines 1013--1016.

**Local fix (rectangular vertical map):** Exact physical reconstruction uses
the adjoint of the retained-row coisometry, rather than treating that
rectangular matrix as a square unitary.  See
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

**Scope restriction (retained vertical coordinates):** The Hamiltonian and
projectors inside the sitewise map act on the retained chain.  This theorem
does not construct a physical-space Gibbs factor.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** The source
local term is defined on two spins.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem singleKrausMap_gibbsDecomposition_eq_mpo
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (N : ℕ) :
    singleKrausMap
        (sitewisePhysicalMatrix H.verticalCoisometryᴴ (N + 2))
        (∑ s : H.TerminalSpectralIndex,
          (H.terminalEigenvalue hM s : ℂ) •
            (H.topologicalSpectralProjectorSucc hM (N + 1) s *
              NormedSpace.exp
                (-H.topologicalGibbsHamiltonianSuccSucc N))) =
      mpo M (N + 2) := by
  rw [←
    H.topologicalDensityOperatorSucc_eq_sum_projector_mul_gibbsFactor
      hM N]
  exact
    H.singleKrausMap_conjTranspose_verticalCoisometry_topologicalDensityOperatorSucc_eq_mpo
      (N + 1)

/-- The zero-padded `d`-term Gibbs/projector sum reconstructs the physical
MPDO density operator exactly.

Source: arXiv:1606.00608, the local-equivalence statement at line 999 and
the `d`-term density formula at lines 1013--1016.

**Local fix (rectangular vertical map):** Exact physical reconstruction uses
the adjoint retained-row map.  See
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

**Scope restriction (retained vertical coordinates):** The Hamiltonian and
projectors inside the sitewise map act on the retained chain.  This theorem
does not construct a physical-space Gibbs factor.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** The source
local term is defined on two spins.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem singleKrausMap_physicalIndexedGibbsDecomposition_eq_mpo
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (N : ℕ) :
    singleKrausMap
        (sitewisePhysicalMatrix H.verticalCoisometryᴴ (N + 2))
        (∑ i : Fin d,
          (H.physicalIndexedTerminalEigenvalue hM i : ℂ) •
            (H.physicalIndexedTopologicalSpectralProjectorSucc
                hM (N + 1) i *
              NormedSpace.exp
                (-H.topologicalGibbsHamiltonianSuccSucc N))) =
      mpo M (N + 2) := by
  rw [←
    H.topologicalDensityOperatorSucc_eq_sum_physicalIndexedProjector_mul_gibbsFactor
      hM N]
  exact
    H.singleKrausMap_conjTranspose_verticalCoisometry_topologicalDensityOperatorSucc_eq_mpo
      (N + 1)

/-- The commuting nearest-neighbor Gibbs conclusion for the retained
topological normal form.

The same two-site local term is translated around every periodic chain.  Its
translates commute, its negative exponential is the multiplicity factor, each
terminal spectral projector commutes with that Gibbs factor, and their
eigenvalue-weighted sum is the retained density operator.

Source: arXiv:1606.00608, lines 1013--1016.

**Scope restriction (retained vertical coordinates):** This predicate
describes the Gibbs formula on the retained chain together with exact
sitewise reconstruction of the physical MPDO.  It does not assert a
physical-space Hamiltonian or physical-space projectors.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** Definition
4.8 defines the local term on two spins, so this predicate covers lengths
`N + 2`.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
def HasTopologicalGibbsDecomposition (H : BNTFusionTensorClause M)
    (hM : IsMPDO M) : Prop :=
  Fintype.card H.TerminalSpectralIndex ≤ d ∧
    H.topologicalGibbsLocalTerm.IsHermitian ∧
    ∀ N : ℕ,
      (∀ i j : Fin (N + 2),
        Commute
          (MPOTensor.embedLocalOperator 2 (N + 2) (by omega) i
            H.topologicalGibbsLocalTerm)
          (MPOTensor.embedLocalOperator 2 (N + 2) (by omega) j
            H.topologicalGibbsLocalTerm)) ∧
      NormedSpace.exp (-H.topologicalGibbsHamiltonianSuccSucc N) =
          H.topologicalMultiplicityWeightFactorSucc (N + 1) ∧
      (∀ i : Fin d,
        0 ≤ H.physicalIndexedTerminalEigenvalue hM i ∧
          ((H.physicalIndexedTopologicalSpectralProjectorSucc
              hM (N + 1) i).IsHermitian ∧
            H.physicalIndexedTopologicalSpectralProjectorSucc
                hM (N + 1) i *
              H.physicalIndexedTopologicalSpectralProjectorSucc
                hM (N + 1) i =
              H.physicalIndexedTopologicalSpectralProjectorSucc
                hM (N + 1) i) ∧
          H.physicalIndexedTopologicalSpectralProjectorSucc
                hM (N + 1) i *
              NormedSpace.exp
                (-H.topologicalGibbsHamiltonianSuccSucc N) =
            NormedSpace.exp
                (-H.topologicalGibbsHamiltonianSuccSucc N) *
              H.physicalIndexedTopologicalSpectralProjectorSucc
                hM (N + 1) i) ∧
      H.topologicalDensityOperatorSucc (N + 1) =
        ∑ i : Fin d,
          (H.physicalIndexedTerminalEigenvalue hM i : ℂ) •
            (H.physicalIndexedTopologicalSpectralProjectorSucc
                hM (N + 1) i *
              NormedSpace.exp
                (-H.topologicalGibbsHamiltonianSuccSucc N)) ∧
      singleKrausMap
          (sitewisePhysicalMatrix H.verticalCoisometryᴴ (N + 2))
          (∑ i : Fin d,
            (H.physicalIndexedTerminalEigenvalue hM i : ℂ) •
              (H.physicalIndexedTopologicalSpectralProjectorSucc
                  hM (N + 1) i *
                NormedSpace.exp
                  (-H.topologicalGibbsHamiltonianSuccSucc N))) =
        mpo M (N + 2)

/-- A chosen BNT fusion clause has the retained commuting nearest-neighbor
Gibbs decomposition.

Source: arXiv:1606.00608, lines 1013--1016.

**Scope restriction (retained vertical coordinates):** The conclusion is the
retained-coordinate Gibbs formula and its exact sitewise reconstruction.  See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** Definition
4.8 defines the local term on two spins.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem hasTopologicalGibbsDecomposition
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent) :
    H.HasTopologicalGibbsDecomposition hM := by
  refine ⟨H.terminalSpectralIndex_card_le_physicalDim,
    H.topologicalGibbsLocalTerm_isHermitian, fun N ↦ ?_⟩
  refine ⟨H.topologicalGibbsBondSuccSucc_commute N,
    H.exp_neg_topologicalGibbsHamiltonianSuccSucc N, ?_,
    H.topologicalDensityOperatorSucc_eq_sum_physicalIndexedProjector_mul_gibbsFactor
      hM N,
    H.singleKrausMap_physicalIndexedGibbsDecomposition_eq_mpo hM N⟩
  intro i
  exact ⟨H.physicalIndexedTerminalEigenvalue_nonneg hM i,
    H.physicalIndexedTopologicalSpectralProjectorSucc_isOrthogonalProjection
      hM hLI (N + 1) i,
    H.physicalIndexedTopologicalSpectralProjectorSucc_commutes_gibbsFactor
      hM N i⟩

end MPOTensor.BNTFusionTensorClause

namespace MPOTensor

variable {d D : ℕ}

/-- **Retained-coordinate Gibbs decomposition for a length-independent RFP MPDO.**

The BNT fusion clause, positive multiplicity weights, local Hamiltonian,
terminal eigenweights, and topological projectors are all selected or
constructed internally.  The conclusion includes the preceding all-label
density decomposition, factor commutator, terminal spectral refinement, and
the retained commuting nearest-neighbor Gibbs formula.

**Scope restriction (BNT-refined horizontal form):** This theorem assumes
normalized BNT-refined horizontal form (`IsHorizontalCF`), which is stronger
than the literal CPSV canonical form.

Source: arXiv:1606.00608, lines 999--1016.

**Scope restriction (retained vertical coordinates):** The Gibbs
Hamiltonian and projectors in the conclusion act on the retained vertical
chain; the physical MPDO is obtained only by exact sitewise reconstruction.
See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** Definition
4.8 defines its local term on two spins, while the printed theorem does not
state a separate length-one convention.  This theorem proves the retained
nearest-neighbor conclusion for every chain of length `N + 2`; the density
and spectral conclusions remain available at length one.  See
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem topologicalGibbsDecomposition_of_isRFPViaTS
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M)
    (hM : IsMPDO M) (hRFP : IsRFPViaTS M)
    (hLI : (BNTLabelCoefficientFamily.ofChi
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP).chi).LengthIndependent) :
    let H := rfpBNTFusionTensorClause M hHorizontal hM hRFP
    H.HasTopologicalDensityDecomposition ∧
      H.HasTopologicalDensityFactorCommutator ∧
        H.HasTerminalSpectralProjectorRefinement hM ∧
          H.HasTopologicalGibbsDecomposition hM := by
  dsimp only
  exact ⟨BNTFusionTensorClause.hasTopologicalDensityDecomposition
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP),
    BNTFusionTensorClause.hasTopologicalDensityFactorCommutator
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP),
    BNTFusionTensorClause.hasTerminalSpectralProjectorRefinement
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP) hM hLI,
    BNTFusionTensorClause.hasTopologicalGibbsDecomposition
      (rfpBNTFusionTensorClause M hHorizontal hM hRFP) hM hLI⟩

end MPOTensor
