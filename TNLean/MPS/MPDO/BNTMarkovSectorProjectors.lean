/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.MPS.MPDO.BNTMarkovKeyFormula
import TNLean.MPS.MPDO.HayashiSectorProjector
import TNLean.MPS.MPDO.SectorEtaOperator

/-!
# Normal-sector projectors from quantum-Markov sectors

This module proves the existence assertion following the principal Case II
identity in arXiv:1606.00608, Appendix C.2.  For every Hayashi sector of
nonzero weight, at least one basis-of-normal-tensors sector has a nonzero
diagonal block.  Under the separately stated nonzero-closing-matrix hypothesis
used by the source cancellation, this sector is unique.  The corresponding
sums of the canonical Hayashi projections give the normal-sector projections
of equation `Pis` on the positive-weight support.

The source discards zero blocks by assuming
$Q_k\sigma^{(N)}_3Q_k\ne 0$.  Since the formal Hayashi decomposition retains
summands of weight zero, the assertion is stated on the subtype $p_k\ne0$.
This is the inactive-sector correction recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

## Main definitions

* `MPOTensor.bntMarkovBlock`: the block $O_s^{(k)}=Q_k\mathcal K_sQ_k$ in
  coordinates adapted to the Hayashi decomposition.
* `MPOTensor.BNTMarkovBlockNonzero`: nonvanishing of some virtual slice of
  $O_s^{(k)}$.
* `MPOTensor.bntSectorLabel`: the unique label $j_k$ under the explicit
  nonzero-closing-matrix hypothesis.
* `MPOTensor.bntSectorProjection`: the projection
  $P_s=\sum_{k:j_k=s}Q_k$ on the positive-weight support.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, equations `QkKjs` and `Pis`, lines 1698--1737.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d g D : ℕ} {dim : Fin g → ℕ}

/-- The $k$-th diagonal quantum-Markov block of one physical slice of a
basis-of-normal-tensors sector:
\[
  O_s^{(k)}(\beta,\alpha)
  =\left[U_B\kappa^{(s)}_{\beta,\alpha}U_B^\dagger\right]_{k,k}.
\]

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1703--1707,
and the definition of $O_j^{(k)}$ at lines 1733--1736. -/
noncomputable def bntMarkovBlock
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hη : EtaStructure ρ) (k : Fin hη.m)
    (β α : Fin D) :
    Matrix (Fin (hη.dL k) × Fin (hη.dR k))
      (Fin (hη.dL k) × Fin (hη.dR k)) ℂ :=
  fun x y ↦
    Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) *
          physicalSlice K β α *
          (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
      ⟨k, x⟩ ⟨k, y⟩

/-- The normal sector has a nonzero diagonal block in the $k$-th
quantum-Markov summand when one of the virtual slices $O_s^{(k)}(\beta,\alpha)$
is nonzero.

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1703--1707,
and lines 1733--1737. -/
def BNTMarkovBlockNonzero
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hη : EtaStructure ρ) (k : Fin hη.m) : Prop :=
  ∃ β α : Fin D, bntMarkovBlock K hη k β α ≠ 0

/-- Conjugating the middle physical index of a three-site family closure
conjugates the middle tensor in every normal sector.

Source: arXiv:1606.00608, Appendix C.2, lines 1726--1732. -/
theorem conjugated_middle_threeSiteFamilyClosure
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (hρ : IsThreeSiteFamilyClosure K R ρ)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (i₁ j₁ i₃ j₃ b b' : Fin d) :
    (∑ i₂ : Fin d, ∑ j₂ : Fin d,
      U b i₂ * ρ (i₁, i₂, i₃) (j₁, j₂, j₃) * star (U b' j₂)) =
      ∑ s : Fin g, Matrix.trace
        (K s i₁ j₁ * conjugatePhysical (K s) U b b' * K s i₃ j₃ * R s) := by
  classical
  unfold IsThreeSiteFamilyClosure at hρ
  simp_rw [hρ]
  let rotate : (Fin d × Fin d × Fin g) ≃ (Fin g × Fin d × Fin d) := {
    toFun := fun ⟨i₂, j₂, s⟩ ↦ (s, i₂, j₂)
    invFun := fun ⟨s, i₂, j₂⟩ ↦ (i₂, j₂, s)
    left_inv := by rintro ⟨i₂, j₂, s⟩; rfl
    right_inv := by rintro ⟨s, i₂, j₂⟩; rfl }
  have sum_sector_first (f : Fin d → Fin d → Fin g → ℂ) :
      (∑ i₂, ∑ j₂, ∑ s, f i₂ j₂ s) =
        ∑ s, ∑ i₂, ∑ j₂, f i₂ j₂ s := by
    classical
    let F : Fin d × Fin d × Fin g → ℂ := fun ⟨i₂, j₂, s⟩ ↦ f i₂ j₂ s
    have hflat : (∑ z, F z) = ∑ i₂, ∑ j₂, ∑ s, f i₂ j₂ s := by
      simp only [Fintype.sum_prod_type, F]
    have hflat' : (∑ z, F (rotate.symm z)) =
        ∑ s, ∑ i₂, ∑ j₂, f i₂ j₂ s := by
      simp [Fintype.sum_prod_type, F, rotate]
    rw [← hflat, ← hflat']
    exact (Equiv.sum_comp rotate.symm F).symm
  have hmiddle (s : Fin g) : conjugatePhysical (K s) U b b' =
      ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        (U b i₂ * star (U b' j₂)) • K s i₂ j₂ := by
    exact conjugatePhysical_eq_sum (K s) U b b'
  simp_rw [hmiddle]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [sum_sector_first]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  refine Finset.sum_congr rfl fun i₂ _ ↦ ?_
  refine Finset.sum_congr rfl fun j₂ _ ↦ ?_
  ring

/-- Every quantum-Markov sector of nonzero weight has a nonzero diagonal
block in at least one normal sector:
\[
  p_k\ne0 \quad\Longrightarrow\quad
  \exists s,\; Q_k\mathcal K_sQ_k\ne0.
\]

The conclusion is the existence part of equation `QkKjs`.  It follows
directly from the three-site family closure and the trace-one left and right
states in the Hayashi decomposition.

**Local fix (inactive sectors):** the source removes summands for which
$Q_k\sigma^{(N)}_3Q_k=0$.  The formal statement instead retains the ambient
decomposition and restricts to $p_k\ne0$, as recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1733--1737. -/
theorem exists_bntMarkovBlockNonzero_of_probability_ne_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (hρ : IsThreeSiteFamilyClosure K R ρ)
    (hη : EtaStructure ρ) (k : Fin hη.m) (hk : hη.p k ≠ 0) :
    ∃ s : Fin g, BNTMarkovBlockNonzero (K s) hη k := by
  classical
  obtain ⟨⟨i₁, l⟩, hleft⟩ :=
    Matrix.exists_diagonal_ne_zero_of_trace_eq_one
      (hη.ρ_left k) (hη.hρ_left_dm k).2
  obtain ⟨⟨r, i₃⟩, hright⟩ :=
    Matrix.exists_diagonal_ne_zero_of_trace_eq_one
      (hη.ρ_right k) (hη.hρ_right_dm k).2
  let b : Fin d := hη.decompB.symm ⟨k, (l, r)⟩
  have hs := congrFun (congrFun hη.h_state
    (i₁, (⟨k, (l, r)⟩, i₃))) (i₁, (⟨k, (l, r)⟩, i₃))
  rw [Matrix.reindex_apply, Matrix.submatrix_apply] at hs
  have hindex : (HayashiMarkov.abcEquiv hη.decompB).symm
      (i₁, (⟨k, (l, r)⟩, i₃)) = (i₁, b, i₃) := by
    simp [HayashiMarkov.abcEquiv, b]
  rw [hindex, HayashiMarkov.liftB_conj_apply,
    HayashiMarkov.blockState_apply] at hs
  have hs' :
      (∑ i₂ : Fin d, ∑ j₂ : Fin d,
        (hη.U_B : Matrix (Fin d) (Fin d) ℂ) b i₂ *
          ρ (i₁, i₂, i₃) (i₁, j₂, i₃) *
            star ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) b j₂)) =
        (hη.p k : ℂ) * hη.ρ_left k (i₁, l) (i₁, l) *
          hη.ρ_right k (r, i₃) (r, i₃) := by
    simpa using hs
  have hsum_ne :
      (∑ s : Fin g, Matrix.trace
        (K s i₁ i₁ * conjugatePhysical (K s) hη.U_B b b *
          K s i₃ i₃ * R s)) ≠ 0 := by
    rw [← conjugated_middle_threeSiteFamilyClosure
      hρ hη.U_B i₁ i₁ i₃ i₃ b b, hs']
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) hleft) hright
  obtain ⟨s, _, hs_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hmiddle_ne : conjugatePhysical (K s) hη.U_B b b ≠ 0 := by
    intro hzero
    rw [hzero] at hs_ne
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero] at hs_ne
    exact hs_ne rfl
  obtain ⟨β, α, hentry⟩ :=
    Matrix.exists_entry_ne_zero_of_ne_zero _ hmiddle_ne
  refine ⟨s, β, α, ?_⟩
  intro hblock
  have hdiag := congrFun (congrFun hblock (l, r)) (l, r)
  rw [bntMarkovBlock, Matrix.reindex_apply, Matrix.submatrix_apply] at hdiag
  change conjugatePhysical (K s) hη.U_B b b β α = 0 at hdiag
  exact hentry hdiag

/-- A positive-weight quantum-Markov sector cannot have nonzero diagonal
blocks in two distinct normal sectors.

The proof is the cancellation argument following equation `QkKjs`: a
same-sector instance of the principal identity supplies a nonzero left
factor; a mixed normal-sector instance forces the right factor of the second
sector to vanish; a final same-sector instance contradicts its nonzero
block.

**Scope restriction (closing matrices):** this statement assumes explicitly
that every closing matrix $R_s$ is nonzero.  The source obtains suitable
nonzero closing entries from the simplicity and common-weight construction at
lines 1714--1718.  Connecting that construction to
`IsThreeSiteFamilyClosure` remains recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1733--1737. -/
theorem bntMarkovBlockNonzero_eq_of_probability_ne_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (k : Fin hη.m) (hk : hη.p k ≠ 0)
    {s t : Fin g} (hs : BNTMarkovBlockNonzero (K s) hη k)
    (ht : BNTMarkovBlockNonzero (K t) hη k) : s = t := by
  classical
  by_contra hst
  obtain ⟨βs, αs, hBs⟩ := hs
  obtain ⟨⟨ls, rs⟩, ⟨ls', rs'⟩, hBs_entry⟩ :=
    Matrix.exists_entry_ne_zero_of_ne_zero _ hBs
  obtain ⟨β3s, α1s, hRs_entry⟩ :=
    Matrix.exists_entry_ne_zero_of_ne_zero _ (hR s)
  have hsame_s := isMPOBlockLeftInverse_bnt_markov_key_formula hC hρ hη
    (⟨s, α1s, βs⟩) (⟨s, αs, β3s⟩) k k ls rs ls' rs'
  simp only [dif_pos trivial] at hsame_s
  change
    (hη.p k : ℂ) *
        bntMarkovLeftFactor C hη (⟨s, α1s, βs⟩) k ls ls' *
          bntMarkovRightFactor C hη (⟨s, αs, β3s⟩) k rs rs' =
      R s β3s α1s * bntMarkovBlock (K s) hη k βs αs
        (ls, rs) (ls', rs') at hsame_s
  have hsame_s_ne :
      (hη.p k : ℂ) *
          bntMarkovLeftFactor C hη (⟨s, α1s, βs⟩) k ls ls' *
            bntMarkovRightFactor C hη (⟨s, αs, β3s⟩) k rs rs' ≠ 0 := by
    rw [hsame_s]
    exact mul_ne_zero hRs_entry hBs_entry
  have hleft_s :
      bntMarkovLeftFactor C hη (⟨s, α1s, βs⟩) k ls ls' ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, zero_mul] at hsame_s_ne
    exact hsame_s_ne rfl
  obtain ⟨βt, αt, hBt⟩ := ht
  obtain ⟨⟨lt, rt⟩, ⟨lt', rt'⟩, hBt_entry⟩ :=
    Matrix.exists_entry_ne_zero_of_ne_zero _ hBt
  obtain ⟨β3t, α1t, hRt_entry⟩ :=
    Matrix.exists_entry_ne_zero_of_ne_zero _ (hR t)
  have hmixed := isMPOBlockLeftInverse_bnt_markov_key_formula hC hρ hη
    (⟨s, α1s, βs⟩) (⟨t, αt, β3t⟩) k k ls rt ls' rt'
  simp only [dif_pos trivial, dif_neg hst] at hmixed
  have hright_t :
      bntMarkovRightFactor C hη (⟨t, αt, β3t⟩) k rt rt' = 0 := by
    rcases mul_eq_zero.mp hmixed with hp_left_zero | hright_zero
    · exact False.elim <|
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) hleft_s) hp_left_zero
    · exact hright_zero
  have hsame_t := isMPOBlockLeftInverse_bnt_markov_key_formula hC hρ hη
    (⟨t, α1t, βt⟩) (⟨t, αt, β3t⟩) k k lt rt lt' rt'
  simp only [dif_pos trivial] at hsame_t
  change
    (hη.p k : ℂ) *
        bntMarkovLeftFactor C hη (⟨t, α1t, βt⟩) k lt lt' *
          bntMarkovRightFactor C hη (⟨t, αt, β3t⟩) k rt rt' =
      R t β3t α1t * bntMarkovBlock (K t) hη k βt αt
        (lt, rt) (lt', rt') at hsame_t
  rw [hright_t, mul_zero] at hsame_t
  exact (mul_ne_zero hRt_entry hBt_entry) hsame_t.symm

/-- Under the explicit nonzero-closing-matrix hypothesis, every
positive-weight quantum-Markov sector has a unique normal-sector label with a
nonzero diagonal block.

**Scope restriction (closing matrices):** see
`bntMarkovBlockNonzero_eq_of_probability_ne_zero`.  The missing derivation of
this hypothesis from the paper's simplicity and common-weight construction is
recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1733--1737. -/
theorem existsUnique_bntMarkovBlockNonzero_of_probability_ne_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (k : Fin hη.m) (hk : hη.p k ≠ 0) :
    ∃! s : Fin g, BNTMarkovBlockNonzero (K s) hη k := by
  obtain ⟨s, hs⟩ :=
    exists_bntMarkovBlockNonzero_of_probability_ne_zero hρ hη k hk
  refine ⟨s, hs, fun t ht ↦ ?_⟩
  exact bntMarkovBlockNonzero_eq_of_probability_ne_zero
    hC hρ hη hR k hk ht hs

/-- The normal-sector label $j_k$ assigned to a positive-weight
quantum-Markov sector by equation `QkKjs`.

**Scope restriction (closing matrices):** the definition uses the conditional
uniqueness theorem above; see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1733--1737. -/
noncomputable def bntSectorLabel
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0)
    (k : {k : Fin hη.m // hη.p k ≠ 0}) : Fin g :=
  Classical.choose
    (existsUnique_bntMarkovBlockNonzero_of_probability_ne_zero
      hC hρ hη hR k k.property).exists

/-- The block selected by $j_k$ is nonzero.

**Scope restriction (closing matrices):** see `bntSectorLabel`.

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1733--1737. -/
theorem bntMarkovBlockNonzero_bntSectorLabel
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0)
    (k : {k : Fin hη.m // hη.p k ≠ 0}) :
    BNTMarkovBlockNonzero
      (K (bntSectorLabel hC hρ hη hR k)) hη k := by
  exact Classical.choose_spec
    (existsUnique_bntMarkovBlockNonzero_of_probability_ne_zero
      hC hρ hη hR k k.property).exists

/-- The label $j_k$ is characterized by nonvanishing of the corresponding
diagonal block.

**Scope restriction (closing matrices):** see `bntSectorLabel`.

Source: arXiv:1606.00608, Appendix C.2, equation `QkKjs`, lines 1733--1737. -/
theorem bntMarkovBlockNonzero_iff_eq_bntSectorLabel
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0)
    (k : {k : Fin hη.m // hη.p k ≠ 0}) (s : Fin g) :
    BNTMarkovBlockNonzero (K s) hη k ↔
      s = bntSectorLabel hC hρ hη hR k := by
  constructor
  · intro hs
    exact bntMarkovBlockNonzero_eq_of_probability_ne_zero
      hC hρ hη hR k k.property hs
        (bntMarkovBlockNonzero_bntSectorLabel hC hρ hη hR k)
  · rintro rfl
    exact bntMarkovBlockNonzero_bntSectorLabel hC hρ hη hR k

/-- The projector
\[
  P_s=\sum_{k:\,j_k=s}Q_k
\]
formed from the positive-weight quantum-Markov sectors assigned to normal
sector $s$.

**Scope restriction (closing matrices):** this definition uses the
conditional label $j_k$ above.  Zero-weight Markov summands do not occur in
the sum.

Source: arXiv:1606.00608, Appendix C.2, equation `Pis`, lines 1733--1737. -/
noncomputable def bntSectorProjection
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ k : {k : Fin hη.m // hη.p k ≠ 0},
    if bntSectorLabel hC hρ hη hR k = s then
      hη.sectorProjection k
    else 0

/-- Each $P_s$ is an orthogonal projection.

**Scope restriction (closing matrices):** see `bntSectorProjection`.

Source: arXiv:1606.00608, Appendix C.2, equation `Pis`, lines 1733--1737. -/
theorem bntSectorProjection_isOrthogonal
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s : Fin g) :
    IsOrthogonalProjection (bntSectorProjection hC hρ hη hR s) := by
  classical
  apply isOrthogonalProjection_sum_of_pairwise_mul_eq_zero
  · intro k
    by_cases hk : bntSectorLabel hC hρ hη hR k = s
    · simpa [bntSectorProjection, hk] using hη.sectorProjection_isOrthogonal k
    · simp [hk, IsOrthogonalProjection]
  · intro k l hkl
    by_cases hk : bntSectorLabel hC hρ hη hR k = s
    · by_cases hl : bntSectorLabel hC hρ hη hR l = s
      · simp only [hk, hl, if_pos]
        exact hη.sectorProjection_mul_eq_zero fun hco ↦
          hkl (Subtype.ext hco)
      · simp [hl]
    · simp [hk]

/-- Projectors belonging to distinct normal-sector labels are mutually
orthogonal.

**Scope restriction (closing matrices):** see `bntSectorProjection`.

Source: arXiv:1606.00608, Appendix C.2, equation `Pis`, lines 1733--1737. -/
theorem bntSectorProjection_mul_eq_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) {s t : Fin g} (hst : s ≠ t) :
    bntSectorProjection hC hρ hη hR s *
      bntSectorProjection hC hρ hη hR t = 0 := by
  classical
  rw [bntSectorProjection, bntSectorProjection, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hk : bntSectorLabel hC hρ hη hR k = s
  · by_cases hl : bntSectorLabel hC hρ hη hR l = t
    · simp only [hk, hl, if_pos]
      apply hη.sectorProjection_mul_eq_zero
      intro hkl
      apply hst
      rw [← hk, ← hl]
      congr
      exact Subtype.ext hkl
    · simp [hl]
  · simp [hk]

/-- The projector onto the positive-weight part of the quantum-Markov
decomposition.

**Local fix (inactive sectors):** the source removes zero blocks before
equations `QkKjs` and `Pis`; the retained ambient decomposition is therefore
resolved only on the positive-weight support.

Source: arXiv:1606.00608, Appendix C.2, lines 1698--1707 and 1733--1737. -/
noncomputable def activeMarkovProjection
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (hη : EtaStructure ρ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ k : {k : Fin hη.m // hη.p k ≠ 0}, hη.sectorProjection k

/-- The $P_s$ resolve the positive-weight quantum-Markov support.

**Scope restriction (closing matrices):** see `bntSectorProjection`.

**Local fix (inactive sectors):** see `activeMarkovProjection`.

Source: arXiv:1606.00608, Appendix C.2, equation `Pis`, lines 1733--1737. -/
theorem sum_bntSectorProjection
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) :
    ∑ s : Fin g, bntSectorProjection hC hρ hη hR s =
      activeMarkovProjection hη := by
  classical
  simp only [bntSectorProjection, activeMarkovProjection]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp

end MPOTensor
