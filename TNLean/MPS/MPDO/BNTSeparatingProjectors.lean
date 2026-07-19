/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTProjectorSelection

/-!
# Separating projectors for a simple tensor satisfying the strong area law

For the four-site quantum-Markov decomposition, the BNT projectors resolve the
positive-weight Markov support. The remaining zero-weight Markov summands
annihilate every physical slice. Assigning them to one BNT label therefore
gives orthogonal projectors which resolve the full physical identity and retain
the local separation relation.

**Local fix (inactive sectors):** The source removes zero-weight Markov
summands before defining the separating projectors. The formal decomposition
retains them and assigns them to one BNT label, as documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

## Main declarations

* `completedBntSectorProjection`: the BNT projector after assigning every
  zero-weight Markov summand to a distinguished BNT label.
* `exists_bntSeparatingProjectors_of_sameMPV₂Pos_isSAL_of_weight_copy_independent`:
  the separating projectors selected by SAL after copy independence is supplied.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `Pis` and `PjKiPj`, lines 1680--1737
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d g : ℕ} {dim : Fin g → ℕ}

/-- The BNT label of a Markov sector, with every zero-weight sector assigned
to a fixed label.

The source removes zero-weight Markov summands before defining the sets
$S_j$. Retaining the summands and assigning them to one label gives the same
separation relation on every physical slice.

**Local fix (inactive sectors):** This total assignment replaces the source's
implicit removal of zero-weight summands; see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equations `QkKjs` and `Pis`, lines
1698--1737. -/
noncomputable def completedBntSectorLabel
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s₀ : Fin g) (k : Fin hη.m) : Fin g :=
  if hk : hη.p k ≠ 0 then
    bntSectorLabel hC hρ hη hR ⟨k, hk⟩
  else s₀

/-- The projector obtained by summing all Markov-sector projections carrying
one completed BNT label.

**Local fix (inactive sectors):** The completed label assigns the retained
zero-weight summands to one BNT sector; see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `Pis`, lines 1680--1712. -/
noncomputable def completedBntSectorProjection
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s₀ s : Fin g) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ k : Fin hη.m,
    if completedBntSectorLabel hC hρ hη hR s₀ k = s then
      hη.sectorProjection k
    else 0

/-- Each completed BNT-sector matrix is an orthogonal projection.

Source: arXiv:1606.00608, Appendix C.2, equation `Pis`, lines 1680--1712. -/
theorem completedBntSectorProjection_isOrthogonal
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s₀ s : Fin g) :
    IsOrthogonalProjection
      (completedBntSectorProjection hC hρ hη hR s₀ s) := by
  classical
  apply isOrthogonalProjection_sum_of_pairwise_mul_eq_zero
  · intro k
    by_cases hk : completedBntSectorLabel hC hρ hη hR s₀ k = s
    · simpa [completedBntSectorProjection, hk] using
        hη.sectorProjection_isOrthogonal k
    · simp [hk, IsOrthogonalProjection]
  · intro k l hkl
    by_cases hk : completedBntSectorLabel hC hρ hη hR s₀ k = s
    · by_cases hl : completedBntSectorLabel hC hρ hη hR s₀ l = s
      · simp only [hk, hl, if_pos]
        exact hη.sectorProjection_mul_eq_zero hkl
      · simp [hl]
    · simp [hk]

/-- Completed projectors with distinct BNT labels are mutually orthogonal.

Source: arXiv:1606.00608, Appendix C.2, equation `Pis`, lines 1680--1712. -/
theorem completedBntSectorProjection_mul_eq_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s₀ : Fin g)
    {s t : Fin g} (hst : s ≠ t) :
    completedBntSectorProjection hC hρ hη hR s₀ s *
        completedBntSectorProjection hC hρ hη hR s₀ t = 0 := by
  classical
  rw [completedBntSectorProjection, completedBntSectorProjection, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hk : completedBntSectorLabel hC hρ hη hR s₀ k = s
  · by_cases hl : completedBntSectorLabel hC hρ hη hR s₀ l = t
    · simp only [hk, hl, if_pos]
      apply hη.sectorProjection_mul_eq_zero
      intro hkl
      apply hst
      rw [← hk, ← hl, hkl]
    · simp [hl]
  · simp [hk]

/-- The completed BNT-sector projectors resolve the full physical identity.

Source: arXiv:1606.00608, Appendix C.2, equation `Pis`, lines 1680--1696. -/
theorem sum_completedBntSectorProjection
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s₀ : Fin g) :
    ∑ s : Fin g, completedBntSectorProjection hC hρ hη hR s₀ s = 1 := by
  classical
  simp only [completedBntSectorProjection]
  rw [Finset.sum_comm]
  simpa using hη.sum_sectorProjection

/-- The completed BNT projectors separate the physical slices of distinct
normal representatives. Whenever $s\ne t$ or $i\ne s$,
\[
  P_s K_i^{\beta\alpha} P_t=0.
\]

Zero-weight Markov sectors are assigned to the distinguished label `s₀`.
Their diagonal corners vanish for every physical slice, so this assignment
does not change the separation relation.

Source: arXiv:1606.00608, Appendix C.2, equation `PjKiPj`, lines
1680--1737. -/
theorem completedBntSectorProjection_mul_physicalSlice_mul_eq_zero
    {K : (s : Fin g) → MPOTensor d (dim s)}
    {R : (s : Fin g) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex dim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse K C)
    (hρ : IsThreeSiteFamilyClosure K R ρ) (hη : EtaStructure ρ)
    (hR : ∀ s : Fin g, R s ≠ 0) (s₀ i s t : Fin g)
    (hst : s ≠ t ∨ i ≠ s) (β α : Fin (dim i)) :
    completedBntSectorProjection hC hρ hη hR s₀ s *
        physicalSlice (K i) β α *
          completedBntSectorProjection hC hρ hη hR s₀ t = 0 := by
  classical
  rw [completedBntSectorProjection, completedBntSectorProjection,
    Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hks : completedBntSectorLabel hC hρ hη hR s₀ k = s
  · by_cases hlt : completedBntSectorLabel hC hρ hη hR s₀ l = t
    · simp only [hks, hlt, if_pos]
      by_cases hkl : k = l
      · subst l
        have hst_eq : s = t := hks.symm.trans hlt
        have hi : i ≠ s := by
          rcases hst with hst | hi
          · exact False.elim (hst hst_eq)
          · exact hi
        by_cases hk : hη.p k ≠ 0
        · have hlabel :
              bntSectorLabel hC hρ hη hR ⟨k, hk⟩ = s := by
            simpa [completedBntSectorLabel, hk] using hks
          apply sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_ne_label
            hC hρ hη hR ⟨k, hk⟩ i
          · intro hilabel
            exact hi (hilabel.trans hlabel)
        · exact
            sectorProjection_mul_physicalSlice_mul_self_eq_zero_of_probability_eq_zero
              hC hρ hη hR i β α k (not_ne_iff.mp hk)
      · exact
          sectorProjection_mul_physicalSlice_mul_sectorProjection_eq_zero_of_ne
            hC hρ hη hR i β α hkl
    · simp [hlt]
  · simp [hks]

/-- Under copy-independent BNT weights, a simple tensor in biCF which satisfies
SAL has separating projectors for its BNT representatives.

More precisely, there is a distinguished BNT label $s_0$ and a family of
orthogonal projectors $P_s$ which resolves the physical identity. Whenever
$s\ne t$ or $i\ne s$,
\[
  P_s K_i^{\beta\alpha}P_t=0.
\]
The distinguished label exists because a BNT canonical form has a copy with
unit-modulus weight. Every zero-weight Markov summand is assigned to this
label. Such summands annihilate all physical slices, so the assignment restores
$\sum_sP_s=\mathbf 1$ without changing the displayed relation.

The hypotheses are the source context at the beginning of Case II: the BNT
canonical form and simultaneous span express biCF, nonnilpotence expresses
simplicity, copy independence is the conclusion immediately preceding the
projector lemma, and SAL supplies the four-site quantum-Markov decomposition.
There is no independent closing-matrix hypothesis.

**Scope restriction (copy-independent weights):** This theorem takes copy
independence as the explicit hypothesis `hWeight`. The source obtains it from
ZCL before the separating-projector lemma. A source-faithful standing-context
formulation must instead derive `hWeight` from the ZCL hypothesis and the BNT
canonical-form hypotheses; see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

**Local fix (inactive sectors):** The source discards zero-weight Markov
summands. Here they are assigned to the distinguished label $s_0$, which
restores the ambient identity resolution without changing any physical slice;
see `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, equations `CFK`, `biCFK`, `Pis`, and
`PjKiPj`, lines 1626--1737. -/
theorem exists_bntSeparatingProjectors_of_sameMPV₂Pos_isSAL_of_weight_copy_independent
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hCF : MPSTensor.IsBNTCanonicalForm S)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M) :
    let ρ := Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))
      (M.reducedBlockState 4 3 (by omega))
    ∃ (C : Matrix (MPSTensor.BlockEntryIndex S.basisDim)
        (Fin d × Fin d) ℂ),
      ∃ hC : MPSTensor.IsMPOBlockLeftInverse
          (fun j ↦ S.basisMPOTensor j) C,
        ∃ hη : EtaStructure ρ,
          let hρ : IsThreeSiteFamilyClosure
              (fun j ↦ S.basisMPOTensor j)
              (S.normalizedThreeSiteClosingMatrix M 1) ρ :=
            (reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
              M S hM hWeight hnonNil hSAL).1
          let hR : ∀ j : Fin S.basisCount,
              S.normalizedThreeSiteClosingMatrix M 1 j ≠ 0 :=
            (reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
              M S hM hWeight hnonNil hSAL).2
          ∃ s₀ : Fin S.basisCount,
            (∀ s, IsOrthogonalProjection
              (completedBntSectorProjection hC hρ hη hR s₀ s)) ∧
            (∀ s t, s ≠ t →
              completedBntSectorProjection hC hρ hη hR s₀ s *
                completedBntSectorProjection hC hρ hη hR s₀ t = 0) ∧
            (∑ s, completedBntSectorProjection hC hρ hη hR s₀ s) = 1 ∧
            ∀ (i s t : Fin S.basisCount), s ≠ t ∨ i ≠ s →
              ∀ (β α : Fin (S.basisDim i)),
                completedBntSectorProjection hC hρ hη hR s₀ s *
                    physicalSlice (S.basisMPOTensor i) β α *
                  completedBntSectorProjection hC hρ hη hR s₀ t = 0 := by
  dsimp only
  obtain ⟨s₀, _q₀, _hs₀⟩ := hCF.weight_unit_exists
  obtain ⟨C, hC, hη, _hunique, _hproj, _horth, _hsum⟩ :=
    exists_bntSectorProjectors_four_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL
  let hClosure :=
    reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
      M S hM hWeight hnonNil hSAL
  let hρ := hClosure.1
  let hR := hClosure.2
  refine ⟨C, hC, hη, s₀, ?_, ?_, ?_, ?_⟩
  · intro s
    exact completedBntSectorProjection_isOrthogonal hC hρ hη hR s₀ s
  · intro s t hst
    exact completedBntSectorProjection_mul_eq_zero hC hρ hη hR s₀ hst
  · exact sum_completedBntSectorProjection hC hρ hη hR s₀
  · intro i s t hst β α
    exact completedBntSectorProjection_mul_physicalSlice_mul_eq_zero
      hC hρ hη hR s₀ i s t hst β α

end MPOTensor
