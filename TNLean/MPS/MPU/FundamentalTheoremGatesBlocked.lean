import TNLean.MPS.MPU.FundamentalTheoremGates
import TNLean.MPS.MPU.FundamentalTheoremGatesNecessity
import TNLean.MPS.MPU.TwoSiteStandardForm

/-!
# The fundamental theorem of matrix product unitaries: sufficiency for the source gates

Relabelling the two internal legs of a two-site standard form by bijections of their index sets
gives a two-site standard form with relabelled gates. Combined with the gate-level sufficiency
theorem, two simple tensors in canonical form II whose source gates are related by unitaries on
the internal legs, after such a relabelling, have the same periodic operators on every ring of
even length.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), 'if' direction read
for the two-site standard forms; Milestone M-A, Theorem A3 first assertion.

**Scope restriction (even ring lengths):** the source asserts that the gate relations give
`U^(N) = V^(N)` for every `N`. The gates are built from the two-site block, so they determine only
the blocked family, and `IsMPUCanonicalFormII.mpo_two_mul_eq_of_source_gate_gauges` concludes
equality on rings of even length only. At odd lengths the printed converse fails: the bond-one
tensors `U = 1` and `V = -1` on `ℂ²` have gates related by `x = y = -1` and equal two-site blocks,
yet `V^(N) = (-1)^N U^(N)`. Documented in `docs/paper-gaps/mpu_standard_form_parity_gap.tex`.
Equality at every length follows from the letter-level unitary conjugation, not from the gates.
-/

open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

/-- Relabel the left and right internal legs of a two-site standard form along bijections
`el : Fin ℓ ≃ Fin ℓ'` and `er : Fin r ≃ Fin r'`. The tensor is unchanged; the gates and the half
factors are reindexed accordingly.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), 'if' direction read
for the two-site standard forms; Milestone M-A, Theorem A3 first assertion. -/
noncomputable def TwoSiteStandardFormData.reindexRanks
    {d D ℓ r ℓ' r' : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (el : Fin ℓ ≃ Fin ℓ') (er : Fin r ≃ Fin r') :
    TwoSiteStandardFormData W
      (Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) u)
      (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) v) where
  phys_pos := S.phys_pos
  bond_pos := S.bond_pos
  left_pos := by
    have h := Fintype.card_congr el
    simp only [Fintype.card_fin] at h
    exact h ▸ S.left_pos
  right_pos := by
    have h := Fintype.card_congr er
    simp only [Fintype.card_fin] at h
    exact h ▸ S.right_pos
  X₁ := Matrix.reindex (Equiv.refl _) er S.X₁
  X₂ := Matrix.reindex (Equiv.refl _) el S.X₂
  u_unitary := Matrix.IsUnitaryBetween.reindex _ S.u_unitary _ _
  v_unitary := Matrix.IsUnitaryBetween.reindex _ S.v_unitary _ _
  v_apply i₁ i₂ s t := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map]
    exact S.v_apply i₁ i₂ (er.symm s) (el.symm t)
  W_apply i j α γ := by
    rw [S.W_apply]
    refine Fintype.sum_equiv el _ _ fun t => Fintype.sum_equiv er _ _ fun s => ?_
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- **Fundamental theorem, source gates, sufficiency.** Let `U` and `V` be simple tensors in
canonical form II. If, after bijections `el`, `er` of the internal legs, the source gates of `V`
are those of `U` dressed by unitaries, `u_V = (x ⊗ y) u_U` and `v_V = v_U (y† ⊗ x†)`, then the
two-site blocks of `U` and `V` generate the same periodic operators at every positive length.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), 'if' direction read
for the two-site standard forms; Milestone M-A, Theorem A3 first assertion. -/
theorem IsMPUCanonicalFormII.mpo_blockTwo_eq_of_source_gate_gauges
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V)
    (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
    (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ)
    (hu : sourceU V hV.ρ hV.ρ_posDef =
      ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
        Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef))
    (hv : sourceV V hV.ρ hV.ρ_posDef =
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (sourceV U hU.ρ hU.ρ_posDef) *
        (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)))
    (N : ℕ) [NeZero N] :
    mpo (blockTwo U) N = mpo (blockTwo V) N := by
  have S := (hU.twoSiteStandardFormData hSU).reindexRanks el er
  have T := hV.twoSiteStandardFormData hSV
  rw [hu, hv] at T
  exact S.mpo_eq_of_gate_gauges x y T

/-- **Fundamental theorem, source gates, sufficiency, on rings of even length.** Under the
hypotheses of `IsMPUCanonicalFormII.mpo_blockTwo_eq_of_source_gate_gauges`, the tensors `U` and
`V` themselves generate the same periodic operators on every ring of positive even length.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), 'if' direction read
for the two-site standard forms; Milestone M-A, Theorem A3 first assertion. -/
theorem IsMPUCanonicalFormII.mpo_two_mul_eq_of_source_gate_gauges
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V)
    (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
    (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ)
    (hu : sourceU V hV.ρ hV.ρ_posDef =
      ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
        Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef))
    (hv : sourceV V hV.ρ hV.ρ_posDef =
      Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (sourceV U hU.ρ hU.ρ_posDef) *
        (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)))
    (N : ℕ) [NeZero N] :
    mpo U (2 * N) = mpo V (2 * N) := by
  have h := hU.mpo_blockTwo_eq_of_source_gate_gauges hSU hV hSV er el x y hu hv N
  rw [mpo_blockTwo_eq_reindex_blockTensor, mpo_blockTwo_eq_reindex_blockTensor,
    mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex] at h
  rw [Nat.mul_comm]
  exact (Matrix.reindex _ _).injective ((Matrix.reindex _ _).injective h)

end MPOTensor
