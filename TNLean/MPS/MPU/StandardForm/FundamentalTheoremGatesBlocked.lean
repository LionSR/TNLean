import TNLean.MPS.MPU.StandardForm.FundamentalTheoremGates
import TNLean.MPS.MPU.StandardForm.TwoSiteStandardForm
import TNLean.MPS.MPU.StandardForm.FundamentalTheoremLetters
import TNLean.MPS.MPU.StandardForm.SelectedSourceGateVirtualGauge

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

It also contains the following results.

* `MPOTensor.IsMPUCanonicalFormII.fundamentalTheorem`: the fundamental theorem of matrix product
  unitaries.
* `MPOTensor.IsMPUCanonicalFormII.eq_virtualSandwich_of_mpo_eq`,
  `MPOTensor.IsMPUCanonicalFormII.exists_source_gate_unitary_gauges_of_mpo_eq`: the fundamental
  theorem of matrix product unitaries: gates, necessity.
-/

section FundamentalTheoremGatesNecessity

/-!
## The fundamental theorem of matrix product unitaries: gates, necessity

Two simple tensors in canonical form II with the same periodic operators at every length at
least two have gates related by unitaries on the two internal legs. The letter-level theorem
supplies the bond unitary `z`; the selected-factor and selected-gate comparison theorems, stated
for the sandwich `z U z†`, are transported along the equality `V = z U z†`.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), relation (35a) and
the contraction of the half-factor relations (35b). Milestone M-A, Theorem A2.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

/-- Equal operators at every length at least two express `V` as the unitary sandwich of `U`. -/
theorem IsMPUCanonicalFormII.eq_virtualSandwich_of_mpo_eq
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∃ z : Matrix.unitaryGroup (Fin D) ℂ,
      V = virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ)) := by
  obtain ⟨hdim, z, hz⟩ := (hU.mpo_eq_iff_exists_unitary_conj hV).mp hEq
  refine ⟨z, ?_⟩
  funext ⟨i, j⟩
  rw [hz i j]
  rfl

/-- **Fundamental theorem, gates, necessity.** Simple tensors in canonical form II with equal
periodic operators at every length at least two have the same source ranks and gates related by
unitaries `x` on the left rank and `y` on the right rank:
`u_V = (x ⊗ y) u_U` and `v_V = v_U (y† ⊗ x†)`, with the gates of the fixed factorizations.

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648): the first relation
is (35a); the second is the contraction of the two half-factor relations (35b) over the bond,
not (35b) itself. The half-factor relations themselves are
`IsMPUCanonicalFormII.exists_selected_source_factor_unitary_gauges` applied to the unitary `z`
of `eq_virtualSandwich_of_mpo_eq`. Simplicity of both tensors is assumed because the gate
comparison theorem is stated for simple tensors; the mathematical argument does not need it. -/
theorem IsMPUCanonicalFormII.exists_source_gate_unitary_gauges_of_mpo_eq
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∃ (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
      (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      sourceU V hV.ρ hV.ρ_posDef =
        ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
          Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _) (sourceU U hU.ρ hU.ρ_posDef) ∧
      sourceV V hV.ρ hV.ρ_posDef =
        Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (sourceV U hU.ρ hU.ρ_posDef) *
          (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ)) := by
  obtain ⟨z, rfl⟩ := hU.eq_virtualSandwich_of_mpo_eq hV hEq
  obtain ⟨x, y, hu, hv⟩ := hU.exists_selected_source_gate_unitary_gauges hSU z hV hSV
  exact ⟨_, _, x, y, hu, hv⟩

end MPOTensor

end FundamentalTheoremGatesNecessity

section FundamentalTheoremGatesBlocked

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

end FundamentalTheoremGatesBlocked

section FundamentalTheorem

/-!
## The fundamental theorem of matrix product unitaries

The combined statement. For simple tensors `U, V` in canonical form II the following are
equivalent: the periodic operators agree at every length at least two; the bond dimensions agree
and the letters are unitarily conjugate. Either implies that the gates of the fixed
factorizations are related by unitaries `x, y` on the two internal legs; and gates so related
give equal periodic operators on rings of even length
(`TwoSiteStandardFormData.mpo_eq_of_gate_gauges`).

Source: CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624--648), equation (35a) and
the contraction of (35b). The source states the theorem for the two-site standard forms; the
letter-level equivalence makes its remark that `z` is unitary into a statement, and the parity
example
(`StandardFormParityCounterexample.lean`) shows that the gate relations alone determine the
operators only on rings of even length. Milestone M-A, Theorem A4.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

/-- **Fundamental theorem of matrix product unitaries** (CPSV17 Thm III.10), for simple tensors
in canonical form II with the same bond dimension: equal periodic operators at every length at
least two are equivalent to a unitary conjugation of the letters, and imply the gate relations
`u_V = (x ⊗ y) u_U`, `v_V = v_U (y† ⊗ x†)` for unitaries `x, y` on the internal legs. -/
theorem IsMPUCanonicalFormII.fundamentalTheorem
    {d D : ℕ} {U V : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V) :
    ((∀ N : ℕ, 1 < N → mpo U N = mpo V N) ↔
      ∃ z : Matrix.unitaryGroup (Fin D) ℂ,
        V = virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
          (star (z : Matrix (Fin D) (Fin D) ℂ))) ∧
    ((∀ N : ℕ, 1 < N → mpo U N = mpo V N) →
      ∃ (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
        (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
        sourceU V hV.ρ hV.ρ_posDef =
          ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
            Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
              (sourceU U hU.ρ hU.ρ_posDef) ∧
        sourceV V hV.ρ hV.ρ_posDef =
          Matrix.reindex (Equiv.refl _) (Equiv.prodCongr er el) (sourceV U hU.ρ hU.ρ_posDef) *
            (star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) ⊗ₖ
              star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ))) := by
  refine ⟨⟨fun hEq => hU.eq_virtualSandwich_of_mpo_eq hV hEq, ?_⟩,
    fun hEq => hU.exists_source_gate_unitary_gauges_of_mpo_eq hSU hV hSV hEq⟩
  rintro ⟨z, rfl⟩ N _
  exact mpo_eq_of_unitary_conj rfl z (fun i j => rfl) N

end MPOTensor

end FundamentalTheorem
