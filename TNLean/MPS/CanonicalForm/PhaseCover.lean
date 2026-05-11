/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase

open scoped Matrix BigOperators
open Filter

/-!
# MPV phase covers for canonical-form block families

This file contains the MPV phase-equivalence and phase-cover constructions used by the
canonical-form equal-norm comparison and sector-comparison layers.
-/

namespace MPSTensor

variable {d : ℕ}

/-! ### Section 4. MPV phase-class representatives -/

/-- Heterogeneous MPV phase equivalence between two individual blocks.

`MPVBlockPhaseEquiv A B` means that the finite-chain MPV of `B` is a nonzero
scalar power times the finite-chain MPV of `A`, uniformly in the chain length and
physical word.  The bond dimensions of `A` and `B` may differ. -/
def MPVBlockPhaseEquiv {d DA DB : ℕ} (A : MPSTensor d DA) (B : MPSTensor d DB) : Prop :=
  ∃ ζ : ℂ, ζ ≠ 0 ∧ ∀ (N : ℕ) (σ : Fin N → Fin d),
    mpv B σ = ζ ^ N * mpv A σ

namespace MPVBlockPhaseEquiv

/-- Reflexivity of heterogeneous MPV phase equivalence. -/
lemma refl {D : ℕ} (A : MPSTensor d D) : MPVBlockPhaseEquiv A A := by
  exact ⟨1, one_ne_zero, fun N σ => by simp⟩

/-- Symmetry of heterogeneous MPV phase equivalence. -/
lemma symm {DA DB : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}
    (h : MPVBlockPhaseEquiv A B) : MPVBlockPhaseEquiv B A := by
  rcases h with ⟨ζ, hζ, hmpv⟩
  refine ⟨ζ⁻¹, inv_ne_zero hζ, ?_⟩
  intro N σ
  rw [hmpv N σ]
  rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N hζ), one_mul]

/-- Transitivity of heterogeneous MPV phase equivalence. -/
lemma trans {DA DB DC : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}
    {C : MPSTensor d DC} (hAB : MPVBlockPhaseEquiv A B)
    (hBC : MPVBlockPhaseEquiv B C) : MPVBlockPhaseEquiv A C := by
  rcases hAB with ⟨ζ, hζ, hζmpv⟩
  rcases hBC with ⟨η, hη, hηmpv⟩
  refine ⟨η * ζ, mul_ne_zero hη hζ, ?_⟩
  intro N σ
  rw [hηmpv N σ, hζmpv N σ, mul_pow]
  ring

/-- Gauge-phase equivalence after a dimension cast gives heterogeneous MPV phase equivalence. -/
lemma of_gaugePhaseEquiv_cast {DA DB : ℕ} (A : MPSTensor d DA) (B : MPSTensor d DB)
    (hdim : DA = DB)
    (hGPE : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim) A) B) :
    MPVBlockPhaseEquiv A B := by
  rcases hGPE with ⟨X, ζ, hζ, hX⟩
  refine ⟨ζ, hζ, ?_⟩
  intro N σ
  rw [mpv_eq_pow_mul_of_gaugePhase
    (A := cast (congr_arg (MPSTensor d) hdim) A) (B := B) X ζ hX N σ,
    mpv_cast_dim hdim A N σ]

/-- Heterogeneous MPV phase equivalence gives a scalar-power equality of MPV state vectors. -/
lemma exists_mpvState_eq_smul {DA DB : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}
    (h : MPVBlockPhaseEquiv A B) (N : ℕ) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧ mpvState (d := d) B N = ζ ^ N • mpvState (d := d) A N := by
  rcases h with ⟨ζ, hζ, hmpv⟩
  refine ⟨ζ, hζ, ?_⟩
  ext σ
  simp only [PiLp.smul_apply, smul_eq_mul, mpvState_apply]
  exact hmpv N σ

end MPVBlockPhaseEquiv

/-- Common MPV-phase cover for two block families.

The data consist of the finite common family, the class maps from the two block
families to it, the MPV-phase equivalences between each block and its chosen
common block, and surjectivity of both class maps.  These are the paper-level
data needed by the span comparison result; constructing them from the full
structural `SameMPV₂` data is a separate comparison step. -/
structure MPVCommonPhaseCover {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k)) where
  rC : ℕ
  dimC : Fin rC → ℕ
  common : (c : Fin rC) → MPSTensor d (dimC c)
  classA : Fin rA → Fin rC
  classB : Fin rB → Fin rC
  phaseA : ∀ j : Fin rA, MPVBlockPhaseEquiv (common (classA j)) (blocksA j)
  phaseB : ∀ k : Fin rB, MPVBlockPhaseEquiv (common (classB k)) (blocksB k)
  surjA : Function.Surjective classA
  surjB : Function.Surjective classB

/-- MPV phase equivalence for a dependent block family.

`MPVPhaseEquiv blocks j k` means that block `k` has the same MPV family as
block `j` after multiplying length-`N` vectors by a nonzero scalar power
`ζ ^ N`.  Gauge-phase equivalence implies this relation, and quotienting a
finite family by this relation is enough to absorb all repeated scalar-power
copies into sector weights.

This is the family-indexed specialization of `MPVBlockPhaseEquiv`, so the
homogeneous phase-class relation shares the heterogeneous block-level relation
rather than duplicating it. -/
def MPVPhaseEquiv {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) (j k : Fin r) : Prop :=
  MPVBlockPhaseEquiv (blocks j) (blocks k)

/-- MPV phase equivalence is reflexive. -/
lemma MPVPhaseEquiv.refl {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) (j : Fin r) :
    MPVPhaseEquiv blocks j j :=
  MPVBlockPhaseEquiv.refl (blocks j)

/-- MPV phase equivalence is symmetric. -/
lemma MPVPhaseEquiv.symm {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {j k : Fin r}
    (h : MPVPhaseEquiv blocks j k) : MPVPhaseEquiv blocks k j :=
  MPVBlockPhaseEquiv.symm h

/-- MPV phase equivalence is transitive. -/
lemma MPVPhaseEquiv.trans {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {i j k : Fin r}
    (hij : MPVPhaseEquiv blocks i j) (hjk : MPVPhaseEquiv blocks j k) :
    MPVPhaseEquiv blocks i k :=
  MPVBlockPhaseEquiv.trans hij hjk

/-- A gauge-phase equivalence between equal-dimension blocks gives MPV phase equivalence. -/
lemma MPVPhaseEquiv.of_gaugePhaseEquiv_cast {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {j k : Fin r}
    (hdim : dim j = dim k)
    (hGPE : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim) (blocks j)) (blocks k)) :
    MPVPhaseEquiv blocks j k :=
  MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast (blocks j) (blocks k) hdim hGPE

/-- MPV phase equivalence gives a scalar-power equality of finite-length MPV state vectors. -/
lemma MPVPhaseEquiv.exists_mpvState_eq_smul {r : ℕ} {dim : Fin r → ℕ}
    {blocks : (k : Fin r) → MPSTensor d (dim k)} {j k : Fin r}
    (h : MPVPhaseEquiv blocks j k) (N : ℕ) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧
      mpvState (d := d) (blocks k) N = ζ ^ N • mpvState (d := d) (blocks j) N :=
  MPVBlockPhaseEquiv.exists_mpvState_eq_smul h N

/-- Span inclusion for blocks covered by another family up to MPV phase.

For each block in `blocksA`, choose a block in `blocksB` whose MPV state differs only by a
nonzero scalar power. Then, at every finite length, the MPV span of `blocksA` is contained in
the MPV span of `blocksB`. -/
lemma mpv_span_le_of_phase_cover {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hcover : ∀ j : Fin rA, ∃ k : Fin rB, MPVBlockPhaseEquiv (blocksB k) (blocksA j))
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) ≤
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) := by
  refine Submodule.span_le.2 ?_
  intro v hv
  rcases hv with ⟨j, rfl⟩
  obtain ⟨k, hphase⟩ := hcover j
  obtain ⟨ζ, _hζ, hstate⟩ := hphase.exists_mpvState_eq_smul N
  have hmem : ζ ^ N • mpvState (d := d) (blocksB k) N ∈
      Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  simpa [hstate] using hmem

/-- Mutual MPV-phase covers give equality of finite-length block MPV spans. -/
lemma mpv_span_eq_of_mutual_phase_cover {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hA_le_B : ∀ j : Fin rA, ∃ k : Fin rB, MPVBlockPhaseEquiv (blocksB k) (blocksA j))
    (hB_le_A : ∀ k : Fin rB, ∃ j : Fin rA, MPVBlockPhaseEquiv (blocksA j) (blocksB k))
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) :=
  le_antisymm
    (mpv_span_le_of_phase_cover blocksA blocksB hA_le_B N)
    (mpv_span_le_of_phase_cover blocksB blocksA hB_le_A N)

/-- A surjective common MPV-phase quotient preserves finite-length block spans.

This is the abstract span step used after a common nonzero-weight block theorem identifies a
representative family and shows that every block maps onto it up to MPV phase. -/
lemma mpv_span_eq_of_surjective_phase_cover {r rC : ℕ}
    {dim : Fin r → ℕ} {dimC : Fin rC → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (common : (c : Fin rC) → MPSTensor d (dimC c))
    (classOf : Fin r → Fin rC)
    (hphase : ∀ k : Fin r, MPVBlockPhaseEquiv (common (classOf k)) (blocks k))
    (hsurj : Function.Surjective classOf)
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun k : Fin r => mpvState (d := d) (blocks k) N)) =
    Submodule.span ℂ (Set.range (fun c : Fin rC => mpvState (d := d) (common c) N)) := by
  refine mpv_span_eq_of_mutual_phase_cover blocks common ?_ ?_ N
  · intro k
    exact ⟨classOf k, hphase k⟩
  · intro c
    obtain ⟨k, hk⟩ := hsurj c
    refine ⟨k, ?_⟩
    rw [← hk]
    exact (hphase k).symm

/-- Two block families with a common surjective MPV-phase quotient have equal finite-length
MPV spans.

This lemma is deliberately independent of the sector weights.  It states the precise
linear-algebra hypothesis used by the nonzero-part after-blocking theorem once a common-blocking
result supplies a common representative family and shows that both sides cover it. -/
lemma mpv_span_eq_of_common_phase_cover {rA rB rC : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ} {dimC : Fin rC → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (common : (c : Fin rC) → MPSTensor d (dimC c))
    (classA : Fin rA → Fin rC) (classB : Fin rB → Fin rC)
    (hAphase : ∀ j : Fin rA, MPVBlockPhaseEquiv (common (classA j)) (blocksA j))
    (hBphase : ∀ k : Fin rB, MPVBlockPhaseEquiv (common (classB k)) (blocksB k))
    (hAsurj : Function.Surjective classA) (hBsurj : Function.Surjective classB)
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) := by
  calc
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N))
        = Submodule.span ℂ (Set.range (fun c : Fin rC => mpvState (d := d) (common c) N)) :=
          mpv_span_eq_of_surjective_phase_cover blocksA common classA hAphase hAsurj N
    _ = Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) :=
          (mpv_span_eq_of_surjective_phase_cover blocksB common classB hBphase hBsurj N).symm

namespace MPVCommonPhaseCover

variable {rA rB : ℕ}
variable {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
variable {blocksA : (j : Fin rA) → MPSTensor d (dimA j)}
variable {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}

/-- A common cover gives equality of the finite-length block MPV spans. -/
lemma span_eq (C : MPVCommonPhaseCover blocksA blocksB) (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) :=
  mpv_span_eq_of_common_phase_cover (d := d) blocksA blocksB C.common
    C.classA C.classB C.phaseA C.phaseB C.surjA C.surjB N

end MPVCommonPhaseCover

namespace SectorBasisPreMatching

variable {P Q : SectorDecomposition d}

/-- A sector-basis pre-matching supplies a common MPV phase cover of the two basis families.

The common family is the left basis. The left class map is the identity, the right
class map is the inverse of the matching permutation, and gauge-phase equivalence
of paired basis blocks gives the required MPV-phase equivalences. -/
def commonPhaseCover (M : SectorBasisPreMatching P Q) :
    MPVCommonPhaseCover P.basis Q.basis := by
  refine {
    rC := P.basisCount
    dimC := P.basisDim
    common := P.basis
    classA := id
    classB := M.perm.symm
    phaseA := ?_
    phaseB := ?_
    surjA := ?_
    surjB := ?_
  }
  · intro j
    exact MPVBlockPhaseEquiv.refl (P.basis j)
  · intro k
    have h := MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast
      (P.basis (M.perm.symm k)) (Q.basis (M.perm (M.perm.symm k)))
      (M.dim_eq (M.perm.symm k)) (M.basis_equiv (M.perm.symm k))
    rw [M.perm.apply_symm_apply k] at h
    exact h
  · intro j
    exact ⟨j, rfl⟩
  · intro j
    exact ⟨M.perm j, by simp⟩

/-- A sector-basis pre-matching gives equality of finite-length MPV spans of the two basis
families. -/
lemma span_eq (M : SectorBasisPreMatching P Q) (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
      mpvState (d := d) (P.basis j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
      mpvState (d := d) (Q.basis k) N)) :=
  M.commonPhaseCover.span_eq N

/-- A sector-basis pre-matching establishes the finite-length span equality needed by the
primitive overlap-span hypotheses. -/
lemma to_overlapSpan (M : SectorBasisPreMatching P Q)
    (HP : SectorBasisOverlapOrthoHypotheses P)
    (HQ : SectorBasisOverlapOrthoHypotheses Q)
    (hP_inj : ∀ j : Fin P.basisCount, IsInjective (P.basis j))
    (hQ_inj : ∀ k : Fin Q.basisCount, IsInjective (Q.basis k)) :
    SectorBasisOverlapSpanHypotheses P Q :=
  HP.to_overlapSpan HQ hP_inj hQ_inj M.span_eq

end SectorBasisPreMatching

/-- A proportional-decomposition BNT comparison conclusion produces a common MPV phase cover. -/
lemma nonempty_mpvCommonPhaseCover_of_proportionalDecompositionConclusion
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (h : ProportionalDecompositionConclusion (d := d) blocksA blocksB) :
    Nonempty (MPVCommonPhaseCover blocksA blocksB) := by
  rcases h with ⟨_hcount, perm, hmatch⟩
  refine ⟨?_⟩
  refine {
    rC := rA
    dimC := dimA
    common := blocksA
    classA := id
    classB := perm.symm
    phaseA := ?_
    phaseB := ?_
    surjA := ?_
    surjB := ?_
  }
  · intro j
    exact MPVBlockPhaseEquiv.refl (blocksA j)
  · intro k
    obtain ⟨hdim, hGPE⟩ := hmatch (perm.symm k)
    have h := MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast
      (blocksA (perm.symm k)) (blocksB (perm (perm.symm k))) hdim hGPE
    rw [perm.apply_symm_apply k] at h
    exact h
  · intro j
    exact ⟨j, rfl⟩
  · intro j
    exact ⟨perm j, by simp⟩

/-- A bijective MPV-phase matching gives a common MPV phase cover.

This is the direct implication used when a comparison theorem has already identified
the phase classes by a bijection, without restating the data as a proportional
decomposition conclusion. -/
lemma nonempty_mpvCommonPhaseCover_of_equiv_phase
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (e : Fin rA ≃ Fin rB)
    (hPhase : ∀ j : Fin rA, MPVBlockPhaseEquiv (blocksA j) (blocksB (e j))) :
    Nonempty (MPVCommonPhaseCover blocksA blocksB) := by
  refine ⟨?_⟩
  refine {
    rC := rA
    dimC := dimA
    common := blocksA
    classA := id
    classB := e.symm
    phaseA := ?_
    phaseB := ?_
    surjA := ?_
    surjB := ?_
  }
  · intro j
    exact MPVBlockPhaseEquiv.refl (blocksA j)
  · intro k
    have h := hPhase (e.symm k)
    rw [e.apply_symm_apply k] at h
    exact h
  · intro j
    exact ⟨j, rfl⟩
  · intro j
    exact ⟨e j, by simp⟩

/-- A BNT proportional-decomposition conclusion gives finite-length MPV span equality.

The conclusion is obtained by taking the left family as the common MPV phase-cover family and
then applying the common phase-cover span lemma. -/
lemma mpv_span_eq_of_proportionalDecompositionConclusion
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (h : ProportionalDecompositionConclusion (d := d) blocksA blocksB)
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) := by
  obtain ⟨cover⟩ := nonempty_mpvCommonPhaseCover_of_proportionalDecompositionConclusion
    (d := d) blocksA blocksB h
  exact cover.span_eq N

/-- A bijective MPV-phase matching gives finite-length MPV span equality. -/
lemma mpv_span_eq_of_equiv_phase
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (e : Fin rA ≃ Fin rB)
    (hPhase : ∀ j : Fin rA, MPVBlockPhaseEquiv (blocksA j) (blocksB (e j)))
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) := by
  obtain ⟨cover⟩ := nonempty_mpvCommonPhaseCover_of_equiv_phase
    (d := d) blocksA blocksB e hPhase
  exact cover.span_eq N

/-- Equivalence relation on block indices given by MPV phase equivalence. -/
def mpvPhaseSetoid {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) : Setoid (Fin r) where
  r := MPVPhaseEquiv blocks
  iseqv := {
    refl := MPVPhaseEquiv.refl blocks
    symm := fun {_ _} h => MPVPhaseEquiv.symm blocks h
    trans := fun {_ _ _} h₁ h₂ => MPVPhaseEquiv.trans blocks h₁ h₂
  }

/-- Quotient set of MPV phase equivalence classes. -/
abbrev MPVPhaseClass {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) :=
  Quotient (mpvPhaseSetoid blocks)

/-- The finite quotient by MPV phase classes is finite. -/
noncomputable instance instFintypeMPVPhaseClass {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) : Fintype (MPVPhaseClass blocks) := by
  dsimp [MPVPhaseClass]
  infer_instance

/-- Finite class data for the MPV phase relation.

The data consist of an enumeration of the quotient classes, a choice of
representative per class, the scalar-power relation from each representative to
each member, the separation property for the representatives, and the regrouping
identity for finite sums over the original blocks. -/
structure MPVPhaseClassData {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) where
  g : ℕ
  copies : Fin g → ℕ
  copies_pos : ∀ j, 0 < copies j
  enum : (j : Fin g) → Fin (copies j) → Fin r
  repr : Fin g → Fin r
  enum_phase : ∀ j q, MPVPhaseEquiv blocks (repr j) (enum j q)
  blocks_not_equiv : BlocksNotGaugePhaseEquiv (d := d) (fun j => blocks (repr j))
  regroup : ∀ f : Fin r → ℂ,
    ∑ j : Fin g, ∑ q : Fin (copies j), f (enum j q) = ∑ k : Fin r, f k

namespace MPVPhaseClassData

variable {r : ℕ} {dim : Fin r → ℕ}
variable {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-- Every original block index occurs in the finite enumeration of MPV phase classes. -/
lemma exists_enum_eq (classes : MPVPhaseClassData blocks) (k : Fin r) :
    ∃ j : Fin classes.g, ∃ q : Fin (classes.copies j), classes.enum j q = k := by
  classical
  by_contra h
  push Not at h
  have hzero :
      (∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
        (if classes.enum j q = k then (1 : ℂ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro q _
    simp [h j q]
  have hone : (∑ x : Fin r, (if x = k then (1 : ℂ) else 0)) = 1 := by
    simp
  have hregroup := classes.regroup (fun x : Fin r => if x = k then (1 : ℂ) else 0)
  rw [hzero, hone] at hregroup
  exact zero_ne_one hregroup

/-- The chosen MPV phase-class representatives span exactly the same finite-length MPV
subspace as the original block family.

Each representative is one of the original blocks, giving one inclusion. Conversely, every
original block occurs in a phase class and is a nonzero scalar-power multiple of that class's
representative at each length, hence lies in the representative span. -/
theorem representative_mpv_span_eq (classes : MPVPhaseClassData blocks) (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin classes.g =>
      mpvState (d := d) (blocks (classes.repr j)) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin r =>
      mpvState (d := d) (blocks k) N)) := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro v hv
    rcases hv with ⟨j, rfl⟩
    exact Submodule.subset_span ⟨classes.repr j, rfl⟩
  · refine Submodule.span_le.2 ?_
    intro v hv
    rcases hv with ⟨k, rfl⟩
    obtain ⟨j, q, hq⟩ := classes.exists_enum_eq k
    have hphase : MPVPhaseEquiv blocks (classes.repr j) k := by
      simpa [hq] using classes.enum_phase j q
    change mpvState (d := d) (blocks k) N ∈
      Submodule.span ℂ (Set.range (fun j : Fin classes.g =>
        mpvState (d := d) (blocks (classes.repr j)) N))
    obtain ⟨ζ, _hζ, hstate⟩ := hphase.exists_mpvState_eq_smul N
    rw [hstate]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end MPVPhaseClassData

/-- Construct the finite MPV phase classes of a block family.

The representative of each class is the first element in the finite enumeration
of that class.  If two representatives were gauge-phase equivalent, then they
would be MPV-phase equivalent and hence lie in the same quotient class; this
proves that distinct representatives are pairwise not gauge-phase equivalent. -/
noncomputable def mpvPhaseClassData {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) : MPVPhaseClassData blocks := by
  classical
  let cls := MPVPhaseClass blocks
  let e : cls ≃ Fin (Fintype.card cls) := Fintype.equivFin cls
  let g := Fintype.card cls
  let classOf : Fin g → cls := e.symm
  let classFinset : Fin g → Finset (Fin r) :=
    fun j => Finset.univ.filter (fun k => Quotient.mk (mpvPhaseSetoid blocks) k = classOf j)
  have hClass_nonempty : ∀ j, (classFinset j).Nonempty := by
    intro j
    obtain ⟨k, hk⟩ := Quotient.exists_rep (classOf j)
    refine ⟨k, ?_⟩
    simp [classFinset, hk]
  have hClass_disj :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin g)) : Set (Fin g)) classFinset := by
    intro j _ k _ hne
    apply Finset.disjoint_left.mpr
    intro x hxj hxk
    have hxj' : Quotient.mk (mpvPhaseSetoid blocks) x = classOf j :=
      (Finset.mem_filter.mp hxj).2
    have hxk' : Quotient.mk (mpvPhaseSetoid blocks) x = classOf k :=
      (Finset.mem_filter.mp hxk).2
    have hclass : classOf j = classOf k := hxj'.symm.trans hxk'
    apply hne
    simpa [classOf, e] using congrArg e hclass
  have hClass_cover : Finset.biUnion Finset.univ classFinset = Finset.univ := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    refine ⟨e (Quotient.mk (mpvPhaseSetoid blocks) k), ?_⟩
    simp [classFinset, classOf, e]
  let copiesFn : Fin g → ℕ := fun j => (classFinset j).card
  have hcopies_pos : ∀ j, 0 < copiesFn j :=
    fun j => Finset.card_pos.mpr (hClass_nonempty j)
  let enumFn : (j : Fin g) → Fin (copiesFn j) → Fin r :=
    fun j => (classFinset j).orderEmbOfFin rfl
  let reprFn : Fin g → Fin r := fun j => enumFn j ⟨0, hcopies_pos j⟩
  have hrepr_mem : ∀ j, Quotient.mk (mpvPhaseSetoid blocks) (reprFn j) = classOf j := by
    intro j
    exact (Finset.mem_filter.mp ((classFinset j).orderEmbOfFin_mem rfl ⟨0, hcopies_pos j⟩)).2
  have hEnum_phase : ∀ j q, MPVPhaseEquiv blocks (reprFn j) (enumFn j q) := by
    intro j q
    have hrepr : Quotient.mk (mpvPhaseSetoid blocks) (reprFn j) = classOf j := hrepr_mem j
    have henum : Quotient.mk (mpvPhaseSetoid blocks) (enumFn j q) = classOf j :=
      (Finset.mem_filter.mp ((classFinset j).orderEmbOfFin_mem rfl q)).2
    exact Quotient.exact (hrepr.trans henum.symm)
  have hBlocks : BlocksNotGaugePhaseEquiv (d := d) (fun j => blocks (reprFn j)) := by
    intro j k hjk hdim hGPE
    have hphase : MPVPhaseEquiv blocks (reprFn j) (reprFn k) :=
      MPVPhaseEquiv.of_gaugePhaseEquiv_cast blocks hdim hGPE
    have hquot : Quotient.mk (mpvPhaseSetoid blocks) (reprFn j) =
        Quotient.mk (mpvPhaseSetoid blocks) (reprFn k) :=
      Quotient.sound hphase
    have hclass : classOf j = classOf k := by
      exact (hrepr_mem j).symm.trans (hquot.trans (hrepr_mem k))
    apply hjk
    simpa [classOf, e] using congrArg e hclass
  have hRegroup : ∀ (f : Fin r → ℂ),
      ∑ j : Fin g, ∑ q : Fin (copiesFn j), f (enumFn j q) = ∑ k : Fin r, f k := by
    intro f
    have inner_eq : ∀ j : Fin g,
        ∑ q : Fin (copiesFn j), f (enumFn j q) = ∑ k ∈ classFinset j, f k := by
      intro j
      rw [← Finset.map_orderEmbOfFin_univ (classFinset j) rfl, Finset.sum_map]
      rfl
    simp_rw [inner_eq]
    calc ∑ j : Fin g, ∑ k ∈ classFinset j, f k
        = ∑ k ∈ Finset.biUnion Finset.univ classFinset, f k :=
            (Finset.sum_biUnion hClass_disj).symm
      _ = ∑ k ∈ Finset.univ, f k := by rw [hClass_cover]
      _ = ∑ k : Fin r, f k := rfl
  exact {
    g := g
    copies := copiesFn
    copies_pos := hcopies_pos
    enum := enumFn
    repr := reprFn
    enum_phase := hEnum_phase
    blocks_not_equiv := hBlocks
    regroup := hRegroup
  }

end MPSTensor
