/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.HayashiMarkovStructure
import TNLean.Channel.KoashiImoto.MarkovDilationBlockForm

/-!
# Markov tripartite block form

This module states the final sector substitution in the equality case of strong
subadditivity.  It converts the invariant middle-system factors to the
Hayden--Jozsa--Petz--Winter order, identifies the sector output factor on
each ambient sector, and gives the resulting tripartite direct sum without
normalizing the left factors.

Source: Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 6,
equations (11), (14), and (15), lines 547--570.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace Matrix

open MarkovDilation

variable {dA dB dC : ℕ}

/-- The left-factor dimension in the finite Hayashi indexing of the ambient
middle-system sectors.  Complementary sectors have dimension one.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570. -/
def ambientHayashiLeftDim {z K : ℕ} (d : Fin K → ℕ)
    (k : Fin (z + K)) : ℕ :=
  ambientMarkovConditionalDim d (finSumFinEquiv.symm k)

/-- The right-factor dimension in the finite Hayashi indexing of the ambient
middle-system sectors.  Complementary sectors have dimension one.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570. -/
def ambientHayashiRightDim {z K : ℕ} (m : Fin K → ℕ)
    (k : Fin (z + K)) : ℕ :=
  ambientMarkovCommonDim m (finSumFinEquiv.symm k)

/-- The ambient middle-system decomposition in HJPW/Hayashi factor order:
the conditional factor precedes the common sector output factor.

This reverses each fibre of `ambientMarkovMiddleBlockEquiv`, whose order is
common factor followed by conditional factor.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (14)--(15),
lines 547--570. -/
def ambientHayashiMiddleEquiv
    {n K : ℕ} {m d : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n) :
    Fin dB ≃ Σ s : AmbientMarkovBlockIndex (dB - n) K,
      Fin (ambientMarkovConditionalDim d s) ×
        Fin (ambientMarkovCommonDim m s) :=
  (ambientMarkovMiddleBlockEquiv e₀ e).symm |>.trans
    (Equiv.sigmaCongrRight fun s =>
      Equiv.prodComm
        (Fin (ambientMarkovCommonDim m s))
        (Fin (ambientMarkovConditionalDim d s)))

@[simp]
theorem ambientHayashiMiddleEquiv_apply
    {n K : ℕ} {m d : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (s : AmbientMarkovBlockIndex (dB - n) K)
    (u : Fin (ambientMarkovCommonDim m s))
    (v : Fin (ambientMarkovConditionalDim d s)) :
    ambientHayashiMiddleEquiv e₀ e
        (ambientMarkovMiddleBlockEquiv e₀ e ⟨s, (u, v)⟩) =
      ⟨s, (v, u)⟩ := by
  simp [ambientHayashiMiddleEquiv]

/-- Number the ambient HJPW sectors by a finite interval, as required by
`HayashiMarkovDecomposition`. -/
def ambientHayashiFinMiddleEquiv
    {n K : ℕ} {m d : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n) :
    Fin dB ≃ Σ k : Fin ((dB - n) + K),
      Fin (ambientHayashiLeftDim (z := dB - n) d k) ×
        Fin (ambientHayashiRightDim (z := dB - n) m k) :=
  (ambientHayashiMiddleEquiv e₀ e).trans
    (Equiv.sigmaCongrLeft
      (β := fun s =>
        Fin (ambientMarkovConditionalDim d s) ×
          Fin (ambientMarkovCommonDim m s))
      finSumFinEquiv.symm).symm

@[simp]
theorem ambientHayashiFinMiddleEquiv_apply
    {n K : ℕ} {m d : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (k : Fin ((dB - n) + K))
    (u : Fin (ambientMarkovCommonDim m (finSumFinEquiv.symm k)))
    (v : Fin (ambientMarkovConditionalDim d (finSumFinEquiv.symm k))) :
    ambientHayashiFinMiddleEquiv e₀ e
        (ambientMarkovMiddleBlockEquiv e₀ e
          ⟨finSumFinEquiv.symm k, (u, v)⟩) =
      ⟨k, (v, u)⟩ := by
  simp only [ambientHayashiFinMiddleEquiv, Equiv.trans_apply,
    ambientHayashiMiddleEquiv_apply]
  apply (Equiv.symm_apply_eq (Equiv.sigmaCongrLeft
    (β := fun s =>
      Fin (ambientMarkovConditionalDim d s) ×
        Fin (ambientMarkovCommonDim m s))
    finSumFinEquiv.symm)).2
  rfl

/-- The tripartite sector equivalence agrees pointwise with the Hayashi
reassociation after the middle subsystem is decomposed in HJPW factor order.
This identifies the reindexing needed to instantiate a Hayashi Markov
structure without reconstructing the factor swap.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570. -/
@[simp]
theorem hayashi_sigmaAssoc_tripartiteBlockEquiv_apply
    {n K : ℕ} {m d : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (k : Fin ((dB - n) + K)) (a : Fin dA)
    (u : Fin (ambientMarkovCommonDim m (finSumFinEquiv.symm k)))
    (v : Fin (ambientMarkovConditionalDim d (finSumFinEquiv.symm k)))
    (c : Fin dC) :
    HayashiMarkov.abcEquiv (dA := dA) (dB := dB) (dC := dC)
        (ambientHayashiFinMiddleEquiv e₀ e)
        (tripartiteBlockEquiv
          (ambientMarkovMiddleBlockEquiv e₀ e)
          ⟨finSumFinEquiv.symm k, ((a, v), (u, c))⟩) =
      HayashiMarkov.sigmaAssoc (dA := dA) (dC := dC)
        (ambientHayashiLeftDim (z := dB - n) d)
        (ambientHayashiRightDim (z := dB - n) m)
        ⟨k, ((a, v), (u, c))⟩ := by
  simp [HayashiMarkov.abcEquiv, HayashiMarkov.sigmaAssoc]

/-- The sector output factor on every ambient sector.  It is zero on
a complementary sector and is the sector output state on a supported
sector.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--570. -/
noncomputable def MarkovDilationBlockForm.ambientSectorOutputFactor
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F)
    (s : AmbientMarkovBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K) :
    Matrix
      (Fin (ambientMarkovCommonDim F.jointSupport.m s) × Fin dC)
      (Fin (ambientMarkovCommonDim F.jointSupport.m s) × Fin dC) ℂ :=
  match s with
  | Sum.inl _ => 0
  | Sum.inr j => D.sectorOutputState j

@[simp]
theorem MarkovDilationBlockForm.ambientSectorOutputFactor_complement
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F)
    (z : Fin (dB - F.jointSupport.n)) :
    D.ambientSectorOutputFactor (Sum.inl z) =
      (0 : Matrix (Fin 1 × Fin dC) (Fin 1 × Fin dC) ℂ) :=
  rfl

@[simp]
theorem MarkovDilationBlockForm.ambientSectorOutputFactor_support
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    D.ambientSectorOutputFactor (Sum.inr j) = D.sectorOutputState j :=
  rfl

/-- The middle-system unitary with the orientation used by
`HayashiMarkovDecomposition`.  The Markov block equations use `F.U_B` from
adapted coordinates to physical coordinates, whereas Hayashi conjugates the
physical state into adapted coordinates and therefore uses `star F.U_B`.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (14)--(15),
lines 547--570. -/
def AmbientMarkovBipartiteBlockForm.hayashiMiddleUnitary
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    (F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm) :
    Matrix.unitaryGroup (Fin dB) ℂ :=
  ⟨star F.U_B, by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa only [star_star] using Matrix.mem_unitaryGroup_iff'.mp F.U_B_unitary⟩

@[simp]
theorem AmbientMarkovBipartiteBlockForm.coe_hayashiMiddleUnitary
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    (F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm) :
    (F.hayashiMiddleUnitary : Matrix (Fin dB) (Fin dB) ℂ) = star F.U_B :=
  rfl

/-- Ambient HJPW tripartite block data obtained from equality in strong
subadditivity.  The field `h_tripartite` is the unnormalized direct-sum
identity; no probabilities, normalized left factors, or density fillers are
included.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (11), (14), and
(15), lines 470--570. -/
structure MarkovTripartiteBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))] where
  F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm
  D : MarkovDilationBlockForm ρ_ABC hρ_dm F
  h_tripartite :
    let eB := ambientMarkovMiddleBlockEquiv F.e₀ F.jointSupport.e
    star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        (F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ))) *
        ρ_ABC *
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        (F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ))) =
      ambientTripartiteBlockMatrix eB F.jointSupport.ω
        D.sectorOutputState

/-- Equality in strong subadditivity yields the unnormalized ambient
tripartite direct sum in HJPW factor order, with no hypotheses beyond the
density-matrix and equality assumptions.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (11), (14), and
(15), lines 470--570. -/
theorem exists_markovTripartiteBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    letI : Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC)) :=
      activeConditionalEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
        rw [← trace_eq_trace_traceC_ABC]
        exact hρ_dm.2)
    Nonempty (MarkovTripartiteBlockForm ρ_ABC hρ_dm) := by
  classical
  letI : Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC)) :=
    activeConditionalEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
      rw [← trace_eq_trace_traceC_ABC]
      exact hρ_dm.2)
  obtain ⟨⟨F, D⟩⟩ := exists_markovDilationBlockForm ρ_ABC hρ_dm hSSA
  exact ⟨{
    F := F
    D := D
    h_tripartite := D.ambient_tripartite_block_form }⟩

end Matrix
