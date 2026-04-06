/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.StringOrderDefs
import TNLean.MPS.Symmetry.StringOrderAux
import TNLean.MPS.Symmetry.VirtualRepresentation
import TNLean.Algebra.CocycleCohomology

/-!
# String order parameters and local symmetry equivalence

This file proves the main equivalence theorems relating string order,
local symmetry, and spectral radius for injective MPS tensors, together
with the SPT phase classification results.

The core definitions (twisted transfer map, string order parameter, conditions
C1/C2/C3 and their equivalences) live in `TNLean.MPS.Symmetry.StringOrderDefs`.
The auxiliary TP-gauge infrastructure and long supporting proofs live in
`TNLean.MPS.Symmetry.StringOrderAux`.

## Main definitions

* `MPSTensor.IsSameSPTPhase` — two MPS are in the same SPT phase when their
  virtual representation cocycles are cohomologous

## Main results

* `MPSTensor.twistedTransfer_spectralRadius_le_one` — spectral radius bound
* `MPSTensor.twistedTransfer_modulus_one_implies_gaugePhase` — modulus-one
  rigidity bridge
* `MPSTensor.stringOrder_iff_localSymmetry` — string order ↔ local
  symmetry (for injective MPS)
* `MPSTensor.localSymmetry_iff_spectralRadius_one` — local symmetry ↔
  ρ(ℰ_u) = 1
* `MPSTensor.hasStringOrder_of_symmetric_injective` — string order holds
  universally for injective symmetric MPS with canonical FCS data
* `MPSTensor.stringOrder_invariant_of_samePhase` — string order is an
  SPT-phase invariant

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447 (PRL 2008)
* Chen, Gu, Wen, Phys. Rev. B 83, 035107 (2011) — SPT classification
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-! ### Main equivalence theorems -/

section MainTheorems

/-- **Spectral radius bound** (Lemma 1 of arXiv:0802.0447):
for an injective pure FCS, every eigenvalue of the twisted
transfer map `ℰ_u` has modulus at most `1`.

The proof follows a TP-gauge reduction: rewrite `ℰ_u` as a mixed
transfer map, pass to a common positive-definite fixed point of the
adjoint channels, gauge both Kraus families into trace-preserving
form, and invoke the existing mixed-transfer eigenvalue bound
`eigenvalue_norm_le_one`. -/
theorem twistedTransfer_spectralRadius_le_one
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (hNorm : transferMap A 1 = 1)
    (ev : ℂ) (V : Matrix (Fin D) (Fin D) ℂ)
    (hV : V ≠ 0)
    (hEig : twistedTransferMap A u V = ev • V) :
    ‖ev‖ ≤ 1 := by
  have hDpos : 0 < D := by
    by_contra hD
    have hD0 : D = 0 := Nat.eq_zero_of_not_pos hD
    subst hD0
    apply hV
    ext i j
    exact Fin.elim0 i
  haveI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
  let setup := twistedTPGaugeSetup (A := A) hA u hu hNorm
  have hHas : Module.End.HasEigenvalue
      (mixedTransferMap setup.A' setup.B') ev :=
    twistedTPGaugeSetup_hasEigenvalue
      (A := A) (u := u) (setup := setup) ev V hV hEig
  exact eigenvalue_norm_le_one
    (A := setup.A') (B := setup.B') setup.hA'TP setup.hB'TP ev hHas

/-- A modulus-one eigenvalue of the twisted transfer map forces the twisted
companion tensor to be gauge-phase equivalent to the original tensor. The proof
reuses the irreducible TP mixed-transfer rigidity theorem after passing both
families to a common TP gauge. -/
theorem twistedTransfer_modulus_one_implies_gaugePhase
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (hNorm : transferMap A 1 = 1)
    (ev : ℂ) (V : Matrix (Fin D) (Fin D) ℂ)
    (hV : V ≠ 0)
    (hEig : twistedTransferMap A u V = ev • V)
    (hev : ‖ev‖ = 1) :
    GaugePhaseEquiv A (twistedMixedCompanion A u) := by
  have hDpos : 0 < D := by
    by_contra hD
    have hD0 : D = 0 := Nat.eq_zero_of_not_pos hD
    subst hD0
    apply hV
    ext i j
    exact Fin.elim0 i
  haveI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
  let setup := twistedTPGaugeSetup (A := A) hA u hu hNorm
  have hHas : Module.End.HasEigenvalue (mixedTransferMap setup.A' setup.B') ev :=
    twistedTPGaugeSetup_hasEigenvalue
      (A := A) (u := u) (setup := setup) ev V hV hEig
  let Φ : (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) :=
    Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
  have hspec : ev ∈ spectrum ℂ (Φ (mixedTransferMap setup.A' setup.B')) := by
    rw [AlgEquiv.spectrum_eq Φ]
    exact hHas.mem_spectrum
  have hRadGe : mixedTransferSpectralRadius setup.A' setup.B' ≥ 1 := by
    rw [mixedTransferSpectralRadius_eq]
    have hnorm_ev_nn : (1 : NNReal) = ‖ev‖₊ := by
      apply Subtype.ext
      simpa using hev.symm
    have hnorm_ev : (1 : ENNReal) = ‖ev‖₊ := by
      exact congrArg (fun r : NNReal => (r : ENNReal)) hnorm_ev_nn
    rw [ge_iff_le, hnorm_ev]
    exact @le_iSup₂ ENNReal ℂ (· ∈ spectrum ℂ (Φ (mixedTransferMap setup.A' setup.B'))) _
      (fun k _ => (‖k‖₊ : ENNReal)) ev hspec
  have hGauge' : GaugePhaseEquiv setup.A' setup.B' :=
    modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
      setup.A' setup.B' setup.hIrrA' setup.hIrrB' setup.hA'TP setup.hB'TP hRadGe
  simpa [setup.hA'_def, setup.hB'_def, setup.hB_def] using
    gaugePhaseEquiv_of_gaugeEquiv_left_right
    (gaugeEquiv_tpGauge (A := A) (ρ := setup.σ) setup.hσ_pd)
    hGauge'
    (gaugeEquiv_tpGauge (A := setup.B) (ρ := setup.σ) setup.hσ_pd)

/-- A non-decaying string-order parameter forces the twisted companion family to be
gauge-phase equivalent to the original tensor. This is the reuse-heavy bridge from
string order to the mixed-transfer peripheral spectrum. -/
theorem gaugePhaseEquiv_twisted_of_hasStringOrder
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hNorm : transferMap A 1 = 1)
    (hSO : HasStringOrder A u Λ) :
    GaugePhaseEquiv A (twistedMixedCompanion A u) := by
  rcases eq_or_ne D 0 with hD | hD
  · subst hD
    exact ⟨1, 1, one_ne_zero, fun i => by ext a; exact Fin.elim0 a⟩
  haveI : NeZero D := ⟨hD⟩
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (twistedTransferMap A u)
  obtain ⟨X, Y, hnot0⟩ := not_tendsto_zero_of_hasStringOrder A u Λ hSO
  have hsr_ge : spectralRadius ℂ F' ≥ 1 := by
    have hsr_not_lt : ¬ spectralRadius ℂ F' < 1 := by
      intro hlt
      exact hnot0 (stringOrderBoundaryParam_tendsto_zero_of_spectralRadius_lt_one
        A u Λ X Y <| by simpa [F'] using hlt)
    exact le_of_not_gt hsr_not_lt
  haveI : Nontrivial V := by
    haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
    exact Matrix.nonempty
  haveI : Nontrivial (V →L[ℂ] V) := ContinuousLinearMap.instNontrivialId
  haveI : FiniteDimensional ℂ (V →L[ℂ] V) := Φ.toLinearEquiv.finiteDimensional
  have hF'_nonempty : (spectrum ℂ F').Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ F'
  have hcompact : IsCompact (spectrum ℂ F') := by
    let hComplete : CompleteSpace (V →L[ℂ] V) := FiniteDimensional.complete ℂ (V →L[ℂ] V)
    exact @spectrum.isCompact ℂ (V →L[ℂ] V)
      inferInstance inferInstance inferInstance hComplete inferInstance F'
  obtain ⟨μ, hμ_spec, hμ_max⟩ :=
    hcompact.exists_isMaxOn hF'_nonempty continuous_nnnorm.continuousOn
  have hμ_rad : (‖μ‖₊ : ENNReal) = spectralRadius ℂ F' := by
    exact le_antisymm (le_iSup₂ (α := ENNReal) μ hμ_spec) (iSup₂_le <| mod_cast hμ_max)
  have hμ_spec_end : μ ∈ spectrum ℂ (twistedTransferMap A u) := by
    rw [← AlgEquiv.spectrum_eq Φ]
    exact hμ_spec
  have hμ_ev : Module.End.HasEigenvalue (twistedTransferMap A u) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec_end
  obtain ⟨X, hX_mem, hX_ne⟩ := hμ_ev.exists_hasEigenvector
  have hFX : twistedTransferMap A u X = μ • X :=
    Module.End.mem_eigenspace_iff.mp hX_mem
  have hμ_le : ‖μ‖ ≤ 1 :=
    twistedTransfer_spectralRadius_le_one A hA u hu hNorm μ X hX_ne hFX
  have hμ_ge : (1 : ENNReal) ≤ ‖μ‖₊ := by
    rw [hμ_rad]
    exact hsr_ge
  have hμ_eq : ‖μ‖ = 1 := le_antisymm hμ_le <| by
    rw [ENNReal.one_le_coe_iff] at hμ_ge
    exact_mod_cast hμ_ge
  exact twistedTransfer_modulus_one_implies_gaugePhase
    A hA u hu hNorm μ X hX_ne hFX hμ_eq

/-- Local symmetry provides a non-decaying boundary witness for the twisted
transfer powers. Choosing `X = V†` and `Y = V` turns the boundary sequence into
`μ^L tr(Λ)`. -/
lemma hasStringOrder_of_localSymmetry
    (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛtr : Matrix.trace Λ = 1)
    (hNorm : transferMap A 1 = 1)
    (hLocal : IsLocalSymmetry A u Λ) :
    HasStringOrder A u Λ := by
  rcases hLocal with ⟨V, μ, hV, hV', hμ, -, hC1μ⟩
  have hEig : twistedTransferMap A u V = μ • V :=
    twistedTransfer_eigen_of_virtualUnitary A u V μ hNorm hV hC1μ
  have hpow :
      ∀ L : ℕ, ((twistedTransferMap A u) ^ L) V = μ ^ L • V := by
    intro L
    induction L with
    | zero =>
        simp
    | succ n ih =>
        calc
          ((twistedTransferMap A u) ^ (n + 1)) V
              = twistedTransferMap A u (((twistedTransferMap A u) ^ n) V) := by
                  simp [pow_succ']
          _ = twistedTransferMap A u (μ ^ n • V) := by rw [ih]
          _ = μ ^ n • twistedTransferMap A u V := by simp
          _ = μ ^ n • (μ • V) := by rw [hEig]
          _ = μ ^ (n + 1) • V := by
                simp [pow_succ, smul_smul, mul_comm]
  refine ⟨Vᴴ, V, (1 / 2 : ℝ), by norm_num, ?_⟩
  intro L
  have hparam :
      stringOrderBoundaryParam A u Λ Vᴴ V L = μ ^ L := by
    calc
      stringOrderBoundaryParam A u Λ Vᴴ V L
          = Matrix.trace (Λ * Vᴴ * (((twistedTransferMap A u) ^ L) V)) := by
              simp [stringOrderBoundaryParam, twistedTransferIter]
      _ = Matrix.trace (Λ * Vᴴ * (μ ^ L • V)) := by rw [hpow L]
      _ = Matrix.trace ((μ ^ L) • (Λ * (Vᴴ * V))) := by
            simp [Matrix.mul_assoc]
      _ = μ ^ L * Matrix.trace (Λ * (Vᴴ * V)) := by
            simp [Matrix.trace_smul]
      _ = μ ^ L := by simp [hV', hΛtr]
  have hnorm_pow : ‖μ ^ L‖ = 1 := by
    simp [norm_pow, hμ]
  have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
  calc
    (1 / 2 : ℝ) ≤ 1 := hhalf
    _ = ‖μ ^ L‖ := by rw [hnorm_pow]
    _ = ‖stringOrderBoundaryParam A u Λ Vᴴ V L‖ := by rw [hparam]

/-- A modulus-one twisted-transfer eigenpair yields the paper's local-symmetry
virtual witness once the stationary boundary state is fixed by the adjoint
transfer channel. -/
private theorem localSymmetry_of_twistedTransfer_eigen
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : transferMap A 1 = 1)
    (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ≠ 0)
    (hEig : twistedTransferMap A u X = ev • X)
    (hev : ‖ev‖ = 1) :
    IsLocalSymmetry A u Λ := by
  have hGauge : GaugePhaseEquiv A (twistedMixedCompanion A u) :=
    twistedTransfer_modulus_one_implies_gaugePhase A hA u hu hNorm ev X hX hEig hev
  obtain ⟨V, μ, hV, hV', hμ, hC1μ⟩ :=
    virtualUnitary_of_gaugePhaseEquiv_twisted A hA u hu hNorm hGauge
  have hΛinv : Vᴴ * Λ * V = Λ :=
    boundaryState_invariant_of_virtualUnitary A hA u hu Λ hΛpos hΛtr hΛfix
      V μ hV hV' hμ hC1μ
  exact ⟨V, μ, hV, hV', hμ, hΛinv, hC1μ⟩

/-- **Theorem 2** (arXiv:0802.0447): For a pure finitely correlated
state, `u` is a local symmetry if and only if the twisted transfer
map `ℰ_u` has a unitary eigenvector with unit-modulus eigenvalue.

The right-hand side is the witness form of `ρ(ℰ_u) = 1`:
combined with `twistedTransfer_spectralRadius_le_one` (all
eigenvalues satisfy `|λ| ≤ 1`), existence of an eigenvalue with
`|μ| = 1` is equivalent to `spectralRadius(ℰ_u) = 1`.

Here `IsLocalSymmetry` is formalized in the virtual form supplied by
Lemma 1 of the paper, and the theorem assumes the canonical fixed-point
hypothesis `transferMap A† Λ = Λ` needed to recover `V† Λ V = Λ`. -/
theorem localSymmetry_iff_spectralRadius_one
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : transferMap A 1 = 1) :
    IsLocalSymmetry A u Λ ↔
      ∃ V : Matrix (Fin D) (Fin D) ℂ,
        V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
        ∃ μ : ℂ, ‖μ‖ = 1 ∧
          twistedTransferMap A u V = μ • V := by
  constructor
  · rintro ⟨V, μ, hV, hV', hμ, -, hC1μ⟩
    refine ⟨V, hV, hV', μ, hμ, ?_⟩
    exact twistedTransfer_eigen_of_virtualUnitary A u V μ hNorm hV hC1μ
  · rintro ⟨V, hV, hV', μ, hμ, hEig⟩
    have hV_ne : V ≠ 0 := by
      rcases eq_or_ne D 0 with hD | hD
      · subst hD
        simp at hΛtr
      · intro hV0
        have hzero : (0 : Matrix (Fin D) (Fin D) ℂ) = 1 := by simpa [hV0] using hV
        have hentry :=
          congrFun (congrFun hzero ⟨0, Nat.pos_of_ne_zero hD⟩) ⟨0, Nat.pos_of_ne_zero hD⟩
        simp at hentry
    exact localSymmetry_of_twistedTransfer_eigen
      A hA u hu Λ hΛpos hΛtr hΛfix hNorm μ V hV_ne hEig hμ

/-- **Theorem 1** (arXiv:0802.0447, virtual-boundary form): String order
exists for a pure canonical FCS if and only if `u` is a local symmetry.

The Lean definition `HasStringOrder A u Λ` packages the paper's endpoint
operators `x,y` as arbitrary virtual boundary matrices `X,Y`, so the theorem is
stated directly at the transfer-matrix level. -/
theorem stringOrder_iff_localSymmetry
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : transferMap A 1 = 1) :
    HasStringOrder A u Λ ↔ IsLocalSymmetry A u Λ := by
  constructor
  · intro hSO
    have hGauge : GaugePhaseEquiv A (twistedMixedCompanion A u) :=
      gaugePhaseEquiv_twisted_of_hasStringOrder A hA u hu Λ hNorm hSO
    obtain ⟨V, μ, hV, hV', hμ, hC1μ⟩ :=
      virtualUnitary_of_gaugePhaseEquiv_twisted A hA u hu hNorm hGauge
    have hΛinv : Vᴴ * Λ * V = Λ :=
      boundaryState_invariant_of_virtualUnitary A hA u hu Λ hΛpos hΛtr hΛfix
        V μ hV hV' hμ hC1μ
    exact ⟨V, μ, hV, hV', hμ, hΛinv, hC1μ⟩
  · intro hLocal
    exact hasStringOrder_of_localSymmetry A u Λ hΛtr hNorm hLocal

/-- **Virtual symmetry from string order**: If string order exists
for `u`, then there exists a virtual unitary `V` and a
unit-modulus scalar `μ` satisfying a phased intertwining relation
`∑_j u_{ij} A_j = μ • (V A_i V†)`.

The phase `μ` is necessary: for `u = e^{iθ} · 1` (a global
phase), string order holds but `CondC1` (without phase) would
force `e^{iθ} = 1`. The phased form matches the projective
symmetry statement from `VirtualRepresentation.lean`. -/
theorem virtualUnitary_of_stringOrder
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hNorm : transferMap A 1 = 1)
    (hSO : HasStringOrder A u Λ) :
    ∃ V : Matrix (Fin D) (Fin D) ℂ, ∃ μ : ℂ,
      V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ ‖μ‖ = 1 ∧
      ∀ i : Fin d,
        ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ) := by
  have hGauge : GaugePhaseEquiv A (twistedMixedCompanion A u) :=
    gaugePhaseEquiv_twisted_of_hasStringOrder A hA u hu Λ hNorm hSO
  exact virtualUnitary_of_gaugePhaseEquiv_twisted A hA u hu hNorm hGauge

end MainTheorems

/-! ### SPT phase classification

Two injective symmetric MPS tensors are in the same SPT phase when their virtual
representation cocycles are cohomologous.  The main result of this section is that
string order is an invariant of the SPT phase: for canonical finitely correlated
states, the virtual representation gauge matrix is always a fixed point of the
twisted transfer map (eigenvalue 1), so `HasStringOrder` holds universally and the
phase-invariance `↔` is immediate.

### References

* Chen, Gu, Wen, *Classification of gapped symmetric phases in one-dimensional
  spin systems*, Phys. Rev. B 83, 035107 (2011)
* Pérez-García et al., arXiv:0802.0447
-/

section SPTDetection

open TNLean.Algebra

variable {G : Type*} [Group G]

/-- Two MPS tensors with the same on-site symmetry are in the **same SPT phase** if
there exist virtual representation cocycles that intertwine the respective tensors
and are cohomologous.  This is the topological invariant classifying
symmetry-protected topological phases in one dimension (Chen–Gu–Wen 2011). -/
def IsSameSPTPhase (A B : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (ωA ωB : ScalarCocycle G)
    (ρA : ProjectiveRepresentation (D := D) ωA)
    (ρB : ProjectiveRepresentation (D := D) ωB),
    (∀ g i, twistedTensor A U g i =
      (ρA.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρA.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ∧
    (∀ g i, twistedTensor B U g i =
      (ρB.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * B i *
        (((ρB.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ∧
    ScalarCocycle.CohomologousTo ωA ωB

/-- `IsSameSPTPhase` implies on-site symmetry for the first tensor: the virtual
representation intertwining gives a gauge equivalence between `A` and each
twisted tensor, which implies `SameMPV`. -/
theorem IsSameSPTPhase.isOnSiteSymmetric_left
    {A B : MPSTensor d D} {U : G →* Matrix (Fin d) (Fin d) ℂ}
    (h : IsSameSPTPhase A B U) : IsOnSiteSymmetric A U := by
  obtain ⟨_, _, ρA, _, hA, _, _⟩ := h
  intro g
  exact GaugeEquiv.sameMPV ⟨ρA.X (g⁻¹), fun i => hA g i⟩

/-- `IsSameSPTPhase` implies on-site symmetry for the second tensor. -/
theorem IsSameSPTPhase.isOnSiteSymmetric_right
    {A B : MPSTensor d D} {U : G →* Matrix (Fin d) (Fin d) ℂ}
    (h : IsSameSPTPhase A B U) : IsOnSiteSymmetric B U := by
  obtain ⟨_, _, _, ρB, _, hB, _⟩ := h
  intro g
  exact GaugeEquiv.sameMPV ⟨ρB.X (g⁻¹), fun i => hB g i⟩

/-- For an injective symmetric MPS with canonical FCS data, the twisted transfer
map has the virtual representation gauge matrix as a fixed point (eigenvalue 1).
This is immediate from the virtual representation intertwining relation and the
normalization `transferMap A 1 = 1`. -/
private lemma twistedTransfer_virtual_rep_fixed
    (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hNorm : transferMap A 1 = 1)
    {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g i, twistedTensor A U g i =
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (g : G) :
    twistedTransferMap A (U g)
      ((ρ.X (g⁻¹) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      ((ρ.X (g⁻¹) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  let V := ((ρ.X (g⁻¹) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  let Vinv := (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hVinvV : Vinv * V = 1 := by show
    (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
      ((ρ.X g⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1; simp
  show twistedTransferMap A (U g) V = V
  rw [twistedTransferMap_apply]
  rw [Finset.sum_comm]
  -- Each inner sum simplifies via virtual rep
  have htwist : ∀ n' : Fin d,
      (∑ n : Fin d, U g n' n • A n) = V * A n' * Vinv := hρ g
  have hterm : ∀ n' : Fin d,
      ∑ n : Fin d, U g n' n • (A n * V * (A n')ᴴ) =
        V * A n' * (A n')ᴴ := by
    intro n'
    calc ∑ n : Fin d, U g n' n • (A n * V * (A n')ᴴ)
        = ∑ n : Fin d, (U g n' n • A n) * (V * (A n')ᴴ) := by
          congr 1; funext n; rw [smul_mul_assoc, Matrix.mul_assoc]
      _ = (∑ n : Fin d, U g n' n • A n) * (V * (A n')ᴴ) :=
          (Finset.sum_mul ..).symm
      _ = V * A n' * Vinv * (V * (A n')ᴴ) := by rw [htwist n']
      _ = V * A n' * (Vinv * V) * (A n')ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = V * A n' * (A n')ᴴ := by rw [hVinvV, Matrix.mul_one]
  simp_rw [hterm]
  -- Now: ∑_{n'} V * A n' * (A n')ᴴ = V
  simp_rw [Matrix.mul_assoc V]
  rw [← Finset.mul_sum]
  have : ∑ n' : Fin d, A n' * (A n')ᴴ = transferMap A 1 := by
    rw [transferMap_apply]; congr 1; funext n'; rw [Matrix.mul_one]
  rw [this, hNorm, Matrix.mul_one]

/-- For an injective symmetric MPS with canonical FCS data and unitary on-site
representation, `HasStringOrder` holds universally for every group element.

The proof chains:
1. Virtual rep gives an eigenvector of twisted transfer with eigenvalue 1
2. `twistedTransfer_modulus_one_implies_gaugePhase` gives gauge-phase equivalence
3. `virtualUnitary_of_gaugePhaseEquiv_twisted` normalizes to a unitary intertwining
4. `boundaryState_invariant_of_virtualUnitary` shows the unitary preserves `Λ`
5. `hasStringOrder_of_localSymmetry` closes the argument -/
theorem hasStringOrder_of_symmetric_injective
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U)
    (hUnitary : ∀ g : G, U g * (U g)ᴴ = 1)
    (g : G)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : transferMap A 1 = 1) :
    HasStringOrder A (U g) Λ := by
  -- Step 1: Get virtual representation
  obtain ⟨ω, ρ, hρ⟩ := virtual_rep_of_symmetric_injective A hA U hSymm
  -- Step 2: Virtual rep gauge matrix is eigenvector with eigenvalue 1
  set V : Matrix (Fin D) (Fin D) ℂ :=
    ((ρ.X (g⁻¹) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hEig : twistedTransferMap A (U g) V = (1 : ℂ) • V := by
    rw [one_smul]
    exact twistedTransfer_virtual_rep_fixed A U hNorm ρ hρ g
  -- Step 3: V is nonzero (it's invertible); handle D = 0 vacuously
  rcases eq_or_ne D 0 with hD | hD
  · subst hD; simp at hΛtr
  haveI : NeZero D := ⟨hD⟩
  have hV_ne : V ≠ 0 := by
    intro hV0
    have h1 : V * (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 := by
      simp [V]
    rw [hV0, zero_mul] at h1
    exact one_ne_zero h1.symm
  -- Step 4: Modulus-one eigenvalue → GaugePhaseEquiv
  have hGauge : GaugePhaseEquiv A (twistedMixedCompanion A (U g)) :=
    twistedTransfer_modulus_one_implies_gaugePhase A hA (U g) (hUnitary g)
      hNorm 1 V hV_ne hEig (by simp)
  -- Step 5: GaugePhaseEquiv → virtual unitary with phase
  obtain ⟨W, μ, hW, hW', hμ, hC1μ⟩ :=
    virtualUnitary_of_gaugePhaseEquiv_twisted A hA (U g) (hUnitary g) hNorm hGauge
  -- Step 6: Virtual unitary preserves boundary state
  have hΛinv : Wᴴ * Λ * W = Λ :=
    boundaryState_invariant_of_virtualUnitary A hA (U g) (hUnitary g)
      Λ hΛpos hΛtr hΛfix W μ hW hW' hμ hC1μ
  -- Step 7: Assemble IsLocalSymmetry and derive HasStringOrder
  exact hasStringOrder_of_localSymmetry A (U g) Λ hΛtr hNorm
    ⟨W, μ, hW, hW', hμ, hΛinv, hC1μ⟩

/-- **String order is an SPT-phase invariant.**  If two injective MPS tensors
are both on-site symmetric under the same representation `U` and satisfy
the canonical normalisation hypotheses, then string order for any group
element `g` holds for one iff it holds for the other.

In the SPT classification context, `IsSameSPTPhase A B U` implies
`IsOnSiteSymmetric` for both tensors (via
`IsSameSPTPhase.isOnSiteSymmetric_left/right`), so this theorem applies
to tensors in the same phase.  The statement is kept in terms of
`IsOnSiteSymmetric` directly so the hypotheses match what the proof
actually uses. -/
theorem stringOrder_invariant_of_samePhase
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hUnitary : ∀ g : G, U g * (U g)ᴴ = 1)
    (hSymmA : IsOnSiteSymmetric A U)
    (hSymmB : IsOnSiteSymmetric B U)
    (Λ_A Λ_B : Matrix (Fin D) (Fin D) ℂ)
    (hΛApos : Λ_A.PosDef) (hΛBpos : Λ_B.PosDef)
    (hΛAtr : Matrix.trace Λ_A = 1) (hΛBtr : Matrix.trace Λ_B = 1)
    (hΛAfix : transferMap (fun i => (A i)ᴴ) Λ_A = Λ_A)
    (hΛBfix : transferMap (fun i => (B i)ᴴ) Λ_B = Λ_B)
    (hNormA : transferMap A 1 = 1)
    (hNormB : transferMap B 1 = 1) :
    ∀ g : G, HasStringOrder A (U g) Λ_A ↔ HasStringOrder B (U g) Λ_B := by
  intro g
  exact ⟨fun _ => hasStringOrder_of_symmetric_injective B hB U
              hSymmB hUnitary g Λ_B hΛBpos hΛBtr hΛBfix hNormB,
         fun _ => hasStringOrder_of_symmetric_injective A hA U
              hSymmA hUnitary g Λ_A hΛApos hΛAtr hΛAfix hNormA⟩

end SPTDetection

end MPSTensor
