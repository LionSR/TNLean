/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Core.Correlations
import TNLean.Spectral.MixedTransfer

/-!
# Zero correlation length (ZCL) for MPS tensors

This file defines single-block zero-correlation-length (ZCL) conditions for MPS
tensors, following arXiv:1606.00608 Section 3.2
(Cirac–Pérez-García–Schuch–Verstraete).

The following conditions are introduced:

* `IsPositiveGapPhysicalCID A` — physical block-observable correlations are
  independent of distance when both complementary gaps are positive.
* `IsCID A` — the stronger virtual-insertion CID condition used by the current
  converse theorem.
* `IsLocallyOrthogonal A` — the local single-block convention used here; it is
  transfer-map idempotence.
* `IsBNTLocallyOrthogonal blocks` — the source BNT-level mixed-sector
  equations.
* `IsBNTZCL A blocks` — the older virtual-insertion BNT surrogate.
* `IsPositiveGapBNTZCL A blocks` — the physical positive-gap BNT condition.
* `IsZCL A` — the conjunction of local orthogonality and CID.

The proved local result identifies this single-block convention with an
idempotent transfer map (`IsRFP`).  Neither BNT predicate records the source
condition for all disjoint regions; the full BNT-level ZCL theorem is tracked in
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}
variable {g : ℕ} {dim : Fin g → ℕ}

/-- The transfer insertion associated with an observable on a block of `L`
physical spins.  If `σ, τ : Fin L → Fin d` label basis words, then
`physicalObservableTransfer A L O X` equals
$\sum_{\sigma,\tau} O_{\tau,\sigma}\, A^{\sigma} X (A^{\tau})^{\dagger}$.

This is the matrix $\mathbb{E}_O$ appearing in arXiv:1606.00608, equation Corr
(lines 490--496), written as a map on virtual matrices. -/
noncomputable def physicalObservableTransfer (A : MPSTensor d D) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ σ : Fin L → Fin d, ∑ τ : Fin L → Fin d,
    O τ σ • ((LinearMap.mulLeft ℂ (evalWord A (List.ofFn σ))).comp
      (LinearMap.mulRight ℂ (evalWord A (List.ofFn τ))ᴴ))

/-- The periodic-chain two-region expectation obtained by placing observables
`O₁` and `O₂` on physical blocks, with `n₁` and `n₂` unobserved sites in the two
complementary arcs.  This is the trace formula in arXiv:1606.00608, equation
Corr (lines 490--496). -/
noncomputable def physicalTwoPointExpectation (A : MPSTensor d D)
    (L₁ L₂ : ℕ)
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ)
    (n₁ n₂ : ℕ) : ℂ :=
  LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
    (physicalObservableTransfer A L₂ O₂ ∘ₗ ((transferMap A) ^ n₂) ∘ₗ
      physicalObservableTransfer A L₁ O₁ ∘ₗ ((transferMap A) ^ n₁))

/-- Positive-gap physical correlations independent of distance, in the transfer
formula surrounding arXiv:1606.00608, Definition 3.3 and equation Corr (lines
437--445 and 490--496): translating either of two physical block observables
through the unobserved part of a fixed periodic chain does not change their
two-region expectation.  Thus the two complementary gaps may change while
their sum, and hence the chain length, remains fixed.

The definition permits observables on blocks of arbitrary finite lengths and
does not replace physical observables by arbitrary virtual bond matrices.

**Scope restriction (arXiv:1606.00608, Definition 3.3):** the source quantifies
over all disjoint regions, including adjacent regions.  Here both complementary
gaps are required to be positive.  If a gap is zero, equation Corr contains
$\mathbb{E}^0 = 1$, which does not follow from $\mathbb{E}^2 = \mathbb{E}$.  See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
def IsPositiveGapPhysicalCID (A : MPSTensor d D) : Prop :=
  ∀ (L₁ L₂ : ℕ)
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ)
    (n₁ n₂ m₁ m₂ : ℕ),
    1 ≤ n₁ → 1 ≤ n₂ → 1 ≤ m₁ → 1 ≤ m₂ → n₁ + n₂ = m₁ + m₂ →
    physicalTwoPointExpectation A L₁ L₂ O₁ O₂ n₁ n₂ =
      physicalTwoPointExpectation A L₁ L₂ O₁ O₂ m₁ m₂

/-- Virtual-insertion correlations independent of distance: the connected
two-point expression through the transfer map is constant in the separation
for all virtual bond matrices.

For every positive definite right fixed point `ρR` of the transfer map, the
connected correlator
$C(X,Y;n) = \langle X_0 Y_n \rangle - \langle X \rangle \langle Y \rangle$ is
the same for all separations `n ≥ 1` and all bond matrices `X`, `Y`.

**Scope restriction:** this is a virtual-insertion surrogate, not Definition
3.3 of the source.  It is also vacuous when no positive definite fixed point
exists.  It is retained for the existing virtual converse theorem; the
positive-gap physical predicate is `IsPositiveGapPhysicalCID` above.  See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
def IsCID (A : MPSTensor d D) : Prop :=
  ∀ (ρR : Matrix (Fin D) (Fin D) ℂ),
    ρR.PosDef → transferMap A ρR = ρR →
    ∀ (X Y : Matrix (Fin D) (Fin D) ℂ) (n m : ℕ),
      1 ≤ n → 1 ≤ m →
      connectedCorrelator A ρR X Y n = connectedCorrelator A ρR X Y m

/-- Idempotence of the transfer map implies positive-gap physical CID.

This is the positive-gap part of the forward implication stated immediately
before arXiv:1606.00608, Theorem TheoremZCLPure (lines 498--502).  Equation
Corr shows the reason directly: every positive power of an idempotent
transfer map equals the transfer map itself.

**Scope restriction:** adjacent regions are not covered because idempotence
does not identify $\mathbb{E}^0$ with $\mathbb{E}$.  This is recorded in
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem isPositiveGapPhysicalCID_of_isRFP (A : MPSTensor d D) (hRFP : IsRFP A) :
    IsPositiveGapPhysicalCID A := by
  intro L₁ L₂ O₁ O₂ n₁ n₂ m₁ m₂ hn₁ hn₂ hm₁ hm₂ _
  have hIdem : IsIdempotentElem (transferMap A) := hRFP
  have hpow_n₁ : (transferMap A) ^ n₁ = transferMap A :=
    hIdem.pow_eq (by omega)
  have hpow_n₂ : (transferMap A) ^ n₂ = transferMap A :=
    hIdem.pow_eq (by omega)
  have hpow_m₁ : (transferMap A) ^ m₁ = transferMap A :=
    hIdem.pow_eq (by omega)
  have hpow_m₂ : (transferMap A) ^ m₂ = transferMap A :=
    hIdem.pow_eq (by omega)
  simp only [physicalTwoPointExpectation, hpow_n₁, hpow_n₂, hpow_m₁, hpow_m₂]

/-- Local orthogonality in the single-block convention used by this file:
the self-transfer map is idempotent. Thus, for one tensor `A`, this is
definitionally equivalent to `IsRFP A` (see `isLocallyOrthogonal_iff_isRFP`).

**Scope restriction (arXiv:1606.00608, Definition 3.5):** in the source, local
orthogonality is a BNT-level condition: for distinct BNT components `j ≠ k`, the
mixed transfer maps vanish. This one-tensor predicate has no mixed sectors and
does not formalize those equations. The missing BNT-level statement is recorded
in `docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
def IsLocallyOrthogonal (A : MPSTensor d D) : Prop :=
  IsRFP A

/-- `IsLocallyOrthogonal` is definitionally equal to `IsRFP` for a single
BNT block. -/
lemma isLocallyOrthogonal_iff_isRFP (A : MPSTensor d D) :
    IsLocallyOrthogonal A ↔ IsRFP A :=
  Iff.rfl

/-- BNT-level local orthogonality (arXiv:1606.00608, Definition 3.5):
for distinct BNT components `j ≠ j'`, the mixed-sector transfer matrix
$\mathbb{E}_{j,j'} = \sum_i A_j^i \otimes \overline{A_{j'}^i}$ vanishes.

This is the source local-orthogonality condition used in the pure-state ZCL
theorem. The rectangular mixed transfer operator is the corresponding linear
map form of the displayed mixed-sector matrix. -/
def IsBNTLocallyOrthogonal
    (blocks : (j : Fin g) → MPSTensor d (dim j)) : Prop :=
  ∀ j j' : Fin g, j ≠ j' → mixedTransferMap₂ (blocks j) (blocks j') = 0

/-- Unfolding of BNT-level local orthogonality into the mixed transfer
equations. -/
lemma isBNTLocallyOrthogonal_iff
    (blocks : (j : Fin g) → MPSTensor d (dim j)) :
    IsBNTLocallyOrthogonal blocks ↔
      ∀ j j' : Fin g, j ≠ j' → mixedTransferMap₂ (blocks j) (blocks j') = 0 :=
  Iff.rfl

/-- BNT-level virtual-insertion zero correlation length: `blocks` is a basis of
normal tensors for `A`, the virtual correlator is independent of distance, and
the mixed-sector local-orthogonality equations hold.

**Scope restriction (arXiv:1606.00608, Definition 3.6):** `IsCID` is the older
virtual-insertion surrogate, rather than the source predicate on all disjoint
physical regions.  Thus this definition is not the source ZCL definition.  See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
def IsBNTZCL (A : MPSTensor d D)
    (blocks : (j : Fin g) → MPSTensor d (dim j)) : Prop :=
  IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, blocks j⟩) ∧
    IsCID A ∧ IsBNTLocallyOrthogonal blocks

/-- Unfolding of BNT-level zero correlation length into the BNT relation, CID,
and BNT local orthogonality. -/
lemma isBNTZCL_iff (A : MPSTensor d D)
    (blocks : (j : Fin g) → MPSTensor d (dim j)) :
    IsBNTZCL A blocks ↔
      IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, blocks j⟩) ∧
        IsCID A ∧ IsBNTLocallyOrthogonal blocks :=
  Iff.rfl

/-- Positive-gap BNT zero correlation length: a BNT family satisfies the
mixed-sector local-orthogonality equations, while physical block-observable
correlations are independent of the separation whenever both complementary
gaps are positive.

**Scope restriction (arXiv:1606.00608, Definition 3.6):** the source permits
arbitrary disjoint regions, including adjacent regions for which a
complementary transfer power is $\mathbb{E}^0$.  This predicate excludes those
cases.
It is therefore a positive-gap consequence of transfer idempotence, not the
source ZCL predicate.  See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
def IsPositiveGapBNTZCL (A : MPSTensor d D)
    (blocks : (j : Fin g) → MPSTensor d (dim j)) : Prop :=
  IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, blocks j⟩) ∧
    IsPositiveGapPhysicalCID A ∧ IsBNTLocallyOrthogonal blocks

/-- Unfolding of positive-gap BNT zero correlation length into the BNT
relation, positive-gap physical CID, and BNT local orthogonality. -/
lemma isPositiveGapBNTZCL_iff (A : MPSTensor d D)
    (blocks : (j : Fin g) → MPSTensor d (dim j)) :
    IsPositiveGapBNTZCL A blocks ↔
      IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, blocks j⟩) ∧
        IsPositiveGapPhysicalCID A ∧ IsBNTLocallyOrthogonal blocks :=
  Iff.rfl

/-- Zero correlation length in the single-block convention: a tensor has ZCL
when it satisfies the local idempotence convention above and has correlations
independent of distance.

**Scope restriction (arXiv:1606.00608, Definition 3.6):** the source definition
combines CID with BNT-level local orthogonality. Since `IsLocallyOrthogonal`
above is the single-block idempotence convention, this predicate should not be
read as the full source definition for a multi-block BNT family. See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
def IsZCL (A : MPSTensor d D) : Prop :=
  IsLocallyOrthogonal A ∧ IsCID A

/-- **Virtual-insertion distance independence implies RFP.**

For a tensor with a positive-definite fixed point, independence of the
virtual-insertion correlator implies that the transfer map is idempotent.

The proof uses trace nondegeneracy: IsCID forces
$\operatorname{tr}(Y\, E^n(X \rho_R))$ to be constant in `n` for all `X`, `Y`,
so $E^n(X \rho_R)$ is constant. Since `ρR` is PosDef (hence invertible),
$X \rho_R$ ranges over all matrices, giving $E^2 = E$.

**Scope restriction (virtual insertions):** `IsCID` quantifies over arbitrary
virtual bond matrices, rather than the physical block observables in
arXiv:1606.00608, Definition 3.3 and Theorem TheoremZCLPure.  The missing
physical-realization step from lines 1250--1258 is recorded in
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem isCID_implies_isRFP
    (A : MPSTensor d D)
    (ρR : Matrix (Fin D) (Fin D) ℂ)
    (hρ_pd : ρR.PosDef)
    (hρ_fix : transferMap A ρR = ρR)
    (hCID : IsCID A) : IsRFP A := by
  change transferMap A ∘ₗ transferMap A = transferMap A
  obtain ⟨u, rfl⟩ := hρ_pd.isUnit
  apply LinearMap.ext; intro Z
  simp only [LinearMap.comp_apply]
  -- Write Z = X * ↑u using invertibility of ρR (PosDef ⟹ IsUnit)
  set X := Z * (↑u⁻¹ : Matrix (Fin D) (Fin D) ℂ) with hX
  have hZ : Z = X * (u : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hX, mul_assoc, Units.inv_mul, mul_one]
  rw [hZ]
  -- By trace nondegeneracy, suffices: E(E(X·ρR)) - E(X·ρR) = 0
  suffices h_diff : transferMap A (transferMap A (X * (u : Matrix (Fin D) (Fin D) ℂ))) -
      transferMap A (X * (u : Matrix (Fin D) (Fin D) ℂ)) = 0 from
    eq_of_sub_eq_zero h_diff
  apply (Matrix.ext_iff_trace_mul_right
    (A := transferMap A (transferMap A (X * (u : Matrix (Fin D) (Fin D) ℂ))) -
      transferMap A (X * (u : Matrix (Fin D) (Fin D) ℂ)))
    (B := 0)).2
  intro N
  -- From IsCID with n=2, m=1: correlator equality gives trace equality
  have h := hCID ↑u hρ_pd hρ_fix X N 2 1 (by omega) (by omega)
  simp only [connectedCorrelator_def, twoPointExpectation_transfer] at h
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply] at h
  -- h : tr(N * E(E(X*ρR))) - c = tr(N * E(X*ρR)) - c, so extract equality
  have heq := sub_left_injective h
  -- Goal: tr((E(E(X*ρR)) - E(X*ρR)) * N) = 0
  rw [sub_mul, Matrix.trace_sub,
    Matrix.trace_mul_comm _ N, Matrix.trace_mul_comm _ N]
  calc
    Matrix.trace (N * transferMap A (transferMap A (X * (u : Matrix (Fin D) (Fin D) ℂ)))) -
        Matrix.trace (N * transferMap A (X * (u : Matrix (Fin D) (Fin D) ℂ))) = 0 :=
      sub_eq_zero.mpr heq
    _ = Matrix.trace (0 * N) := by simp

/-- Single-block ZCL is equivalent to transfer-map idempotence (i.e. `IsRFP`).

Forward: `IsZCL → IsRFP` is immediate since `IsLocallyOrthogonal = IsRFP`.
Reverse: $E^2 = E$ implies $E^n = E$ for `n ≥ 1` by `IsIdempotentElem.pow_eq`,
so the connected correlator is independent of separation, giving CID.

**Scope restriction (arXiv:1606.00608, Theorem TheoremZCLPure):** the source
theorem is stated for canonical-form tensors and includes the BNT-level local
orthogonality equations for distinct components. This result proves the
single-block idempotence/CID equivalence under the convention above; it is not
the full BNT-level theorem. See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem zcl_iff_idempotent_transfer (A : MPSTensor d D) :
    IsZCL A ↔ IsRFP A := by
  constructor
  · exact fun ⟨hLO, _⟩ => hLO
  · intro hRFP
    refine ⟨hRFP, fun ρR _ _ X Y n m hn hm => ?_⟩
    have hIdem : IsIdempotentElem (transferMap A) := hRFP
    have hpow_n : (transferMap A) ^ n = transferMap A :=
      hIdem.pow_eq (by omega)
    have hpow_m : (transferMap A) ^ m = transferMap A :=
      hIdem.pow_eq (by omega)
    simp only [connectedCorrelator_def, twoPointExpectation_transfer,
      hpow_n, hpow_m]

end MPSTensor
