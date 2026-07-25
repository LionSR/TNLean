/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.Core.Correlations
import TNLean.MPS.Core.Transfer
import TNLean.MPS.RFP.Defs
import TNLean.Spectral.MixedTransfer

/-!
# Zero correlation length (ZCL) for MPS tensors

This file defines single-block zero-correlation-length (ZCL) conditions for MPS
tensors, following arXiv:1606.00608 Section 3.2
(Cirac–Pérez-García–Schuch–Verstraete).

The following conditions are introduced:

* `IsPhysicalCID A` — the source condition for all disjoint physical regions.
* `IsPositiveGapPhysicalCID A` — physical block-observable correlations are
  independent of distance when both complementary gaps are positive.
* `IsCID A` — the stronger virtual-insertion CID condition used by the current
  converse theorem.
* `IsLocallyOrthogonal A` — the local single-block convention used here; it is
  transfer-map idempotence.
* `IsBNTLocallyOrthogonal blocks` — the source BNT-level mixed-sector
  equations.
* `IsPhysicalBNTZCL A blocks` — the source BNT zero-correlation-length
  condition.
* `IsBNTZCL A blocks` — the older virtual-insertion BNT surrogate.
* `IsPositiveGapBNTZCL A blocks` — the physical positive-gap BNT condition.
* `IsZCL A` — the conjunction of local orthogonality and CID.

The proved local result identifies this single-block convention with an
idempotent transfer map (`IsTransferIdempotent`). The source BNT predicate is now stated, but
its equivalence with transfer idempotence remains open and is tracked in
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}
variable {g : ℕ} {dim : Fin g → ℕ}

/-- The transfer insertion associated with an observable on a block of $L$
physical spins. If $\sigma,\tau:\operatorname{Fin}(L)\to\operatorname{Fin}(d)$
label basis words, then
`physicalObservableTransfer A L O X` equals
$\sum_{\sigma,\tau} O_{\tau,\sigma}\, A^{\sigma} X (A^{\tau})^{\dagger}$.

This is the inserted transfer map $\mathbb{E}_O$ in the two-observable formula
at arXiv:1606.00608, lines 490--496, written as a map on virtual matrices. -/
noncomputable def physicalObservableTransfer (A : MPSTensor d D) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ σ : Fin L → Fin d, ∑ τ : Fin L → Fin d,
    O τ σ • ((LinearMap.mulLeft ℂ (evalWord A (List.ofFn σ))).comp
      (LinearMap.mulRight ℂ (evalWord A (List.ofFn τ))ᴴ))

/-- The periodic-chain two-region expectation obtained by placing observables
$O_1$ and $O_2$ on physical blocks, with $n_1$ and $n_2$ unobserved sites in
the two complementary arcs. This is the trace formula at arXiv:1606.00608,
lines 490--496. -/
noncomputable def physicalTwoPointExpectation (A : MPSTensor d D)
    (L₁ L₂ : ℕ)
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ)
    (n₁ n₂ : ℕ) : ℂ :=
  LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
    (physicalObservableTransfer A L₂ O₂ ∘ₗ ((transferMap A) ^ n₂) ∘ₗ
      physicalObservableTransfer A L₁ O₁ ∘ₗ ((transferMap A) ^ n₁))

/-- Physical correlations independent of distance in the sense of
arXiv:1606.00608, Definition 3.3 (lines 437--445): for two observables on
disjoint contiguous regions, translating one region without crossing the
other does not change the expectation. In the periodic-chain formula at
lines 490--496, the two complementary gap lengths may therefore be
redistributed while their sum, and hence the chain length, remains fixed.

The physical block lengths are positive, as the source regions are nonempty.
The gap lengths are arbitrary natural numbers. In particular, a zero gap
represents adjacent regions, as permitted by the source definition. The
adjacent case obstructs the unrestricted forward implication from transfer
idempotence; see
`docs/paper-gaps/cpsv16_pure_zcl_adjacent_gap_cid_scope.tex`. -/
def IsPhysicalCID (A : MPSTensor d D) : Prop :=
  ∀ (L₁ L₂ : ℕ)
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ)
    (n₁ n₂ m₁ m₂ : ℕ),
    1 ≤ L₁ → 1 ≤ L₂ → n₁ + n₂ = m₁ + m₂ →
    physicalTwoPointExpectation A L₁ L₂ O₁ O₂ n₁ n₂ =
      physicalTwoPointExpectation A L₁ L₂ O₁ O₂ m₁ m₂

/-- Positive-gap physical correlations independent of distance, in the transfer
formula surrounding arXiv:1606.00608, Definition 3.3 (lines 437--445) and the
two-observable formula at lines 490--496: translating either physical block
observable through the unobserved part of a fixed periodic chain does not change their
two-region expectation.  Thus the two complementary gaps may change while
their sum, and hence the chain length, remains fixed.

The definition permits observables on blocks of arbitrary positive finite
lengths and does not replace physical observables by arbitrary virtual bond
matrices.

**Scope restriction (arXiv:1606.00608, Definition 3.3):** the source quantifies
over all disjoint regions, including adjacent regions.  Here both complementary
gaps are required to be positive. If a gap is zero, the transfer formula
contains $\mathbb{E}^0=1$, which does not follow from
$\mathbb{E}^2=\mathbb{E}$. See
`docs/paper-gaps/cpsv16_pure_zcl_adjacent_gap_cid_scope.tex`. -/
def IsPositiveGapPhysicalCID (A : MPSTensor d D) : Prop :=
  ∀ (L₁ L₂ : ℕ)
    (O₁ : Matrix (Fin L₁ → Fin d) (Fin L₁ → Fin d) ℂ)
    (O₂ : Matrix (Fin L₂ → Fin d) (Fin L₂ → Fin d) ℂ)
    (n₁ n₂ m₁ m₂ : ℕ),
    1 ≤ L₁ → 1 ≤ L₂ →
    1 ≤ n₁ → 1 ≤ n₂ → 1 ≤ m₁ → 1 ≤ m₂ → n₁ + n₂ = m₁ + m₂ →
    physicalTwoPointExpectation A L₁ L₂ O₁ O₂ n₁ n₂ =
      physicalTwoPointExpectation A L₁ L₂ O₁ O₂ m₁ m₂

/-- Physical CID implies its positive-gap restriction. This is the direct
restriction of arXiv:1606.00608, Definition 3.3 (lines 437--445), to positive
complementary gaps. -/
theorem isPositiveGapPhysicalCID_of_isPhysicalCID (A : MPSTensor d D)
    (hCID : IsPhysicalCID A) : IsPositiveGapPhysicalCID A := by
  intro L₁ L₂ O₁ O₂ n₁ n₂ m₁ m₂ hL₁ hL₂ _ _ _ _ hsum
  exact hCID L₁ L₂ O₁ O₂ n₁ n₂ m₁ m₂ hL₁ hL₂ hsum

/-- Virtual-insertion correlations independent of distance: the connected
two-point expression through the transfer map is constant in the separation
for all virtual bond matrices.

For every positive definite right fixed point `ρR` of the transfer map, the
connected correlator
$C(X,Y;n) = \langle X_0 Y_n \rangle - \langle X \rangle \langle Y \rangle$ is
the same for all separations $n \geq 1$ and all bond matrices `X`, `Y`.

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

This is the positive-gap part of the forward implication at
arXiv:1606.00608, lines 498--502. The relation
$\mathbb E_A^n=\mathbb E_A$ for $n\geq 1$ shows the reason directly:
substitution in the two-observable formula makes the expectation independent
of both positive gap sizes.

**Scope restriction:** adjacent regions are not covered because idempotence
does not identify $\mathbb{E}^0$ with $\mathbb{E}$.  This is recorded in
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem isPositiveGapPhysicalCID_of_isTransferIdempotent
    (A : MPSTensor d D) (hRFP : IsTransferIdempotent A) :
    IsPositiveGapPhysicalCID A := by
  intro L₁ L₂ O₁ O₂ n₁ n₂ m₁ m₂ _ _ hn₁ hn₂ hm₁ hm₂ _
  have hIdem : IsIdempotentElem (transferMap A) := hRFP
  have hpow_n₁ : (transferMap A) ^ n₁ = transferMap A :=
    hIdem.pow_eq (Nat.ne_of_gt hn₁)
  have hpow_n₂ : (transferMap A) ^ n₂ = transferMap A :=
    hIdem.pow_eq (Nat.ne_of_gt hn₂)
  have hpow_m₁ : (transferMap A) ^ m₁ = transferMap A :=
    hIdem.pow_eq (Nat.ne_of_gt hm₁)
  have hpow_m₂ : (transferMap A) ^ m₂ = transferMap A :=
    hIdem.pow_eq (Nat.ne_of_gt hm₂)
  simp only [physicalTwoPointExpectation, hpow_n₁, hpow_n₂, hpow_m₁, hpow_m₂]

/-- Local orthogonality in the single-block convention used by this file:
the self-transfer map is idempotent. Thus, for one tensor `A`, this is
definitionally equivalent to `IsTransferIdempotent A` (see
`isLocallyOrthogonal_iff_isTransferIdempotent`).

**Scope restriction (arXiv:1606.00608, Definition 3.5):** in the source, local
orthogonality is a BNT-level condition: for distinct BNT components `j ≠ k`, the
mixed transfer maps vanish. This one-tensor predicate has no mixed sectors and
does not formalize those equations. The missing BNT-level statement is recorded
in `docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
def IsLocallyOrthogonal (A : MPSTensor d D) : Prop :=
  IsTransferIdempotent A

/-- `IsLocallyOrthogonal` is definitionally equal to `IsTransferIdempotent` for a single
BNT block. -/
lemma isLocallyOrthogonal_iff_isTransferIdempotent (A : MPSTensor d D) :
    IsLocallyOrthogonal A ↔ IsTransferIdempotent A :=
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

/-- BNT zero correlation length in the source sense of arXiv:1606.00608,
Definition 3.6 (lines 476--478): `blocks` is a basis of normal tensors for
`A`, the physical correlations of `A` satisfy Definition 3.3 (lines 437--445),
and distinct BNT components satisfy the local-orthogonality equations of
Definition 3.5 (lines 467--474). -/
def IsPhysicalBNTZCL (A : MPSTensor d D)
    (blocks : (j : Fin g) → MPSTensor d (dim j)) : Prop :=
  IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, blocks j⟩) ∧
    IsPhysicalCID A ∧ IsBNTLocallyOrthogonal blocks

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

/-- Source BNT zero correlation length implies its positive-gap restriction.
The CID component is restricted from all disjoint regions in arXiv:1606.00608,
Definition 3.3 (lines 437--445), while the BNT and local-orthogonality
components of Definition 3.6 (lines 476--478) are unchanged. -/
theorem isPositiveGapBNTZCL_of_isPhysicalBNTZCL (A : MPSTensor d D)
    (blocks : (j : Fin g) → MPSTensor d (dim j))
    (hZCL : IsPhysicalBNTZCL A blocks) : IsPositiveGapBNTZCL A blocks :=
  ⟨hZCL.1, isPositiveGapPhysicalCID_of_isPhysicalCID A hZCL.2.1, hZCL.2.2⟩

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

/-- Correlator independence of distance forces the trace pairings of
$\mathbb{E}^2(X\rho_R)$ and $\mathbb{E}(X\rho_R)$ against every observable to
agree: this is the independence-of-separation step at gaps $2$ and $1$
(arXiv:1606.00608, Definition 3.3). -/
private lemma trace_mul_transferMap_sq_eq_of_isCID
    (A : MPSTensor d D) (ρR : Matrix (Fin D) (Fin D) ℂ)
    (hρ_pd : ρR.PosDef) (hρ_fix : transferMap A ρR = ρR) (hCID : IsCID A)
    (X N : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (N * transferMap A (transferMap A (X * ρR))) =
      Matrix.trace (N * transferMap A (X * ρR)) := by
  have h := hCID ρR hρ_pd hρ_fix X N 2 1 (by omega) (by omega)
  simp only [connectedCorrelator_def, twoPointExpectation_transfer] at h
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply] at h
  exact sub_left_injective h

/-- **Virtual-insertion distance independence implies RFP.**

For a tensor with a positive-definite fixed point, independence of the
virtual-insertion correlator implies that the transfer map is idempotent.

The proof uses trace nondegeneracy: IsCID forces
$\operatorname{tr}(Y\, E^n(X \rho_R))$ to be constant in $n$ for all $X,Y$,
so $E^n(X \rho_R)$ is constant. Since $\rho_R$ is positive definite and hence
invertible, $X \rho_R$ ranges over all matrices, giving $E^2 = E$.

**Scope restriction (virtual insertions):** `IsCID` quantifies over arbitrary
virtual bond matrices, rather than the physical block observables in
arXiv:1606.00608, Definition 3.3 and the theorem at lines 498--502. The missing
physical-realization step from lines 1250--1258 is recorded in
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem isCID_implies_isTransferIdempotent
    (A : MPSTensor d D)
    (ρR : Matrix (Fin D) (Fin D) ℂ)
    (hρ_pd : ρR.PosDef)
    (hρ_fix : transferMap A ρR = ρR)
    (hCID : IsCID A) : IsTransferIdempotent A := by
  change transferMap A ∘ₗ transferMap A = transferMap A
  obtain ⟨u, rfl⟩ := hρ_pd.isUnit
  apply LinearMap.ext; intro Z
  simp only [LinearMap.comp_apply]
  -- Write Z = X * ↑u using invertibility of ρR (PosDef ⟹ IsUnit)
  set X := Z * (↑u⁻¹ : Matrix (Fin D) (Fin D) ℂ) with hX
  have hZ : Z = X * (u : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hX, mul_assoc, Units.inv_mul, mul_one]
  rw [hZ]
  -- By trace nondegeneracy, suffices: tr(N · E(E(X·ρR))) = tr(N · E(X·ρR)) for all N
  refine eq_of_sub_eq_zero ((Matrix.ext_iff_trace_mul_right (B := 0)).2 fun N => ?_)
  rw [sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm _ N, Matrix.trace_mul_comm _ N,
    Matrix.zero_mul, Matrix.trace_zero]
  exact sub_eq_zero.mpr (trace_mul_transferMap_sq_eq_of_isCID A ↑u hρ_pd hρ_fix hCID X N)

/-- Single-block ZCL is equivalent to transfer-map idempotence (i.e. `IsTransferIdempotent`).

Forward: `IsZCL → IsTransferIdempotent` is immediate since
`IsLocallyOrthogonal = IsTransferIdempotent`.
Reverse: $E^2 = E$ implies $E^n = E$ for $n \geq 1$ by
`IsIdempotentElem.pow_eq`,
so the connected correlator is independent of separation, giving CID.

**Scope restriction (arXiv:1606.00608, lines 498--502):** the source theorem is
stated for canonical-form tensors and includes the BNT-level local
orthogonality equations for distinct components. This result proves the
single-block idempotence/CID equivalence under the convention above; it is not
the full BNT-level theorem. See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`. -/
theorem zcl_iff_idempotent_transfer (A : MPSTensor d D) :
    IsZCL A ↔ IsTransferIdempotent A := by
  constructor
  · exact fun ⟨hLO, _⟩ => hLO
  · intro hRFP
    refine ⟨hRFP, fun ρR _ _ X Y n m hn hm => ?_⟩
    have hIdem : IsIdempotentElem (transferMap A) := hRFP
    have hpow_n : (transferMap A) ^ n = transferMap A :=
      hIdem.pow_eq (Nat.ne_of_gt hn)
    have hpow_m : (transferMap A) ^ m = transferMap A :=
      hIdem.pow_eq (Nat.ne_of_gt hm)
    simp only [connectedCorrelator_def, twoPointExpectation_transfer,
      hpow_n, hpow_m]

end MPSTensor
