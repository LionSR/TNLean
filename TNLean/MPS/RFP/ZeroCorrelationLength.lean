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

Three conditions are introduced:

* `IsCID A` — correlations are independent of distance.
* `IsLocallyOrthogonal A` — the local single-block convention used here; it is
  transfer-map idempotence.
* `IsBNTLocallyOrthogonal blocks` — the source BNT-level mixed-sector
  equations.
* `IsBNTZCL A blocks` — the family `blocks` is a BNT for `A`, and `A`
  satisfies CID together with the BNT-level mixed-sector equations.
* `IsZCL A` — the conjunction of local orthogonality and CID.

The proved local result identifies this single-block convention with an
idempotent transfer map (`IsRFP`). The BNT-family predicate records the source
definition with an explicit BNT relation between `A` and `blocks`; the full
BNT-level ZCL theorem is still tracked in
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}
variable {g : ℕ} {dim : Fin g → ℕ}

/-- Correlations independent of distance (arXiv:1606.00608, Definition 3.3):
the connected two-point correlation function through the transfer map is
constant in the separation for all local observables.

For every positive definite right fixed point `ρR` of the transfer map, the
connected correlator `C(X,Y;n) = ⟨X₀Yₙ⟩ − ⟨X⟩⟨Y⟩` is the same for all
separations `n ≥ 1` and all observables `X`, `Y`. Requiring `ρR.PosDef`
(positive definite) ensures the condition is non-vacuous — CID is only
meaningful for genuine quantum states, not the zero matrix. -/
def IsCID (A : MPSTensor d D) : Prop :=
  ∀ (ρR : Matrix (Fin D) (Fin D) ℂ),
    ρR.PosDef → transferMap A ρR = ρR →
    ∀ (X Y : Matrix (Fin D) (Fin D) ℂ) (n m : ℕ),
      1 ≤ n → 1 ≤ m →
      connectedCorrelator A ρR X Y n = connectedCorrelator A ρR X Y m

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
`𝔼_{j,j'} = ∑ i, A_j^i ⊗ \overline{A_{j'}^i}` vanishes.

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

/-- BNT-level zero correlation length (arXiv:1606.00608, Definition 3.6):
`blocks` is a basis of normal tensors for `A`, the generated family has
correlations independent of distance, and its BNT components satisfy the
mixed-sector local-orthogonality equations. -/
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

/-- **CID implies RFP** (arXiv:1606.00608, Theorem 3.8 reverse direction):
for a tensor with a PosDef fixed point, correlations independent of distance
implies the transfer map is idempotent.

The proof uses trace nondegeneracy: IsCID forces `tr(Y · Eⁿ(X · ρR))` to be
constant in `n` for all `X`, `Y`, so `Eⁿ(X · ρR)` is constant. Since `ρR` is
PosDef (hence invertible), `X · ρR` ranges over all matrices, giving `E² = E`. -/
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
  apply (Matrix.trace_mul_right_eq_zero_iff (n := Fin D)
    (transferMap A (transferMap A (X * (u : Matrix (Fin D) (Fin D) ℂ))) -
      transferMap A (X * (u : Matrix (Fin D) (Fin D) ℂ)))).1
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
  exact sub_eq_zero.mpr heq

/-- Single-block ZCL is equivalent to transfer-map idempotence (i.e. `IsRFP`).

Forward: `IsZCL → IsRFP` is immediate since `IsLocallyOrthogonal = IsRFP`.
Reverse: `E² = E` implies `Eⁿ = E` for `n ≥ 1` by `IsIdempotentElem.pow_eq`,
so the connected correlator is independent of separation, giving CID.

**Scope restriction (arXiv:1606.00608, Theorem `TheoremZCLPure`):** the source
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
