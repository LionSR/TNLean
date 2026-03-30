/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Core.CPPrimitive
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Irreducible.Adjoint
import TNLean.Channel.FixedPoint.CanonicalGauge
import TNLean.Channel.Irreducible.Ergodicity
import TNLean.Channel.KrausFreedom
import TNLean.Channel.KrausRepresentation
import TNLean.Spectral.SpectralGap
import Mathlib.Analysis.Matrix.Order

/-!
# String order parameters and local symmetry equivalence

This file formalizes the main results of Pérez-García, Wolf, Sanz, Verstraete,
Cirac, *String order and symmetries in quantum spin lattices* (PRL 2008,
arXiv:0802.0447):

* The **twisted transfer map** `ℰ_u` associated to a unitary `u` on the
  physical index.
* The **string order parameter** `R_L(u) = ⟨ψ_L | u^{⊗L} | ψ_L⟩`,
  expressed via the transfer-matrix formalism as `tr(Λ · ℰ_u^L(𝟙))`.
* **Conditions C1/C2/C3**: three equivalent formulations of the
  intertwining relation between the on-site unitary `u` and a virtual
  unitary `V`.
* The **main equivalence**: for an injective (pure) FCS, string order
  for `u` exists iff `u` is a local symmetry iff `ρ(ℰ_u) = 1`.

## Main definitions

* `MPSTensor.twistedTransferMap` — the u-twisted transfer map `ℰ_u`
* `MPSTensor.stringOrderParam` — the string order parameter `R_L(u)`
* `MPSTensor.IsLocalSymmetry` — predicate: `u^{⊗L}` leaves the FCS
  invariant
* `MPSTensor.CondC1` — intertwining: `∑_j U_{ij} A^j = V A^i V†`
* `MPSTensor.CondC2` — covariance: `ℰ(V X V†) = V ℰ(X) V†`
* `MPSTensor.CondC3` — doubled commutation: `[E, V ⊗ V̄] = 0`
* `MPSTensor.HasStringOrder` — nonvanishing of the string order

## Main results

* `MPSTensor.condC2_iff_condC3` — C2 ↔ C3
* `MPSTensor.condC1_imp_condC2` — C1 → C2
* `MPSTensor.stringOrder_iff_localSymmetry` — string order ↔ local
  symmetry (for injective MPS)

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447
  (PRL 2008)
* Wolf, *Quantum Channels & Operations*, Chapter 2

## Status

The condition equivalences and the basic spectral-radius bound are now proved.
The following downstream theorems still require additional Perron-Frobenius
input for completely positive maps and are marked `sorry`:

* `localSymmetry_iff_spectralRadius_one` — needs the modulus-one case of the
  peripheral spectral theory
* `stringOrder_iff_localSymmetry` — depends on the local-symmetry/spectral-radius
  equivalence
* `virtualUnitary_of_stringOrder` — depends on the same peripheral-eigenvalue
  analysis
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-! ### Twisted transfer map -/

/-- The twisted transfer map `ℰ_u` associated to a unitary `u` on
the physical index. For MPS tensor `A` and physical-index unitary
`u`:

$$\mathcal{E}_u(X) = \sum_{n,n'} \langle n'|u|n\rangle
  \, A_n \, X \, A_{n'}^\dagger$$

This is the key map whose spectral properties determine string
order. -/
noncomputable def twistedTransferMap (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ :=
  ∑ n : Fin d, ∑ n' : Fin d,
    (u n' n) •
      ((LinearMap.mulLeft ℂ (A n)).comp
        (LinearMap.mulRight ℂ (A n')ᴴ))

@[simp]
lemma twistedTransferMap_apply (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    twistedTransferMap A u X =
      ∑ n : Fin d, ∑ n' : Fin d,
        u n' n • (A n * X * (A n')ᴴ) := by
  simp [twistedTransferMap, Matrix.mul_assoc]

/-- The standard (untwisted) transfer map is the twisted transfer
map with `u = 1`. -/
lemma twistedTransferMap_one (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    twistedTransferMap A 1 X = transferMap A X := by
  simp only [twistedTransferMap_apply, transferMap_apply,
    Matrix.one_apply]
  congr 1; ext n
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- The unitary-twisted transfer map can be rewritten as a mixed transfer map
with a unitary-mixed companion Kraus family. -/
noncomputable def twistedMixedCompanion (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) : MPSTensor d D :=
  fun n => ∑ n' : Fin d, (starRingEnd ℂ) (u n' n) • A n'

/-- The twisted transfer map is the mixed transfer map for `A` and its
unitary-mixed companion family. In symbols, `ℰ_u = F_{A,B}` with
`B := twistedMixedCompanion A u`. -/
lemma twistedTransferMap_eq_mixedTransfer (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    twistedTransferMap A u = mixedTransferMap A (twistedMixedCompanion A u) := by
  ext X i j
  simp only [twistedTransferMap_apply, mixedTransferMap_apply, twistedMixedCompanion,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.mul_smul,
    starRingEnd_apply, star_star, Matrix.mul_assoc]

/-! ### Iterated twisted transfer map -/

/-- The `N`-fold iterate of the twisted transfer map, defined via
the `Monoid` instance on `Module.End` so that `pow_zero`,
`pow_succ`, and `pow_add` are available for free. -/
noncomputable def twistedTransferIter (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ :=
  (twistedTransferMap A u) ^ N

@[simp]
lemma twistedTransferIter_zero (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    twistedTransferIter A u 0 = LinearMap.id :=
  pow_zero _

lemma twistedTransferIter_succ (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    twistedTransferIter A u (N + 1) =
      (twistedTransferMap A u).comp
        (twistedTransferIter A u N) :=
  pow_succ' _ _

/-! ### String order parameter -/

/-- The string order parameter `R_L(u)` for an MPS with stationary
state `Λ`:

$$R_L(u) = \mathrm{tr}(\Lambda \cdot \mathcal{E}_u^L(\mathbf{1}))$$

This measures the overlap `⟨ψ_L | u^{⊗L} | ψ_L⟩` in the
transfer-matrix formalism (Eq. (5) of arXiv:0802.0447). -/
noncomputable def stringOrderParam (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (L : ℕ) : ℂ :=
  Matrix.trace (Λ * twistedTransferIter A u L 1)

/-! ### Local symmetry -/

/-- A state generated by `A` has **local symmetry** under a unitary
`u` if for every system size `L`, the application of `u^{⊗L}`
leaves all reduced density matrices invariant. In the MPS/FCS
language this is expressed as:

$$\forall L,\; \|R_L(u)\| = \|R_L(\mathbf{1})\|$$

i.e. the norm of the string order parameter for `u` equals that
for the identity.

**Convention**: This definition uses *norm* equality of the string
order parameters rather than exact complex equality, matching the
paper's density-matrix formulation (arXiv:0802.0447, Definition 3).
Reduced density matrix invariance allows a global phase factor
`e^{iφL}` in the state vector, so only `|R_L(u)| = |R_L(1)|` is
required. For injective MPS the stationary state `Λ > 0` makes
`R_L(1)` real and positive, and the spectral gap ensures the
sequence converges, so this norm-based definition captures the
correct physical notion. -/
def IsLocalSymmetry (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ L : ℕ,
    ‖stringOrderParam A u Λ L‖ = ‖stringOrderParam A 1 Λ L‖

/-- String order exists for `u` if the string order parameter is
uniformly bounded below by a positive constant for all `L`.

This is a stronger condition than mere non-vanishing of the limit
`lim_{L→∞} R_L(u)`. The uniform bound is chosen because for
injective MPS the string order parameter converges exponentially
(due to the spectral gap of the transfer map), so both
formulations are equivalent in the injective setting. The uniform
version is more convenient for formal proofs as it avoids
filter/limit machinery.

**Edge case**: For a trivial-phase twist `u = ζ · 1` with
`|ζ| = 1`, `ζ ≠ 1`, the norm `‖R_L(u)‖ = 1` for all `L` so
`HasStringOrder` holds, but the complex sequence `R_L(u) = ζ^L`
need not converge (e.g. for irrational `arg ζ`). For injective
MPS the spectral gap ensures exponential convergence of the
dominant term, making the uniform bound and limit-based
definitions agree for the cases of physical interest. -/
def HasStringOrder (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ L : ℕ,
      c ≤ ‖stringOrderParam A u Λ L‖

/-! ### Conditions C1, C2, C3 -/

section Conditions

variable (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ)

/-- **Condition C1** (intertwining relation):
For each physical index `i`,
$$\sum_j u_{ij} A^j = V A^i V^\dagger$$

This states that the on-site unitary `u` is intertwined by the
virtual unitary `V` at the level of individual MPS matrices.
(Eq. from Lemma 1 of arXiv:0802.0447, reformulated.) -/
def CondC1 : Prop :=
  ∀ i : Fin d,
    ∑ j : Fin d, u i j • A j = V * A i * Vᴴ

/-- **Condition C2** (covariance of transfer map):
$$\mathcal{E}(V X V^\dagger) = V \, \mathcal{E}(X) \, V^\dagger$$

The transfer map commutes with virtual conjugation by `V`. -/
def CondC2 : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ,
    transferMap A (V * X * Vᴴ) =
      V * transferMap A X * Vᴴ

/-- **Condition C3** (doubled transfer matrix commutation):
The doubled transfer matrix `E = ∑_j A_j ⊗ Ā_j` commutes with
`V ⊗ V̄`.

We express this via the transfer-map channel written in the
`twistedTransferMap` formalism (with twist `u = 1`):
`ℰ = ℰ_1`. In channel form this is
`V ℰ(X) V† = ℰ(V X V†)`, i.e. `[E, V ⊗ V̄] = 0`. -/
def CondC3 : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ,
    V * twistedTransferMap A 1 X * Vᴴ =
      twistedTransferMap A 1 (V * X * Vᴴ)

end Conditions

/-! ### Equivalence of conditions C1, C2, C3 -/

section ConditionEquivalences

variable {A : MPSTensor d D}
    {u : Matrix (Fin d) (Fin d) ℂ}
    {V : Matrix (Fin D) (Fin D) ℂ}

/-- C2 ↔ C3: Transfer-map covariance is equivalent to doubled
commutation.

Both sides express the same identity
`∑_i A_i (V X V†) A_i† = V (∑_i A_i X A_i†) V†`. C2 reads
right-to-left and C3 rearranges the left side using conjugated
Kraus operators `V A_i V†`.

Note: This equivalence holds for any `V`, not just unitaries,
since `CondC2` and `CondC3` are literally `∀ X, P = Q` vs
`∀ X, Q = P`. -/
theorem condC2_iff_condC3 :
    CondC2 A V ↔ CondC3 A V := by
  simp only [CondC2, CondC3, twistedTransferMap_one]
  exact forall_congr' fun _ => eq_comm

/-- Unitary mixing of Kraus operators preserves the channel:
if `u` is unitary then `∑_i (∑_j u_{ij} A_j) X (∑_j u_{ij} A_j)† = ∑_i A_i X A_i†`.

This is a thin adapter over `kraus_same_map_of_unitary_combination` from
`TNLean.Channel.KrausRepresentation` (Theorem 2.18 in Wolf's "Quantum
Channels & Operations"). -/
lemma unitary_kraus_mixing
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    ∑ i : Fin d,
      (∑ j : Fin d, u i j • A j) * Y *
        (∑ j : Fin d, u i j • A j)ᴴ =
    ∑ i : Fin d, A i * Y * (A i)ᴴ :=
  kraus_same_map_of_unitary_combination _ A u (mul_eq_one_comm.mp hu) (fun _ => rfl) Y

/-- C1 → C2: The intertwining condition implies transfer-map
covariance.

If `∑_j u_{ij} A_j = V A_i V†` for all `i`, then `V` commutes
with the action of the transfer map. -/
theorem condC1_imp_condC2
    (hV : V * Vᴴ = 1)
    (hu : u * uᴴ = 1)
    (hC1 : CondC1 A u V) :
    CondC2 A V := by
  have hVc : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  -- Helper: Vᴴ * (V * Z) = Z (cancel VᴴV in right-associated form)
  have hc : ∀ Z : Matrix (Fin D) (Fin D) ℂ, Vᴴ * (V * Z) = Z :=
    fun Z => by rw [← Matrix.mul_assoc, hVc, Matrix.one_mul]
  intro X
  simp only [transferMap_apply]
  -- Show LHS = RHS via: RHS → conjugated Kraus → C1 → unitary mixing → LHS
  symm
  rw [Finset.mul_sum, Finset.sum_mul]
  -- Step 1: Insert VᴴV = 1 to get conjugated Kraus operators
  have step1 : ∀ i : Fin d, V * (A i * X * (A i)ᴴ) * Vᴴ =
      (V * A i * Vᴴ) * (V * X * Vᴴ) * (V * A i * Vᴴ)ᴴ := by
    intro i
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    simp_rw [hc]
  simp_rw [step1]
  -- Step 2: Use C1: V * A_i * V† = ∑_j u_{ij} • A_j
  simp_rw [show ∀ i, V * A i * Vᴴ = ∑ j : Fin d, u i j • A j
    from fun i => (hC1 i).symm]
  -- Step 3: Apply unitary Kraus mixing
  exact unitary_kraus_mixing A u hu (V * X * Vᴴ)

/-- C2 → C1 (under injectivity): If `V` is unitary and C2 holds,
then there exists a unitary `u` satisfying C1.

This is the reverse direction of `condC1_imp_condC2`, completing
the equivalence C1 ↔ C2 for injective MPS (Lemma 1 of
arXiv:0802.0447). The present formal proof is slightly stronger
than the paper-facing statement: it derives C1 from C2 by
identifying `V A_i V†` as an alternative Kraus family for the same
channel and applying rectangular Kraus freedom, so the explicit
injectivity hypothesis is retained only to match the paper's API. -/
theorem condC2_imp_condC1_of_injective
    (hA : IsInjective A)
    (hV : V * Vᴴ = 1)
    (hC2 : CondC2 A V) :
    ∃ u : Matrix (Fin d) (Fin d) ℂ, u * uᴴ = 1 ∧ CondC1 A u V := by
  let _ := hA
  let B : MPSTensor d D := fun i => V * A i * Vᴴ
  have hB_eq : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      transferMap B X = transferMap A X := by
    intro X
    calc
      transferMap B X
          = V * transferMap A (Vᴴ * X * V) * Vᴴ := by
              simp [B, transferMap_apply, Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul]
      _ = transferMap A X := by
            have hVV : V * (Vᴴ * X * V) * Vᴴ = X := by
              calc
                V * (Vᴴ * X * V) * Vᴴ = (V * Vᴴ) * X * (V * Vᴴ) := by
                  simp [Matrix.mul_assoc]
                _ = X := by simp [hV]
            have hC2' : transferMap A X =
                V * transferMap A (Vᴴ * X * V) * Vᴴ := by
              simpa [hVV] using hC2 (Vᴴ * X * V)
            exact hC2'.symm
  rcases kraus_rectangular_freedom B A
      (fun X => by simpa [transferMap_apply] using hB_eq X)
      (Nat.le_refl d) with ⟨u, hu, huK⟩
  refine ⟨u, mul_eq_one_comm.mp hu, ?_⟩
  intro i
  simpa [B] using (huK i).symm

end ConditionEquivalences

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
  let B : MPSTensor d D := twistedMixedCompanion A u
  have hEigMixed : mixedTransferMap A B V = ev • V := by
    simpa [B, twistedTransferMap_eq_mixedTransfer] using hEig
  have hB_eq : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      transferMap B X = transferMap A X := by
    intro X
    simpa [B, transferMap_apply] using
      kraus_same_map_of_unitary_combination B A uᴴ
        (by simpa using hu)
        (fun j => by
          simp [B, twistedMixedCompanion, Matrix.conjTranspose_apply])
        X
  have hDpos : 0 < D := by
    by_contra hD
    have hD0 : D = 0 := Nat.eq_zero_of_not_pos hD
    subst hD0
    apply hV
    ext i j
    exact Fin.elim0 i
  haveI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    injective_implies_irreducibleCP A hA
  have hIrrTensor : IsIrreducibleTensor (d := d) (D := D) A :=
    isIrreducibleTensor_of_isIrreducibleMap A hIrrA
  have hIrrAdj : IsIrreducibleMap (transferMap (d := d) (D := D) fun i => (A i)ᴴ) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor A hIrrTensor
  have hAadjNorm : ∑ i : Fin d, (((fun i => (A i)ᴴ) i)ᴴ) * ((fun i => (A i)ᴴ) i) = 1 := by
    simpa using
      kraus_sum_mul_conjTranspose_of_unital A (transferMap A)
        (fun X => by simp [transferMap_apply]) hNorm
  have hChAdj : IsChannel (transferMap (d := d) (D := D) fun i => (A i)ᴴ) :=
    transferMap_isChannel (A := fun i => (A i)ᴴ) hAadjNorm
  obtain ⟨σ, hσ_mem, hσ_pd, hσ_fixA, _⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible
      (E := transferMap (d := d) (D := D) fun i => (A i)ᴴ) hChAdj hIrrAdj hDpos
  have hσ_fixB : transferMap (d := d) (D := D) (fun i => (B i)ᴴ) σ = σ := by
    calc
      transferMap (d := d) (D := D) (fun i => (B i)ᴴ) σ
          = transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ := by
              simpa [B, transferMap_apply, Matrix.mul_assoc] using
                kraus_dual_eq_of_map_eq B A
                  (fun X => by simpa [transferMap_apply] using hB_eq X) σ
      _ = σ := hσ_fixA
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ with hS_def
  have hS_herm : Sᴴ = S := by
    simpa [hS_def] using conjTranspose_cfc_sqrt (D := D) σ
  have hS_det : IsUnit (Matrix.det S) := by
    simpa [hS_def] using isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ_pd
  have hS_mul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det
  have hS_inv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS_det
  have hS_detT : IsUnit (Matrix.det Sᴴ) := by
    simpa [Matrix.det_conjTranspose] using IsUnit.star hS_det
  have hS_hMul_inv : Sᴴ * (Sᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv Sᴴ hS_detT
  have hS_hInv_mul : (Sᴴ)⁻¹ * Sᴴ = 1 := Matrix.nonsing_inv_mul Sᴴ hS_detT
  have hS_inv_herm : (S⁻¹)ᴴ = S⁻¹ := by
    simpa [hS_herm] using Matrix.conjTranspose_nonsing_inv S
  have hA'TP :
      ∑ i : Fin d,
        (tpGauge (d := d) (D := D) A σ i)ᴴ * tpGauge (d := d) (D := D) A σ i = 1 :=
    tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint (A := A) (ρ := σ) hσ_pd hσ_fixA
  have hB'TP :
      ∑ i : Fin d,
        (tpGauge (d := d) (D := D) B σ i)ᴴ * tpGauge (d := d) (D := D) B σ i = 1 :=
    tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint (A := B) (ρ := σ) hσ_pd hσ_fixB
  have hEigGauge :
      mixedTransferMap (tpGauge (d := d) (D := D) A σ)
        (tpGauge (d := d) (D := D) B σ) (S * V * Sᴴ) =
        ev • (S * V * Sᴴ) := by
    have hTerm :
        ∀ i : Fin d,
          tpGauge (d := d) (D := D) A σ i * (S * V * Sᴴ) *
            (tpGauge (d := d) (D := D) B σ i)ᴴ =
          S * (A i * V * (B i)ᴴ) * Sᴴ := by
      intro i
      have hAeq : tpGauge (d := d) (D := D) A σ i = S * A i * S⁻¹ := by
        simp [tpGauge, hS_def]
      have hSsqrt_herm : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := by
        simpa [hS_def] using hS_herm
      have hBstar :
          (tpGauge (d := d) (D := D) B σ i)ᴴ = S⁻¹ * (B i)ᴴ * S := by
        rw [tpGauge, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_nonsing_inv]
        simp [hS_def, hSsqrt_herm, Matrix.mul_assoc]
      calc
        tpGauge (d := d) (D := D) A σ i * (S * V * Sᴴ) *
            (tpGauge (d := d) (D := D) B σ i)ᴴ
            = (S * A i * S⁻¹) * (S * V * S) * (S⁻¹ * (B i)ᴴ * S) := by
                rw [hAeq, hBstar, hS_herm]
        _ = S * (A i * V * (B i)ᴴ) * S := by
              calc
                (S * A i * S⁻¹) * (S * V * S) * (S⁻¹ * (B i)ᴴ * S)
                    = S * A i * (S⁻¹ * (S * V * S)) * (S⁻¹ * (B i)ᴴ * S) := by
                        simp [Matrix.mul_assoc]
                _ = S * A i * (V * S) * (S⁻¹ * (B i)ᴴ * S) := by
                      rw [show S⁻¹ * (S * V * S) = V * S by
                        calc
                          S⁻¹ * (S * V * S) = (S⁻¹ * S) * V * S := by
                            simp [Matrix.mul_assoc]
                          _ = V * S := by simp [hS_inv_mul]]
                _ = S * A i * (V * (B i)ᴴ * S) := by
                      calc
                        S * A i * (V * S) * (S⁻¹ * (B i)ᴴ * S)
                            = S * A i * ((V * S) * (S⁻¹ * (B i)ᴴ * S)) := by
                                simp [Matrix.mul_assoc]
                        _ = S * A i * (V * (B i)ᴴ * S) := by
                              congr 1
                              calc
                                (V * S) * (S⁻¹ * (B i)ᴴ * S)
                                    = V * (S * S⁻¹) * (B i)ᴴ * S := by
                                        simp [Matrix.mul_assoc]
                                _ = V * (B i)ᴴ * S := by
                                      simp [hS_mul_inv, Matrix.mul_assoc]
                _ = S * (A i * V * (B i)ᴴ) * S := by
                      simp [Matrix.mul_assoc]
        _ = S * (A i * V * (B i)ᴴ) * Sᴴ := by simp [hS_herm]
    calc
      mixedTransferMap (tpGauge (d := d) (D := D) A σ)
          (tpGauge (d := d) (D := D) B σ) (S * V * Sᴴ)
          = ∑ i : Fin d,
              tpGauge (d := d) (D := D) A σ i * (S * V * Sᴴ) *
                (tpGauge (d := d) (D := D) B σ i)ᴴ := by
                  simp [mixedTransferMap_apply]
      _ = ∑ i : Fin d, S * (A i * V * (B i)ᴴ) * Sᴴ := by
            simp [hTerm]
      _ = S * (∑ i : Fin d, A i * V * (B i)ᴴ) * Sᴴ := by
            simpa using
              (Matrix.sum_mul_mul
                (L := S) (M := fun i : Fin d => A i * V * (B i)ᴴ) (R := Sᴴ))
      _ = ev • (S * V * Sᴴ) := by
            simpa [mixedTransferMap_apply, Matrix.mul_assoc] using
              congrArg (fun M => S * M * Sᴴ) hEigMixed
  have hGauge_ne : S * V * Sᴴ ≠ 0 := by
    intro hZero
    apply hV
    have h' : S⁻¹ * (S * V * Sᴴ) * (Sᴴ)⁻¹ = 0 := by
      simp [hZero]
    have h'' : S⁻¹ * (S * V) = 0 := by
      simpa [Matrix.mul_assoc, hS_hMul_inv] using h'
    have h''' : (S⁻¹ * S) * V = 0 := by
      simpa [Matrix.mul_assoc] using h''
    simpa [hS_inv_mul] using h'''
  have hHas : Module.End.HasEigenvalue
      (mixedTransferMap (tpGauge (d := d) (D := D) A σ)
        (tpGauge (d := d) (D := D) B σ)) ev := by
    rw [Module.End.hasEigenvalue_iff]
    intro hBot
    have hMem :
        S * V * Sᴴ ∈ Module.End.eigenspace
          (mixedTransferMap (tpGauge (d := d) (D := D) A σ)
            (tpGauge (d := d) (D := D) B σ)) ev :=
      Module.End.mem_eigenspace_iff.mpr hEigGauge
    have : S * V * Sᴴ ∈ (⊥ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
      simpa [hBot] using hMem
    exact hGauge_ne (Submodule.mem_bot ℂ |>.mp this)
  exact eigenvalue_norm_le_one
    (A := tpGauge (d := d) (D := D) A σ)
    (B := tpGauge (d := d) (D := D) B σ)
    hA'TP hB'TP ev hHas

/-- **Theorem 2** (arXiv:0802.0447): For a pure finitely correlated
state, `u` is a local symmetry if and only if the twisted transfer
map `ℰ_u` has a unitary eigenvector with unit-modulus eigenvalue.

The right-hand side is the witness form of `ρ(ℰ_u) = 1`:
combined with `twistedTransfer_spectralRadius_le_one` (all
eigenvalues satisfy `|λ| ≤ 1`), existence of an eigenvalue with
`|μ| = 1` is equivalent to `spectralRadius(ℰ_u) = 1`.

The forward direction uses the fact that local symmetry implies
`tr(ρ²) = tr[ρ u^{⊗N} ρ u^{†⊗N}]` is bounded below.
The reverse direction follows from Lemma 1: the eigenvalue-1
eigenvector of `ℰ_u` gives the virtual unitary `V`, and
`V†V = 𝟙` from the unique fixed point property. -/
theorem localSymmetry_iff_spectralRadius_one
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : transferMap A 1 = 1) :
    IsLocalSymmetry A u Λ ↔
      ∃ V : Matrix (Fin D) (Fin D) ℂ,
        V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
        ∃ μ : ℂ, ‖μ‖ = 1 ∧
          twistedTransferMap A u V = μ • V := by
  -- TODO(sorry): requires CP map spectral theory; see Status section.
  -- Dependency: needs unique fixed point of transfer map (from `IsInjective`)
  -- and Perron-Frobenius for CP maps; see `twistedTransfer_spectralRadius_le_one`.
  sorry

/-- **Theorem 1** (arXiv:0802.0447, simplified): String order
exists for a pure FCS if and only if there exists a non-trivial
virtual symmetry `V ≠ 𝟙`.

More precisely, `HasStringOrder A u Λ` iff `ρ(ℰ_u) = 1`, iff
there exists a unitary `V` satisfying the intertwining condition
C1, and there exist operators `x, y` such that the boundary terms
are nonzero.

For injective MPS, the spanning property of `{A_i}` ensures the
boundary terms can always be made nonzero (possibly after
blocking). -/
theorem stringOrder_iff_localSymmetry
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : transferMap A 1 = 1) :
    HasStringOrder A u Λ ↔ IsLocalSymmetry A u Λ := by
  -- TODO(sorry): requires CP map spectral theory; see Status section.
  -- Dependency: needs unique fixed point of transfer map (from `IsInjective`)
  -- and Perron-Frobenius for CP maps; see `twistedTransfer_spectralRadius_le_one`.
  sorry

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
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : transferMap A 1 = 1)
    (hSO : HasStringOrder A u Λ) :
    ∃ V : Matrix (Fin D) (Fin D) ℂ, ∃ μ : ℂ,
      V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ ‖μ‖ = 1 ∧
      ∀ i : Fin d,
        ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ) := by
  -- TODO(sorry): requires CP map spectral theory; see Status section.
  -- Dependency: needs unique fixed point of transfer map (from `IsInjective`)
  -- and Perron-Frobenius for CP maps; see `twistedTransfer_spectralRadius_le_one`.
  sorry

end MainTheorems

/-! ### SPT detection

TODO(`stringOrder_invariant_of_samePhase`):

Once a precise notion of "same SPT phase" (e.g. via cohomologous
projective cocycles for the virtual representation, see issue #159)
is available, this file should state and prove:

  theorem stringOrder_invariant_of_samePhase
      {G : Type*} [Group G]
      (A B : MPSTensor d D)
      (hA : IsInjective A) (hB : IsInjective B)
      (U : G →* Matrix (Fin d) (Fin d) ℂ)
      (hSymmA : IsOnSiteSymmetric A U)
      (hSymmB : IsOnSiteSymmetric B U)
      (Λ_A Λ_B : Matrix (Fin D) (Fin D) ℂ)
      (hΛA : Λ_A.PosDef) (hΛB : Λ_B.PosDef)
      (hNormA : transferMap A 1 = 1)
      (hNormB : transferMap B 1 = 1)
      (hSamePhase : IsCohomologous ...) :
      ∀ g : G, HasStringOrder A (U g) Λ_A ↔
        HasStringOrder B (U g) Λ_B

The key argument: string order detects whether the projective
cocycle is trivial for a given group element, and cocycles in the
same cohomology class agree on this property.
-/

end MPSTensor
