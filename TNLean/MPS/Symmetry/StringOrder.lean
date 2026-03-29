/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Core.Transfer

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

The condition equivalences (`condC2_iff_condC3`, `condC1_imp_condC2`) are fully
proved. The following theorems require spectral theory of completely positive
maps beyond what is currently available in Mathlib and are marked `sorry`:

* `twistedTransfer_spectralRadius_le_one` — needs CP map spectral theory
* `localSymmetry_iff_spectralRadius_one` — needs CP map spectral theory
* `stringOrder_iff_localSymmetry` — needs CP map spectral theory
* `virtualUnitary_of_stringOrder` — needs CP map spectral theory
-/

open scoped Matrix BigOperators ComplexOrder

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

/-! ### Iterated twisted transfer map -/

/-- The `N`-fold iterate of the twisted transfer map. -/
noncomputable def twistedTransferIter (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    ℕ → (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ)
  | 0 => LinearMap.id
  | n + 1 => (twistedTransferMap A u).comp
      (twistedTransferIter A u n)

@[simp]
lemma twistedTransferIter_zero (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    twistedTransferIter A u 0 = LinearMap.id := rfl

lemma twistedTransferIter_succ (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    twistedTransferIter A u (N + 1) =
      (twistedTransferMap A u).comp
        (twistedTransferIter A u N) := rfl

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

$$\forall L,\; R_L(u) = R_L(\mathbf{1})$$

i.e. the string order parameter for `u` equals that for the
identity. -/
def IsLocalSymmetry (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ L : ℕ,
    stringOrderParam A u Λ L = stringOrderParam A 1 Λ L

/-- String order exists for `u` if the string order parameter does
not vanish in the limit, i.e. there exists a positive lower bound
for all `L`. -/
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

In the channel picture, `(V ⊗ V̄) E` acts as `X ↦ V ℰ(X) V†`
while `E (V ⊗ V̄)` acts as `X ↦ ℰ(V X V†)`. Their equality is
the operator-level statement of `[E, V ⊗ V̄] = 0`. -/
def CondC3 : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ,
    V * transferMap A X * Vᴴ =
      transferMap A (V * X * Vᴴ)

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
Kraus operators `V A_i V†`. -/
theorem condC2_iff_condC3
    (_hV : V * Vᴴ = 1) (_hVc : Vᴴ * V = 1) :
    CondC2 A V ↔ CondC3 A V :=
  forall_congr' fun _ => eq_comm

/-- Unitary mixing of Kraus operators preserves the channel:
if `u` is unitary then `∑_i (∑_j u_{ij} A_j) X (∑_j u_{ij} A_j)† = ∑_i A_i X A_i†`. -/
private lemma unitary_kraus_mixing
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    ∑ i : Fin d,
      (∑ j : Fin d, u i j • A j) * Y *
        (∑ j : Fin d, u i j • A j)ᴴ =
    ∑ i : Fin d, A i * Y * (A i)ᴴ := by
  have huc : uᴴ * u = 1 := mul_eq_one_comm.mp hu
  -- Column orthogonality: ∑_i u_{ij} * star(u_{ik}) = δ_{jk}
  have hcol : ∀ j k : Fin d,
      ∑ i : Fin d, u i j * star (u i k) =
        if j = k then 1 else 0 := by
    intro j k
    have h := congr_fun (congr_fun huc k) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    -- h : ∑ i, star (u i k) * u i j = if k = j then 1 else 0
    rw [show (if k = j then (1 : ℂ) else 0) = if j = k then 1 else 0 from
      if_congr eq_comm rfl rfl] at h
    convert h using 1
    apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _
  -- Expand conjugate transpose of sum and smul
  simp_rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  -- Distribute sums over multiplication
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Pull scalars through multiplication
  simp_rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Rearrange triple sum: ∑ i ∑ j ∑ k → ∑ j ∑ k ∑ i
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  -- Factor out the matrix part and apply orthogonality
  conv_lhs => arg 2; ext k; rw [← Finset.sum_smul, hcol j k]
  -- Collapse: ∑ k, (if j = k then 1 else 0) • (A j * Y * (A k)ᴴ) = A j * Y * (A j)ᴴ
  simp only [ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

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

end ConditionEquivalences

/-! ### Main equivalence theorems -/

section MainTheorems

/-- **Spectral radius bound** (Lemma 1 of arXiv:0802.0447):
For a pure FCS (with `Λ > 0` and `ℰ` having unique fixed point
`𝟙`), the spectral radius of the twisted transfer map satisfies
`ρ(ℰ_u) ≤ 1`.

The proof uses Cauchy-Schwarz and the unitality (Heisenberg-picture
normalization) `ℰ(𝟙) = 𝟙`. This requires spectral theory for
completely positive maps beyond what is currently available in
Mathlib. -/
theorem twistedTransfer_spectralRadius_le_one
    (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hNorm : transferMap A 1 = 1)
    (hΛ : ∃ Λ : Matrix (Fin D) (Fin D) ℂ,
      Λ.PosSemidef ∧ Matrix.trace Λ = 1)
    (ev : ℂ) (V : Matrix (Fin D) (Fin D) ℂ)
    (hV : V ≠ 0)
    (hEig : twistedTransferMap A u V = ev • V) :
    ‖ev‖ ≤ 1 := by
  sorry

/-- **Theorem 2** (arXiv:0802.0447): For a pure finitely correlated
state, `u` is a local symmetry if and only if `ρ(ℰ_u) = 1`.

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
    (hΛpos : Λ.PosSemidef) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : transferMap A 1 = 1) :
    IsLocalSymmetry A u Λ ↔
      ∃ V : Matrix (Fin D) (Fin D) ℂ,
        V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
        ∃ μ : ℂ, ‖μ‖ = 1 ∧
          twistedTransferMap A u V = μ • V := by
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
    (hΛpos : Λ.PosSemidef) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : transferMap A 1 = 1) :
    HasStringOrder A u Λ ↔ IsLocalSymmetry A u Λ := by
  sorry

/-- **Virtual symmetry from string order**: If string order exists
for `u`, then there exists a virtual unitary `V` satisfying C1,
i.e. intertwining `u` with `V` at the level of MPS matrices.

This connects string order to the projective representation from
`VirtualRepresentation.lean`. -/
theorem virtualUnitary_of_stringOrder
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosSemidef) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : transferMap A 1 = 1)
    (hSO : HasStringOrder A u Λ) :
    ∃ V : Matrix (Fin D) (Fin D) ℂ,
      V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
      CondC1 A u V := by
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
      (hΛA : Λ_A.PosSemidef) (hΛB : Λ_B.PosSemidef)
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
