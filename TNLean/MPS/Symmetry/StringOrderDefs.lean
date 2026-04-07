/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Core.Transfer
import TNLean.Channel.KrausFreedom
import TNLean.Channel.KrausRepresentation
import TNLean.Spectral.SpectralGap
import Mathlib.Analysis.Matrix.Order

/-!
# String order: definitions and condition equivalences

This file collects the core definitions for the string-order / local-symmetry
theory of Pérez-García, Wolf, Sanz, Verstraete, Cirac (arXiv:0802.0447):

* The **twisted transfer map** `ℰ_u` and its iterates.
* The **string order parameter** `R_L(u)` and its boundary refinement.
* **Local symmetry** and **HasStringOrder** predicates.
* **Conditions C1/C2/C3** and their equivalences.

The main equivalence theorems live in `TNLean.MPS.Symmetry.StringOrder`.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447 (PRL 2008)
* Wolf, *Quantum Channels & Operations*, Chapter 2
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

/-- Unitary mixing of the Kraus family does not change the associated transfer
map, so the twisted companion tensor defines the same channel as `A`. -/
lemma transferMap_twistedMixedCompanion_eq (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (twistedMixedCompanion A u) X = transferMap A X := by
  simpa [transferMap_apply] using
    kraus_same_map_of_unitary_combination (twistedMixedCompanion A u) A uᴴ
      (by simpa using hu)
      (fun j => by
        simp [twistedMixedCompanion, Matrix.conjTranspose_apply])
      X

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

/-- `stringOrderParam` is the weighted trace pairing of the `L`-th mixed-transfer
iterate for `A` and the twisted Kraus companion family. -/
private lemma stringOrderParam_eq_trace_mixedTransfer (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (L : ℕ) :
    stringOrderParam A u Λ L =
      Matrix.trace
        (Λ * (((mixedTransferMap A (twistedMixedCompanion A u)) ^ L) 1)) := by
  simp [stringOrderParam, twistedTransferIter, twistedTransferMap_eq_mixedTransfer]

/-- For a unital transfer map and trace-one boundary state, the untwisted string
order parameter is constantly `1`. -/
private lemma stringOrderParam_one_eq_one
    (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛtr : Matrix.trace Λ = 1)
    (hNorm : transferMap A 1 = 1) (L : ℕ) :
    stringOrderParam A 1 Λ L = 1 := by
  have hpow_one :
      ((transferMap A) ^ L) (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    induction L with
    | zero =>
        simp
    | succ n ih =>
        calc
          ((transferMap A) ^ (n + 1)) (1 : Matrix (Fin D) (Fin D) ℂ)
              = transferMap A (((transferMap A) ^ n) 1) := by
                  simp [pow_succ']
          _ = transferMap A 1 := by rw [ih]
          _ = 1 := hNorm
  have htwisted_pow_one :
      ((twistedTransferMap A 1) ^ L) (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    have htwisted_eq : twistedTransferMap A 1 = transferMap A := by
      ext X i j
      exact congrArg (fun M => M i j) (twistedTransferMap_one (A := A) X)
    simpa [htwisted_eq] using hpow_one
  simp [stringOrderParam, twistedTransferIter, htwisted_pow_one, hΛtr]

/-! ### Boundary string order and local symmetry -/

/-- The virtual-boundary version of the string-order expression:
`tr(Λ X ℰ_u^L(Y))`.

This absorbs the paper's endpoint operators `x,y` into arbitrary
virtual boundary matrices `X,Y`. For injective tensors, sufficiently
long physical boundary insertions span all such virtual boundaries,
so this is the right reusable formalization of the paper's boundary
criterion. -/
noncomputable def stringOrderBoundaryParam (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ X Y : Matrix (Fin D) (Fin D) ℂ) (L : ℕ) : ℂ :=
  Matrix.trace (Λ * X * twistedTransferIter A u L Y)

/-- The original one-sided string-order parameter is the boundary expression with
trivial boundaries `X = Y = 1`. -/
private lemma stringOrderBoundaryParam_one_one (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (L : ℕ) :
    stringOrderBoundaryParam A u Λ 1 1 L = stringOrderParam A u Λ L := by
  simp [stringOrderBoundaryParam, stringOrderParam]

/-- If the continuous linear operator underlying the twisted transfer map has
spectral radius `< 1`, then every virtual-boundary string-order sequence tends
to `0`. -/
lemma stringOrderBoundaryParam_tendsto_zero_of_spectralRadius_lt_one
    (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ X Y : Matrix (Fin D) (Fin D) ℂ)
    (hsr :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (twistedTransferMap A u)) < 1) :
    Filter.Tendsto (fun L => stringOrderBoundaryParam A u Λ X Y L)
      Filter.atTop (nhds 0) := by
  let V := Matrix (Fin D) (Fin D) ℂ
  let F' : V →L[ℂ] V :=
    (Module.End.toContinuousLinearMap V) (twistedTransferMap A u)
  haveI : FiniteDimensional ℂ (V →L[ℂ] V) :=
    (Module.End.toContinuousLinearMap V).toLinearEquiv.finiteDimensional
  have hpow : Filter.Tendsto (fun L => F' ^ L) Filter.atTop (nhds 0) :=
    by
      let hFinite : FiniteDimensional ℂ (V →L[ℂ] V) :=
        (Module.End.toContinuousLinearMap V).toLinearEquiv.finiteDimensional
      letI : FiniteDimensional ℂ (V →L[ℂ] V) := hFinite
      let hComplete : CompleteSpace (V →L[ℂ] V) := FiniteDimensional.complete ℂ (V →L[ℂ] V)
      exact @pow_tendsto_zero_of_spectralRadius_lt_one (V →L[ℂ] V)
        inferInstance hComplete inferInstance F' <| by
          simpa [F'] using hsr
  have hEval := (ContinuousLinearMap.apply ℂ V Y).continuous.tendsto (0 : V →L[ℂ] V)
  rw [map_zero] at hEval
  have hIter0 :
      Filter.Tendsto (fun L => ((twistedTransferMap A u) ^ L) Y)
        Filter.atTop (nhds 0) := by
    have hEval0 : Filter.Tendsto (fun L => (F' ^ L) Y) Filter.atTop (nhds 0) :=
      hEval.comp hpow
    refine hEval0.congr' ?_
    filter_upwards with L
    have hpow_eq :
        (((Module.End.toContinuousLinearMap V) (twistedTransferMap A u)) ^ L) =
          (Module.End.toContinuousLinearMap V) ((twistedTransferMap A u) ^ L) := by
      exact (map_pow (Module.End.toContinuousLinearMap V) (twistedTransferMap A u) L).symm
    exact congrArg (fun T => T Y) hpow_eq
  let φ : V →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      ((LinearMap.mulLeft ℂ Λ).comp (LinearMap.mulLeft ℂ X))
  have hφ_cont : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  have hφ0 :
      Filter.Tendsto (fun L => φ (((twistedTransferMap A u) ^ L) Y))
        Filter.atTop (nhds 0) := by
    rw [show (0 : ℂ) = φ 0 by simp]
    exact hφ_cont.continuousAt.tendsto.comp hIter0
  simpa [stringOrderBoundaryParam, twistedTransferIter, φ, Matrix.mul_assoc] using hφ0

/-- Local symmetry in the virtual FCS language of the paper: there is a unitary
virtual intertwiner satisfying the phased covariance relation and preserving the
stationary boundary state `Λ`. -/
def IsLocalSymmetry (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∃ V : Matrix (Fin D) (Fin D) ℂ, ∃ μ : ℂ,
    V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ ‖μ‖ = 1 ∧
    Vᴴ * Λ * V = Λ ∧
    ∀ i : Fin d,
      ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ)

/-- String order exists if some virtual boundary pair produces a uniformly
non-decaying twisted-transfer overlap. This is the matrix-level version of the
paper's endpoint-operator criterion. -/
def HasStringOrder (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∃ X Y : Matrix (Fin D) (Fin D) ℂ, ∃ c : ℝ, 0 < c ∧
    ∀ L : ℕ,
      c ≤ ‖stringOrderBoundaryParam A u Λ X Y L‖

/-- A uniformly positive lower bound on a boundary string-order sequence prevents
convergence to `0`. -/
lemma not_tendsto_zero_of_hasStringOrder
    (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hSO : HasStringOrder A u Λ) :
    ∃ X Y : Matrix (Fin D) (Fin D) ℂ,
      ¬ Filter.Tendsto (fun L => stringOrderBoundaryParam A u Λ X Y L)
        Filter.atTop (nhds 0) := by
  rcases hSO with ⟨X, Y, c, hc, hbound⟩
  refine ⟨X, Y, ?_⟩
  intro hzero
  have hsmall :
      ∀ᶠ L in Filter.atTop, ‖stringOrderBoundaryParam A u Λ X Y L‖ < c :=
    hzero.norm.eventually (Iio_mem_nhds (by simpa using hc))
  rcases Filter.eventually_atTop.1 hsmall with ⟨L₀, hL₀⟩
  have hge := hbound L₀
  exact not_lt_of_ge hge (hL₀ L₀ le_rfl)

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
    (_hA : IsInjective A)
    (hV : V * Vᴴ = 1)
    (hC2 : CondC2 A V) :
    ∃ u : Matrix (Fin d) (Fin d) ℂ, u * uᴴ = 1 ∧ CondC1 A u V := by
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

end MPSTensor
