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
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.Channel.Irreducible.Similarity
import TNLean.Channel.Irreducible.TraceAdjoint
import TNLean.Channel.KrausFreedom
import TNLean.Channel.KrausRepresentation
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.SpectralGapNT
import Mathlib.Analysis.Matrix.Order

/-!
# String order parameters and local symmetry equivalence

This file formalizes the main results of Pérez-García, Wolf, Sanz, Verstraete,
Cirac, *String order and symmetries in quantum spin lattices* (PRL 2008,
arXiv:0802.0447):

* The **twisted transfer map** `ℰ_u` associated to a unitary `u` on the
  physical index.
* The **string order parameter** `R_L(u) = ⟨ψ_L | u^{⊗L} | ψ_L⟩`,
  together with its virtual-boundary refinement `tr(Λ X · ℰ_u^L(Y))`.
* **Conditions C1/C2/C3**: three equivalent formulations of the
  intertwining relation between the on-site unitary `u` and a virtual
  unitary `V`.
* The **main equivalence**: for an injective (pure) FCS, string order
  for `u` exists iff `u` is a local symmetry iff `ρ(ℰ_u) = 1`,
  assuming the canonical fixed-point normalization
  `transferMap A 1 = 1`, `transferMap A† Λ = Λ`.

## Main definitions

* `MPSTensor.twistedTransferMap` — the u-twisted transfer map `ℰ_u`
* `MPSTensor.stringOrderParam` — the string order parameter `R_L(u)`
* `MPSTensor.IsLocalSymmetry` — the paper's virtual-unitary local-symmetry
  criterion, including `V† Λ V = Λ`
* `MPSTensor.CondC1` — intertwining: `∑_j U_{ij} A^j = V A^i V†`
* `MPSTensor.CondC2` — covariance: `ℰ(V X V†) = V ℰ(X) V†`
* `MPSTensor.CondC3` — doubled commutation: `[E, V ⊗ V̄] = 0`
* `MPSTensor.HasStringOrder` — nondecay of a virtual-boundary string-order
  witness

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

This file now proves the condition equivalences, the spectral-radius bound, the
modulus-one rigidity bridge, and the paper-faithful local-symmetry/string-order
equivalences in the canonical FCS setting.
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

/-! ### Main equivalence theorems -/

section MainTheorems

-- The transfer map of a TP-gauged tensor is the similarity transform of the
-- original transfer map by the positive square root of the adjoint fixed point.
set_option maxHeartbeats 800000 in
-- Expanding `tpGauge`, `transferMap`, and CFC adjoint identities is kernel-expensive here.
lemma transferMap_tpGauge_eq_similarityMap
    (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosDef) :
    transferMap (tpGauge (d := d) (D := D) A σ) =
      similarityMap (D := D) (CFC.sqrt σ)⁻¹ (transferMap A) := by
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_det : IsUnit S.det := by
    simpa [S] using isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ
  have hS_herm : Sᴴ = S := by
    simpa [S] using conjTranspose_cfc_sqrt (D := D) σ
  have hS_inv_inv : S⁻¹⁻¹ = S := Matrix.nonsing_inv_nonsing_inv S hS_det
  have hS_inv_herm : (S⁻¹)ᴴ = (Sᴴ)⁻¹ := Matrix.conjTranspose_nonsing_inv S
  have hS_inv_herm' : (S⁻¹)ᴴ = S⁻¹ := by simpa [hS_herm] using hS_inv_herm
  ext X i j
  have hcalc :
      transferMap (tpGauge (d := d) (D := D) A σ) X =
        similarityMap (D := D) S⁻¹ (transferMap A) X := by
    calc
      transferMap (tpGauge (d := d) (D := D) A σ) X
          = ∑ i : Fin d, (S * A i * S⁻¹) * X * (S * A i * S⁻¹)ᴴ := by
              simp [transferMap_apply, tpGauge, S]
              rfl
      _ = ∑ i : Fin d, S * (A i * (S⁻¹ * X * S⁻¹ * (A i)ᴴ)) * S := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
            simp [Matrix.mul_assoc, hS_inv_herm', hS_herm]
      _ = S * (∑ i : Fin d, A i * (S⁻¹ * X * S⁻¹ * (A i)ᴴ)) * S := by
            rw [Matrix.sum_mul_mul]
      _ = similarityMap (D := D) S⁻¹ (transferMap A) X := by
            simp [similarityMap, transferMap_apply, S, hS_inv_inv, hS_inv_herm',
              Matrix.mul_assoc]
  exact congrFun (congrFun hcalc i) j

/-- TP gauging preserves irreducibility when the original transfer map is
irreducible. -/
lemma isIrreducibleTensor_tpGauge_of_isIrreducibleMap [NeZero D]
    (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosDef)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A)) :
    IsIrreducibleTensor (d := d) (D := D) (tpGauge (d := d) (D := D) A σ) := by
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_det : S.det ≠ 0 := by
    exact (isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ).ne_zero
  have hIrrSim :
      IsIrreducibleMap (similarityMap (D := D) S⁻¹ (transferMap A)) := by
    refine isIrreducibleMap_similarity (D := D) ?_ hIrr
    simpa [S, Matrix.det_nonsing_inv] using inv_ne_zero hS_det
  have hEq :
      transferMap (tpGauge (d := d) (D := D) A σ) =
        similarityMap (D := D) S⁻¹ (transferMap A) := by
    simpa [S] using transferMap_tpGauge_eq_similarityMap (A := A) (σ := σ) hσ
  have hIrr' : IsIrreducibleMap
      (transferMap (d := d) (D := D) (tpGauge (d := d) (D := D) A σ)) := by
    simpa [hEq] using hIrrSim
  exact isIrreducibleTensor_of_isIrreducibleMap _ hIrr'

/-- Gauge equivalence on the left and right transports a gauge-phase
equivalence back to the original tensors. -/
lemma gaugePhaseEquiv_of_gaugeEquiv_left_right
    {A A' B B' : MPSTensor d D}
    (hAA' : GaugeEquiv A A')
    (hA'B' : GaugePhaseEquiv A' B')
    (hBB' : GaugeEquiv B B') :
    GaugePhaseEquiv A B := by
  obtain ⟨X, hX⟩ := hAA'
  obtain ⟨Y, ζ, hζ, hY⟩ := hA'B'
  obtain ⟨Z, hZ⟩ := hBB'
  refine ⟨Z⁻¹ * Y * X, ζ, hζ, ?_⟩
  intro i
  have hB' : B' i = Z * B i * Z⁻¹ := hZ i
  calc
    B i = Z⁻¹ * B' i * Z := by
      rw [hB']
      simp [Matrix.mul_assoc]
    _ = Z⁻¹ * (ζ • (Y * A' i * Y⁻¹)) * Z := by rw [hY i]
    _ = ζ • (Z⁻¹ * (Y * A' i * Y⁻¹) * Z) := by
          simp [Matrix.mul_assoc]
    _ = ζ • (Z⁻¹ * (Y * (X * A i * X⁻¹) * Y⁻¹) * Z) := by rw [hX i]
    _ = ζ • (((Z⁻¹ * Y * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
          (((((Z⁻¹ * Y * X : GL (Fin D) ℂ)⁻¹ : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ))) := by
          simp [Matrix.mul_assoc, mul_inv_rev]

private structure TwistedTPGaugeSetup [NeZero D]
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ) where
  B : MPSTensor d D
  hB_def : B = twistedMixedCompanion A u
  hB_eq : ∀ X : Matrix (Fin D) (Fin D) ℂ, transferMap B X = transferMap A X
  σ : Matrix (Fin D) (Fin D) ℂ
  hσ_pd : σ.PosDef
  hσ_fixB : transferMap (d := d) (D := D) (fun i => (B i)ᴴ) σ = σ
  S : Matrix (Fin D) (Fin D) ℂ
  hS_def : S = CFC.sqrt σ
  hS_herm : Sᴴ = S
  hS_mul_inv : S * S⁻¹ = 1
  hS_inv_mul : S⁻¹ * S = 1
  hS_hMul_inv : Sᴴ * (Sᴴ)⁻¹ = 1
  hS_inv_herm : (S⁻¹)ᴴ = S⁻¹
  A' : MPSTensor d D
  hA'_def : A' = tpGauge (d := d) (D := D) A σ
  B' : MPSTensor d D
  hB'_def : B' = tpGauge (d := d) (D := D) B σ
  hA'TP : ∑ i : Fin d, (A' i)ᴴ * A' i = 1
  hB'TP : ∑ i : Fin d, (B' i)ᴴ * B' i = 1
  hIrrA' : IsIrreducibleTensor (d := d) (D := D) A'
  hIrrB' : IsIrreducibleTensor (d := d) (D := D) B'

private noncomputable def twistedTPGaugeSetup [NeZero D]
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (hNorm : transferMap A 1 = 1) :
    TwistedTPGaugeSetup (d := d) (D := D) A u := by
  classical
  let B : MPSTensor d D := twistedMixedCompanion A u
  have hB_eq : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      transferMap B X = transferMap A X := by
    intro X
    simpa [B] using transferMap_twistedMixedCompanion_eq (A := A) (u := u) hu X
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    injective_implies_irreducibleCP A hA
  have hEqBA : transferMap B = transferMap A := LinearMap.ext hB_eq
  have hIrrB : IsIrreducibleMap (transferMap (d := d) (D := D) B) := by
    simpa [hEqBA] using hIrrA
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
  let hσ_exists :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible
      (E := transferMap (d := d) (D := D) fun i => (A i)ᴴ) hChAdj hIrrAdj (NeZero.pos D)
  let σ := Classical.choose hσ_exists
  have hσ_spec := Classical.choose_spec hσ_exists
  have hσ_pd : σ.PosDef := hσ_spec.2.1
  have hσ_fixA : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ = σ := hσ_spec.2.2.1
  have hσ_fixB : transferMap (d := d) (D := D) (fun i => (B i)ᴴ) σ = σ := by
    calc
      transferMap (d := d) (D := D) (fun i => (B i)ᴴ) σ
          = transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ := by
              simpa [B, transferMap_apply, Matrix.mul_assoc] using
                kraus_dual_eq_of_map_eq B A
                  (fun X => by simpa [transferMap_apply] using hB_eq X) σ
      _ = σ := hσ_fixA
  let S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_herm : Sᴴ = S := by
    simpa [S] using conjTranspose_cfc_sqrt (D := D) σ
  have hS_det : IsUnit (Matrix.det S) := by
    simpa [S] using isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ_pd
  have hS_mul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det
  have hS_inv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS_det
  have hS_detT : IsUnit (Matrix.det Sᴴ) := by
    simpa [Matrix.det_conjTranspose] using IsUnit.star hS_det
  have hS_hMul_inv : Sᴴ * (Sᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv Sᴴ hS_detT
  have hS_inv_herm : (S⁻¹)ᴴ = S⁻¹ := by
    simpa [hS_herm] using Matrix.conjTranspose_nonsing_inv S
  let A' := tpGauge (d := d) (D := D) A σ
  let B' := tpGauge (d := d) (D := D) B σ
  have hA'TP : ∑ i : Fin d, (A' i)ᴴ * A' i = 1 := by
    simpa [A'] using
      tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint (A := A) (ρ := σ) hσ_pd hσ_fixA
  have hB'TP : ∑ i : Fin d, (B' i)ᴴ * B' i = 1 := by
    simpa [B'] using
      tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint (A := B) (ρ := σ) hσ_pd hσ_fixB
  have hIrrA' : IsIrreducibleTensor (d := d) (D := D) A' := by
    simpa [A'] using isIrreducibleTensor_tpGauge_of_isIrreducibleMap
      (A := A) (σ := σ) hσ_pd hIrrA
  have hIrrB' : IsIrreducibleTensor (d := d) (D := D) B' := by
    simpa [B'] using isIrreducibleTensor_tpGauge_of_isIrreducibleMap
      (A := B) (σ := σ) hσ_pd hIrrB
  exact
    { B := B
      hB_def := rfl
      hB_eq := hB_eq
      σ := σ
      hσ_pd := hσ_pd
      hσ_fixB := hσ_fixB
      S := S
      hS_def := rfl
      hS_herm := hS_herm
      hS_mul_inv := hS_mul_inv
      hS_inv_mul := hS_inv_mul
      hS_hMul_inv := hS_hMul_inv
      hS_inv_herm := hS_inv_herm
      A' := A'
      hA'_def := rfl
      B' := B'
      hB'_def := rfl
      hA'TP := hA'TP
      hB'TP := hB'TP
      hIrrA' := hIrrA'
      hIrrB' := hIrrB' }

private theorem twistedTPGaugeSetup_hasEigenvalue [NeZero D]
    (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (setup : TwistedTPGaugeSetup (d := d) (D := D) A u)
    (ev : ℂ) (V : Matrix (Fin D) (Fin D) ℂ)
    (hV : V ≠ 0)
    (hEig : twistedTransferMap A u V = ev • V) :
    Module.End.HasEigenvalue (mixedTransferMap setup.A' setup.B') ev := by
  have hEigMixed : mixedTransferMap A setup.B V = ev • V := by
    simpa [setup.hB_def, twistedTransferMap_eq_mixedTransfer] using hEig
  have hEigGauge :
      mixedTransferMap setup.A' setup.B' (setup.S * V * setup.Sᴴ) =
        ev • (setup.S * V * setup.Sᴴ) := by
    have hTerm :
        ∀ i : Fin d,
          setup.A' i * (setup.S * V * setup.Sᴴ) * (setup.B' i)ᴴ =
            setup.S * (A i * V * (setup.B i)ᴴ) * setup.Sᴴ := by
      intro i
      have hAeq : setup.A' i = setup.S * A i * setup.S⁻¹ := by
        rw [setup.hA'_def, tpGauge, setup.hS_def]
        rfl
      have hBstar :
          (setup.B' i)ᴴ = setup.S⁻¹ * (setup.B i)ᴴ * setup.S := by
        calc
          (setup.B' i)ᴴ
              = ((setup.S * setup.B i * setup.S⁻¹ : Matrix (Fin D) (Fin D) ℂ))ᴴ := by
                  rw [setup.hB'_def, tpGauge, setup.hS_def]
                  rfl
          _ = (setup.S⁻¹)ᴴ * (setup.B i)ᴴ * setup.Sᴴ := by
                simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = setup.S⁻¹ * (setup.B i)ᴴ * setup.S := by
                simp [setup.hS_herm, setup.hS_inv_herm]
      calc
        setup.A' i * (setup.S * V * setup.Sᴴ) * (setup.B' i)ᴴ
            = (setup.S * A i * setup.S⁻¹) * (setup.S * V * setup.S) *
                (setup.S⁻¹ * (setup.B i)ᴴ * setup.S) := by
                  rw [hAeq, hBstar, setup.hS_herm]
        _ = setup.S * (A i * V * (setup.B i)ᴴ) * setup.S := by
              calc
                (setup.S * A i * setup.S⁻¹) * (setup.S * V * setup.S) *
                    (setup.S⁻¹ * (setup.B i)ᴴ * setup.S)
                    = setup.S * A i * (setup.S⁻¹ * (setup.S * V * setup.S)) *
                        (setup.S⁻¹ * (setup.B i)ᴴ * setup.S) := by
                        simp [Matrix.mul_assoc]
                _ = setup.S * A i * (V * setup.S) *
                      (setup.S⁻¹ * (setup.B i)ᴴ * setup.S) := by
                      rw [show setup.S⁻¹ * (setup.S * V * setup.S) = V * setup.S by
                        calc
                          setup.S⁻¹ * (setup.S * V * setup.S)
                              = (setup.S⁻¹ * setup.S) * V * setup.S := by
                            simp [Matrix.mul_assoc]
                          _ = V * setup.S := by simp [setup.hS_inv_mul]]
                _ = setup.S * A i * (V * (setup.B i)ᴴ * setup.S) := by
                      calc
                        setup.S * A i * (V * setup.S) *
                            (setup.S⁻¹ * (setup.B i)ᴴ * setup.S)
                            = setup.S * A i *
                                ((V * setup.S) * (setup.S⁻¹ * (setup.B i)ᴴ * setup.S)) := by
                                simp [Matrix.mul_assoc]
                        _ = setup.S * A i * (V * (setup.B i)ᴴ * setup.S) := by
                              congr 1
                              calc
                                (V * setup.S) * (setup.S⁻¹ * (setup.B i)ᴴ * setup.S)
                                    = V * (setup.S * setup.S⁻¹) * (setup.B i)ᴴ * setup.S := by
                                        simp [Matrix.mul_assoc]
                                _ = V * (setup.B i)ᴴ * setup.S := by
                                      simp [setup.hS_mul_inv, Matrix.mul_assoc]
                _ = setup.S * (A i * V * (setup.B i)ᴴ) * setup.S := by
                      simp [Matrix.mul_assoc]
        _ = setup.S * (A i * V * (setup.B i)ᴴ) * setup.Sᴴ := by
              simp [setup.hS_herm]
    calc
      mixedTransferMap setup.A' setup.B' (setup.S * V * setup.Sᴴ)
          = ∑ i : Fin d,
              setup.A' i * (setup.S * V * setup.Sᴴ) * (setup.B' i)ᴴ := by
                  simp [mixedTransferMap_apply]
      _ = ∑ i : Fin d, setup.S * (A i * V * (setup.B i)ᴴ) * setup.Sᴴ := by
            simp [hTerm]
      _ = setup.S * (∑ i : Fin d, A i * V * (setup.B i)ᴴ) * setup.Sᴴ := by
            simpa using
              (Matrix.sum_mul_mul
                (L := setup.S) (M := fun i : Fin d => A i * V * (setup.B i)ᴴ) (R := setup.Sᴴ))
      _ = ev • (setup.S * V * setup.Sᴴ) := by
            simpa [mixedTransferMap_apply, Matrix.mul_assoc] using
              congrArg (fun M => setup.S * M * setup.Sᴴ) hEigMixed
  have hGauge_ne : setup.S * V * setup.Sᴴ ≠ 0 := by
    intro hZero
    apply hV
    have h' : setup.S⁻¹ * (setup.S * V * setup.Sᴴ) * (setup.Sᴴ)⁻¹ = 0 := by
      simp [hZero]
    have h'' : setup.S⁻¹ * (setup.S * V) = 0 := by
      simpa [Matrix.mul_assoc, setup.hS_hMul_inv] using h'
    have h''' : (setup.S⁻¹ * setup.S) * V = 0 := by
      simpa [Matrix.mul_assoc] using h''
    simpa [setup.hS_inv_mul] using h'''
  rw [Module.End.hasEigenvalue_iff]
  intro hBot
  have hMem :
      setup.S * V * setup.Sᴴ ∈ Module.End.eigenspace
        (mixedTransferMap setup.A' setup.B') ev :=
    Module.End.mem_eigenspace_iff.mpr hEigGauge
  have : setup.S * V * setup.Sᴴ ∈ (⊥ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
    simpa [hBot] using hMem
  exact hGauge_ne (Submodule.mem_bot ℂ |>.mp this)

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

/-- If the twisted companion family is gauge-phase equivalent to `A`, the gauge
matrix can be normalized to a unitary and converted into the phased virtual
symmetry relation from the string-order paper. -/
private theorem virtualUnitary_of_gaugePhaseEquiv_twisted
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (hNorm : transferMap A 1 = 1)
    (hGauge : GaugePhaseEquiv A (twistedMixedCompanion A u)) :
    ∃ V : Matrix (Fin D) (Fin D) ℂ, ∃ μ : ℂ,
      V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ ‖μ‖ = 1 ∧
      ∀ i : Fin d,
        ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ) := by
  classical
  rcases eq_or_ne D 0 with hD | hD
  · subst hD
    refine ⟨1, 1, by simp, by simp, by simp, ?_⟩
    intro i
    ext a
    exact Fin.elim0 a
  haveI : NeZero D := ⟨hD⟩
  let B : MPSTensor d D := twistedMixedCompanion A u
  obtain ⟨Xgl, ζ, hζ, hX⟩ := hGauge
  let X : Matrix (Fin D) (Fin D) ℂ := (Xgl : Matrix (Fin D) (Fin D) ℂ)
  let Xin : Matrix (Fin D) (Fin D) ℂ := ((Xgl⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hX_mul_inv : X * Xin = 1 := by
    simp [X, Xin]
  have hX_inv_mul : Xin * X = 1 := by
    simp [X, Xin]
  have hB_eq : ∀ Y : Matrix (Fin D) (Fin D) ℂ, transferMap B Y = transferMap A Y := by
    intro Y
    simpa [B] using transferMap_twistedMixedCompanion_eq (A := A) (u := u) hu Y
  let Q : Matrix (Fin D) (Fin D) ℂ := X * Xᴴ
  have hQ_psd : Q.PosSemidef := by
    simpa [Q] using Matrix.posSemidef_self_mul_conjTranspose X
  let C : MPSTensor d D := fun i => X * A i * Xin
  have hB_C : B = fun i => ζ • C i := by
    funext i
    simpa [B, C, X, Xin] using hX i
  have hXinQ : Xin * Q * Xinᴴ = 1 := by
    calc
      Xin * Q * Xinᴴ = (Xin * X) * Xᴴ * Xinᴴ := by
        simp [Q, Matrix.mul_assoc]
      _ = Xᴴ * Xinᴴ := by
        simp [hX_inv_mul]
      _ = (Xin * X)ᴴ := by
        simp [Matrix.conjTranspose_mul]
      _ = 1 := by
        simp [hX_inv_mul]
  have hQ_eigC : transferMap C Q = Q := by
    calc
      transferMap C Q = X * transferMap A (Xin * Q * Xinᴴ) * Xᴴ := by
        simpa [C, X, Xin, Matrix.mul_assoc] using transferMap_gauge_conj A Xgl Q
      _ = X * transferMap A 1 * Xᴴ := by rw [hXinQ]
      _ = Q := by simp [Q, hNorm]
  have hQ_eigB : transferMap B Q = (Complex.normSq ζ : ℂ) • Q := by
    calc
      transferMap B Q = transferMap (fun i => ζ • C i) Q := by
        simp [hB_C]
      _ = ∑ i : Fin d, (ζ • C i) * Q * (ζ • C i)ᴴ := by
            simp [transferMap_apply]
      _ = ∑ i : Fin d, (Complex.normSq ζ : ℂ) • (C i * Q * (C i)ᴴ) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [Matrix.conjTranspose_smul, smul_smul,
              Complex.normSq_eq_conj_mul_self, mul_comm]
      _ = (Complex.normSq ζ : ℂ) • ∑ i : Fin d, C i * Q * (C i)ᴴ := by
            simp [Finset.smul_sum]
      _ = (Complex.normSq ζ : ℂ) • transferMap C Q := by
            simp [transferMap_apply]
      _ = (Complex.normSq ζ : ℂ) • Q := by rw [hQ_eigC]
  have hQ_eigA : transferMap A Q = (Complex.normSq ζ : ℂ) • Q := by
    rw [← hB_eq Q]
    exact hQ_eigB
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hXh_inv_mul : Xᴴ * Xinᴴ = 1 := by
      calc
        Xᴴ * Xinᴴ = (Xin * X)ᴴ := by
          simp [Matrix.conjTranspose_mul]
        _ = 1 := by
          simp [hX_inv_mul]
    have : X = 0 := by
      calc
        X = X * 1 := by simp
        _ = X * (Xᴴ * Xinᴴ) := by rw [hXh_inv_mul]
        _ = (X * Xᴴ) * Xinᴴ := by simp [Matrix.mul_assoc]
        _ = 0 := by simp [Q, hQ0]
    have hX_ne : X ≠ 0 := by
      intro hX0
      have hbad := hX_mul_inv
      simp [X, Xin, hX0] at hbad
    exact hX_ne this
  have hζ_sq_eq_one : Complex.normSq ζ = 1 := by
    have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
      injective_implies_irreducibleCP A hA
    have hCPA : IsCPMap (transferMap (d := d) (D := D) A) :=
      transferMap_isCPMap A
    have hone_psd : (1 : Matrix (Fin D) (Fin D) ℂ).PosSemidef := by
      simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
    have hone_eig : transferMap A 1 = ((1 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa using hNorm
    exact
      eigenvalue_unique_of_irreducible_cp
        (E := transferMap (d := d) (D := D) A) hCPA hIrrA
        (1 : Matrix (Fin D) (Fin D) ℂ) Q 1 (Complex.normSq ζ)
        hone_psd one_ne_zero (by norm_num) hQ_psd hQ_ne
        (Complex.normSq_pos.2 hζ) hone_eig hQ_eigA |>.symm
  have hQ_fix : transferMap A Q = Q := by
    simpa [hζ_sq_eq_one] using hQ_eigA
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    injective_implies_irreducibleCP A hA
  have hone_psd : (1 : Matrix (Fin D) (Fin D) ℂ).PosSemidef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := A) hIrrA
      (1 : Matrix (Fin D) (Fin D) ℂ) Q hone_psd one_ne_zero hQ_psd hNorm hQ_fix with
    ⟨c, hQ_scalar⟩
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    apply hQ_ne
    simp [hQ_scalar, hc0]
  have hc_nonneg : 0 ≤ c := by
    have hscalar_psd : (c • (1 : Matrix (Fin D) (Fin D) ℂ)).PosSemidef := by
      simpa [hQ_scalar] using hQ_psd
    have hdiag_psd : (Matrix.diagonal (fun _ : Fin D => c)).PosSemidef := by
      simpa [Matrix.smul_one_eq_diagonal] using hscalar_psd
    have hdiag_nonneg := (Matrix.posSemidef_diagonal_iff).1 hdiag_psd
    exact hdiag_nonneg ⟨0, NeZero.pos D⟩
  have hc_eq_real : c = (c.re : ℂ) := by
    exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hc_nonneg).2.symm)
  have hcre_nonneg : 0 ≤ c.re := (Complex.nonneg_iff.mp hc_nonneg).1
  have hcre_ne0 : c.re ≠ 0 := by
    intro h0
    apply hc_ne0
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = 0 := by simp [h0]
  have hcre_pos : 0 < c.re := lt_of_le_of_ne hcre_nonneg (Ne.symm hcre_ne0)
  set a : ℂ := (Real.sqrt c.re : ℂ)
  have ha_ne0 : a ≠ 0 := by
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.mpr hcre_pos)
  have hc_eq_sq : c = a * a := by
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = (((Real.sqrt c.re) ^ 2 : ℝ) : ℂ) := by
            simp [Real.sq_sqrt hcre_nonneg]
      _ = a * a := by
            rw [pow_two]
            simp [a]
  have hstar_a : star a = a := by
    simp [a]
  have hstar_a_inv : star a⁻¹ = a⁻¹ := by
    simp [a]
  let U : Matrix (Fin D) (Fin D) ℂ := a⁻¹ • X
  have hU_unitary_left : U * Uᴴ = 1 := by
    calc
      U * Uᴴ = (star a⁻¹ * a⁻¹) • (X * Xᴴ) := by
            simp [U, Matrix.conjTranspose_smul, smul_smul]
      _ = (a⁻¹ * a⁻¹) • Q := by
            rw [hstar_a_inv]
      _ = ((a⁻¹ * a⁻¹) * c) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
            rw [hQ_scalar]
            simp [smul_smul, mul_comm]
      _ = 1 := by
            have hscalar : ((a⁻¹ * a⁻¹) * c : ℂ) = 1 := by
              calc
                (a⁻¹ * a⁻¹) * c = (a⁻¹ * a⁻¹) * (a * a) := by rw [hc_eq_sq]
                _ = 1 := by field_simp [ha_ne0]
            simp [hscalar]
  have hU_unitary_right : Uᴴ * U = 1 := mul_eq_one_comm.mp hU_unitary_left
  have hX_eq : X = a • U := by
    simp [U, ha_ne0]
  have hXinv_eq : Xin = a⁻¹ • Uᴴ := by
    have hXin' : X⁻¹ = a⁻¹ • Uᴴ := by
      apply Matrix.inv_eq_right_inv
      calc
        X * (a⁻¹ • Uᴴ) = (a • U) * (a⁻¹ • Uᴴ) := by rw [hX_eq]
        _ = (a * a⁻¹) • (U * Uᴴ) := by
              simpa [Matrix.mul_assoc] using smul_mul_smul_comm a U a⁻¹ Uᴴ
        _ = 1 := by simp [ha_ne0, hU_unitary_left]
    simpa [X, Xin] using hXin'
  refine ⟨Uᴴ, ζ⁻¹, ?_, ?_, ?_, ?_⟩
  · simpa using hU_unitary_right
  · simpa using hU_unitary_left
  · have hζ_norm : ‖ζ‖ = 1 := by
      have hsq : ‖ζ‖ ^ 2 = 1 := by
        simpa [Complex.normSq_eq_norm_sq] using hζ_sq_eq_one
      nlinarith [norm_nonneg ζ]
    simp [norm_inv, hζ_norm]
  · intro i
    have hBi : ∀ j : Fin d, B j = ζ • (U * A j * Uᴴ) := by
      intro j
      calc
        B j = ζ • (X * A j * Xin) := hX j
        _ = ζ • ((a • U) * A j * (a⁻¹ • Uᴴ)) := by rw [hX_eq, hXinv_eq]
        _ = ζ • (U * A j * Uᴴ) := by
              congr 1
              calc
                (a • U) * A j * (a⁻¹ • Uᴴ)
                    = (a • (U * A j)) * (a⁻¹ • Uᴴ) := by
                        simp [Matrix.mul_assoc]
                _ = (a * a⁻¹) • ((U * A j) * Uᴴ) := by
                      simpa [Matrix.mul_assoc] using
                        smul_mul_smul_comm a (U * A j) a⁻¹ Uᴴ
                _ = (a * a⁻¹) • (U * A j * Uᴴ) := by
                      simp [Matrix.mul_assoc]
                _ = U * A j * Uᴴ := by simp [ha_ne0]
    have hsum :
        ∑ j : Fin d, u i j • B j = A i := by
      have hcoeff :
          ∀ n' : Fin d,
            ∑ j : Fin d, u i j * (starRingEnd ℂ) (u n' j) = if i = n' then 1 else 0 := by
        intro n'
        have hentry := congrFun (congrFun hu i) n'
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hentry
      calc
        ∑ j : Fin d, u i j • B j
            = ∑ j : Fin d, ∑ n' : Fin d, (u i j * (starRingEnd ℂ) (u n' j)) • A n' := by
                refine Finset.sum_congr rfl ?_
                intro j _
                rw [show u i j • B j =
                  u i j • ∑ n' : Fin d, (starRingEnd ℂ) (u n' j) • A n' by
                    simp [B, twistedMixedCompanion]]
                simpa [smul_smul, mul_assoc] using
                  (Finset.smul_sum (s := Finset.univ)
                    (f := fun n' : Fin d => (starRingEnd ℂ) (u n' j) • A n')
                    (r := u i j))
        _ = ∑ n' : Fin d, ∑ j : Fin d, (u i j * (starRingEnd ℂ) (u n' j)) • A n' := by
              rw [Finset.sum_comm]
        _ = ∑ n' : Fin d, (∑ j : Fin d, u i j * (starRingEnd ℂ) (u n' j)) • A n' := by
              refine Finset.sum_congr rfl ?_
              intro n' _
              simpa using
                (Finset.sum_smul (s := Finset.univ)
                  (f := fun j : Fin d => u i j * (starRingEnd ℂ) (u n' j))
                  (x := A n')).symm
        _ = ∑ n' : Fin d, (if i = n' then 1 else 0) • A n' := by
              simp [hcoeff]
        _ = A i := by
              simp
    have htransport : Uᴴ * A i * U = ζ • (∑ j : Fin d, u i j • A j) := by
      have hsum_virtual : A i = ζ • (U * (∑ j : Fin d, u i j • A j) * Uᴴ) := by
        calc
          A i = ∑ j : Fin d, u i j • B j := hsum.symm
          _ = ∑ j : Fin d, u i j • (ζ • (U * A j * Uᴴ)) := by
                simp [hBi]
          _ = ζ • (U * (∑ j : Fin d, u i j • A j) * Uᴴ) := by
                simp [Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, mul_comm,
                  smul_smul, Matrix.mul_assoc]
      have hconj := congrArg (fun M => Uᴴ * M * U) hsum_virtual
      calc
        Uᴴ * A i * U = Uᴴ * (ζ • (U * (∑ j : Fin d, u i j • A j) * Uᴴ)) * U := by
              simpa [Matrix.mul_assoc] using hconj
        _ = ζ • (∑ j : Fin d, u i j • A j) := by
              calc
                Uᴴ * (ζ • (U * (∑ j : Fin d, u i j • A j) * Uᴴ)) * U
                    = ζ • (Uᴴ * ((U * (∑ j : Fin d, u i j • A j) * Uᴴ) * U)) := by
                        simp [Matrix.mul_assoc]
                _ = ζ • ((Uᴴ * U) * (∑ j : Fin d, u i j • A j) * (Uᴴ * U)) := by
                        simp [Matrix.mul_assoc]
                _ = ζ • (∑ j : Fin d, u i j • A j) := by
                        simp [hU_unitary_right]
    calc
      ∑ j : Fin d, u i j • A j = ζ⁻¹ • (ζ • (∑ j : Fin d, u i j • A j)) := by
            simp [hζ, smul_smul]
      _ = ζ⁻¹ • (Uᴴ * A i * U) := by
            rw [htransport]
      _ = ζ⁻¹ • (Uᴴ * A i * Uᴴᴴ) := by
            simp

/-- A phased virtual symmetry immediately produces a peripheral eigenvector of the
twisted transfer map. -/
private theorem twistedTransfer_eigen_of_virtualUnitary
    (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ)
    (hNorm : transferMap A 1 = 1)
    (hV : V * Vᴴ = 1)
    (hC1μ : ∀ i : Fin d,
      ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ)) :
    twistedTransferMap A u V = μ • V := by
  have hV' : Vᴴ * V = 1 := by
    simpa using (mul_eq_one_comm.mp hV)
  calc
    twistedTransferMap A u V
        = ∑ i : Fin d, (∑ j : Fin d, u i j • A j) * V * (A i)ᴴ := by
            rw [twistedTransferMap_apply, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            simp [Finset.sum_mul, Matrix.mul_assoc]
    _ = ∑ i : Fin d, (μ • (V * A i * Vᴴ)) * V * (A i)ᴴ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hC1μ i]
    _ = μ • ∑ i : Fin d, V * A i * (A i)ᴴ := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          calc
            (μ • (V * A i * Vᴴ)) * V * (A i)ᴴ
                = μ • (((V * A i * Vᴴ) * V) * (A i)ᴴ) := by
                    simp [Matrix.mul_assoc]
            _ = μ • ((V * A i * (Vᴴ * V)) * (A i)ᴴ) := by
                    simp [Matrix.mul_assoc]
            _ = μ • ((V * A i) * (A i)ᴴ) := by
                    simp [hV', Matrix.mul_assoc]
            _ = μ • (V * A i * (A i)ᴴ) := by
                    simp [Matrix.mul_assoc]
    _ = μ • (V * ∑ i : Fin d, A i * (A i)ᴴ) := by
          simp [Matrix.mul_assoc, Matrix.mul_sum]
    _ = μ • (V * transferMap A 1) := by
          simp [transferMap_apply]
    _ = μ • V := by
          simp [hNorm]

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

/-- A phased virtual symmetry preserving the twisted transfer data also preserves
the stationary boundary state `Λ`, provided `Λ` is the unique fixed point of the
adjoint transfer channel. This is the paper's `V† Λ V = Λ` conclusion from
Lemma 1. -/
private theorem boundaryState_invariant_of_virtualUnitary
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (V : Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ)
    (hV : V * Vᴴ = 1) (hV' : Vᴴ * V = 1) (hμ : ‖μ‖ = 1)
    (hC1μ : ∀ i : Fin d,
      ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ)) :
    Vᴴ * Λ * V = Λ := by
  rcases eq_or_ne D 0 with hD | hD
  · subst hD
    simp at hΛtr
  haveI : NeZero D := ⟨hD⟩
  let B : MPSTensor d D := twistedMixedCompanion A u
  have hμ_ne : μ ≠ 0 := by
    intro hμ0
    have : ‖μ‖ = 0 := by simp [hμ0]
    rw [hμ] at this
    norm_num at this
  have hμ_sq : star μ * μ = 1 := by
    have hsq : ‖μ‖ * ‖μ‖ = 1 := by
      nlinarith [hμ]
    have hsqR : Complex.normSq μ = 1 := by
      simpa [Complex.normSq_eq_norm_sq, sq] using hsq
    have hsq' : (Complex.normSq μ : ℂ) = 1 := by
      exact_mod_cast hsqR
    rw [Complex.normSq_eq_conj_mul_self] at hsq'
    simpa using hsq'
  have huc : uᴴ * u = 1 := mul_eq_one_comm.mp hu
  have hcoeff :
      ∀ k j : Fin d,
        ∑ i : Fin d, (starRingEnd ℂ) (u i k) * u i j = if k = j then 1 else 0 := by
    intro k j
    have hentry := congrFun (congrFun huc k) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hentry
  have hA_from_B :
      ∀ k : Fin d, A k = μ • (V * B k * Vᴴ) := by
    intro k
    calc
      A k = ∑ j : Fin d, (if k = j then 1 else 0) • A j := by simp
      _ = ∑ j : Fin d, (∑ i : Fin d, (starRingEnd ℂ) (u i k) * u i j) • A j := by
            simp [hcoeff]
      _ = ∑ j : Fin d, ∑ i : Fin d, ((starRingEnd ℂ) (u i k) * u i j) • A j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_smul]
      _ = ∑ i : Fin d, ∑ j : Fin d, ((starRingEnd ℂ) (u i k) * u i j) • A j := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin d, (starRingEnd ℂ) (u i k) • (∑ j : Fin d, u i j • A j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j _
            simp [smul_smul]
      _ = ∑ i : Fin d, (starRingEnd ℂ) (u i k) • (μ • (V * A i * Vᴴ)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hC1μ i]
      _ = μ • (V * B k * Vᴴ) := by
            simp [B, twistedMixedCompanion, smul_smul, mul_assoc,
              Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, mul_comm]
  have hB_eq :
      ∀ X : Matrix (Fin D) (Fin D) ℂ, transferMap B X = transferMap A X := by
    intro X
    simpa [B] using transferMap_twistedMixedCompanion_eq (A := A) (u := u) hu X
  have hBfix : transferMap (fun i => (B i)ᴴ) Λ = Λ := by
    calc
      transferMap (fun i => (B i)ᴴ) Λ
          = transferMap (fun i => (A i)ᴴ) Λ := by
              simpa [transferMap_apply, Matrix.mul_assoc] using
                kraus_dual_eq_of_map_eq B A
                  (fun X => by simpa [transferMap_apply] using hB_eq X) Λ
      _ = Λ := hΛfix
  let ρ : Matrix (Fin D) (Fin D) ℂ := V * Λ * Vᴴ
  have hρ_psd : ρ.PosSemidef := by
    simpa [ρ, Matrix.mul_assoc] using hΛpos.posSemidef.mul_mul_conjTranspose_same (B := V)
  have hρ_fix : transferMap (fun i => (A i)ᴴ) ρ = ρ := by
    calc
      transferMap (fun i => (A i)ᴴ) ρ
          = ∑ i : Fin d, (A i)ᴴ * ρ * A i := by
              simp [transferMap_apply]
      _ = ∑ i : Fin d, V * ((B i)ᴴ * Λ * B i) * Vᴴ := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              (A i)ᴴ * ρ * A i
                  = ((μ • (V * B i * Vᴴ))ᴴ) * ρ * (μ • (V * B i * Vᴴ)) := by
                      rw [hA_from_B i]
              _ = (star μ * μ) • (((V * B i * Vᴴ)ᴴ) * ρ * (V * B i * Vᴴ)) := by
                    simp [Matrix.conjTranspose_smul, smul_smul, Matrix.mul_assoc, mul_comm]
              _ = (star μ * μ) • (V * ((B i)ᴴ * Λ * B i) * Vᴴ) := by
                    congr 1
                    calc
                      ((V * B i * Vᴴ)ᴴ) * ρ * (V * B i * Vᴴ)
                          = (V * (B i)ᴴ * Vᴴ) * (V * Λ * Vᴴ) * (V * B i * Vᴴ) := by
                              simp [ρ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
                      _ = V * (B i)ᴴ * (Vᴴ * V) * Λ * (Vᴴ * V) * B i * Vᴴ := by
                            simp [Matrix.mul_assoc]
                      _ = V * (B i)ᴴ * Λ * B i * Vᴴ := by simp [hV', Matrix.mul_assoc]
                      _ = V * ((B i)ᴴ * Λ * B i) * Vᴴ := by simp [Matrix.mul_assoc]
              _ = V * ((B i)ᴴ * Λ * B i) * Vᴴ := by
                    rw [hμ_sq, one_smul]
      _ = V * (∑ i : Fin d, (B i)ᴴ * Λ * B i) * Vᴴ := by
            simpa using
              (Matrix.sum_mul_mul
                (L := V) (M := fun i : Fin d => (B i)ᴴ * Λ * B i) (R := Vᴴ))
      _ = V * transferMap (fun i => (B i)ᴴ) Λ * Vᴴ := by
            simp [transferMap_apply]
      _ = ρ := by simp [ρ, hBfix, Matrix.mul_assoc]
  have hρ_tr : Matrix.trace ρ = 1 := by
    calc
      Matrix.trace ρ = Matrix.trace (V * Λ * Vᴴ) := rfl
      _ = Matrix.trace (Vᴴ * (V * Λ)) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle V Λ Vᴴ
      _ = Matrix.trace ((Vᴴ * V) * Λ) := by simp [Matrix.mul_assoc]
      _ = 1 := by simpa [hV'] using hΛtr
  have hρ_ne : ρ ≠ 0 := by
    intro hρ0
    simp [hρ0] at hρ_tr
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    injective_implies_irreducibleCP A hA
  have hIrrTensor : IsIrreducibleTensor (d := d) (D := D) A :=
    isIrreducibleTensor_of_isIrreducibleMap A hIrrA
  have hIrrAdj :
      IsIrreducibleMap (transferMap (d := d) (D := D) fun i => (A i)ᴴ) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor A hIrrTensor
  have hΛ_ne : Λ ≠ 0 := by
    intro hΛ0
    simp [hΛ0] at hΛtr
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := fun i => (A i)ᴴ) hIrrAdj
      Λ ρ hΛpos.posSemidef hΛ_ne hρ_psd hΛfix hρ_fix with ⟨c, hρ_scalar⟩
  have hc : c = 1 := by
    rw [hρ_scalar, Matrix.trace_smul, hΛtr] at hρ_tr
    simpa using hρ_tr
  have hρ_eq : ρ = Λ := by simpa [hc] using hρ_scalar
  calc
    Vᴴ * Λ * V = Vᴴ * ρ * V := by
      simpa [Matrix.mul_assoc] using congrArg (fun M => Vᴴ * M * V) hρ_eq.symm
    _ = Vᴴ * (V * (Λ * (Vᴴ * V))) := by simp [ρ, Matrix.mul_assoc]
    _ = Vᴴ * (V * Λ) := by simp [hV']
    _ = (Vᴴ * V) * Λ := by simp [Matrix.mul_assoc]
    _ = Λ := by simp [hV']

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
