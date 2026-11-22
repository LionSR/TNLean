/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedInteractionKernel
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedInteractionWindow
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.PositiveFunctionalCommutator
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.PrimitiveQuasiLocalUniqueness
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalOpenInteractionExpectation
import TNLean.QCA.BlockingStateTransport
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedQuasiLocalFace
import TNLean.MPS.ParentHamiltonian.Blocking.EventualKernelGroundStateSupport
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalEventualKernelGap

/-!
# Infinite-volume commutator gaps under blocking

Let a positive finite-range interaction have zero expectation under every
translate of a positive functional. Its commutator energies are nonnegative.
If a coarse interaction is the original open Hamiltonian on \(KL\) sites,
positive comparison bounds its commutator energy by \(KL+1-R\) times the
original energy. Consequently a supplied coarse gap \(\gamma\) gives an
original gap \(\gamma/(KL+1-R)\).

Every original finite interval observable has a blocked interval
representation, including intervals with negative or unaligned endpoints.
The proof uses locality and positivity; it imposes no translation-invariance
condition and no prescribed local parent kernel.

These are general transport statements for the blocking identification,
used in Nachtergaele, arXiv:cond-mat/9410110, Section 6,
lines 2649--2675. They do not assert the existence of a gap for a particular
interaction or state.

## Pure-state commutator gaps from an exact blocked primitive presentation

Suppose that every boundary-condition space of a tensor blocked by a positive
length is exactly the joint space of an inequivalent primitive family with
faithful invariant matrices. For a positive finite-range interaction with the
original boundary spaces as its eventual open-chain kernels, one positive
constant bounds the literal infinite-volume commutator energy in every pure
zero-energy state and for every centered local observable.

The interaction is grouped into a sufficiently long coarse interval. Its
primitive-sector gap transfers to the original lattice by positive comparison.
The support classification identifies every pure zero-energy state with a
transported sector. Translation invariance of a competing state is unnecessary.
The primitive family may be empty, in which case the state face is empty.

**Scope restriction (exact blocked primitive presentation):** The finite-space
representation is supplied here. Its derivation from periodic tensor data is
separate, as is identification of a general GVBS construction with these tensor
boundary spaces. See
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
No finite-volume gap in unaligned residue classes is asserted.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
the site grouping at lines 825--836, and Section 6, lines 2649--2675.
-/

section

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open SpinChain
open Kraus (blockPhysDim)
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d L : ℕ} [NeZero d] [NeZero L]
/-- Blocking transports each finite-volume commutator energy
by the interval coordinate isomorphism. -/
private theorem blocking_interval_commutator_eq
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (a : ℤ) (N : ℕ)
    (H X : Matrix (Cfg (blockPhysDim d L) N) (Cfg (blockPhysDim d L) N) ℂ) :
    (quasiLocalBlockingFunctional d L).symm φ
      (quasiLocalIntervalObservable (blockPhysDim d L) a N
        (Xᴴ * (H * X - X * H))) =
    φ (quasiLocalIntervalObservable d (a * L) (N * L)
      ((Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L) X)ᴴ *
        (Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L) H *
          Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L) X -
          Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L) X *
            Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L) H))) := by
  change φ (quasiLocalBlocking d L
    (quasiLocalIntervalObservable (blockPhysDim d L) a N
      (Xᴴ * (H * X - X * H)))) = _
  rw [quasiLocalBlocking_quasiLocalIntervalObservable]
  apply congrArg (fun Z => φ (quasiLocalIntervalObservable d (a * L) (N * L) Z))
  change (Matrix.reindexAlgEquiv ℂ ℂ (blockedConfigEquiv d N L))
      (Xᴴ * (H * X - X * H)) =
    ((Matrix.reindexAlgEquiv ℂ ℂ (blockedConfigEquiv d N L)) X)ᴴ *
      ((Matrix.reindexAlgEquiv ℂ ℂ (blockedConfigEquiv d N L)) H *
          (Matrix.reindexAlgEquiv ℂ ℂ (blockedConfigEquiv d N L)) X -
        (Matrix.reindexAlgEquiv ℂ ℂ (blockedConfigEquiv d N L)) X *
          (Matrix.reindexAlgEquiv ℂ ℂ (blockedConfigEquiv d N L)) H)
  simp only [map_mul, map_sub]
  rfl
/-- Equal quasi-local interval observables have equal stabilized commutator energies.
This is a consequence of finite-range locality; no state is required.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem localCommutatorObservable_eq_of_quasiLocalIntervalObservable_eq
    {R k t : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hR : 0 < R) (a b : ℤ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (Y : Matrix (Cfg d t) (Cfg d t) ℂ)
    (hXY : quasiLocalIntervalObservable d a k X = quasiLocalIntervalObservable d b t Y) :
    quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X) =
      quasiLocalIntervalObservable d (b - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + t) + (R - 1)) (localCommutatorObservable h Y) := by
  let c := min a b - ((R - 1 : ℕ) : ℤ)
  let e := max (a + (k : ℤ)) (b + (t : ℤ)) + ((R - 1 : ℕ) : ℤ)
  let ℓa := (a - c).toNat
  let ra := (e - (a + (k : ℤ))).toNat
  let ℓb := (b - c).toNat
  let rb := (e - (b + (t : ℤ))).toNat
  have hmin₁ := min_le_left a b
  have hmin₂ := min_le_right a b
  have hmax₁ := le_max_left (a + (k : ℤ)) (b + (t : ℤ))
  have hmax₂ := le_max_right (a + (k : ℤ)) (b + (t : ℤ))
  have ha : a - (ℓa : ℤ) = c := by dsimp [ℓa, c]; omega
  have hb : b - (ℓb : ℤ) = c := by dsimp [ℓb, c]; omega
  have hlen : (ℓa + k) + ra = (ℓb + t) + rb := by
    dsimp [ℓa, ℓb, ra, rb, c, e]; omega
  have hℓa : R - 1 ≤ ℓa := by dsimp [ℓa, c]; omega
  have hra : R - 1 ≤ ra := by dsimp [ra, e]; omega
  have hℓb : R - 1 ≤ ℓb := by dsimp [ℓb, c]; omega
  have hrb : R - 1 ≤ rb := by dsimp [rb, e]; omega
  have hA := quasiLocalIntervalObservable_commutator_locality a h X hR hℓa hra
  have hB := quasiLocalIntervalObservable_commutator_locality b h Y hR hℓb hrb
  rw [ha, hlen, hXY] at hA
  rw [hb] at hB
  exact hA.symm.trans hB
/-- A positive functional annihilating every translated interaction has real, nonnegative
local commutator energy. Normalization and translation invariance are unnecessary.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem quasiLocalIntervalObservable_localCommutatorObservable_nonneg
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hpos : ∀ Z, 0 ≤ φ (star Z * Z))
    {R k : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : h.PosSemidef)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    0 ≤ φ (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
      ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)) := by
  let f := intervalStateFunctional φ hpos (a - ((R - 1 : ℕ) : ℤ))
    ((R - 1 + k) + (R - 1))
  let H := (chainTranslates R ((R - 1 + k) + (R - 1)) h).hamiltonian
  let Z := bulkObservable X (R - 1) (R - 1)
  have hH : H.PosSemidef := hamiltonian_chainTranslates_posSemidef h hh _
  have hz : f H = 0 :=
    apply_quasiLocalIntervalObservable_hamiltonian_chainTranslates_eq_zero φ.toLinearMap h
      hzero (a - ((R - 1 : ℕ) : ℤ)) ((R - 1 + k) + (R - 1))
  change 0 ≤ f (Zᴴ * (H * Z - Z * H))
  rw [PositiveLinearMap.apply_conjTranspose_commutator_eq f H Z hH hz]
  exact f.map_nonneg (hH.conjTranspose_mul_mul_same Z).nonneg
/-- The blocked commutator energy is bounded by the original energy times the number
of original interaction terms in one coarse interaction. The covering condition is
explicit; no local-kernel condition is imposed.
Source: the positive-comparison argument in Nachtergaele,
arXiv:cond-mat/9410110, Section 6. -/
theorem blocking_localCommutator_energy_le
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hpos : ∀ Z, 0 ≤ φ (star Z * Z))
    {R K : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R)
    (hh : h.PosSemidef) (hK : 0 < K) (hcover : R + L ≤ K * L + 1)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (a : ℤ) {k : ℕ}
    (Y : Matrix (Cfg (blockPhysDim d L) k) (Cfg (blockPhysDim d L) k) ℂ) :
    (quasiLocalBlockingFunctional d L).symm φ
      (quasiLocalIntervalObservable (blockPhysDim d L) (a - ((K - 1 : ℕ) : ℤ))
        ((K - 1 + k) + (K - 1))
        (localCommutatorObservable (blockedInteractionMatrix h L K) Y)) ≤
    ((K * L + 1 - R : ℕ) : ℂ) *
      φ (quasiLocalIntervalObservable d (a * L - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k * L) + (R - 1))
        (localCommutatorObservable h
          (Matrix.reindex (blockedConfigEquiv d k L) (blockedConfigEquiv d k L) Y))) := by
  let n := K + R
  let N := (n + k) + n
  let f := intervalStateFunctional φ hpos ((a - (n : ℤ)) * L) (N * L)
  let Z := Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
    (bulkObservable Y n n)
  let H := (chainTranslates R (N * L) h).hamiltonian
  let C := Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
    ((chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian)
  have hKN : K ≤ N := by dsimp [N, n]; omega
  have hH : H.PosSemidef := hamiltonian_chainTranslates_posSemidef h hh (N * L)
  have hC : C.PosSemidef :=
    (hamiltonian_chainTranslates_posSemidef (blockedInteractionMatrix h L K)
      (blockedInteractionMatrix_posSemidef h hh L K) N).submatrix
        (blockedConfigEquiv d N L).symm
  have hfH : f H = 0 :=
    apply_quasiLocalIntervalObservable_hamiltonian_chainTranslates_eq_zero
      φ.toLinearMap h hzero ((a - (n : ℤ)) * L) (N * L)
  have hBound := (hamiltonian_chainTranslates_blockedInteractionMatrix_comparison
    h hh hKN hcover).2
  have hEnergy := PositiveLinearMap.apply_conjTranspose_commutator_le
    f C H Z hC hH hfH ((K * L + 1 - R : ℕ) : ℝ) (by simpa [C, H] using hBound)
  have hLeft : f (Zᴴ * (C * Z - Z * C)) =
      (quasiLocalBlockingFunctional d L).symm φ
        (quasiLocalIntervalObservable (blockPhysDim d L)
          (a - ((K - 1 : ℕ) : ℤ)) ((K - 1 + k) + (K - 1))
          (localCommutatorObservable (blockedInteractionMatrix h L K) Y)) := by
    rw [show f (Zᴴ * (C * Z - Z * C)) =
      (quasiLocalBlockingFunctional d L).symm φ
        (quasiLocalIntervalObservable (blockPhysDim d L) (a - (n : ℤ)) N
          ((bulkObservable Y n n)ᴴ *
            ((chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian *
              bulkObservable Y n n - bulkObservable Y n n *
                (chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian))) from
      (blocking_interval_commutator_eq φ (a - (n : ℤ)) N
        ((chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian)
        (bulkObservable Y n n)).symm]
    rw [quasiLocalIntervalObservable_bulkObservable_commutator a
      (blockedInteractionMatrix h L K) Y hK
      (show K - 1 ≤ n by dsimp [n]; omega)
      (show K - 1 ≤ n by dsimp [n]; omega)]
  let X := Matrix.reindex (blockedConfigEquiv d k L) (blockedConfigEquiv d k L) Y
  have hZ : quasiLocalIntervalObservable d ((a - (n : ℤ)) * L) (N * L) Z =
      quasiLocalIntervalObservable d (a * L) (k * L) X := by
    rw [show quasiLocalIntervalObservable d ((a - (n : ℤ)) * L) (N * L) Z =
      quasiLocalBlocking d L
        (quasiLocalIntervalObservable (blockPhysDim d L) (a - (n : ℤ)) N
          (bulkObservable Y n n)) from
      (quasiLocalBlocking_quasiLocalIntervalObservable d L (a - (n : ℤ)) N
        (bulkObservable Y n n)).symm]
    rw [quasiLocalIntervalObservable_bulkObservable a Y n n]
    exact quasiLocalBlocking_quasiLocalIntervalObservable d L a k Y
  have hMargin : R - 1 ≤ n * L := by
    have hL := NeZero.pos L
    have hn : R ≤ n := by dsimp [n]; omega
    exact le_trans (Nat.sub_le R 1) (le_trans hn (Nat.le_mul_of_pos_right n hL))
  have hRight : f (Zᴴ * (H * Z - Z * H)) =
      φ (quasiLocalIntervalObservable d (a * L - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k * L) + (R - 1)) (localCommutatorObservable h X)) := by
    change φ (quasiLocalIntervalObservable d ((a - (n : ℤ)) * L) (N * L)
      (Zᴴ * (H * Z - Z * H))) = _
    apply congrArg φ
    rw [← Matrix.star_eq_conjTranspose, map_mul, map_sub, map_mul, map_mul, map_star, hZ]
    have hLoc := quasiLocalIntervalObservable_commutator_locality (a * L) h X hR
      hMargin hMargin
    dsimp only [H, N]
    rw [Nat.add_mul, Nat.add_mul]
    simpa only [Nat.add_mul, Int.natCast_mul, Int.sub_mul] using hLoc
  rw [hLeft, hRight] at hEnergy
  simpa [X] using hEnergy
/-- A supplied gap for the inverse-blocked functional yields a gap for every original
local observable, with the counting factor lost from the constant. The functional
need not be translation invariant. Source: the blocking reduction in Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem quasiLocalCommutator_gap_of_blocking
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hpos : ∀ Z, 0 ≤ φ (star Z * Z))
    {R K : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R)
    (hh : h.PosSemidef) (hK : 0 < K) (hcover : R + L ≤ K * L + 1)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (γ : ℝ)
    (hgap : ∀ (a : ℤ) {k : ℕ}
      (Y : Matrix (Cfg (blockPhysDim d L) k) (Cfg (blockPhysDim d L) k) ℂ),
      0 < k → (quasiLocalBlockingFunctional d L).symm φ
        (quasiLocalIntervalObservable (blockPhysDim d L) a k Y) = 0 →
      γ * ((quasiLocalBlockingFunctional d L).symm φ
        (star (quasiLocalIntervalObservable (blockPhysDim d L) a k Y) *
          quasiLocalIntervalObservable (blockPhysDim d L) a k Y)).re ≤
        ((quasiLocalBlockingFunctional d L).symm φ
          (quasiLocalIntervalObservable (blockPhysDim d L) (a - ((K - 1 : ℕ) : ℤ))
            ((K - 1 + k) + (K - 1))
            (localCommutatorObservable (blockedInteractionMatrix h L K) Y))).re) :
    ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
      (γ / (K * L + 1 - R : ℕ)) *
        (φ (star (quasiLocalIntervalObservable d a k X) *
          quasiLocalIntervalObservable d a k X)).re ≤
        (φ (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
          ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X))).re := by
  intro a k X hk hcenter
  obtain ⟨b, t, ht, Y, hY⟩ := exists_blocked_quasiLocalIntervalObservable (L := L) a X hk
  have hCenter : (quasiLocalBlockingFunctional d L).symm φ
      (quasiLocalIntervalObservable (blockPhysDim d L) b t Y) = 0 := by
    change φ (quasiLocalBlocking d L
      (quasiLocalIntervalObservable (blockPhysDim d L) b t Y)) = 0
    rw [hY]
    exact hcenter
  have hVariance : (quasiLocalBlockingFunctional d L).symm φ
      (star (quasiLocalIntervalObservable (blockPhysDim d L) b t Y) *
        quasiLocalIntervalObservable (blockPhysDim d L) b t Y) =
      φ (star (quasiLocalIntervalObservable d a k X) *
        quasiLocalIntervalObservable d a k X) := by
    change φ (quasiLocalBlocking d L (star _ * _)) = _
    rw [map_mul, map_star, hY]
  have hGap := hgap b Y ht hCenter
  rw [hVariance] at hGap
  have hEnergy := blocking_localCommutator_energy_le φ hpos h hR hh hK hcover hzero b Y
  have hDecoded : quasiLocalIntervalObservable d (b * L) (t * L)
      (Matrix.reindex (blockedConfigEquiv d t L) (blockedConfigEquiv d t L) Y) =
      quasiLocalIntervalObservable d a k X := by
    rw [← quasiLocalBlocking_quasiLocalIntervalObservable d L b t Y]
    exact hY
  have hEnergyEq := localCommutatorObservable_eq_of_quasiLocalIntervalObservable_eq
    h hR (b * L) a
    (Matrix.reindex (blockedConfigEquiv d t L) (blockedConfigEquiv d t L) Y) X hDecoded
  rw [hEnergyEq] at hEnergy
  have hEnergyRe := (Complex.le_def.mp hEnergy).1
  have hM : 0 < ((K * L + 1 - R : ℕ) : ℝ) := by
    have hL := NeZero.pos L
    exact_mod_cast (show 0 < K * L + 1 - R by omega)
  have hReal :
      ((quasiLocalBlockingFunctional d L).symm φ
        (quasiLocalIntervalObservable (blockPhysDim d L) (b - ((K - 1 : ℕ) : ℤ))
          ((K - 1 + t) + (K - 1))
          (localCommutatorObservable (blockedInteractionMatrix h L K) Y))).re ≤
      ((K * L + 1 - R : ℕ) : ℝ) *
        (φ (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
          ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X))).re := by
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] using hEnergyRe
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hM).2
  simpa only [mul_comm] using hGap.trans hReal
/-- The transported gap bounds the literal infinite-volume commutator-energy limit
for every original local observable. Both interval margins may diverge along an
arbitrary filter. Source: Nachtergaele, arXiv:cond-mat/9410110,
Section 6, lines 2649--2675. -/
theorem quasiLocalCommutator_limit_gap_of_blocking
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hpos : ∀ Z, 0 ≤ φ (star Z * Z))
    {R K : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R)
    (hh : h.PosSemidef) (hK : 0 < K) (hcover : R + L ≤ K * L + 1)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (γ : ℝ)
    (hgap : ∀ (a : ℤ) {k : ℕ}
      (Y : Matrix (Cfg (blockPhysDim d L) k) (Cfg (blockPhysDim d L) k) ℂ),
      0 < k → (quasiLocalBlockingFunctional d L).symm φ
        (quasiLocalIntervalObservable (blockPhysDim d L) a k Y) = 0 →
      γ * ((quasiLocalBlockingFunctional d L).symm φ
        (star (quasiLocalIntervalObservable (blockPhysDim d L) a k Y) *
          quasiLocalIntervalObservable (blockPhysDim d L) a k Y)).re ≤
        ((quasiLocalBlockingFunctional d L).symm φ
          (quasiLocalIntervalObservable (blockPhysDim d L) (a - ((K - 1 : ℕ) : ℤ))
            ((K - 1 + k) + (K - 1))
            (localCommutatorObservable (blockedInteractionMatrix h L K) Y))).re)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Filter.Tendsto ℓ f Filter.atTop) (hr : Filter.Tendsto r f Filter.atTop) :
    ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
      ∃ e : ℂ, Filter.Tendsto (fun n => φ
        (star (quasiLocalIntervalObservable d a k X) *
          (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
              ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
            quasiLocalIntervalObservable d a k X -
            quasiLocalIntervalObservable d a k X *
              quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
        ((γ / (K * L + 1 - R : ℕ) : ℝ) : ℂ) *
          φ (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X) ≤ e := by
  intro a k X hk hcenter
  refine ⟨φ (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
    ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)), ?_, ?_⟩
  · exact tendsto_apply_quasiLocalIntervalObservable_commutator φ a h X hR hℓ hr
  · rw [Complex.le_def]
    constructor
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
        quasiLocalCommutator_gap_of_blocking φ hpos h hR hh hK hcover hzero γ hgap a X hk hcenter
    · have hsquareIm := (Complex.nonneg_iff.mp
        (hpos (quasiLocalIntervalObservable d a k X))).2
      have henergyIm := (Complex.nonneg_iff.mp
        (quasiLocalIntervalObservable_localCommutatorObservable_nonneg
          φ hpos h hh hzero a X)).2
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        ← hsquareIm, ← henergyIm, mul_zero, zero_mul, add_zero]
end MPSTensor

end

section

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
open Kraus (blockPhysDim blockTensor)
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d D L R b : ℕ} [NeZero d] [NeZero L]
  {E : Fin b → ℕ} [∀ j, NeZero (E j)]
/-- An exact blocked primitive presentation and the eventual original kernel
identity give one positive literal commutator gap for all pure zero-energy
states on the original chain. The interaction range is arbitrary and positive,
and both interval margins may diverge along any filter.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675. -/
theorem exists_pos_quasiLocalCommutator_limit_gap_of_blocked_primitive_family
    (A : MPSTensor d D) (μ : Fin b → ℂ)
    (B : ∀ j, MPSTensor (blockPhysDim d L) (E j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (E j)) (Fin (E j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : E j = E i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hJoint : ∀ N, groundSpaceES (blockTensor A L) N =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        groundSpaceES A N) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
        ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
          ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
            Tendsto ℓ f atTop → Tendsto r f atTop →
          ∃ e : ℂ, Tendsto (fun n => φ
            (star (quasiLocalIntervalObservable d a k X) *
              (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                  ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    ((chainTranslates R ((ℓ n + k) + r n) h).hamiltonian)))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  let K := R + L
  have hK : 0 < K := by dsimp [K]; omega
  have hcover : R + L ≤ K * L + 1 :=
    (Nat.le_mul_of_pos_right (R + L) (NeZero.pos L)).trans (Nat.le_succ _)
  have hkerB : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (Matrix.toEuclideanLin
        (chainTranslates K N (blockedInteractionMatrix h L K)).hamiltonian) =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N :=
    (eventually_ker_hamiltonian_chainTranslates_blockedInteractionMatrix_eq_groundSpaceES
      A h hh hcover hker).mono fun N hN => hN.trans (hJoint N)
  obtain ⟨γ, hγ, _hFinite, hGap⟩ :=
    exists_pos_multiblock_quasiLocalCommutator_gap_of_eventual_kernel
      μ B hμ ρ hP hρ hDistinct hK (blockedInteractionMatrix h L K)
      (blockedInteractionMatrix_posSemidef h hh L K) hkerB
  have hM : 0 < ((K * L + 1 - R : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt
      ((Nat.lt_add_of_pos_right (NeZero.pos L)).trans_le hcover)
  refine ⟨γ / (K * L + 1 - R : ℕ), div_pos hγ hM, ?_⟩
  intro φ hφ hφPure
  have hSupport := (mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
    A h hR hh hker φ).mp hφ
  obtain ⟨j, hφj⟩ :=
    (isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
      A μ B hμ ρ hP hρ hDistinct hJoint φ hφ.1).mp ⟨hSupport.2, hφPure⟩
  have hInv : (quasiLocalBlockingFunctional d L).symm φ =
      quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
    rw [hφj]
    exact (quasiLocalBlockingFunctional d L).symm_apply_apply _
  intro a k X hk hcenter ι f ℓ r hℓ hr
  apply quasiLocalCommutator_limit_gap_of_blocking φ hφ.1.2.2 h hR hh hK hcover hφ.2 γ
    (fun a' k' Y hk' hcenter' => ?_) hℓ hr a X hk hcenter
  simpa only [hInv] using hGap j a' Y hk' (by simpa only [hInv] using hcenter')
end MPSTensor

end
