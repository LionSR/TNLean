/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedInteractionKernel
import TNLean.MPS.ParentHamiltonian.BlockedLocalObservable
import TNLean.MPS.ParentHamiltonian.PositiveFunctionalCommutator
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalUniqueness
import TNLean.MPS.ParentHamiltonian.QuasiLocalOpenInteractionExpectation
import TNLean.QCA.BlockingStateTransport

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
-/

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open SpinChain
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
    (hk : 0 < k) (ht : 0 < t)
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
  have hA := quasiLocalIntervalObservable_commutator_locality a h X hR hk hℓa hra
  have hB := quasiLocalIntervalObservable_commutator_locality b h Y hR ht hℓb hrb
  rw [ha, hlen, hXY] at hA
  rw [hb] at hB
  exact hA.symm.trans hB
/-- A positive functional annihilating every translated interaction has real, nonnegative
local commutator energy. Normalization and translation invariance are unnecessary.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem quasiLocalIntervalObservable_localCommutatorObservable_nonneg
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hpos : ∀ Z, 0 ≤ φ (star Z * Z))
    {R k : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R)
    (hh : h.PosSemidef)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    0 ≤ φ (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
      ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)) := by
  let f := intervalStateFunctional φ hpos (a - ((R - 1 : ℕ) : ℤ))
    ((R - 1 + k) + (R - 1))
  let H := openInteractionMatrix h ((R - 1 + k) + (R - 1))
  let Z := bulkObservable X (R - 1) (R - 1)
  have hH : H.PosSemidef := openInteractionMatrix_posSemidef h hh hR _
  have hz : f H = 0 :=
    apply_quasiLocalIntervalObservable_openInteractionMatrix_eq_zero φ.toLinearMap h hR
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
    (Y : Matrix (Cfg (blockPhysDim d L) k) (Cfg (blockPhysDim d L) k) ℂ)
    (hk : 0 < k) :
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
  let H := openInteractionMatrix h (N * L)
  let C := Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
    (openInteractionMatrix (blockedInteractionMatrix h L K) N)
  have hKN : K ≤ N := by dsimp [N, n]; omega
  have hH : H.PosSemidef := openInteractionMatrix_posSemidef h hh hR (N * L)
  have hC : C.PosSemidef :=
    (openInteractionMatrix_posSemidef (blockedInteractionMatrix h L K)
      (blockedInteractionMatrix_posSemidef h hh hR L K) hK N).submatrix
        (blockedConfigEquiv d N L).symm
  have hfH : f H = 0 :=
    apply_quasiLocalIntervalObservable_openInteractionMatrix_eq_zero
      φ.toLinearMap h hR hzero ((a - (n : ℤ)) * L) (N * L)
  have hBound := (openInteractionMatrix_blockedInteractionMatrix_comparison
    h hh hR hK hKN hcover).2
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
            (openInteractionMatrix (blockedInteractionMatrix h L K) N *
              bulkObservable Y n n - bulkObservable Y n n *
                openInteractionMatrix (blockedInteractionMatrix h L K) N))) from
      (blocking_interval_commutator_eq φ (a - (n : ℤ)) N
        (openInteractionMatrix (blockedInteractionMatrix h L K) N)
        (bulkObservable Y n n)).symm]
    rw [quasiLocalIntervalObservable_bulkObservable_commutator a
      (blockedInteractionMatrix h L K) Y hK hk
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
      (Nat.mul_pos hk (NeZero.pos L)) hMargin hMargin
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
  have hEnergy := blocking_localCommutator_energy_le φ hpos h hR hh hK hcover hzero b Y ht
  have hDecoded : quasiLocalIntervalObservable d (b * L) (t * L)
      (Matrix.reindex (blockedConfigEquiv d t L) (blockedConfigEquiv d t L) Y) =
      quasiLocalIntervalObservable d a k X := by
    rw [← quasiLocalBlocking_quasiLocalIntervalObservable d L b t Y]
    exact hY
  have hEnergyEq := localCommutatorObservable_eq_of_quasiLocalIntervalObservable_eq
    h hR (b * L) a
    (Matrix.reindex (blockedConfigEquiv d t L) (blockedConfigEquiv d t L) Y) X
    (Nat.mul_pos ht (NeZero.pos L)) hk hDecoded
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
              (openInteractionMatrix h ((ℓ n + k) + r n)) *
            quasiLocalIntervalObservable d a k X -
            quasiLocalIntervalObservable d a k X *
              quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                (openInteractionMatrix h ((ℓ n + k) + r n))))) f (𝓝 e) ∧
        ((γ / (K * L + 1 - R : ℕ) : ℝ) : ℂ) *
          φ (star (quasiLocalIntervalObservable d a k X) *
            quasiLocalIntervalObservable d a k X) ≤ e := by
  intro a k X hk hcenter
  refine ⟨φ (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
    ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)), ?_, ?_⟩
  · exact tendsto_apply_quasiLocalIntervalObservable_commutator φ a h X hR hk hℓ hr
  · rw [Complex.le_def]
    constructor
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
        quasiLocalCommutator_gap_of_blocking φ hpos h hR hh hK hcover hzero γ hgap a X hk hcenter
    · have hsquareIm := (Complex.nonneg_iff.mp
        (hpos (quasiLocalIntervalObservable d a k X))).2
      have henergyIm := (Complex.nonneg_iff.mp
        (quasiLocalIntervalObservable_localCommutatorObservable_nonneg
          φ hpos h hR hh hzero a X)).2
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        ← hsquareIm, ← henergyIm, mul_zero, zero_mul, add_zero]
end MPSTensor
