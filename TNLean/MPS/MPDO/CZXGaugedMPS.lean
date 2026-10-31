/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import TNLean.MPS.Core.CyclicTraceForcedBond
import TNLean.MPS.MPDO.CZXGHZAction
import TNLean.MPS.MPDO.CZXGaussInvariantSubspace

/-!
# The gauged CZX matrix product state and its modified Gauss law

For the anomalous `ℤ₂` CZX example of arXiv:2502.20257, lines 5121--5183, the gauged tensor
`CZX_gaugedMPS` of the once-blocked GHZ state places one gauge matrix on the bond to the left of
every site: `𝟙` for the gauge label `e` and `[[0, 1], [-i, 0]]` for the gauge label `g`. Its
periodic vector is a vector on the chain whose sites carry one blocked matter index and one gauge
label.

The local symmetry representation `𝒢_g` of `eq:mcGCZX` is the local Gauss operator built from
the unmodified fusion operators `λ^R_{e,e} = λ^R_{e,g} = 𝟙`, `λ^R_{g,e} = w_R` and
`λ^R_{g,g} = λ`. This file proves the three claims of lines 5179--5183:

* the unmodified local Gauss operator does not fix the gauged state, at any window of any
  chain of at least two sites;
* after the modification `λ^R_{g,g} ↦ λ^R_{g,g} Z₁`, every placed modified Gauss operator, hence
  every placed modified Gauss projector, fixes the gauged state, which therefore lies in the
  gauge-invariant subspace of the modified fusion operators;
* the modified Gauss projectors on two neighbouring windows do not commute, on every chain of at
  least three sites.

The local representation property of the modified operators is
`TNLean.Algebra.gaussOperator_mul` for every tuple of unitaries.

The periodic vector of the gauged tensor is a product of nearest-neighbour factors, because the
incoming bond of every letter is forced by the letter
(`MPOTensor.CZX.gaugedMPS_eq_prod`); both Gauss operators are monomial, so each claim reduces to
an identity of these factors on one window, decided over the Gaussian integers.

## Main definitions

* `MPOTensor.CZX.gaugeLabelMatrix`: the gauge matrices of `CZX_gaugedMPS`.
* `MPOTensor.CZX.gaugedTensor`: the gauged tensor `CZX_gaugedMPS`.
* `MPOTensor.CZX.gaugedMPS`: its periodic vector on a chain of `N` sites.
* `MPOTensor.CZX.unmodifiedCircuitTuple`: the unmodified fusion operators of `eq:mcGCZX`.

## Main results

* `MPOTensor.CZX.unmodifiedPlacedGaussOperator_mulVec_gaugedMPS_ne`: `eq:mcGCZX` does not fix
  the gauged state.
* `MPOTensor.CZX.placedGaussOperator_mulVec_gaugedMPS`: the modified Gauss law fixes it.
* `MPOTensor.CZX.gaugedMPS_mem_gaugeInvariantSubspace`
* `MPOTensor.CZX.not_commute_placedGaussProjector`: neighbouring modified projectors do not
  commute.
-/

noncomputable section

open scoped BigOperators Matrix
open Matrix Complex

namespace MPOTensor.CZX

/-! ### The gauged tensor -/

/-- The gauge matrices of the gauged CZX tensor: the identity for the label `e` and
`[[0, 1], [-i, 0]]` for the label `g`.

Source: arXiv:2502.20257, `CZX_gaugedMPS`, `main.tex` lines 5129--5178. -/
def gaugeLabelMatrix (a : Multiplicative (ZMod 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  if Multiplicative.toAdd a = 0 then 1 else !![0, 1; -I, 0]

/-- The blocked matter index and the gauge label of one site of the gauged chain, in the
coordinates of `MPOTensor.gaugedVector`. -/
def gaugedSite : Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2))) ≃
    Fin 4 × Multiplicative (ZMod 2) :=
  (Fintype.equivFin _).symm

/-- **The gauged CZX tensor** `CZX_gaugedMPS`: the letter of a site with blocked matter index
`m` and gauge label `a` is the gauge matrix of `a`, on the bond to the left of the site, times
the letter `m` of the once-blocked GHZ tensor.

Source: arXiv:2502.20257, `CZX_gaugedMPS`, `main.tex` lines 5129--5178, an instance of
`eq:gauged_tensor_dw`. -/
def gaugedTensor : MPSTensor (Fintype.card (Fin 4 × Multiplicative (ZMod 2))) 2 :=
  fun s ↦ gaugeLabelMatrix (gaugedSite s).2 * blockedGHZTensor (gaugedSite s).1

/-- The periodic vector of the gauged CZX tensor on a chain of `N` sites. -/
def gaugedMPS (N : ℕ) : (Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) → ℂ :=
  fun σ ↦ MPSTensor.mpv gaugedTensor σ

/-- The matter state attached to a configuration `α` of gauge labels: the periodic GHZ state
with the gauge matrix of `α k` inserted on the bond to the left of the site `k`. -/
def gaugedDefectState {N : ℕ} (α : Fin N → Multiplicative (ZMod 2)) (m : Fin N → Fin 4) : ℂ :=
  (List.ofFn fun k ↦ gaugeLabelMatrix (α k) * blockedGHZTensor (m k)).prod.trace

private theorem evalWord_eq_prod_map {d D : ℕ} (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (w : List (Fin d)) : Kraus.evalWord K w = (w.map K).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [Kraus.evalWord_cons, ih, List.map_cons, List.prod_cons]

/-- **The gauged state is the gauged vector `∑_α Ψ_α ⊗ |α⟩`** of the matter states attached to
the gauge-label configurations, the form of the state-level gauging of `eq:gauged_tensor_dw`.

Source: arXiv:2502.20257, `eq:gauged_tensor_dw`, `main.tex` lines 3511--3530, and
`CZX_gaugedMPS`, lines 5129--5178. -/
theorem gaugedMPS_eq_gaugedVector (N : ℕ) :
    gaugedMPS N = gaugedVector 4 (Multiplicative (ZMod 2)) gaugedDefectState := by
  funext σ
  rw [gaugedMPS, MPSTensor.mpv, MPSTensor.coeff, evalWord_eq_prod_map, List.map_ofFn,
    gaugedVector_apply, gaugedDefectState]
  rfl

/-! ### Forced bonds -/

/-- The incoming bond forced by a site: the GHZ sector of the matter index, exchanged when the
gauge label is `g`. -/
def gaugedLeftBond (u : Fin 4 × Multiplicative (ZMod 2)) : Fin 2 :=
  if Multiplicative.toAdd u.2 = 0 then ((finProdFinEquiv (m := 2) (n := 2)).symm u.1).1
  else 1 - ((finProdFinEquiv (m := 2) (n := 2)).symm u.1).1

/-- The entry of a site at the outgoing bond `r`, over the Gaussian integers. -/
def gaugedBondWeightZ (u : Fin 4 × Multiplicative (ZMod 2)) (r : Fin 2) : GaussianInt :=
  if u.1 = finProdFinEquiv (r, r) then
    if Multiplicative.toAdd u.2 = 0 then 1 else if r = 0 then ⟨0, -1⟩ else 1
  else 0

/-- The nearest-neighbour factor of the gauged vector over the Gaussian integers: the entry of
the site `u` at the bond forced by its right neighbour `v`. -/
def gaugedBondFactorZ (u v : Fin 4 × Multiplicative (ZMod 2)) : GaussianInt :=
  gaugedBondWeightZ u (gaugedLeftBond v)

private theorem toComplex_neg_i : GaussianInt.toComplex ⟨0, -1⟩ = -I := by
  apply Complex.ext <;> simp [GaussianInt.toComplex_def]

private theorem gaugeLabelMatrix_mul_blockedGHZTensor_apply (u : Fin 4 × Multiplicative (ZMod 2))
    (l r : Fin 2) :
    (gaugeLabelMatrix u.2 * blockedGHZTensor u.1) l r = if l = gaugedLeftBond u then
      GaussianInt.toComplex (gaugedBondWeightZ u r) else 0 := by
  obtain ⟨m, a⟩ := u
  rw [blockedGHZTensor_apply, Matrix.mul_diagonal]
  rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
    fin_cases m <;> fin_cases l <;> fin_cases r <;>
    simp +decide [gaugeLabelMatrix, gaugedBondWeightZ, toComplex_neg_i]

theorem gaugedTensor_apply (s : Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2))))
    (l r : Fin 2) :
    gaugedTensor s l r = if l = gaugedLeftBond (gaugedSite s) then
      GaussianInt.toComplex (gaugedBondWeightZ (gaugedSite s) r) else 0 :=
  gaugeLabelMatrix_mul_blockedGHZTensor_apply (gaugedSite s) l r

/-- **The gauged vector as a product of nearest-neighbour factors.** -/
theorem gaugedMPS_eq_prod {N : ℕ} [NeZero N]
    (σ : Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) :
    gaugedMPS N σ = ∏ n, GaussianInt.toComplex
      (gaugedBondFactorZ (gaugedSite (σ n)) (gaugedSite (σ (n + 1)))) :=
  MPSTensor.mpv_of_forced_left_bond gaugedTensor_apply σ

/-! ### Replacing one window -/

/-- Shorthand for the physical index of the gauged chain. -/
local notation "Gs" => Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))

/-- **Replacing one window.** Replacing the window `(j, j + 1)` of a configuration changes the
product of nearest-neighbour factors only in the factor of the window and in the factor leaving
it, provided that the incoming bond forced at the site `j` is unchanged. -/
theorem gaugedMPS_replaceWindow {N : ℕ} [NeZero N] (hN : 2 ≤ N) (j : Fin N) (s : Fin N → Gs)
    (u : Fin 2 → Gs)
    (hu : gaugedLeftBond (gaugedSite (u 0)) = gaugedLeftBond (gaugedSite (s j))) :
    ∃ R : ℂ,
      gaugedMPS N (MPSTensor.replaceWindow 2 hN j s u) =
        GaussianInt.toComplex (gaugedBondFactorZ (gaugedSite (u 0)) (gaugedSite (u 1)) *
          gaugedBondWeightZ (gaugedSite (u 1)) (gaugedLeftBond (gaugedSite (s (j + 1 + 1))))) *
          R ∧
      gaugedMPS N s =
        GaussianInt.toComplex (gaugedBondFactorZ (gaugedSite (s j)) (gaugedSite (s (j + 1))) *
          gaugedBondWeightZ (gaugedSite (s (j + 1)))
            (gaugedLeftBond (gaugedSite (s (j + 1 + 1))))) * R := by
  have hj1 : j + 1 ≠ j := succ_ne_self hN j
  have hj21 : j + 1 + 1 ≠ j + 1 := succ_ne_self hN (j + 1)
  set t := MPSTensor.replaceWindow 2 hN j s u with htdef
  have ht : ∀ k, t k = if k = j then u 0 else if k = j + 1 then u 1 else s k :=
    fun k ↦ replaceWindow_two_apply hN j s u k
  have ht0 : t j = u 0 := by rw [ht, ite_eq_left rfl]
  have ht1 : t (j + 1) = u 1 := by rw [ht, ite_eq_right hj1, ite_eq_left rfl]
  have hbond : ∀ k, k ≠ j + 1 →
      gaugedLeftBond (gaugedSite (t k)) = gaugedLeftBond (gaugedSite (s k)) := by
    intro k hk
    by_cases hkj : k = j
    · rw [hkj, ht0, hu]
    · rw [ht k, ite_eq_right hkj, ite_eq_right hk]
  let f : (Fin N → Gs) → Fin N → ℂ := fun σ n ↦
    GaussianInt.toComplex (gaugedBondFactorZ (gaugedSite (σ n)) (gaugedSite (σ (n + 1))))
  have hsplit : ∀ σ, ∏ n, f σ n =
      f σ j * f σ (j + 1) * ∏ n ∈ (Finset.univ.erase j).erase (j + 1), f σ n := by
    intro σ
    rw [← Finset.mul_prod_erase Finset.univ (f σ) (Finset.mem_univ j),
      ← Finset.mul_prod_erase (Finset.univ.erase j) (f σ)
        (Finset.mem_erase.mpr ⟨hj1, Finset.mem_univ _⟩), mul_assoc]
  have hrest : ∏ n ∈ (Finset.univ.erase j).erase (j + 1), f t n =
      ∏ n ∈ (Finset.univ.erase j).erase (j + 1), f s n := by
    refine Finset.prod_congr rfl fun n hn ↦ ?_
    have hn1 : n ≠ j + 1 := Finset.ne_of_mem_erase hn
    have hn0 : n ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hn)
    have hnn : n + 1 ≠ j + 1 := fun h ↦ hn0 (add_right_cancel h)
    simp only [f, gaugedBondFactorZ]
    rw [ht n, ite_eq_right hn0, ite_eq_right hn1, hbond (n + 1) hnn]
  refine ⟨∏ n ∈ (Finset.univ.erase j).erase (j + 1), f s n, ?_, ?_⟩
  · rw [gaugedMPS_eq_prod]
    change ∏ n, f t n = _
    rw [hsplit, hrest]
    simp only [f, gaugedBondFactorZ, map_mul]
    rw [ht0, ht1, hbond (j + 1 + 1) hj21]
  · rw [gaugedMPS_eq_prod]
    change ∏ n, f s n = _
    rw [hsplit]
    simp only [f, gaugedBondFactorZ, map_mul]

/-! ### The modified Gauss law -/

/-- The powers of the Gaussian integer `i` indexed by exponents modulo four. -/
def iPowZ (q : ZMod 4) : GaussianInt :=
  ⟨0, 1⟩ ^ q.val

theorem toComplex_iPowZ (q : ZMod 4) : GaussianInt.toComplex (iPowZ q) = iPow q := by
  have hI : GaussianInt.toComplex ⟨0, 1⟩ = I := by
    apply Complex.ext <;> simp [GaussianInt.toComplex_def]
  rw [iPowZ, map_pow, hI, iPow]

/-- The image of one window under the modified local Gauss operator of the generator, in the
matter indices and gauge labels of its two sites: the matter bits of the first site are
complemented and the two gauge labels are moved by the Gauss leg action. -/
def gaussWindowImage (x y : Fin 4 × Multiplicative (ZMod 2)) :
    (Fin 4 × Multiplicative (ZMod 2)) × (Fin 4 × Multiplicative (ZMod 2)) :=
  ((matterBarFlip ![x.1, y.1] 0, x.2 * gen⁻¹), (matterBarFlip ![x.1, y.1] 1, gen * y.2))

private theorem windowCoordinates_symm_gaugedSite (x y : Fin 4 × Multiplicative (ZMod 2)) :
    windowCoordinates.symm ![gaugedSite.symm x, gaugedSite.symm y] =
      (![x.1, y.1], (x.2, y.2)) := by
  rw [Equiv.symm_apply_eq]
  funext k
  fin_cases k <;> simp [windowCoordinates, gaugedSite]

private theorem localPerm_gaugedSite_window (x y : Fin 4 × Multiplicative (ZMod 2)) :
    (windowCoordinates.symm.trans (localPerm.trans windowCoordinates))
        ![gaugedSite.symm x, gaugedSite.symm y] =
      ![gaugedSite.symm (gaussWindowImage x y).1, gaugedSite.symm (gaussWindowImage x y).2] := by
  rw [Equiv.trans_apply, Equiv.trans_apply, windowCoordinates_symm_gaugedSite]
  funext k
  fin_cases k <;> simp [windowCoordinates, gaugedSite, localPerm, gaussWindowImage,
    TNLean.Algebra.gaussLegAction_apply]

private theorem localPhase_gaugedSite_window (x y : Fin 4 × Multiplicative (ZMod 2)) :
    localPhase (windowCoordinates.symm ![gaugedSite.symm x, gaugedSite.symm y]) =
      iPow (phaseExponent (localBits ![x.1, y.1]) (Multiplicative.toAdd x.2)
        (Multiplicative.toAdd y.2)) := by
  rw [windowCoordinates_symm_gaugedSite, localPhase]

/-- The modified Gauss operator does not change the incoming bond forced at the first site of
its window. -/
private theorem gaugedLeftBond_gaussWindowImage (x y : Fin 4 × Multiplicative (ZMod 2)) :
    gaugedLeftBond (gaussWindowImage x y).1 = gaugedLeftBond x := by
  revert x y
  decide

/-- **The modified Gauss law on one window**, over the Gaussian integers: the factor of the
window and the factor leaving it acquire exactly the phase of the modified local Gauss
operator. -/
private theorem gaussWindowImage_bondFactor (x y : Fin 4 × Multiplicative (ZMod 2)) (b : Fin 2) :
    gaugedBondFactorZ (gaussWindowImage x y).1 (gaussWindowImage x y).2 *
        gaugedBondWeightZ (gaussWindowImage x y).2 b =
      iPowZ (phaseExponent (localBits ![x.1, y.1]) (Multiplicative.toAdd x.2)
        (Multiplicative.toAdd y.2)) * (gaugedBondFactorZ x y * gaugedBondWeightZ y b) := by
  revert x y b
  decide +kernel

/-- **The modified Gauss law fixes the gauged CZX state**: on every chain of at least two sites,
the modified local Gauss operator of the generator, with `λ^R_{g,g}` replaced by
`λ^R_{g,g} Z₁`, placed on any window fixes the periodic vector of `CZX_gaugedMPS`.

Source: arXiv:2502.20257, `main.tex` lines 5179--5183, with `CZX_gaugedMPS` at lines
5129--5178. -/
theorem placedGaussOperator_mulVec_gaugedMPS (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    placedGaussOperator N hN j *ᵥ gaugedMPS N = gaugedMPS N := by
  have : NeZero N := ⟨by omega⟩
  rw [placedGaussOperator_eq_monomial, monomial_mulVec_eq_self_iff]
  intro s
  rw [windowPerm_apply, extractWindow_two hN j s]
  set x := gaugedSite (s j)
  set y := gaugedSite (s (j + 1))
  have hw : ![s j, s (j + 1)] = ![gaugedSite.symm x, gaugedSite.symm y] := by simp [x, y]
  rw [hw, localPerm_gaugedSite_window, localPhase_gaugedSite_window]
  obtain ⟨R, h1, h2⟩ := gaugedMPS_replaceWindow hN j s
    ![gaugedSite.symm (gaussWindowImage x y).1, gaugedSite.symm (gaussWindowImage x y).2]
    (by simpa using gaugedLeftBond_gaussWindowImage x y)
  rw [h1, h2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Equiv.apply_symm_apply]
  rw [gaussWindowImage_bondFactor, map_mul, toComplex_iPowZ]
  ring

/-- The modified Gauss projectors fix the gauged CZX state, which therefore lies in the
gauge-invariant subspace of the modified fusion operators.

Source: arXiv:2502.20257, `main.tex` lines 5179--5183, with `eq:gauge_projs` at lines
3494--3499. -/
theorem gaugedMPS_mem_gaugeInvariantSubspace (N : ℕ) (hN : 2 ≤ N) :
    gaugedMPS N ∈ gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) N hN circuitTuple := by
  rw [gaugeInvariantSubspace, LinearMap.mem_commonFixedSubmodule_iff]
  intro j
  rw [mulVecLin_apply, placedGaussProjector_circuitTuple, inv_two_smul_add_mulVec_eq_iff]
  exact placedGaussOperator_mulVec_gaugedMPS N hN j

/-! ### The unmodified Gauss law -/

theorem lambda_mem_unitaryGroup :
    matterMatrix lambda ∈ Matrix.unitaryGroup (Fin 2 → Fin 4) ℂ := by
  rw [lambda_eq, matterMatrix_monomial]
  refine monomial_mem_unitaryGroup _ _ fun s ↦ ?_
  have hstar : star (-I * (-1 : ℂ) ^ (hExponent (localBits s)).val) =
      I * (-1) ^ (hExponent (localBits s)).val := by
    simp
  rw [Function.comp_apply, hstar]
  calc I * (-1 : ℂ) ^ (hExponent (localBits s)).val *
        (-I * (-1) ^ (hExponent (localBits s)).val)
      = -(I * I) * ((-1) ^ (hExponent (localBits s)).val *
          (-1) ^ (hExponent (localBits s)).val) := by ring
    _ = 1 := by
        rw [I_mul_I, ← mul_pow]
        simp

/-- **The unmodified fusion operators** of the CZX example:
`λ^R_{e,e} = λ^R_{e,g} = 𝟙`, `λ^R_{g,e} = w_R` and `λ^R_{g,g} = λ`. Their local Gauss operator
of the generator is `𝒢_g` of `eq:mcGCZX`.

Source: arXiv:2502.20257, `eq:mcGCZX`, `main.tex` lines 5121--5128, with the fusion operators
of lines 4989--5067. -/
def unmodifiedCircuitTuple (a b : Multiplicative (ZMod 2)) :
    Matrix.unitaryGroup (Fin 2 → Fin 4) ℂ :=
  if Multiplicative.toAdd a = 0 then 1
  else if Multiplicative.toAdd b = 0 then ⟨matterMatrix w, w_mem_unitaryGroup⟩
  else ⟨matterMatrix lambda, lambda_mem_unitaryGroup⟩

/-- The permutations of the monomial unmodified fusion operators. -/
private def unmodifiedPerm (a _ : Multiplicative (ZMod 2)) : Equiv.Perm (Fin 2 → Fin 4) :=
  if Multiplicative.toAdd a = 0 then 1 else matterBarFlip

/-- The phases of the monomial unmodified fusion operators. -/
private def unmodifiedPhase (a b : Multiplicative (ZMod 2)) : (Fin 2 → Fin 4) → ℂ :=
  if Multiplicative.toAdd a = 0 then fun _ ↦ 1
  else if Multiplicative.toAdd b = 0 then fun i ↦ (-1) ^ (eExponent (localBits i)).val
  else fun i ↦ -I * (-1) ^ (hExponent (localBits i)).val

private theorem unmodifiedCircuitTuple_eq_monomial (a b : Multiplicative (ZMod 2)) :
    (unmodifiedCircuitTuple a b : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) =
      monomial (unmodifiedPerm a b) (unmodifiedPhase a b) := by
  rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
    rcases MPSTensor.zmod2_cases b with rfl | rfl
  · simp [unmodifiedCircuitTuple, unmodifiedPerm, unmodifiedPhase, monomial_one]
  · simp [unmodifiedCircuitTuple, unmodifiedPerm, unmodifiedPhase, monomial_one]
  · simp only [unmodifiedCircuitTuple, unmodifiedPerm, unmodifiedPhase, w_eq,
      matterMatrix_monomial, toAdd_ofAdd, one_ne_zero, ↓reduceIte, toAdd_one]
    rfl
  · simp only [unmodifiedCircuitTuple, unmodifiedPerm, unmodifiedPhase, lambda_eq,
      matterMatrix_monomial, toAdd_ofAdd, one_ne_zero, ↓reduceIte]
    rfl

/-- **The unmodified Gauss law does not fix the gauged CZX state**: on every chain of at least
two sites and at every window, the local Gauss operator `𝒢_g` of `eq:mcGCZX`, built from the
unmodified fusion operators, moves the periodic vector of `CZX_gaugedMPS`. The witness is the
configuration with matter `|00⟩` and gauge label `e` at every site, where the phase of `𝒢_g`
is `i` while the gauged vector changes by `-i`.

Source: arXiv:2502.20257, `main.tex` lines 5121--5179: "This MPS is not invariant under
`eq:mcGCZX` due to the nontrivial L-symbol". -/
theorem unmodifiedPlacedGaussOperator_mulVec_gaugedMPS_ne (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    MPOTensor.placedGaussOperator 4 (Multiplicative (ZMod 2)) N hN j unmodifiedCircuitTuple gen *ᵥ
      gaugedMPS N ≠ gaugedMPS N := by
  have : NeZero N := ⟨by omega⟩
  rw [MPOTensor.placedGaussOperator, gaussWindowOperator,
    TNLean.Algebra.gaussOperator_eq_monomial _ _ _ unmodifiedCircuitTuple_eq_monomial,
    Matrix.coe_reindexAlgEquiv, reindex_monomial, embedLocalOperator_monomial, Ne,
    monomial_mulVec_eq_self_iff]
  intro h
  set c : Gs := gaugedSite.symm (0, 1)
  have hs := h fun _ ↦ c
  rw [windowPerm_apply, extractWindow_two hN j] at hs
  have hwin : (gaussLocalCoordinateEquiv 4 (Multiplicative (ZMod 2))).symm ![c, c] =
      (![0, 0], (1, 1)) := windowCoordinates_symm_gaugedSite (0, 1) (0, 1)
  have himg : ((gaussLocalCoordinateEquiv 4 (Multiplicative (ZMod 2))).symm.trans
      ((TNLean.Algebra.gaussMonomialPerm unmodifiedPerm gen).trans
        (gaussLocalCoordinateEquiv 4 (Multiplicative (ZMod 2))))) ![c, c] =
      ![gaugedSite.symm (3, gen), gaugedSite.symm (0, gen)] := by
    rw [Equiv.trans_apply, Equiv.trans_apply, hwin]
    funext k
    fin_cases k <;>
      simp +decide [gaugedSite, unmodifiedPerm, TNLean.Algebra.gaussLegAction_apply]
  rw [himg, Function.comp_apply, hwin] at hs
  obtain ⟨R, h1, h2⟩ := gaugedMPS_replaceWindow hN j (fun _ ↦ c)
    ![gaugedSite.symm (3, gen), gaugedSite.symm (0, gen)] (by simp +decide [c, gaugedLeftBond])
  have hR : R = 1 := by
    have hone : gaugedMPS N (fun _ ↦ c) = 1 := by
      rw [gaugedMPS_eq_prod]
      simp +decide [c, gaugedBondFactorZ, gaugedBondWeightZ, gaugedLeftBond]
    rw [h2] at hone
    simpa +decide [c, gaugedBondFactorZ, gaugedBondWeightZ, gaugedLeftBond] using hone
  rw [h1, h2, hR] at hs
  have hphase : TNLean.Algebra.gaussMonomialPhase unmodifiedPerm unmodifiedPhase gen
      (![0, 0], (1, 1)) = I := by
    simp +decide [TNLean.Algebra.gaussMonomialPhase, unmodifiedPerm, unmodifiedPhase, hExponent]
  rw [hphase] at hs
  have hlhs : GaussianInt.toComplex
      (gaugedBondFactorZ (gaugedSite (gaugedSite.symm (3, gen)))
          (gaugedSite (gaugedSite.symm (0, gen))) *
        gaugedBondWeightZ (gaugedSite (gaugedSite.symm (0, gen)))
          (gaugedLeftBond (gaugedSite c))) = -I := by
    simp +decide [c, gaugedBondFactorZ, gaugedBondWeightZ, gaugedLeftBond, toComplex_neg_i]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hs
  rw [hlhs] at hs
  have hrhs : GaussianInt.toComplex
      (gaugedBondFactorZ (gaugedSite c) (gaugedSite c) *
        gaugedBondWeightZ (gaugedSite c) (gaugedLeftBond (gaugedSite c))) = 1 := by
    simp +decide [c, gaugedBondFactorZ, gaugedBondWeightZ, gaugedLeftBond]
  rw [hrhs] at hs
  have := congrArg Complex.im hs
  norm_num at this

/-! ### Neighbouring modified projectors do not commute -/

/-- The modified local Gauss operators of the generator on two neighbouring windows do not
commute, on every chain of at least three sites. The witness is the configuration with matter
`|00⟩` and gauge label `g` at every site. -/
theorem not_commute_placedGaussOperator (N : ℕ) [NeZero N] (hN : 3 ≤ N) (j : Fin N) :
    ¬ Commute (placedGaussOperator N (Nat.le_of_succ_le hN) j)
      (placedGaussOperator N (Nat.le_of_succ_le hN) (j + 1)) := by
  set hN2 : 2 ≤ N := Nat.le_of_succ_le hN
  have hj1 : j + 1 ≠ j := succ_ne_self hN2 j
  have hj2 : j + 1 + 1 ≠ j := succ_succ_ne_self hN j
  have hj21 : j + 1 + 1 ≠ j + 1 := succ_ne_self hN2 (j + 1)
  intro hc
  have h := hc.eq
  rw [placedGaussOperator_eq_monomial, placedGaussOperator_eq_monomial, monomial_mul_monomial,
    monomial_mul_monomial] at h
  set π := windowCoordinates.symm.trans (localPerm.trans windowCoordinates)
  set c : Gs := gaugedSite.symm (0, gen)
  set s : Fin N → Gs := fun _ ↦ c
  have hπ : π ![c, c] = ![gaugedSite.symm (3, 1), gaugedSite.symm (0, 1)] := by
    rw [localPerm_gaugedSite_window]
    rfl
  -- The images of the constant configuration under the two placed permutations.
  have hPj : ∀ k, windowPerm 2 hN2 j π s k =
      if k = j then gaugedSite.symm (3, 1) else if k = j + 1 then gaugedSite.symm (0, 1)
      else c := by
    intro k
    rw [windowPerm_apply, extractWindow_two hN2 j, replaceWindow_two_apply, hπ]
    rfl
  have hPj1 : ∀ k, windowPerm 2 hN2 (j + 1) π s k =
      if k = j + 1 then gaugedSite.symm (3, 1) else if k = j + 1 + 1 then gaugedSite.symm (0, 1)
      else c := by
    intro k
    rw [windowPerm_apply, extractWindow_two hN2 (j + 1), replaceWindow_two_apply, hπ]
    rfl
  -- The phases.
  have hΦj1 : localPhase (windowCoordinates.symm (MPSTensor.extractWindow 2 j
      (windowPerm 2 hN2 (j + 1) π s))) =
      iPow (phaseExponent (localBits ![0, 3]) 1 0) := by
    rw [extractWindow_two hN2 j, hPj1, hPj1, ite_eq_right hj1.symm, ite_eq_right hj2.symm,
      ite_eq_left rfl, localPhase_gaugedSite_window]
    rfl
  have hΦj1' : localPhase (windowCoordinates.symm (MPSTensor.extractWindow 2 (j + 1)
      (windowPerm 2 hN2 j π s))) =
      iPow (phaseExponent (localBits ![0, 0]) 0 1) := by
    rw [extractWindow_two hN2 (j + 1), hPj, hPj, ite_eq_right hj1, ite_eq_left rfl,
      ite_eq_right hj2, ite_eq_right hj21, localPhase_gaugedSite_window]
    rfl
  have hΦ : ∀ k, localPhase (windowCoordinates.symm (MPSTensor.extractWindow 2 k s)) =
      iPow (phaseExponent (localBits ![0, 0]) 1 1) := by
    intro k
    rw [extractWindow_two hN2 k, localPhase_gaugedSite_window]
    rfl
  have hentry := congrFun (congrFun h ((windowPerm 2 hN2 j π * windowPerm 2 hN2 (j + 1) π) s)) s
  rw [monomial_apply, monomial_apply, ite_eq_left rfl] at hentry
  simp only [Equiv.Perm.mul_apply] at hentry
  rw [hΦj1, hΦ, hΦ] at hentry
  have hne : iPow (phaseExponent (localBits ![0, 3]) 1 0) *
      iPow (phaseExponent (localBits ![0, 0]) 1 1) ≠
      iPow (phaseExponent (localBits ![0, 0]) 0 1) *
        iPow (phaseExponent (localBits ![0, 0]) 1 1) := by
    rw [← toComplex_iPowZ, ← toComplex_iPowZ, ← toComplex_iPowZ, ← map_mul, ← map_mul]
    exact fun h ↦ absurd (GaussianInt.toComplex_injective h) (by decide)
  have hne0 : iPow (phaseExponent (localBits ![0, 3]) 1 0) *
      iPow (phaseExponent (localBits ![0, 0]) 1 1) ≠ 0 := by
    rw [← toComplex_iPowZ, ← toComplex_iPowZ, ← map_mul, map_ne_zero_iff _
      GaussianInt.toComplex_injective]
    decide
  by_cases hperm : windowPerm 2 hN2 j π (windowPerm 2 hN2 (j + 1) π s) =
      windowPerm 2 hN2 (j + 1) π (windowPerm 2 hN2 j π s)
  · simp only [hperm, ↓reduceIte, hΦj1'] at hentry
    exact hne hentry
  · simp only [hperm, ↓reduceIte] at hentry
    exact hne0 hentry

/-- **The modified Gauss projectors do not commute**: on every chain of at least three sites,
the modified Gauss projectors on two neighbouring windows do not commute. This is the cost
stated in line 5183 for the anomalous CZX example.

Source: arXiv:2502.20257, `main.tex` lines 5179--5183, with `eq:gauge_projs` at lines
3494--3499. -/
theorem not_commute_placedGaussProjector (N : ℕ) [NeZero N] (hN : 3 ≤ N) (j : Fin N) :
    ¬ Commute
      (placedGaussProjector 4 (Multiplicative (ZMod 2)) N (Nat.le_of_succ_le hN) j circuitTuple)
      (placedGaussProjector 4 (Multiplicative (ZMod 2)) N (Nat.le_of_succ_le hN) (j + 1)
        circuitTuple) := by
  intro hP
  refine not_commute_placedGaussOperator N hN j ?_
  have hG : ∀ k, placedGaussOperator N (Nat.le_of_succ_le hN) k = (2 : ℂ) •
      placedGaussProjector 4 (Multiplicative (ZMod 2)) N (Nat.le_of_succ_le hN) k circuitTuple -
        1 := by
    intro k
    rw [placedGaussProjector_circuitTuple, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul,
      add_sub_cancel_left]
  rw [hG, hG]
  exact (((hP.smul_left _).smul_right _).sub_right (Commute.one_right _)).sub_left
    ((Commute.one_left _).sub_right (Commute.one_left _))

end MPOTensor.CZX
