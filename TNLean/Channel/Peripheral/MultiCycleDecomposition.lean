/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.Cycles

/-!
# Multi-cycle block-permutation decompositions

This file packages an explicit multi-cycle refinement of the
block-permutation infrastructure developed in
`TNLean.Channel.Peripheral.Cycles`, in the form needed for the
asymptotic-image side of
Wolf, *Quantum Channels & Operations*, Theorem 6.16.

Concretely, Wolf Thm. 6.16 describes the asymptotic dynamics of a general
trace-preserving positive Schwarz map `T` as a permutation of Wedderburn
blocks, with each block transported by a unitary.  Such a permutation may
already be represented abstractly by the `CycleStructure` bundled data of
`TNLean.Channel.Peripheral.Cycles`, whose underlying permutation `σ` is
allowed to have multiple disjoint cycles.  The present file refines that
view by choosing an *explicit* cycle-index type `ι`, a per-cycle period
`period : ι → ℕ`, and the corresponding projection families, recording the
disjoint-union-of-cycles structure as separate data.

The corner-preservation proofs reuse the per-orbit proof pattern of
`preserves_corner_pow_of_cyclic_decomp` from
`TNLean.Channel.Peripheral.CyclicDecomposition`, adapted to the setting
where the per-cycle projections do not sum to the identity.  The
*existence direction* — that every TP positive Schwarz map admits such a
decomposition on its asymptotic image — depends on Wolf Thm. 6.14
(Wedderburn decomposition of the fixed-point algebra, issues #27/#360)
and is left to future work.

## Main definitions

* `MultiCycleDecomposition T` — bundled data for a multi-cycle
  block-permutation decomposition of `T`: a finite family of cycles indexed
  by `ι`, a per-cycle period `period : ι → ℕ` (each nonzero), a projection
  family `P : (c : ι) → Fin (period c) → MatrixAlg D`, per-cycle cyclic
  action `T (P c (k + 1)) = P c k`, and the multiplicative-domain
  factorisations on each `P c k`.

## Main results

* `MultiCycleDecomposition.preserves_corner_pow_period` — per-cycle
  corner preservation: `T^(period c)` preserves each corner
  `P c k · M_D(ℂ) · P c k`.

* `MultiCycleDecomposition.preserves_corner_pow_of_dvd` — common-period
  corner preservation: whenever `period c ∣ N` for every cycle `c`,
  `T^N` preserves every corner of the decomposition.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm. 6.16, §6.5]
-/

open scoped Matrix BigOperators
open Matrix Finset

variable {D : ℕ}

/-- Bundled data for a **multi-cycle block-permutation decomposition** of a
matrix endomorphism `T`.

A `MultiCycleDecomposition T` records a finite family of cycles — one per
element of the cycle-index type `ι` — together with:

* a per-cycle `period c : ℕ` with `NeZero (period c)`;
* a projection family `P c : Fin (period c) → MatrixAlg D` of orthogonal
  projections (one family per cycle);
* the cyclic action `T (P c (k + 1)) = P c k` *within* each cycle;
* the multiplicative-domain factorisations `T (P c k * X) = T (P c k) * T X`
  and `T (X * P c k) = T X * T (P c k)`.

This refines the bundled permutation data of
`TNLean.Channel.Peripheral.Cycles.CycleStructure`: a
`MultiCycleDecomposition` chooses an explicit cycle-index type together
with per-cycle periods and projection families for the underlying
permutation structure, while `toCycleStructure` forgets that extra
organisation.

In Wolf's Thm. 6.16, the cycle-index `ι` runs over the equivalence classes
of Wedderburn blocks that share both a common multiplicity and a common
period under the block permutation.  The existence of this data on the
asymptotic image of an arbitrary TP positive Schwarz map depends on the
Wedderburn decomposition of the fixed-point algebra (Wolf Thm. 6.14) and is
deferred. -/
structure MultiCycleDecomposition.{u} (T : MatrixEnd D) where
  /-- Finite index type for the cycles. -/
  ι : Type u
  /-- `ι` is finite. -/
  [fintype : Fintype ι]
  /-- `ι` has decidable equality. -/
  [decidableEq : DecidableEq ι]
  /-- The period of each cycle. -/
  period : ι → ℕ
  /-- Each cycle has nonzero period. -/
  nePeriod : ∀ c : ι, NeZero (period c)
  /-- The family of block projections inside each cycle. -/
  P : (c : ι) → Fin (period c) → MatrixAlg D
  /-- Each projection is an orthogonal projection. -/
  isProj : ∀ (c : ι) (k : Fin (period c)), IsOrthogonalProjection (P c k)
  /-- `T` cyclically permutes the projections inside each cycle. -/
  cyclic : ∀ (c : ι) (k : Fin (period c)), T (P c (k + 1)) = P c k
  /-- Each `P c k` lies in the left multiplicative domain of `T`. -/
  mulLeft : ∀ (c : ι) (k : Fin (period c)) (X : MatrixAlg D),
    T (P c k * X) = T (P c k) * T X
  /-- Each `P c k` lies in the right multiplicative domain of `T`. -/
  mulRight : ∀ (c : ι) (k : Fin (period c)) (X : MatrixAlg D),
    T (X * P c k) = T X * T (P c k)

namespace MultiCycleDecomposition

attribute [instance] fintype decidableEq

variable {T : MatrixEnd D}

/-- Per-cycle period is nonzero. -/
instance instNeZeroPeriod (M : MultiCycleDecomposition T) (c : M.ι) :
    NeZero (M.period c) :=
  M.nePeriod c

section CyclicShift

/-- The cyclic-shift index: an explicit `Fin m` representative of `k + n`,
constructed from `⟨((k : ℕ) + n) % m, _⟩`.  Mirrors the `cyclicIndex` helper
used inside `preserves_corner_pow_of_cyclic_decomp`. -/
private def shiftIndex {m : ℕ} [NeZero m] (k : Fin m) (n : ℕ) : Fin m :=
  ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

@[simp] private lemma shiftIndex_zero {m : ℕ} [NeZero m] (k : Fin m) :
    shiftIndex k 0 = k := by
  ext
  simp only [shiftIndex, add_zero, Nat.mod_eq_of_lt k.is_lt, Fin.eta]

private lemma shiftIndex_succ {m : ℕ} [NeZero m] (k : Fin m) (n : ℕ) :
    shiftIndex k (n + 1) = shiftIndex k n + 1 := by
  ext
  change (((k : ℕ) + n) + 1) % m = ((((k : ℕ) + n) % m) + 1 % m) % m
  exact Nat.add_mod ((k : ℕ) + n) 1 m

@[simp] private lemma shiftIndex_period {m : ℕ} [NeZero m] (k : Fin m) :
    shiftIndex k m = k := by
  ext
  change ((k : ℕ) + m) % m = k
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt]

end CyclicShift

section PreservesCornerHelper

/-- Corner preservation is stable under taking powers. -/
private lemma preserves_corner_pow {S : MatrixEnd D} {P : MatrixAlg D}
    (hP : IsOrthogonalProjection P) (hPS : PreservesCorner P S) (n : ℕ) :
    PreservesCorner P (S ^ n) := by
  induction n with
  | zero =>
      intro X
      have hIdem : P * P = P := hP.2
      change P * ((1 : MatrixEnd D) (P * X * P)) * P = (1 : MatrixEnd D) (P * X * P)
      simp only [Module.End.one_apply]
      calc
        P * (P * X * P) * P = (P * P) * X * (P * P) := by
              simp only [Matrix.mul_assoc]
        _ = P * X * P := by rw [hIdem]
  | succ n ih =>
      intro X
      have hSform : S (P * X * P) = P * S (P * X * P) * P := (hPS X).symm
      have : P * ((S ^ n) (S (P * X * P))) * P = (S ^ n) (S (P * X * P)) := by
        calc
          P * ((S ^ n) (S (P * X * P))) * P
              = P * ((S ^ n) (P * S (P * X * P) * P)) * P := by rw [← hSform]
          _ = (S ^ n) (P * S (P * X * P) * P) := ih (S (P * X * P))
          _ = (S ^ n) (S (P * X * P)) := by rw [← hSform]
      calc
        P * ((S ^ (n + 1)) (P * X * P)) * P
            = P * ((S ^ n) (S (P * X * P))) * P := by simp [pow_succ]
        _ = (S ^ n) (S (P * X * P)) := this
        _ = (S ^ (n + 1)) (P * X * P) := by simp [pow_succ]

end PreservesCornerHelper

section PerCycle

/-- **Per-cycle corner preservation.**

In cycle `c`, the channel's `period c`-th iterate preserves each corner
`P c k · M_D(ℂ) · P c k`.  The proof follows the per-orbit proof pattern
from `preserves_corner_pow_of_cyclic_decomp`, *without* the sum-to-one
hypothesis on the sector projections (which is not available in the
multi-cycle setting, where the per-cycle projections typically do not
sum to the identity).

Per Wolf Thm. 6.16 §6.5, this is the per-cycle restriction of the block
permutation back to its own orbit: after `period c` applications of `T`,
each cycle returns to itself. -/
theorem preserves_corner_pow_period (M : MultiCycleDecomposition T)
    (c : M.ι) (k : Fin (M.period c)) :
    PreservesCorner (M.P c k) (T ^ M.period c) := by
  -- main lemma: `T^n` applied to the `(k + n)`-shifted corner lands in the `k`-corner.
  have hstep :
      ∀ n : ℕ, ∀ (j : Fin (M.period c)) (X : MatrixAlg D),
        (T ^ n) (M.P c (shiftIndex j n) * X * M.P c (shiftIndex j n)) =
          M.P c j * ((T ^ n) X) * M.P c j := by
    intro n
    induction n with
    | zero =>
        intro j X
        simp only [pow_zero, shiftIndex_zero, Module.End.one_apply]
    | succ n ih =>
        intro j X
        calc
          (T ^ (n + 1))
              (M.P c (shiftIndex j (n + 1)) * X * M.P c (shiftIndex j (n + 1)))
              = (T ^ n)
                  (T (M.P c (shiftIndex j (n + 1)) * X * M.P c (shiftIndex j (n + 1)))) := by
                  simp only [pow_succ, Module.End.mul_apply]
          _ = (T ^ n)
                (T (M.P c (shiftIndex j n + 1) * X * M.P c (shiftIndex j n + 1))) := by
                  rw [shiftIndex_succ j n]
          _ = (T ^ n) (M.P c (shiftIndex j n) * T X * M.P c (shiftIndex j n)) := by
                  congr 1
                  calc
                    T (M.P c (shiftIndex j n + 1) * X * M.P c (shiftIndex j n + 1))
                        = T (M.P c (shiftIndex j n + 1) * X) *
                            T (M.P c (shiftIndex j n + 1)) := by
                              exact M.mulRight c (shiftIndex j n + 1)
                                (M.P c (shiftIndex j n + 1) * X)
                    _ = (T (M.P c (shiftIndex j n + 1)) * T X) *
                          T (M.P c (shiftIndex j n + 1)) := by
                            rw [M.mulLeft c (shiftIndex j n + 1) X]
                    _ = M.P c (shiftIndex j n) * T X * M.P c (shiftIndex j n) := by
                            rw [M.cyclic c (shiftIndex j n)]
          _ = M.P c j * ((T ^ n) (T X)) * M.P c j := ih j (T X)
          _ = M.P c j * ((T ^ (n + 1)) X) * M.P c j := by
                  simp only [pow_succ, Module.End.mul_apply]
  -- specialise `hstep` at `n = period c` using `shiftIndex k (period c) = k`
  intro X
  have hmk : (T ^ M.period c) (M.P c k * X * M.P c k) =
      M.P c k * ((T ^ M.period c) X) * M.P c k := by
    simpa using hstep (M.period c) k X
  calc
    M.P c k * (T ^ M.period c) (M.P c k * X * M.P c k) * M.P c k
        = M.P c k * (M.P c k * ((T ^ M.period c) X) * M.P c k) * M.P c k := by rw [hmk]
    _ = (M.P c k * M.P c k) * ((T ^ M.period c) X) * (M.P c k * M.P c k) := by
          simp only [Matrix.mul_assoc]
    _ = M.P c k * ((T ^ M.period c) X) * M.P c k := by
          simp only [(M.isProj c k).2, Matrix.mul_assoc]
    _ = (T ^ M.period c) (M.P c k * X * M.P c k) := by rw [hmk]

/-- **Common-period corner preservation.**

Whenever `N` is divisible by every per-cycle period, `T^N` preserves each
corner of the decomposition.

In Wolf's Thm. 6.16, `N` is the global period (= LCM of per-cycle periods),
after which the whole block permutation returns to the identity and the
channel acts diagonally on each block. -/
theorem preserves_corner_pow_of_dvd (M : MultiCycleDecomposition T)
    {N : ℕ} (hN : ∀ c : M.ι, M.period c ∣ N)
    (c : M.ι) (k : Fin (M.period c)) :
    PreservesCorner (M.P c k) (T ^ N) := by
  obtain ⟨q, hq⟩ := hN c
  have hPowEq : (T ^ N) = (T ^ M.period c) ^ q := by
    rw [← pow_mul, ← hq]
  rw [hPowEq]
  exact preserves_corner_pow (M.isProj c k)
    (M.preserves_corner_pow_period c k) q

end PerCycle

section CycleStructureInterop

/-- Total block-index type: `Σ c : ι, Fin (period c)`. -/
abbrev Idx (M : MultiCycleDecomposition T) : Type _ :=
  Σ c : M.ι, Fin (M.period c)

/-- Flattened projection family indexed by `Idx`. -/
def totalProj (M : MultiCycleDecomposition T) : M.Idx → MatrixAlg D :=
  fun x => M.P x.1 x.2

/-- Flattened permutation: per-cycle cyclic shift `k ↦ k + 1`, combined via
`Equiv.Perm.sigmaCongrRight`. -/
noncomputable def totalPerm (M : MultiCycleDecomposition T) :
    Equiv.Perm M.Idx :=
  Equiv.Perm.sigmaCongrRight (fun c : M.ι =>
    { toFun := fun k => k + 1
      invFun := fun k => k - 1
      left_inv := by intro k; simp
      right_inv := by intro k; simp })

@[simp]
lemma totalPerm_apply (M : MultiCycleDecomposition T) (x : M.Idx) :
    M.totalPerm x = ⟨x.1, x.2 + 1⟩ := rfl

/-- **Flattening construction.**  A multi-cycle decomposition gives a
`CycleStructure` on the total block-index type
`Σ c : M.ι, Fin (M.period c)`.

The permutation is the sigma-product of per-cycle cyclic shifts; the
projections are the flattened family; the cyclic action on the sigma
index matches the per-cycle action on each `Fin (period c)`.

This provides an assembly point: given a Wolf Thm. 6.16 Wedderburn-based
existence result (currently blocked on issues #27/#360), the resulting
`MultiCycleDecomposition` can be flattened to a `CycleStructure` for use
with the existing block-permutation infrastructure in
`TNLean.Channel.Peripheral.Cycles`. -/
noncomputable def toCycleStructure (M : MultiCycleDecomposition T) :
    CycleStructure T :=
  CycleStructure.ofPermDecomp (T := T)
    (ι := M.Idx) M.totalPerm M.totalProj
    (by
      rintro ⟨c, k⟩
      exact M.isProj c k)
    (by
      rintro ⟨c, k⟩
      change T (M.P c (k + 1)) = M.P c k
      exact M.cyclic c k)
    (by
      rintro ⟨c, k⟩ X
      exact M.mulLeft c k X)
    (by
      rintro ⟨c, k⟩ X
      exact M.mulRight c k X)

end CycleStructureInterop

end MultiCycleDecomposition
