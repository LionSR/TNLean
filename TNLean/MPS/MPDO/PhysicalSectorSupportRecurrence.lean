/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.Algebra.TracePairing
import TNLean.MPS.MPDO.PhysicalSectorFactorization

/-!
# Recurrence from physical-sector spanning

For a physical-sector factorization, every matrix entry within one sector
determines a matrix on the virtual space. Multiplying entries from two
consecutive sectors exposes the neighboring operator between them.

If these virtual matrices span the full matrix algebra and both endpoints of
each nonzero neighboring edge contain a nonzero virtual matrix, then every
such edge `k → h` admits a two-edge return `h → j → k`. The proof uses
nondegeneracy and cyclicity of the matrix trace.

## Main declarations

- `sectorVirtualMatrix`: the virtual matrix associated with one matrix entry
  inside a physical sector.
- `sectorVirtualMatrix_mul_apply`: the product of two sector virtual matrices
  contains the corresponding neighboring-operator entry as its middle factor.
- `exists_two_edge_return_of_neighboringOperator_ne_zero`: every nonzero
  neighboring edge closes to a directed triangle under the spanning and
  nonvanishing hypotheses.
- `neighboringOperator_reaches_of_ne_zero`: the corresponding reachability
  statement for the nonzero neighboring relation.
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The virtual matrix obtained from a matrix entry within physical sector
`k`. Its `(beta, alpha)` entry is the product of the corresponding left and
right sector-tensor entries. -/
def sectorVirtualMatrix (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) (x y : F.SectorIndex k) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun beta alpha ↦
    F.leftTensor k beta x.1 y.1 * F.rightTensor k alpha x.2 y.2

/-- Multiplying virtual matrices from sectors `k` and `h` exposes the
neighboring operator from `k` to `h` as the middle factor. -/
theorem sectorVirtualMatrix_mul_apply (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) (x y : F.SectorIndex k)
    (u v : F.SectorIndex h) (beta gamma : Fin D) :
    (F.sectorVirtualMatrix k x y * F.sectorVirtualMatrix h u v) beta gamma =
      F.leftTensor k beta x.1 y.1 *
        F.neighboringOperator k h (x.2, u.1) (y.2, v.1) *
          F.rightTensor h gamma u.2 v.2 := by
  simp only [Matrix.mul_apply, sectorVirtualMatrix, neighboringOperator_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- If the neighboring operator from `k` to `h` vanishes, then every product
of a sector-`k` virtual matrix with a sector-`h` virtual matrix vanishes. -/
theorem sectorVirtualMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount)
    (hzero : F.neighboringOperator k h = 0)
    (x y : F.SectorIndex k) (u v : F.SectorIndex h) :
    F.sectorVirtualMatrix k x y * F.sectorVirtualMatrix h u v = 0 := by
  ext beta gamma
  rw [F.sectorVirtualMatrix_mul_apply k h x y u v beta gamma, hzero]
  simp

/-- The finite index type of all matrix entries within all physical sectors. -/
abbrev SectorEntryIndex (F : PhysicalSectorFactorization K) :=
  Σ k : Fin F.sectorCount, F.SectorIndex k × F.SectorIndex k

/-- The family of virtual matrices indexed by all entries within all physical
sectors. -/
def sectorVirtualMatrixFamily (F : PhysicalSectorFactorization K)
    (q : SectorEntryIndex F) : Matrix (Fin D) (Fin D) ℂ :=
  F.sectorVirtualMatrix q.1 q.2.1 q.2.2

/-- Suppose the sector virtual matrices span the full virtual matrix algebra
and both endpoint sectors of every nonzero neighboring edge contain a nonzero
virtual matrix. Then every nonzero edge `k → h` has a two-edge return
`h → j → k`.

Indeed, a nonzero neighboring entry gives sector matrices `A` and `B` with
`A * B ≠ 0`. Nondegeneracy of the trace pairing and the spanning hypothesis
give a sector matrix `C` with `trace (A * B * C) ≠ 0`. Cyclicity of the trace
then forces both `B * C` and `C * A` to be nonzero. -/
theorem exists_two_edge_return_of_neighboringOperator_ne_zero
    (F : PhysicalSectorFactorization K)
    (hspan : Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) = ⊤)
    (hnonzero : ∀ {k h}, F.neighboringOperator k h ≠ 0 →
      (∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0) ∧
        ∃ x y : F.SectorIndex h, F.sectorVirtualMatrix h x y ≠ 0)
    {k h : Fin F.sectorCount} (hkh : F.neighboringOperator k h ≠ 0) :
    ∃ j : Fin F.sectorCount,
      F.neighboringOperator h j ≠ 0 ∧ F.neighboringOperator j k ≠ 0 := by
  classical
  obtain ⟨ex, ey, heta⟩ := Matrix.exists_entry_ne_zero_of_ne_zero _ hkh
  obtain ⟨⟨kx, ky, hkxy⟩, ⟨hx, hy, hhxy⟩⟩ := hnonzero hkh
  obtain ⟨beta, alpha, hkentry⟩ :=
    Matrix.exists_entry_ne_zero_of_ne_zero _ hkxy
  have hkleft : F.leftTensor k beta kx.1 ky.1 ≠ 0 :=
    left_ne_zero_of_mul hkentry
  obtain ⟨delta, gamma, hhentry⟩ :=
    Matrix.exists_entry_ne_zero_of_ne_zero _ hhxy
  have hhright : F.rightTensor h gamma hx.2 hy.2 ≠ 0 :=
    right_ne_zero_of_mul hhentry
  let x : F.SectorIndex k := (kx.1, ex.1)
  let y : F.SectorIndex k := (ky.1, ey.1)
  let u : F.SectorIndex h := (ex.2, hx.2)
  let v : F.SectorIndex h := (ey.2, hy.2)
  let A := F.sectorVirtualMatrix k x y
  let B := F.sectorVirtualMatrix h u v
  have hAB : A * B ≠ 0 := by
    intro hz
    have hzentry := congrFun (congrFun hz beta) gamma
    rw [Matrix.zero_apply,
      F.sectorVirtualMatrix_mul_apply k h x y u v beta gamma] at hzentry
    exact mul_ne_zero (mul_ne_zero hkleft heta) hhright hzentry
  obtain ⟨Y, htraceY⟩ : ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      Matrix.trace (A * B * Y) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hAB ((Matrix.trace_mul_right_eq_zero_iff (A * B)).mp hall)
  have hYmem : Y ∈ Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp hYmem
  have hsum : Matrix.trace
      (A * B * ∑ q, c q • F.sectorVirtualMatrixFamily q) ≠ 0 := by
    rw [hc]
    exact htraceY
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul] at hsum
  obtain ⟨q, hq⟩ : ∃ q : SectorEntryIndex F,
      c q * Matrix.trace (A * B * F.sectorVirtualMatrixFamily q) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hsum (Finset.sum_eq_zero fun q _ ↦ hall q)
  have htraceC : Matrix.trace
      (A * B * F.sectorVirtualMatrixFamily q) ≠ 0 :=
    right_ne_zero_of_mul hq
  let C := F.sectorVirtualMatrixFamily q
  have hBC : B * C ≠ 0 := by
    intro hz
    apply htraceC
    rw [← Matrix.trace_mul_cycle B C A, hz, Matrix.zero_mul,
      Matrix.trace_zero]
  have hCA : C * A ≠ 0 := by
    intro hz
    apply htraceC
    rw [Matrix.trace_mul_cycle A B C, hz, Matrix.zero_mul,
      Matrix.trace_zero]
  refine ⟨q.1, ?_, ?_⟩
  · intro hz
    exact hBC (F.sectorVirtualMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
      h q.1 hz u v q.2.1 q.2.2)
  · intro hz
    exact hCA (F.sectorVirtualMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
      q.1 k hz q.2.1 q.2.2 x y)

/-- Under the spanning and endpoint-nonvanishing hypotheses, the terminal
sector of every nonzero neighboring edge reaches its initial sector through
nonzero neighboring edges. The return path supplied here has length two. -/
theorem neighboringOperator_reaches_of_ne_zero
    (F : PhysicalSectorFactorization K)
    (hspan : Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) = ⊤)
    (hnonzero : ∀ {k h}, F.neighboringOperator k h ≠ 0 →
      (∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0) ∧
        ∃ x y : F.SectorIndex h, F.sectorVirtualMatrix h x y ≠ 0)
    {k h : Fin F.sectorCount} (hkh : F.neighboringOperator k h ≠ 0) :
    Relation.ReflTransGen (fun a b ↦ F.neighboringOperator a b ≠ 0) h k := by
  obtain ⟨j, hhj, hjk⟩ :=
    F.exists_two_edge_return_of_neighboringOperator_ne_zero hspan hnonzero hkh
  exact Relation.ReflTransGen.head hhj (Relation.ReflTransGen.single hjk)

end MPOTensor.PhysicalSectorFactorization
