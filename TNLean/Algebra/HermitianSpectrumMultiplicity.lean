/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import TNLean.Algebra.HermitianTracePower

/-!
# Recovering spectral multiplicities from simple spectrum

For complex matrices of the same finite dimension, equality of their spectra
as sets determines equality of their characteristic-root multisets whenever one
matrix has simple spectrum.  The other root multiset is forced to have no repetitions by
comparing its cardinality with the common root support.  For Hermitian matrices,
this also gives equality of all trace powers.  No nonempty-dimension assumption
is needed.

## Main declarations

* `Matrix.roots_charpoly_eq_of_spectrum_eq_of_roots_nodup`: set-spectrum
  equality upgrades to root-multiset equality when one side has simple spectrum.
* `Matrix.IsHermitian.trace_pow_eq_of_spectrum_eq_of_roots_nodup`: the
  resulting equality of all trace powers for Hermitian matrices.
-/

open scoped Matrix BigOperators

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℂ}

private theorem roots_toFinset_eq_of_spectrum_eq
    (hSpectrum : spectrum ℂ B = spectrum ℂ A) :
    B.charpoly.roots.toFinset = A.charpoly.roots.toFinset := by
  ext z
  simp only [Multiset.mem_toFinset]
  rw [Polynomial.mem_roots B.charpoly_monic.ne_zero,
    Polynomial.mem_roots A.charpoly_monic.ne_zero]
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly,
    ← Matrix.mem_spectrum_iff_isRoot_charpoly, hSpectrum]

/-- If two complex matrices of the same finite dimension have equal spectra
as sets and the first matrix has simple spectrum, then their characteristic
roots agree as multisets.  Thus the second matrix also has simple spectrum.
The proof includes empty matrix dimensions. -/
theorem roots_charpoly_eq_of_spectrum_eq_of_roots_nodup
    (hSpectrum : spectrum ℂ B = spectrum ℂ A)
    (hNodup : A.charpoly.roots.Nodup) :
    B.charpoly.roots = A.charpoly.roots := by
  classical
  have hSupport := roots_toFinset_eq_of_spectrum_eq hSpectrum
  have hCardA : A.charpoly.roots.card = Fintype.card n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim]
  have hCardB : B.charpoly.roots.card = Fintype.card n := by
    rw [← (IsAlgClosed.splits B.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim]
  have hNodupB : B.charpoly.roots.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp <| by
      calc
        B.charpoly.roots.toFinset.card = A.charpoly.roots.toFinset.card :=
          congrArg Finset.card hSupport
        _ = A.charpoly.roots.card := Multiset.toFinset_card_of_nodup hNodup
        _ = Fintype.card n := hCardA
        _ = B.charpoly.roots.card := hCardB.symm
  have hBval : B.charpoly.roots = B.charpoly.roots.toFinset.val :=
    congrArg Finset.val (Multiset.toFinset_eq hNodupB)
  have hAval : A.charpoly.roots = A.charpoly.roots.toFinset.val :=
    congrArg Finset.val (Multiset.toFinset_eq hNodup)
  rw [hBval, hAval, hSupport]

end Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℂ}

/-- For Hermitian matrices under the same spectrum and simple-spectrum
hypotheses, all trace powers agree.  This is the power-sum form of the
set-to-multiplicity comparison. -/
theorem trace_pow_eq_of_spectrum_eq_of_roots_nodup
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hSpectrum : spectrum ℂ B = spectrum ℂ A)
    (hNodup : A.charpoly.roots.Nodup) (k : ℕ) :
    Matrix.trace (B ^ k) = Matrix.trace (A ^ k) := by
  have hRoots := Matrix.roots_charpoly_eq_of_spectrum_eq_of_roots_nodup
    hSpectrum hNodup
  rw [hB.trace_pow_eq_sum_eigenvalues_pow, hA.trace_pow_eq_sum_eigenvalues_pow]
  have hPowerSums := congrArg (fun s : Multiset ℂ => (s.map fun z => z ^ k).sum) hRoots
  simpa [hA.roots_charpoly_eq_eigenvalues, hB.roots_charpoly_eq_eigenvalues,
    Multiset.map_map, Function.comp_def] using hPowerSums

end Matrix.IsHermitian
