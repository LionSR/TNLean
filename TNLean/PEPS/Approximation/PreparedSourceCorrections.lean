/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PreparedSourceContraction

/-!
# Source-operator corrections in actual prepared density calculations

The endpoint coefficient array is obtained from the actual remaining words.
Replacing their source operators by exact terms plus corrections expands over
the common source positions. Each position remains fixed while the ket and bra
labels vary; in particular, the subsets do not select labels.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-source-corrections-preparedsourcecorrections-01
Downstream declaration:
TNLean.PEPS.PairEffect.Word.sourceOperatorDensity

Provenance-ID: 8769-source-corrections-preparedsourcecorrections-02
Downstream declaration:
TNLean.PEPS.PairEffect.Word.sourceOperatorDensity_sub

Provenance-ID: 8769-source-corrections-preparedsourcecorrections-03
Downstream declaration:
TNLean.PEPS.PairEffect.Word.sourceOperatorDensity_exact

Provenance-ID: 8769-source-corrections-preparedsourcecorrections-04
Downstream declaration:
TNLean.PEPS.PairEffect.Word.sourceOperatorDensity_sub_prepared

-/

noncomputable section
open scoped ComplexConjugate Matrix TensorProduct
namespace TNLean.PEPS.PairEffect.Word

variable {P m n ι : Type} [Fintype m] [Fintype n] [Fintype ι]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : ι → Fin R.length → Type}
    [∀ ξ i, Fintype (A ξ i)] [∀ ξ i, Fintype (B ξ i)]
    (uU : ∀ ξ i, A ξ i → U i) (uV : ∀ ξ i, B ξ i → V i)
    (c : ι → ℂ) (ℓ : Layout P) {ℓ' : Layout P}
    (v : ι → Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n ℂ)

/-- Substitute arbitrary source operators into the density calculation of the
actual prepared words, retaining the original complex branch coefficients.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
def sourceOperatorDensity
    (X : ∀ ξ ζ i, Matrix (A ξ i × B ξ i) (A ζ i × B ζ i) ℂ) : Matrix m m ℂ :=
  ∑ ξ, ∑ ζ, (c ξ * conj (c ζ)) •
    Matrix.sourceContraction
      (fun x ↦ (v ξ).preparedDensityCoefficient R U V (uU ξ) (uV ξ)
        (uU ζ) (uV ζ) ℓ (v ζ) bIn bOut ρ (fun i ↦ (x i).1) (fun i ↦ (x i).2))
      (X ξ ζ)

/-- Subtracting the exact source-operator density leaves precisely the nonempty
subsets of corrected positions. The source operators may be rectangular and
the input matrix is arbitrary. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, `eq:compression-subset-expansion`, lines 338–355. -/
theorem sourceOperatorDensity_sub
    (X E : ∀ ξ ζ i, Matrix (A ξ i × B ξ i) (A ζ i × B ζ i) ℂ) :
    sourceOperatorDensity R U V uU uV c ℓ v bIn bOut ρ (E + X) -
        sourceOperatorDensity R U V uU uV c ℓ v bIn bOut ρ X =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin R.length))).erase ∅,
        sourceOperatorDensity R U V uU uV c ℓ v bIn bOut ρ
          (fun ξ ζ ↦ S.piecewise (E ξ ζ) (X ξ ζ)) := by
  classical
  simp only [sourceOperatorDensity, Pi.add_apply, ← Finset.sum_sub_distrib, ← smul_sub]
  simp only [Matrix.sourceContraction_sub, Finset.smul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι))
    (t := (Finset.univ : Finset (Finset (Fin R.length))).erase ∅)]

/-- Exact rank-one source operators recover the density of the actual weighted
prepared operator. The finite endpoint bases may depend on the branch.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem sourceOperatorDensity_exact
    (bU : ∀ ξ i, OrthonormalBasis (A ξ i) ℂ (U i))
    (bV : ∀ ξ i, OrthonormalBasis (B ξ i) ℂ (V i))
    (η : ι → ∀ i, U i ⊗[ℂ] V i) :
    sourceOperatorDensity R U V (fun ξ i ↦ bU ξ i) (fun ξ i ↦ bV ξ i)
        c ℓ v bIn bOut ρ
        (fun ξ ζ i ↦ Matrix.vecMulVec
          (((bU ξ i).tensorProduct (bV ξ i)).repr (η ξ i))
          (fun a ↦ conj (((bU ζ i).tensorProduct (bV ζ i)).repr (η ζ i) a))) =
      (∑ ξ, c ξ • (v ξ).preparedMatrix R U V (η ξ) ℓ bIn bOut) * ρ *
        (∑ ξ, c ξ • (v ξ).preparedMatrix R U V (η ξ) ℓ bIn bOut)ᴴ := by
  classical
  unfold sourceOperatorDensity
  rw [preparedMatrix_gate_density_eq_sum_basis R U V bU bV c η ℓ v bIn bOut ρ]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [(v ξ).sourceContraction_preparedDensityCoefficient_basis R U V
    (bU ξ) (bV ξ) (bU ζ) (bV ζ) (η ξ) (η ζ) ℓ (v ζ) bIn bOut ρ,
    (v ξ).preparedMatrix_density_eq_sum_basis R U V
      (bU ξ) (bV ξ) (bU ζ) (bV ζ) (η ξ) (η ζ) ℓ (v ζ) bIn bOut ρ]

/-- Replacing the actual pure sources by arbitrary corrected source operators
gives an exact expansion of the error relative to the original weighted prepared
density. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, `eq:compression-subset-expansion`, lines 338–355. -/
theorem sourceOperatorDensity_sub_prepared
    (bU : ∀ ξ i, OrthonormalBasis (A ξ i) ℂ (U i))
    (bV : ∀ ξ i, OrthonormalBasis (B ξ i) ℂ (V i))
    (η : ι → ∀ i, U i ⊗[ℂ] V i)
    (E : ∀ ξ ζ i, Matrix (A ξ i × B ξ i) (A ζ i × B ζ i) ℂ) :
    let X := fun ξ ζ i ↦ Matrix.vecMulVec
      (((bU ξ i).tensorProduct (bV ξ i)).repr (η ξ i))
      (fun a ↦ conj (((bU ζ i).tensorProduct (bV ζ i)).repr (η ζ i) a))
    let M := ∑ ξ, c ξ • (v ξ).preparedMatrix R U V (η ξ) ℓ bIn bOut
    sourceOperatorDensity R U V (fun ξ i ↦ bU ξ i) (fun ξ i ↦ bV ξ i)
        c ℓ v bIn bOut ρ (E + X) - M * ρ * Mᴴ =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin R.length))).erase ∅,
        sourceOperatorDensity R U V (fun ξ i ↦ bU ξ i) (fun ξ i ↦ bV ξ i)
          c ℓ v bIn bOut ρ (fun ξ ζ ↦ S.piecewise (E ξ ζ) (X ξ ζ)) := by
  classical
  dsimp only
  rw [← sourceOperatorDensity_exact R U V c ℓ v bIn bOut ρ bU bV η]
  exact sourceOperatorDensity_sub R U V (fun ξ i ↦ bU ξ i) (fun ξ i ↦ bV ξ i)
    c ℓ v bIn bOut ρ _ E

end TNLean.PEPS.PairEffect.Word
