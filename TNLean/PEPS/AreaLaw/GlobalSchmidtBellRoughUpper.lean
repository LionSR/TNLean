/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GlobalSchmidtBellPrevector
import QICLean.Representation.ReplicaPrevectorRoughUpper

/-!
# The rough upper comparison for supplied physical labels

The label sequence and its selected auxiliary mass are supplied by the
physical prevector construction. At each fixed band count, the same labels
give the rough upper estimate with a vanishing logarithmic remainder.
The initial vector retains the original physical state, and the compressed
band product retains the supplied symmetric coordinates and mean tree.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 130–169, 240–281 and 332–381;
`08-scanner.tex`, lines 755–769, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology symmDiff

namespace TNLean.PEPS.AreaLaw

open Classical in
/-- The rough upper comparison for the original physical prevector and the
supplied common labels. The mass premise is the auxiliary-mass conclusion
of the global prevector construction. The remainder is uniform in the
symmetric coordinates, band regions, mean tree and entropy bounds.
Source: `07-comparators.tex`, `comparator:rough-upper`, lines 130–169,
240–281 and 332–381; `08-scanner.tex`, lines 755–769, adc7f124. -/
theorem eventually_suppliedGlobalSchmidtBellPrevector_rough_upper
    {q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {J : Type*} [Finite J]
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (hΩ : ‖Ω‖ = 1)
    (X : Finset ι)
    (E : Finset (FiniteProduct.Configuration (fun _ : ι ↦ Fin q) X))
    (regions : List (Finset ι))
    (hnested : regions.Pairwise fun D D' ↦ D ⊆ D' ∨ D' ⊆ D)
    (hdisjoint : ∀ D ∈ regions, Disjoint X D)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (K : ℕ) (hK : 8 ≤ K) :
    let β := fun _ : ι ↦ Fin q
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (FiniteProduct.splitEquiv β X) Ω
    let z := Matrix.IsHermitian.spectralRestrictionMass
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E
    0 < z →
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    (∀ᶠ k : ℕ in atTop,
      (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
        ‖WithLp.toLp 2
          (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
            (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
            labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
            (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
              (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) →
    let d := E.card
    let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
    ∃ c : ℝ, 0 ≤ c ∧
      Tendsto (Real.bellOverlapRemainder E.card c K) atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop,
        ∀ (n : ℕ) (Z : Matrix (Config k ι₀) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → ι₀ o) k) →
        ∀ (U Y : J → Fin K → Finset ι),
        (∀ j g, Disjoint (U j g) (Y j g)) →
        (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
        (∀ j g, Disjoint X (U j g ∪ Y j g)) →
        ∀ (T : MeanTree J) (Bsh Bexc : ℝ),
        (∀ D ∈ regions, FiniteProduct.entropy β Ω D ≤ Bsh) →
        (∀ j g (Q : Finset ι), Q = U j g ∨ Q = U j g ∪ Y j g →
          ∃ D ∈ regions, (D ⊆ Q ∨ Q ⊆ D) ∧
            1 + Real.log (Fintype.card (FiniteProduct.Configuration β (D ∆ Q))) ≤ Bexc) →
        let eₖ := globalReplicaCopiesEquiv β (Fin d) (Fin d) k
        let ξ := WithLp.toLp 2 (replicaPrevector Ω d k (ell k) ∘ eₖ)
        let W := replicaMetric ι₀ (2 / (K : ℝ)) k
        let L := fun j g ↦ insert (some none)
          ((X ∪ U j g).image fun x ↦ some (some x))
        let F := fun j g ↦ insert none
          (((X ∪ (U j g ∪ Y j g))ᶜ).image fun x ↦ some (some x))
        let Bmid := fun j g ↦ (Y j g).image fun x ↦ some (some x)
        let A := fun j g ↦ ((W (L j g))⁻¹ * (W (F j g))⁻¹ * W (Bmid j g)) ^ 2
        let M := (List.ofFn fun g ↦ T.eval (fun j ↦ Zᴴ * A j g * Z)).prod
        let w := toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin Zᴴ ξ)
        0 < ‖w‖ ^ 2 ∧ -Real.log (‖w‖ ^ 2) / (k : ℝ) ≤
          2 * Real.log (d : ℝ) - Real.log z +
            4 * (Bsh / z + Bexc) + Real.bellOverlapRemainder d c K k := by
  classical
  intro β ΩX z hz ψ hmass
  have hu :=
    FiniteProduct.eventually_suppliedReplicaPrevector_rough_upper
      (S := J) β Ω X E hΩ hz regions hnested hdisjoint ell
      (t := 2 / (K : ℝ))
      (div_pos (by norm_num) (by exact_mod_cast (show 0 < K by omega)))
  run_tac Lean.throwError (α := Unit) "rough-upper QIC application reached"
  done

end TNLean.PEPS.AreaLaw
