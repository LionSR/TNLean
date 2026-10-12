/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.GlobalSchmidtBellPrevector
import QICLean.Analysis.RegionalRoughLowerThree
import QICLean.Analysis.MeanTreeSublinearRemainder

/-!
# The rough lower comparison for one selected Schmidt--Bell sequence

The original physical eigenvector and one positive-mass spectral restriction
choose a single common auxiliary label sequence. The same sequence retains
the mass in the selected label and its dimension asymptotic and supplies the
initial vector for every band product below. The lower comparison uses the original
Hamiltonian and the normalized inverse-power vector of that same product.

At each fixed band count the logarithmic remainder is independent of the
symmetric coordinates, regions and mean tree. Its convergence follows from
the dimension asymptotic of the same labels. Neither the comparison value
nor its energy defect is required to converge.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
07-comparators.tex, comparator:prevector, comparator:high-label and
comparator:rough-lower, lines 130--169, 240--281 and 585--651;
08-scanner.tex, scanner:bootstrap-comparison, lines 755--769, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.

The configurations of the physical sites and both auxiliary sites are retained.
Identification with the regions and geometric mean at a scan point is a
separate application. The proof remains unfinished.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw

open Classical in
/-- One selected label sequence gives the physical rough lower comparison
and a common vanishing remainder at every fixed band count. Positive selected
mass, rather than a separate cardinality or nonempty assumption, supplies the
auxiliary dimension. The selected vector determines the labels; its energy is
not asserted. All energy expressions use the original physical Hamiltonian
and the normalized inverse-power vector of the specified band product.
Source: 07-comparators.tex, comparator:prevector, comparator:high-label and
comparator:rough-lower, lines 130--169, 240--281 and 585--651;
08-scanner.tex, scanner:bootstrap-comparison, lines 755--769, adc7f124. -/
theorem exists_global_schmidtBellPrevector_rough_lower
    {q : ℕ} [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (E₀ gap : ℝ)
    (hΩ : ‖Ω‖ = 1) (hE : H *ᵥ Ω.ofLp = (E₀ : ℂ) • Ω.ofLp)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ω.ofLp (star Ω.ofLp))).PosSemidef)
    (hgap_pos : 0 < gap)
    (X : Finset ι)
    (E : Finset (FiniteProduct.Configuration (fun _ : ι => Fin q) X)) :
    let β := fun _ : ι => Fin q
    let split := FiniteProduct.splitEquiv β X
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split Ω
    0 < Matrix.IsHermitian.spectralRestrictionMass
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E →
    let d := E.card
    let ι₀ := addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x =>
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let S' := vonNeumannEntropy
      (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
      (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      let ε : ℕ → ℝ := fun k => -2 * (Real.log (ell k).dim - (k : ℝ) * S')
      (∀ k : ℕ, 0 < k →
        let d := E.card
        let eₖ := TensorPower.globalReplicaCopiesEquiv β (Fin d) (Fin d) k
        let ξ := WithLp.toLp 2
          (TensorPower.replicaPrevector Ω d k (ell k) ∘ eₖ)
        let L := PermutationRepresentation.labelProj
          (TensorPower.copyPerm (Fin d) k) (ell k)
        let I := (1 : Matrix (Fin k → ι → Fin q) (Fin k → ι → Fin q) ℂ)
        let Pe := PermutationRepresentation.symProj
          (TensorPower.copyPerm
            ((v : Option (Option ι)) →
              TensorPower.addedSiteSpace (TensorPower.addedSiteSpace β (Fin d))
                (Fin d) v) k)
        ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 ∧
          (((((k : ℝ)⁻¹ • Matrix.replicaHamiltonian H k) ⊗ₖ
            (1 : Matrix ((Fin k → Fin d) × (Fin k → Fin d))
              ((Fin k → Fin d) × (Fin k → Fin d)) ℂ)).submatrix eₖ eₖ) *ᵥ ξ =
            (E₀ : ℂ) • ξ.ofLp) ∧
          Pe *ᵥ ξ = ξ.ofLp ∧
          ((I ⊗ₖ (L ⊗ₖ (1 : Matrix (Fin k → Fin d)
            (Fin k → Fin d) ℂ))).submatrix eₖ eₖ) *ᵥ ξ = ξ.ofLp ∧
          ((I ⊗ₖ ((1 : Matrix (Fin k → Fin d)
            (Fin k → Fin d) ℂ) ⊗ₖ L)).submatrix eₖ eₖ) *ᵥ ξ = ξ.ofLp) ∧
      (∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
              (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
              PermutationRepresentation.labelProj
                (TensorPower.copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                (Fin k → Fin E.card) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * S')
        (fun k : ℕ => (k : ℝ)) ∧
      (∀ k : ℕ,
        2 * (k : ℝ) * S' - ε k = Real.log (ell k).dim + Real.log (ell k).dim) ∧
      Tendsto (fun k : ℕ => ε k / (k : ℝ)) atTop (𝓝 0) ∧
      ∀ (K : ℕ), 8 ≤ K →
        ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
          let a := 4 / (K : ℝ)
          let t := 2 / (K : ℝ)
          let r : ℕ → ℝ := fun k =>
            Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) + a * ε k
          let ρ : ℕ → ℝ := fun k =>
            ((K : ℝ) / 2 * (2 * |r k| + Cf * Real.log ((k : ℝ) + 2) +
              2 * Real.log 2 + Real.log (3 / 2))) / (k : ℝ)
          Tendsto ρ atTop (𝓝 0) ∧
          ∀ (k n : ℕ), 0 < k →
            ∀ (Z : Matrix (Config k ι₀) (Fin n) ℂ),
            Zᴴ * Z = 1 →
            Z * Zᴴ = symProj (copyPerm ((x : Option (Option ι)) → ι₀ x) k) →
            ∀ (J : Type) [Fintype J] [DecidableEq J]
              (Q Y : J → Fin K → Finset ι),
            (∀ j g, Disjoint (Q j g) (Y j g)) →
            (∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h) →
            ∀ T : MeanTree J,
            let eₖ := globalReplicaCopiesEquiv β (Fin d) (Fin d) k
            let ξ := WithLp.toLp 2 (replicaPrevector Ω d k (ell k) ∘ eₖ)
            let W := replicaMetric ι₀ t k
            let L := fun j g => insert (some none) ((Q j g).image fun x => some (some x))
            let F := fun j g => insert none
              (((Q j g ∪ Y j g)ᶜ).image fun x => some (some x))
            let Bmid := fun j g => (Y j g).image fun x => some (some x)
            let A := fun j g =>
              ((W (L j g))⁻¹ * (W (F j g))⁻¹ * W (Bmid j g)) ^ 2
            let B := fun j g => Zᴴ * A j g * Z
            let M := (List.ofFn fun g => T.eval (B · g)).prod
            let w := toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin Zᴴ ξ)
            let φ := (‖w‖⁻¹ : ℂ) • w
            let v := toEuclideanLin Z φ
            let δ := ((star v ⬝ᵥ
              (globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k *ᵥ v)).re - E₀) / gap
            w ≠ 0 ∧ ‖v‖ = 1 ∧ 0 ≤ δ ∧
              ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                4 * S' - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
                    3 * (δ / τ) * max 0 (2 * S') - ρ k ≤
                  -Real.log (‖w‖ ^ 2) / (k : ℝ) := by
  classical
  intro β split ΩX hz d ι₀ ψ S'
  done

end TNLean.PEPS.AreaLaw
