/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.MarginalTails
import QICLean.Entropy.ConditionalMovementRegional
import QICLean.Representation.ReplicaEtaForms

/-!
# Conditional movement and skew estimates on lattice regions

Lemmas 5.1 and 5.3 of the area-law manuscript are stated for a unit vector on four
finite-dimensional systems. This module reads them on a finite induced square-lattice
domain with local dimension `q`, where the four systems are four regions partitioning the
sites and every operator acts on its region through the placement `localLift` of the
finite-domain model. The vector is an arbitrary unit vector; neither lemma uses the
Hamiltonian or the gap. The entropy exponent is written with the regional entropies of the
finite-domain model, `η = S(x|P) + S(x|Y) = I(x:F|P) = I(x:F|Y)`.

The finite-dimensional statements are proved in QICLean on an arbitrary finite set of sites
with arbitrary local dimensions. This module identifies the regional states, entropies and
placements of the finite-domain model with those of QICLean and specializes the regional
forms to the lattice.

## Main results

* `reducedState_eq_regionState`, `regionalEntropy_eq_regionEntropy`,
  `localLift_eq_entropyLocalLift`: the lattice regional data are the QICLean regional data.
* `movementEta_eq_condMutualInfo_left`, `movementEta_eq_condMutualInfo_right`,
  `movementEta_nonneg`: the two conditional-mutual-information forms of `η`, and `η ≥ 0`.
* `exists_norm_movement_le`: Lemma 5.1 (`lem:movement`) on lattice regions.
* `skewSymbol_skew_le`: Lemma 5.3 (`lem:skew`) on lattice regions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Lemma 5.1 (`lem:movement`), `04-conditional.tex`, lines 118–135, and
  Lemma 5.3 (`lem:skew`), lines 487–507; the regional reading of both lemmas in
  `05-replicas.tex`, lines 486–505 and 640–660.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace TNLean.PEPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-! ### The lattice regional data are the QICLean regional data -/

/-- The regional state of the finite-domain model is the QICLean regional state for constant
local dimension `q`. -/
theorem reducedState_eq_regionState (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    reducedState Λ q Ω A = Entropy.regionState (n := fun _ ↦ q) A Ω :=
  (partialTraceRight_cutVector Ω A).symm

/-- The regional entropy of the finite-domain model is the QICLean regional entropy. -/
theorem regionalEntropy_eq_regionEntropy (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    regionalEntropy Λ q Ω A = Entropy.regionEntropy (n := fun _ ↦ q) A Ω :=
  vonNeumannEntropy_congr (reducedState_eq_regionState Ω A) _ _

/-- The placement of a local matrix in the finite-domain model is the QICLean local lift. -/
theorem localLift_eq_entropyLocalLift (A : Finset (Site Λ))
    (K : Matrix (↥A → Fin q) (↥A → Fin q) ℂ) :
    localLift Λ q A K = Entropy.localLift (n := fun _ ↦ q) A K := by
  ext σ τ
  rw [Entropy.localLift_apply, localLift, QuantumCircuit.embedOp_apply]
  congr 1
  simp only [QuantumCircuit.AgreeOff, eq_iff_iff]
  constructor
  · intro h v hv
    exact h v fun w hw ↦ hv (hw ▸ w.2)
  · intro h v hv
    exact h v fun hvA ↦ hv ⟨v, hvA⟩ rfl

/-- The number of configurations of a region is `q ^ |A|`. -/
theorem card_regionConfig (A : Finset (Site Λ)) :
    Fintype.card (Entropy.RegionConfig (fun _ : Site Λ ↦ q) A) = q ^ A.card := by
  simp [Entropy.RegionConfig]

/-! ### The entropy exponent -/

/-- `S(x|P) + S(x|Y) = I(x:F|P)` for four regions partitioning the domain and a unit
vector. Area-law manuscript, `04-conditional.tex`, lines 122–124 and 138–139;
`05-replicas.tex`, lines 491–492. -/
theorem movementEta_eq_condMutualInfo_left {P x Y F : Finset (Site Λ)}
    (h : Entropy.FourPartition P x Y F) (Ω : StateSpace Λ q) :
    regionalEntropy Λ q Ω (P ∪ x) - regionalEntropy Λ q Ω P +
        (regionalEntropy Λ q Ω (x ∪ Y) - regionalEntropy Λ q Ω Y) =
      regionalEntropy Λ q Ω (x ∪ P) + regionalEntropy Λ q Ω (F ∪ P) -
        regionalEntropy Λ q Ω (x ∪ F ∪ P) - regionalEntropy Λ q Ω P := by
  have e1 := Entropy.regionEntropy_compl (n := fun _ ↦ q) (x ∪ Y) Ω
  have e2 := Entropy.regionEntropy_compl (n := fun _ ↦ q) Y Ω
  rw [h.compl_union_xY] at e1
  rw [h.compl_Y] at e2
  simp only [regionalEntropy_eq_regionEntropy, Finset.union_comm P x] at *
  linarith

/-- `S(x|P) + S(x|Y) = I(x:F|Y)` for four regions partitioning the domain and a unit
vector. Area-law manuscript, `04-conditional.tex`, lines 122–124 and 138–139;
`05-replicas.tex`, lines 491–492. -/
theorem movementEta_eq_condMutualInfo_right {P x Y F : Finset (Site Λ)}
    (h : Entropy.FourPartition P x Y F) (Ω : StateSpace Λ q) :
    regionalEntropy Λ q Ω (P ∪ x) - regionalEntropy Λ q Ω P +
        (regionalEntropy Λ q Ω (x ∪ Y) - regionalEntropy Λ q Ω Y) =
      regionalEntropy Λ q Ω (x ∪ Y) + regionalEntropy Λ q Ω (F ∪ Y) -
        regionalEntropy Λ q Ω (x ∪ F ∪ Y) - regionalEntropy Λ q Ω Y := by
  have h' : Entropy.FourPartition Y x P F :=
    ⟨h.xY.symm, h.PY.symm, h.YF, h.Px.symm, h.xF, h.PF,
      fun v ↦ by rcases h.cover v with h1 | h1 | h1 | h1 <;> simp [h1]⟩
  have := movementEta_eq_condMutualInfo_left h' Ω
  rw [Finset.union_comm Y x] at this
  rw [Finset.union_comm P x]
  linarith

/-- `η = S(x|P) + S(x|Y) ≥ 0`, by strong subadditivity. Area-law manuscript,
`04-conditional.tex`, lines 138–139. -/
theorem movementEta_nonneg {P x Y F : Finset (Site Λ)} (h : Entropy.FourPartition P x Y F)
    (Ω : StateSpace Λ q) :
    0 ≤ regionalEntropy Λ q Ω (P ∪ x) - regionalEntropy Λ q Ω P +
        (regionalEntropy Λ q Ω (x ∪ Y) - regionalEntropy Λ q Ω Y) := by
  simpa only [regionalEntropy_eq_regionEntropy, Entropy.regionalMovementEta] using
    Entropy.regionalMovementEta_nonneg (n := fun _ ↦ q) h Ω

/-! ### Lemma 5.1 -/

/-- **Lemma 5.1 on lattice regions** (area-law manuscript, `lem:movement`,
`04-conditional.tex`, lines 118–135; regional form `05-replicas.tex`, lines 553–569).
There are universal constants `C, c > 0` such that for every finite domain `Λ`, local
dimension `q`, four regions `P, x, Y, F` partitioning the sites, unit vector `θ`, positive
semidefinite `σ` on `P ∪ x` and `τ` on `x ∪ Y` of trace at most one, and `0 < a` with
`a ℓ ≤ c`, where `ℓ = log (e q^{|x|})`,
`‖σ^{a/2} ρ̂_P^{-a/2} τ^{a/2} ρ̂_Y^{-a/2} θ‖ ≤ exp (-(a/2) η + C a^{5/4} ℓ²)`.
Each factor acts on its region, `ρ̂ = ρ + Π_{ker ρ}` is the kernel completion of the
regional state, and `η = S(x|P) + S(x|Y)`. No faithfulness of the marginals is assumed. -/
theorem exists_norm_movement_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (q : ℕ) {P x Y F : Finset (Site Λ)},
        Entropy.FourPartition P x Y F → ∀ θ : StateSpace Λ q, ‖θ‖ = 1 →
        ∀ (σ : Matrix (↥(P ∪ x) → Fin q) (↥(P ∪ x) → Fin q) ℂ)
          (τ : Matrix (↥(x ∪ Y) → Fin q) (↥(x ∪ Y) → Fin q) ℂ),
          σ.PosSemidef → σ.trace.re ≤ 1 → τ.PosSemidef → τ.trace.re ≤ 1 →
          ∀ a : ℝ, 0 < a → a * Real.log (Real.exp 1 * (q : ℝ) ^ x.card) ≤ c →
            ‖(WithLp.toLp 2
                ((localLift Λ q (P ∪ x) (cfc (fun t : ℝ ↦ t ^ (a / 2)) σ) *
                  localLift Λ q P (cfc (fun t : ℝ ↦ t ^ (-a / 2))
                    (kernelCompletion (reducedState Λ q θ P))) *
                  localLift Λ q (x ∪ Y) (cfc (fun t : ℝ ↦ t ^ (a / 2)) τ) *
                  localLift Λ q Y (cfc (fun t : ℝ ↦ t ^ (-a / 2))
                    (kernelCompletion (reducedState Λ q θ Y)))) *ᵥ θ.ofLp) :
                StateSpace Λ q)‖ ≤
              Real.exp (-(a / 2) * (regionalEntropy Λ q θ (P ∪ x) - regionalEntropy Λ q θ P +
                  (regionalEntropy Λ q θ (x ∪ Y) - regionalEntropy Λ q θ Y)) +
                C * a ^ (5 / 4 : ℝ) * Real.log (Real.exp 1 * (q : ℝ) ^ x.card) ^ 2) := by
  obtain ⟨C, c, hC, hc, H⟩ := Entropy.regionalMovement_norm_le
  refine ⟨C, c, hC, hc, ?_⟩
  intro Λ q P x Y F h θ hθ σ τ hσ hσtr hτ hτtr a ha hsmall
  have hcard : (Fintype.card (Entropy.RegionConfig (fun _ : Site Λ ↦ q) x) : ℝ) =
      (q : ℝ) ^ x.card := by
    rw [card_regionConfig]; push_cast; rfl
  have key := H (n := fun _ : Site Λ ↦ q) h θ hθ σ τ hσ hσtr hτ hτtr a ha (by rwa [hcard])
  rw [hcard, Entropy.FourPartition.movementEta_frameVector] at key
  simp only [Entropy.regionalMoveOperator, Entropy.FourPartition.frameMarginalP_eq,
    Entropy.FourPartition.frameMarginalY_eq] at key
  simpa only [localLift_eq_entropyLocalLift, reducedState_eq_regionState,
    regionalEntropy_eq_regionEntropy, Entropy.regionalMovementEta] using key

/-! ### Lemma 5.3 -/

/-- The scalar function `f(t) = ⟨θ, ρ_P^{[t]} ρ_Y^{[-t]} h ρ_P^{[-t]} ρ_Y^{[t]} θ⟩` of
Lemma 5.3 on lattice regions, where `ρ^{[s]}` is the zero-on-kernel real power of a regional
state and `h` acts on the whole domain. Area-law manuscript, `04-conditional.tex`,
lines 495–500. -/
noncomputable def skewSymbol (Λ : Finset (ℤ × ℤ)) (q : ℕ) (t : ℝ) (P Y : Finset (Site Λ))
    (h : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) (θ : StateSpace Λ q) : ℂ :=
  star θ.ofLp ⬝ᵥ
    ((localLift Λ q P (cfc (TensorPower.suppRpow t) (reducedState Λ q θ P)) *
      localLift Λ q Y (cfc (TensorPower.suppRpow (-t)) (reducedState Λ q θ Y)) * h *
      localLift Λ q P (cfc (TensorPower.suppRpow (-t)) (reducedState Λ q θ P)) *
      localLift Λ q Y (cfc (TensorPower.suppRpow t) (reducedState Λ q θ Y))) *ᵥ θ.ofLp)

theorem skewSymbol_eq_markedScalarSymbol (t : ℝ) (P Y : Finset (Site Λ))
    (h : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) (θ : StateSpace Λ q) :
    skewSymbol Λ q t P Y h θ =
      TensorPower.markedScalarSymbol (n := fun _ ↦ q) t P Y h θ.ofLp := by
  simp only [skewSymbol, TensorPower.markedScalarSymbol, TensorPower.regionPow,
    localLift_eq_entropyLocalLift, reducedState_eq_regionState, WithLp.toLp_ofLp]

/-- **Lemma 5.3 on lattice regions** (area-law manuscript, `lem:skew`, `04-conditional.tex`,
lines 487–507; regional form `05-replicas.tex`, lines 640–660 and 838–843). Let
`P₀, P₁, x, U, F` partition the sites of a finite domain with `P = P₀ ∪ P₁` and `Y = x ∪ U`,
let `θ` be a unit vector, and let `0 ≤ K ≤ 1` act on `P₀ ∪ x`. With
`ℓ_h = log (e q^{|P₀| + |x|})` and `0 < a ℓ_h ≤ 1/8`, the function `f` of Lemma 5.3 at
`t = a/2` satisfies `|f(t)| - Re f(t) ≤ C a² ℓ_h⁴ η^{1/8}`, with the universal constant
`C = 18π² + 6144 e^{π²+1}` and `η = S(x|P) + S(x|U) = I(x:F|U)`. No dimension of
`P₁`, `U` or `F` enters. -/
theorem skewSymbol_skew_le {P₀ P₁ x U F : Finset (Site Λ)}
    (hp : TensorPower.SkewPartition P₀ P₁ x U F)
    {K : Matrix (↥(P₀ ∪ x) → Fin q) (↥(P₀ ∪ x) → Fin q) ℂ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    {a : ℝ} (ha : 0 < a)
    (hac : a * Real.log (Real.exp 1 * (q : ℝ) ^ (P₀.card + x.card)) ≤ 1 / 8)
    {θ : StateSpace Λ q} (hθ : ‖θ‖ = 1) :
    ‖skewSymbol Λ q (a / 2) (P₀ ∪ P₁) (x ∪ U) (localLift Λ q (P₀ ∪ x) K) θ‖ -
        (skewSymbol Λ q (a / 2) (P₀ ∪ P₁) (x ∪ U) (localLift Λ q (P₀ ∪ x) K) θ).re ≤
      Entropy.ConditionalSkew.skewConst * a ^ 2 *
        Real.log (Real.exp 1 * (q : ℝ) ^ (P₀.card + x.card)) ^ 4 *
        (regionalEntropy Λ q θ ((P₀ ∪ P₁) ∪ x) - regionalEntropy Λ q θ (P₀ ∪ P₁) +
          (regionalEntropy Λ q θ (x ∪ U) - regionalEntropy Λ q θ U)) ^ (1 / 8 : ℝ) := by
  have hcard : (Fintype.card (Entropy.RegionConfig (fun _ : Site Λ ↦ q) P₀) : ℝ) *
      Fintype.card (Entropy.RegionConfig (fun _ : Site Λ ↦ q) x) =
      (q : ℝ) ^ (P₀.card + x.card) := by
    rw [card_regionConfig, card_regionConfig, pow_add]; push_cast; rfl
  have hθ' : θ.ofLp ∈ TensorPower.unitSphere := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) θ
    rw [hθ, EuclideanSpace.inner_eq_star_dotProduct] at h
    change θ.ofLp ⬝ᵥ star θ.ofLp = 1
    simpa using h
  have key := hp.markedScalarSymbol_skew_le (n := fun _ ↦ q) hK0 hK1 ha (by rwa [hcard]) hθ'
  rw [hcard, hp.skewEta_transport, WithLp.toLp_ofLp] at key
  simpa only [skewSymbol_eq_markedScalarSymbol, localLift_eq_entropyLocalLift,
    regionalEntropy_eq_regionEntropy, Entropy.regionalMovementEta] using key

end TNLean.PEPS.AreaLaw
