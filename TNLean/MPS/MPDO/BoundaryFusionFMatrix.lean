/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryZipper
import TNLean.MPS.MPDO.CompleteZipperFusionInverseTrace

/-!
# The source-oriented fusion matrix of exact boundary maps

GLM23 uses the analysis-oriented fusion comparison: left-tree analysis
followed by right-tree synthesis. The actual contraction below has rows
`(e,mu,nu)` and columns `(f,lambda,sigma)`. It agrees with the inverse of
the printed comparison in the reused complete-zipper API, including after
any common physical blocking that leaves the virtual maps unchanged.

This is a coefficient construction, with zero entries allowed. No
entrywise nonvanishing, unit, duality, or pentagon is a premise.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `Fsymbolsdef`.
The convention and the corrected mixed-pentagon index order are recorded
in `docs/paper-gaps/glm23_multiplicity_l_indices.tex`.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {p r : ℕ} {χ : Fin r → ℕ} {N : Fin r → Fin r → Fin r → ℕ}

/-- Left-associated source fusion multiplicities, ordered `(e,mu,nu)`. -/
abbrev FusionLeftMultiplicity (N : Fin r → Fin r → Fin r → ℕ)
    (a b c d : Fin r) :=
  (e : Fin r) × (Fin (N a b e) × Fin (N e c d))

/-- Right-associated source fusion multiplicities, ordered `(f,lambda,sigma)`. -/
abbrev FusionRightMultiplicity (N : Fin r → Fin r → Fin r → ℕ)
    (a b c d : Fin r) :=
  (f : Fin r) × (Fin (N b c f) × Fin (N a f d))

variable
  (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)

/-- The actual GLM23 F coefficient: the normalized trace of left analysis
followed by right synthesis. In the source's main fusion section these
maps are respectively `W` and hatted `W`; here `V` always means analysis. -/
noncomputable def fusionFMatrix (a b c d : Fin r) :
    Matrix (FusionLeftMultiplicity N a b c d) (FusionRightMultiplicity N a b c d) ℂ :=
  fun ⟨e, mu, nu⟩ ⟨f, lambda, sigma⟩ ↦
    let H : Matrix (Fin (χ d)) ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) ℂ :=
      fun z v ↦
        ∑ t : Fin (χ e),
          V e c d nu z (finProdFinEquiv (t, v.2)) *
            V a b e mu t (finProdFinEquiv v.1)
    let S : Matrix ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) (Fin (χ d)) ℂ :=
      fun v z ↦
        ∑ t : Fin (χ f),
          W b c f lambda (finProdFinEquiv (v.1.2, v.2)) t *
            W a f d sigma (finProdFinEquiv (v.1.1, t)) z
    (χ d : ℂ)⁻¹ * Matrix.trace (H * S)

variable {T : ∀ a, MPOTensor p (χ a)}
  (hD : ∀ a, 0 < χ a) (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor)
  (hVW : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (T q.1).toMPSTensor)
      (fun q ↦ V a b q.1 q.2) (fun q ↦ W a b q.1 q.2))
  (K : Matrix ((c : Fin r) × (Fin (χ c) × Fin (χ c))) (Fin p × Fin p) ℂ)
  (hK : ∀ (c d : Fin r) (x y : Fin (χ c)) (x' y' : Fin (χ d)),
    (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
      if he : c = d then
        if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
      else 0)

/-- The source-oriented matrix constructed from the exact fusion maps is
the inverse printed F matrix of their complete zipper family. Physical
blocking does not appear in either contraction. -/
theorem ofBiorthogonal_inversePrintedFMatrix_eq_fusionFMatrix
    (a b c d : Fin r) (q : FusionLeftMultiplicity N a b c d)
    (t : FusionRightMultiplicity N a b c d) :
    (CompleteZipperFusionFamily.ofBiorthogonal hD hT V W hVW K hK).inversePrintedFMatrix
      a b c d q t = fusionFMatrix V W a b c d q t := by
  rw [CompleteZipperFusionFamily.inversePrintedFMatrix_eq_inv_dim_mul_trace]
  rcases q with ⟨e, mu, nu⟩
  rcases t with ⟨f, lambda, sigma⟩
  rfl

end MPOTensor
