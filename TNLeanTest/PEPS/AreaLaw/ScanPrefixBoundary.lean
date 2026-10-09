import TNLean.PEPS.AreaLaw.Scan.PrefixBoundary

/-! Regression checks for source-row physical prefix boundaries and changed-site bounds. -/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open scoped symmDiff

section

variable (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (A : Finset (Site Λ))
  {n L r₀ : ℕ} (hL : 1 ≤ L)
  (hrow : ∀ d : ℕ, 1 ≤ d → d ≤ L →
    (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
  (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
    ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z)

-- The target boundary uses row one, without a target-cardinality hypothesis.
example : (edgeBoundary Λ (depthPrefix A (fun x ↦ ambientDepth T hT x.val) 0)).card ≤
    4 * n :=
  card_edgeBoundary_depthPrefix_le Λ T hT A hL hrow hclear (by omega)

-- The last available row suffices; no estimate at L + 1 is requested.
example : (edgeBoundary Λ
    (positiveDepthPrefix A (fun x ↦ ambientDepth T hT x.val) L)).card ≤ 8 * n :=
  card_edgeBoundary_positiveDepthPrefix_le Λ T hT A hL hrow hclear le_rfl

-- Negative fronts remain legitimate comparison prefixes.
example : (edgeBoundary Λ
    (positiveDepthPrefix A (fun x ↦ ambientDepth T hT x.val) (-1))).card ≤ 8 * n :=
  card_edgeBoundary_positiveDepthPrefix_le Λ T hT A hL hrow hclear (by omega)

end

example (Λ : Finset (ℤ × ℤ)) (A B : Finset (Site Λ)) {b d : ℕ}
    (hb : (edgeBoundary Λ B).card ≤ b) (hd : (A ∆ B).card ≤ d) :
    (edgeBoundary Λ A).card ≤ b + 4 * d := by
  have := card_edgeBoundary_le_add_four_mul_symmDiff Λ A B
  omega

example (Λ : Finset (ℤ × ℤ)) (A B : Finset (Site Λ)) :
    (edgeBoundary Λ (A \ B)ᶜ).card ≤
      (edgeBoundary Λ A).card + (edgeBoundary Λ B).card := by
  rw [edgeBoundary_compl]
  exact card_edgeBoundary_sdiff_le Λ A B
