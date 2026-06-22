# Issue: Reviewer error on Thm 5.54 dimension convention

**Date:** April 8, 2026
**Review file:** `blueprint_chapter5_v4_review.md`, item C5-3 (Thm 5.54)
**Status:** Reviewer claim incorrect; original blueprint was correct

## Reviewer's claim

> **Thm 5.54 (Rectangular Kraus freedom): ⚠ Dimension/convention error.**
> The theorem declares V as r₁ × r₂ with V†V = 1, and writes B_α = Σ_j V_{αj} A_j.
> But {B_α} has r₂ operators (α ∈ Fin(r₂)) and {A_j} has r₁ operators (j ∈ Fin(r₁)),
> so V_{αj} is naturally an r₂ × r₁ matrix — not r₁ × r₂ as declared.

## Why this is wrong

The reviewer assumed `{B_α}` has `r₂` operators and `{A_j}` has `r₁` operators.
This is backwards. The Lean declaration makes the convention explicit:

```lean
theorem kraus_rectangular_freedom
    {r₁ r₂ : ℕ}
    (B : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)   -- B has r₁ operators (LARGER)
    (A : Fin r₂ → Matrix (Fin D) (Fin D) ℂ)   -- A has r₂ operators (smaller)
    (h : ∀ X, ∑ α : Fin r₁, B α * X * (B α)ᴴ =
             ∑ j : Fin r₂, A j * X * (A j)ᴴ)
    (hCard : r₂ ≤ r₁) :                        -- r₂ ≤ r₁
    ∃ V : Matrix (Fin r₁) (Fin r₂) ℂ,          -- V is r₁ × r₂
      V.conjTranspose * V = 1 ∧                 -- V†V = I_{r₂}
      ∀ α : Fin r₁, B α = ∑ j : Fin r₂, V α j • A j
```

So:
- `B` has `r₁` operators, indexed by `α ∈ Fin r₁` (the **larger** family)
- `A` has `r₂` operators, indexed by `j ∈ Fin r₂` (the smaller family)
- `V` is `r₁ × r₂`, and `V†V = I_{r₂}` (an `r₂ × r₂` identity)
- `B_α = Σ_j V_{α,j} A_j` with `α ∈ Fin r₁`, `j ∈ Fin r₂` — consistent

The original blueprint declared `V` as `r₁ × r₂` with `V†V = I`, which was
**correct**. The only valid improvement was to specify `V†V = I_{r₂}` instead
of the ambiguous `V†V = I`.

## What was done

The blueprint statement was updated to:
- Clarify which family is larger: added "(where `{B_α}` is the larger family
  and `{A_j}` the smaller)"
- Specify the identity size: `V†V = I_{r₂}`
- Dimensions kept as `r₁ × r₂` (matching Lean)

No Lean code changes needed.
