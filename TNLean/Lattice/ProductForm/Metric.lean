/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm.Supported

/-!
# Product forms on finite metric site sets

The radius in the coefficient functions is the radius of the interaction
supports. Physical dimensions may vary from site to site.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 176–188 and 1024–1077.
-/

namespace TNLean.Lattice.Locality

variable {ι : Type} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace ι]

/-- Trotter products on arbitrary finite metric site sets have product forms
with the same radius as the centred interaction supports. The statement allows
varying local dimensions, empty supports, arbitrary factor order, and zero steps.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1053–1077. This proves the
existence and radius assertion; the index-component count is a separate result. -/
theorem hasProductForm_trotterProduct_of_metric (n : ι → ℕ) {R : ℝ} (hR : 0 ≤ R)
    (H : ι → Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ)
    (X : ι → Finset ι) (hX : ∀ i j, j ∈ X i → dist i j ≤ R)
    (hH : ∀ i, Entropy.IsSupportedOn (H i) (X i))
    (seq : List ι) (β : ℝ) (k : ℕ) :
    HasProductForm (fun i ↦ {j | dist i j ≤ R}) n
      (((seq.map fun i ↦ NormedSpace.exp ((-((β : ℂ) / k)) • H i)).prod) ^ k) :=
  hasProductForm_trotterProduct _ n
    (fun i ↦ by change dist i i ≤ R; simpa using hR) H X hX hH seq β k

end TNLean.Lattice.Locality
