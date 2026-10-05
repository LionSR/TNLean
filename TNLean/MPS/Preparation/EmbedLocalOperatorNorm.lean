/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalGibbsEmbedding
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Contractivity of local operator embeddings

Embedding a local matrix into a periodic chain is a star algebra homomorphism,
so it does not increase the Hilbert-space operator norm. This supplies the
volume-independent local interaction bound used in the finite-ring
Lieb–Robinson estimate of Hastings–Koma, arXiv:math-ph/0507008, Appendix A.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix.Norms.L2Operator

namespace MPOTensor

/-- Local operator embedding is contractive in the Hilbert-space operator norm.
This follows from contractivity of star algebra homomorphisms and supplies the
local norm bound needed in the finite-volume Lieb–Robinson estimate. -/
theorem norm_embedLocalOperator_le
    {d : ℕ} (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (A : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ‖embedLocalOperator L N hLN i A‖ ≤ ‖A‖ := by
  let φ : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ →⋆ₐ[ℂ] ChainOperator d N :=
    { toAlgHom := embedLocalOperatorAlgHom L N hLN i
      map_star' := fun X => embedLocalOperator_conjTranspose L N hLN i X }
  exact NonUnitalStarAlgHom.norm_apply_le φ A

end MPOTensor
