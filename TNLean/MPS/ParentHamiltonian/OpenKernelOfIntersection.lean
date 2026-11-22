/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian

/-!
# Exact canonical open kernels from one-step intersections

The one-step intersection identities determine every larger boundary space
from contiguous local constraints. A canonical open kernel vector satisfies
all such constraints, so the intersection identities imply exact open
kernels. The intersection property is supplied explicitly in these two
criteria; no injectivity or tensor normalization is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.13),
Lemma existenceinteraction; PGVWC07, arXiv:quant-ph/0608197, Theorem 12.
-/

open Filter
open scoped BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- Iterating one-step intersections identifies the kernel of the Hamiltonian of the parent
interaction on the open chain at every volume at least the interaction range. The intersection
assumption is explicit; no injectivity is assumed. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.10)--(3.13), Lemma existenceinteraction; PGVWC07, arXiv:quant-ph/0608197,
Theorem 12. -/
theorem ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_restriction_intersection
    [NeZero d] (A : MPSTensor d D) {R N : ℕ} (hR : 0 < R) (hRN : R ≤ N)
    (hStep : ∀ M, R ≤ M →
      ((⨅ b, (groundSpace A M).comap (restrictLastₗ b)) ⊓
        ⨅ a, (groundSpace A M).comap (restrictFirstₗ a)) = groundSpace A (M + 1)) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
      groundSpaceES A N := by
  apply le_antisymm ?_ (groundSpaceES_le_ker_hamiltonian_parentChainInteraction A R N)
  intro v hv
  exact (mem_groundSpaceES_iff A N v).mpr
    (contiguous_mem_of_restriction_intersection_submodules (fun M => groundSpace A M) hR hRN
      hStep fun s hs τ ↦
        contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv
          s hs τ)

/-- An eventual one-step intersection property gives one positive threshold beyond which the
Hamiltonian of the parent interaction on the open chain has, for every range, the open MPS
boundary-condition space as its kernel. Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma
existenceinteraction and equations (3.10)--(3.13). -/
theorem exists_ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_eventually_intersection
    [NeZero d] (A : MPSTensor d D)
    (hStep : ∀ᶠ n in atTop,
      ((⨅ b, (groundSpace A (n + 1)).comap (restrictLastₗ b)) ⊓
        ⨅ a, (groundSpace A (n + 1)).comap (restrictFirstₗ a)) = groundSpace A (n + 2)) :
    ∃ R₀, 0 < R₀ ∧ ∀ R N, R₀ ≤ R → R ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) =
        groundSpaceES A N := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hStep
  refine ⟨n₀ + 1, Nat.succ_pos _, fun R N hR hRN => ?_⟩
  apply ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_restriction_intersection
    A (by omega) hRN
  rintro (_ | n) hn
  · omega
  · simpa only [Nat.add_assoc] using hn₀ n (by omega)

end MPSTensor
