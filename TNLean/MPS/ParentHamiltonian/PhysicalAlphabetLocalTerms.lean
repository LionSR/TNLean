/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalAlphabetEmbedding
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorPhysicalEmbedding

/-!
# Actual local parent terms under physical embeddings

The complementary pair projector is extended by the identity on the physical
coordinates outside that pair. Physical extension by zero intertwines these
actual extended local terms, including independent embeddings of the outside
configuration space. This is the local-to-global operator identity needed to
transport the varying-physical-space open parent Hamiltonian in PGVWC07,
arXiv:quant-ph/0608197, Theorem 9, source lines 1201–1220.
-/


namespace Matrix

variable {I J K L S T a b c : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype S] [Fintype T]
  [Fintype a] [Fintype b] [Fintype c]

/-- Extending an actual pair parent projector by the identity outside that pair
commutes with independent physical embeddings of both sites and the entire
outside configuration space. The local intertwining is derived from the actual
boundary ranges, not supplied as an assumption.
Source: PGVWC07, Theorem 9 proof, lines 1213–1220. -/
theorem pair_parent_localTerm_extend_physical
    (e : I ↪ J) (f : K ↪ L) (g : S ↪ T)
    (A : I → Matrix a b ℂ) (B : K → Matrix b c ℂ)
    (v : EuclideanSpace ℂ ((I × K) × S)) :
    ContinuousLinearMap.rightFiberwiseMap
        (LinearMap.range (rectangularPairBoundary
          (Function.extend e A 0) (Function.extend f B 0)))ᗮ.starProjection
        (((e.prodMap f).prodMap g).euclideanExtendByZero v) =
      ((e.prodMap f).prodMap g).euclideanExtendByZero
        (ContinuousLinearMap.rightFiberwiseMap
          (LinearMap.range (rectangularPairBoundary A B))ᗮ.starProjection v) :=
  ContinuousLinearMap.rightFiberwiseMap_extendByZero (e.prodMap f) g _ _
    (pair_parent_projection_extend_physical e f A B) v

end Matrix
