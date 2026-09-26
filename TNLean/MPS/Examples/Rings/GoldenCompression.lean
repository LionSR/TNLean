/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Rings.GoldenRing

/-!
# Golden compression: compression data with gauges over `ℤ[σ]`

**Source.** Construction of this development; no paper prints it. It packages the exact
arithmetic shared by the Fibonacci examples (`Examples/Fibonacci.lean`,
`Examples/FibonacciUnit.lean`, `Examples/FibonacciAction.lean`), whose entries come from the
F-symbols of arXiv:1511.08090, Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex`
lines 1250–1260.

**Formalized here.** In the worked examples over the ring `ℤ[σ]` of `GoldenRing.lean`, the
letters of the source tensor, of the target blocks, of the change of bond coordinates and of its
inverse are explicit matrices over `ℤ[σ]`, the conjugated letters `G B^i G⁻¹` are explicit
block-triangular matrices recorded through `B^i G⁻¹ = G⁻¹ K^i`, and every identity between them
is decided in exact arithmetic. The datum is the ring-generic
`MPSTensor.MultiBlockCompression.ofRing` along the embedding `goldenToComplex`.

## Main definitions

* `MPSTensor.MultiBlockCompression.ofGolden`: the multi-block compression datum assembled from a
  gauge over `ℤ[σ]` and the decided block structure of the conjugated letters.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

open scoped Matrix

namespace MPSTensor

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {Dι : ι → ℕ} {S : Finset ι}

/-- **A multi-block compression datum from a gauge over `ℤ[σ]`.** The letters of the source
`B` and of the targets `C s` are the entrywise embeddings of the matrices `Bg` and `Cg` over
`ℤ[σ]`; the matrices `G` and `Ginv` over `ℤ[σ]` are mutually inverse; the conjugated letters
`G Bg^i Ginv` are the matrices `K i`, recorded through the identity `Bg^i Ginv = Ginv K^i`; and,
read along the bond coordinates `τ`, each `K i` is block upper triangular for the ordering `ord`
with the target `Cg s` on the diagonal block of the slot `s` and zero on every zero slot. This
is `MultiBlockCompression.ofRing` for the gauge `gaugeOfRingMatrix` over `ℤ[σ]`. -/
noncomputable def MultiBlockCompression.ofGolden {B : MPSTensor d DB}
    {C : ∀ s, MPSTensor d (Dι s)} (z : ℕ) (ord : BlockIndex S z ≃ Fin (S.card + z))
    (τ : BlockSpace Dι S z ≃ Fin DB) (Bg : Fin d → Matrix (Fin DB) (Fin DB) GoldenInt)
    (hB : ∀ i, B i = complexOfGolden (Bg i))
    (Cg : ∀ s, Fin d → Matrix (Fin (Dι s)) (Fin (Dι s)) GoldenInt)
    (hC : ∀ s i, C s i = complexOfGolden (Cg s i))
    (G Ginv : Matrix (Fin DB) (Fin DB) GoldenInt) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (K : Fin d → Matrix (Fin DB) (Fin DB) GoldenInt) (hK : ∀ i, Bg i * Ginv = Ginv * K i)
    (htri : ∀ (i : Fin d) (x y : BlockSpace Dι S z), ord y.1 < ord x.1 → K i (τ x) (τ y) = 0)
    (hmatched : ∀ (i : Fin d) (s : ι) (hs : s ∈ S) (p q : Fin (Dι s)),
      K i (τ ⟨Sum.inl ⟨s, hs⟩, p⟩) (τ ⟨Sum.inl ⟨s, hs⟩, q⟩) = Cg s i p q)
    (hunmatched : ∀ (i : Fin d) (t : Fin z) (p q : Fin 1),
      K i (τ ⟨Sum.inr t, p⟩) (τ ⟨Sum.inr t, q⟩) = 0) :
    MultiBlockCompression B S C :=
  MultiBlockCompression.ofRing goldenToComplex ord τ
    (gaugeOfRingMatrix goldenToComplex τ G Ginv hG hG') K (fun i => by
      rw [conjMatrix_gaugeOfRingMatrix goldenToComplex τ hG hG' (hB i), Matrix.mul_assoc, hK,
        ← Matrix.mul_assoc, hG, Matrix.one_mul])
    Cg hC htri (fun i s p q => hmatched i s.1 s.2 p q) hunmatched

end MPSTensor
