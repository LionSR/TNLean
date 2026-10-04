/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.EncodedUniformMergingCircuit

/-!
# Factorization of product-compatible computational basis encodings

Suppose that the final register depends only on its prescribed bond label,
and that the remaining registers are independent of that label. The full
injective encoding then factors as a product encoding. Injectivity of the
remaining-register encoding follows from injectivity of the full encoding;
it is not supplied separately.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open MPSTensor
namespace MPUCircuit

/-- The remaining-register encoding obtained by fixing one label of the final register. Its
injectivity follows from injectivity of the full encoding and the fixed final-register encoding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def prefixBasisEmbedding {d a b : ℕ} {ρ κ : Type*}
    (E : (ρ × κ) ↪ Cfg d (a + b)) (e : κ ↪ Cfg d b) (z : κ)
    (hsuffix : ∀ p, E p ∘ Fin.natAdd a = e p.2) : ρ ↪ Cfg d a where
  toFun p := E (p, z) ∘ Fin.castAdd b
  inj' p q h := by
    have heq : E (p, z) = E (q, z) := by
      funext i
      induction i using Fin.addCases with
      | left j => exact congrFun h j
      | right j =>
        exact (congrFun (hsuffix (p, z)) j).trans (congrFun (hsuffix (q, z)) j).symm
    exact congrArg Prod.fst (E.injective heq)

/-- Independence of the final-register label in the prefix and the prescribed suffix encoding
imply an exact factorization of the full basis embedding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem appendBasisEmbedding_prefixBasisEmbedding {d a b : ℕ} {ρ κ : Type*}
    (E : (ρ × κ) ↪ Cfg d (a + b)) (e : κ ↪ Cfg d b) (z : κ)
    (hsuffix : ∀ p, E p ∘ Fin.natAdd a = e p.2)
    (hprefix : ∀ p, E p ∘ Fin.castAdd b = E (p.1, z) ∘ Fin.castAdd b) :
    appendBasisEmbedding (prefixBasisEmbedding E e z hsuffix) e = E := by
  apply Function.Embedding.ext
  intro p
  funext i
  induction i using Fin.addCases with
  | left j =>
    change Fin.append _ _ (Fin.castAdd b j) = E p (Fin.castAdd b j)
    rw [Fin.append_left]
    exact (congrFun (hprefix p) j).symm
  | right j =>
    change Fin.append _ _ (Fin.natAdd a j) = E p (Fin.natAdd a j)
    rw [Fin.append_right]
    exact (congrFun (hsuffix p) j).symm

end MPUCircuit
