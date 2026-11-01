# Bounded pure-state conversion on the original physical ports

Source: Piroli, Styliaris and Cirac, [arXiv:2103.13367v3](https://arxiv.org/html/2103.13367v3),
main-text paragraphs “Quantum circuits and LOCC” and “State transformations with QC and LOCC”,
HTML lines 45–53. The source permits “ancillary spins (initialized in a product state)”
and counts nearest-neighbor gates on physical qudits, with onsite unitaries free.

## Exact mathematical statement

Fix physical dimension d≥2 and an intermediate local dimension bound B before the chain
length. For N≥2 and an actual B-bounded native channel Ψ of depth T taking
|ψ><ψ| to a normalized |φ><φ|, the actual compiled unitary has physical depth at most
2 ceil(log_d B) T and satisfies

U(V_port ψ ⊗ |0_A>) = V_port φ ⊗ η,

where η is derived and normalized. V_port is the existing explicit product isometry:
it stores the original qudits on the original physical ports and initializes their
designated data/scratch memory to zero. That memory is consequently zero in the actual
final vector. The same U also realizes Ψ on every logical operator after its final
partial trace; this is stronger than an identity on one input density matrix.

## Derived ingredients

- Main’s `exists_physicalPortIO` constructs the actual compiled channel Γ and proves
  Γ J_port = J_port Ψ at depth 2 ceil(log_d B) T.
- `registerEncoding_isIsometry` normalizes the actual encoded target vector.
  `mul_vecMulVec`, `vecMulVec_mul` and `star_mulVec` identify its pure projector with
  the existing code-initialization channel on |φ><φ|.
- Draft #10334’s `exists_appended_unitary_dilation_pure_output` derives the actual U
  and η from that actual channel output, preserving all physical ports and ownership.
- Composing its all-operator channel identity with J_port retains the exact native
  input/output identity. No simulator, decoupling, kernel, or reset hypothesis is added.

The new statement does not assert environment reset or a spatial product environment.
It does not duplicate #10350’s regrouping of actual channel protocols. Adaptive source
block counts/control restrictions, approximate pure-output robustness, and the
unrestricted enlarged-site relation remain separate open obligations under #8640/#8622.

## Verification boundary

The new proof was first written without a local Lean build. Its Blueprint statement
and proof are tagged `leanok`; the declaration compiles in the full root build of the
merge train `train/wielandt-singletons`, which combines it with current main.
