# Shared owner contract and narrow verification

Code owner head: b992c791dc35580cb84e1161150b98b9963284bb.
QIC pin: 729428582b78ab7529b3796099193649f947354a.
Only the six shared-assigned production files have changed after the main merge.
Other worker file sets and the running original caches were not edited.

Five shared modules passed direct Lean compilation and strict, using a separate
output overlay. LocalHamiltonian and chain Hamiltonian were checked at b2c72008;
their sources are byte-identical at b992c791. MarginalTails, ProductForm and
RectangularHamiltonian were checked at b992c791. This is not Lake or whole-library
validation. Exact commands/PIDs/times and initial environment failure are retained.
Read-only symlinks expose matching warm artifacts; each generated target is an
independent real file, and symlinks are unlinked before generation, preventing
writes into the original cache. No imported payload was exported.

## API for consumer workers

- ChainInteraction/DomainInteraction/PlaneInteraction are the sole QIC objects.
  Use term, mem and hamiltonian, not bundled supported/hermitian/norm_le/operator.
- MarginalTails quantitative results take explicit term Hermiticity and term norm
  bound (the former bundled hypotheses), followed by their existing hJ/hDelta.
  These positive-gap concentration theorems retain genuinely needed premises.
- PlaneInteraction.trotterProduct and hasProductForm_trotterProduct take neither
  J nor Hermiticity: their proofs use support alone.
- RectangleInteraction.toAreaLawHamiltonian takes ONLY Phi.
- Phi.isHermitian_toAreaLawHamiltonian_term gives term Hermiticity of the converted
  Hermitian-part interaction. Phi.norm_toAreaLawHamiltonian_term_le takes hhJ.
- Phi.toAreaLawHamiltonian_hamiltonian takes TOTAL-Hermitian hH only.
- Phi.projectorGap_toAreaLawHamiltonian takes hH, hOmega, projector-PSD hgap, hmem,
  with implicit E0/Delta/Omega. No J or term norm bound argument remains. The output
  is transported norm/PSD/groundSpace membership for arbitrary Delta. Do not add
  termwise Hermiticity, positive Delta, J>=0, or singleton assumptions to callers.

ComponentReduction is not validated. Its remaining 13-module closure is recorded;
BufferDiscount, WindowCounting and AreaLaw still contain old ChainHamiltonian
references and are owned by the MPS worker. Do not paper over this with aliases.

## Fixture/review gate

All five existing fixtures must remain. The shared mixed wrapper file is unchanged
until the requested full 69b8 preaudit can be read and both consumer API lanes settle.
The report was not available through the accessible history search; this is an
explicit outstanding input, not a completed review. Visible constraints are retained:
total Hermitian must not become termwise; arbitrary J must not gain J>=0; arbitrary
Delta keeps norm/PSD/member; empty physical intersections are not zero-size IntRects.

Before integrating worker commits, compare their changed paths with their exclusive
allocation (including fixture ownership), confirm exact base/main/pin and recorded
checks, and inspect all cross-owner API calls. Integrate MPS and PEPS on disjoint sets,
then the shared wrapper, then documentation/signature synchronization and combined
verification. No existing PR has been updated and this tree remains unmergeable.
