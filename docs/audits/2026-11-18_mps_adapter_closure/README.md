# MPS canonical Interaction adapter closure

Code source: `42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d`.
Parent: `dccc85e5607077b51822664e9d475287d300d607`.
QICLean: `729428582b78ab7529b3796099193649f947354a`.

This evidence-only publication changes no production source and records no Lean
compilation. The existing code branch remains unchanged. The closure is an
explicit import-line reverse graph, not a proof of elaboration or cache validity.
It contains 25 paths including three changed targets. Individual reverse-consumer
counts excluding each target are 12, 14 and 13, respectively. Aggregators are
included; external dependency modules are not downstream repository consumers.

`import-closure.json` is byte-identical to the original local handoff. Its `base`
field identifies the original graph snapshot. Regeneration at both parent and
code source produced identical bytes because this patch changes no imports.
`manifest.json` records the code tree, pin, toolchain, all 25 source SHA-256 values,
and hashes for the generator and closure file. These hashes do not certify any
existing compiled artifacts.

Run from a repository containing the fixed source commit:

```sh
python3 docs/audits/2026-11-18_mps_adapter_closure/generate.py 42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d > /tmp/mps-adapter-closure.json
cmp /tmp/mps-adapter-closure.json docs/audits/2026-11-18_mps_adapter_closure/import-closure.json
```

The generator reads committed files through Git; it does not switch branches or
write build artifacts. Its lexical scan recognizes explicit one-line imports;
it is not a Lean parser or an elaborated dependency analysis. Warm validators
must compile the three changed targets at the matching pin and account for
consumer validation separately. No build, strict run or cache mutation was made
for this publication.
