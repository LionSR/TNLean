# Common-source regression checks

These checks use the exact nine-module source revision
`b8864ae6ca2a3fbd5ecf0989e682a38d33ee02a6`.

The empty-family case invokes the final finite-source preparation theorem and
shows that the pair of two distinct parties still occurs in its reference list.
The other cases use one- and two-dimensional branch halfspaces, establish
separation of their orthogonal sectors, preserve normalization of the pair
sources, and recover the nonreal phase `I` after projecting both source halves.

The regression module compiled directly with every package Lean option and
warnings treated as errors. The separate audit imports its compiled artifact;
all seven theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`.
Only the audit disables the linter for its intentional `#print axioms` commands.
No Lake command or repository-cache mutation was used.

The command records retain the precise temporary paths and environment.
`checked-sources.json` records the committed source and imported artifact hashes
of the nine modules. The parent evidence directory records their full dependency
closure. Compressed files use deterministic gzip with zero modification time;
`artifact-sha256.json` records hashes of the uncompressed files and regression
artifact. The compiled regression artifact itself is not committed.
