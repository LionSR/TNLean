# Ordered crossing Fourier blocks: the exterior-scalar factorization (2026-10-14)

`TNLean/PEPS/ParentHamiltonian/GraphCoordinateCanonicalParentTransport.lean`
carried a factorization of a crossing Fourier block of the ordered (unreversed)
bond orientation into a fixed exterior scalar times the regional Fourier
operation. Since #9280 the ordered parent transports are derived as the
unreversed case `o = fun _ => false` of the oriented ones, so the ordered
factorization lost its last consumer. #9362 removed it together with the two
private abbreviations only it used, and dropped its blueprint entry; the
ordered results in `ch24_peps_fourier_parent_transport.tex` now cite the
oriented regional-block theorem.

No call site remained in `TNLean/`, in `TNLeanTest/`, or on any open pull
request branch at removal time.

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.graphBoundaryExteriorCoordinateCoefficient` | `TNLean.PEPS.graphOrientedBoundaryExteriorCoordinateCoefficient` at `o = fun _ => false` |
| `TNLean.PEPS.mixedPhysicalProductMatrix_boundary_coordinates` | `TNLean.PEPS.mixedPhysicalProductMatrix_oriented_boundary_coordinates` at `o = fun _ => false` |

Both replacements live in
`TNLean/PEPS/ParentHamiltonian/OrientedCoordinateParentTransport.lean`.
