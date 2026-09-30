# Physics-example openings

Follow-up to #8062 under #8011. Source snapshot: `fafa75e42`.
This is an audit of the exposition and its declaration links, not an independent
proof of every source theorem. References below are blueprint labels in
`blueprint/src/chapter/`; the review is
`Papers/2011.12127/TN-Review-main.tex`, Appendix A, lines 2318–2627.

The four checks are physical context and citation, the printed tensor or an
explicit relation to it, boundary data, and links for the stated properties.
Chapter 25 supplies a common positive-length periodic-trace convention in
`ch25_asymmetric_examples.tex`; individual sections state deviations.
Constructed examples must be identified as constructions, not attributed to a
paper merely because their physical target is familiar.

| Example / file suffix | Tensor and boundary evidence | Property evidence and remaining work |
|---|---|---|
| Product states (`ch15...product_states`) | Appendix A scalar tensor; `def:product_state_tensor`; open boundaries both 1. | `thm:product_state_mps`. The product tensor now precedes the general contraction; scalar boundary vectors and the two state-identification results are listed immediately after it. |
| GHZ (`ch15...ghz`) | Appendix A delta tensor, `def:ghz_tensor_d`; periodic trace, including the empty-chain convention. | `thm:ghz_d_mpv`, `thm:ghz_d_transfer`, `thm:ghz_d_not_injective`, `thm:ghz_d_symmetric`; parent results in `ch15...parent_hamiltonians`. |
| AKLT (`ch15...aklt`) | Now starts with the singlet-bond tensor, `def:aklt_tensor_review`; physical-basis and scalar/gauge changes in `thm:aklt_review_pauli_form` and `lem:aklt_review_gauge_bridge`. | Review symmetries, SPT and parent claims have `thm:aklt_review_symmetries`, `thm:aklt_review_spt`, `thm:aklt_review_parent_hamiltonian`; correlation-length subsection follows. The issue's claim that the opening starts from an unrelated representative is stale. |
| Majumdar–Ghosh (`ch15...majumdar_ghosh`) | Printed shorthand and its literal bond-six reading now appear in `def:majumdar_ghosh_review_tensor`; the singlet-bond representative is distinguished later. | `thm:majumdar_ghosh_review_mpv`, `thm:majumdar_ghosh_ground_space`, `thm:majumdar_ghosh_review_hamiltonian`; retain `rmp_majumdar_ghosh_tensor_gap`. Spin-exchange correction is #8353, PR #8396. |
| W (`ch15...w_state`) | Printed matrices and boundary vectors in `def:w_tensor`, explicitly identified in the opening. | `thm:w_state_identification`, `thm:w_state_periodic_closure`; general asymptotic bound remains #2947. PR #8386 changes the length-bound discussion and also covers #8352; avoid overlapping that text. |
| Cluster (`ch15...cluster_state`) | Now starts with `def:cluster_tensor_review`; periodic controlled-Z construction with short-ring conventions; gauge relation `lem:cluster_review_gauge`. | `thm:cluster_review_transferred`, `thm:cluster_z2z2_symmetric`, `thm:cluster_gauge_anticomm`; source parent results in the parent-Hamiltonian section. The opening concern in #8062 is stale. |
| Kitaev (`ch15...kitaev_chain`) | Printed matrices and twist in `def:kitaev_tensor`; graded physical meaning separated from ordinary matrix contraction. | `thm:kitaev_amplitudes`, `lem:kitaev_open_boundary`, `thm:kitaev_not_normal`; graded statements remain outside these results, with `rmp_kitaev_chain_bosonic_scope`. |
| CPSV16 Example 3.4 (`ch15...cpsv16_example_34`) | Source example number and diagonal matrices stated; periodic trace. | `thm:cpsv16_example_34_mpv`, `thm:cpsv16_example_34_cid`, `thm:cpsv16_example_34_not_rfp`. |
| Parent-Hamiltonian section (`ch15...parent_hamiltonians`) | Shared construction, not a new tensor example; explicit boundary-matrix local space. | Links back to the individual tensors. Do not require a second printed tensor for every parent theorem. |
| GHZ compression (`ch25...elementary_states`) | Standard GHZ target distinguished from constructed bond-four source; periodic trace stated. | `thm:asymex_ghz_state`, `thm:asymex_ghz_compression`; construction is not claimed to be the printed GHZ tensor. |
| Repeated-block product state (same file) | Constructed extension of a scalar product-state target; inherits explicit trace convention. | `thm:asymex_repeated_compression`, `thm:asymex_repeated_not_gauge`; boundary-detectable Jordan extension is separate. |
| CZX (`ch25...czx`) | Constructed input-phase convention distinguished from printed output-phase convention; source tensor `def:asymex_czx_review_tensor`, kernel bridge `thm:asymex_czx_review_kernel`. | The printed tensor now comes first, with its normalization caveat, trace boundary convention and links to the kernel, unitarity, square and normality results; the constructed input-phase tensor follows. |
| Decorated CZX (same file) | Separate representative from the cited domain-wall paper; periodic convention explicit. | `thm:asymex_czx_decorated_normal`, `thm:asymex_czx_decorated_anomaly_class`. Domain-wall statistics themselves remain #8013. |
| Levin–Gu / CZY (`ch25...czy`) | Section II source, explicit matrices and physical-index convention. | Kernel, printed reduction, nonsplitting and fusion have linked statements. The opening distinguishes the proved compression obstruction from arbitrary direct-sum decompositions and excludes the source's associator. Both missing source claims are now tracked explicitly in #8425. |
| Kramers–Wannier (`ch25...kramers_wannier`) | Sources and normalization factor `2^(N/2)` stated; periodic and short-ring conventions explicit. | The tensor definition now precedes operator notation; trace closure and links to the kernel, square, normality, coupling exchange and state action follow it. |
| Fibonacci (`ch25...fibonacci`) | Two-label restriction distinguished from full source alphabet; `def:asymex_fib_gsymbol_tensor`, `thm:asymex_fib_gsymbol_similarity`, `thm:asymex_fib_review_congruence`. | Added opening links to the dimension factors, bond similarity and physical normalization. These bridges resolve the old omitted-factor concern; full classification remains #8053. |
| Fibonacci anomaly (`ch25...fibonacci_anomaly`) | Continuation of the preceding example, not a new source tensor; regular two-block action distinguished from single-block no-go. | `thm:asymex_fib_anomaly_no_go` is explicitly restricted; not a uniqueness/classification theorem (#8053). |
| Ising (`ch25...ising`) | F-symbol convention, integer-ring scaling and periodic trace explicit; full G-symbol tensor and bridge now exist. | Added opening links to `def:asymex_ising_gsymbol_tensor` and `thm:asymex_ising_gsymbol_similarity`; normality at `thm:asymex_ising_normal`. |
| Group cocycles (`ch25...group_cocycle`) | Source construction; one-shift correction recorded in `glm23_pbc_group_mpo_single_shift`; explicit tensor and periodic kernel. | General kernel/fusion statements carry links; source-level multiplicity/pentagon and domain-wall claims remain #8045 and #8013. |
| Z2×Z2 (`ch25...z2z2`) | Constructed CZX-letter family, explicitly projective on odd rings; dressed exact representation distinguished. | `thm:asymex_z2z2_normal`, `thm:asymex_z2z2_anomaly_class`; full condensation-anomaly scope remains #8041. |
| Anomalous Z3 (`ch25...z3`) | Constructed decorated shift; source cocycle context, matrices, periodic self-loop convention explicit. | `thm:asymex_z3anomalous_cocycle_bridge`, `thm:asymex_z3anomalous_anomaly_class`, fusion/condensation statements. |
| Clock Z3 (`ch25...z3clock`) | Explicit clock matrices and cyclic gates; dressed trivial-cocycle kernel. | Corrected opening: triviality of the actual Else–Nayak class remains #8347. A trivial underlying cocycle alone does not prove the class of the dressed operators. |
| Mixed Bell bonds (`ch25...rfp`) | Explicitly a construction, with only the flag factor attributed to CPSV16 Example 4.12; cyclic bond regrouping and normalization stated. | Physical density formulas and fixed-point maps precede vertical products. No claim of a general classification. |
| Flagged Bell bonds (same file) | Constructed controlled flip and even-parity flag; source of flag factor identified. | Separate physical-state and fixed-point-map statements; retain distinction between positivity, normalization and fixed-point identities. |
| One-label and dimer vertical tensors (same file) | Derived vertical components of the displayed constructions; matrices and inherited periodic closure stated. | `thm:asymex_one_label_normal`, `thm:asymex_dimer_normal` and their compression entries; general length-dependent classification not asserted. |

## Remaining editorial work for #8062

The source relations now present on main should replace the stale list of known
missing bridges in the issue. The changes accompanying this audit expose the
CZX, Fibonacci and Ising bridges in their openings and remove the clock-class
overclaim. The product-state, CZX and Kramers–Wannier introductions now put their
example tensors before general operator or contraction notation, followed by
boundary data and property links. Chapter 15 now also links the boundary conventions and property results
for GHZ, AKLT, cluster, Majumdar--Ghosh, W, Kitaev, and CPSV16 Example 3.4.
The Kitaev tensor also precedes the boundary-state formula, and the
Majumdar--Ghosh property inventory follows its source tensor. The clock
section title no longer presupposes the unproved anomaly-class identification.
The W tensor precedes the general open-boundary definitions; its lower-bound
proof discussion is unchanged. The CZY, group-cocycle, and clock introductions
now state the trace boundary and link the proved operator and fusion properties,
with the associator, normality, and anomaly-class limits explicit. A uniform
opening property list now also covers the elementary GHZ, repeated-block and
Jordan examples, the anomalous Z3 family, and the Z2-by-Z2 family, with the
dressed-family detector restriction explicit. Fibonacci, its anomaly continuation, Ising, and the Bell-bond constructions
now also link their property results. The Fibonacci and Ising source tensor definitions now precede the
arithmetic conventions; quantum dimensions are stated at first use, followed
by the source-to-block relation, trace boundary, and property links.
A four-page XeLaTeX excerpt of the reordered Fibonacci and Ising openings
was visually checked: no clipping or overfull boxes. The excerpt does not
resolve full-document cross-references. Full rendering and a final review
of the four opening requirements remain before #8062 can close. Keep #8062 open until that pass is complete. Missing mathematics must
remain attached to the issues above, not acquire new `leanok` tags through an
editorial change.
