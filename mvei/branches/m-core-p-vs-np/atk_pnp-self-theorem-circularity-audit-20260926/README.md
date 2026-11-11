# m-core-p-vs-np — branch `atk/pnp-self-theorem-circularity-audit-20260926`

Lean sources from the branch `atk/pnp-self-theorem-circularity-audit-20260926` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `1071a1d3602a89ab0ecd3df3611f2b2f773b3a15` (2026-09-26T23:42:27+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 5 — closed 1, conditional 0, open 0, proof error 4, not reached 0, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `02e27ea0330a8947f815425754811f4ca4b58c5d6fa3f4ded28b12eefcf2a0ef`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_pnp-self-theorem-circularity-audit-20260926/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Hardening.SSEWitnessConstruction.construction_closes_p02` | `lean/MCore/Hardening/SSEWitnessConstruction.lean`:41 | fechado |
| `MCore.Real.PNPSelfTheoremCircularityAudit20260926.sat_not_in_p_to_universalFailure` | `audit/PNP_SELF_THEOREM_CIRCULARITY_AUDIT_20260926.lean`:12 | erro |
| `MCore.Real.PNPSelfTheoremCircularityAudit20260926.self_theorem_route_exactly_circular` | `audit/PNP_SELF_THEOREM_CIRCULARITY_AUDIT_20260926.lean`:27 | erro |
| `MCore.Real.PNPSelfTheoremCircularityAudit20260926.self_theorem_route_to_p02` | `audit/PNP_SELF_THEOREM_CIRCULARITY_AUDIT_20260926.lean`:32 | erro |
| `MCore.Real.PNPSelfTheoremCircularityAudit20260926.universalFailure_to_sat_not_in_p` | `audit/PNP_SELF_THEOREM_CIRCULARITY_AUDIT_20260926.lean`:20 | erro |
