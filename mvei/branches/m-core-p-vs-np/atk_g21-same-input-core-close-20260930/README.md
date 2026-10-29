# m-core-p-vs-np — branch `atk/g21-same-input-core-close-20260930`

Lean sources from the branch `atk/g21-same-input-core-close-20260930` of the private repository `ShantiDraconis/m-core-p-vs-np`, commit `4c49b1a5f7c603bba3802f8a26258d89d56f6e9e` (2026-10-01T01:26:37+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 32 — closed 4, conditional 0, open 5, proof error 3, not reached 20, no result 0.
* History: 300 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `d451068c3fec626be3b9c97f8710c91ae176c37970680dec5ce18f4b54d2d539`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-p-vs-np/atk_g21-same-input-core-close-20260930/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P02BoundedComputationClose.copyLeftAll_true_of_guard` | `lean/MCore/Real/P02BoundedComputationClose.lean`:890 | aberto-sorry |
| `MCore.Real.P02BoundedComputationClose.copyLeftCell_true_of_guard` | `lean/MCore/Real/P02BoundedComputationClose.lean`:922 | aberto-sorry |
| `MCore.Real.P02BoundedComputationClose.copyRightAll_true_of_guard` | `lean/MCore/Real/P02BoundedComputationClose.lean`:906 | aberto-sorry |
| `MCore.Real.P02BoundedComputationClose.copyRightCell_true_of_guard` | `lean/MCore/Real/P02BoundedComputationClose.lean`:929 | aberto-sorry |
| `MCore.Real.P02BoundedComputationClose.copySymbolClauses_true_of_guard` | `lean/MCore/Real/P02BoundedComputationClose.lean`:876 | erro |
| `MCore.Real.P02BoundedComputationClose.setStateClauses_true_of_guard` | `lean/MCore/Real/P02BoundedComputationClose.lean`:847 | fechado |
| `MCore.Real.P02BoundedComputationClose.setSymbolClauses_true_of_guard` | `lean/MCore/Real/P02BoundedComputationClose.lean`:863 | fechado |
| `MCore.Real.P02BoundedComputationClose.transitionCaseCNF_true_of_guard` | `lean/MCore/Real/P02BoundedComputationClose.lean`:936 | erro |
| `MCore.Real.P02CanonicalClockReduction.canonicalClockFailure_closes_P02` | `lean/MCore/Real/P02CanonicalClockReduction.lean`:55 | erro |
| `MCore.Real.P02CanonicalClockReduction.canonicalClockFailure_closes_internal` | `lean/MCore/Real/P02CanonicalClockReduction.lean`:63 | aberto-sorry |
| `MCore.Real.P02CanonicalClockReduction.canonicalClockFailure_to_universalFailure` | `lean/MCore/Real/P02CanonicalClockReduction.lean`:42 | fechado |
| `MCore.Real.P02CanonicalClockReduction.normalized_failure_reflects` | `lean/MCore/Real/P02CanonicalClockReduction.lean`:23 | fechado |
| `MCore.Real.P02ExtensionalCoreAfterCookLevin.core_gap_closes_G21` | `lean/MCore/Real/P02ExtensionalCoreAfterCookLevin.lean`:76 | nao_alcancado |
| `MCore.Real.P02ExtensionalCoreAfterCookLevin.uniform_core_closes_G21` | `lean/MCore/Real/P02ExtensionalCoreAfterCookLevin.lean`:62 | nao_alcancado |
| `MCore.Real.P02ExtensionalCoreAfterCookLevin.uniform_core_closes_P02` | `lean/MCore/Real/P02ExtensionalCoreAfterCookLevin.lean`:67 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.boundedExecBits_strictly_longer` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:139 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.cnfCircuit_encoding_length_ge` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:44 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.encodeCircuit_length_ge_three` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:37 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.flatMap_length_three` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:74 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.initialCNF_length_le_tableau` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:129 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.initialLeftPart_length` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:92 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.no_extensionalRejectCompilerCore` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:202 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.no_sameInputTransport` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:178 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.radius_le_initialCNF_length` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:110 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.rejectCircuit_no_literal_same_input` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:159 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.sameInputCoreGap_false` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:192 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.setLeftCell_length` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:65 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.setSymbolClauses_length` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:58 | nao_alcancado |
| `MCore.Real.P02SameInputLengthFirewall.uniformExtensionalRejectCompilerCoreGap_false` | `lean/MCore/Real/P02SameInputLengthFirewall.lean`:221 | nao_alcancado |
| `MCore.Real.P02SameInputOnlyFrontier.SameInputCore.toG21` | `lean/MCore/Real/P02SameInputOnlyFrontier.lean`:47 | nao_alcancado |
| `MCore.Real.P02SameInputOnlyFrontier.SameInputCore.toP02Target` | `lean/MCore/Real/P02SameInputOnlyFrontier.lean`:53 | nao_alcancado |
| `MCore.Real.P02SameInputOnlyFrontier.sameInputCoreGap_closes_G21` | `lean/MCore/Real/P02SameInputOnlyFrontier.lean`:63 | nao_alcancado |
