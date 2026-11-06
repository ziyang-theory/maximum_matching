# Additional checked proofs and remaining boundary

This extension adds proofs to the existing partial MV formalization. It does
not complete Theorems 6.19, 8.3 or 8.6, or instantiate the phase search contracts.
Source correspondence uses the supplied arXiv v1 PDF (7 December 2020), SHA-256
`05f3cfcc51c12eea0537cb9892a9bc832f8f175fc507b2b0f8228b68e922996c`.
The source hash was rechecked. Relevant cached pages were read after consulting
the authorized paper-library navigation and targeted matching search.

## Checked additions

| Source step | Main declarations | Actual guarantee |
| --- | --- | --- |
| Higher-tenacity predecessor reduction | `AltPath.equal_predecessor_parity_bases_agree`, `parity_bases_agree_of_predecessor_ge` | Handles predecessors of equal or greater tenacity. Only the equal case needs the already-established common base at a strictly smaller minlevel. Lower-tenacity vertices elsewhere are allowed. |
| Cut a shortest path at a lower blossom's boundary | `IsBase.threshold_prefix`, `blossom_threshold_prefix`, `AltPath.predecessor_blossom_prefix` | Constructs an actual shortest even prefix and preserves every higher-threshold base value. The last theorem covers the odd minlevel path; the general opposite-path argument is now completed below. |
| Weighted paths, pp.31–32 | `DDFS.BlossomWeightedMatching.realize`, `realize_disjoint` | Constructs simple alternating paths of length equal to the sum of actual segment lengths; disjoint compressed paths expand disjointly. Requires actual edge segments, compatible matching phases, target-blossom interior containment and high-tenacity core vertices. |
| Minimum-tenacity edge witnesses | `IsBase.minimum_exit_segment`, `minimum_exit_reverse` | Extends an actual shortest relative blossom path by a compatible exit edge; freshness follows from tenacity, with an explicit distinct-base condition. Reversal gives the target-blossom orientation. |
| Lemma 8.1, pp.36–37 | `matched_bridge_levels`, `unmatched_bridge_tenacity` | For finite bridge tenacity, matched endpoints are inner with equal odd minlevels. An unmatched bridge bounds an outer endpoint's tenacity non-strictly and an inner endpoint's strictly. No shortest-augmenting-length premise is needed. |
| Theorem 8.3, Task 1 ingredients, p.38 | `AltPath.minlevel_last_predecessor_honest`, `predecessor_iff_level_guard` | The final predecessor of any minlevel path is honest, including infinite endpoint tenacity; characterizes exactly which oriented edges can assign the next minlevel. Earlier prefixes may be dishonest. |
| Executable MIN scans | `Search.scan_assigns_semantic`, `scan_rejects_bridge`, `scanCandidates_preserves` | Under explicit earlier-level and scan invariants, admitted scans assign real minlevels/props, rejected unseen edges are bridges, and candidate folds preserve label soundness and earlier assignments. `initial_scanCandidates_labelsSound` establishes initial-level soundness unconditionally for any enumeration. |
| Theorem 2.1 abstract work, pp.6–8 | `DDFS.Machine.trace_scanned_bound`, `trace_bottleneck_local_bound`, `trace_disjoint_local_bound` | Every initialized trace uses at most four transitions per scanned edge plus three; terminal traces are bounded by `4 * |E_b| + 3` or `4 * |E_p| + 3`, counting distinct directed edges in the union of root-to-output paths. |

## Subsequent goal progress

| Source step | Checked additions | Remaining boundary |
| --- | --- | --- |
| Full layered DDFS output | `DDFSExecutable`, `DDFSTrees`: deterministic execution, global parent trees, exact color coverage and overlap | All-pair/vertex enumeration and forest postprocessing are executable; their concrete costs are separate from the transition bound. |
| Complete finite MIN | `MinComplete`: initialized/preserved record invariants, all next minlabels and exact predecessor lists, prior-level frontier derivation | Later frontiers depend on the preceding MAX labels, not a same-stage completeness assumption. |
| MAX and bridge buckets | `MaxCorrectness`, `MaxBridgeRefresh`, `BridgeComplete`: semantic assignment, actual previously-unregistered incident-edge refresh, and all current-tenacity bridge buckets under initialized/preserved state invariants | DDFS support discovery and the synchronized complete phase remain open. |
| Stage assembly | `SearchStage`: initializes every state invariant and executes MIN plus MAX label/refresh lists while preserving them | The complete current-tenacity vertex list remains an explicit support-discovery input; this is not a concrete complete MV phase. |
| Established blossom chains | `BlossomRelative`: each boundary is the last high vertex on a shortest path; its suffix is relatively shortest | Suffix tenacity is bounded; blossom membership is not inferred from that bound alone. |
| Higher-tenacity geometry | `GeneralHighGeometry`: triangular minlevels and exact midpoint bridge tenacity for adjacent high vertices | Edges involving lower-tenacity vertices still need the simultaneous structural induction. |
| Actual compressed segments | `GeneralWeightedEdges`, `GeneralWeightedTop`: ordinary low stretches and even low-top paths with exact expanded lengths | Base existence and confinement are explicit hypotheses at the lower contraction threshold. They are not established at the current induction threshold. |
| Low-top weighted realization | `WeightedTopExpansion`: core realization avoids its initial blossom; prepend a real low-top segment, retaining simplicity and disjointness | Selecting all edges of the source's `H_v` and deriving its bridge length budgets remain open. |
| Weighted bridge detour | `WeightedBridgePath`: reverse the free-ending realized arm, cross the actual bridge, append the other arm; exact potential-based length | Current-tenacity edge-budget identity remains a matching-graph construction obligation. |
| Original low-path localization | `GeneralLowLocalization`: locate a preceding high boundary for each low vertex before an honest high endpoint | Uses the lower-threshold confinement induction hypothesis; no global avoidance is assumed. |
| Direct base rerouting | `GeneralBaseReroute`: disjoint boundary-suffix reroute, high-prefix exclusion, strict first-hit indices, and derived full avoidance for an absent boundary with `C≤B` | All remaining cases are now discharged by `GeneralStructureStep`, described below. |

Root and independent agents reviewed the new executable DDFS, MIN/MAX, base
rerouting and weighted-path declarations. The weighted review checked the target
orientation, even top-edge phase, exact segment lengths, and lower-threshold
scope of the induction hypotheses. The DDFS review checked saturation coverage,
fixed parent functions, and either root equal to the bottleneck. No additional
logical or assumption-hiding issue was found within that scope.

The finite premise in the bridge theorem is intentional. A literal reading that
allows infinite-tenacity unreachable matched edges does not justify classifying
their endpoints as inner. The checked result covers the finite bridge buckets
used by MIN/MAX.

## Proof details that matter

For MIN, a shorter path to a penultimate vertex either already contains the
original endpoint, giving a too-short prefix, or extends freshly to it, again
contradicting its minlevel. For mixed bridge endpoints, the source's informal
path concatenation is replaced by a simple-path case split. An existing
occurrence gives an odd prefix or lies in the proved low-tenacity suffix;
otherwise the extension is fresh.

The DDFS bounds assume the source's layered input and bottom reachability.
The DDFS potential charges only the red stack below Barrier, together with the
green stack and constant mode credit. Restoring a saved red path places Barrier
at its endpoint and therefore does not restore charged stack depth. Scanned
sources have root-discovery paths. Scanned targets have continuations to the
reported outputs, including after abandoned branches in the disjoint outcome.
This connects the transition bound to the source's output-local edge regions.
It does not price adjacency selection, exhaustion tests or stored-path updates.

Weighted expansion separates matching phase from assigned DDFS layer and from
actual segment length. Independent review caught an initial source-blossom
orientation mismatch; the final interface places interiors in the target's
blossom for descending compressed edges. The realization proof inducts over
path prefixes and derives separation from blossom laminarity.

## Independent review and validation

Independent agents inspected the new statements, assumptions and source
correspondence. Separate reviewers checked the base steps, MIN/bridge proofs,
weighted concatenation, minimum exit witnesses, global DDFS work and output-local
DDFS work. The orientation issue above was repaired and rechecked. No other
mathematical or assumption-hiding issue was found in that review scope.

Targeted builds and principal-theorem axiom reports passed. Kernel-checked
boundary examples include both edgeless DDFS outcomes, odd-prefix segment joins,
reversal phase and zero-length cases. Permanent DDFS examples are in
`DDFSWorkExamples.lean`; the segment checks were separate scratch examples.
The final source-only build, complete public-declaration axiom audit and bundled
kernel replay are recorded in `validation/summary.json` and its linked logs.
These checks validate this source snapshot under the trust limits in
[VALIDATION.md](VALIDATION.md); they do not establish the missing full algorithm.

## General base and confinement completion

`GeneralStructureInduction` proves `general_unique_base` and
`general_blossom_relative_confined` without structural oracle premises. Its
joint tenacity induction calls the complete minlevel base induction and the
new path-length confinement induction. [GENERAL_BASE_REMAINING.md](GENERAL_BASE_REMAINING.md)
records the full route and actual source correspondence.

Independent review covered the ordered and unordered minimal-witness cases,
short-path closure, the two simple reverse splices, actual iterated-base joins,
small-edge boundary equality, first-entry selection and tail replacement,
honesty of the preceding prefix, and the final simultaneous induction. Reviewers
checked that every lower confinement call has cutoff `t−2`, every same-tenacity
base call has a smaller minlevel in the inner induction, and every confinement
length call has a strictly shorter original prefix. No current-confinement
premise or assumed rerouting conclusion remains in the public theorems.

Principal target builds and axiom reports passed, using only `propext`,
`Classical.choice` and `Quot.sound`. The complete source-only build, public
axiom audit and kernel replay are recorded with the final source hashes in
`validation/`.

## General structural completion and actual bud contraction

`GeneralSuffixBase` proves that the actual base of each suffix vertex occurs
somewhere on the original suffix. `GeneralRelativeBaseTransfer` transfers the
property to every shortest relative path through the proved simple join.
`GeneralEdgeBounds` proves the relative edge-tenacity bound by strong cutoff
induction and the honest-prefix/first-entry decomposition. Neither theorem
retains lower-cutoff structure as an assumption.

`GeneralBridge` uses strong path-length induction: an honest terminal edge is
either the unique bridge of current tenacity or a prop leaving a shorter
maxlevel prefix. A dishonest predecessor is handled at the first lower-blossom
entry; all later edges have lower tenacity. Lower eligible-cutoff facts suffice,
so the public theorem includes `t = l_m`. Its uniqueness concerns current-tenacity
bridges, not every bridge. `GeneralSupport` derives an actual maxlevel witness
and proves semantic support coverage without asserting disjoint supports or
concrete discovery.

Independent reviewers checked the first-entry transport, reversed-tail edge
indices, recursive decreases, threshold equality and public hypotheses.
`BudLink` additionally implements guarded root merging with exact class behavior;
`DDFSBud.executeAndContract` runs DDFS and contracts its actual computed region.
Strict layered paths supply rank guards under explicit representation premises.
Executable regressions cover pre-existing descendants, unselected classes,
abandoned search branches and the disjoint outcome. These operation proofs do
not identify the region with matching-specific bridge support.

## Still required for completion

Concrete matching-derived
DDFS support, mutable petal/bud correspondence, complete MIN/MAX search,
recursive expansion/removal and maximal shortest-family discovery also remain.
The `Complete` and `ShortestBlocking` contracts are still uninstantiated for
MV. Executable DDFS and its local abstract transition bounds do not establish
the concrete representation or whole-algorithm running-time bound.
