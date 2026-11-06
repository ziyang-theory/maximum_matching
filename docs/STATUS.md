# Theorem correspondence and remaining work

Source locators refer to the supplied 43-page arXiv v1 PDF, dated 7 December 2020. The checked theorems use the definitions in this project. Their trust and reproduction limits are in VALIDATION.md.

| Source claim/component | Lean declaration/module | Status and limits |
| --- | --- | --- |
| §3 p.8: simple alternating paths and augmentation | `AltPath`, `AltPath.augment`, `augment_path_edge`, `augment_off_path`, `augment_cardinality` | Proved; actual executable flip, exact cardinality gain +1. |
| §3 p.8: no augmenting path iff maximum | `Matching.isMaximum_iff_noAugmentingPath` | Proved for every finite simple graph on `Fin n`. See BERGE_PROOF.md. |
| §4 p.11: augment a disjoint path family | `AugmentingFamily.run_cardinality` | Proved for supplied disjoint augmenting paths; no shortestness/maximality/search result is assumed or asserted. |
| Defs 3.2/3.6 and Lemma 5.2 p.20 | `level_eq_some_iff`, `level_eq_none_iff`, `evenlevel_matched`, `matched_tenacity` | Proved, with `none = infinity`. Semantic minima use classical choice. |
| Theorem 5.3 p.20 | `AltPath.limited_bfs_honesty` | Both conclusions proved for all endpoint/interior parity and finite/infinite tenacity cases. |
| Defs 3.3–3.9, 6.1–6.4 | `Structure.lean` | Semantic min/max levels, predecessors, props, bridges, supports, eligibility and path-dependent bases defined. These definitions do not assume path-independent bases. |
| A last higher-tenacity vertex on each path | `AltPath.baseOnPath_exists_of_eligible`, `baseOnPath_unique` | Proved separately for each path. Equality across different shortest paths remains open. |
| Base/parity reductions toward Lemma 6.13 pp.24–27 | `Base.lean` | Path-relative bases are even/outer; global minimum tenacity implies prefix honesty; matched endpoints have the same base-value sets and equivalent unique-base assertions. These are proved reductions, not a proof of the common-base assertion. |
| DDFS graph-theoretic facts, §2 pp.6–8 | `DDFS.lean` | Layer descent/simplicity, highest-bottleneck existence/uniqueness when a bottleneck exists, and disjoint-path exclusion proved. **Not Theorem 2.1**: the DDFS procedure, outcome completeness, certificate trees and work bound remain open. |
| Def 4.1 p.15: bud lookup/compression | `BudForest` | Executable lookup and compression proved under a decreasing-rank invariant. Preservation of that invariant by actual MV petal updates remains open. |
| Algorithm 1 MIN p.13 | `Search.scan`, `scanCandidate`, `scanCandidates` | Local guards, assignments, tie retention and scan-once property proved. Candidate enumeration completeness and semantic level/bridge correctness remain open. |
| Algorithm 1 MAX p.13 | `Search.assignMax_sum` | Only local arithmetic proved, explicitly requiring `minlevel ≤ tenacity`; no support-finding algorithm is supplied. |
| Theorem 6.19 pp.29–33 | — | Open: simultaneous unique-base/blossom/bridge induction, internal path confinement/decomposition and laminarity. `HasUniqueBase` is only the target predicate. |
| Lemma 6.20 p.33 | — | Open: identify mutable bud roots with mathematical bases at the specified end-of-search-level instant. |
| Theorem 8.3 / Claim 8.4 pp.37–39 | — | Open: synchronized MIN/MAX computes semantic levels and DDFS discovers exactly the remaining support. |
| Lemma 8.5 p.40 | — | Open: complete phase, recursive path expansion and safe removal, maximality of shortest disjoint path family. |
| Theorem 8.6 p.40, correctness | — | Open: instantiate the complete concrete MV algorithm and prove maximum-cardinality output and termination. |
| Theorem 8.6 p.40, complexity | — | Open: phase bound, edge accounting and machine-model data-structure costs. No asymptotic runtime result is claimed. |

## Trust and interpretation

The intended mathematical input is a finite undirected simple graph. `Matching`'s symmetry and graph-membership fields specify legal inputs. `AltPath`'s simplicity and alternating-edge fields specify a legal path. Augmentation and family execution derive legal output matchings; validity is not an assumed postcondition. `DifferencePath.other` specifies which matching supplies each alternating edge, and the Berge proof constructs finite terminal paths rather than assuming a decomposition theorem.

`BudForest.decreases` is a genuine representation-invariant premise. It has not been connected to MV petal construction. DDFS's layered input and bottom-reachability properties likewise do not assert DDFS correctness. MIN/MAX labels are operational state, distinct from noncomputable semantic levels. This separation prevents local update lemmas from silently claiming that the phase computed the right labels.

`minlevel` and `maxlevel` are harmlessly totalized to infinity for an entirely unreachable vertex; the paper only defines them when a finite level exists. Eligibility preserves strict `t < l_m` by quantifying over every augmenting path. Support includes `t ≤ l_m`. The rank-free graph theory is generic in the vertex type; finite cardinality statements use `Fin n`.

The precise first unproved structural target and the investigated derivation are in [STRUCTURAL_OBLIGATIONS.md](STRUCTURAL_OBLIGATIONS.md). The completed path-splicing proof is explained in [HONESTY_PROOF.md](HONESTY_PROOF.md).
