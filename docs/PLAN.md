# Execution plan

The requested end result is a Lean 4 verification of the concrete Micali–Vazirani maximum-matching algorithm described by the supplied PDF, including a clear separation between functional correctness and complexity. This plan was presented before implementation. Completion of a foundation does not mark the full target complete.

1. **Identify the source and target.** Read the supplied paper, hash the exact version, map the definitions and theorem dependencies, and apply the new `fv-paper-formalization` and `fv-lean` skills. **Completed.** See SOURCE_MAP.md.
2. **Pin and build the environment.** Reuse installed Lean 4.34.0; create a reproducible Lake project and use Std with no external dependencies. **Completed.**
3. **Prove matching/path foundations.** Define valid graphs, matchings, simple alternating paths, augmentation, cardinality and semantic levels independently of desired correctness. Prove augmentation and optimality. **Completed for the recorded representation**, including a complete Berge criterion.
4. **Develop MV structure and operations.** Prove matched-edge identities and limited BFS honesty; implement local MIN updates and bud compression; reconstruct DDFS and blossom/base arguments. **Partially completed.** Lemma 5.2 and full Theorem 5.3 are proved. Complete DDFS and Theorem 6.19 remain open.
5. **Assemble the actual MV algorithm.** Prove the complete phase returns a maximal family of disjoint shortest augmenting paths; prove path extraction/removal, outer-loop termination and maximum cardinality; separately count phases and operations. **Open.** Execution of a supplied disjoint path family is proved, but finding that family by MV is not.
6. **Check correspondence and reproduce.** Independently review statements and assumptions, build a source-only copy, print transitive axioms and replay the bundled kernel. **Performed for the completed development.** This validates the checked subset; it does not close steps 4–5.

## Decisions during execution

- Use a symmetric partial mate function for a matching, with graph-edge membership proved in its data. An indexed path stores distinct vertices and explicit alternating edges. These are input definitions; the result matching's validity is derived by the augmentation proof.
- Preserve infinity rather than totalizing unreachable levels to zero. The theorem development treats all finite/infinite combinations.
- Prove the central path-splicing argument before building a large unproved blossom interface. Full limited BFS honesty was reconstructed with actual simple path splices, first-intersection arguments and parity reductions.
- Prove Berge's criterion internally using deterministic paths in the union of two matchings, endpoint injection and finite counting; do not accept optimality as an oracle premise.
- Keep a precise obstruction for DDFS reconstruction: ordinary visited-node skipping fails at a collision, and permanent ownership fails on a five-vertex rerouting example. See DDFS_OBLIGATIONS.md. These are counterexamples to naive translations, not to MV.
- Do not rename exhaustive search, generic augmentation, or a conditional phase oracle as an MV implementation. There is deliberately no purported complete `micaliVazirani` function yet.
