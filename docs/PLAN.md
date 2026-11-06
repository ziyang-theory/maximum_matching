# Correctness development

The requested result is a Lean 4 verification of correctness and termination
for the executable maximum-matching algorithm described in this repository.
The source correspondence and representation scope are recorded in SOURCE_MAP.md.

1. **Identify the source and target.** Hash the supplied paper and map definitions and theorem dependencies. Completed; see SOURCE_MAP.md.
2. **Pin the environment.** Use Lean 4.34.0 and Std, with no external package dependencies. Completed.
3. **Prove matching/path foundations.** Define legal graphs, matchings, simple alternating paths, augmentation, cardinality and semantic levels independently of desired correctness. Prove augmentation and the Berge criterion. Completed.
4. **Prove structure and search operations.** Establish bases, blossom confinement and laminarity, the unique current-tenacity bridge, DDFS correctness and termination, and actual MIN/MAX stage preservation and discovery. Completed.
5. **Assemble the solver.** Compute path expansion, prove safe deletion and maximal shortest-family discovery, discharge both concrete search contracts, and prove outer-loop termination and maximum cardinality. Completed; see BLOCKING_PHASE_PROOF.md.
6. **Review and reproduce.** Check statements and assumptions independently, rebuild a source-only copy, audit transitive axioms, and replay the bundled kernel. The final records are in `validation/`.

## Representation decisions

- Matchings use a symmetric partial mate function whose edges belong to the graph. Indexed paths store distinct vertices and alternating edges. Augmentation derives output matching validity.
- Semantic levels retain infinity for unreachable vertices.
- The structural proofs use actual simple path splices and first-intersection arguments rather than assumed blossom conclusions.
- The Berge criterion is proved internally from the union of two matchings.
- DDFS collision recovery handles the failures of ordinary visited-node skipping and permanent ownership. See DDFS_OBLIGATIONS.md.
- Runtime search uses actual MIN/MAX/DDFS states and stored routes. The live deletion representation removes touched bud fibers and proves preservation of the arms needed for maximality; exact intermediate-state equivalence to literal source deletion is outside the claim.
