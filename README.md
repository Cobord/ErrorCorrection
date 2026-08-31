# ErrorCorrection

A Lean 4 / Mathlib project formalizing subjects related to ;linear error correcting codes:

- [`ErrorCorrection/`](ErrorCorrection/README.md) — linear error-correcting
  codes (`[n, k, d]_q`), Hadamard and Hamming code constructions, and
  "chromotopology": the graph structure (vertices colored, `N` differently
  colored edges per vertex, disjoint 4-cycles per color pair) obtained by
  quotienting `F_q^n` by a suitable code's coordinate-shift action.
- [`Supersymmetric/`](Supersymmetric/README.md) — Lie `1 | N`-dimensional superalgebras. The Adinkraic representations thereof are import the concepts from the `ErrorCorrection` portion.
- [`QuantumErrorCorrection/`](QuantumErrorCorrection/README.md) — the generalized Pauli and
  Clifford groups on finite sets of qudits, and quasi-local `*`-algebras (nets of local algebras
  over regions, with isotony and disjoint super-commutation) built from their group algebras.

See each directory's README for details on its files.