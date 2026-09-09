# Verification Record

Verification date: 2026-09-09.

- Lean: `4.29.0`.
- Mathlib: `8a178386ffc0f5fef0b77738bb5449d50efeea95`, pinned by `lake-manifest.json`.
- `lake build`: passed, with 8353 build jobs; existing dependency and module caches were reused.
- `python3 scripts/check_axioms.py`: passed, with 297 checks across four inventories and 18 further checks in two interface tests, for a total of 315.
- Both interface tests compiled successfully. Every reported axiom dependency was among `propext`, `Classical.choice`, and `Quot.sound`.
- All 104 library modules are reachable through the import graph of the root module `ArithDyn.lean`.

The build ran on a server. A file-by-file comparison confirmed identical SHA-256 hashes for all 111 Lean source, test, configuration, and audit-script files in the local and server copies. The repository contains only source files and documentation, without dependency caches or compiled artifacts.

This record verifies the declared theorems under their explicit hypotheses. The [TODO for the general geometric input](TODO.md) remains open.
