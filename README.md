# KE92ErdosProblems

Lean formalizations of Erdős problems 192 and 231 using Keränen's 1992 result
that abelian squares are avoidable on four letters.

All solutions in this repository were written by
[Aristotle](https://aristotle.harmonic.fun).

## Layout

- `KE92ErdosProblems/KE92.lean` is the main Keränen 1992 formalization.
- `KE92ErdosProblems/KE92/` contains supporting files imported by `KE92.lean`.
- `KE92ErdosProblems/Erdos192.lean` and
  `KE92ErdosProblems/Erdos231.lean` are the two Erdős problem endpoints.

## Build

This project is pinned by `lean-toolchain`.

The block-bound proof uses an algebraic Parikh-matrix bridge, leaving only the
length-6 spanning check as a small finite computation.

```bash
lake exe cache get
lake build
```
