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

The original full proof performs a large finite case analysis using
`native_decide`, so compiling it can take a very long time.  To make routine CI
and editing practical, `KE92ErdosProblems/KE92/PaperCoreDefs.lean` overrides
`native_decide` with `sorry` near the top of the file.  To verify the finite
computations locally, comment out that macro line and run a local build.

```bash
lake exe cache get
lake build
```
