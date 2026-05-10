# KE92

Supporting files for the Keränen 1992 formalization.

The public source module is `KE92ErdosProblems.KE92`. It imports these files and proves the shared theorem
`KE92.exists_inf_abelianSquareFree_four`, which is used by the problem endpoint
files for Erdős problems 192 and 231.

## Performance notes

Retained source files:

- `../KE92.lean`: common paper file and main Keränen theorem package.
- `PaperCoreDefs.lean`: shared definitions and basic lemmas.
- `KeranenBounded.lean`, `KeranenBounded5a.lean` through `KeranenBounded5d.lean`: bounded morphism checks through length 5.
- `BlockBound.lean`, `BlockBoundParikh*.lean`, `BlockBoundSpanning*.lean`, and `BlockBoundBridge.lean`: block-bound reduction.
- `../Erdos192.lean` and `../Erdos231.lean`: problem endpoints.
