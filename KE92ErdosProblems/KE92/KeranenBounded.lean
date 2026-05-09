import KE92ErdosProblems.KE92.PaperCoreDefs

/-!
# Bounded computational verification of Keränen's morphism preservation (K = 4)

Proves by `native_decide` that Keränen's 85-uniform morphism preserves
abelian-square-freeness for all abelian-square-free words of length ≤ 4.

This covers all potential abelian squares of half-length ≤ 127 in morphism images.

## Role in the proof chain

Combined with `finASF_subword` (localization) and the block-bound finite reduction,
this is part of the chain proving `keranenG_preserves_ASF`.

The K = 5 verification (covering half-length ≤ 170) is split into separate files
`KeranenBounded5a.lean` through `KeranenBounded5d.lean`, each handling one starting
letter. Together they verify all 1024 length-5 words.
-/

set_option maxHeartbeats 4000000

namespace KE92

/-- Morphism preservation verified for all words of length 4 by `native_decide`.
For every word `[a,b,c,d]` over `{0,1,2,3}` that is abelian-square-free,
its morphism image `g([a,b,c,d])` (of length 340) is also abelian-square-free. -/
theorem morphism_check_4 :
    ∀ a b c d : Fin 4, isFinASF [a, b, c, d] = true →
    isFinASF (applyKeranenG [a, b, c, d]) = true := by
  native_decide

end KE92
