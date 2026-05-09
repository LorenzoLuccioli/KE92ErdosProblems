import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-7 abelian square elimination -/

set_option maxHeartbeats 40000000

namespace KE92

/-- No ASF word of length 7 has a spanning-7 abelian square in its morphism image. -/
theorem no_spanning7_abelianSquare :
    ∀ a b c d e f g : Fin 4,
      isFinASF [a, b, c, d, e, f, g] = true →
      hasSpanningAS [a, b, c, d, e, f, g] = false := by native_decide

end KE92
