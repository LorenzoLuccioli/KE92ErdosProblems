import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-8 abelian square elimination -/

set_option maxHeartbeats 80000000

namespace KE92

/-- No ASF word of length 8 has a spanning-8 abelian square in its morphism image. -/
theorem no_spanning8_abelianSquare :
    ∀ a b c d e f g h : Fin 4,
      isFinASF [a, b, c, d, e, f, g, h] = true →
      hasSpanningAS [a, b, c, d, e, f, g, h] = false := by native_decide

end KE92
