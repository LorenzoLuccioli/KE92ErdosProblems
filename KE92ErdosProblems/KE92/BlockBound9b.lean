import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-9 abelian square elimination, first letter = 1 -/

set_option maxHeartbeats 200000000

namespace KE92

theorem no_spanning9b :
    ∀ b c d e f g h i : Fin 4,
      isFinASF [(1 : Fin 4), b, c, d, e, f, g, h, i] = true →
      hasSpanningAS [(1 : Fin 4), b, c, d, e, f, g, h, i] = false := by native_decide

end KE92
