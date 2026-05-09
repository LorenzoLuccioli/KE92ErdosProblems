import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-10 abelian square elimination, first two letters = 0,2 -/

set_option maxHeartbeats 800000000

namespace KE92

/-- Spanning-10 check, first two letters = 0, 2. -/
theorem no_spanning10_02 :
    ∀ c d e f g h i j : Fin 4,
      isFinASF [(0 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j] = true →
      hasSpanningAS [(0 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j] = false := by native_decide

end KE92
