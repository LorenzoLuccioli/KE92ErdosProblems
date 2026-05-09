import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-13 abelian square elimination, first three letters = 3,1,2 -/

set_option maxHeartbeats 8000000000

namespace KE92

/-- Spanning-13 check, first three letters = 3, 1, 2. -/
theorem no_spanning13_312 :
    ∀ a b c d e f g h i j : Fin 4,
      isFinASF [(3 : Fin 4), (1 : Fin 4), (2 : Fin 4), a, b, c, d, e, f, g, h, i, j] = true →
      hasSpanningAS [(3 : Fin 4), (1 : Fin 4), (2 : Fin 4), a, b, c, d, e, f, g, h, i, j] = false := by native_decide

end KE92
