import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-13 abelian square elimination, first three letters = 0,2,0 -/

set_option maxHeartbeats 8000000000

namespace KE92

/-- Spanning-13 check, first three letters = 0, 2, 0. -/
theorem no_spanning13_020 :
    ∀ a b c d e f g h i j : Fin 4,
      isFinASF [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), a, b, c, d, e, f, g, h, i, j] = true →
      hasSpanningAS [(0 : Fin 4), (2 : Fin 4), (0 : Fin 4), a, b, c, d, e, f, g, h, i, j] = false := by native_decide

end KE92
