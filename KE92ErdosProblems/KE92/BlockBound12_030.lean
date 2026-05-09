import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-12 abelian square elimination, first three letters = 0,3,0 -/

set_option maxHeartbeats 2000000000

namespace KE92

/-- Spanning-12 check, first three letters = 0, 3, 0. -/
theorem no_spanning12_030 :
    ∀ a b c d e f g h i : Fin 4,
      isFinASF [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), a, b, c, d, e, f, g, h, i] = true →
      hasSpanningAS [(0 : Fin 4), (3 : Fin 4), (0 : Fin 4), a, b, c, d, e, f, g, h, i] = false := by native_decide

end KE92
