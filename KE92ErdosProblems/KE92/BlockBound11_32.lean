import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-11 abelian square elimination, first two letters = 3,2 -/

set_option maxHeartbeats 2000000000

namespace KE92

/-- Spanning-11 check, first two letters = 3, 2. -/
theorem no_spanning11_32 :
    ∀ x a b c d e f g h : Fin 4,
      isFinASF [(3 : Fin 4), (2 : Fin 4), x, a, b, c, d, e, f, g, h] = true →
      hasSpanningAS [(3 : Fin 4), (2 : Fin 4), x, a, b, c, d, e, f, g, h] = false := by native_decide

end KE92
