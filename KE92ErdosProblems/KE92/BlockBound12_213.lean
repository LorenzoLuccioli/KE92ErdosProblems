import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-12 abelian square elimination, first three letters = 2,1,3 -/

set_option maxHeartbeats 2000000000

namespace KE92

/-- Spanning-12 check, first three letters = 2, 1, 3. -/
theorem no_spanning12_213 :
    ∀ a b c d e f g h i : Fin 4,
      isFinASF [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4), a, b, c, d, e, f, g, h, i] = true →
      hasSpanningAS [(2 : Fin 4), (1 : Fin 4), (3 : Fin 4), a, b, c, d, e, f, g, h, i] = false := by native_decide

end KE92
