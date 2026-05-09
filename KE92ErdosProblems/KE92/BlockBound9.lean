import KE92ErdosProblems.KE92.BlockBound

/-! # Spanning-9 abelian square elimination (split into 4 files) -/

set_option maxHeartbeats 200000000

namespace KE92

/-- Spanning-9 check, first letter = 0. -/
theorem no_spanning9a :
    ∀ b c d e f g h i : Fin 4,
      isFinASF [(0 : Fin 4), b, c, d, e, f, g, h, i] = true →
      hasSpanningAS [(0 : Fin 4), b, c, d, e, f, g, h, i] = false := by native_decide

end KE92
