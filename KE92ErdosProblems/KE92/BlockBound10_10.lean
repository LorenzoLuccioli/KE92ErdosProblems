import KE92ErdosProblems.KE92.BlockBound

set_option maxHeartbeats 800000000

namespace KE92

theorem no_spanning10_10 :
    ∀ c d e f g h i j : Fin 4,
      isFinASF [(1 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j] = true →
      hasSpanningAS [(1 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j] = false := by native_decide

end KE92
