import KE92ErdosProblems.KE92.PaperCoreDefs

/-! # Morphism preservation for length-5 words starting with letter 1 -/

set_option maxHeartbeats 4000000

namespace KE92

/-- Morphism preservation for length-5 words starting with letter 1.
Verified by `native_decide` over all 4⁴ = 256 inputs. -/
theorem morphism_check_5b :
    ∀ b c d e : Fin 4,
    isFinASF [(1 : Fin 4), b, c, d, e] = true →
    isFinASF (applyKeranenG [(1 : Fin 4), b, c, d, e]) = true := by
  native_decide

end KE92
