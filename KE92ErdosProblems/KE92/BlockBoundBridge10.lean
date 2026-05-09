import KE92ErdosProblems.KE92.BlockBound
import KE92ErdosProblems.KE92.BlockBound10a
import KE92ErdosProblems.KE92.BlockBound10b
import KE92ErdosProblems.KE92.BlockBound10c
import KE92ErdosProblems.KE92.BlockBound10_10
import KE92ErdosProblems.KE92.BlockBound10_12
import KE92ErdosProblems.KE92.BlockBound10_13
import KE92ErdosProblems.KE92.BlockBound10_20
import KE92ErdosProblems.KE92.BlockBound10_21
import KE92ErdosProblems.KE92.BlockBound10_23
import KE92ErdosProblems.KE92.BlockBound10_30
import KE92ErdosProblems.KE92.BlockBound10_31
import KE92ErdosProblems.KE92.BlockBound10_32

/-!
# Spanning-10 abelian square impossibility

Assembles the 12 computational checks (one per valid first-two-letter pair)
to prove that no ASF word of length 10 has a spanning abelian square.
-/

set_option maxHeartbeats 8000000

namespace KE92

private theorem sameParikh4_of_perm' {l1 l2 : List (Fin 4)} (h : l1.Perm l2) :
    sameParikh4 l1 l2 = true := by
  unfold sameParikh4
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨h.count_eq 0, h.count_eq 1⟩, h.count_eq 2⟩, h.count_eq 3⟩

/-- No ASF word of length 10 has a spanning abelian square (detected by hasSpanningAS). -/
theorem no_spanning10_abelianSquare :
    ∀ a b c d e f g h i j : Fin 4,
      isFinASF [a, b, c, d, e, f, g, h, i, j] = true →
      hasSpanningAS [a, b, c, d, e, f, g, h, i, j] = false := by
  intro a b c d e f g h i j hASF
  -- Dispatch a = b cases (isFinASF is false for words starting with equal consecutive letters)
  by_cases hab : a = b
  · subst hab
    have : isFinASF [a, a, c, d, e, f, g, h, i, j] = false := by
      fin_cases a <;> native_decide +revert
    simp_all
  · fin_cases a <;> fin_cases b <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning10_01 c d e f g h i j hASF
    · exact no_spanning10_02 c d e f g h i j hASF
    · exact no_spanning10_03 c d e f g h i j hASF
    · exact no_spanning10_10 c d e f g h i j hASF
    · exact no_spanning10_12 c d e f g h i j hASF
    · exact no_spanning10_13 c d e f g h i j hASF
    · exact no_spanning10_20 c d e f g h i j hASF
    · exact no_spanning10_21 c d e f g h i j hASF
    · exact no_spanning10_23 c d e f g h i j hASF
    · exact no_spanning10_30 c d e f g h i j hASF
    · exact no_spanning10_31 c d e f g h i j hASF
    · exact no_spanning10_32 c d e f g h i j hASF

/-- No ASF word of length 10 has a spanning Perm-based abelian square. -/
theorem no_spanning10_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 10)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 10)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  have h_no_spanning : hasSpanningAS w = false := by
    rcases w with (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, _ | w⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
      <;> simp_all +arith +decide
    exact no_spanning10_abelianSquare a b c d e f g h i j (isFinASF_complete _ hw)
  have h_spanning : hasSpanningAS w = true := by
    unfold hasSpanningAS; simp +decide
    use r; refine ⟨hr, L - ((85 * (w.length - 1) - r) / 2 + 1), ?_, ?_⟩
    · omega
    · rw [Nat.add_sub_of_le]
      · exact sameParikh4_of_perm' hperm
      · omega
  simp_all

end KE92
