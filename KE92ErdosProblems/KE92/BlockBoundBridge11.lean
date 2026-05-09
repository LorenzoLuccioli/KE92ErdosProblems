import KE92ErdosProblems.KE92.BlockBound
import KE92ErdosProblems.KE92.BlockBound11a
import KE92ErdosProblems.KE92.BlockBound11b
import KE92ErdosProblems.KE92.BlockBound11c
import KE92ErdosProblems.KE92.BlockBound11_10
import KE92ErdosProblems.KE92.BlockBound11_12
import KE92ErdosProblems.KE92.BlockBound11_13
import KE92ErdosProblems.KE92.BlockBound11_20
import KE92ErdosProblems.KE92.BlockBound11_21
import KE92ErdosProblems.KE92.BlockBound11_23
import KE92ErdosProblems.KE92.BlockBound11_30
import KE92ErdosProblems.KE92.BlockBound11_31
import KE92ErdosProblems.KE92.BlockBound11_32

/-!
# Spanning-11 abelian square impossibility

Assembles the 12 computational checks (one per valid first-two-letter pair)
to prove that no ASF word of length 11 has a spanning abelian square.
-/

set_option maxHeartbeats 8000000

namespace KE92

/-- No ASF word of length 11 has a spanning abelian square (detected by hasSpanningAS). -/
theorem no_spanning11_abelianSquare :
    ∀ a b c d e f g h i j k : Fin 4,
      isFinASF [a, b, c, d, e, f, g, h, i, j, k] = true →
      hasSpanningAS [a, b, c, d, e, f, g, h, i, j, k] = false := by
  intro a b c d e f g h i j k hASF
  -- Dispatch a = b cases (isFinASF is false for words starting with equal consecutive letters)
  by_cases hab : a = b
  · subst hab
    have : isFinASF [a, a, c, d, e, f, g, h, i, j, k] = false := by
      fin_cases a <;> native_decide +revert
    simp_all
  · fin_cases a <;> fin_cases b <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning11_01 c d e f g h i j k hASF
    · exact no_spanning11_02 c d e f g h i j k hASF
    · exact no_spanning11_03 c d e f g h i j k hASF
    · exact no_spanning11_10 c d e f g h i j k hASF
    · exact no_spanning11_12 c d e f g h i j k hASF
    · exact no_spanning11_13 c d e f g h i j k hASF
    · exact no_spanning11_20 c d e f g h i j k hASF
    · exact no_spanning11_21 c d e f g h i j k hASF
    · exact no_spanning11_23 c d e f g h i j k hASF
    · exact no_spanning11_30 c d e f g h i j k hASF
    · exact no_spanning11_31 c d e f g h i j k hASF
    · exact no_spanning11_32 c d e f g h i j k hASF

private theorem sameParikh4_of_perm'' {l1 l2 : List (Fin 4)} (h : l1.Perm l2) :
    sameParikh4 l1 l2 = true := by
  unfold sameParikh4
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨h.count_eq 0, h.count_eq 1⟩, h.count_eq 2⟩, h.count_eq 3⟩

/-- No ASF word of length 11 has a spanning Perm-based abelian square. -/
theorem no_spanning11_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 11)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 11)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  have h_no_spanning : hasSpanningAS w = false := by
    rcases w with (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | w⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
      <;> simp_all +arith +decide
    exact no_spanning11_abelianSquare a b c d e f g h i j k (isFinASF_complete _ hw)
  have h_spanning : hasSpanningAS w = true := by
    unfold hasSpanningAS; simp +decide
    use r; refine ⟨hr, L - ((85 * (w.length - 1) - r) / 2 + 1), ?_, ?_⟩
    · omega
    · rw [Nat.add_sub_of_le]
      · exact sameParikh4_of_perm'' hperm
      · omega
  simp_all

end KE92
