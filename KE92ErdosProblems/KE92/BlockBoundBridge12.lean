import KE92ErdosProblems.KE92.BlockBound
import KE92ErdosProblems.KE92.BlockBound12_010
import KE92ErdosProblems.KE92.BlockBound12_012
import KE92ErdosProblems.KE92.BlockBound12_013
import KE92ErdosProblems.KE92.BlockBound12_020
import KE92ErdosProblems.KE92.BlockBound12_021
import KE92ErdosProblems.KE92.BlockBound12_023
import KE92ErdosProblems.KE92.BlockBound12_030
import KE92ErdosProblems.KE92.BlockBound12_031
import KE92ErdosProblems.KE92.BlockBound12_032
import KE92ErdosProblems.KE92.BlockBound12_101
import KE92ErdosProblems.KE92.BlockBound12_102
import KE92ErdosProblems.KE92.BlockBound12_103
import KE92ErdosProblems.KE92.BlockBound12_120
import KE92ErdosProblems.KE92.BlockBound12_121
import KE92ErdosProblems.KE92.BlockBound12_123
import KE92ErdosProblems.KE92.BlockBound12_130
import KE92ErdosProblems.KE92.BlockBound12_131
import KE92ErdosProblems.KE92.BlockBound12_132
import KE92ErdosProblems.KE92.BlockBound12_201
import KE92ErdosProblems.KE92.BlockBound12_202
import KE92ErdosProblems.KE92.BlockBound12_203
import KE92ErdosProblems.KE92.BlockBound12_210
import KE92ErdosProblems.KE92.BlockBound12_212
import KE92ErdosProblems.KE92.BlockBound12_213
import KE92ErdosProblems.KE92.BlockBound12_230
import KE92ErdosProblems.KE92.BlockBound12_231
import KE92ErdosProblems.KE92.BlockBound12_232
import KE92ErdosProblems.KE92.BlockBound12_301
import KE92ErdosProblems.KE92.BlockBound12_302
import KE92ErdosProblems.KE92.BlockBound12_303
import KE92ErdosProblems.KE92.BlockBound12_310
import KE92ErdosProblems.KE92.BlockBound12_312
import KE92ErdosProblems.KE92.BlockBound12_313
import KE92ErdosProblems.KE92.BlockBound12_320
import KE92ErdosProblems.KE92.BlockBound12_321
import KE92ErdosProblems.KE92.BlockBound12_323

/-!
# Spanning-12 abelian square impossibility

Assembles the 36 computational checks (one per valid first-three-letter triple)
to prove that no ASF word of length 12 has a spanning abelian square.
-/

set_option maxHeartbeats 8000000

namespace KE92

private theorem no_spanning12_01_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(0 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(0 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (1 : Fin 4)
  · subst hbc
    have : isFinASF [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_010 d e f g h i j k l hASF
    · exact no_spanning12_012 d e f g h i j k l hASF
    · exact no_spanning12_013 d e f g h i j k l hASF

private theorem no_spanning12_02_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(0 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(0 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (2 : Fin 4)
  · subst hbc
    have : isFinASF [(0 : Fin 4), (2 : Fin 4), (2 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_020 d e f g h i j k l hASF
    · exact no_spanning12_021 d e f g h i j k l hASF
    · exact no_spanning12_023 d e f g h i j k l hASF

private theorem no_spanning12_03_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(0 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(0 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (3 : Fin 4)
  · subst hbc
    have : isFinASF [(0 : Fin 4), (3 : Fin 4), (3 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_030 d e f g h i j k l hASF
    · exact no_spanning12_031 d e f g h i j k l hASF
    · exact no_spanning12_032 d e f g h i j k l hASF

private theorem no_spanning12_10_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(1 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(1 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (0 : Fin 4)
  · subst hbc
    have : isFinASF [(1 : Fin 4), (0 : Fin 4), (0 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_101 d e f g h i j k l hASF
    · exact no_spanning12_102 d e f g h i j k l hASF
    · exact no_spanning12_103 d e f g h i j k l hASF

private theorem no_spanning12_12_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(1 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(1 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (2 : Fin 4)
  · subst hbc
    have : isFinASF [(1 : Fin 4), (2 : Fin 4), (2 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_120 d e f g h i j k l hASF
    · exact no_spanning12_121 d e f g h i j k l hASF
    · exact no_spanning12_123 d e f g h i j k l hASF

private theorem no_spanning12_13_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(1 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(1 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (3 : Fin 4)
  · subst hbc
    have : isFinASF [(1 : Fin 4), (3 : Fin 4), (3 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_130 d e f g h i j k l hASF
    · exact no_spanning12_131 d e f g h i j k l hASF
    · exact no_spanning12_132 d e f g h i j k l hASF

private theorem no_spanning12_20_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(2 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(2 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (0 : Fin 4)
  · subst hbc
    have : isFinASF [(2 : Fin 4), (0 : Fin 4), (0 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_201 d e f g h i j k l hASF
    · exact no_spanning12_202 d e f g h i j k l hASF
    · exact no_spanning12_203 d e f g h i j k l hASF

private theorem no_spanning12_21_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(2 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(2 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (1 : Fin 4)
  · subst hbc
    have : isFinASF [(2 : Fin 4), (1 : Fin 4), (1 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_210 d e f g h i j k l hASF
    · exact no_spanning12_212 d e f g h i j k l hASF
    · exact no_spanning12_213 d e f g h i j k l hASF

private theorem no_spanning12_23_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(2 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(2 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (3 : Fin 4)
  · subst hbc
    have : isFinASF [(2 : Fin 4), (3 : Fin 4), (3 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_230 d e f g h i j k l hASF
    · exact no_spanning12_231 d e f g h i j k l hASF
    · exact no_spanning12_232 d e f g h i j k l hASF

private theorem no_spanning12_30_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(3 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(3 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (0 : Fin 4)
  · subst hbc
    have : isFinASF [(3 : Fin 4), (0 : Fin 4), (0 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_301 d e f g h i j k l hASF
    · exact no_spanning12_302 d e f g h i j k l hASF
    · exact no_spanning12_303 d e f g h i j k l hASF

private theorem no_spanning12_31_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(3 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(3 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (1 : Fin 4)
  · subst hbc
    have : isFinASF [(3 : Fin 4), (1 : Fin 4), (1 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_310 d e f g h i j k l hASF
    · exact no_spanning12_312 d e f g h i j k l hASF
    · exact no_spanning12_313 d e f g h i j k l hASF

private theorem no_spanning12_32_all :
    ∀ c d e f g h i j k l : Fin 4,
      isFinASF [(3 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [(3 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l] = false := by
  intro c d e f g h i j k l hASF
  by_cases hbc : c = (2 : Fin 4)
  · subst hbc
    have : isFinASF [(3 : Fin 4), (2 : Fin 4), (2 : Fin 4), d, e, f, g, h, i, j, k, l] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_320 d e f g h i j k l hASF
    · exact no_spanning12_321 d e f g h i j k l hASF
    · exact no_spanning12_323 d e f g h i j k l hASF

/-- No ASF word of length 12 has a spanning abelian square (detected by hasSpanningAS). -/
theorem no_spanning12_abelianSquare :
    ∀ a b c d e f g h i j k l : Fin 4,
      isFinASF [a, b, c, d, e, f, g, h, i, j, k, l] = true →
      hasSpanningAS [a, b, c, d, e, f, g, h, i, j, k, l] = false := by
  intro a b c d e f g h i j k l hASF
  by_cases hab : a = b
  · subst hab
    have : isFinASF [a, a, c, d, e, f, g, h, i, j, k, l] = false := by
      fin_cases a <;> native_decide +revert
    simp_all
  · fin_cases a <;> fin_cases b <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning12_01_all c d e f g h i j k l hASF
    · exact no_spanning12_02_all c d e f g h i j k l hASF
    · exact no_spanning12_03_all c d e f g h i j k l hASF
    · exact no_spanning12_10_all c d e f g h i j k l hASF
    · exact no_spanning12_12_all c d e f g h i j k l hASF
    · exact no_spanning12_13_all c d e f g h i j k l hASF
    · exact no_spanning12_20_all c d e f g h i j k l hASF
    · exact no_spanning12_21_all c d e f g h i j k l hASF
    · exact no_spanning12_23_all c d e f g h i j k l hASF
    · exact no_spanning12_30_all c d e f g h i j k l hASF
    · exact no_spanning12_31_all c d e f g h i j k l hASF
    · exact no_spanning12_32_all c d e f g h i j k l hASF

private theorem sameParikh4_of_perm''' {l1 l2 : List (Fin 4)} (h : l1.Perm l2) :
    sameParikh4 l1 l2 = true := by
  unfold sameParikh4
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨h.count_eq 0, h.count_eq 1⟩, h.count_eq 2⟩, h.count_eq 3⟩

/-- No ASF word of length 12 has a spanning Perm-based abelian square. -/
theorem no_spanning12_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 12)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 12)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  have h_no_spanning : hasSpanningAS w = false := by
    rcases w with (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨l, _ | w⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
      <;> simp_all +arith +decide
    exact no_spanning12_abelianSquare a b c d e f g h i j k l (isFinASF_complete _ hw)
  have h_spanning : hasSpanningAS w = true := by
    unfold hasSpanningAS; simp +decide
    use r; refine ⟨hr, L - ((85 * (w.length - 1) - r) / 2 + 1), ?_, ?_⟩
    · omega
    · rw [Nat.add_sub_of_le]
      · exact sameParikh4_of_perm''' hperm
      · omega
  simp_all

end KE92
