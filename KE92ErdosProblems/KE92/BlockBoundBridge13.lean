import KE92ErdosProblems.KE92.BlockBound
import KE92ErdosProblems.KE92.BlockBound13_010
import KE92ErdosProblems.KE92.BlockBound13_012
import KE92ErdosProblems.KE92.BlockBound13_013
import KE92ErdosProblems.KE92.BlockBound13_020
import KE92ErdosProblems.KE92.BlockBound13_021
import KE92ErdosProblems.KE92.BlockBound13_023
import KE92ErdosProblems.KE92.BlockBound13_030
import KE92ErdosProblems.KE92.BlockBound13_031
import KE92ErdosProblems.KE92.BlockBound13_032
import KE92ErdosProblems.KE92.BlockBound13_101
import KE92ErdosProblems.KE92.BlockBound13_102
import KE92ErdosProblems.KE92.BlockBound13_103
import KE92ErdosProblems.KE92.BlockBound13_120
import KE92ErdosProblems.KE92.BlockBound13_121
import KE92ErdosProblems.KE92.BlockBound13_123
import KE92ErdosProblems.KE92.BlockBound13_130
import KE92ErdosProblems.KE92.BlockBound13_131
import KE92ErdosProblems.KE92.BlockBound13_132
import KE92ErdosProblems.KE92.BlockBound13_201
import KE92ErdosProblems.KE92.BlockBound13_202
import KE92ErdosProblems.KE92.BlockBound13_203
import KE92ErdosProblems.KE92.BlockBound13_210
import KE92ErdosProblems.KE92.BlockBound13_212
import KE92ErdosProblems.KE92.BlockBound13_213
import KE92ErdosProblems.KE92.BlockBound13_230
import KE92ErdosProblems.KE92.BlockBound13_231
import KE92ErdosProblems.KE92.BlockBound13_232
import KE92ErdosProblems.KE92.BlockBound13_301
import KE92ErdosProblems.KE92.BlockBound13_302
import KE92ErdosProblems.KE92.BlockBound13_303
import KE92ErdosProblems.KE92.BlockBound13_310
import KE92ErdosProblems.KE92.BlockBound13_312
import KE92ErdosProblems.KE92.BlockBound13_313
import KE92ErdosProblems.KE92.BlockBound13_320
import KE92ErdosProblems.KE92.BlockBound13_321
import KE92ErdosProblems.KE92.BlockBound13_323

/-!
# Spanning-13 abelian square impossibility

Assembles the 36 computational checks (one per valid first-three-letter triple)
to prove that no ASF word of length 13 has a spanning abelian square.
-/

set_option maxHeartbeats 8000000

namespace KE92

private theorem no_spanning13_01_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(0 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(0 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (1 : Fin 4)
  · subst hbc
    have : isFinASF [(0 : Fin 4), (1 : Fin 4), (1 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_010 d e f g h i j k l m hASF
    · exact no_spanning13_012 d e f g h i j k l m hASF
    · exact no_spanning13_013 d e f g h i j k l m hASF

private theorem no_spanning13_02_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(0 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(0 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (2 : Fin 4)
  · subst hbc
    have : isFinASF [(0 : Fin 4), (2 : Fin 4), (2 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_020 d e f g h i j k l m hASF
    · exact no_spanning13_021 d e f g h i j k l m hASF
    · exact no_spanning13_023 d e f g h i j k l m hASF

private theorem no_spanning13_03_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(0 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(0 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (3 : Fin 4)
  · subst hbc
    have : isFinASF [(0 : Fin 4), (3 : Fin 4), (3 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_030 d e f g h i j k l m hASF
    · exact no_spanning13_031 d e f g h i j k l m hASF
    · exact no_spanning13_032 d e f g h i j k l m hASF

private theorem no_spanning13_10_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(1 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(1 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (0 : Fin 4)
  · subst hbc
    have : isFinASF [(1 : Fin 4), (0 : Fin 4), (0 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_101 d e f g h i j k l m hASF
    · exact no_spanning13_102 d e f g h i j k l m hASF
    · exact no_spanning13_103 d e f g h i j k l m hASF

private theorem no_spanning13_12_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(1 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(1 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (2 : Fin 4)
  · subst hbc
    have : isFinASF [(1 : Fin 4), (2 : Fin 4), (2 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_120 d e f g h i j k l m hASF
    · exact no_spanning13_121 d e f g h i j k l m hASF
    · exact no_spanning13_123 d e f g h i j k l m hASF

private theorem no_spanning13_13_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(1 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(1 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (3 : Fin 4)
  · subst hbc
    have : isFinASF [(1 : Fin 4), (3 : Fin 4), (3 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_130 d e f g h i j k l m hASF
    · exact no_spanning13_131 d e f g h i j k l m hASF
    · exact no_spanning13_132 d e f g h i j k l m hASF

private theorem no_spanning13_20_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(2 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(2 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (0 : Fin 4)
  · subst hbc
    have : isFinASF [(2 : Fin 4), (0 : Fin 4), (0 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_201 d e f g h i j k l m hASF
    · exact no_spanning13_202 d e f g h i j k l m hASF
    · exact no_spanning13_203 d e f g h i j k l m hASF

private theorem no_spanning13_21_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(2 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(2 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (1 : Fin 4)
  · subst hbc
    have : isFinASF [(2 : Fin 4), (1 : Fin 4), (1 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_210 d e f g h i j k l m hASF
    · exact no_spanning13_212 d e f g h i j k l m hASF
    · exact no_spanning13_213 d e f g h i j k l m hASF

private theorem no_spanning13_23_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(2 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(2 : Fin 4), (3 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (3 : Fin 4)
  · subst hbc
    have : isFinASF [(2 : Fin 4), (3 : Fin 4), (3 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_230 d e f g h i j k l m hASF
    · exact no_spanning13_231 d e f g h i j k l m hASF
    · exact no_spanning13_232 d e f g h i j k l m hASF

private theorem no_spanning13_30_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(3 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(3 : Fin 4), (0 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (0 : Fin 4)
  · subst hbc
    have : isFinASF [(3 : Fin 4), (0 : Fin 4), (0 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_301 d e f g h i j k l m hASF
    · exact no_spanning13_302 d e f g h i j k l m hASF
    · exact no_spanning13_303 d e f g h i j k l m hASF

private theorem no_spanning13_31_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(3 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(3 : Fin 4), (1 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (1 : Fin 4)
  · subst hbc
    have : isFinASF [(3 : Fin 4), (1 : Fin 4), (1 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_310 d e f g h i j k l m hASF
    · exact no_spanning13_312 d e f g h i j k l m hASF
    · exact no_spanning13_313 d e f g h i j k l m hASF

private theorem no_spanning13_32_all :
    ∀ c d e f g h i j k l m : Fin 4,
      isFinASF [(3 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [(3 : Fin 4), (2 : Fin 4), c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro c d e f g h i j k l m hASF
  by_cases hbc : c = (2 : Fin 4)
  · subst hbc
    have : isFinASF [(3 : Fin 4), (2 : Fin 4), (2 : Fin 4), d, e, f, g, h, i, j, k, l, m] = false := by
      native_decide +revert
    simp_all
  · fin_cases c <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_320 d e f g h i j k l m hASF
    · exact no_spanning13_321 d e f g h i j k l m hASF
    · exact no_spanning13_323 d e f g h i j k l m hASF

/-- No ASF word of length 13 has a spanning abelian square (detected by hasSpanningAS). -/
theorem no_spanning13_abelianSquare :
    ∀ a b c d e f g h i j k l m : Fin 4,
      isFinASF [a, b, c, d, e, f, g, h, i, j, k, l, m] = true →
      hasSpanningAS [a, b, c, d, e, f, g, h, i, j, k, l, m] = false := by
  intro a b c d e f g h i j k l m hASF
  by_cases hab : a = b
  · subst hab
    have : isFinASF [a, a, c, d, e, f, g, h, i, j, k, l, m] = false := by
      fin_cases a <;> native_decide +revert
    simp_all
  · fin_cases a <;> fin_cases b <;> (try contradiction) <;> simp_all +decide
    · exact no_spanning13_01_all c d e f g h i j k l m hASF
    · exact no_spanning13_02_all c d e f g h i j k l m hASF
    · exact no_spanning13_03_all c d e f g h i j k l m hASF
    · exact no_spanning13_10_all c d e f g h i j k l m hASF
    · exact no_spanning13_12_all c d e f g h i j k l m hASF
    · exact no_spanning13_13_all c d e f g h i j k l m hASF
    · exact no_spanning13_20_all c d e f g h i j k l m hASF
    · exact no_spanning13_21_all c d e f g h i j k l m hASF
    · exact no_spanning13_23_all c d e f g h i j k l m hASF
    · exact no_spanning13_30_all c d e f g h i j k l m hASF
    · exact no_spanning13_31_all c d e f g h i j k l m hASF
    · exact no_spanning13_32_all c d e f g h i j k l m hASF

private theorem sameParikh4_of_perm'''' {l1 l2 : List (Fin 4)} (h : l1.Perm l2) :
    sameParikh4 l1 l2 = true := by
  unfold sameParikh4
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨h.count_eq 0, h.count_eq 1⟩, h.count_eq 2⟩, h.count_eq 3⟩

/-- No ASF word of length 13 has a spanning Perm-based abelian square. -/
theorem no_spanning13_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 13)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 13)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  have h_no_spanning : hasSpanningAS w = false := by
    rcases w with (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨l, _ | ⟨m, _ | w⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
      <;> simp_all +arith +decide
    exact no_spanning13_abelianSquare a b c d e f g h i j k l m (isFinASF_complete _ hw)
  have h_spanning : hasSpanningAS w = true := by
    unfold hasSpanningAS; simp +decide
    use r; refine ⟨hr, L - ((85 * (w.length - 1) - r) / 2 + 1), ?_, ?_⟩
    · omega
    · rw [Nat.add_sub_of_le]
      · exact sameParikh4_of_perm'''' hperm
      · omega
  simp_all

end KE92
