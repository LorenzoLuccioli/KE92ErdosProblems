import KE92ErdosProblems.KE92.BlockBound

/-! # Parikh norm bound and 3-letter ASF bound -/

set_option maxHeartbeats 8000000

namespace KE92

/-- **Parikh norm bound.** For every boundary configuration, either no
integer solution exists for `M^T v = δ`, or `‖v‖₁ ≤ 3`. -/
theorem parikh_norm_bound :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      (adjMTtimesDelta wa wb we r.val s.val 0 % 43435 = 0 ∧
       adjMTtimesDelta wa wb we r.val s.val 1 % 43435 = 0 ∧
       adjMTtimesDelta wa wb we r.val s.val 2 % 43435 = 0 ∧
       adjMTtimesDelta wa wb we r.val s.val 3 % 43435 = 0) →
      (adjMTtimesDelta wa wb we r.val s.val 0 / 43435).natAbs +
      (adjMTtimesDelta wa wb we r.val s.val 1 / 43435).natAbs +
      (adjMTtimesDelta wa wb we r.val s.val 2 / 43435).natAbs +
      (adjMTtimesDelta wa wb we r.val s.val 3 / 43435).natAbs ≤ 3 := by
  native_decide

/-- Decidable ASF check for `Fin 3` words. -/
def isFinASF3 (word : List (Fin 3)) : Bool :=
  !(List.range word.length |>.any fun i =>
    List.range word.length |>.any fun l =>
      let l := l + 1
      if i + 2 * l > word.length then false
      else (word.drop i |>.take l).isPerm (word.drop (i + l) |>.take l))

/-- **3-letter ASF bound.** No ASF word on 3 letters has length ≥ 8. -/
theorem max_asf_3letters :
    ∀ a b c d e f g h : Fin 3,
      isFinASF3 [a, b, c, d, e, f, g, h] = false := by native_decide

end KE92
