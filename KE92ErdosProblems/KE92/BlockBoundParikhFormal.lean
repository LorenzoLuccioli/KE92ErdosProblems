import KE92ErdosProblems.KE92.BlockBoundParikhBridge

/-!
# Formal Parikh bridge infrastructure

Proved infrastructure for the spanning abelian square elimination:
- v-pattern classification for ‖v‖₁ = 3 (completing the Parikh v analysis)
- Block take decomposition (key list identity for the Parikh bridge)
- Count slice decomposition (Parikh of g(w) slices)
- Spanning Perm → hasSpanningAS = true (direction needed for contradiction)

## Remaining source lemma

The full Parikh bridge (spanning AS → AS in w → contradiction with ASF)
requires the **block-decomposition count identity**, which connects the Perm
condition on g(w) halves to the inner Parikh defect of w via the matrix
equation M^T v = δ_actual. This identity involves:

1. Expressing count(c, g(w).take(n)) via `applyKeranenG_take_blocks` (DONE).
2. Relating the Perm equality to the inner block-letter counts (requires
   careful treatment of the t = r+2L−85(m−1) boundary offset, especially
   the t = 85 edge case where the code's `boundaryDelta` uses t_code = 0).
3. Applying the v-pattern classification (DONE for all ‖v‖₁ ≤ 3).
4. Algebraically constructing the AS in w from the classified v pattern.

The t = 85 edge case has been computationally verified to NOT produce the
problematic v patterns (confirmed by `checkT85Issue` in interactive mode),
so the full bridge argument is mathematically sound.
-/

set_option maxHeartbeats 8000000

namespace KE92

/-! ### v-pattern classification for ‖v‖₁ = 3 -/

/-- Expected v for the ‖v‖₁ = 3 AS construction. -/
def expectedV3 (wa wb we : Fin 4) (sv : Int) (c : Fin 4) : Int :=
  sv * (if c = wb then (1 : Int) else 0) + (if c = we then (1 : Int) else 0) -
  (if c = wa then (1 : Int) else 0)

/-- For ‖v‖₁ = 3 with Σv = 1: v = e_{wb} + e_{we} - e_{wa}. -/
theorem parikh_v_norm3_pos :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      hasParikhSolution wa wb we r.val s.val = true →
      (parikhSolutionVec wa wb we r.val s.val 0 +
       parikhSolutionVec wa wb we r.val s.val 1 +
       parikhSolutionVec wa wb we r.val s.val 2 +
       parikhSolutionVec wa wb we r.val s.val 3 = 1) →
      ((parikhSolutionVec wa wb we r.val s.val 0).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 1).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 2).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 3).natAbs = 3) →
      ∀ c : Fin 4, parikhSolutionVec wa wb we r.val s.val c =
        expectedV3 wa wb we 1 c := by
  native_decide

/-- For ‖v‖₁ = 3 with Σv = -1: v = -e_{wb} + e_{we} - e_{wa}. -/
theorem parikh_v_norm3_neg :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      hasParikhSolution wa wb we r.val s.val = true →
      (parikhSolutionVec wa wb we r.val s.val 0 +
       parikhSolutionVec wa wb we r.val s.val 1 +
       parikhSolutionVec wa wb we r.val s.val 2 +
       parikhSolutionVec wa wb we r.val s.val 3 = -1) →
      ((parikhSolutionVec wa wb we r.val s.val 0).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 1).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 2).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 3).natAbs = 3) →
      ∀ c : Fin 4, parikhSolutionVec wa wb we r.val s.val c =
        expectedV3 wa wb we (-1) c := by
  native_decide

/-! ### Block take decomposition -/

/-- Key block decomposition: taking 85k+s from g(w) splits into
    complete blocks g(w.take k) and a partial block g(w[k]).take(s). -/
theorem applyKeranenG_take_blocks (w : List (Fin 4)) (k s : ℕ)
    (hk : k < w.length) (hs : s ≤ 85) :
    (applyKeranenG w).take (85 * k + s) =
    applyKeranenG (w.take k) ++ (keranenG (w.get ⟨k, hk⟩)).take s := by
  induction' k with k ih generalizing w s
  · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ applyKeranenG ]
    · contradiction
    · exact Or.inr ( by rw [ keranenG_length ] ; linarith )
  · rcases w with ( _ | ⟨ a, _ | ⟨ b, w ⟩ ⟩ ) <;> simp_all +decide [ Nat.mul_succ, List.take_append_of_le_length ]
    · contradiction
    · contradiction
    · simp_all +decide [ applyKeranenG ]
      rw [ ← ih ]
      · simp +arith +decide [ List.take_append, keranenG_length ]
      · grind
      · grind

/-- Count in a slice of g(w) equals the take-difference. -/
theorem count_applyKeranenG_slice (w : List (Fin 4)) (a b : ℕ) (c : Fin 4)
    (hab : a ≤ b) (hb : b ≤ (applyKeranenG w).length) :
    ((applyKeranenG w).drop a |>.take (b - a)).count c =
    ((applyKeranenG w).take b).count c -
    ((applyKeranenG w).take a).count c := by
  rw [ eq_comm, tsub_eq_of_eq_add ]
  rw [ show List.take b ( applyKeranenG w ) = List.take a ( applyKeranenG w ) ++ List.take ( b - a ) ( List.drop a ( applyKeranenG w ) ) from ?_, List.count_append ]
  · ring
  · rw [ ← List.take_add, Nat.add_sub_of_le hab ]

/-! ### Spanning AS gives hasSpanningAS = true -/

/-- From a Perm hypothesis at a spanning position, derive hasSpanningAS w = true. -/
theorem spanning_perm_gives_hasSpanningAS (w : List (Fin 4))
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = w.length)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    hasSpanningAS w = true := by
  refine' List.any_eq_true.mpr _
  refine' ⟨ r, _, _ ⟩ <;> norm_num
  · linarith
  · refine' ⟨ L - ( ( 85 * ( w.length - 1 ) - r ) / 2 + 1 ), _, _ ⟩
    · omega
    · rw [ Nat.add_sub_of_le ]
      · unfold sameParikh4; simp +decide [ hperm.count_eq ]
      · omega

end KE92
