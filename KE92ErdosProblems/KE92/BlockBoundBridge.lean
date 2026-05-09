import KE92ErdosProblems.KE92.BlockBound
import KE92ErdosProblems.KE92.BlockBoundSpanningChain

/-!
# Block bound bridge lemmas

Connecting the List.Perm abelian-square hypothesis in `g(w)` to the
Boolean spanning checks, via explicit localization and Perm → sameParikh4.

## Performance note (2025-05)

The algebraic Parikh-matrix analysis (`no_spanning_large`) now handles all
spanning lengths ≥ 7, replacing the 100+ brute-force `native_decide` files
that previously covered lengths 7–13 individually. Only the length-6
spanning check remains as a single fast `native_decide`.
-/

set_option maxHeartbeats 4000000

namespace KE92

/-! ### Perm → sameParikh4 -/

theorem sameParikh4_of_perm {l1 l2 : List (Fin 4)} (h : l1.Perm l2) :
    sameParikh4 l1 l2 = true := by
  unfold sameParikh4
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨h.count_eq 0, h.count_eq 1⟩, h.count_eq 2⟩, h.count_eq 3⟩

/-! ### Explicit localization -/

theorem abelianSquare_localize_explicit (w : List (Fin 4))
    (i L : ℕ) (hL : L > 0)
    (hlen : i + 2 * L ≤ (applyKeranenG w).length)
    (hperm : ((applyKeranenG w).drop i |>.take L).Perm
             ((applyKeranenG w).drop (i + L) |>.take L)) :
    let a := i / 85
    let m := (i + 2 * L - 1) / 85 - a + 1
    let r := i % 85
    let w' := w.drop a |>.take m
    (r + 2 * L ≤ (applyKeranenG w').length) ∧
    ((applyKeranenG w').drop r |>.take L).Perm
      ((applyKeranenG w').drop (r + L) |>.take L) := by
  refine' ⟨ _, _ ⟩;
  · rw [ applyKeranenG_length ] at *;
    simp +arith +decide [ List.length_take, List.length_drop ];
    omega;
  · have h_localize : List.drop i (applyKeranenG w) = List.drop (i % 85) (applyKeranenG (List.drop (i / 85) w)) ∧ List.drop (i + L) (applyKeranenG w) = List.drop (i % 85 + L) (applyKeranenG (List.drop (i / 85) w)) := by
      have h_localize : ∀ (a : ℕ) (w : List (Fin 4)), List.drop (85 * a) (applyKeranenG w) = applyKeranenG (List.drop a w) := by
        intro a w; induction' a with a ih generalizing w <;> simp_all +decide [ List.drop ] ;
        rcases w <;> simp_all +decide [ Nat.mul_succ, List.drop ];
        · rfl;
        · simp_all +decide [ applyKeranenG, List.drop_append ];
          simp_all +decide [ keranenG_length ];
      rw [ ← h_localize ];
      constructor <;> rw [ List.drop_drop ] <;> congr 1 <;> omega;
    have h_localize : applyKeranenG (List.drop (i / 85) w) = applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)) ++ applyKeranenG (List.drop ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)) := by
      unfold applyKeranenG; simp +decide ;
      rw [ ← List.take_append_drop ( ( i + 2 * L - 1 ) / 85 - i / 85 + 1 ) ( List.drop ( i / 85 ) w ), List.flatMap_append ];
      simp +decide [ List.drop_drop ];
    have h_localize : List.take L (List.drop (i % 85) (applyKeranenG (List.drop (i / 85) w))) = List.take L (List.drop (i % 85) (applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)))) ∧ List.take L (List.drop (i % 85 + L) (applyKeranenG (List.drop (i / 85) w))) = List.take L (List.drop (i % 85 + L) (applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)))) := by
      rw [ h_localize ];
      rw [ List.drop_append, List.drop_append ];
      constructor <;> rw [ List.take_append_of_le_length ];
      · simp +arith +decide [ applyKeranenG_length ];
        rw [ applyKeranenG_length ] at hlen;
        omega;
      · simp +arith +decide [ applyKeranenG_length ];
        rw [ applyKeranenG_length ] at hlen;
        omega;
    lia

theorem localized_block_span (w : List (Fin 4)) (i L : ℕ) (_hL : L > 0)
    (_hlen : i + 2 * L ≤ (applyKeranenG w).length) :
    let a := i / 85
    let m := (i + 2 * L - 1) / 85 - a + 1
    let r := i % 85
    (r + 2 * L - 1) / 85 + 1 = m := by
  omega

/-! ### Spanning contradiction lemmas -/

/-
No ASF word of length 6 has a spanning Perm-based abelian square.
-/
theorem no_spanning6_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 6)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 6)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ : ∃ a b c d e f : Fin 4, w = [a, b, c, d, e, f] := by
    rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | w ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
  have h_spanning : hasSpanning6AS [a, b, c, d, e, f] = true := by
    unfold hasSpanning6AS; simp_all +decide [ List.isPerm_iff ] ;
    refine' ⟨ r, hr, L - ( ( 426 - r + 1 ) / 2 ), _, _ ⟩ <;> norm_num at *;
    · omega;
    · lia;
  exact absurd h_spanning ( by simpa using no_spanning6_abelianSquare a b c d e f ( isFinASF_complete _ hw ) )

/-! ### Main inductive block bound -/

/-- **Block bound by well-founded induction.**
For any ASF word `w`, an abelian square in `g(w)` spans at most 5 blocks.

Proved by strong induction on `w.length`:
- If `m < w.length`: extract subword `w'` of length `m`, apply IH.
- If `m = w.length ≤ 5`: trivial.
- If `m = w.length = 6`: contradiction via spanning-6 check (single `native_decide`).
- If `m = w.length ≥ 7`: contradiction via algebraic Parikh-matrix bridge. -/
theorem abelianSquare_block_bound_inductive :
    ∀ (w : List (Fin 4)), FinAbelianSquareFree w →
    ∀ (i L : ℕ), L > 0 → i + 2 * L ≤ (applyKeranenG w).length →
    ((applyKeranenG w).drop i |>.take L).Perm
      ((applyKeranenG w).drop (i + L) |>.take L) →
    (i + 2 * L - 1) / 85 - i / 85 + 1 ≤ 5 := by
  -- Reformulate with explicit length parameter for strong induction
  suffices h : ∀ n, ∀ w : List (Fin 4), w.length ≤ n →
    FinAbelianSquareFree w →
    ∀ i L, L > 0 → i + 2 * L ≤ (applyKeranenG w).length →
    ((applyKeranenG w).drop i |>.take L).Perm
      ((applyKeranenG w).drop (i + L) |>.take L) →
    (i + 2 * L - 1) / 85 - i / 85 + 1 ≤ 5
    from fun w hw i L hL hlen hperm => h w.length w le_rfl hw i L hL hlen hperm
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro w hw_le hw i L hL hlen hperm
    set m := (i + 2 * L - 1) / 85 - i / 85 + 1 with hm_def
    set a := i / 85 with ha_def
    set r := i % 85 with hr_def
    -- m ≤ w.length
    have ham : a + m ≤ w.length := by
      rw [applyKeranenG_length] at hlen; omega
    -- If m ≤ 5: done
    by_contra hm_gt
    push_neg at hm_gt
    -- hm_gt : 6 ≤ m
    -- Extract localization
    set w' := w.drop a |>.take m with hw'_def
    have hw' : FinAbelianSquareFree w' := finASF_subword w hw a m ham
    obtain ⟨hlen', hperm'⟩ := abelianSquare_localize_explicit w i L hL hlen hperm
    have hspan : (r + 2 * L - 1) / 85 + 1 = m := localized_block_span w i L hL hlen
    have hw'_len : w'.length = m := by
      simp [hw'_def, List.length_take, List.length_drop]; omega
    have hr_lt : r < 85 := Nat.mod_lt i (by omega)
    -- Case split: m < w.length or m = w.length
    by_cases hm_lt : m < w.length
    · -- m < w.length: apply IH to w' (which has length m < w.length ≤ n)
      have hm_lt_n : m < n := by omega
      have ih_result := ih m hm_lt_n w' (by omega) hw' r L hL hlen' hperm'
      -- ih_result : (r + 2*L - 1)/85 - r/85 + 1 ≤ 5
      -- Since r < 85: r/85 = 0
      have hr_div : r / 85 = 0 := by omega
      -- So (r+2L-1)/85 + 1 ≤ 5, i.e., m ≤ 5
      omega
    · -- m = w.length (spanning case)
      push_neg at hm_lt
      have hm_eq : m = w.length := by omega
      -- a = 0 (since a + m ≤ w.length and m = w.length)
      have ha_zero : a = 0 := by omega
      -- w' = w
      have hw'_eq_w : w' = w := by
        simp only [hw'_def, ha_zero]
        simp only [List.drop_zero]
        exact List.take_of_length_le (by omega)
      -- Simplify using i/85 = 0
      have hi85 : i / 85 = 0 := by omega
      simp only [hi85, Nat.sub_zero, List.drop_zero,
        List.take_of_length_le (by omega : w.length ≤ (i + 2 * L - 1) / 85 + 1)] at hlen' hperm'
      -- Case split: m = 6 or m ≥ 7
      rcases Nat.lt_or_ge m 7 with hm6 | hm7
      · -- m = 6: spanning-6 check
        exact no_spanning6_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
      · -- m ≥ 7: algebraic Parikh-matrix bridge
        exact no_spanning_large w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'

end KE92
