import KE92ErdosProblems.KE92.BlockBound
import KE92ErdosProblems.KE92.BlockBound7
import KE92ErdosProblems.KE92.BlockBound8
import KE92ErdosProblems.KE92.BlockBound9
import KE92ErdosProblems.KE92.BlockBound9b
import KE92ErdosProblems.KE92.BlockBound9c
import KE92ErdosProblems.KE92.BlockBound9d
import KE92ErdosProblems.KE92.BlockBoundBridge10
import KE92ErdosProblems.KE92.BlockBoundBridge11
import KE92ErdosProblems.KE92.BlockBoundBridge12
import KE92ErdosProblems.KE92.BlockBoundBridge13
import KE92ErdosProblems.KE92.BlockBoundSpanningChain

/-!
# Block bound bridge lemmas

Connecting the List.Perm abelian-square hypothesis in `g(w)` to the
Boolean spanning checks, via explicit localization and Perm → sameParikh4.
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
        intro a w; induction' a with a ih generalizing w <;> simp_all +decide [ Nat.mul_succ, List.drop ] ;
        rcases w <;> simp_all +decide [ Nat.mul_succ, List.drop ];
        · rfl;
        · simp_all +decide [ applyKeranenG, List.drop_append ];
          simp_all +decide [ keranenG_length ];
      rw [ ← h_localize ];
      constructor <;> rw [ List.drop_drop ] <;> congr 1 <;> omega;
    have h_localize : applyKeranenG (List.drop (i / 85) w) = applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)) ++ applyKeranenG (List.drop ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)) := by
      unfold applyKeranenG; simp +decide [ List.flatMap_append ] ;
      rw [ ← List.take_append_drop ( ( i + 2 * L - 1 ) / 85 - i / 85 + 1 ) ( List.drop ( i / 85 ) w ), List.flatMap_append ];
      simp +decide [ add_assoc, List.drop_drop ];
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

theorem localized_block_span (w : List (Fin 4)) (i L : ℕ) (hL : L > 0)
    (hlen : i + 2 * L ≤ (applyKeranenG w).length) :
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

/-
No ASF word of length 7 has a spanning Perm-based abelian square.
-/
theorem no_spanning7_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 7)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 7)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  revert r L hL hr hlen hspan hperm;
  -- By definition of `w`, we know that it can be written as `[a, b, c, d, e, f, g]` for some `a, b, c, d, e, f, g : Fin 4`.
  obtain ⟨a, b, c, d, e, f, g, hw_eq⟩ : ∃ a b c d e f g : Fin 4, w = [a, b, c, d, e, f, g] := by
    rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | ⟨ g, _ | w ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +decide;
  intros r L hL hr hlen hspan hperm;
  convert no_spanning7_abelianSquare a b c d e f g _;
  · simp +decide [ hasSpanningAS ];
    use r;
    refine' ⟨ hr, L - ( ( 510 - r ) / 2 + 1 ), _, _ ⟩;
    · grind +splitImp;
    · rw [ add_tsub_cancel_of_le ];
      · convert sameParikh4_of_perm ( hw_eq ▸ hperm ) using 1;
      · omega;
  · exact isFinASF_complete _ ( hw_eq ▸ hw )

/-
No ASF word of length 8 has a spanning Perm-based abelian square.
-/
theorem no_spanning8_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 8)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 8)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  -- By `isFinASF_complete`, since w is ASF, `isFinASF w` is true.
  have h_isFinASF : isFinASF w = true := by
    exact isFinASF_complete w hw
  -- By `no_spanning8_abelianSquare`, hasSpanningAS [a,b,c,d,e,f,g,h] is false for ASF words.
  have h_no_spanning8 : hasSpanningAS w = false := by
    rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | ⟨ g, _ | ⟨ h, _ | w ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +decide;
    exact no_spanning8_abelianSquare a b c d e f g h h_isFinASF;
  unfold hasSpanningAS at h_no_spanning8; simp_all +decide ;
  specialize h_no_spanning8 r hr ( L - ( ( 595 - r ) / 2 + 1 ) ) ; simp_all +decide [ Nat.sub_sub ];
  rw [ Nat.add_sub_of_le ] at h_no_spanning8;
  · exact absurd ( h_no_spanning8 ( by omega ) ) ( by rw [ sameParikh4_of_perm hperm ] ; decide );
  · lia

/-
No ASF word of length 9 has a spanning Perm-based abelian square.
-/
theorem no_spanning9_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 9)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 9)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  obtain ⟨a, b, c, d, e, f, g, h, i, hw_eq⟩ : ∃ a b c d e f g h i : Fin 4, w = [a, b, c, d, e, f, g, h, i] := by
    rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | ⟨ g, _ | ⟨ h, _ | ⟨ i, _ | w ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp +arith +decide at hw_len ⊢;
  have h_no_spanning9 : hasSpanningAS w = false := by
    fin_cases a <;> simp +decide [ * ];
    · exact no_spanning9a b c d e f g h i ( by simpa [ hw_eq ] using isFinASF_complete w hw );
    · exact no_spanning9b b c d e f g h i ( by simpa [ hw_eq ] using isFinASF_complete w hw );
    · exact no_spanning9c b c d e f g h i ( by simpa [ hw_eq ] using isFinASF_complete w ( by simpa [ hw_eq ] using hw ) );
    · exact no_spanning9d b c d e f g h i ( by simpa [ hw_eq ] using isFinASF_complete w hw );
  contrapose! h_no_spanning9;
  unfold hasSpanningAS;
  simp +zetaDelta at *;
  use r;
  refine' ⟨ hr, L - ( ( 85 * ( w.length - 1 ) - r ) / 2 + 1 ), _, _ ⟩;
  · omega;
  · convert sameParikh4_of_perm hperm using 1;
    grind

/-! ### Main inductive block bound -/

/-- **Block bound by well-founded induction.**
For any ASF word `w`, an abelian square in `g(w)` spans at most 5 blocks.

Proved by strong induction on `w.length`:
- If `m < w.length`: extract subword `w'` of length `m`, apply IH.
- If `m = w.length ≤ 5`: trivial.
- If `m = w.length ∈ {6,7,8,9,10,11,12}`: contradiction via spanning checks.
- If `m = w.length ≥ 13`: requires Parikh matrix bridge. -/
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
      -- The spanning AS is in g(w) at (r, L)
      -- Simplify the raw expressions in hlen' and hperm' using i/85 = 0
      have hi85 : i / 85 = 0 := by omega
      simp only [hi85, Nat.sub_zero, List.drop_zero,
        List.take_of_length_le (by omega : w.length ≤ (i + 2 * L - 1) / 85 + 1)] at hlen' hperm'
      -- Use spanning checks for contradiction
      -- We know m ≥ 6 and m = w.length
      rcases Nat.lt_or_ge m 7 with hm6 | hm7
      · exact no_spanning6_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
      · rcases Nat.lt_or_ge m 8 with hm7' | hm8
        · exact no_spanning7_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
        · rcases Nat.lt_or_ge m 9 with hm8' | hm9
          · exact no_spanning8_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
          · rcases Nat.lt_or_ge m 10 with hm9' | hm10
            · exact no_spanning9_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
            · rcases Nat.lt_or_ge m 11 with hm10' | hm11
              · exact no_spanning10_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
              · rcases Nat.lt_or_ge m 12 with hm11' | hm12
                · exact no_spanning11_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
                · rcases Nat.lt_or_ge m 13 with hm12' | hm13
                  · exact no_spanning12_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
                  · rcases Nat.lt_or_ge m 14 with hm13' | hm14
                    · exact no_spanning13_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
                    · -- m ≥ 14: spanning AS for ASF word of length ≥ 14
                      exact no_spanning_large w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'

end KE92
