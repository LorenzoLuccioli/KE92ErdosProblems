import KE92ErdosProblems.KE92.PaperCoreDefs
import KE92ErdosProblems.KE92.KeranenBounded
import KE92ErdosProblems.KE92.KeranenBounded5a
import KE92ErdosProblems.KE92.KeranenBounded5b
import KE92ErdosProblems.KE92.KeranenBounded5c
import KE92ErdosProblems.KE92.KeranenBounded5d
import KE92ErdosProblems.KE92.BlockBoundBridge

/-!
# KE92 — Keränen 1992 paper formalization

Common infrastructure for the Keränen 1992 paper workspace.  This file
re-exports every definition and helper lemma needed by the downstream
Erdős problem files (`Erdos231.lean`, `Erdos192.lean`).

## Dependency structure

- `PaperCoreDefs.lean` — shared definitions and basic lemmas (abelian-square-free,
  Parikh walk, 3-AP, Keränen morphism, boolean ASF check, subword lemmas).
- `KeranenBounded.lean`, `KeranenBounded5a–d.lean` — bounded verification by
  `native_decide` (morphism preservation for words of length ≤ 5).
- `BlockBound*.lean`, `BlockBoundBridge*.lean`, `BlockBoundSpanning*.lean` —
  Parikh-matrix finite reduction (any abelian square in the morphism image
  spans ≤ 5 letter-blocks).

## Main results proved here

- `morphism_preserves_le5` — the morphism image of any ASF word of length ≤ 5
  is abelian-square-free.
- `keranenG_preserves_ASF` — Keränen's morphism preserves abelian-square-freeness.
- `exists_finASF_all_lengths` — for every `n`, there exists a length-`n` ASF word
  on four letters.
- `exists_inf_abelianSquareFree_four` — there exists an infinite ASF word on four
  letters.
-/

set_option maxHeartbeats 4000000

namespace KE92

/-! ### Bounded verification for small lengths -/

/-- Morphism preservation for length 1. -/
theorem morphism_check_1 :
    ∀ a : Fin 4, isFinASF [a] = true →
    isFinASF (applyKeranenG [a]) = true := by native_decide

/-- Morphism preservation for length 2. -/
theorem morphism_check_2 :
    ∀ a b : Fin 4, isFinASF [a, b] = true →
    isFinASF (applyKeranenG [a, b]) = true := by native_decide

/-- Morphism preservation for length 3. -/
theorem morphism_check_3 :
    ∀ a b c : Fin 4, isFinASF [a, b, c] = true →
    isFinASF (applyKeranenG [a, b, c]) = true := by native_decide

/-- Combined: for any ASF word of length ≤ 5, the morphism image is ASF. -/
theorem morphism_preserves_le5 (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hlen : w.length ≤ 5) : FinAbelianSquareFree (applyKeranenG w) := by
  obtain ⟨a, b, c, d, e, hw_eq⟩ :
      ∃ a b c d e : Fin 4,
        w = [a, b, c, d, e] ∨ w = [a, b, c, d] ∨ w = [a, b, c] ∨
        w = [a, b] ∨ w = [a] ∨ w = [] := by
    rcases w with (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | w⟩⟩⟩⟩⟩) <;>
      simp_all +decide
    linarith
  rcases hw_eq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (have := isFinASF_complete _ hw; simp_all +decide only [isFinASF_sound])
  · fin_cases a <;> simp_all +decide only [isFinASF_sound]
    · exact isFinASF_sound _ (morphism_check_5a b c d e this)
    · exact isFinASF_sound _ (morphism_check_5b _ _ _ _ this)
    · exact isFinASF_sound _ (morphism_check_5c _ _ _ _ this)
    · exact isFinASF_sound _ (morphism_check_5d _ _ _ _ this)
  · exact isFinASF_sound _ (morphism_check_4 a b c d this)
  · exact isFinASF_sound _ (morphism_check_3 a b c this)
  · exact isFinASF_sound _ (morphism_check_2 a b this)
  · exact isFinASF_sound _ (morphism_check_1 a this)

/-! ### Abelian-square localization in uniform morphism images -/

/-- Length of `g(w.take n)` when `n ≤ w.length`. -/
private lemma applyKeranenG_take_length (w : List (Fin 4)) (n : ℕ) (hn : n ≤ w.length) :
    (applyKeranenG (w.take n)).length = 85 * n := by
  rw [applyKeranenG_length, List.length_take, Nat.min_eq_left hn]

/-- Abelian square localization for Keränen's uniform morphism.

If `applyKeranenG w` has an abelian square at position `(i, L)`, then
`applyKeranenG w'` is not abelian-square-free, where `w'` is the subword
`w.drop a |>.take m` with `a = i / 85` and `m = (i+2L−1)/85 − a + 1`. -/
private lemma abelianSquare_flatMap_localize (w : List (Fin 4))
    (i L : ℕ) (hL : L > 0)
    (hlen : i + 2 * L ≤ (applyKeranenG w).length)
    (hperm : ((applyKeranenG w).drop i |>.take L).Perm
             ((applyKeranenG w).drop (i + L) |>.take L)) :
    ¬FinAbelianSquareFree
      (applyKeranenG (w.drop (i / 85) |>.take ((i + 2 * L - 1) / 85 - i / 85 + 1))) := by
  contrapose! hperm
  set a := i / 85
  set r := i % 85
  set m := (i + 2 * L - 1) / 85 - a + 1
  have ha : a ≤ w.length := by rw [applyKeranenG_length] at hlen; omega
  have hm : a + m ≤ w.length := by rw [applyKeranenG_length] at hlen; omega
  have hr : r + 2 * L ≤ 85 * m := by omega
  have h_split :
      applyKeranenG w =
        applyKeranenG (w.take a) ++ applyKeranenG (w.drop a |>.take m) ++
          applyKeranenG (w.drop (a + m)) := by
    have h_split : w = w.take a ++ (w.drop a |>.take m) ++ w.drop (a + m) := by
      simp +arith +decide
    unfold applyKeranenG
    simp +decide
    conv_lhs => rw [h_split, List.flatMap_append, List.flatMap_append]
    rw [List.append_assoc]
  have h_simplify :
      List.take L (List.drop i (applyKeranenG w)) =
        List.take L (List.drop r (applyKeranenG (w.drop a |>.take m))) ∧
      List.take L (List.drop (i + L) (applyKeranenG w)) =
        List.take L (List.drop (r + L) (applyKeranenG (w.drop a |>.take m))) := by
    have h1 :
        List.drop i (applyKeranenG w) =
          List.drop r
            (applyKeranenG (w.drop a |>.take m) ++ applyKeranenG (w.drop (a + m))) ∧
        List.drop (i + L) (applyKeranenG w) =
          List.drop (r + L)
            (applyKeranenG (w.drop a |>.take m) ++ applyKeranenG (w.drop (a + m))) := by
      have h2 :
          List.drop i (applyKeranenG w) =
            List.drop (i - 85 * a) (List.drop (85 * a) (applyKeranenG w)) ∧
          List.drop (i + L) (applyKeranenG w) =
            List.drop (i + L - 85 * a) (List.drop (85 * a) (applyKeranenG w)) := by
        simp +decide [List.drop_drop]
        lia
      rw [h2.1, h2.2, h_split]
      simp +decide [List.drop_append, applyKeranenG_take_length _ _ ha]
      have hir : i - 85 * a = r := by
        have hmod : r + 85 * a = i := by
          simpa [a, r] using Nat.mod_add_div i 85
        omega
      have hiLr : i + L - 85 * a = r + L := by
        have hmod : r + 85 * a = i := by
          simpa [a, r] using Nat.mod_add_div i 85
        omega
      simp +decide [hir, hiLr]
    simp_all +decide [List.drop_append, applyKeranenG_length]
    omega
  simp_all +decide [FinAbelianSquareFree]
  convert hperm r L hL _ using 1
  rw [applyKeranenG_length]
  simp +arith +decide [*]
  exact le_trans (by linarith)
    (Nat.mul_le_mul_left _
      (le_min (Nat.le_refl _) (Nat.le_sub_of_add_le (by linarith))))

/-! ### Block bound (Parikh-matrix finite reduction) -/

/-- **Block bound** (Keränen's Parikh-matrix analysis).

For any ASF word `w`, an abelian square in `applyKeranenG w` at position
`(i, L)` spans at most 5 letter-blocks. -/
private lemma abelianSquare_block_bound (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (i L : ℕ) (hL : L > 0)
    (hlen : i + 2 * L ≤ (applyKeranenG w).length)
    (hperm : ((applyKeranenG w).drop i |>.take L).Perm
             ((applyKeranenG w).drop (i + L) |>.take L)) :
    (i + 2 * L - 1) / 85 - i / 85 + 1 ≤ 5 :=
  abelianSquare_block_bound_inductive w hw i L hL hlen hperm

/-! ### Main theorem -/

/-- **Keränen's morphism preserves abelian-square-freeness.**

Proved by:
1. **Localization** (`abelianSquare_flatMap_localize`): any abelian square in
   `g(w)` at `(i, L)` gives a non-ASF witness in `g(w')` where `w'` is a
   subword of `w`.
2. **Block bound** (`abelianSquare_block_bound`): the subword has `≤ 5`
   letters.
3. **Bounded verification** (`morphism_preserves_le5`): `g(w')` is ASF for
   all ASF `w'` with `|w'| ≤ 5`.

This yields a contradiction. -/
theorem keranenG_preserves_ASF (w : List (Fin 4)) (hw : FinAbelianSquareFree w) :
    FinAbelianSquareFree (applyKeranenG w) := by
  intro i L hL hlen hperm
  set a := i / 85
  set m := (i + 2 * L - 1) / 85 - a + 1
  set w' := w.drop a |>.take m
  have ham : a + m ≤ w.length := by
    rw [applyKeranenG_length] at hlen
    have : i + 2 * L - 1 < 85 * w.length := by omega
    have : (i + 2 * L - 1) / 85 < w.length := Nat.div_lt_of_lt_mul this
    omega
  have hw'_asf : FinAbelianSquareFree w' := finASF_subword w hw a m ham
  have hw'_len : w'.length ≤ 5 := by
    have := abelianSquare_block_bound w hw i L hL hlen hperm
    simp only [w', List.length_take, List.length_drop]
    omega
  have hgw'_asf : FinAbelianSquareFree (applyKeranenG w') :=
    morphism_preserves_le5 w' hw'_asf hw'_len
  exact absurd hgw'_asf (abelianSquare_flatMap_localize w i L hL hlen hperm)

/-! ### Downstream theorems -/

private theorem keranenIterate_ASF (n : ℕ) : FinAbelianSquareFree (keranenIterate n) := by
  induction n with
  | zero => exact singleton_finASF 0
  | succ n ih => exact keranenG_preserves_ASF _ ih

/-- **Keränen 1992, computational content.** For every `n`, there exists a finite
abelian-square-free word of length `n` on four letters. -/
theorem exists_finASF_all_lengths :
    ∀ m : ℕ, ∃ w : List (Fin 4), w.length = m ∧ FinAbelianSquareFree w := by
  intro m
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m ≤ 85 ^ n :=
    ⟨m, le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by omega) m))⟩
  exact ⟨(keranenIterate n).take m,
    by rw [List.length_take, keranenIterate_length]; omega,
    finASF_prefix _ (keranenIterate_ASF n) m (by rw [keranenIterate_length]; omega)⟩

theorem exists_inf_from_all_lengths
    (hall : ∀ m : ℕ, ∃ w : List (Fin 4), w.length = m ∧ FinAbelianSquareFree w) :
    ∃ f : ℕ → Fin 4, InfAbelianSquareFree f := by
  obtain ⟨f, hf⟩ :
      ∃ f : ℕ → Fin 4,
        ∀ m : ℕ, FinAbelianSquareFree (List.ofFn (fun i : Fin m => f i)) := by
    set extendable : List (Fin 4) → Prop := fun p =>
      ∀ m : ℕ, ∃ w : List (Fin 4),
        w.length = p.length + m ∧ FinAbelianSquareFree w ∧ w.take p.length = p
    have h_pigeonhole :
        ∀ p : List (Fin 4), extendable p → ∃ c : Fin 4, extendable (p ++ [c]) := by
      intro p hp
      by_contra h_contra
      push_neg at h_contra
      have h_finite :
          ∀ c : Fin 4, ∃ m : ℕ, ∀ w : List (Fin 4),
            w.length = p.length + 1 + m → FinAbelianSquareFree w →
            w.take (p.length + 1) ≠ p ++ [c] := by
        intro c; specialize h_contra c; unfold extendable at h_contra; aesop
      obtain ⟨M, hM⟩ :
          ∃ M : ℕ, ∀ c : Fin 4, ∀ w : List (Fin 4),
            w.length = p.length + 1 + M → FinAbelianSquareFree w →
            w.take (p.length + 1) ≠ p ++ [c] := by
        choose m hm using h_finite
        use Finset.univ.sup m
        intros c w hwASF hw
        specialize hm c (w.take (p.length + 1 + m c)) ?_ ?_ <;>
          simp_all +decide [List.take_take]
        · exact Finset.le_sup (f := m) (Finset.mem_univ c)
        · exact finASF_prefix _ hw _
            (by linarith [Finset.le_sup (f := m) (Finset.mem_univ c)])
      obtain ⟨w, hw₁, hw₂, hw₃⟩ := hp (1 + M)
      have h_take : ∃ c : Fin 4, List.take (p.length + 1) w = p ++ [c] := by
        rw [← List.take_append_drop p.length w, hw₃]
        rcases x : List.drop p.length w with (_ | ⟨c, _ | ⟨d, l⟩⟩) <;>
          simp_all +decide [List.take_append]
      grind
    choose! c hc using h_pigeonhole
    have h_rec :
        ∃ f : ℕ → Fin 4, ∀ n : ℕ,
          f n = c (List.ofFn (fun i : Fin n => f i)) := by
      have h_rec :
          ∀ n : ℕ, ∃ f : ℕ → Fin 4,
            ∀ i < n, f i = c (List.ofFn (fun j : Fin i => f j)) := by
        intro n
        induction' n with n ih
        · exact ⟨fun _ => 0, by norm_num⟩
        · obtain ⟨f, hf⟩ := ih
          use fun i =>
            if i < n then f i
            else c (List.ofFn (fun j : Fin i =>
              if j.val < n then f j.val
              else c (List.ofFn (fun k : Fin j.val => f k.val))))
          grind
      choose f hf using h_rec
      have h_eq : ∀ n m : ℕ, n ≤ m → ∀ i < n, f n i = f m i := by
        intros n m hnm i hi
        induction' i using Nat.strong_induction_on with i ih
        grind +qlia
      use fun n => f (n + 1) n
      grind
    obtain ⟨f, hf⟩ := h_rec
    use f
    have h_extendable : ∀ n : ℕ, extendable (List.ofFn (fun i : Fin n => f i)) := by
      intro n
      induction' n with n ih
      · exact fun m => by
          obtain ⟨w, hw₁, hw₂⟩ := hall m
          exact ⟨w, by simpa using hw₁, hw₂, by simp +decide⟩
      · convert hc _ ih using 1
        refine' List.ext_get _ _ <;> simp +decide [← hf]
        intro i hi₁ hi₂
        rcases i with (_ | i) <;> simp +decide [List.getElem_append, List.getElem_ofFn]
        · rintro rfl; rfl
        · grind +qlia
    intro m
    obtain ⟨w, hw₁, hw₂, hw₃⟩ := h_extendable m 0
    grind
  use f
  intro i l hl h
  have := hf (i + 2 * l)
  simp_all +decide [FinAbelianSquareFree]
  contrapose! hf
  refine ⟨i + 2 * l, i, l, hl, by linarith, ?_⟩
  convert h using 1 <;> (refine List.ext_get ?_ ?_ <;> simp +decide [infBlock] <;> omega)

/-- **Keränen 1992, Theorem 1.** There exists an infinite abelian-square-free
word over a four-letter alphabet. -/
theorem exists_inf_abelianSquareFree_four :
    ∃ f : ℕ → Fin 4, InfAbelianSquareFree f :=
  exists_inf_from_all_lengths exists_finASF_all_lengths

end KE92
