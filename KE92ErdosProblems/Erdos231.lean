import KE92ErdosProblems.KE92

/-!
# Erdős Problem 231 — Infinite abelian-square-free words

Erdős asked whether abelian squares are avoidable on a finite alphabet.
An *abelian square* is a nonempty word `PQ` where `Q` is a permutation of `P`.
Keränen (1992) proved that abelian squares are avoidable on four letters by
constructing an abelian-square-free endomorphism of length 85 whose iteration
gives an infinite abelian-square-free word.

## Main result

* `KE92.erdos_problem_231` — There exists an infinite word on 4 letters that is
  abelian-square-free.
* `KE92.erdos_problem_231_finite` — For every `n`, there exists a length-`n`
  abelian-square-free word on four letters.
-/

namespace KE92

/-- **Erdős Problem 231 (infinite formulation).**
There exists an infinite word over a four-letter alphabet that contains
no abelian square. -/
theorem erdos_problem_231 :
    ∃ f : ℕ → Fin 4, InfAbelianSquareFree f :=
  exists_inf_abelianSquareFree_four

/-- Finite consequence: for every `n`, there exists an abelian-square-free
word of length `n` on four letters. -/
theorem erdos_problem_231_finite :
    ∀ n : ℕ, ∃ w : List (Fin 4), w.length = n ∧
      ∀ i l, l > 0 → i + 2 * l ≤ w.length →
        ¬(w.drop i |>.take l).Perm (w.drop (i + l) |>.take l) := by
  intro n
  obtain ⟨f, hf⟩ := exists_inf_abelianSquareFree_four
  refine ⟨infBlock f 0 n, infBlock_length f 0 n, ?_⟩
  intro i l hl hlen
  simp [infBlock_length] at hlen
  intro hperm
  apply hf i l hl
  convert hperm using 1 <;>
    (refine List.ext_get ?_ ?_ <;> simp +arith +decide [infBlock] <;> omega)

end KE92
