import KE92ErdosProblems.KE92

/-!
# Erdős Problem 192 — Walks avoiding 3-term arithmetic progressions

## Connection to abelian squares

Given a word `f : ℕ → Fin k`, the **Parikh walk** is the sequence `V(n) ∈ ℕ^k` where
`V(n)_c` counts occurrences of letter `c` among `f(0), …, f(n−1)`. Each step of the
walk is a standard basis vector `e_{f(n)}` ("positive unit step").

Three positions `a < b < c` satisfy `V(a) + V(c) = 2 · V(b)` (a **3-term AP** in the
walk) if and only if `f` contains an abelian square at position `a` with half-length
`b − a`. Therefore, the Parikh walk is 3-AP-free if and only if `f` is
abelian-square-free.

## Main result

* `KE92.erdos_problem_192` — There exists an infinite walk in `ℕ^4` with positive
  unit steps whose sequence of visited positions contains no 3-term AP.
-/

namespace KE92

/-- **Erdős Problem 192.**
There exists an infinite walk in `ℕ^4` with positive unit steps (each step is
a standard basis vector `eᵢ` for some `i ∈ Fin 4`) such that the sequence of
visited positions contains no 3-term arithmetic progression. -/
theorem erdos_problem_192 :
    ∃ f : ℕ → Fin 4, parikhAPFree f := by
  obtain ⟨f, hf⟩ := exists_inf_abelianSquareFree_four
  exact ⟨f, (infAbelianSquareFree_iff_parikhAPFree f).mp hf⟩

end KE92
