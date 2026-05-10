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

## Main results

* `KE92.erdos_problem_192` — There exists an infinite walk in `ℕ^4` with positive
  unit steps whose sequence of visited positions contains no 3-term AP.
* `KE92.erdos_problem_192_classification` — Full classification: every infinite
  positive-unit-step walk in `ℤ^d` (d ≤ 3) contains a 3-term AP, while `d ≥ 4`
  admits AP-free walks.
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

/-! ### Classification helpers -/

/-
Completeness of `isFinASF3`: every abelian-square-free word over `Fin 3`
satisfies `isFinASF3 w = true`.
-/
private theorem isFinASF3_complete (w : List (Fin 3)) (hw : FinAbelianSquareFree w) :
    isFinASF3 w = true := by
  unfold isFinASF3;
  simp +zetaDelta at *;
  intro i hi j hj hij; contrapose! hw;
  exact fun h => h i ( j + 1 ) ( Nat.succ_pos _ ) hij ( by simpa [ List.isPerm_iff ] using hw )

/-
`infBlock` of `e ∘ f` is the map of `infBlock` of `f`.
-/
private theorem infBlock_comp {α β : Type*} (e : α → β) (f : ℕ → α) (s l : ℕ) :
    infBlock (e ∘ f) s l = (infBlock f s l).map e := by
  unfold infBlock; simp +decide [ List.map_map, Function.comp_def ] ;

/-
Infinite abelian-square-freeness is preserved under composition with
an injection.
-/
private theorem inf_asf_comp_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : ℕ → α) (e : α → β) (he : Function.Injective e)
    (hf : InfAbelianSquareFree f) : InfAbelianSquareFree (e ∘ f) := by
  intro i l hl; specialize hf i l hl; simp_all +decide [ InfAbelianSquareFree, List.map_eq_map_iff ] ;
  contrapose! hf;
  rw [ ← List.map_perm_map_iff he ];
  unfold infBlock at *; aesop;

/-
No infinite word over `Fin 3` is abelian-square-free.
Proof: by `max_asf_3letters`, every length-8 prefix has an abelian square.
-/
private theorem no_inf_asf_three (f : ℕ → Fin 3) : ¬InfAbelianSquareFree f := by
  intro hf
  have h8 : FinAbelianSquareFree (infBlock f 0 8) := by
    -- For any i, l, if the two blocks of length l starting at i and i+l are permutations, then they are also permutations of the infinite word.
    intro i l hl h
    have := hf i l hl
    contrapose! this
    simp_all +decide [ infBlock ];
    convert this using 1;
    · refine' List.ext_get _ _ <;> simp +arith +decide [ List.get ];
      omega;
    · refine' List.ext_get _ _ <;> simp +arith +decide;
      omega;
  convert isFinASF3_complete _ h8 using 1;
  simp [infBlock];
  exact max_asf_3letters _ _ _ _ _ _ _ _

/-
For `d ≤ 3`, every infinite word over `Fin d` has a Parikh AP.
-/
private theorem hasParikhAP_of_le_three {d : ℕ} (hd : d ≤ 3) (f : ℕ → Fin d) :
    hasParikhAP f := by
  -- Let `e := Fin.castLE hd : Fin d → Fin 3`. This is injective (Fin.castLE_injective).
  set e : Fin d → Fin 3 := fun x => Fin.castLE hd x
  have he_inj : Function.Injective e := by
    exact fun x y h => Fin.ext <| by simpa [ Fin.ext_iff ] using h;
  -- If `InfAbelianSquareFree f`, then by `inf_asf_comp_inj`, `InfAbelianSquareFree (e ∘ f)`.
  by_cases h_inf_asf : InfAbelianSquareFree f;
  · exact False.elim <| no_inf_asf_three ( e ∘ f ) <| inf_asf_comp_inj f e he_inj h_inf_asf;
  · exact Classical.not_not.1 fun h => h_inf_asf <| by simpa [ h ] using infAbelianSquareFree_iff_parikhAPFree f |>.2 h;

/-
For `d ≥ 4`, there exists an infinite parikhAPFree word over `Fin d`.
-/
private theorem exists_parikhAPFree_of_ge_four {d : ℕ} (hd : 4 ≤ d) :
    ∃ f : ℕ → Fin d, parikhAPFree f := by
  -- From exists_inf_abelianSquareFree_four, get f : ℕ → Fin 4 with InfAbelianSquareFree f.
  obtain ⟨f, hf⟩ := exists_inf_abelianSquareFree_four;
  use fun n => Fin.castLE hd (f n);
  exact infAbelianSquareFree_iff_parikhAPFree _ |>.1 ( inf_asf_comp_inj f ( Fin.castLE hd ) ( Fin.castLE_injective _ ) hf )

/-- **Erdős Problem 192 — Full classification.**

An infinite walk in `ℤ^d` with positive unit steps has all its visited positions
free of 3-term arithmetic progressions if and only if `d ≥ 4`.

Equivalently, `(∀ f, hasParikhAP f) ↔ d ≤ 3`:
* **`d ≤ 3`**: every infinite word over a ≤ 3-letter alphabet contains an abelian
  square (no length-8 word over 3 letters is abelian-square-free), so every
  positive-unit-step walk in dimensions ≤ 3 has a 3-term AP.
* **`d ≥ 4`**: Keränen's 85-uniform morphism produces an infinite
  abelian-square-free word over 4 letters, giving a walk in `ℤ^4` (and hence
  in `ℤ^d` for all `d ≥ 4`) with no 3-term AP. -/
theorem erdos_problem_192_classification (d : ℕ) :
    (∀ f : ℕ → Fin d, hasParikhAP f) ↔ d ≤ 3 := by
  constructor
  · intro h
    by_contra hd
    push_neg at hd
    obtain ⟨f, hf⟩ := exists_parikhAPFree_of_ge_four (by omega : 4 ≤ d)
    exact hf (h f)
  · intro hd f
    exact hasParikhAP_of_le_three hd f

end KE92