import KE92ErdosProblems.KE92.BlockBound
import KE92ErdosProblems.KE92.BlockBoundParikh

/-!
# Parikh bridge infrastructure for the spanning abelian square elimination

This file contains the Parikh-matrix bridge infrastructure for proving that
ASF words of length m ≥ 14 have no spanning abelian square in their
Keränen morphism image.

## Overview

A *spanning* abelian square in g(w) at offset r with half-length L means:
- The AS covers all m = w.length blocks: (r + 2L - 1)/85 + 1 = m
- The two halves have the same Parikh vector (letter counts)

The midpoint falls in block k = (r + L) / 85 with offset s = (r + L) % 85.
The boundary letters are wa = w[0], wb = w[k], we = w[m-1].

The Parikh equality of the two halves yields the matrix equation:
  M · v = δ(wa, wb, we, r, s)
where v is the inner block Parikh defect and M is the 4×4 Parikh matrix
of the morphism.

## Computationally verified properties

1. `parikh_norm_bound` (in BlockBoundParikh.lean): ‖v‖₁ ≤ 3
2. `parikh_v_sum_zero_norm_le2`: For Σv = 0 and ‖v‖₁ ≤ 2, v ∈ {e_X − e_Y : X,Y ∈ {wa,wb,we}}
3. `parikh_v_norm1_is_wb`: For |Σv| = 1 and ‖v‖₁ = 1, v = Σv · e_{wb}
4. The ‖v‖₁ = 3 case (even m only, 40 patterns) requires deeper analysis.
-/

set_option maxHeartbeats 8000000

namespace KE92

/-! ### Computational verification of v-pattern structure -/

/-- Helper: compute v from boundary configuration -/
def parikhSolutionVec (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  adjMTtimesDelta wa wb we r s c / 43435

/-- Helper: check if solution exists (divisibility) -/
def hasParikhSolution (wa wb we : Fin 4) (r s : Nat) : Bool :=
  adjMTtimesDelta wa wb we r s 0 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 1 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 2 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 3 % 43435 = 0

/-- Unit vector difference: (e_X - e_Y)_c -/
def unitDiffAt (x y c : Fin 4) : Int :=
  (if c = x then (1 : Int) else 0) + (if c = y then (-1 : Int) else 0)

/-- **v-pattern check for Σv = 0 (odd m), ‖v‖₁ ≤ 2.**

For all boundary configurations where the Parikh equation has an integer
solution with Σv = 0 and ‖v‖₁ ≤ 2, v equals e_X − e_Y for some
X, Y ∈ {wa, wb, we}.

This covers:
- v = 0 (when X = Y): handled by `delta_zero_forces_boundary_eq`
- v = e_{wa} − e_{wb}: abelian square at position (0, k) in w
- v = e_{wb} − e_{we}: abelian square at position (1, k) in w
- Other boundary-letter pairs: abelian square at different positions in w
-/
theorem parikh_v_sum_zero_norm_le2 :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      hasParikhSolution wa wb we r.val s.val = true →
      (parikhSolutionVec wa wb we r.val s.val 0 +
       parikhSolutionVec wa wb we r.val s.val 1 +
       parikhSolutionVec wa wb we r.val s.val 2 +
       parikhSolutionVec wa wb we r.val s.val 3 = 0) →
      ((parikhSolutionVec wa wb we r.val s.val 0).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 1).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 2).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 3).natAbs ≤ 2) →
      ∃ x y : Fin 4, (x = wa ∨ x = wb ∨ x = we) ∧
                      (y = wa ∨ y = wb ∨ y = we) ∧
      (∀ c : Fin 4, parikhSolutionVec wa wb we r.val s.val c = unitDiffAt x y c) := by
  native_decide

/-- **v-pattern check for |Σv| = 1 (even m), ‖v‖₁ = 1.**

For all boundary configurations where the Parikh equation has an integer
solution with |Σv| = 1 and ‖v‖₁ = 1, v = Σv · e_{wb}. -/
theorem parikh_v_norm1_is_wb :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      hasParikhSolution wa wb we r.val s.val = true →
      let sv := parikhSolutionVec wa wb we r.val s.val 0 +
                parikhSolutionVec wa wb we r.val s.val 1 +
                parikhSolutionVec wa wb we r.val s.val 2 +
                parikhSolutionVec wa wb we r.val s.val 3
      (sv = 1 ∨ sv = -1) →
      ((parikhSolutionVec wa wb we r.val s.val 0).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 1).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 2).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 3).natAbs = 1) →
      (∀ c : Fin 4, parikhSolutionVec wa wb we r.val s.val c =
        if c = wb then sv else 0) := by
  native_decide

/-- **v-pattern check for Σv = 0 (odd m), ‖v‖₁ = 2: only easy patterns.**

For all boundary configs where M·v = δ has solution with Σv = 0 and ‖v‖₁ = 2,
v is always e_{wb}−e_{wa} or e_{we}−e_{wb}. These are exactly the patterns
that give clean abelian-square constructions at positions (0,k) and (1,k)
respectively, with no conditions on the boundary letters. -/
theorem parikh_v_norm2_is_easy :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      hasParikhSolution wa wb we r.val s.val = true →
      (parikhSolutionVec wa wb we r.val s.val 0 +
       parikhSolutionVec wa wb we r.val s.val 1 +
       parikhSolutionVec wa wb we r.val s.val 2 +
       parikhSolutionVec wa wb we r.val s.val 3 = 0) →
      ((parikhSolutionVec wa wb we r.val s.val 0).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 1).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 2).natAbs +
       (parikhSolutionVec wa wb we r.val s.val 3).natAbs = 2) →
      (∀ c : Fin 4, parikhSolutionVec wa wb we r.val s.val c = unitDiffAt wb wa c) ∨
      (∀ c : Fin 4, parikhSolutionVec wa wb we r.val s.val c = unitDiffAt we wb c) := by
  native_decide

end KE92
