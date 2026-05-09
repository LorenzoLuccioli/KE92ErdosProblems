import KE92ErdosProblems.KE92.PaperCoreDefs

/-!
# Block bound: computational helpers (base file)

Core definitions and the spanning-6/delta-zero checks.
Spanning-7, spanning-8, Parikh norm bound, and 3-letter bound
are in separate files to manage native_decide compilation time.
-/

set_option maxHeartbeats 8000000

namespace KE92

/-! ### Fast Parikh comparison -/

/-- Fast abelian-equality check for `Fin 4` lists via letter counting. -/
def sameParikh4 (l1 l2 : List (Fin 4)) : Bool :=
  l1.count 0 == l2.count 0 &&
  l1.count 1 == l2.count 1 &&
  l1.count 2 == l2.count 2 &&
  l1.count 3 == l2.count 3

/-! ### General spanning abelian square check -/

/-- Check whether `g(w)` has an abelian square spanning all `w.length` blocks. -/
def hasSpanningAS (w : List (Fin 4)) : Bool :=
  let m := w.length
  let gw := applyKeranenG w
  let n := gw.length
  (List.range 85).any fun i =>
    let lMin := (85 * (m - 1) - i + 2) / 2
    let lMax := (n - i) / 2
    (List.range (lMax - lMin + 1)).any fun k =>
      let ll := lMin + k
      sameParikh4 (gw.drop i |>.take ll) (gw.drop (i + ll) |>.take ll)

/-! ### Spanning-6 abelian square check -/

def hasSpanning6AS (w : List (Fin 4)) : Bool :=
  let gw := applyKeranenG w
  (List.range 85).any fun i =>
    let lMin := (426 - i + 1) / 2
    let lMax := (510 - i) / 2
    (List.range (lMax - lMin + 1)).any fun k =>
      let ll := lMin + k
      (gw.drop i |>.take ll).isPerm (gw.drop (i + ll) |>.take ll)

/-- No ASF word of length 6 has a spanning-6 abelian square in its morphism image. -/
theorem no_spanning6_abelianSquare :
    ∀ a b c d e f : Fin 4,
      isFinASF [a, b, c, d, e, f] = true →
      hasSpanning6AS [a, b, c, d, e, f] = false := by native_decide

/-! ### δ = 0 impossibility -/

def cumParikhCount (a : Fin 4) (k : Nat) (c : Fin 4) : Nat :=
  ((keranenG a).take k).count c

def sliceParikhCount (a : Fin 4) (lo hi : Nat) (c : Fin 4) : Int :=
  (cumParikhCount a hi c : Int) - (cumParikhCount a lo c : Int)

def boundaryDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let t := (2 * s + 85 * 1000 - r) % 85
  sliceParikhCount wb s 85 c + sliceParikhCount we 0 t c
  - sliceParikhCount wa r 85 c - sliceParikhCount wb 0 s c

theorem delta_zero_forces_boundary_eq :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      wa ≠ wb → wb ≠ we →
      ¬(boundaryDelta wa wb we r.val s.val 0 = 0 ∧
        boundaryDelta wa wb we r.val s.val 1 = 0 ∧
        boundaryDelta wa wb we r.val s.val 2 = 0 ∧
        boundaryDelta wa wb we r.val s.val 3 = 0) := by native_decide

/-! ### Parikh norm bound definitions -/

/-- Product of adjugate of M^T with delta vector. -/
def adjMTtimesDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let d : Fin 4 → Int := boundaryDelta wa wb we r s
  match c with
  | 0 => -701 * d 0 + (-531) * d 1 + 4059 * d 2 + (-2316) * d 3
  | 1 => (-2316) * d 0 + (-701) * d 1 + (-531) * d 2 + 4059 * d 3
  | 2 => 4059 * d 0 + (-2316) * d 1 + (-701) * d 2 + (-531) * d 3
  | 3 => (-531) * d 0 + 4059 * d 1 + (-2316) * d 2 + (-701) * d 3

end KE92
