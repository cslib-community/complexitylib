/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.Sperner
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import Mathlib.Data.FinEnum
import Mathlib.Tactic.FinCases

/-!
# `PPAD`-completeness of circuit `2D-SPERNER`

Chen and Deng proved that the two-dimensional Sperner / discrete Brouwer problem is
`PPAD`-complete [ChenDeng2006], cited as the `PPAD`-completeness of `Brouwer^{f₂}` in
[ChenDengTeng2009] (Section 4.1, after Definition 4.5). This module reduces `EndOfLine` to
`Sperner2D` (`EndOfLine_searchReducible_Sperner2D`), establishing `Sperner2D_searchHard` and
`Sperner2D_searchComplete`.

## Construction

An `EndOfLine` instance of bit-width `n` has `N = 2 ^ n` vertices `0, …, N - 1`, embedded into
`16 × 16` tiles `[16 * (X + 1), 16 * (X + 1) + 15] × [16 * (Y + 1), 16 * (Y + 1) + 15]` inside the
`2 ^ (n + 5) × 2 ^ (n + 5)` grid of `Sperner2D`:

* Each active edge `u → v` (`u ≠ v`, `v ≠ 0`) follows the L-path `(u, u) → (v, u) → (v, v)`
  along row `u` and column `v`. Because edges have out-degree and in-degree at most one, no two
  horizontal segments share a row, no two vertical segments share a column, and corners `(v, u)`
  never coincide with passing segments.
* Whenever a horizontal and a vertical edge cross at an off-diagonal tile `(X, Y)`, local
  uncrossing turns swap their exit ports inside the `16 × 16` tile, preserving in- and out-degrees
  at every grid point and leaving the set of unbalanced vertices invariant.
* Directed paths are painted as 2-wide signed channels (`1` on the left bank, `2` on the right
  bank, `0` outside), matching across every coarse tile seam (`eastPort = westPort`,
  `northPort = southPort`). The boundary entrance `start = ⟨false, 0, 0⟩` of `Sperner2D` either
  feeds into vertex `0` when `0 ^ n` has an outgoing edge or terminates immediately at `start`.
* All non-terminal tiles, tile seams, and outer margin strips contain no trichromatic triangles;
  every trichromatic triangle lies either at `start` (when `0 ^ n` lacks an outgoing edge) or at
  the center of a diagonal terminal tile `(X, X)` representing an unbalanced non-zero vertex.

## Main results

* `Cslib.Complexity.EndOfLine_searchReducible_Sperner2D`: `EndOfLine` reduces to `Sperner2D`.
* `Cslib.Complexity.Sperner2D_searchHard`: `Sperner2D` is `PPAD`-hard under `SearchReducible`.
* `Cslib.Complexity.Sperner2D_searchComplete`: `Sperner2D` is `PPAD`-complete.

## References

* [X. Chen and X. Deng, *On the complexity of 2D discrete fixed point problem*][ChenDeng2006]
* [X. Chen, X. Deng and S.-H. Teng, *Settling the complexity of computing two-player Nash
  equilibria*][ChenDengTeng2009]
* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
-/

public section

namespace Cslib.Complexity

open Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Sperner Cslib.Sperner.GridTriangle
open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Signed-bank `16 × 16` tiles -/

private inductive Port : Type
  | none
  | pos
  | neg
  deriving DecidableEq, Repr

private inductive TileKind : Type
  | empty
  | lr | rl | bt | tb
  | wn | nw | es | se | sw | ne
  | crossLB | crossRT | crossLT | crossRB
  | capS | capN | capE | capW
  deriving DecidableEq, Repr

private def TileKind.all : List TileKind :=
  [.empty, .lr, .rl, .bt, .tb, .wn, .nw, .es, .se, .sw, .ne,
   .crossLB, .crossRT, .crossLT, .crossRB, .capS, .capN, .capE, .capW]

private def TileKind.isCap : TileKind → Bool
  | .capS | .capN | .capE | .capW => true
  | _ => false

private def tilePorts : TileKind → Port × Port × Port × Port
  | .empty   => (.none, .none, .none, .none)
  | .lr      => (.pos,  .pos,  .none, .none)
  | .rl      => (.neg,  .neg,  .none, .none)
  | .bt      => (.none, .none, .pos,  .pos)
  | .tb      => (.none, .none, .neg,  .neg)
  | .wn      => (.pos,  .none, .none, .pos)
  | .nw      => (.neg,  .none, .none, .neg)
  | .es      => (.none, .neg,  .neg,  .none)
  | .se      => (.none, .pos,  .pos,  .none)
  | .sw      => (.neg,  .none, .pos,  .none)
  | .ne      => (.none, .pos,  .none, .neg)
  | .crossLB => (.pos,  .pos,  .pos,  .pos)
  | .crossRT => (.neg,  .neg,  .neg,  .neg)
  | .crossLT => (.pos,  .pos,  .neg,  .neg)
  | .crossRB => (.neg,  .neg,  .pos,  .pos)
  | .capS    => (.none, .none, .pos,  .none)
  | .capN    => (.none, .none, .none, .neg)
  | .capE    => (.none, .pos,  .none, .none)
  | .capW    => (.neg,  .none, .none, .none)

private def portColor (p : Port) (i : ℕ) : Fin 3 :=
  match p with
  | .none => 0
  | .pos => if i = 7 then 2 else if i = 8 then 1 else 0
  | .neg => if i = 7 then 1 else if i = 8 then 2 else 0

private def portColorV (p : Port) (i : ℕ) : Fin 3 :=
  match p with
  | .none => 0
  | .pos => if i = 7 then 1 else if i = 8 then 2 else 0
  | .neg => if i = 7 then 2 else if i = 8 then 1 else 0

private def flipColor : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

private def hseg (x0 x1 y0 : ℕ) (pos : Bool) (dx dy : ℕ) : Fin 3 :=
  if x0 ≤ dx ∧ dx ≤ x1 then
    if dy = y0 + 1 then (if pos then 1 else 2)
    else if dy = y0 then (if pos then 2 else 1)
    else 0
  else 0

private def vseg (y0 y1 x0 : ℕ) (pos : Bool) (dx dy : ℕ) : Fin 3 :=
  if y0 ≤ dy ∧ dy ≤ y1 then
    if dx = x0 then (if pos then 1 else 2)
    else if dx = x0 + 1 then (if pos then 2 else 1)
    else 0
  else 0

private def turnBox (cx cy : ℕ) (ix iy ox oy : Int) (dx dy : ℕ) : Fin 3 :=
  if (dx = cx ∨ dx = cx + 1) ∧ (dy = cy ∨ dy = cy + 1) then
    let inCol : Fin 3 := if ix * oy - iy * ox > 0 then 1 else 2
    let sx : Int := if dx = cx then -1 else 1
    let sy : Int := if dy = cy then -1 else 1
    if sx * (-ix + ox) > 0 ∧ sy * (-iy + oy) > 0 then inCol else flipColor inCol
  else 0

private def orCol (a b : Fin 3) : Fin 3 := if a ≠ 0 then a else b
private def firstNZ (l : List (Fin 3)) : Fin 3 := l.foldr orCol 0

private def qWN (rev : Bool) (dx dy : ℕ) : Fin 3 :=
  let c := firstNZ [hseg 0 1 7 true dx dy, turnBox 2 7 1 0 0 1 dx dy,
    vseg 9 11 2 true dx dy, turnBox 2 12 0 1 1 0 dx dy,
    hseg 4 6 12 true dx dy, turnBox 7 12 1 0 0 1 dx dy, vseg 14 15 7 true dx dy]
  if rev then flipColor c else c

private def qSE (rev : Bool) (dx dy : ℕ) : Fin 3 :=
  let c := firstNZ [vseg 0 1 7 true dx dy, turnBox 7 2 0 1 1 0 dx dy,
    hseg 9 11 2 true dx dy, turnBox 12 2 1 0 0 1 dx dy,
    vseg 4 6 12 true dx dy, turnBox 12 7 0 1 1 0 dx dy, hseg 14 15 7 true dx dy]
  if rev then flipColor c else c

private def qWS (rev : Bool) (dx dy : ℕ) : Fin 3 :=
  let c := firstNZ [hseg 0 1 7 true dx dy, turnBox 2 7 1 0 0 (-1) dx dy,
    vseg 4 6 2 false dx dy, turnBox 2 2 0 (-1) 1 0 dx dy,
    hseg 4 6 2 true dx dy, turnBox 7 2 1 0 0 (-1) dx dy, vseg 0 1 7 false dx dy]
  if rev then flipColor c else c

private def qNE (rev : Bool) (dx dy : ℕ) : Fin 3 :=
  let c := firstNZ [vseg 14 15 7 false dx dy, turnBox 7 12 0 (-1) 1 0 dx dy,
    hseg 9 11 12 true dx dy, turnBox 12 12 1 0 0 (-1) dx dy,
    vseg 9 11 12 false dx dy, turnBox 12 7 0 (-1) 1 0 dx dy, hseg 14 15 7 true dx dy]
  if rev then flipColor c else c

private def wnBase (dx dy : ℕ) : Fin 3 :=
  firstNZ [hseg 0 6 7 true dx dy, turnBox 7 7 1 0 0 1 dx dy, vseg 9 15 7 true dx dy]

private def esBase (dx dy : ℕ) : Fin 3 :=
  firstNZ [hseg 9 15 7 false dx dy, turnBox 7 7 (-1) 0 0 (-1) dx dy, vseg 0 6 7 false dx dy]

private def tileColor : TileKind → ℕ → ℕ → Fin 3
  | .empty, _, _ => 0
  | .lr, dx, dy => hseg 0 15 7 true dx dy
  | .rl, dx, dy => hseg 0 15 7 false dx dy
  | .bt, dx, dy => vseg 0 15 7 true dx dy
  | .tb, dx, dy => vseg 0 15 7 false dx dy
  | .wn, dx, dy => wnBase dx dy
  | .nw, dx, dy => flipColor (wnBase dx dy)
  | .es, dx, dy => esBase dx dy
  | .se, dx, dy => flipColor (esBase dx dy)
  | .sw, dx, dy =>
      firstNZ [vseg 0 6 7 true dx dy, turnBox 7 7 0 1 (-1) 0 dx dy, hseg 0 6 7 false dx dy]
  | .ne, dx, dy =>
      firstNZ [vseg 9 15 7 false dx dy, turnBox 7 7 0 (-1) 1 0 dx dy, hseg 9 15 7 true dx dy]
  | .crossLB, dx, dy => orCol (qWN false dx dy) (qSE false dx dy)
  | .crossRT, dx, dy => orCol (qWN true dx dy) (qSE true dx dy)
  | .crossLT, dx, dy => orCol (qWS false dx dy) (qNE false dx dy)
  | .crossRB, dx, dy => orCol (qWS true dx dy) (qNE true dx dy)
  | .capS, dx, dy => vseg 0 7 7 true dx dy
  | .capN, dx, dy => vseg 8 15 7 false dx dy
  | .capE, dx, dy => hseg 8 15 7 true dx dy
  | .capW, dx, dy => hseg 0 7 7 false dx dy

private theorem tileColor_border_check :
    TileKind.all.all (fun k =>
      (List.range 16).all fun i =>
        decide (tileColor k 0 i = portColor (tilePorts k).1 i) &&
        decide (tileColor k 15 i = portColor (tilePorts k).2.1 i) &&
        decide (tileColor k i 0 = portColorV (tilePorts k).2.2.1 i) &&
        decide (tileColor k i 15 = portColorV (tilePorts k).2.2.2 i)) = true := by
  decide

private theorem tileColor_no_spurious :
    TileKind.all.all (fun k =>
      k.isCap || (List.range 15).all fun x => (List.range 15).all fun y =>
        !decide (Trichromatic (fun p => tileColor k p.1 p.2) ⟨false, x, y⟩) &&
        !decide (Trichromatic (fun p => tileColor k p.1 p.2) ⟨true, x, y⟩)) = true := by
  decide

private theorem mem_tileKind_all (k : TileKind) : k ∈ TileKind.all := by
  cases k <;> simp [TileKind.all]

private instance : FinEnum TileKind :=
  FinEnum.ofList TileKind.all mem_tileKind_all

private theorem tileColor_west {k : TileKind} {i : ℕ} (hi : i < 16) :
    tileColor k 0 i = portColor (tilePorts k).1 i := by
  have h := List.all_eq_true.mp tileColor_border_check k (mem_tileKind_all k)
  have h' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'.1.1.1

private theorem tileColor_east {k : TileKind} {i : ℕ} (hi : i < 16) :
    tileColor k 15 i = portColor (tilePorts k).2.1 i := by
  have h := List.all_eq_true.mp tileColor_border_check k (mem_tileKind_all k)
  have h' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'.1.1.2

private theorem tileColor_south {k : TileKind} {i : ℕ} (hi : i < 16) :
    tileColor k i 0 = portColorV (tilePorts k).2.2.1 i := by
  have h := List.all_eq_true.mp tileColor_border_check k (mem_tileKind_all k)
  have h' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'.1.2

private theorem tileColor_north {k : TileKind} {i : ℕ} (hi : i < 16) :
    tileColor k i 15 = portColorV (tilePorts k).2.2.2 i := by
  have h := List.all_eq_true.mp tileColor_border_check k (mem_tileKind_all k)
  have h' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'.2

private theorem isCap_of_trichromatic_tileColor {k : TileKind} {t : GridTriangle}
    (hx : t.x < 15) (hy : t.y < 15)
    (ht : Trichromatic (fun p => tileColor k p.1 p.2) t) : k.isCap = true := by
  have h := List.all_eq_true.mp tileColor_no_spurious k (mem_tileKind_all k)
  rcases Bool.or_eq_true_iff.mp h with hcap | hno
  · exact hcap
  · have h1 := List.all_eq_true.mp hno t.x (List.mem_range.mpr hx)
    have h2 := List.all_eq_true.mp h1 t.y (List.mem_range.mpr hy)
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2
    cases hl : t.lower with
    | false =>
      have hfalse : ¬Trichromatic (fun p => tileColor k p.1 p.2) ⟨false, t.x, t.y⟩ := h2.1
      exact absurd (by rcases t; simp only at hl; subst hl; exact ht) hfalse
    | true =>
      have htrue : ¬Trichromatic (fun p => tileColor k p.1 p.2) ⟨true, t.x, t.y⟩ := h2.2
      exact absurd (by rcases t; simp only at hl; subst hl; exact ht) htrue

/-! ### Grid embedding of bounded directed end-of-line graphs -/

private def activeOut (N : ℕ) (P S : ℕ → ℕ) (u : ℕ) : Bool :=
  decide (S u < N ∧ S u ≠ u ∧ S u ≠ 0 ∧ P (S u) = u)

private def activeIn (N : ℕ) (P S : ℕ → ℕ) (u : ℕ) : Bool :=
  decide (P u < N ∧ P u ≠ u ∧ u ≠ 0 ∧ S (P u) = u)

private theorem activeIn_of_activeOut {N : ℕ} {P S : ℕ → ℕ} {Y : ℕ} (hY : Y < N)
    (ho : activeOut N P S Y = true) : activeIn N P S (S Y) = true ∧ P (S Y) = Y := by
  simp only [activeOut, decide_eq_true_eq] at ho
  obtain ⟨_, hne, hnz, hp⟩ := ho
  simp only [activeIn, decide_eq_true_eq]
  exact ⟨⟨by rw [hp]; exact hY, by rw [hp]; exact hne.symm, hnz, by rw [hp]⟩, hp⟩

private theorem activeOut_of_activeIn {N : ℕ} {P S : ℕ → ℕ} {X : ℕ} (hX : X < N)
    (hi : activeIn N P S X = true) : activeOut N P S (P X) = true ∧ S (P X) = X := by
  simp only [activeIn, decide_eq_true_eq] at hi
  obtain ⟨_, hne, hnz, hs⟩ := hi
  simp only [activeOut, decide_eq_true_eq]
  exact ⟨⟨by rw [hs]; exact hX, by rw [hs]; exact hne.symm, by rw [hs]; exact hnz, by rw [hs]⟩, hs⟩

private def tileKindDiag (ho0 ho hi ltXv ltXu : Bool) (isZero : Bool) : TileKind :=
  let inDir : Option Bool :=
    if isZero && ho0 then some false else if hi then some ltXu else none
  let outDir : Option Bool := if ho then some ltXv else none
  match inDir, outDir with
  | none, none => .empty
  | some false, some true => .se
  | some false, some false => .sw
  | some true, some true => .ne
  | some true, some false => .nw
  | some false, none => .capS
  | some true, none => .capN
  | none, some true => .capE
  | none, some false => .capW

private def tileKindOff (ho hi eqv ltYX ltXv ltvX ltXu ltYu : Bool) : TileKind :=
  if ho && eqv then
    if ltYX then .wn else .es
  else
    let hp : Option Bool :=
      if ho then (if ltYX && ltXv then some true else if ltvX && !ltYX then some false else none)
      else none
    let vp : Option Bool :=
      if hi then (if ltXu && ltYX then some true else if !ltYX && ltYu then some false else none)
      else none
    match hp, vp with
    | none, none => .empty
    | some true, none => .lr
    | some false, none => .rl
    | none, some true => .bt
    | none, some false => .tb
    | some true, some true => .crossLB
    | some false, some false => .crossRT
    | some true, some false => .crossLT
    | some false, some true => .crossRB

private def tileKind (N : ℕ) (P S : ℕ → ℕ) (X Y : ℕ) : TileKind :=
  let ho := activeOut N P S Y
  let hi := activeIn N P S X
  if X = Y then
    tileKindDiag (activeOut N P S 0) ho hi (decide (X < S Y)) (decide (X < P X)) (decide (X = 0))
  else
    tileKindOff ho hi (decide (S Y = X)) (decide (Y < X)) (decide (X < S Y)) (decide (S Y < X))
      (decide (P X < Y)) (decide (Y < P X))

private def westPort (N : ℕ) (P S : ℕ → ℕ) (X Y : ℕ) : Port :=
  if activeOut N P S Y then
    if Y < X ∧ X ≤ S Y then .pos else if S Y < X ∧ X ≤ Y then .neg else .none
  else .none

private def eastPort (N : ℕ) (P S : ℕ → ℕ) (X Y : ℕ) : Port :=
  if activeOut N P S Y then
    if Y ≤ X ∧ X < S Y then .pos else if S Y ≤ X ∧ X < Y then .neg else .none
  else .none

private def southPort (N : ℕ) (P S : ℕ → ℕ) (X Y : ℕ) : Port :=
  if X = 0 ∧ Y = 0 ∧ activeOut N P S 0 then .pos
  else if activeIn N P S X then
    if P X < Y ∧ Y ≤ X then .pos else if X < Y ∧ Y ≤ P X then .neg else .none
  else .none

private def northPort (N : ℕ) (P S : ℕ → ℕ) (X Y : ℕ) : Port :=
  if activeIn N P S X then
    if P X ≤ Y ∧ Y < X then .pos else if X ≤ Y ∧ Y < P X then .neg else .none
  else .none

private def portsOff (ho hi eqv ltYX ltXv ltvX ltPY ltYP : Bool) :
    Port × Port × Port × Port :=
  let w := if ho then (if ltYX && !ltvX then .pos else if ltvX && !ltYX then .neg else .none)
    else .none
  let e := if ho then (if ltYX && ltXv then .pos else if (eqv || ltvX) && !ltYX then .neg
    else .none) else .none
  let s := if hi then (if ltPY && ltYX then .pos else if !ltYX && !ltPY then .neg else .none)
    else .none
  let n := if hi then (if !ltYP && ltYX then .pos else if !ltYX && ltYP then .neg else .none)
    else .none
  (w, e, s, n)

private def validOff (ho hi eqv _ltYX ltXv ltvX ltPY ltYP : Bool) : Bool :=
  (if eqv then !ltXv && !ltvX else ltXv != ltvX) &&
  (!(ltPY && ltYP)) &&
  (!(ho && eqv) || hi) &&
  (!hi || (if ho && eqv then !ltPY && !ltYP else ltPY != ltYP))

private theorem tilePorts_tileKindOff_check (ho hi eqv ltYX ltXv ltvX ltPY ltYP : Bool) :
    (!validOff ho hi eqv ltYX ltXv ltvX ltPY ltYP) ||
      decide (tilePorts (tileKindOff ho hi eqv ltYX ltXv ltvX ltPY ltYP) =
        portsOff ho hi eqv ltYX ltXv ltvX ltPY ltYP) = true := by
  revert ho hi eqv ltYX ltXv ltvX ltPY ltYP
  decide

private theorem tilePorts_tileKind {N : ℕ} {P S : ℕ → ℕ} {X Y : ℕ}
    (hX : X < N) (hY : Y < N) :
    tilePorts (tileKind N P S X Y) =
      (westPort N P S X Y, eastPort N P S X Y, southPort N P S X Y, northPort N P S X Y) := by
  unfold tileKind
  by_cases hxy : X = Y
  · subst hxy
    unfold westPort eastPort southPort northPort
    simp only [↓reduceIte, tileKindDiag]
    by_cases hz : X = 0
    · subst hz
      have hi0 : activeIn N P S 0 = false := by simp [activeIn]
      rw [hi0]
      rcases ho0 : activeOut N P S 0 with _ | _
      · simp [tilePorts]
      · have hne : S 0 ≠ 0 := by
          simp only [activeOut, decide_eq_true_eq] at ho0
          exact ho0.2.2.1
        have hpos : 0 < S 0 := Nat.pos_of_ne_zero hne
        simp [hpos, tilePorts]
    · rcases hi : activeIn N P S X with _ | _ <;> rcases ho : activeOut N P S X with _ | _
      · simp [hz, tilePorts]
      · have hne : S X ≠ X := by
          simp only [activeOut, decide_eq_true_eq] at ho
          exact ho.2.1
        rcases lt_or_gt_of_ne hne with h1 | h2
        · simp [hz, h1, Nat.not_lt.mpr h1.le, tilePorts]
        · simp [hz, h2, Nat.not_lt.mpr h2.le, tilePorts]
      · have hne : P X ≠ X := by
          simp only [activeIn, decide_eq_true_eq] at hi
          exact hi.2.1
        rcases lt_or_gt_of_ne hne with h1 | h2
        · simp [hz, h1, Nat.not_lt.mpr h1.le, tilePorts]
        · simp [hz, h2, Nat.not_lt.mpr h2.le, tilePorts]
      · have hne1 : S X ≠ X := by
          simp only [activeOut, decide_eq_true_eq] at ho
          exact ho.2.1
        have hne2 : P X ≠ X := by
          simp only [activeIn, decide_eq_true_eq] at hi
          exact hi.2.1
        rcases lt_or_gt_of_ne hne1 with hs1 | hs2
        · rcases lt_or_gt_of_ne hne2 with hp1 | hp2
          · simp [hz, hs1, hp1, Nat.not_lt.mpr hs1.le, Nat.not_lt.mpr hp1.le, tilePorts]
          · simp [hz, hs1, hp2, Nat.not_lt.mpr hs1.le, Nat.not_lt.mpr hp2.le, tilePorts]
        · rcases lt_or_gt_of_ne hne2 with hp1 | hp2
          · simp [hz, hs2, hp1, Nat.not_lt.mpr hs2.le, Nat.not_lt.mpr hp1.le, tilePorts]
          · simp [hz, hs2, hp2, Nat.not_lt.mpr hs2.le, Nat.not_lt.mpr hp2.le, tilePorts]
  · simp only [hxy, ↓reduceIte]
    have hval : validOff (activeOut N P S Y) (activeIn N P S X) (decide (S Y = X))
        (decide (Y < X)) (decide (X < S Y)) (decide (S Y < X))
        (decide (P X < Y)) (decide (Y < P X)) = true := by
      simp only [validOff, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rcases Nat.lt_trichotomy (S Y) X with hlt | heq | hgt
        · simp [hlt, Nat.ne_of_lt hlt, Nat.not_lt.mpr hlt.le]
        · simp [heq]
        · simp [hgt, Nat.ne_of_gt hgt, Nat.not_lt.mpr hgt.le]
      · rcases Nat.lt_trichotomy (P X) Y with hlt | heq | hgt
        · simp [hlt, Nat.not_lt.mpr hlt.le]
        · simp [heq]
        · simp [hgt, Nat.not_lt.mpr hgt.le]
      · by_cases hboth : activeOut N P S Y = true ∧ S Y = X
        · have ⟨hi', _⟩ := activeIn_of_activeOut hY hboth.1
          rw [hboth.2] at hi'
          simp [hi']
        · cases ho : activeOut N P S Y <;> by_cases hs : S Y = X <;> simp_all
      · rcases hi : activeIn N P S X with _ | _
        · simp
        · simp only [Bool.not_true, Bool.false_or]
          by_cases hboth : activeOut N P S Y = true ∧ S Y = X
          · have hpx : P X = Y := by
              have ⟨_, hp⟩ := activeIn_of_activeOut hY hboth.1
              rw [← hboth.2, hp]
            simp [hboth.1, hboth.2, hpx]
          · have hne : P X ≠ Y := by
              intro hpx
              have ⟨ho', hs'⟩ := activeOut_of_activeIn hX hi
              exact hboth ⟨hpx ▸ ho', hpx ▸ hs'⟩
            have hnot' : ¬(activeOut N P S Y = true ∧ decide (S Y = X) = true) := by
              simp only [decide_eq_true_eq]
              exact hboth
            simp only [hnot', ↓reduceIte]
            rcases Nat.lt_trichotomy (P X) Y with hlt | heq | hgt
            · simp [hlt, Nat.not_lt.mpr hlt.le]
            · exact absurd heq hne
            · simp [hgt, Nat.not_lt.mpr hgt.le]
    have hchk := tilePorts_tileKindOff_check (activeOut N P S Y) (activeIn N P S X)
      (decide (S Y = X)) (decide (Y < X)) (decide (X < S Y)) (decide (S Y < X))
      (decide (P X < Y)) (decide (Y < P X))
    simp only [hval, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hchk
    rw [hchk]
    simp only [portsOff, westPort, eastPort, southPort, northPort]
    have h0 : ¬ (X = 0 ∧ Y = 0 ∧ activeOut N P S 0 = true) := by
      rintro ⟨rfl, rfl, _⟩; exact hxy rfl
    simp only [h0, ↓reduceIte]
    cases activeOut N P S Y <;> cases activeIn N P S X
    · rfl
    · refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_)) <;>
        simp only [↓reduceIte] <;> split_ifs <;>
        first | rfl | (simp only [Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)
    · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl)) <;>
        simp only [↓reduceIte] <;> split_ifs <;>
        first | rfl | (simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)
    · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
        simp only [↓reduceIte] <;> split_ifs <;>
        first | rfl | (simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)

private theorem eastPort_eq_westPort (N : ℕ) (P S : ℕ → ℕ) (X Y : ℕ) :
    eastPort N P S X Y = westPort N P S (X + 1) Y := by
  unfold eastPort westPort
  cases activeOut N P S Y
  · rfl
  · simp only [↓reduceIte]
    split_ifs <;> first | rfl | omega

private theorem northPort_eq_southPort (N : ℕ) (P S : ℕ → ℕ) (X Y : ℕ) :
    northPort N P S X Y = southPort N P S X (Y + 1) := by
  unfold northPort southPort
  have h0 : ¬ (X = 0 ∧ Y + 1 = 0 ∧ activeOut N P S 0 = true) := by omega
  simp only [h0, ↓reduceIte]
  cases activeIn N P S X
  · rfl
  · simp only [↓reduceIte]
    split_ifs <;> first | rfl | omega

private theorem westPort_zero (N : ℕ) (P S : ℕ → ℕ) (Y : ℕ) :
    westPort N P S 0 Y = .none := by
  simp [westPort]

private theorem eastPort_top (N : ℕ) (P S : ℕ → ℕ) (Y : ℕ) (hY : Y < N) :
    eastPort N P S (N - 1) Y = .none := by
  unfold eastPort
  by_cases ho : activeOut N P S Y
  · have hlt : S Y < N := by
      simp only [activeOut, decide_eq_true_eq] at ho
      exact ho.1
    have h1 : ¬ (Y ≤ N - 1 ∧ N - 1 < S Y) := by omega
    have h2 : ¬ (S Y ≤ N - 1 ∧ N - 1 < Y) := by omega
    simp [ho, h1, h2]
  · simp [ho]

private theorem northPort_top (N : ℕ) (P S : ℕ → ℕ) (X : ℕ) (hX : X < N) :
    northPort N P S X (N - 1) = .none := by
  unfold northPort
  by_cases hi : activeIn N P S X
  · have hlt : P X < N := by
      simp only [activeIn, decide_eq_true_eq] at hi
      exact hi.1
    have h1 : ¬ (P X ≤ N - 1 ∧ N - 1 < X) := by omega
    have h2 : ¬ (X ≤ N - 1 ∧ N - 1 < P X) := by omega
    simp [hi, h1, h2]
  · simp [hi]

private theorem southPort_zero (N : ℕ) (P S : ℕ → ℕ) (X : ℕ) :
    southPort N P S X 0 = if X = 0 ∧ activeOut N P S 0 = true then .pos else .none := by
  unfold southPort
  by_cases h : X = 0 ∧ activeOut N P S 0 = true
  · simp [h]
  · simp [h]

/-! ### Margin and global coloring guarantees -/

private def marginColor (ho0 : Bool) (x y : ℕ) : Fin 3 :=
  if y = 0 then 2
  else if x = 0 then 1
  else if ho0 then
    if y = 1 ∧ x ≤ 23 then 1
    else if y = 1 ∧ x = 24 then 2
    else if 2 ≤ y ∧ y ≤ 16 ∧ x = 23 then 1
    else if 2 ≤ y ∧ y ≤ 16 ∧ x = 24 then 2
    else 0
  else 0

private theorem margin_no_trichromatic :
    ((List.range 26).all fun x => (List.range 16).all fun y =>
      !decide (Trichromatic (fun p => marginColor true p.1 p.2) ⟨false, x, y⟩) &&
      !decide (Trichromatic (fun p => marginColor true p.1 p.2) ⟨true, x, y⟩)) = true := by
  decide

private theorem trichromatic_marginColor_imp {ho0 : Bool} {t : GridTriangle}
    (hx : t.x < 26) (hy : t.y < 16)
    (ht : Trichromatic (fun p => marginColor ho0 p.1 p.2) t) : ho0 = false := by
  cases ho0
  · rfl
  · have h1 := List.all_eq_true.mp margin_no_trichromatic t.x (List.mem_range.mpr hx)
    have h2 := List.all_eq_true.mp h1 t.y (List.mem_range.mpr hy)
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2
    cases hl : t.lower with
    | false =>
      have hfalse : ¬Trichromatic (fun p => marginColor true p.1 p.2) ⟨false, t.x, t.y⟩ := h2.1
      exact absurd (by rcases t; simp only at hl; subst hl; exact ht) hfalse
    | true =>
      have htrue : ¬Trichromatic (fun p => marginColor true p.1 p.2) ⟨true, t.x, t.y⟩ := h2.2
      exact absurd (by rcases t; simp only at hl; subst hl; exact ht) htrue

private def marginTailColor (ho0 : Bool) (x y : ℕ) : Fin 3 :=
  if ho0 then
    if y = 1 ∧ x ≤ 23 then 1
    else if y = 1 ∧ x = 24 then 2
    else if 2 ≤ y ∧ y < 16 ∧ x = 23 then 1
    else if 2 ≤ y ∧ y < 16 ∧ x = 24 then 2
    else 0
  else 0

private def graphInteriorColor (N : ℕ) (P S : ℕ → ℕ) (x y : ℕ) : Fin 3 :=
  if 16 ≤ x ∧ x < 16 * (N + 1) ∧ 16 ≤ y ∧ y < 16 * (N + 1) then
    tileColor (tileKind N P S (x / 16 - 1) (y / 16 - 1)) (x % 16) (y % 16)
  else marginTailColor (activeOut N P S 0) x y

private def graphColor (N : ℕ) (P S : ℕ → ℕ) (M : ℕ) (p : ℕ × ℕ) : Fin 3 :=
  if p.1 = 0 ∨ p.2 = 0 ∨ p.1 = M ∨ p.2 = M then boundaryColor p
  else graphInteriorColor N P S p.1 p.2

private theorem graphColor_eq_tile {N : ℕ} {P S : ℕ → ℕ} {M x y : ℕ}
    (hM : 16 * (N + 1) ≤ M)
    (hx0 : 16 ≤ x) (hx1 : x < 16 * (N + 1)) (hy0 : 16 ≤ y) (hy1 : y < 16 * (N + 1)) :
    graphColor N P S M (x, y) =
      tileColor (tileKind N P S (x / 16 - 1) (y / 16 - 1)) (x % 16) (y % 16) := by
  have hxne0 : x ≠ 0 := by omega
  have hyne0 : y ≠ 0 := by omega
  have hxneM : x ≠ M := by omega
  have hyneM : y ≠ M := by omega
  simp [graphColor, graphInteriorColor, hxne0, hyne0, hxneM, hyneM, hx0, hx1, hy0, hy1]

private theorem graphColor_east_edge {N : ℕ} {P S : ℕ → ℕ} {M y : ℕ}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (hy0 : 16 ≤ y) (hy1 : y < 16 * (N + 1)) :
    graphColor N P S M (16 * (N + 1) - 1, y) = 0 := by
  have hx0 : 16 ≤ 16 * (N + 1) - 1 := by omega
  have hx1 : 16 * (N + 1) - 1 < 16 * (N + 1) := by omega
  rw [graphColor_eq_tile hM hx0 hx1 hy0 hy1]
  have hdiv : (16 * (N + 1) - 1) / 16 - 1 = N - 1 := by omega
  have hmod : (16 * (N + 1) - 1) % 16 = 15 := by omega
  have hY : y / 16 - 1 < N := by omega
  have hmY : y % 16 < 16 := Nat.mod_lt y (by decide)
  rw [hdiv, hmod, tileColor_east hmY, tilePorts_tileKind (by omega : N - 1 < N) hY]
  rw [eastPort_top N P S (y / 16 - 1) hY]
  rfl

private theorem graphColor_north_edge {N : ℕ} {P S : ℕ → ℕ} {M x : ℕ}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (hx0 : 16 ≤ x) (hx1 : x < 16 * (N + 1)) :
    graphColor N P S M (x, 16 * (N + 1) - 1) = 0 := by
  have hy0 : 16 ≤ 16 * (N + 1) - 1 := by omega
  have hy1 : 16 * (N + 1) - 1 < 16 * (N + 1) := by omega
  rw [graphColor_eq_tile hM hx0 hx1 hy0 hy1]
  have hdiv : (16 * (N + 1) - 1) / 16 - 1 = N - 1 := by omega
  have hmod : (16 * (N + 1) - 1) % 16 = 15 := by omega
  have hX : x / 16 - 1 < N := by omega
  have hmX : x % 16 < 16 := Nat.mod_lt x (by decide)
  rw [hdiv, hmod, tileColor_north hmX, tilePorts_tileKind hX (by omega : N - 1 < N)]
  rw [northPort_top N P S (x / 16 - 1) hX]
  rfl

private theorem graphColor_west_edge {N : ℕ} {P S : ℕ → ℕ} {M y : ℕ}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (hy0 : 16 ≤ y) (hy1 : y < 16 * (N + 1)) :
    graphColor N P S M (16, y) = 0 := by
  have hx0 : 16 ≤ 16 := le_rfl
  have hx1 : 16 < 16 * (N + 1) := by omega
  rw [graphColor_eq_tile hM hx0 hx1 hy0 hy1]
  have hdiv : 16 / 16 - 1 = 0 := rfl
  have hmod : 16 % 16 = 0 := rfl
  have hY : y / 16 - 1 < N := by omega
  have hmY : y % 16 < 16 := Nat.mod_lt y (by decide)
  rw [hdiv, hmod, tileColor_west hmY, tilePorts_tileKind hN hY, westPort_zero]
  rfl

private theorem graphColor_south_edge {N : ℕ} {P S : ℕ → ℕ} {M x : ℕ}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (hx0 : 16 ≤ x) (hx1 : x < 16 * (N + 1)) :
    graphColor N P S M (x, 16) =
      if activeOut N P S 0 then (if x = 23 then 1 else if x = 24 then 2 else 0) else 0 := by
  have hy0 : 16 ≤ 16 := le_rfl
  have hy1 : 16 < 16 * (N + 1) := by omega
  rw [graphColor_eq_tile hM hx0 hx1 hy0 hy1]
  have hdiv : 16 / 16 - 1 = 0 := rfl
  have hmod : 16 % 16 = 0 := rfl
  have hX : x / 16 - 1 < N := by omega
  have hmX : x % 16 < 16 := Nat.mod_lt x (by decide)
  rw [hdiv, hmod, tileColor_south hmX, tilePorts_tileKind hX hN, southPort_zero]
  by_cases hX0 : x / 16 - 1 = 0
  · have hlo : 16 ≤ x := hx0
    have hhi : x < 32 := by omega
    have hm7 : x % 16 = 7 ↔ x = 23 := by omega
    have hm8 : x % 16 = 8 ↔ x = 24 := by omega
    cases activeOut N P S 0 <;> simp [hX0, portColorV, hm7, hm8]
  · have hnot : x ≠ 23 ∧ x ≠ 24 := by omega
    cases activeOut N P S 0 <;> simp [hX0, portColorV, hnot.1, hnot.2]

private theorem graphColor_eq_marginColor {N : ℕ} {P S : ℕ → ℕ} {M x y : ℕ}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (hx : x ≤ 26) (hy : y ≤ 16) :
    graphColor N P S M (x, y) = marginColor (activeOut N P S 0) x y := by
  have hxltM : x < M := by omega
  have hyltM : y < M := by omega
  by_cases hy0 : y = 0
  · subst hy0
    simp [graphColor, marginColor, boundaryColor]
  · by_cases hx0 : x = 0
    · subst hx0
      simp [graphColor, marginColor, boundaryColor, hy0]
    · by_cases hy16 : y = 16
      · subst hy16
        by_cases hx16 : 16 ≤ x
        · have hx1 : x < 16 * (N + 1) := by omega
          rw [graphColor_south_edge hN hM hx16 hx1]
          have hn1 : (16 : ℕ) ≠ 1 := by decide
          have hx23 : ¬ (x = 23 ∧ x = 24) := by omega
          by_cases ho : activeOut N P S 0
          · by_cases h23 : x = 23 <;> by_cases h24 : x = 24 <;>
              simp [marginColor, hx0, ho, h23, h24]
          · simp [marginColor, hx0, ho]
        · have hx23 : x ≠ 23 := by omega
          have hx24 : x ≠ 24 := by omega
          simp [graphColor, graphInteriorColor, marginTailColor, marginColor, hx0, hxltM.ne,
            hyltM.ne, hx16, hx23, hx24]
      · have hy15 : y < 16 := by omega
        have hnot : ¬ (16 ≤ x ∧ x < 16 * (N + 1) ∧ 16 ≤ y ∧ y < 16 * (N + 1)) := by omega
        simp [graphColor, graphInteriorColor, marginTailColor, marginColor, hx0, hy0, hxltM.ne,
          hyltM.ne, hnot, hy15, hy15.le]

private theorem graphColor_outer_twoColors {N : ℕ} {P S : ℕ → ℕ} {M x y : ℕ}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (_hx : x ≤ M) (_hy : y ≤ M)
    (hhi : 16 * (N + 1) - 1 ≤ x ∨ 16 * (N + 1) - 1 ≤ y) :
    graphColor N P S M (x, y) = 0 ∨ (y = 0 ∧ graphColor N P S M (x, y) = 2) ∨
      (x = 0 ∧ y ≠ 0 ∧ graphColor N P S M (x, y) = 1) := by
  have hM0 : M ≠ 0 := by omega
  by_cases hy0 : y = 0
  · right; left; exact ⟨hy0, by simp [graphColor, hy0, boundaryColor]⟩
  · by_cases hx0 : x = 0
    · right; right; exact ⟨hx0, hy0, by simp [graphColor, hx0, hy0, boundaryColor]⟩
    · left
      by_cases hxM : x = M
      · simp [graphColor, hxM, hM0, hy0, boundaryColor]
      · by_cases hyM : y = M
        · simp [graphColor, hyM, hM0, hx0, boundaryColor]
        · by_cases hin : 16 ≤ x ∧ x < 16 * (N + 1) ∧ 16 ≤ y ∧ y < 16 * (N + 1)
          · rcases hhi with hxhi | hyhi
            · have hxedge : x = 16 * (N + 1) - 1 := by omega
              rw [hxedge]
              exact graphColor_east_edge hN hM hin.2.2.1 hin.2.2.2
            · have hyedge : y = 16 * (N + 1) - 1 := by omega
              rw [hyedge]
              exact graphColor_north_edge hN hM hin.1 hin.2.1
          · simp only [graphColor, graphInteriorColor, marginTailColor, hx0, hy0, hxM, hyM,
              or_self, ↓reduceIte, hin]
            rcases hhi with hxhi | hyhi
            · have hx25 : 25 ≤ x := by omega
              split_ifs <;> first | rfl | omega
            · have hy16 : 16 ≤ y := by omega
              split_ifs <;> first | rfl | omega

private theorem not_trichromatic_of_twoColors {c : ℕ × ℕ → Fin 3} {t : GridTriangle}
    (h1 : ∃ a : Fin 3, ∀ k : Fin 3, c (t.corner k) ≠ a) : ¬Trichromatic c t := by
  intro ht
  obtain ⟨a, ha⟩ := h1
  have : Fintype.card (Fin 3) ≤ Fintype.card { b : Fin 3 // b ≠ a } := by
    refine Fintype.card_le_of_injective (fun k => ⟨c (t.corner k), ha k⟩) ?_
    intro k₁ k₂ h
    exact ht (congrArg Subtype.val h)
  have hcard : Fintype.card { b : Fin 3 // b ≠ a } < Fintype.card (Fin 3) := by
    fin_cases a <;> decide
  omega

private theorem not_trichromatic_outside_box {N : ℕ} {P S : ℕ → ℕ} {M : ℕ} {t : GridTriangle}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (ht : InGrid M M t)
    (hhi : 16 * (N + 1) - 1 ≤ t.x ∨ 16 * (N + 1) - 1 ≤ t.y) :
    ¬Trichromatic (graphColor N P S M) t := by
  obtain ⟨htx, hty⟩ := ht
  have hc : ∀ k : Fin 3,
      (t.corner k).1 ≤ M ∧ (t.corner k).2 ≤ M ∧
        (16 * (N + 1) - 1 ≤ (t.corner k).1 ∨ 16 * (N + 1) - 1 ≤ (t.corner k).2) := by
    intro k
    rcases t with ⟨_ | _, x, y⟩ <;> dsimp only at * <;>
      fin_cases k <;> simp only [corner] <;> exact ⟨by omega, by omega, by omega⟩
  by_cases h0y : ∃ k : Fin 3, (t.corner k).2 = 0
  · refine not_trichromatic_of_twoColors ⟨1, fun k => ?_⟩
    obtain ⟨hxk, hyk, hhik⟩ := hc k
    rcases graphColor_outer_twoColors hN hM hxk hyk hhik with h | ⟨_, h⟩ | ⟨hx0, _, _⟩
    · rw [h]; decide
    · rw [h]; decide
    · obtain ⟨k₀, hk₀⟩ := h0y
      rcases t with ⟨_ | _, x, y⟩ <;> dsimp only at * <;>
        fin_cases k <;> fin_cases k₀ <;> simp_all only [corner] <;> omega
  · refine not_trichromatic_of_twoColors ⟨2, fun k => ?_⟩
    obtain ⟨hxk, hyk, hhik⟩ := hc k
    rcases graphColor_outer_twoColors hN hM hxk hyk hhik with h | ⟨hy0, _⟩ | ⟨_, _, h⟩
    · rw [h]; decide
    · exact absurd hy0 (fun h' => h0y ⟨k, h'⟩)
    · rw [h]; decide

private theorem not_trichromatic_low_strip {N : ℕ} {P S : ℕ → ℕ} {M : ℕ} {t : GridTriangle}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (ht : InGrid M M t)
    (hlow : t.x < 16 ∨ t.y < 16) :
    t.x < 26 ∧ t.y < 16 ∧ activeOut N P S 0 = false ∨
      ¬Trichromatic (graphColor N P S M) t := by
  obtain ⟨htx, hty⟩ := ht
  have hMne0 : M ≠ 0 := by omega
  by_cases hbox : t.x < 26 ∧ t.y < 16
  · by_cases htri : Trichromatic (graphColor N P S M) t
    · refine .inl ⟨hbox.1, hbox.2, trichromatic_marginColor_imp hbox.1 hbox.2 ?_⟩
      intro k₁ k₂ heq
      have hcorner (k : Fin 3) : (t.corner k).1 ≤ 26 ∧ (t.corner k).2 ≤ 16 := by
        rcases t with ⟨_ | _, x, y⟩ <;> dsimp only at * <;>
          fin_cases k <;> simp only [corner] <;> omega
      have hc₁ := hcorner k₁
      have hc₂ := hcorner k₂
      apply htri
      dsimp only [Function.comp_def] at heq ⊢
      rw [← Prod.eta (t.corner k₁), ← Prod.eta (t.corner k₂),
        graphColor_eq_marginColor hN hM hc₁.1 hc₁.2,
        graphColor_eq_marginColor hN hM hc₂.1 hc₂.2]
      exact heq
    · exact .inr htri
  · refine .inr ?_
    rcases hlow with hx16 | hy16
    · have hyge : 16 ≤ t.y := by omega
      refine not_trichromatic_of_twoColors ⟨2, fun k => ?_⟩
      have hc : (t.corner k).1 ≤ 16 ∧ 16 ≤ (t.corner k).2 ∧ (t.corner k).2 ≤ M := by
        rcases t with ⟨_ | _, x, y⟩ <;> dsimp only at * <;>
          fin_cases k <;> simp only [corner] <;> exact ⟨by omega, by omega, by omega⟩
      rcases hc with ⟨hxk, hy0, hyM⟩
      have hxneM : (t.corner k).1 ≠ M := by omega
      have hyne0 : (t.corner k).2 ≠ 0 := by omega
      by_cases hx0 : (t.corner k).1 = 0
      · simp [graphColor, hx0, hyne0, boundaryColor]
      · by_cases hyEqM : (t.corner k).2 = M
        · simp [graphColor, hyEqM, hMne0, hx0, boundaryColor]
        · by_cases hxEq16 : (t.corner k).1 = 16
          · by_cases hyhi : (t.corner k).2 < 16 * (N + 1)
            · rw [← Prod.eta (t.corner k), hxEq16, graphColor_west_edge hN hM hy0 hyhi]
              decide
            · simp only [graphColor, graphInteriorColor, marginTailColor, hx0, hyne0, hxneM,
                hyEqM, or_self, ↓reduceIte, hyhi, and_false]
              split_ifs <;> first | decide | omega
          · have hnot : ¬ (16 ≤ (t.corner k).1 ∧ (t.corner k).1 < 16 * (N + 1) ∧
                16 ≤ (t.corner k).2 ∧ (t.corner k).2 < 16 * (N + 1)) := by omega
            simp only [graphColor, graphInteriorColor, marginTailColor, hx0, hyne0, hxneM,
              hyEqM, or_self, ↓reduceIte, hnot]
            split_ifs <;> first | decide | omega
    · have hxge : 26 ≤ t.x := by omega
      refine not_trichromatic_of_twoColors ⟨1, fun k => ?_⟩
      have hc : 26 ≤ (t.corner k).1 ∧ (t.corner k).1 ≤ M ∧ (t.corner k).2 ≤ 16 := by
        rcases t with ⟨_ | _, x, y⟩ <;> dsimp only at * <;>
          fin_cases k <;> simp only [corner] <;> exact ⟨by omega, by omega, by omega⟩
      rcases hc with ⟨hx26, hxM, hy16k⟩
      have hxne0 : (t.corner k).1 ≠ 0 := by omega
      have hyneM : (t.corner k).2 ≠ M := by omega
      by_cases hy0 : (t.corner k).2 = 0
      · simp [graphColor, hy0, boundaryColor]
      · by_cases hxEqM : (t.corner k).1 = M
        · simp [graphColor, hxEqM, hMne0, hy0, boundaryColor]
        · by_cases hboth : (t.corner k).2 = 16 ∧ (t.corner k).1 < 16 * (N + 1)
          · have hxlo : 16 ≤ (t.corner k).1 := by omega
            have hx23 : (t.corner k).1 ≠ 23 := by omega
            have hx24 : (t.corner k).1 ≠ 24 := by omega
            rw [← Prod.eta (t.corner k), hboth.1, graphColor_south_edge hN hM hxlo hboth.2]
            cases activeOut N P S 0 <;> simp [hx23, hx24]
          · have hnot : ¬ (16 ≤ (t.corner k).1 ∧ (t.corner k).1 < 16 * (N + 1) ∧
                16 ≤ (t.corner k).2 ∧ (t.corner k).2 < 16 * (N + 1)) := by omega
            simp only [graphColor, graphInteriorColor, marginTailColor, hxne0, hy0, hxEqM,
              hyneM, or_self, ↓reduceIte, hnot]
            split_ifs <;> first | decide | omega

private theorem not_trichromatic_east_seam {N : ℕ} {P S : ℕ → ℕ} {M : ℕ} {t : GridTriangle}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M)
    (hx0 : 16 ≤ t.x) (hx1 : t.x < 16 * (N + 1) - 1)
    (hy0 : 16 ≤ t.y) (hy1 : t.y < 16 * (N + 1) - 1)
    (hmod : t.x % 16 = 15) :
    ¬Trichromatic (graphColor N P S M) t := by
  have heq (y' : ℕ) (hy'0 : 16 ≤ y') (hy'1 : y' < 16 * (N + 1)) :
      graphColor N P S M (t.x, y') = graphColor N P S M (t.x + 1, y') := by
    have hx'0 : 16 ≤ t.x + 1 := by omega
    have hx'1 : t.x + 1 < 16 * (N + 1) := by omega
    have hxlt : t.x < 16 * (N + 1) := by omega
    rw [graphColor_eq_tile hM hx0 hxlt hy'0 hy'1, graphColor_eq_tile hM hx'0 hx'1 hy'0 hy'1]
    have hX : t.x / 16 - 1 < N := by omega
    have hY : y' / 16 - 1 < N := by omega
    have hmY : y' % 16 < 16 := Nat.mod_lt y' (by decide)
    have hdiv : (t.x + 1) / 16 - 1 = t.x / 16 - 1 + 1 := by omega
    have hX1 : t.x / 16 - 1 + 1 < N := by omega
    have hmod1 : (t.x + 1) % 16 = 0 := by omega
    rw [hmod, tileColor_east hmY, tilePorts_tileKind hX hY,
      hdiv, hmod1, tileColor_west hmY, tilePorts_tileKind hX1 hY,
      eastPort_eq_westPort]
  intro htri
  cases hl : t.lower
  · have hstep := heq (t.y + 1) (by omega) (by omega)
    have hc : graphColor N P S M (t.corner 1) = graphColor N P S M (t.corner 2) := by
      rcases t with ⟨l, x, y⟩
      simp only at hl
      subst hl
      simpa only [corner] using hstep.symm
    exact absurd (htri hc) (by decide)
  · have hstep := heq t.y hy0 (by omega)
    have hc : graphColor N P S M (t.corner 0) = graphColor N P S M (t.corner 1) := by
      rcases t with ⟨l, x, y⟩
      simp only at hl
      subst hl
      simpa only [corner] using hstep
    exact absurd (htri hc) (by decide)

private theorem not_trichromatic_north_seam {N : ℕ} {P S : ℕ → ℕ} {M : ℕ} {t : GridTriangle}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M)
    (hx0 : 16 ≤ t.x) (hx1 : t.x < 16 * (N + 1) - 1)
    (hy0 : 16 ≤ t.y) (hy1 : t.y < 16 * (N + 1) - 1)
    (hmod : t.y % 16 = 15) :
    ¬Trichromatic (graphColor N P S M) t := by
  have heq (x' : ℕ) (hx'0 : 16 ≤ x') (hx'1 : x' < 16 * (N + 1)) :
      graphColor N P S M (x', t.y) = graphColor N P S M (x', t.y + 1) := by
    have hy'0 : 16 ≤ t.y + 1 := by omega
    have hy'1 : t.y + 1 < 16 * (N + 1) := by omega
    have hylt : t.y < 16 * (N + 1) := by omega
    rw [graphColor_eq_tile hM hx'0 hx'1 hy0 hylt, graphColor_eq_tile hM hx'0 hx'1 hy'0 hy'1]
    have hX : x' / 16 - 1 < N := by omega
    have hY : t.y / 16 - 1 < N := by omega
    have hmX : x' % 16 < 16 := Nat.mod_lt x' (by decide)
    have hdiv : (t.y + 1) / 16 - 1 = t.y / 16 - 1 + 1 := by omega
    have hY1 : t.y / 16 - 1 + 1 < N := by omega
    have hmod1 : (t.y + 1) % 16 = 0 := by omega
    rw [hmod, tileColor_north hmX, tilePorts_tileKind hX hY,
      hdiv, hmod1, tileColor_south hmX, tilePorts_tileKind hX hY1,
      northPort_eq_southPort]
  intro htri
  cases hl : t.lower
  · have hstep := heq t.x hx0 (by omega)
    have hc : graphColor N P S M (t.corner 0) = graphColor N P S M (t.corner 2) := by
      rcases t with ⟨l, x, y⟩
      simp only at hl
      subst hl
      simpa only [corner] using hstep
    exact absurd (htri hc) (by decide)
  · have hstep := heq (t.x + 1) (by omega) (by omega)
    have hc : graphColor N P S M (t.corner 1) = graphColor N P S M (t.corner 2) := by
      rcases t with ⟨l, x, y⟩
      simp only at hl
      subst hl
      simpa only [corner] using hstep
    exact absurd (htri hc) (by decide)

private theorem tileKindOff_isCap_false (a b c d e f g h : Bool) :
    (tileKindOff a b c d e f g h).isCap = false := by
  revert a b c d e f g h
  decide

private theorem tileKindDiag_zero_isCap_false (ho0 a b : Bool) :
    (tileKindDiag ho0 ho0 false a b true).isCap = false := by
  revert ho0 a b
  decide

private theorem tileKindDiag_diag_isCap_false (ho0 b0 a b : Bool) :
    (tileKindDiag ho0 b0 b0 a b false).isCap = false := by
  revert ho0 b0 a b
  decide

private theorem isCap_imp {N : ℕ} {P S : ℕ → ℕ} {X Y : ℕ}
    (hcap : (tileKind N P S X Y).isCap = true) :
    X = Y ∧ X ≠ 0 ∧ activeIn N P S X ≠ activeOut N P S X := by
  by_cases hxy : X = Y
  · refine ⟨hxy, ?_, ?_⟩
    · subst hxy
      intro hz
      subst hz
      have hi0 : activeIn N P S 0 = false := by simp [activeIn]
      simp only [tileKind, ↓reduceIte, hi0, decide_true] at hcap
      rw [tileKindDiag_zero_isCap_false] at hcap
      exact Bool.false_ne_true hcap
    · subst hxy
      intro heq
      have hne0 : X ≠ 0 := by
        intro hz
        subst hz
        have hi0 : activeIn N P S 0 = false := by simp [activeIn]
        simp only [tileKind, ↓reduceIte, hi0, decide_true] at hcap
        rw [tileKindDiag_zero_isCap_false] at hcap
        exact Bool.false_ne_true hcap
      simp only [tileKind, ↓reduceIte, decide_eq_false hne0] at hcap
      rw [← heq, tileKindDiag_diag_isCap_false] at hcap
      exact Bool.false_ne_true hcap
  · simp only [tileKind, hxy, ↓reduceIte] at hcap
    rw [tileKindOff_isCap_false] at hcap
    exact absurd hcap (by decide)

private theorem trichromatic_graphColor_imp {N : ℕ} {P S : ℕ → ℕ} {M : ℕ} {t : GridTriangle}
    (hN : 1 ≤ N) (hM : 16 * (N + 1) ≤ M) (ht : InGrid M M t)
    (htri : Trichromatic (graphColor N P S M) t) :
    (t.x < 26 ∧ t.y < 16 ∧ activeOut N P S 0 = false) ∨
      (16 ≤ t.x ∧ t.x < 16 * (N + 1) - 1 ∧ t.x % 16 < 15 ∧
        16 ≤ t.y ∧ t.y < 16 * (N + 1) - 1 ∧ t.y % 16 < 15 ∧
        let X := t.x / 16 - 1
        X < N ∧ X ≠ 0 ∧ activeIn N P S X ≠ activeOut N P S X) := by
  by_cases hhi : 16 * (N + 1) - 1 ≤ t.x ∨ 16 * (N + 1) - 1 ≤ t.y
  · exact absurd htri (not_trichromatic_outside_box hN hM ht hhi)
  · by_cases hlow : t.x < 16 ∨ t.y < 16
    · rcases not_trichromatic_low_strip hN hM ht hlow with h | h
      · exact .inl h
      · exact absurd htri h
    · have hx0 : 16 ≤ t.x := by omega
      have hx1 : t.x < 16 * (N + 1) - 1 := by omega
      have hy0 : 16 ≤ t.y := by omega
      have hy1 : t.y < 16 * (N + 1) - 1 := by omega
      by_cases hxm : t.x % 16 = 15
      · exact absurd htri (not_trichromatic_east_seam hN hM hx0 hx1 hy0 hy1 hxm)
      · by_cases hym : t.y % 16 = 15
        · exact absurd htri (not_trichromatic_north_seam hN hM hx0 hx1 hy0 hy1 hym)
        · have hxm15 : t.x % 16 < 15 := by omega
          have hym15 : t.y % 16 < 15 := by omega
          let X := t.x / 16 - 1
          let Y := t.y / 16 - 1
          let t' : GridTriangle := ⟨t.lower, t.x % 16, t.y % 16⟩
          have hdiv_succ (a : ℕ) (ha : a % 16 < 15) : (a + 1) / 16 - 1 = a / 16 - 1 := by omega
          have hmod_succ (a : ℕ) (ha : a % 16 < 15) : (a + 1) % 16 = a % 16 + 1 := by omega
          have hcorner (k : Fin 3) :
              graphColor N P S M (t.corner k) =
                tileColor (tileKind N P S X Y) (t'.corner k).1 (t'.corner k).2 := by
            have hxb : 16 ≤ (t.corner k).1 ∧ (t.corner k).1 < 16 * (N + 1) := by
              rcases t with ⟨_ | _, x, y⟩ <;> dsimp only at * <;>
                fin_cases k <;> simp only [corner] <;> omega
            have hyb : 16 ≤ (t.corner k).2 ∧ (t.corner k).2 < 16 * (N + 1) := by
              rcases t with ⟨_ | _, x, y⟩ <;> dsimp only at * <;>
                fin_cases k <;> simp only [corner] <;> omega
            have hdivx : (t.corner k).1 / 16 - 1 = X := by
              rcases t with ⟨_ | _, x, y⟩ <;> dsimp only [X] at hxm15 ⊢ <;>
                fin_cases k <;> simp only [corner, hdiv_succ x hxm15]
            have hdivy : (t.corner k).2 / 16 - 1 = Y := by
              rcases t with ⟨_ | _, x, y⟩ <;> dsimp only [Y] at hym15 ⊢ <;>
                fin_cases k <;> simp only [corner, hdiv_succ y hym15]
            have hmodx : (t.corner k).1 % 16 = (t'.corner k).1 := by
              rcases t with ⟨_ | _, x, y⟩ <;> dsimp only [t'] at hxm15 ⊢ <;>
                fin_cases k <;> simp only [corner, hmod_succ x hxm15]
            have hmody : (t.corner k).2 % 16 = (t'.corner k).2 := by
              rcases t with ⟨_ | _, x, y⟩ <;> dsimp only [t'] at hym15 ⊢ <;>
                fin_cases k <;> simp only [corner, hmod_succ y hym15]
            rw [graphColor_eq_tile hM hxb.1 hxb.2 hyb.1 hyb.2, hdivx, hdivy, hmodx, hmody]
          have htri' : Trichromatic (fun p => tileColor (tileKind N P S X Y) p.1 p.2) t' := by
            intro k₁ k₂ heq
            apply htri
            dsimp only [Function.comp_def] at heq ⊢
            rw [hcorner k₁, hcorner k₂]
            exact heq
          have hcap := isCap_of_trichromatic_tileColor hxm15 hym15 htri'
          obtain ⟨_, hXne, hneq⟩ := isCap_imp hcap
          have hXlt : X < N := by omega
          exact .inr ⟨hx0, hx1, hxm15, hy0, hy1, hym15, hXlt, hXne, hneq⟩

/-! ### Polynomial-time circuit reduction from `EndOfLine` to `Sperner2D` -/

private def evalNat (n : ℕ) (c : CircuitCode) (u : ℕ) : ℕ :=
  lsbValue (evalCircuitCode n c (lowBits n u))

private theorem evalNat_lt (n : ℕ) (c : CircuitCode) (u : ℕ) : evalNat n c u < 2 ^ n := by
  have hlen : (evalCircuitCode n c (lowBits n u)).length = n := length_evalCircuitCode _ _ _
  simpa only [evalNat, hlen] using lsbValue_lt (evalCircuitCode n c (lowBits n u))

private theorem lowBits_evalNat (n : ℕ) (c : CircuitCode) (u : ℕ) :
    lowBits n (evalNat n c u) = evalCircuitCode n c (lowBits n u) := by
  have h := lowBits_lsbValue (evalCircuitCode n c (lowBits n u))
  rwa [length_evalCircuitCode] at h

private theorem lowBits_zero_eq (n : ℕ) : lowBits n 0 = zeroVertex n := by
  simpa [zeroVertex] using lowBits_lsbValue (List.replicate n false)

private theorem activeNbr_eq_hasNbr (n : ℕ) (fCode gCode : CircuitCode) {X : ℕ}
    (hX : X < 2 ^ n) (isOut : Bool) :
    let F := evalNat n fCode
    let G := evalNat n gCode
    let cf := evalCircuitCode n fCode
    let cg := evalCircuitCode n gCode
    decide (F X < 2 ^ n ∧ F X ≠ X ∧ (if isOut then F X ≠ 0 else X ≠ 0) ∧ G (F X) = X) =
      decide (cg (cf (lowBits n X)) = lowBits n X ∧ cf (lowBits n X) ≠ lowBits n X ∧
        (if isOut then cf (lowBits n X) ≠ zeroVertex n else lowBits n X ≠ zeroVertex n)) := by
  intro F G cf cg
  have hFlt : F X < 2 ^ n := evalNat_lt n fCode X
  have h0lt : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [decide_eq_decide]
  have h1 : G (F X) = X ↔ cg (cf (lowBits n X)) = lowBits n X := by
    simp only [F, G, cf, cg, ← lowBits_evalNat n fCode X]
    constructor
    · intro heq
      rw [← lowBits_evalNat n gCode (evalNat n fCode X), heq]
    · intro heq
      rw [← lowBits_evalNat n gCode (evalNat n fCode X)] at heq
      exact lowBits_injective_of_lt (evalNat_lt _ _ _) hX heq
  have h2 : F X ≠ X ↔ cf (lowBits n X) ≠ lowBits n X := by
    simp only [F, cf, ← lowBits_evalNat n fCode X]
    exact ⟨fun hne heq => hne (lowBits_injective_of_lt hFlt hX heq),
      fun hne heq => hne (congrArg (lowBits n) heq)⟩
  have h3 : (if isOut then F X ≠ 0 else X ≠ 0) ↔
      (if isOut then cf (lowBits n X) ≠ zeroVertex n else lowBits n X ≠ zeroVertex n) := by
    cases isOut <;>
      simp only [← lowBits_zero_eq n, F, cf, ← lowBits_evalNat n fCode X]
    · exact ⟨fun hne heq => hne (lowBits_injective_of_lt hX h0lt heq),
        fun hne heq => hne (congrArg (lowBits n) heq)⟩
    · exact ⟨fun hne heq => hne (lowBits_injective_of_lt hFlt h0lt heq),
        fun hne heq => hne (congrArg (lowBits n) heq)⟩
  exact ⟨fun h => ⟨h1.mp h.2.2.2, h2.mp h.2.1, h3.mp h.2.2.1⟩,
    fun h => ⟨hFlt, h2.mpr h.2.1, h3.mpr h.2.2, h1.mpr h.1⟩⟩

private theorem activeOut_eq_hasOut (inst : ℕ × CircuitCode × CircuitCode) {X : ℕ}
    (hX : X < 2 ^ inst.1) :
    let (n, pCode, sCode) := inst
    activeOut (2 ^ n) (evalNat n pCode) (evalNat n sCode) X =
      hasOut Prod.fst (fun p => evalCircuitCode p.1.1 p.1.2.1 p.2)
        (fun p => evalCircuitCode p.1.1 p.1.2.2 p.2) inst (lowBits n X) := by
  rcases inst with ⟨n, pCode, sCode⟩
  exact activeNbr_eq_hasNbr n sCode pCode hX true

private theorem activeIn_eq_hasIn (inst : ℕ × CircuitCode × CircuitCode) {X : ℕ}
    (hX : X < 2 ^ inst.1) :
    let (n, pCode, sCode) := inst
    activeIn (2 ^ n) (evalNat n pCode) (evalNat n sCode) X =
      hasIn Prod.fst (fun p => evalCircuitCode p.1.1 p.1.2.1 p.2)
        (fun p => evalCircuitCode p.1.1 p.1.2.2 p.2) inst (lowBits n X) := by
  rcases inst with ⟨n, pCode, sCode⟩
  exact activeNbr_eq_hasNbr n pCode sCode hX false

private def colorToBits (c : Fin 3) : List Bool :=
  match c with
  | 0 => [false, false, false]
  | 1 => [true, false, false]
  | 2 => [false, false, true]

private theorem length_colorToBits (c : Fin 3) : (colorToBits c).length = 3 := by
  fin_cases c <;> rfl

private theorem outputColor_colorToBits (c : Fin 3) :
    Sperner2D.outputColor (colorToBits c) = c := by
  fin_cases c <;> decide

private theorem computableInPolyTime_evalNat {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {code : α → CircuitCode} {u : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hcode : ComputableInPolyTime code enc encCode)
    (hu : ComputableInPolyTime u enc encNat) :
    ComputableInPolyTime (fun a => evalNat (n a) (code a) (u a)) enc encNat := by
  have hlow : ComputableInPolyTime (fun a => lowBits (n a) (u a)) enc encBits :=
    .of_tidy (ComputableTidilyInPolyTime.bitsLow hn.tidy hu.tidy)
  have hev : ComputableInPolyTime (fun a => evalCircuitCode (n a) (code a) (lowBits (n a) (u a)))
      enc encBits :=
    computableInPolyTime_evalCircuitCode hn hcode hlow
  have hnat : ComputableInPolyTime (fun a =>
      ofBits (evalCircuitCode (n a) (code a) (lowBits (n a) (u a)))) enc encNat :=
    .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp hev.tidy)
  refine hnat.of_enc_eq fun a => ?_
  simp only [evalNat, Cslib.BitString.lsbValue_eq_foldr_bit]
  rfl

private theorem computableInPolyTime_lsbValue {α : Type} {enc : α ↪ List Bool}
    {bits : α → List Bool} (hbits : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun a => lsbValue (bits a)) enc encNat := by
  have h : ComputableInPolyTime (fun a => ofBits (bits a)) enc encNat :=
    .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp hbits.tidy)
  refine h.of_enc_eq fun a => ?_
  rw [Cslib.BitString.lsbValue_eq_foldr_bit]
  rfl

private theorem computableInPolyTime_div16Sub1 {α : Type} {enc : α ↪ List Bool}
    {f : α → ℕ} (hf : ComputableInPolyTime f enc encNat) :
    ComputableInPolyTime (fun a => f a / 16 - 1) enc encNat := by
  have hshr : ComputableInPolyTime (fun a => (f a >>> 4) - 1) enc encNat :=
    binary_sub' (binary_shiftRight' hf (const 4)) (const 1)
  refine hshr.of_enc_eq fun a => ?_
  rw [Nat.shiftRight_eq_div_pow]

private theorem computableInPolyTime_mod16 {α : Type} {enc : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f enc encNat) :
    ComputableInPolyTime (fun a => (⟨f a % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16))
      enc (encFinEnum (Fin 16)) := by
  have hand : ComputableInPolyTime (fun a => f a &&& 15) enc encNat :=
    binary_and' hf (const 15)
  have hmod (x : ℕ) : x &&& 15 = x % 16 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod x 4
  have hmin : ComputableInPolyTime (fun a => min 15 (f a &&& 15)) enc encUnary :=
    binary_min_unary' (const 15) hand
  have hmin_eq (x : ℕ) : min 15 (x &&& 15) = x % 16 := by
    rw [hmod]
    have hlt : x % 16 < 16 := Nat.mod_lt x (by decide)
    omega
  have hunary : ComputableInPolyTime (fun a => f a % 16) enc encUnary := by
    simpa only [hmin_eq] using hmin
  have hfin := (unary_finMod (by decide : 0 < 16) (encFinEnum (Fin 16))).comp hunary
  refine hfin.of_enc_eq fun a => ?_
  have hlt : f a % 16 < 16 := Nat.mod_lt _ (by decide)
  simp [Nat.mod_eq_of_lt hlt]

private theorem computableInPolyTime_activeNbr {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {fCode gCode : α → CircuitCode} {u nz : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hf : ComputableInPolyTime fCode enc encCode)
    (hg : ComputableInPolyTime gCode enc encCode)
    (hu : ComputableInPolyTime u enc encNat)
    (hnz : ComputableInPolyTime nz enc encNat) :
    ComputableInPolyTime
      (fun a =>
        let v := evalNat (n a) (fCode a) (u a)
        decide (v < 2 ^ n a ∧ v ≠ u a ∧ nz a ≠ 0 ∧ evalNat (n a) (gCode a) v = u a))
      enc encBool := by
  have hN : ComputableInPolyTime (fun a => 2 ^ n a) enc encNat := binary_two_pow.comp hn
  have hv : ComputableInPolyTime (fun a => evalNat (n a) (fCode a) (u a)) enc encNat :=
    computableInPolyTime_evalNat hn hf hu
  have hgv : ComputableInPolyTime
      (fun a => evalNat (n a) (gCode a) (evalNat (n a) (fCode a) (u a))) enc encNat :=
    computableInPolyTime_evalNat hn hg hv
  have hc1 := binary_lt' hv hN
  have hc2 := hv.decide_ne hu
  have hc3 := hnz.decide_ne (const 0)
  have hc4 := hgv.decide_eq' hu
  exact .of_tidy (hc1.tidy.decide_and (hc2.tidy.decide_and (hc3.tidy.decide_and hc4.tidy)))

private theorem computableInPolyTime_activeOut {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {pCode sCode : α → CircuitCode} {u : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime pCode enc encCode)
    (hs : ComputableInPolyTime sCode enc encCode)
    (hu : ComputableInPolyTime u enc encNat) :
    ComputableInPolyTime
      (fun a => activeOut (2 ^ n a) (evalNat (n a) (pCode a)) (evalNat (n a) (sCode a)) (u a))
      enc encBool :=
  computableInPolyTime_activeNbr hn hs hp hu (computableInPolyTime_evalNat hn hs hu)

private theorem computableInPolyTime_activeIn {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {pCode sCode : α → CircuitCode} {u : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime pCode enc encCode)
    (hs : ComputableInPolyTime sCode enc encCode)
    (hu : ComputableInPolyTime u enc encNat) :
    ComputableInPolyTime
      (fun a => activeIn (2 ^ n a) (evalNat (n a) (pCode a)) (evalNat (n a) (sCode a)) (u a))
      enc encBool :=
  computableInPolyTime_activeNbr hn hp hs hu hu

private theorem computableInPolyTime_tileKindDiag {α : Type} {enc : α ↪ List Bool}
    {b1 b2 b3 b4 b5 b6 : α → Bool}
    (h1 : ComputableInPolyTime b1 enc encBool) (h2 : ComputableInPolyTime b2 enc encBool)
    (h3 : ComputableInPolyTime b3 enc encBool) (h4 : ComputableInPolyTime b4 enc encBool)
    (h5 : ComputableInPolyTime b5 enc encBool) (h6 : ComputableInPolyTime b6 enc encBool) :
    ComputableInPolyTime (fun a => tileKindDiag (b1 a) (b2 a) (b3 a) (b4 a) (b5 a) (b6 a))
      enc (encFinEnum TileKind) := by
  let encB6 := encPair encBool (encPair encBool (encPair encBool
    (encPair encBool (encPair encBool encBool))))
  have hvec := h1.prod (h2.prod (h3.prod (h4.prod (h5.prod h6))))
  have htab : ComputableInPolyTime (fun p : Bool × Bool × Bool × Bool × Bool × Bool =>
      tileKindDiag p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      encB6 (encFinEnum TileKind) := of_finite _
  exact htab.comp hvec

private theorem computableInPolyTime_tileKindOff {α : Type} {enc : α ↪ List Bool}
    {b1 b2 b3 b4 b5 b6 b7 b8 : α → Bool}
    (h1 : ComputableInPolyTime b1 enc encBool) (h2 : ComputableInPolyTime b2 enc encBool)
    (h3 : ComputableInPolyTime b3 enc encBool) (h4 : ComputableInPolyTime b4 enc encBool)
    (h5 : ComputableInPolyTime b5 enc encBool) (h6 : ComputableInPolyTime b6 enc encBool)
    (h7 : ComputableInPolyTime b7 enc encBool) (h8 : ComputableInPolyTime b8 enc encBool) :
    ComputableInPolyTime
      (fun a => tileKindOff (b1 a) (b2 a) (b3 a) (b4 a) (b5 a) (b6 a) (b7 a) (b8 a))
      enc (encFinEnum TileKind) := by
  let encB8 := encPair encBool (encPair encBool (encPair encBool (encPair encBool
    (encPair encBool (encPair encBool (encPair encBool encBool))))))
  have hvec := h1.prod (h2.prod (h3.prod (h4.prod (h5.prod (h6.prod (h7.prod h8))))))
  have htab : ComputableInPolyTime (fun p :
      Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool =>
      tileKindOff p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
        p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)
      encB8 (encFinEnum TileKind) := of_finite _
  exact htab.comp hvec

private def marginOutFun (b1 b2 b3 b4 b5 b6 b7 : Bool) : Fin 3 :=
  if b1 then
    if b2 && b3 then 1
    else if b2 && b4 then 2
    else if b5 && b6 && b7 then 1
    else if b5 && b6 && b4 then 2
    else 0
  else 0

private theorem marginTailColor_eq (ho0 : Bool) (x y : ℕ) :
    marginTailColor ho0 x y =
      marginOutFun ho0 (decide (y = 1)) (decide (x ≤ 23)) (decide (x = 24))
        (decide (2 ≤ y)) (decide (y < 16)) (decide (x = 23)) := by
  cases ho0 <;>
    simp [marginTailColor, marginOutFun, Bool.and_eq_true, and_assoc]

private theorem computableInPolyTime_marginOut {α : Type} {enc : α ↪ List Bool}
    {b1 b2 b3 b4 b5 b6 b7 : α → Bool}
    (h1 : ComputableInPolyTime b1 enc encBool) (h2 : ComputableInPolyTime b2 enc encBool)
    (h3 : ComputableInPolyTime b3 enc encBool) (h4 : ComputableInPolyTime b4 enc encBool)
    (h5 : ComputableInPolyTime b5 enc encBool) (h6 : ComputableInPolyTime b6 enc encBool)
    (h7 : ComputableInPolyTime b7 enc encBool) :
    ComputableInPolyTime (fun a => colorToBits
      (marginOutFun (b1 a) (b2 a) (b3 a) (b4 a) (b5 a) (b6 a) (b7 a))) enc encBits := by
  let encB7 := encPair encBool (encPair encBool (encPair encBool (encPair encBool
    (encPair encBool (encPair encBool encBool)))))
  have hvec := h1.prod (h2.prod (h3.prod (h4.prod (h5.prod (h6.prod h7)))))
  have htab : ComputableInPolyTime (fun p : Bool × Bool × Bool × Bool × Bool × Bool × Bool =>
      colorToBits (marginOutFun p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2)) encB7 encBits := of_finite _
  exact htab.comp hvec

private def eolInstN (p : (ℕ × CircuitCode × CircuitCode) × List Bool) : ℕ :=
  let (a, _) := p
  let (n, _) := a
  n

private def eolInstP (p : (ℕ × CircuitCode × CircuitCode) × List Bool) : CircuitCode :=
  let (a, _) := p
  let (_, c) := a
  let (pCode, _) := c
  pCode

private def eolInstS (p : (ℕ × CircuitCode × CircuitCode) × List Bool) : CircuitCode :=
  let (a, _) := p
  let (_, c) := a
  let (_, sCode) := c
  sCode

private def colorFun (p : (ℕ × CircuitCode × CircuitCode) × List Bool) : List Bool :=
  let (inst, uv) := p
  let (n, pCode, sCode) := inst
  let m := n + 5
  let x := lsbValue (uv.take m)
  let y := lsbValue ((uv.drop m).take m)
  colorToBits (graphInteriorColor (2 ^ n) (evalNat n pCode) (evalNat n sCode) x y)

private theorem computableInPolyTime_eolFields :
    ComputableInPolyTime eolInstN (encPair encEndOfLine encBits) encUnary ∧
    ComputableInPolyTime eolInstP (encPair encEndOfLine encBits) encCode ∧
    ComputableInPolyTime eolInstS (encPair encEndOfLine encBits) encCode := by
  have ha := fst encEndOfLine encBits
  have hn : ComputableInPolyTime eolInstN (encPair encEndOfLine encBits) encUnary :=
    (fst encUnary (encPair encCode encCode)).comp ha
  have hc := (snd encUnary (encPair encCode encCode)).comp ha
  have hp : ComputableInPolyTime eolInstP (encPair encEndOfLine encBits) encCode :=
    (fst encCode encCode).comp hc
  have hs : ComputableInPolyTime eolInstS (encPair encEndOfLine encBits) encCode :=
    (snd encCode encCode).comp hc
  exact ⟨hn, hp, hs⟩

private theorem computableInPolyTime_colorFun :
    ComputableInPolyTime colorFun (encPair encEndOfLine encBits) encBits := by
  let encIn := encPair encEndOfLine encBits
  obtain ⟨hn, hp, hs⟩ := computableInPolyTime_eolFields
  have huv : ComputableInPolyTime (fun p : (ℕ × CircuitCode × CircuitCode) × List Bool => p.2)
      encIn encBits := snd encEndOfLine encBits
  have hm : ComputableInPolyTime (fun p : (ℕ × CircuitCode × CircuitCode) × List Bool =>
      eolInstN p + 5) encIn encUnary := unary_add' hn (const 5)
  have hxBits : ComputableInPolyTime (fun p => p.2.take (eolInstN p + 5)) encIn encBits :=
    .of_tidy (ComputableTidilyInPolyTime.bitsTakeWithInput huv.tidy hm.tidy)
  have hyDrop : ComputableInPolyTime (fun p => p.2.drop (eolInstN p + 5)) encIn encBits :=
    .of_tidy (ComputableTidilyInPolyTime.bitsDropWithInput huv.tidy hm.tidy)
  have hyBits : ComputableInPolyTime (fun p => (p.2.drop (eolInstN p + 5)).take (eolInstN p + 5))
      encIn encBits :=
    .of_tidy (ComputableTidilyInPolyTime.bitsTakeWithInput hyDrop.tidy hm.tidy)
  have hx : ComputableInPolyTime
      (fun p => lsbValue (p.2.take (eolInstN p + 5))) encIn encNat :=
    computableInPolyTime_lsbValue hxBits
  have hy : ComputableInPolyTime
      (fun p => lsbValue ((p.2.drop (eolInstN p + 5)).take (eolInstN p + 5))) encIn encNat :=
    computableInPolyTime_lsbValue hyBits
  have hN : ComputableInPolyTime (fun p => 2 ^ eolInstN p) encIn encNat :=
    binary_two_pow.comp hn
  have hlim : ComputableInPolyTime (fun p => 16 * (2 ^ eolInstN p + 1)) encIn encNat :=
    binary_mul' (const 16) (binary_add' hN (const 1))
  have hinBox : ComputableInPolyTime (fun p =>
      decide (16 ≤ lsbValue (p.2.take (eolInstN p + 5)) ∧
        lsbValue (p.2.take (eolInstN p + 5)) < 16 * (2 ^ eolInstN p + 1) ∧
        16 ≤ lsbValue ((p.2.drop (eolInstN p + 5)).take (eolInstN p + 5)) ∧
        lsbValue ((p.2.drop (eolInstN p + 5)).take (eolInstN p + 5)) < 16 * (2 ^ eolInstN p + 1)))
      encIn encBool := by
    have c1 := binary_le' (const 16) hx
    have c2 := binary_lt' hx hlim
    have c3 := binary_le' (const 16) hy
    have c4 := binary_lt' hy hlim
    exact .of_tidy (c1.tidy.decide_and (c2.tidy.decide_and (c3.tidy.decide_and c4.tidy)))
  have hX : ComputableInPolyTime (fun p => lsbValue (p.2.take (eolInstN p + 5)) / 16 - 1)
      encIn encNat :=
    computableInPolyTime_div16Sub1 hx
  have hY : ComputableInPolyTime
      (fun p => lsbValue ((p.2.drop (eolInstN p + 5)).take (eolInstN p + 5)) / 16 - 1)
      encIn encNat :=
    computableInPolyTime_div16Sub1 hy
  have hho0 := computableInPolyTime_activeOut hn hp hs (const 0)
  have hho := computableInPolyTime_activeOut hn hp hs hY
  have hhi := computableInPolyTime_activeIn hn hp hs hX
  have hS : ComputableInPolyTime (fun p =>
      evalNat (eolInstN p) (eolInstS p)
        (lsbValue ((p.2.drop (eolInstN p + 5)).take (eolInstN p + 5)) / 16 - 1)) encIn encNat :=
    computableInPolyTime_evalNat hn hs hY
  have hP : ComputableInPolyTime (fun p =>
      evalNat (eolInstN p) (eolInstP p)
        (lsbValue (p.2.take (eolInstN p + 5)) / 16 - 1)) encIn encNat :=
    computableInPolyTime_evalNat hn hp hX
  have hkDiag := computableInPolyTime_tileKindDiag hho0 hho hhi (binary_lt' hX hS)
    (binary_lt' hX hP) (hX.decide_eq' (const 0))
  have hkOff := computableInPolyTime_tileKindOff hho hhi (hS.decide_eq' hX) (binary_lt' hY hX)
    (binary_lt' hX hS) (binary_lt' hS hX) (binary_lt' hP hY) (binary_lt' hY hP)
  have hk : ComputableInPolyTime (fun p =>
      tileKind (2 ^ eolInstN p) (evalNat (eolInstN p) (eolInstP p))
        (evalNat (eolInstN p) (eolInstS p))
        (lsbValue (p.2.take (eolInstN p + 5)) / 16 - 1)
        (lsbValue ((p.2.drop (eolInstN p + 5)).take (eolInstN p + 5)) / 16 - 1))
      encIn (encFinEnum TileKind) := by
    have hif := (hX.decide_eq' hY).ite hkDiag hkOff
    refine hif.of_enc_eq fun p => congrArg (encFinEnum TileKind) ?_
    simp [tileKind]
  have hdx := computableInPolyTime_mod16 hx
  have hdy := computableInPolyTime_mod16 hy
  have hboxColor : ComputableInPolyTime (fun p =>
      colorToBits (tileColor (tileKind (2 ^ eolInstN p) (evalNat (eolInstN p) (eolInstP p))
        (evalNat (eolInstN p) (eolInstS p))
        (lsbValue (p.2.take (eolInstN p + 5)) / 16 - 1)
        (lsbValue ((p.2.drop (eolInstN p + 5)).take (eolInstN p + 5)) / 16 - 1))
        (lsbValue (p.2.take (eolInstN p + 5)) % 16)
        (lsbValue ((p.2.drop (eolInstN p + 5)).take (eolInstN p + 5)) % 16))) encIn encBits := by
    let encT := encPair (encFinEnum TileKind) (encPair (encFinEnum (Fin 16)) (encFinEnum (Fin 16)))
    have htab : ComputableInPolyTime (fun q : TileKind × Fin 16 × Fin 16 =>
        colorToBits (tileColor q.1 q.2.1.val q.2.2.val)) encT encBits := of_finite _
    exact htab.comp (hk.prod (hdx.prod hdy))
  have houtColor := computableInPolyTime_marginOut hho0 (hy.decide_eq' (const 1))
    (binary_le' hx (const 23)) (hx.decide_eq' (const 24)) (binary_le' (const 2) hy)
    (binary_lt' hy (const 16)) (hx.decide_eq' (const 23))
  have hres := hinBox.ite hboxColor houtColor
  refine hres.of_enc_eq fun p => congrArg encBits ?_
  rcases p with ⟨⟨n, pCode, sCode⟩, uv⟩
  by_cases hbox : 16 ≤ lsbValue (uv.take (n + 5)) ∧
      lsbValue (uv.take (n + 5)) < 16 * (2 ^ n + 1) ∧
      16 ≤ lsbValue ((uv.drop (n + 5)).take (n + 5)) ∧
      lsbValue ((uv.drop (n + 5)).take (n + 5)) < 16 * (2 ^ n + 1)
  · simp only [colorFun, eolInstN, eolInstP, eolInstS, graphInteriorColor, hbox,
      and_self, decide_true, ↓reduceIte]
  · simp only [colorFun, eolInstN, eolInstP, eolInstS, graphInteriorColor, marginTailColor_eq,
      hbox, ↓reduceIte]
    rfl

private def decodeSol (p : (ℕ × CircuitCode × CircuitCode) × List Bool) : List Bool :=
  let (inst, w) := p
  let (n, _) := inst
  let m := n + 5
  let x := lsbValue (w.tail.take m)
  let y := lsbValue (w.tail.drop m)
  if x < 16 ∨ y < 16 then zeroVertex n else lowBits n (x / 16 - 1)

private theorem computableInPolyTime_decodeSol :
    ComputableInPolyTime decodeSol (encPair encEndOfLine encBits) encBits := by
  let encIn := encPair encEndOfLine encBits
  obtain ⟨hn, _, _⟩ := computableInPolyTime_eolFields
  have hw : ComputableInPolyTime (fun p : (ℕ × CircuitCode × CircuitCode) × List Bool => p.2)
      encIn encBits := snd encEndOfLine encBits
  have hm : ComputableInPolyTime (fun p : (ℕ × CircuitCode × CircuitCode) × List Bool =>
      eolInstN p + 5) encIn encUnary := unary_add' hn (const 5)
  have htail : ComputableInPolyTime (fun p : (ℕ × CircuitCode × CircuitCode) × List Bool =>
      p.2.tail) encIn encBits :=
    .of_tidy (ComputableTidilyInPolyTime.bitsTail.comp hw.tidy)
  have hxBits : ComputableInPolyTime (fun p => p.2.tail.take (eolInstN p + 5)) encIn encBits :=
    .of_tidy (ComputableTidilyInPolyTime.bitsTakeWithInput htail.tidy hm.tidy)
  have hyBits : ComputableInPolyTime (fun p => p.2.tail.drop (eolInstN p + 5)) encIn encBits :=
    .of_tidy (ComputableTidilyInPolyTime.bitsDropWithInput htail.tidy hm.tidy)
  have hx : ComputableInPolyTime
      (fun p => lsbValue (p.2.tail.take (eolInstN p + 5))) encIn encNat :=
    computableInPolyTime_lsbValue hxBits
  have hy : ComputableInPolyTime
      (fun p => lsbValue (p.2.tail.drop (eolInstN p + 5))) encIn encNat :=
    computableInPolyTime_lsbValue hyBits
  have hcond := (binary_lt' hx (const 16)).bool_or' (binary_lt' hy (const 16))
  have hzero : ComputableInPolyTime (fun p : (ℕ × CircuitCode × CircuitCode) × List Bool =>
      zeroVertex (eolInstN p)) encIn encBits :=
    .of_tidy ((ComputableTidilyInPolyTime.bitsReplicate false).comp hn.tidy)
  have hX : ComputableInPolyTime
      (fun p => lsbValue (p.2.tail.take (eolInstN p + 5)) / 16 - 1) encIn encNat :=
    computableInPolyTime_div16Sub1 hx
  have hnz : ComputableInPolyTime
      (fun p => lowBits (eolInstN p) (lsbValue (p.2.tail.take (eolInstN p + 5)) / 16 - 1))
      encIn encBits :=
    .of_tidy (ComputableTidilyInPolyTime.bitsLow hn.tidy hX.tidy)
  have hres := hcond.ite hzero hnz
  refine hres.of_enc_eq fun p => congrArg encBits ?_
  rcases p with ⟨⟨n, pCode, sCode⟩, w⟩
  simp only [decodeSol, eolInstN]
  by_cases h1 : lsbValue (w.tail.take (n + 5)) < 16
  · simp [h1]
  · simp [h1]

/-- `EndOfLine` reduces in polynomial time to `Sperner2D`. -/
theorem EndOfLine_searchReducible_Sperner2D :
    SearchReducible encEndOfLine encSperner2D EndOfLine Sperner2D := by
  have hnIn : ComputableInPolyTime (fun inst : ℕ × CircuitCode × CircuitCode => 2 * (inst.1 + 5))
      encEndOfLine encUnary := by
    have hn : ComputableInPolyTime Prod.fst encEndOfLine encUnary :=
      fst encUnary (encPair encCode encCode)
    exact unary_mul' (const 2) (unary_add' hn (const 5))
  have hmOut : ComputableInPolyTime (fun _ : ℕ × CircuitCode × CircuitCode => 3)
      encEndOfLine encUnary := const 3
  obtain ⟨colorCode, hcodePoly, hcodeSem⟩ :=
    exists_uniformCircuitCodes hnIn hmOut computableInPolyTime_colorFun
      fun _ _ _ => length_colorToBits _
  refine SearchReducible.of_isTotalSearch Sperner2D_mem_TFNP.2
    (f := fun inst => (inst.1 + 5, colorCode inst)) ?_ computableInPolyTime_decodeSol ?_
  · have hn : ComputableInPolyTime Prod.fst encEndOfLine encUnary :=
      fst encUnary (encPair encCode encCode)
    exact (unary_add' hn (const 5)).prod hcodePoly
  · intro inst w hw
    rcases inst with ⟨n, pCode, sCode⟩
    let P := evalNat n pCode
    let S := evalNat n sCode
    let N := 2 ^ n
    let M := 2 ^ (n + 5)
    obtain ⟨hwlen, htri⟩ := hw
    have hwlen' : w.length = 2 * (n + 5) + 1 := hwlen
    have htIn : InGrid M M (Sperner2D.decodeTriangle (n + 5) w) :=
      Sperner2D.inGrid_decodeTriangle hwlen'
    have hN : 1 ≤ N := Nat.one_le_two_pow
    have hM : 16 * (N + 1) ≤ M := by
      have hpow : M = 32 * N := by
        simp only [M, N, Nat.pow_add]
        rw [Nat.mul_comm]
      omega
    have hcolor_eq {cx cy : ℕ} (hx : cx ≤ M) (hy : cy ≤ M) :
        Sperner2D.color (n + 5, colorCode (n, pCode, sCode)) (cx, cy) =
          graphColor N P S M (cx, cy) := by
      simp only [Sperner2D.color, graphColor]
      split_ifs with hbd
      · rfl
      · have hxlt : cx < M := by dsimp only [M] at hx ⊢; omega
        have hylt : cy < M := by dsimp only [M] at hy ⊢; omega
        let uv := lowBits (n + 5) cx ++ lowBits (n + 5) cy
        have huv : uv.length = 2 * ((n, pCode, sCode).1 + 5) := by
          simp only [uv, List.length_append, length_lowBits]
          omega
        rw [hcodeSem (n, pCode, sCode) uv huv]
        have htake : (uv.drop (n + 5)).take (n + 5) = lowBits (n + 5) cy := by
          simp only [uv, List.drop_left' (length_lowBits (n + 5) cx),
            List.take_of_length_le (length_lowBits (n + 5) cy).le]
        simp only [colorFun, uv, List.take_left' (length_lowBits (n + 5) cx), htake,
          lsbValue_lowBits hxlt, lsbValue_lowBits hylt, outputColor_colorToBits]
        rfl
    have htriGraph : Trichromatic (graphColor N P S M) (Sperner2D.decodeTriangle (n + 5) w) := by
      intro k₁ k₂ heq
      have hbd (k : Fin 3) :
          ((Sperner2D.decodeTriangle (n + 5) w).corner k).1 ≤ M ∧
          ((Sperner2D.decodeTriangle (n + 5) w).corner k).2 ≤ M := by
        have htIn' := htIn
        rcases hdt : Sperner2D.decodeTriangle (n + 5) w with ⟨_ | _, x, y⟩ <;>
          (rw [hdt] at htIn'; dsimp only [InGrid] at htIn';
            fin_cases k <;> simp only [corner] <;> exact ⟨by omega, by omega⟩)
      apply htri
      dsimp only [Function.comp_apply] at heq ⊢
      rw [hcolor_eq (hbd k₁).1 (hbd k₁).2, hcolor_eq (hbd k₂).1 (hbd k₂).2]
      exact heq
    have hdrop : w.tail.drop (n + 5) = w.drop (n + 5 + 1) := by
      cases w with
      | nil => rfl
      | cons _ _ => rfl
    rcases trichromatic_graphColor_imp hN hM htIn htriGraph with
      ⟨_, hy16, ho0⟩ | ⟨hx16, _, _, hy16, _, _, hXlt, hXne, hneq⟩
    · have hcond : (Sperner2D.decodeTriangle (n + 5) w).x < 16 ∨
          (Sperner2D.decodeTriangle (n + 5) w).y < 16 := .inr hy16
      simp only [Sperner2D.decodeTriangle] at hcond
      rw [hdrop] at hcond
      have hdec : decodeSol ((n, pCode, sCode), w) = zeroVertex n := by
        simp only [decodeSol, hdrop]
        exact ite_eq_left_iff.mpr fun h => absurd hcond h
      rw [hdec]
      refine endOfLineRel_zeroVertex_of_hasOut_eq_false ?_
      have h0lt : 0 < N := Nat.two_pow_pos n
      rw [← lowBits_zero_eq n, ← activeOut_eq_hasOut (n, pCode, sCode) h0lt]
      exact ho0
    · have hxge : ¬ ((Sperner2D.decodeTriangle (n + 5) w).x < 16 ∨
          (Sperner2D.decodeTriangle (n + 5) w).y < 16) := by
        omega
      let X := (Sperner2D.decodeTriangle (n + 5) w).x / 16 - 1
      have hxge' := hxge
      simp only [Sperner2D.decodeTriangle] at hxge'
      rw [hdrop] at hxge'
      have hdec : decodeSol ((n, pCode, sCode), w) = lowBits n X := by
        simp only [decodeSol, hdrop, X, Sperner2D.decodeTriangle]
        exact ite_eq_right_iff.mpr fun h => absurd h hxge'
      rw [hdec]
      have hulen : (lowBits n X).length = n := length_lowBits n X
      have hune : lowBits n X ≠ zeroVertex n := by
        rw [← lowBits_zero_eq n]
        exact fun heq => hXne (lowBits_injective_of_lt hXlt (Nat.two_pow_pos n) heq)
      dsimp only [EndOfLine, endOfLineRel]
      have hin := (activeIn_eq_hasIn (n, pCode, sCode) hXlt).symm
      have hout := (activeOut_eq_hasOut (n, pCode, sCode) hXlt).symm
      refine ⟨hulen, ?_⟩
      dsimp only [X] at hune ⊢
      rw [hin, hout, beq_iff_eq, decide_eq_true hune, bne_iff_ne]
      exact hneq

/-- `Sperner2D` is `PPAD`-hard under polynomial-time search reductions. -/
theorem Sperner2D_searchHard : SearchHard @PPAD encSperner2D Sperner2D :=
  EndOfLine_searchComplete.2.trans EndOfLine_searchReducible_Sperner2D

/-- `Sperner2D` is `PPAD`-complete. -/
theorem Sperner2D_searchComplete : SearchComplete @PPAD encSperner2D Sperner2D :=
  ⟨Sperner2D_mem_PPAD, Sperner2D_searchHard⟩

end Cslib.Complexity
