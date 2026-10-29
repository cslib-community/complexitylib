/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.GeneralizedGeography
public import Complexity.Computability.Complexity.Classes.Alternation.TQBF
import Complexity.Computability.Complexity.Classes.Alternation.Savitch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Foundations.Data.List.Counting

/-!
# Generalized Geography is in `PSPACE`

Generalized Geography is a game of polynomially many moves, so it is in `PSPACE` by the
characterization of `PSPACE` through games of single-bit moves
(`Cslib.Complexity.IsGameVerifier.mem_PSPACE`). On a graph with `B` arcs, a move of Geography is a
block of `2 * B` single-bit moves, alternately chosen by the existential and the universal player.
The bits of the player to move in the block (`Cslib.Complexity.GeneralizedGeography.moverBits`:
the moves at even positions for the first player, at odd positions for the second) name the index
of the arc taken, as the position of their first `true` bit
(`Cslib.Complexity.GeneralizedGeography.choice`), and the other player's bits in the block do not
matter. A move naming an arc that does not leave the token for an unvisited declared vertex loses
(`Cslib.Complexity.GeneralizedGeography.legal`).

Each move visits a new declared vertex, so a play has at most `n` moves for `n` declared vertex
entries, and one more block decides the loser: the winning condition
(`Cslib.Complexity.GeneralizedGeography.verifier`) replays `n + 1` blocks
(`Cslib.Complexity.GeneralizedGeography.step`), and the existential player wins the game of
single-bit moves exactly when the first player wins Generalized Geography. The replay is a fold
whose state grows by at most one vertex per block, polynomial-time in the graph and the moves.

## Main definitions

* `Cslib.Complexity.GeneralizedGeography.moverBits`, `Cslib.Complexity.GeneralizedGeography.choice`:
  the bits of a move and the arc they name.
* `Cslib.Complexity.GeneralizedGeography.legal`: a legal move.
* `Cslib.Complexity.GeneralizedGeography.step`, `Cslib.Complexity.GeneralizedGeography.verifier`:
  the replay of a play.

## Main results

* `Cslib.Complexity.GeneralizedGeography.alternation_moverBits_true`,
  `Cslib.Complexity.GeneralizedGeography.alternation_moverBits_false`: the other player's bits in a
  block do not matter.
* `Cslib.Complexity.GeneralizedGeography.exists_legal_iff`,
  `Cslib.Complexity.GeneralizedGeography.forall_legal_iff`: the legal arcs are the moves of
  Generalized Geography.
* `Cslib.Complexity.GeneralizedGeography.alternation_foldl_step`: the game of single-bit moves is
  Generalized Geography.
* `Cslib.Complexity.GeneralizedGeography.isGameVerifier_verifier`: the replay is a game verifier of
  Generalized Geography.
* `Cslib.Complexity.GeneralizedGeography.length_encPlay_step_le`: a block adds at most one vertex
  to a play.
* `Cslib.Complexity.GeneralizedGeography.computableInPolyTime_verifier`: the replay is
  polynomial-time.
* `Cslib.Complexity.GeneralizedGeography_mem_PSPACE`: Generalized Geography is in `PSPACE`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.14][Sipser2013]
* [D. Lichtenstein, M. Sipser, *GO is polynomial-space hard*][LichtensteinSipser1980]
* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

@[expose] public section

namespace Cslib.Complexity

namespace GeneralizedGeography

open Turing.MultiTapeTM

/-! ### The bits of a move -/

/-- The bits of the player to move in the first block of `2 * B` single-bit moves: the moves at
even positions for the first player (`first = true`), at odd positions for the second. -/
def moverBits (B : ℕ) (first : Bool) (z : List Bool) : List Bool :=
  (List.range B).map fun j => z.getD (2 * j + if first then 0 else 1) false

@[simp]
theorem length_moverBits (B : ℕ) (first : Bool) (z : List Bool) :
    (moverBits B first z).length = B := by
  simp [moverBits]

private theorem moverBits_cons_cons (B : ℕ) (first b c : Bool) (z : List Bool) :
    moverBits (B + 1) first (b :: c :: z) = (if first then b else c) :: moverBits B first z := by
  simp only [moverBits, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · cases first <;> rfl
  · refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    rw [show 2 * (j + 1) + (if first then 0 else 1) = 2 * j + (if first then 0 else 1) + 1 + 1 by
      ring, List.getD_cons_succ, List.getD_cons_succ]

/-- Only the first block is read. -/
private theorem moverBits_take (B : ℕ) (first : Bool) (z : List Bool) :
    moverBits B first (z.take (2 * B)) = moverBits B first z := by
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt (by split <;> omega)]

private theorem replicate_two_mul_succ (B : ℕ) (ns : List ℕ) :
    List.replicate (2 * (B + 1)) 1 ++ ns = 1 :: 1 :: (List.replicate (2 * B) 1 ++ ns) := by
  rw [show 2 * (B + 1) = 2 * B + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
  rfl

private theorem exists_length_succ {B : ℕ} {P : List Bool → Prop} :
    (∃ b : Bool, ∃ x : List Bool, x.length = B ∧ P (b :: x)) ↔
      ∃ x : List Bool, x.length = B + 1 ∧ P x := by
  constructor
  · rintro ⟨b, x, hx, h⟩
    exact ⟨b :: x, by simp [hx], h⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨b, x, rfl⟩ := List.exists_cons_of_length_eq_add_one hx
    exact ⟨b, x, by simpa using hx, h⟩

private theorem forall_length_succ {B : ℕ} {P : List Bool → Prop} :
    (∀ b : Bool, ∀ x : List Bool, x.length = B → P (b :: x)) ↔
      ∀ x : List Bool, x.length = B + 1 → P x := by
  constructor
  · intro h x hx
    obtain ⟨b, x, rfl⟩ := List.exists_cons_of_length_eq_add_one hx
    exact h b x (by simpa using hx)
  · intro h b x hx
    exact h (b :: x) (by simp [hx])

/-- **A move of the first player**: in a block of `2 * B` single-bit moves, if only the bits at
even positions matter, the universal player's moves are vacuous and the existential player chooses
the `B` bits. -/
theorem alternation_moverBits_true {ns : List ℕ} :
    ∀ {B : ℕ} {F : List Bool → List Bool → Prop},
      Alternation true (List.replicate (2 * B) 1 ++ ns)
          (fun z => F (moverBits B true z) (z.drop (2 * B))) ↔
        ∃ x : List Bool, x.length = B ∧ Alternation true ns (F x)
  | 0, F => by simp [moverBits, List.length_eq_zero_iff]
  | B + 1, F => by
    have h (b c : Bool) : Alternation true (List.replicate (2 * B) 1 ++ ns)
        (fun v => F (moverBits (B + 1) true (b :: c :: v)) ((b :: c :: v).drop (2 * (B + 1)))) ↔
          ∃ x : List Bool, x.length = B ∧ Alternation true ns (F (b :: x)) := by
      rw [← alternation_moverBits_true (F := fun x r => F (b :: x) r)]
      refine alternation_congr fun v => ?_
      rw [moverBits_cons_cons, show 2 * (B + 1) = 2 * B + 1 + 1 by ring]
      rfl
    rw [replicate_two_mul_succ, alternation_true_one_cons]
    simp only [alternation_false_one_cons, h, forall_const]
    exact exists_length_succ (P := fun x => Alternation true ns (F x))

/-- **A move of the second player**: in a block of `2 * B` single-bit moves, if only the bits at
odd positions matter, the existential player's moves are vacuous and the universal player chooses
the `B` bits. -/
theorem alternation_moverBits_false {ns : List ℕ} :
    ∀ {B : ℕ} {F : List Bool → List Bool → Prop},
      Alternation true (List.replicate (2 * B) 1 ++ ns)
          (fun z => F (moverBits B false z) (z.drop (2 * B))) ↔
        ∀ y : List Bool, y.length = B → Alternation true ns (F y)
  | 0, F => by simp [moverBits, List.length_eq_zero_iff]
  | B + 1, F => by
    have h (b c : Bool) : Alternation true (List.replicate (2 * B) 1 ++ ns)
        (fun v => F (moverBits (B + 1) false (b :: c :: v)) ((b :: c :: v).drop (2 * (B + 1)))) ↔
          ∀ y : List Bool, y.length = B → Alternation true ns (F (c :: y)) := by
      rw [← alternation_moverBits_false (F := fun y r => F (c :: y) r)]
      refine alternation_congr fun v => ?_
      rw [moverBits_cons_cons, show 2 * (B + 1) = 2 * B + 1 + 1 by ring]
      rfl
    rw [replicate_two_mul_succ, alternation_true_one_cons]
    simp only [alternation_false_one_cons, h, exists_const]
    exact forall_length_succ (P := fun y => Alternation true ns (F y))

/-! ### Choosing an arc -/

/-- The index of the arc named by the bits of a move: the position of their first `true` bit. -/
def choice (bits : List Bool) : ℕ := bits.idxOf true

/-- The bits naming the arc of index `i` among `B`. -/
private def indicator (B i : ℕ) : List Bool :=
  List.replicate i false ++ true :: List.replicate (B - i - 1) false

private theorem length_indicator {B i : ℕ} (h : i < B) : (indicator B i).length = B := by
  simp only [indicator, List.length_append, List.length_replicate, List.length_cons]
  omega

private theorem choice_indicator (B i : ℕ) : choice (indicator B i) = i := by
  rw [choice, indicator, List.idxOf_append_of_notMem (by simp), List.idxOf_cons_self]
  simp

/-- The arc of index `i`, or `(0, 0)` past the last arc. -/
def arc (G : Graph) (i : ℕ) : ℕ × ℕ := G.2.getD i (0, 0)

/-- The arc of index `i` is a legal move with the token at `v` and the vertices `vis` visited: it
leaves `v` for an unvisited declared vertex. -/
def legal (G : Graph) (vis : List ℕ) (v i : ℕ) : Bool :=
  decide (i < G.2.length) && decide ((arc G i).1 = v) && decide ((arc G i).2 ∈ G.1) &&
    !decide ((arc G i).2 ∈ vis)

private theorem arc_eq {G : Graph} {i : ℕ} (hi : i < G.2.length) : arc G i = G.2[i] :=
  List.getD_eq_getElem _ _ hi

theorem legal_eq_true_iff {G : Graph} {vis : List ℕ} {v i : ℕ} :
    legal G vis v i = true ↔ ∃ h : i < G.2.length, G.2[i].1 = v ∧ G.2[i].2 ∈ G.1 ∧
      G.2[i].2 ∉ vis := by
  unfold legal
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨hi, h₁⟩, h₂⟩, h₃⟩
    rw [arc_eq hi] at h₁ h₂ h₃
    exact ⟨hi, h₁, h₂, h₃⟩
  · rintro ⟨hi, h₁, h₂, h₃⟩
    rw [arc_eq hi]
    exact ⟨⟨⟨hi, h₁⟩, h₂⟩, h₃⟩

/-- Legal arcs are the moves of Generalized Geography. -/
theorem exists_legal_iff {G : Graph} {vis : List ℕ} {v : ℕ} {R : ℕ → Prop} :
    (∃ x : List Bool, x.length = G.2.length ∧ legal G vis v (choice x) = true ∧
        R (arc G (choice x)).2) ↔
      ∃ w, (v, w) ∈ G.2 ∧ w ∈ G.1 ∧ w ∉ vis ∧ R w := by
  constructor
  · rintro ⟨x, -, hlegal, hR⟩
    obtain ⟨hi, h₁, h₂, h₃⟩ := legal_eq_true_iff.1 hlegal
    rw [arc_eq hi] at hR
    refine ⟨_, ?_, h₂, h₃, hR⟩
    rw [← h₁]
    exact List.getElem_mem hi
  · rintro ⟨w, hvw, hw, hwvis, hR⟩
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hvw
    refine ⟨indicator G.2.length i, length_indicator hi, ?_, ?_⟩
    · rw [choice_indicator]
      exact legal_eq_true_iff.2 ⟨hi, by rw [hiw], by rw [hiw]; exact hw, by rw [hiw]; exact hwvis⟩
    · rw [choice_indicator, arc_eq hi, hiw]
      exact hR

/-- The second player's legal arcs are the moves of Generalized Geography. -/
theorem forall_legal_iff {G : Graph} {vis : List ℕ} {v : ℕ} {R : ℕ → Prop} :
    (∀ y : List Bool, y.length = G.2.length → legal G vis v (choice y) = true →
        R (arc G (choice y)).2) ↔
      ∀ w, (v, w) ∈ G.2 → w ∈ G.1 → w ∉ vis → R w := by
  have h := exists_legal_iff (G := G) (vis := vis) (v := v) (R := fun w => ¬R w)
  constructor
  · intro hy w hvw hw hwvis
    by_contra hR
    obtain ⟨y, hy', hlegal, hR'⟩ := h.2 ⟨w, hvw, hw, hwvis, hR⟩
    exact hR' (hy y hy' hlegal)
  · intro hw y hy hlegal
    by_contra hR
    obtain ⟨w, hvw, hw', hwvis, hR'⟩ := h.1 ⟨y, hy, hlegal, hR⟩
    exact hR' (hw w hvw hw' hwvis)

/-! ### Replaying a play -/

/-- A play: its outcome once it is over (`some true` when the first player has won), whether the
first player is to move, the visited vertices and the vertex of the token. -/
abbrev Play : Type := Option Bool × Bool × List ℕ × ℕ

/-- The play after a move by the bits `bits` of the player to move: the token moves along the arc
they name if it is legal, and otherwise the player to move loses. -/
def next (G : Graph) (first : Bool) (vis : List ℕ) (v : ℕ) (bits : List Bool) : Play :=
  if legal G vis v (choice bits) then
    (none, !first, (arc G (choice bits)).2 :: vis, (arc G (choice bits)).2)
  else (some !first, first, vis, v)

/-- **One block of single-bit moves**: a play that is over stays over, and otherwise the player to
move moves by its bits in the block. -/
def step (G : Graph) (B : ℕ) (st : Play) (block : List Bool) : Play :=
  if st.1.isSome then st else next G st.2.1 st.2.2.1 st.2.2.2 (moverBits B st.2.1 block)

/-- The first `R` blocks of `2 * B` single-bit moves. -/
def blocks (B R : ℕ) (z : List Bool) : List (List Bool) :=
  (List.range R).map fun r => (z.drop (2 * B * r)).take (2 * B)

private theorem blocks_succ (B R : ℕ) (z : List Bool) :
    blocks B (R + 1) z = z.take (2 * B) :: blocks B R (z.drop (2 * B)) := by
  simp only [blocks, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    List.drop_zero]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, List.drop_drop, Nat.succ_eq_add_one]
  congr 2
  ring

/-- The blocks only read their moves. -/
private theorem blocks_take (B R : ℕ) (z : List Bool) :
    blocks B R (z.take (2 * B * R)) = blocks B R z := by
  refine List.map_congr_left fun r hr => ?_
  rw [List.mem_range] at hr
  rw [List.drop_take, List.take_take]
  congr 1
  have : 2 * B * r + 2 * B ≤ 2 * B * R := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hr
  omega

/-- A play that is over stays over. -/
private theorem foldl_step_some (G : Graph) (B : ℕ) (b : Bool) (rest : Bool × List ℕ × ℕ) :
    ∀ bs : List (List Bool), bs.foldl (step G B) (some b, rest) = (some b, rest)
  | [] => rfl
  | _ :: bs => by
    rw [List.foldl_cons, step, ite_eq_left (show (some b).isSome = true from rfl)]
    exact foldl_step_some G B b rest bs

/-- **The game of single-bit moves is Generalized Geography**: from a play in progress with fewer
than `r` unvisited declared vertices, the existential player wins the game of `r` blocks of
`2 * B` single-bit moves, `B` the number of arcs, exactly when the first player wins Generalized
Geography from the position (if the first player is to move) or loses it (if the second player is
to move). -/
theorem alternation_foldl_step (G : Graph) :
    ∀ (r : ℕ) (first : Bool) (vis : List ℕ) (v : ℕ),
      (G.1.toFinset \ vis.toFinset).card < r →
      (Alternation true (List.replicate (2 * G.2.length * r) 1) (fun z =>
          ((blocks G.2.length r z).foldl (step G G.2.length) (none, first, vis, v)).1.getD false =
            true) ↔
        (first = true ↔ G.GeographyWins vis v))
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | r + 1, first, vis, v, hr => by
    set B := G.2.length
    -- the outcome after the first block
    have hP (z : List Bool) :
        ((blocks B (r + 1) z).foldl (step G B) (none, first, vis, v)).1.getD false = true ↔
          ((blocks B r (z.drop (2 * B))).foldl (step G B)
            (next G first vis v (moverBits B first z))).1.getD false = true := by
      rw [blocks_succ, List.foldl_cons, step, ite_eq_right (by simp), moverBits_take]
    -- the outcome of the rest of the game after a legal or an illegal move
    have hlegal (bits : List Bool) (hl : legal G vis v (choice bits) = true) :
        Alternation true (List.replicate (2 * B * r) 1) (fun rest =>
            ((blocks B r rest).foldl (step G B) (next G first vis v bits)).1.getD false = true) ↔
          ((!first) = true ↔ G.GeographyWins ((arc G (choice bits)).2 :: vis)
            (arc G (choice bits)).2) := by
      obtain ⟨hi, h₁, h₂, h₃⟩ := legal_eq_true_iff.1 hl
      have hw : (arc G (choice bits)).2 ∈ G.1 := by rwa [arc_eq hi]
      have hwvis : (arc G (choice bits)).2 ∉ vis := by rwa [arc_eq hi]
      rw [next, ite_eq_left hl]
      exact alternation_foldl_step G r _ _ _ (by have := Graph.card_sdiff_cons_lt hw hwvis; omega)
    have hillegal (bits : List Bool) (hl : ¬legal G vis v (choice bits) = true) :
        Alternation true (List.replicate (2 * B * r) 1) (fun rest =>
            ((blocks B r rest).foldl (step G B) (next G first vis v bits)).1.getD false = true) ↔
          (!first) = true := by
      rw [next, ite_eq_right hl]
      simp only [foldl_step_some, Option.getD_some]
      exact alternation_const
    rw [show 2 * B * (r + 1) = 2 * B + 2 * B * r by ring, List.replicate_add,
      alternation_congr hP]
    cases first
    · rw [alternation_moverBits_false (F := fun bits rest => ((blocks B r rest).foldl (step G B)
        (next G false vis v bits)).1.getD false = true)]
      have hy (y : List Bool) : Alternation true (List.replicate (2 * B * r) 1) (fun rest =>
          ((blocks B r rest).foldl (step G B) (next G false vis v y)).1.getD false = true) ↔
            (legal G vis v (choice y) = true →
              G.GeographyWins ((arc G (choice y)).2 :: vis) (arc G (choice y)).2) := by
        by_cases hl : legal G vis v (choice y) = true
        · rw [hlegal y hl]
          simp [hl]
        · rw [hillegal y hl]
          simp [hl]
      simp only [hy]
      rw [forall_legal_iff (R := fun w => G.GeographyWins (w :: vis) w),
        ← Graph.not_geographyWins_iff]
      simp
    · rw [alternation_moverBits_true (F := fun bits rest => ((blocks B r rest).foldl (step G B)
        (next G true vis v bits)).1.getD false = true)]
      have hx (x : List Bool) : Alternation true (List.replicate (2 * B * r) 1) (fun rest =>
          ((blocks B r rest).foldl (step G B) (next G true vis v x)).1.getD false = true) ↔
            (legal G vis v (choice x) = true ∧
              ¬G.GeographyWins ((arc G (choice x)).2 :: vis) (arc G (choice x)).2) := by
        by_cases hl : legal G vis v (choice x) = true
        · rw [hlegal x hl]
          simp [hl]
        · rw [hillegal x hl]
          simp [hl]
      simp only [hx]
      rw [exists_legal_iff (R := fun w => ¬G.GeographyWins (w :: vis) w),
        ← Graph.geographyWins_iff]
      simp

/-! ### The game verifier -/

/-- **The winning condition of Generalized Geography as a game of single-bit moves**: on a graph
with `B` arcs and `n` declared vertex entries, replay `n + 1` blocks of `2 * B` single-bit moves
from the start vertex, the first player to move; the existential player wins when the first player
does. -/
def verifier (x : (Graph × ℕ) × List Bool) : Bool :=
  ((blocks x.1.1.2.length (x.1.1.1.length + 1) x.2).foldl (step x.1.1 x.1.1.2.length)
    (none, true, [x.1.2], x.1.2)).1.getD false

/-- The arcs and the declared vertex entries of a graph are no more than the length of the encoded
instance. -/
private theorem length_le_length_encode (x : Graph × ℕ) :
    x.1.2.length ≤ (encPair encGraph encNat x).length ∧
      x.1.1.length ≤ (encPair encGraph encNat x).length := by
  have h₁ := length_le_length_encList (encPair encNat encNat) x.1.2
  have h₂ := length_le_length_encList encNat x.1.1
  simp only [length_encPair, encGraph]
  omega

/-- **The replay is a game verifier of Generalized Geography**, with `2 * (n + 1) ^ 2` single-bit
moves on instances of encoded length `n`. -/
theorem isGameVerifier_verifier :
    IsGameVerifier (encPair encGraph encNat) ((Polynomial.X + 1) ^ 2) verifier
      GeneralizedGeography := by
  rintro ⟨G, s⟩
  set n := (encPair encGraph encNat (G, s)).length
  obtain ⟨hB, hV⟩ := length_le_length_encode (G, s)
  dsimp only at hB hV
  have hle : 2 * G.2.length * (G.1.length + 1) ≤
      2 * ((Polynomial.X + 1) ^ 2 : Polynomial ℕ).eval n := by
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left 2 ?_
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hcount : (G.1.toFinset \ [s].toFinset).card < G.1.length + 1 :=
    Nat.lt_succ_of_le ((Finset.card_le_card Finset.sdiff_subset).trans (List.toFinset_card_le _))
  rw [mem_GeneralizedGeography, ← Nat.add_sub_cancel' hle, List.replicate_add,
    alternation_append_iff fun z => by rw [sum_replicate_one, verifier, verifier, blocks_take]]
  exact ((alternation_foldl_step G _ true [s] s hcount).trans (by simp)).symm

/-! ### Polynomial time -/

section PolyTime

open ComputableInPolyTime

/-- Plays encoded as framed tuples: the outcome as an option, the player to move, the visited
vertices in binary, and the vertex of the token in binary. -/
abbrev encPlay : Play ↪ List Bool :=
  encPair (encOption encBool) (encPair encBool (encPair (encList encNat) encNat))

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- The bits of a move are polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_moverBits {B : γ → ℕ} {first : γ → Bool}
    {z : γ → List Bool} (hB : ComputableInPolyTime B encIn encUnary)
    (hfirst : ComputableInPolyTime first encIn encBool)
    (hz : ComputableInPolyTime z encIn encBits) :
    ComputableInPolyTime (fun x => moverBits (B x) (first x) (z x)) encIn
      (encList encBool) := by
  unfold moverBits
  fun_prop

/-- A move is polynomial-time. -/
private theorem computableInPolyTime_next :
    ComputableInPolyTime
      (fun p : (Graph × Play) × List Bool => next p.1.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2)
      (encPair (encPair encGraph encPlay) (encList encBool)) encPlay := by
  set encQ := encPair (encPair encGraph encPlay) (encList encBool)
  have hG : ComputableInPolyTime (fun p : (Graph × Play) × List Bool => p.1.1) encQ
      encGraph := by fun_prop
  have hV : ComputableInPolyTime (fun p : (Graph × Play) × List Bool => p.1.1.1) encQ
      (encList encNat) := (fst _ _).comp hG
  have hE : ComputableInPolyTime (fun p : (Graph × Play) × List Bool => p.1.1.2) encQ
      (encList (encPair encNat encNat)) := (snd _ _).comp hG
  have hfirst : ComputableInPolyTime (fun p : (Graph × Play) × List Bool => p.1.2.2.1)
      encQ encBool := by fun_prop
  have hvis : ComputableInPolyTime (fun p : (Graph × Play) × List Bool => p.1.2.2.2.1)
      encQ (encList encNat) := by fun_prop
  have hv : ComputableInPolyTime (fun p : (Graph × Play) × List Bool => p.1.2.2.2.2)
      encQ encNat := by fun_prop
  have hi : ComputableInPolyTime (fun p : (Graph × Play) × List Bool => choice p.2)
      encQ encUnary := idxOfWithInput (snd _ _) (const true)
  have hN : ComputableInPolyTime (fun p : (Graph × Play) × List Bool => p.1.1.2.length)
      encQ encUnary := (length_list _).comp hE
  have harc : ComputableInPolyTime
      (fun p : (Graph × Play) × List Bool => arc p.1.1 (choice p.2)) encQ
      (encPair encNat encNat) := (listGetD (0, 0)).comp (hE.prod hi)
  have hw : ComputableInPolyTime
      (fun p : (Graph × Play) × List Bool => (arc p.1.1 (choice p.2)).2) encQ encNat :=
    (snd _ _).comp harc
  have hmem {l : (Graph × Play) × List Bool → List ℕ}
      (hl : ComputableInPolyTime l encQ (encList encNat)) :
      ComputableInPolyTime
        (fun p => decide ((arc p.1.1 (choice p.2)).2 ∈ l p)) encQ encBool := by
    simp only [List.decide_mem_eq_any]
    exact anyWithInput hl (decide_eq' (snd _ _) (hw.comp (fst _ _)))
  have hlegal : ComputableInPolyTime
      (fun p : (Graph × Play) × List Bool => legal p.1.1 p.1.2.2.2.1 p.1.2.2.2.2 (choice p.2))
      encQ encBool := by
    unfold legal
    have hv' := decide_eq' ((fst _ _).comp harc) hv
    have hV' := hmem hV
    have hvis' := hmem hvis
    fun_prop
  unfold next
  exact ite' hlegal (((const none).prod ((bool_not.comp hfirst).prod
    ((cons' hw hvis).prod hw))))
    (((optionSome encBool).comp (bool_not.comp hfirst)).prod (hfirst.prod (hvis.prod hv)))

/-- A target of an arc is no longer in binary than the encoded graph. -/
private theorem length_encNat_le_of_mem {G : Graph} {e : ℕ × ℕ} (he : e ∈ G.2) :
    (encNat e.2).length ≤ (encGraph G).length := by
  have h₁ := sum_length_le_length_encList (encPair encNat encNat) G.2
  have h₂ := List.le_sum_of_mem (List.mem_map_of_mem (f := fun a =>
    (encPair encNat encNat a).length) he)
  have h₃ := length_le_encPair_right encNat encNat e
  simp only [encGraph, length_encPair] at h₁ h₂ h₃ ⊢
  omega

/-- **A block adds at most one vertex to a play.** -/
theorem length_encPlay_step_le (G : Graph) (B : ℕ) (st : Play) (block : List Bool) :
    (encPlay (step G B st block)).length ≤ (encPlay st).length + 5 * (encGraph G).length + 4 := by
  obtain ⟨o, first, vis, v⟩ := st
  unfold step
  split_ifs with ho
  · omega
  · have ho' : o = none := by cases o <;> simp_all
    subst ho'
    unfold next
    split_ifs with hl
    · obtain ⟨hi, -, -, -⟩ := legal_eq_true_iff.1 hl
      have hw := length_encNat_le_of_mem (G := G)
        (List.getElem_mem (l := G.2) (n := choice (moverBits B first block)) hi)
      rw [← arc_eq hi] at hw
      simp only [length_encPair, encOption_none, encList_cons, List.length_append, length_frame,
        encBool_apply, List.length_cons, List.length_nil, List.length_nil] at hw ⊢
      omega
    · simp only [length_encPair, encOption_none, encOption_some, List.length_cons,
        encBool_apply, List.length_nil]
      omega

/-- The inputs of the verifier: a graph with a start vertex, and the moves. -/
private abbrev encInput : (Graph × ℕ) × List Bool ↪ List Bool :=
  encPair (encPair encGraph encNat) encBits

/-- The inputs of a block of the replay: the input of the verifier, a play and a block. -/
private abbrev encStep : (((Graph × ℕ) × List Bool) × Play) × List Bool ↪ List Bool :=
  encPair (encPair encInput encPlay) encBits

/-- **The replay is polynomial-time**: a fold over the blocks whose state grows by at most one
vertex per block. -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair (encPair encGraph encNat) encBits) encBool := by
  have hG : ComputableInPolyTime (fun x : (Graph × ℕ) × List Bool => x.1.1) encInput
      encGraph := by fun_prop
  have hB : ComputableInPolyTime (fun x : (Graph × ℕ) × List Bool => x.1.1.2.length) encInput
      encUnary := (length_list _).comp ((snd _ _).comp hG)
  have hR : ComputableInPolyTime (fun x : (Graph × ℕ) × List Bool => x.1.1.1.length + 1)
      encInput encUnary :=
    unary_add.comp (((length_list _).comp ((fst _ _).comp hG)).prod (const 1))
  have hblocks : ComputableInPolyTime
      (fun x : (Graph × ℕ) × List Bool => blocks x.1.1.2.length (x.1.1.1.length + 1) x.2) encInput
      (encList encBits) := by
    have h2B : ComputableInPolyTime
        (fun p : ((Graph × ℕ) × List Bool) × ℕ => 2 * p.1.1.1.2.length)
        (encPair encInput encUnary) encUnary := unary_mul.comp ((const 2).prod (hB.comp (fst _ _)))
    unfold blocks
    exact mapWithInput (range.comp hR) (bitsTakeWithInput (bitsDropWithInput
      ((snd _ _).comp (fst _ _)) (unary_mul.comp (h2B.prod (snd _ _)))) h2B)
  have hinit : ComputableInPolyTime
      (fun x : (Graph × ℕ) × List Bool => ((none, true, [x.1.2], x.1.2) : Play)) encInput
      encPlay := by
    fun_prop
  have hstep : ComputableInPolyTime
      (fun p : ((((Graph × ℕ) × List Bool) × Play) × List Bool) =>
        step p.1.1.1.1 p.1.1.1.1.2.length p.1.2 p.2)
      encStep encPlay := by
    have hst : ComputableInPolyTime
        (fun p : ((((Graph × ℕ) × List Bool) × Play) × List Bool) => p.1.2)
        encStep encPlay := by fun_prop
    have hX : ComputableInPolyTime
        (fun p : ((((Graph × ℕ) × List Bool) × Play) × List Bool) => p.1.1)
        encStep encInput := by fun_prop
    have hbits : ComputableInPolyTime
        (fun p : ((((Graph × ℕ) × List Bool) × Play) × List Bool) =>
          moverBits p.1.1.1.1.2.length p.1.2.2.1 p.2)
        encStep (encList encBool) :=
      computableInPolyTime_moverBits (hB.comp hX) (by fun_prop) (snd _ _)
    have hpair : ComputableInPolyTime
        (fun p : ((((Graph × ℕ) × List Bool) × Play) × List Bool) =>
          ((p.1.1.1.1, p.1.2), moverBits p.1.1.1.1.2.length p.1.2.2.1 p.2))
        encStep
        (encPair (encPair encGraph encPlay) (encList encBool)) :=
      ((hG.comp hX).prod hst).prod hbits
    have hnext : ComputableInPolyTime
        (fun p : ((((Graph × ℕ) × List Bool) × Play) × List Bool) =>
          next p.1.1.1.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2
            (moverBits p.1.1.1.1.2.length p.1.2.2.1 p.2))
        encStep encPlay := by
      have h := computableInPolyTime_next.comp hpair
      simp only [Function.comp_def] at h
      exact h
    have hsome : ComputableInPolyTime
        (fun p : ((((Graph × ℕ) × List Bool) × Play) × List Bool) => p.1.2.1.isSome)
        encStep encBool := optionIsSome ((fst _ _).comp hst)
    unfold step
    exact ite' hsome hst hnext
  have hfold := foldlWithInput_of_bounded_growth (encA := encBits) (encL := encList encBits)
    (step := fun x : (Graph × ℕ) × List Bool => step x.1.1 x.1.1.2.length) hinit
    ⟨hblocks, hstep, inferInstance, inferInstance⟩
    (growth := fun x => 5 * (encInput x).length + 4)
    ⟨((PolyBounded.const 5).mul .self).add (.const 4),
      fun x st b _ => (length_encPlay_step_le _ _ st b).trans (by
        have := length_le_encPair_left (encPair encGraph encNat) encBits x
        have : (encInput x).length = (encPair (encPair encGraph encNat) encBits x).length := rfl
        have := length_le_encPair_left encGraph encNat x.1
        omega)⟩
  unfold verifier
  exact optionGetDWithInput ((fst _ _).comp hfold) (const false)

end PolyTime

end GeneralizedGeography

open GeneralizedGeography Turing.MultiTapeTM

/-- **Generalized Geography is in `PSPACE`** [Sipser, Theorem 8.14][Sipser2013]: it is a game of
polynomially many moves whose winning condition is polynomial-time. -/
theorem GeneralizedGeography_mem_PSPACE : GeneralizedGeography ∈ PSPACE (encPair encGraph encNat) :=
  isGameVerifier_verifier.mem_PSPACE computableInPolyTime_verifier

end Cslib.Complexity
