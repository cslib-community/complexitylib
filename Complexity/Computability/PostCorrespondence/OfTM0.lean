/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PostCorrespondence.Rewrite
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Set.Finite.List

/-!
# Turing machine halting as a modified correspondence problem

For a Mathlib `Turing.TM0` machine `M` with finitely many symbols and states and an input `l`,
`OfTM0.mInstance M l` is an MPCP instance that is solvable iff `M` halts on `l`
(`OfTM0.eval_dom_iff_solvable`). This is Sipser's construction [Sipser2013, proof of Theorem 5.15],
phrased through the semi-Thue simulation of `Complexity.Computability.PostCorrespondence.Rewrite`.

The configuration with state `q`, scanned symbol `a`, cells `L` to the left (nearest first) and
cells `R` to the right is the word `⊢ L⁻¹ ⟨q, a⟩ R ⊣`. The rules (`OfTM0.Rule`) rewrite a
configuration word to the next one: a write changes the scanned letter, a move exchanges it with a
neighbouring symbol, and a move onto an end marker first inserts the blank `default`. When `M`
stops, the scanned letter becomes a halt marker, which erases the remaining symbols and finally
the word `⊢ halt ⊣`. The start domino is `ε / ⊢ ⟨q₀, a₀⟩ R ⊣` for the initial configuration, and
the copy dominoes complete the instance. The end marker `⊣` separates successive configurations,
as `#` does in Sipser's construction.

Two differences from Sipser's construction: Mathlib's `TM0` has a two-way infinite tape and halts
when its transition function is undefined, with no accept state, so the instance encodes halting
rather than acceptance, and it has rules to extend the tape on both sides.

`OfTM0.restrict` restricts a `TM0` machine to a set of states closed under its transitions;
`OfTM0.eval_restrict_dom` shows that the restriction halts on the same inputs. It turns a machine
supported on a finite set of states into a machine with finitely many states.

## Main definitions

* `Cslib.PostCorrespondence.OfTM0.Letter`: the letters of configuration words.
* `Cslib.PostCorrespondence.OfTM0.Rule`: the rewriting rules simulating a machine.
* `Cslib.PostCorrespondence.OfTM0.mInstance`: the MPCP instance of a machine and an input.
* `Cslib.PostCorrespondence.OfTM0.restrict`: the restriction of a machine to a closed set of
  states.

## Main results

* `Cslib.PostCorrespondence.OfTM0.eval_dom_iff_solvable`: `M` halts on `l` iff `mInstance M l` is
  solvable.
* `Cslib.PostCorrespondence.OfTM0.primrec_mInstance`: the instance depends primitive recursively
  on the input.
* `Cslib.PostCorrespondence.OfTM0.eval_restrict_dom`: restriction preserves halting.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.PostCorrespondence.OfTM0

open Relation Turing

variable {Γ Λ : Type*}

/-- The letters of configuration words of a `TM0` machine: tape symbols, the scanned cell with
the machine state, the halt marker and the two end markers. -/
inductive Letter (Γ Λ : Type*) where
  /-- A tape symbol. -/
  | sym (a : Γ)
  /-- The scanned cell, holding `a`, with the machine in state `q`. -/
  | cell (q : Λ) (a : Γ)
  /-- The marker left by a halted machine, which then erases the tape. -/
  | halt
  /-- The left end marker. -/
  | lb
  /-- The right end marker. -/
  | rb
deriving DecidableEq

namespace Letter

/-- Letters as a sum type. -/
def equivSum : Letter Γ Λ ≃ Γ ⊕ (Λ × Γ) ⊕ Option Bool where
  toFun
    | sym a => .inl a
    | cell q a => .inr (.inl (q, a))
    | halt => .inr (.inr none)
    | lb => .inr (.inr (some false))
    | rb => .inr (.inr (some true))
  invFun
    | .inl a => sym a
    | .inr (.inl (q, a)) => cell q a
    | .inr (.inr none) => halt
    | .inr (.inr (some false)) => lb
    | .inr (.inr (some true)) => rb
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with a | ⟨q, a⟩ | _ | _ | _ <;> rfl

instance [Fintype Γ] [Fintype Λ] : Fintype (Letter Γ Λ) := Fintype.ofEquiv _ equivSum.symm

instance [Finite Γ] [Finite Λ] : Finite (Letter Γ Λ) := Finite.of_equiv _ equivSum.symm

instance [Primcodable Γ] [Primcodable Λ] : Primcodable (Letter Γ Λ) :=
  Primcodable.ofEquiv _ equivSum

end Letter

open Letter

/-- The word `⊢ L⁻¹ x R ⊣` of a tape `L⁻¹ a R` whose scanned cell is written as the letter `x`. -/
def word (x : Letter Γ Λ) (L R : List Γ) : List (Letter Γ Λ) :=
  lb :: (L.reverse.map sym ++ x :: (R.map sym ++ [rb]))

/-! ### Parsing configuration words -/

/-- Whether a letter is the scanned cell or the halt marker. -/
def IsActive : Letter Γ Λ → Prop
  | cell _ _ => True
  | halt => True
  | _ => False

private theorem split_active {x y : Letter Γ Λ} (hy : IsActive y) :
    ∀ {p s u v : List (Letter Γ Λ)}, (∀ z ∈ u, ¬IsActive z) → (∀ z ∈ v, ¬IsActive z) →
      p ++ y :: s = u ++ x :: v → p = u ∧ y = x ∧ s = v
  | [], s, [], v, _, _, h => by
    obtain ⟨h₁, h₂⟩ := List.cons.inj h
    exact ⟨rfl, h₁, h₂⟩
  | [], s, z :: u, v, hu, _, h => by
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact absurd hy (hu y List.mem_cons_self)
  | z :: p, s, [], v, _, hv, h => by
    obtain ⟨-, h⟩ := List.cons.inj h
    exact absurd hy (hv y (h ▸ List.mem_append_right p List.mem_cons_self))
  | z :: p, s, z' :: u, v, hu, hv, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨h₁, h₂, h₃⟩ := split_active hy (fun w hw => hu w (List.mem_cons_of_mem _ hw)) hv h
    exact ⟨congrArg _ h₁, h₂, h₃⟩

private theorem not_active_left (L : List Γ) :
    ∀ z ∈ (lb :: L.reverse.map sym : List (Letter Γ Λ)), ¬IsActive z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact id
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hz
    exact id

private theorem not_active_right (R : List Γ) :
    ∀ z ∈ (R.map sym ++ [rb] : List (Letter Γ Λ)), ¬IsActive z := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hz
    exact id
  · rw [List.mem_singleton.mp hz]
    exact id

private theorem split_word {x y : Letter Γ Λ} {L R : List Γ} {p s : List (Letter Γ Λ)}
    (h : p ++ y :: s = word x L R) (hy : IsActive y) :
    p = lb :: L.reverse.map sym ∧ y = x ∧ s = R.map sym ++ [rb] :=
  split_active hy (not_active_left L) (not_active_right R) h

private theorem split1 {x y : Letter Γ Λ} {L R : List Γ} {p s : List (Letter Γ Λ)}
    (h : p ++ [y] ++ s = word x L R) (hy : IsActive y) :
    p = lb :: L.reverse.map sym ∧ y = x ∧ s = R.map sym ++ [rb] :=
  split_word (by rw [← h, List.append_assoc, List.singleton_append]) hy

private theorem split2 {x y z : Letter Γ Λ} {L R : List Γ} {p s : List (Letter Γ Λ)}
    (h : p ++ [y, z] ++ s = word x L R) (hy : IsActive y) :
    p = lb :: L.reverse.map sym ∧ y = x ∧ z :: s = R.map sym ++ [rb] :=
  split_word (by rw [← h]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hy

private theorem split2' {x y z : Letter Γ Λ} {L R : List Γ} {p s : List (Letter Γ Λ)}
    (h : p ++ [z, y] ++ s = word x L R) (hy : IsActive y) :
    p ++ [z] = lb :: L.reverse.map sym ∧ y = x ∧ s = R.map sym ++ [rb] :=
  split_word (by rw [← h]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hy

private theorem split3 {x y z w : Letter Γ Λ} {L R : List Γ} {p s : List (Letter Γ Λ)}
    (h : p ++ [z, y, w] ++ s = word x L R) (hy : IsActive y) :
    p ++ [z] = lb :: L.reverse.map sym ∧ y = x ∧ w :: s = R.map sym ++ [rb] :=
  split_word (by rw [← h]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hy

private theorem peel_right_sym {R : List Γ} {s : List (Letter Γ Λ)} {c : Γ}
    (h : sym c :: s = R.map sym ++ [rb]) : ∃ R', R = c :: R' ∧ s = R'.map sym ++ [rb] := by
  rcases R with _ | ⟨c', R'⟩
  · simp at h
  · simp only [List.map_cons, List.cons_append, List.cons.injEq, Letter.sym.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨R', rfl, rfl⟩

private theorem peel_right_rb {R : List Γ} {s : List (Letter Γ Λ)}
    (h : (rb : Letter Γ Λ) :: s = R.map sym ++ [rb]) : R = [] ∧ s = [] := by
  rcases R with _ | ⟨c', R'⟩
  · simp only [List.map_nil, List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.2⟩
  · simp at h

private theorem peel_left_sym {L : List Γ} {p : List (Letter Γ Λ)} {c : Γ}
    (h : p ++ [sym c] = lb :: L.reverse.map sym) :
    ∃ L', L = c :: L' ∧ p = lb :: L'.reverse.map sym := by
  rcases L with _ | ⟨c', L'⟩
  · obtain ⟨-, h₂⟩ := List.append_inj' (s₂ := []) (t₂ := [lb]) h rfl
    simp at h₂
  · rw [List.reverse_cons, List.map_append, List.map_singleton, ← List.cons_append] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, Letter.sym.injEq, and_true] at h₂
    subst h₂
    exact ⟨L', rfl, h₁⟩

private theorem peel_left_lb {L : List Γ} {p : List (Letter Γ Λ)}
    (h : p ++ [lb] = lb :: L.reverse.map sym) : L = [] ∧ p = [] := by
  rcases L with _ | ⟨c', L'⟩
  · obtain ⟨h₁, -⟩ := List.append_inj' (s₂ := []) (t₂ := [lb]) h rfl
    exact ⟨rfl, h₁⟩
  · rw [List.reverse_cons, List.map_append, List.map_singleton, ← List.cons_append] at h
    obtain ⟨-, h₂⟩ := List.append_inj' h rfl
    simp at h₂

theorem rb_notMem_word {x : Letter Γ Λ} (hx : x ≠ rb) (L R : List Γ) :
    rb ∉ lb :: L.reverse.map sym ++ x :: R.map sym := by
  simp [Ne.symm hx]

section Machine

variable [Inhabited Γ]

/-- The configuration with state `q`, scanned symbol `a`, the cells `L` to the left (nearest
first) and the cells `R` to the right. -/
@[expose] def cfgOf (q : Λ) (a : Γ) (L R : List Γ) : TM0.Cfg Γ Λ :=
  ⟨q, ⟨a, ListBlank.mk L, ListBlank.mk R⟩⟩

theorem exists_cfgOf (c : TM0.Cfg Γ Λ) : ∃ q a L R, c = cfgOf q a L R := by
  obtain ⟨q, ⟨a, L, R⟩⟩ := c
  induction L using ListBlank.induction_on with
  | h L =>
  induction R using ListBlank.induction_on with
  | h R => exact ⟨q, a, L, R, rfl⟩

variable [Inhabited Λ]

/-- The rules of the semi-Thue system simulating a `TM0` machine `M`; each rule is a domino whose
top rewrites to its bottom. -/
inductive Rule (M : TM0.Machine Γ Λ) : Domino (Letter Γ Λ) → Prop
  /-- Halting: the scanned cell becomes the halt marker. -/
  | stop {q a} : M q a = none → Rule M ⟨[cell q a], [halt]⟩
  /-- A write step. -/
  | write {q a q' b} : M q a = some (q', .write b) → Rule M ⟨[cell q a], [cell q' b]⟩
  /-- A right move onto a written cell. -/
  | right {q a q'} (c : Γ) : M q a = some (q', .move .right) →
      Rule M ⟨[cell q a, sym c], [sym a, cell q' c]⟩
  /-- A right move onto a fresh blank cell. -/
  | rightEnd {q a q'} : M q a = some (q', .move .right) →
      Rule M ⟨[cell q a, rb], [sym a, cell q' default, rb]⟩
  /-- A left move onto a written cell. -/
  | left {q a q'} (c : Γ) : M q a = some (q', .move .left) →
      Rule M ⟨[sym c, cell q a], [cell q' c, sym a]⟩
  /-- A left move onto a fresh blank cell. -/
  | leftEnd {q a q'} : M q a = some (q', .move .left) →
      Rule M ⟨[lb, cell q a], [lb, cell q' default, sym a]⟩
  /-- The halt marker erases the symbol to its left. -/
  | eatLeft (c : Γ) : Rule M ⟨[sym c, halt], [halt]⟩
  /-- The halt marker erases the symbol to its right. -/
  | eatRight (c : Γ) : Rule M ⟨[halt, sym c], [halt]⟩
  /-- The erased tape is deleted. -/
  | finish : Rule M ⟨[lb, halt, rb], []⟩

theorem finite_rule [Finite Γ] [Finite Λ] (M : TM0.Machine Γ Λ) : {d | Rule M d}.Finite := by
  have hfin : {w : List (Letter Γ Λ) | w.length ≤ 3}.Finite := List.finite_length_le _ _
  refine ((hfin.prod hfin).image fun p => (⟨p.1, p.2⟩ : Domino (Letter Γ Λ))).subset ?_
  intro d hd
  refine ⟨(d.top, d.bottom), ?_, rfl⟩
  cases hd <;> simp

/-- The dominoes of the MPCP instance simulating `M`: the rules and a copy domino for every
letter. -/
noncomputable def dominoes [Fintype Γ] [Fintype Λ] (M : TM0.Machine Γ Λ) :
    List (Domino (Letter Γ Λ)) :=
  (finite_rule M).toFinset.toList ++ (Finset.univ : Finset (Letter Γ Λ)).toList.map copy

theorem mem_dominoes [Fintype Γ] [Fintype Λ] {M : TM0.Machine Γ Λ} {d : Domino (Letter Γ Λ)} :
    d ∈ dominoes M ↔ Rule M d ∨ ∃ x, d = copy x := by
  simp only [dominoes, List.mem_append, Finset.mem_toList, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, List.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨x, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, rfl⟩
  · rintro (h | ⟨x, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, rfl⟩

/-- The MPCP instance simulating `M` on input `l`: the start domino is `⟨[], ⊢ q₀ l ⊣⟩`. -/
noncomputable def mInstance [Fintype Γ] [Fintype Λ] (M : TM0.Machine Γ Λ) (l : List Γ) :
    MInstance (Letter Γ Λ) :=
  ⟨⟨[], word (cell default l.headI) [] l.tail⟩, dominoes M⟩

/-! ### Steps of the machine -/

theorem init_eq (l : List Γ) : (TM0.init l : TM0.Cfg Γ Λ) = cfgOf default l.headI [] l.tail :=
  rfl

theorem step_of_eq_none {M : TM0.Machine Γ Λ} {q a} (h : M q a = none) (L R : List Γ) :
    TM0.step M (cfgOf q a L R) = none := by
  change (M q a).map _ = none
  rw [h]
  rfl

theorem step_of_eq_write {M : TM0.Machine Γ Λ} {q a q' b} (h : M q a = some (q', .write b))
    (L R : List Γ) : TM0.step M (cfgOf q a L R) = some (cfgOf q' b L R) := by
  change (M q a).map _ = _
  rw [h]
  rfl

theorem step_of_eq_right {M : TM0.Machine Γ Λ} {q a q'} (h : M q a = some (q', .move .right))
    (L R : List Γ) : TM0.step M (cfgOf q a L R) = some (cfgOf q' R.headI (a :: L) R.tail) := by
  change (M q a).map _ = _
  rw [h]
  rfl

theorem step_of_eq_left {M : TM0.Machine Γ Λ} {q a q'} (h : M q a = some (q', .move .left))
    (L R : List Γ) : TM0.step M (cfgOf q a L R) = some (cfgOf q' L.headI L.tail (a :: R)) := by
  change (M q a).map _ = _
  rw [h]
  rfl

/-- The machine halts on input `l`. -/
@[expose] def Halts (M : TM0.Machine Γ Λ) (l : List Γ) : Prop :=
  ∃ c, StateTransition.Reaches (TM0.step M) (TM0.init l) c ∧ TM0.step M c = none

theorem eval_dom_iff (M : TM0.Machine Γ Λ) (l : List Γ) : (TM0.eval M l).Dom ↔ Halts M l := by
  rw [TM0.eval, Part.map_Dom, Part.dom_iff_mem]
  exact exists_congr fun _ => StateTransition.mem_eval

/-! ### Soundness: the words reachable from the initial word -/

/-- The words reachable from the initial word: configuration words of reachable configurations,
and, once the machine has halted, words with the halt marker and the empty word. -/
def Good (M : TM0.Machine Γ Λ) (l : List Γ) (w : List (Letter Γ Λ)) : Prop :=
  (∃ q a L R, StateTransition.Reaches (TM0.step M) (TM0.init l) (cfgOf q a L R) ∧
      w = word (cell q a) L R) ∨
    (Halts M l ∧ (w = [] ∨ ∃ L R, w = word halt L R))

/-- One rewriting step preserves `Good`. -/
theorem good_of_rewrites {M : TM0.Machine Γ Λ} {l : List Γ} {u v : List (Letter Γ Λ)}
    (hu : Good M l u) (h : Rewrites (Rule M) u v) : Good M l v := by
  obtain ⟨p, d, s, hd, rfl, rfl⟩ := h
  rcases hu with ⟨q, a, L, R, hr, hw⟩ | ⟨hh, hw | ⟨L, R, hw⟩⟩
  · cases hd with
    | stop hM =>
      obtain ⟨rfl, h, rfl⟩ := split1 hw trivial
      cases h
      exact Or.inr ⟨⟨_, hr, step_of_eq_none hM L R⟩, Or.inr ⟨L, R, by simp [word]⟩⟩
    | @write _ _ q' b hM =>
      obtain ⟨rfl, h, rfl⟩ := split1 hw trivial
      cases h
      exact Or.inl ⟨q', b, L, R, hr.tail (step_of_eq_write hM L R), by simp [word]⟩
    | @right _ _ q' c hM =>
      obtain ⟨rfl, h, hs⟩ := split2 hw trivial
      cases h
      obtain ⟨R', rfl, rfl⟩ := peel_right_sym hs
      exact Or.inl ⟨q', c, _ :: L, R', hr.tail (step_of_eq_right hM L (c :: R')),
        by simp [word]⟩
    | @rightEnd _ _ q' hM =>
      obtain ⟨rfl, h, hs⟩ := split2 hw trivial
      cases h
      obtain ⟨rfl, rfl⟩ := peel_right_rb hs
      exact Or.inl ⟨q', default, _ :: L, [], hr.tail (step_of_eq_right hM L []), by simp [word]⟩
    | @left _ _ q' c hM =>
      obtain ⟨hp, h, rfl⟩ := split2' hw trivial
      cases h
      obtain ⟨L', rfl, rfl⟩ := peel_left_sym hp
      exact Or.inl ⟨q', c, L', _ :: R, hr.tail (step_of_eq_left hM (c :: L') R),
        by simp [word]⟩
    | @leftEnd _ _ q' hM =>
      obtain ⟨hp, h, rfl⟩ := split2' hw trivial
      cases h
      obtain ⟨rfl, rfl⟩ := peel_left_lb hp
      exact Or.inl ⟨q', default, [], _ :: R, hr.tail (step_of_eq_left hM [] R), by simp [word]⟩
    | eatLeft c =>
      obtain ⟨-, h, -⟩ := split2' hw trivial
      cases h
    | eatRight c =>
      obtain ⟨-, h, -⟩ := split2 hw trivial
      cases h
    | finish =>
      obtain ⟨-, h, -⟩ := split3 hw trivial
      cases h
  · cases hd <;> simp at hw
  · cases hd with
    | stop hM =>
      obtain ⟨-, h, -⟩ := split1 hw trivial
      cases h
    | write hM =>
      obtain ⟨-, h, -⟩ := split1 hw trivial
      cases h
    | right c hM =>
      obtain ⟨-, h, -⟩ := split2 hw trivial
      cases h
    | rightEnd hM =>
      obtain ⟨-, h, -⟩ := split2 hw trivial
      cases h
    | left c hM =>
      obtain ⟨-, h, -⟩ := split2' hw trivial
      cases h
    | leftEnd hM =>
      obtain ⟨-, h, -⟩ := split2' hw trivial
      cases h
    | eatLeft c =>
      obtain ⟨hp, -, rfl⟩ := split2' hw trivial
      obtain ⟨L', rfl, rfl⟩ := peel_left_sym hp
      exact Or.inr ⟨hh, Or.inr ⟨L', R, by simp [word]⟩⟩
    | eatRight c =>
      obtain ⟨rfl, -, hs⟩ := split2 hw trivial
      obtain ⟨R', rfl, rfl⟩ := peel_right_sym hs
      exact Or.inr ⟨hh, Or.inr ⟨L, R', by simp [word]⟩⟩
    | finish =>
      obtain ⟨hp, -, hs⟩ := split3 hw trivial
      obtain ⟨rfl, rfl⟩ := peel_left_lb hp
      obtain ⟨rfl, rfl⟩ := peel_right_rb hs
      exact Or.inr ⟨hh, Or.inl rfl⟩

theorem good_of_reflTransGen {M : TM0.Machine Γ Λ} {l : List Γ} {w : List (Letter Γ Λ)}
    (h : ReflTransGen (Rewrites (Rule M)) (word (cell default l.headI) [] l.tail) w) :
    Good M l w := by
  induction h with
  | refl => exact Or.inl ⟨default, l.headI, [], l.tail, ReflTransGen.refl, rfl⟩
  | tail _ hstep ih => exact good_of_rewrites ih hstep

theorem good_ends {M : TM0.Machine Γ Λ} {l : List Γ} {w : List (Letter Γ Λ)} (h : Good M l w) :
    w = [] ∨ ∃ w', w = w' ++ [rb] ∧ rb ∉ w' := by
  rcases h with ⟨q, a, L, R, -, rfl⟩ | ⟨-, rfl | ⟨L, R, rfl⟩⟩
  · exact Or.inr ⟨lb :: L.reverse.map sym ++ cell q a :: R.map sym, by simp [word],
      rb_notMem_word (by simp) L R⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨lb :: L.reverse.map sym ++ halt :: R.map sym, by simp [word],
      rb_notMem_word (by simp) L R⟩

theorem rb_mem_top {M : TM0.Machine Γ Λ} {d : Domino (Letter Γ Λ)} (hd : Rule M d)
    (h : rb ∈ d.top) : ∃ t, d.top = t ++ [rb] ∧ rb ∉ t := by
  cases hd with
  | rightEnd hM => exact ⟨[cell _ _], rfl, by simp⟩
  | finish => exact ⟨[lb, halt], rfl, by simp⟩
  | _ => simp at h

/-! ### Completeness -/

theorem halt_reflTransGen {M : TM0.Machine Γ Λ} :
    ∀ L R : List Γ, ReflTransGen (Rewrites (Rule M)) (word halt L R) []
  | c :: L, R => by
    refine ReflTransGen.head ⟨lb :: L.reverse.map sym, ⟨[sym c, halt], [halt]⟩,
      R.map sym ++ [rb], Rule.eatLeft c, by simp [word], by simp [word]⟩ (halt_reflTransGen L R)
  | [], c :: R => by
    refine ReflTransGen.head ⟨[lb], ⟨[halt, sym c], [halt]⟩, R.map sym ++ [rb], Rule.eatRight c,
      by simp [word], by simp [word]⟩ (halt_reflTransGen [] R)
  | [], [] => ReflTransGen.single ⟨[], ⟨[lb, halt, rb], []⟩, [], Rule.finish, rfl, rfl⟩

theorem reflTransGen_of_reaches {M : TM0.Machine Γ Λ} {c c' : TM0.Cfg Γ Λ}
    (h : StateTransition.Reaches (TM0.step M) c c') (hc' : TM0.step M c' = none) :
    ∀ q a L R, c = cfgOf q a L R →
      ReflTransGen (Rewrites (Rule M)) (word (cell q a) L R) [] := by
  induction h using ReflTransGen.head_induction_on with
  | refl =>
    rintro q a L R rfl
    have hM : M q a = none := by
      rcases hM : M q a with _ | ⟨q', s⟩
      · rfl
      · change (M q a).map _ = none at hc'
        rw [hM] at hc'
        cases hc'
    refine ReflTransGen.head ⟨lb :: L.reverse.map sym, ⟨[cell q a], [halt]⟩, R.map sym ++ [rb],
      Rule.stop hM, by simp [word], by simp [word]⟩ (halt_reflTransGen L R)
  | @head c₀ c₁ hstep _ ih =>
    rintro q a L R rfl
    rcases hM : M q a with _ | ⟨q', _ | b⟩
    · rw [Option.mem_def, step_of_eq_none hM] at hstep
      cases hstep
    · rename_i dir
      cases dir with
      | left =>
        rw [Option.mem_def, step_of_eq_left hM, Option.some_inj] at hstep
        rcases L with _ | ⟨c', L'⟩
        · refine ReflTransGen.head ⟨[], ⟨[lb, cell q a], [lb, cell q' default, sym a]⟩,
            R.map sym ++ [rb], Rule.leftEnd hM, by simp [word], by simp [word]⟩
            (ih q' default [] (a :: R) hstep.symm)
        · refine ReflTransGen.head ⟨lb :: L'.reverse.map sym, ⟨[sym c', cell q a],
            [cell q' c', sym a]⟩, R.map sym ++ [rb], Rule.left c' hM, by simp [word],
            by simp [word]⟩ (ih q' c' L' (a :: R) hstep.symm)
      | right =>
        rw [Option.mem_def, step_of_eq_right hM, Option.some_inj] at hstep
        rcases R with _ | ⟨c', R'⟩
        · refine ReflTransGen.head ⟨lb :: L.reverse.map sym, ⟨[cell q a, rb],
            [sym a, cell q' default, rb]⟩, [], Rule.rightEnd hM, by simp [word],
            by simp [word]⟩ (ih q' default (a :: L) [] hstep.symm)
        · refine ReflTransGen.head ⟨lb :: L.reverse.map sym, ⟨[cell q a, sym c'],
            [sym a, cell q' c']⟩, R'.map sym ++ [rb], Rule.right c' hM, by simp [word],
            by simp [word]⟩ (ih q' c' (a :: L) R' hstep.symm)
    · rw [Option.mem_def, step_of_eq_write hM, Option.some_inj] at hstep
      refine ReflTransGen.head ⟨lb :: L.reverse.map sym, ⟨[cell q a], [cell q' b]⟩,
        R.map sym ++ [rb], Rule.write hM, by simp [word], by simp [word]⟩
        (ih q' b L R hstep.symm)

/-! ### The reduction -/

/-- A `TM0` machine halts on input `l` iff the MPCP instance `mInstance M l` is solvable. -/
theorem eval_dom_iff_solvable [Fintype Γ] [Fintype Λ] (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔ (mInstance M l).Solvable := by
  rw [eval_dom_iff]
  constructor
  · rintro ⟨c, hr, hc⟩
    exact mSolvable_of_reflTransGen (fun d hd => mem_dominoes.mpr (Or.inl hd))
      (fun x => mem_dominoes.mpr (Or.inr ⟨x, rfl⟩))
      (reflTransGen_of_reaches hr hc _ _ _ _ (init_eq l))
  · intro h
    have hD : ∀ d ∈ dominoes M, Rule M d ∨ d.top = d.bottom := by
      intro d hd
      rcases mem_dominoes.mp hd with hd | ⟨x, rfl⟩
      · exact Or.inl hd
      · exact Or.inr rfl
    have he : ∀ d ∈ dominoes M, rb ∈ d.top → ∃ t, d.top = t ++ [rb] ∧ rb ∉ t := by
      intro d hd hrb
      rcases mem_dominoes.mp hd with hd | ⟨x, rfl⟩
      · exact rb_mem_top hd hrb
      · simp only [copy, List.mem_singleton] at hrb
        exact ⟨[], by rw [hrb]; rfl, List.not_mem_nil⟩
    have hrt := reflTransGen_of_mSolvable hD he
      (fun u hu => good_ends (good_of_reflTransGen hu)) h
    rcases good_of_reflTransGen hrt with ⟨q, a, L, R, -, h⟩ | ⟨hh, -⟩
    · simp [word] at h
    · exact hh

theorem primrec_mInstance [Fintype Γ] [Fintype Λ] [Primcodable Γ] [Primcodable Λ]
    (M : TM0.Machine Γ Λ) : Primrec (mInstance M) := by
  have hsym : Primrec (sym : Γ → Letter Γ Λ) := Primrec.dom_finite _
  have hcell : Primrec fun a : Γ => (cell default a : Letter Γ Λ) := Primrec.dom_finite _
  have hw : Primrec fun l : List Γ => word (cell (default : Λ) l.headI) [] l.tail := by
    have : Primrec fun l : List Γ => (lb : Letter Γ Λ) :: (cell (default : Λ) l.headI ::
        (l.tail.map sym ++ [rb])) :=
      Primrec.list_cons.comp (Primrec.const _) (Primrec.list_cons.comp
        (hcell.comp Primrec.list_headI) (Primrec.list_append.comp
          (Primrec.list_map Primrec.list_tail (hsym.comp Primrec.snd).to₂) (Primrec.const _)))
    exact this.of_eq fun _ => rfl
  exact (MInstance.primrec₂_mk.comp
    (Domino.primrec₂_mk.comp (Primrec.const ([] : List (Letter Γ Λ))) hw)
    (Primrec.const _)).of_eq fun _ => rfl

end Machine

/-! ### Restricting a machine to a closed set of states -/

section Restrict

open StateTransition

variable [Inhabited Γ] [Inhabited Λ]

/-- The restriction of a `TM0` machine to a set of states closed under its transitions. -/
def restrict (M : TM0.Machine Γ Λ) {S : Set Λ}
    (hS : ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S) [Inhabited S] :
    TM0.Machine Γ S := fun q a =>
  (M q.1 a).pmap (fun x hx => (⟨x.1, hS hx q.2⟩, x.2)) fun _ h => h

/-- The configuration of the original machine underlying a configuration of the restriction. -/
def liftCfg {S : Set Λ} (c : TM0.Cfg Γ S) : TM0.Cfg Γ Λ := ⟨c.q.1, c.Tape⟩

omit [Inhabited Λ] in
private theorem map_pmap_val {S : Set Λ} {β : Type*} (o : Option (Λ × β))
    (f : ∀ x ∈ o, x.1 ∈ S) :
    (o.pmap (fun x hx => ((⟨x.1, f x hx⟩ : S), x.2)) fun _ h => h).map
      (Prod.map Subtype.val id) = o := by
  cases o <;> rfl

theorem step_liftCfg (M : TM0.Machine Γ Λ) {S : Set Λ}
    (hS : ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S) [Inhabited S] (c : TM0.Cfg Γ S) :
    (TM0.step (restrict M hS) c).map liftCfg = TM0.step M (liftCfg c) := by
  obtain ⟨q, T⟩ := c
  have h := map_pmap_val (S := S) (M q.1 T.head) fun x hx => hS (q := q.1) (a := T.head) hx q.2
  change ((restrict M hS q T.head).map _).map liftCfg = (M q.1 T.head).map _
  rw [← h, Option.map_map, Option.map_map]
  rfl

theorem restrict_respects (M : TM0.Machine Γ Λ) {S : Set Λ}
    (hS : ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S) [Inhabited S] :
    Respects (TM0.step (restrict M hS)) (TM0.step M) fun c c' => liftCfg c = c' := by
  refine fun_respects.2 fun c => ?_
  have h := step_liftCfg M hS c
  rcases e : TM0.step (restrict M hS) c with _ | c'
  · rw [e] at h
    exact h.symm
  · rw [e] at h
    exact TransGen.single h.symm

theorem eval_restrict_dom (M : TM0.Machine Γ Λ) {S : Set Λ}
    (hS : ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S) [Inhabited S]
    (hd : (default : S).1 = default) (l : List Γ) :
    (TM0.eval (restrict M hS) l).Dom ↔ (TM0.eval M l).Dom := by
  simp only [TM0.eval, Part.map_Dom]
  have h0 : liftCfg (TM0.init l : TM0.Cfg Γ S) = TM0.init l := by
    simp only [liftCfg, TM0.init, hd]
  exact (tr_eval_dom (restrict_respects M hS) h0).symm

end Restrict

end Cslib.PostCorrespondence.OfTM0
