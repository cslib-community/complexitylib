/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.ReadOnce
public import CslibFrontier.Computability.Circuit.NNF.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
import CslibFrontier.Foundations.Data.List.FoldlIdx
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Read-once branching programs as d-DNNFs

A read-once branching program `P` of length `L` with states `S` over the alphabet `Bool`
(`Cslib.BranchingPrograms.ReadOnceProgram`), together with a variable order `ord : Fin L → ι`,
computes `x ↦ P.eval (x ∘ ord)`: an ordered binary decision diagram reading `x (ord 0)`,
`x (ord 1)`, …. When the order is injective, this function is computed by a d-DNNF with
`(L + 1) |S| + 2L + 2L |S|` nodes (`ReadOnceProgram.toNNF`, `ReadOnceProgram.card_nnfNode`), the
compilation of ordered binary decision diagrams into d-DNNFs
[ArenasBroadrickLiewVanDenBroeck2026, Fact 3.3].

The circuit has a node `(t, q)` for each time `t ≤ L` and state `q`, computing whether the program
accepts from state `q` at time `t` (`ReadOnceProgram.eval_state`): at `t = L` it is the constant
`accept q`, and before it is
`(¬x_{ord t} ∧ (t + 1, step t q false)) ∨ (x_{ord t} ∧ (t + 1, step t q true))`. The `∨` is
deterministic because its children disagree on `x_{ord t}`, and the `∧` is decomposable because
`ord t` is not read again.

Programs reading a list of labelled variables with a label-dependent transition
(`ReadOnceProgram.ofList`, `ReadOnceProgram.listOrder`) evaluate by a left fold over the list
(`ReadOnceProgram.eval_ofList`).

## Main definitions

* `Cslib.BranchingPrograms.ReadOnceProgram.toNNF`: the d-DNNF of a program and a variable order.
* `Cslib.BranchingPrograms.ReadOnceProgram.ofList`,
  `Cslib.BranchingPrograms.ReadOnceProgram.listOrder`: the program reading a list of labelled
  variables.

## Main results

* `Cslib.BranchingPrograms.ReadOnceProgram.toFun_toNNF`: the circuit computes the program.
* `Cslib.BranchingPrograms.ReadOnceProgram.isDecomposable_toNNF`,
  `Cslib.BranchingPrograms.ReadOnceProgram.isDeterministic_toNNF`: it is a d-DNNF for an injective
  order.
* `Cslib.BranchingPrograms.ReadOnceProgram.card_nnfNode`: its size.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval_ofList`: list programs evaluate by a fold.

## References

* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
-/

@[expose] public section

namespace Cslib.BranchingPrograms.ReadOnceProgram

open Cslib.Circuits

variable {L : ℕ} {S ι : Type*} (P : ReadOnceProgram L S Bool) (ord : Fin L → ι)

/-- The state reached from the state `s` at time `t` by reading the rest of the word `y`. -/
def runFrom (y : Fin L → Bool) (t : ℕ) (s : S) : S :=
  ((List.ofFn y).drop t).foldlIdx P.stepAt s t

/-- Reading the whole word from the start gives the final state. -/
theorem runFrom_zero (y : Fin L → Bool) : P.runFrom y 0 P.start = P.finalState y :=
  (P.finalState_eq y).symm

variable (L S) in
/-- The nodes of the d-DNNF of a program: states at each time, literals at each time, and the
conjunctions of a literal with the next state. -/
abbrev NNFNode : Type _ :=
  (Fin (L + 1) × S) ⊕ (Fin L × Bool) ⊕ (Fin L × S × Bool)

/-- The gate at a node of the d-DNNF of a program. -/
def nnfGate : NNFNode L S → NNF.Gate ι (NNFNode L S)
  | .inl (t, q) =>
    if h : t.val < L then .or (.inr (.inr (⟨t, h⟩, q, false))) (.inr (.inr (⟨t, h⟩, q, true)))
    else .const (P.accept q)
  | .inr (.inl (t, b)) => .lit (ord t) b
  | .inr (.inr (t, q, b)) => .and (.inr (.inl (t, b))) (.inl (t.succ, P.step t q b))

/-- The rank of a node: decreasing along time. -/
def nnfRank : NNFNode L S → ℕ
  | .inl (t, _) => 3 * (L - t) + 2
  | .inr (.inl _) => 0
  | .inr (.inr (t, _, _)) => 3 * (L - t) + 1

theorem nnfGate_and {v l r : NNFNode L S} (h : P.nnfGate ord v = .and l r) :
    nnfRank l < nnfRank v ∧ nnfRank r < nnfRank v := by
  rcases v with ⟨t, q⟩ | ⟨t, b⟩ | ⟨t, q, b⟩
  · simp only [nnfGate] at h; split at h <;> cases h
  · cases h
  · simp only [nnfGate, NNF.Gate.and.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [nnfRank, Fin.val_succ]
    have := t.isLt
    omega

theorem nnfGate_or {v l r : NNFNode L S} (h : P.nnfGate ord v = .or l r) :
    nnfRank l < nnfRank v ∧ nnfRank r < nnfRank v := by
  rcases v with ⟨t, q⟩ | ⟨t, b⟩ | ⟨t, q, b⟩
  · simp only [nnfGate] at h
    split at h
    · simp only [NNF.Gate.or.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [nnfRank]
    · cases h
  · cases h
  · cases h

/-- The d-DNNF of a program reading the variables in the order `ord`. -/
def toNNF : NNF ι (NNFNode L S) where
  gate := P.nnfGate ord
  rank := nnfRank
  and_lt _ _ _ h := P.nnfGate_and ord h
  or_lt _ _ _ h := P.nnfGate_or ord h
  root := .inl (0, P.start)

/-- **The state nodes compute the program**: the node `(t, q)` accepts exactly when the program
accepts from the state `q` at time `t`. -/
theorem eval_state (x : ι → Bool) :
    ∀ (k : ℕ) (t : Fin (L + 1)) (q : S), L - t = k →
      (P.toNNF ord).eval x (.inl (t, q)) = P.accept (P.runFrom (x ∘ ord) t q) := by
  intro k
  induction k with
  | zero =>
    intro t q hk
    have ht : L ≤ t := by omega
    rw [NNF.eval_const (b := P.accept q) (by simp [toNNF, nnfGate, not_lt.mpr ht]), runFrom,
      List.drop_eq_nil_of_le (by simpa using ht)]
    rfl
  | succ k ih =>
    intro t q hk
    have ht : t.val < L := by omega
    have hor : (P.toNNF ord).gate (.inl (t, q)) =
        .or (.inr (.inr (⟨t, ht⟩, q, false))) (.inr (.inr (⟨t, ht⟩, q, true))) := by
      simp [toNNF, nnfGate, ht]
    have hand (b : Bool) : (P.toNNF ord).gate (.inr (.inr (⟨t, ht⟩, q, b))) =
        .and (.inr (.inl (⟨t, ht⟩, b))) (.inl ((⟨t, ht⟩ : Fin L).succ, P.step ⟨t, ht⟩ q b)) := rfl
    have hlit (b : Bool) : (P.toNNF ord).gate (.inr (.inl (⟨t, ht⟩, b))) =
        .lit (ord ⟨t, ht⟩) b := rfl
    have hnext (b : Bool) := ih (⟨t, ht⟩ : Fin L).succ (P.step ⟨t, ht⟩ q b)
      (by simp only [Fin.val_succ]; omega)
    have hrun (b : Bool) (hb : x (ord ⟨t, ht⟩) = b) :
        P.runFrom (x ∘ ord) t q = P.runFrom (x ∘ ord) (t + 1) (P.step ⟨t, ht⟩ q b) := by
      rw [runFrom, List.drop_eq_getElem_cons (by simpa using ht), List.foldlIdx_cons,
        List.getElem_ofFn]
      simp only [stepAt, ht, dite_true, Function.comp_apply, hb]
      rfl
    rw [NNF.eval_or hor, NNF.eval_and (hand false), NNF.eval_and (hand true),
      NNF.eval_lit (hlit false), NNF.eval_lit (hlit true), hnext, hnext]
    simp only [Fin.val_succ]
    cases hx : x (ord ⟨t, ht⟩) <;> simp [hrun _ hx]

/-- **The circuit computes the program** on the variables in the order `ord`. -/
theorem toFun_toNNF (x : ι → Bool) : (P.toNNF ord).toFun x = P.eval (x ∘ ord) := by
  rw [NNF.toFun, show (P.toNNF ord).root = .inl (0, P.start) from rfl,
    P.eval_state ord x _ 0 P.start rfl]
  simp only [Fin.val_zero, eval, runFrom_zero]

variable [DecidableEq ι]

/-- The state node at time `t` mentions only the variables read from time `t` on. -/
theorem vars_state_subset :
    ∀ (k : ℕ) (t : Fin (L + 1)) (q : S), L - t = k →
      (P.toNNF ord).vars (.inl (t, q)) ⊆
        (Finset.univ.filter fun j : Fin L => t.val ≤ j.val).image ord := by
  intro k
  induction k with
  | zero =>
    intro t q hk
    have ht : L ≤ t := by omega
    rw [NNF.vars_const (b := P.accept q) (by simp [toNNF, nnfGate, not_lt.mpr ht])]
    exact Finset.empty_subset _
  | succ k ih =>
    intro t q hk
    have ht : t.val < L := by omega
    have hor : (P.toNNF ord).gate (.inl (t, q)) =
        .or (.inr (.inr (⟨t, ht⟩, q, false))) (.inr (.inr (⟨t, ht⟩, q, true))) := by
      simp [toNNF, nnfGate, ht]
    have hsub (b : Bool) : (P.toNNF ord).vars (.inr (.inr (⟨t, ht⟩, q, b))) ⊆
        (Finset.univ.filter fun j : Fin L => t.val ≤ j.val).image ord := by
      rw [NNF.vars_and (show (P.toNNF ord).gate (.inr (.inr (⟨t, ht⟩, q, b))) = _ from rfl),
        NNF.vars_lit (show (P.toNNF ord).gate (.inr (.inl (⟨t, ht⟩, b))) = _ from rfl)]
      refine Finset.union_subset (Finset.singleton_subset_iff.mpr
        (Finset.mem_image_of_mem _ (by simp)))
        ((ih _ _ (by simp only [Fin.val_succ]; omega)).trans ?_)
      refine Finset.image_subset_image fun j hj => ?_
      simp only [Fin.val_succ, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      omega
    rw [NNF.vars_or hor]
    exact Finset.union_subset (hsub false) (hsub true)

/-- **The circuit is decomposable** when the order reads every variable at most once. -/
theorem isDecomposable_toNNF (hord : Function.Injective ord) : (P.toNNF ord).IsDecomposable := by
  rintro v l r hg
  rcases v with ⟨t, q⟩ | ⟨t, b⟩ | ⟨t, q, b⟩
  · simp only [toNNF, nnfGate] at hg; split at hg <;> cases hg
  · cases hg
  · simp only [toNNF, nnfGate, NNF.Gate.and.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    rw [NNF.vars_lit (i := ord t) (b := b) rfl, Finset.disjoint_singleton_left]
    intro hmem
    obtain ⟨j, hj, hjt⟩ := Finset.mem_image.mp (P.vars_state_subset ord _ t.succ _ rfl hmem)
    rw [hord hjt] at hj
    simp at hj

omit [DecidableEq ι] in
/-- **The circuit is deterministic**: the two branches of a state node disagree on the variable
read. -/
theorem isDeterministic_toNNF : (P.toNNF ord).IsDeterministic := by
  rintro v l r hg x ⟨hl, hr⟩
  rcases v with ⟨t, q⟩ | ⟨t, b⟩ | ⟨t, q, b⟩
  · simp only [toNNF, nnfGate] at hg
    split at hg
    next ht =>
      simp only [NNF.Gate.or.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      rw [NNF.eval_and rfl, NNF.eval_lit rfl] at hl hr
      cases hx : x (ord ⟨t, ht⟩) <;> simp_all
    · cases hg
  · cases hg
  · cases hg

omit [DecidableEq ι] in
/-- **Size**: the d-DNNF of a program of length `L` with `|S|` states has
`(L + 1) |S| + 2L + 2L |S|` nodes. -/
theorem card_nnfNode [Fintype S] :
    Fintype.card (NNFNode L S) = (L + 1) * Fintype.card S + 2 * L + 2 * L * Fintype.card S := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-! ### Programs reading a list of labelled variables -/

variable {Λ : Type*}

/-- The program reading the list `items` of labelled variables in order, moving from state `s`
to `step λ s b` on reading the value `b` of a variable labelled `λ`. -/
def ofList (items : List (ι × Λ)) (start : S) (step : Λ → S → Bool → S) (accept : S → Bool) :
    ReadOnceProgram items.length S Bool where
  start := start
  step t s b := step items[t].2 s b
  accept := accept

/-- The variable order of a list of labelled variables. -/
def listOrder (items : List (ι × Λ)) : Fin items.length → ι :=
  fun t => items[t].1

omit [DecidableEq ι] in
/-- The order of a list of distinct variables is injective. -/
theorem listOrder_injective {items : List (ι × Λ)} (h : (items.map Prod.fst).Nodup) :
    Function.Injective (listOrder items) := fun i j hij =>
  Fin.ext ((List.Nodup.getElem_inj_iff h (hi := by simp) (hj := by simp)).mp
    (by simpa [listOrder] using hij))

omit [DecidableEq ι] in
/-- **List programs evaluate by a fold** over the labelled variables. -/
theorem eval_ofList (items : List (ι × Λ)) (start : S) (step : Λ → S → Bool → S)
    (accept : S → Bool) (x : ι → Bool) :
    (ofList items start step accept).eval (x ∘ listOrder items) =
      accept (items.foldl (fun s a => step a.2 s (x a.1)) start) := by
  set P := ofList items start step accept
  have key : ∀ (pre suf : List (ι × Λ)), items = pre ++ suf → ∀ s,
      suf.foldlIdx (fun i s a => P.stepAt i s (x a.1)) s pre.length =
        suf.foldl (fun s a => step a.2 s (x a.1)) s := by
    intro pre suf
    induction suf generalizing pre with
    | nil => intros; rfl
    | cons a suf ih =>
      intro h s
      have hlt : pre.length < items.length := by rw [h]; simp
      have ha : items[pre.length] = a := by simp [h]
      rw [List.foldlIdx_cons, List.foldl_cons, ← ih (pre ++ [a]) (by simp [h]),
        List.length_append, List.length_singleton]
      simp only [P, stepAt, ofList, hlt, dite_true, Fin.getElem_fin, ha]
  rw [eval, finalState_eq]
  have hofn : List.ofFn (x ∘ listOrder items) = items.map fun a => x a.1 := by
    rw [← List.ofFn_getElem_eq_map]; rfl
  rw [hofn, List.foldlIdx_map]
  exact congrArg accept (key [] items rfl P.start)

end Cslib.BranchingPrograms.ReadOnceProgram
