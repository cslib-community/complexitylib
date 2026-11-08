/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded.Encoding
public import Complexity.Computability.Circuit.Encoding.Evaluation
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD

/-!
# Three-valued evaluation of unbounded fan-in circuits

Kleene's strong three-valued logic reads `none : Option Bool` as an unknown value. A conjunction is
false as soon as one argument is known to be false, true when all are known to be true, and
unknown otherwise; disjunction is dual, and negation maps an unknown value to an unknown value
[Kleene, *Introduction to Metamathematics*, Section 64][Kleene1952]. Evaluating a circuit over the
unbounded fan-in basis in this logic on a partial assignment of its inputs gives a value that is
correct for every completion of the assignment whenever it is known
(`kleeneInterpretation_approx`, with `evalCode_rel`), and that is known when every argument is
(`kleeneInterpretation_some`).

`kleeneEval` evaluates a gate list in this logic, reading arguments by position like `evalCode`
(`kleeneEval_eq_evalCode`), and it is polynomial-time (`computableInPolyTime_kleeneEval`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.Approx`: an option is unknown or the given Boolean.
* `Cslib.Circuits.Boolean.Unbounded.kleeneOp`,
  `Cslib.Circuits.Boolean.Unbounded.kleeneInterpretation`: the operations in Kleene's logic.
* `Cslib.Circuits.Boolean.Unbounded.kleeneEval`: evaluation of a gate list in Kleene's logic.

## Main results

* `Cslib.Circuits.evalCode_rel`: evaluation of gate lists preserves a relation between
  interpretations that the operations preserve.
* `Cslib.Circuits.foldl_eq_evalCode`: a fold reading the arguments of each gate by position is an
  evaluation.
* `Cslib.Circuits.Boolean.Unbounded.kleeneInterpretation_approx`: the three-valued operations
  approximate the Boolean ones.
* `Cslib.Circuits.Boolean.Unbounded.kleeneInterpretation_some`: on known arguments they are the
  Boolean operations.
* `Cslib.Circuits.Boolean.Unbounded.kleeneEval_eq_evalCode`: `kleeneEval` is `evalCode` for
  `kleeneInterpretation` on gates with as many arguments as their arities.
* `Cslib.Circuits.Boolean.Unbounded.approx_kleeneEval`: Kleene evaluation from a partial input
  approximates evaluation on every completion of it.
* `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_kleeneEval`: `kleeneEval` is
  polynomial-time.

## References

* [S. C. Kleene, *Introduction to Metamathematics*, Section 64][Kleene1952]
-/

@[expose] public section

namespace Cslib.Circuits

universe u v

/-- Related lists read related values at every position, given related defaults. -/
private theorem forall₂_getD {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {d₁ : α} {d₂ : β} (hd : R d₁ d₂) (i : ℕ) :
    R (l₁.getD i d₁) (l₂.getD i d₂) := by
  induction h generalizing i with
  | nil => exact hd
  | cons hab _ ih =>
    cases i with
    | zero => exact hab
    | succ i => exact ih i

/-- **Evaluation preserves relations.** If two interpretations take related arguments to related
values, then evaluating a gate list from related inputs, with related defaults, gives related
values at every position. -/
theorem evalCode_rel {σ : Signature.{v}} {U₁ U₂ : Type u} (R : U₁ → U₂ → Prop)
    {I₁ : Interpretation σ U₁} {I₂ : Interpretation σ U₂}
    (hI : ∀ op (a₁ : Fin (σ.Arity op) → U₁) (a₂ : Fin (σ.Arity op) → U₂), (∀ i, R (a₁ i) (a₂ i)) →
      R (I₁ op a₁) (I₂ op a₂))
    {d₁ : U₁} {d₂ : U₂} (hd : R d₁ d₂) {x₁ : List U₁} {x₂ : List U₂} (hx : List.Forall₂ R x₁ x₂)
    (gates : List (σ.Op × List ℕ)) :
    List.Forall₂ R (evalCode I₁ d₁ x₁ gates) (evalCode I₂ d₂ x₂ gates) := by
  induction gates using List.reverseRecOn with
  | nil => exact hx
  | append_singleton gates g ih =>
    rw [evalCode_append_singleton, evalCode_append_singleton]
    refine List.rel_append ih (List.Forall₂.cons (hI _ _ _ fun a => ?_) List.Forall₂.nil)
    rcases g.2[a.val]? with _ | i
    · exact hd
    · exact forall₂_getD ih hd i

/-- Evaluating a gate list keeps the values of the initial wires. -/
theorem getD_evalCode_of_lt {σ : Signature.{v}} {U : Type u} (I : Interpretation σ U) (d : U)
    (x : List U) (gates : List (σ.Op × List ℕ)) {i : ℕ} (hi : i < x.length) :
    (evalCode I d x gates).getD i d = x.getD i d := by
  obtain ⟨t, ht⟩ := prefix_evalCode I d x gates
  rw [← ht, List.getD_append _ _ _ _ hi]

/-- Beyond the initial wires and the gates, evaluation reads the default. -/
theorem getD_evalCode_of_le {σ : Signature.{v}} {U : Type u} (I : Interpretation σ U) (d : U)
    (x : List U) (gates : List (σ.Op × List ℕ)) {i : ℕ} (hi : x.length + gates.length ≤ i) :
    (evalCode I d x gates).getD i d = d :=
  List.getD_eq_default _ _ (by rw [length_evalCode]; exact hi)

/-- Reading the arguments of a gate by position, as a list, is reading them as a function. -/
theorem ofFn_elim_eq_map {σ : Signature.{v}} {U : Type u} (d : U) (values : List U)
    (g : σ.Op × List ℕ) (h : g.2.length = σ.Arity g.1) :
    List.ofFn (fun a : Fin (σ.Arity g.1) => g.2[a.val]?.elim d (values.getD · d)) =
      g.2.map (values.getD · d) := by
  refine List.ext_getElem (by simp [h]) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_ofFn]
  rw [List.getElem?_eq_getElem (by simpa using h₂)]
  rfl

/-- **Folds by position are evaluations.** Appending, for each gate, a function of its operation
and of the values of its arguments read by position is `evalCode` for the interpretation applying
that function to the list of arguments, on gates with as many arguments as their arities. -/
theorem foldl_eq_evalCode {σ : Signature.{v}} {U : Type u} (F : σ.Op → List U → U) (d : U)
    (x : List U) {gates : List (σ.Op × List ℕ)} (h : ∀ g ∈ gates, g.2.length = σ.Arity g.1) :
    gates.foldl (fun values g => values ++ [F g.1 (g.2.map (values.getD · d))]) x =
      evalCode (fun op a => F op (List.ofFn a)) d x gates := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gates ih =>
    rw [List.foldl_cons, ih _ fun g' hg' => h g' (List.mem_cons_of_mem _ hg')]
    change _ = gates.foldl _ (x ++ [F g.1 (List.ofFn fun a => g.2[a.val]?.elim d (x.getD · d))])
    rw [ofFn_elim_eq_map d x g (h g (List.mem_cons_self ..))]
    rfl

/-- **The value of a gate, read as a list.** For an interpretation applying `F` to the list of its
arguments, the value of a gate of a well-formed gate list from `n` inputs is `F` applied to the
values of the arguments of the gate. -/
theorem getD_evalCode_eq_map {σ : Signature.{v}} {U : Type u} {I : Interpretation σ U}
    (F : σ.Op → List U → U) (hI : ∀ op a, I op a = F op (List.ofFn a)) (d : U) {x : List U}
    {n : ℕ} (hx : x.length = n) {gates : List (σ.Op × List ℕ)}
    (h : Program.IsCodeFrom σ n 0 gates) {j : ℕ} {gate : σ.Op × List ℕ}
    (hg : gates[j]? = some gate) :
    (evalCode I d x gates).getD (n + j) d =
      F gate.1 (gate.2.map ((evalCode I d x gates).getD · d)) := by
  subst hx
  rw [getD_evalCode I d x h hg, hI]
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  rw [ofFn_elim_eq_map d _ _ (h.getElem j hj).1]

namespace Boolean.Unbounded

open Turing.MultiTapeTM

/-! ### Kleene's three-valued logic -/

/-- `a` is unknown, or it is `b`: the option `a` approximates the Boolean `b`. -/
def Approx (a : Option Bool) (b : Bool) : Prop :=
  ∀ c ∈ a, c = b

@[simp] theorem approx_none (b : Bool) : Approx none b := fun _ h => nomatch h

@[simp] theorem approx_some {c b : Bool} : Approx (some c) b ↔ c = b :=
  ⟨fun h => h c rfl, fun h _ hc => Option.some_inj.1 hc ▸ h⟩

/-- Kleene conjunction: false when an argument is false, true when all are true, and unknown
otherwise. -/
def kleeneAnd (l : List (Option Bool)) : Option Bool :=
  if some false ∈ l then some false else if l.all (· == some true) then some true else none

/-- Kleene disjunction: true when an argument is true, false when all are false, and unknown
otherwise. -/
def kleeneOr (l : List (Option Bool)) : Option Bool :=
  if some true ∈ l then some true else if l.all (· == some false) then some false else none

/-- An operation in Kleene's logic, on a list of arguments. -/
def kleeneOp : Op → List (Option Bool) → Option Bool
  | .not, l => (l.headD none).map (!·)
  | .and _, l => kleeneAnd l
  | .or _, l => kleeneOr l

/-- **The operations in Kleene's logic**, as an interpretation of the unbounded fan-in basis. -/
def kleeneInterpretation : Interpretation signature (Option Bool) :=
  fun op a => kleeneOp op (List.ofFn a)

/-- A known false argument makes a Kleene conjunction false. -/
theorem kleeneAnd_of_mem {l : List (Option Bool)} (h : some false ∈ l) :
    kleeneAnd l = some false := by
  simp [kleeneAnd, h]

/-- A known true argument makes a Kleene disjunction true. -/
theorem kleeneOr_of_mem {l : List (Option Bool)} (h : some true ∈ l) :
    kleeneOr l = some true := by
  simp [kleeneOr, h]

private theorem all_ofFn_beq {m : ℕ} (f : Fin m → Option Bool) (c : Option Bool) :
    (List.ofFn f).all (· == c) = true ↔ ∀ i, f i = c := by
  simp [List.all_eq_true, List.mem_ofFn]

/-- **Kleene's operations approximate the Boolean operations**: on arguments approximating Boolean
arguments, they give a value approximating the Boolean value. -/
theorem kleeneInterpretation_approx (op : Op) (a : Fin (signature.Arity op) → Option Bool)
    (b : Fin (signature.Arity op) → Bool) (h : ∀ i, Approx (a i) (b i)) :
    Approx (kleeneInterpretation op a) (interpretation op b) := by
  intro c hc
  cases op with
  | not =>
    simp only [kleeneInterpretation, kleeneOp, List.ofFn_succ, List.ofFn_zero, List.headD_cons,
      Option.mem_def, Option.map_eq_some_iff] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    simp [h 0 c' hc']
  | and m =>
    simp only [kleeneInterpretation, kleeneOp, kleeneAnd, List.mem_ofFn] at hc
    split_ifs at hc with h₁ h₂
    · obtain ⟨i, hi⟩ := h₁
      cases hc
      rw [interpretation_and, eq_comm, decide_eq_false_iff_not]
      exact fun hall => Bool.false_ne_true ((h i false hi).trans (hall i))
    · cases hc
      rw [all_ofFn_beq] at h₂
      rw [interpretation_and, eq_comm, decide_eq_true_iff]
      exact fun i => (h i true (h₂ i)).symm
    · cases hc
  | or m =>
    simp only [kleeneInterpretation, kleeneOp, kleeneOr, List.mem_ofFn] at hc
    split_ifs at hc with h₁ h₂
    · obtain ⟨i, hi⟩ := h₁
      cases hc
      rw [interpretation_or, eq_comm, decide_eq_true_iff]
      exact ⟨i, (h i true hi).symm⟩
    · cases hc
      rw [all_ofFn_beq] at h₂
      rw [interpretation_or, eq_comm, decide_eq_false_iff_not, not_exists]
      exact fun i hi => Bool.false_ne_true ((h i false (h₂ i)).trans hi)
    · cases hc

/-- **On known arguments, Kleene's operations are the Boolean operations.** -/
theorem kleeneInterpretation_some (op : Op) (b : Fin (signature.Arity op) → Bool) :
    kleeneInterpretation op (fun i => some (b i)) = some (interpretation op b) := by
  cases op with
  | not => simp [kleeneInterpretation, kleeneOp, List.ofFn_succ]
  | and m =>
    by_cases h : ∀ i, b i = true
    · simp [kleeneInterpretation, kleeneOp, kleeneAnd, h]
    · obtain ⟨i, hi⟩ := not_forall.1 h
      have hmem : some false ∈ List.ofFn (fun i => some (b i)) :=
        List.mem_ofFn.2 ⟨i, by simpa using hi⟩
      simp only [kleeneInterpretation, kleeneOp, kleeneAnd_of_mem hmem, interpretation_and]
      simp [h]
  | or m =>
    by_cases h : ∃ i, b i = true
    · obtain ⟨i, hi⟩ := h
      have hmem : some true ∈ List.ofFn (fun i => some (b i)) :=
        List.mem_ofFn.2 ⟨i, by simp [hi]⟩
      simp only [kleeneInterpretation, kleeneOp, kleeneOr_of_mem hmem, interpretation_or]
      exact congrArg some (decide_eq_true ⟨i, hi⟩).symm
    · simp only [not_exists, Bool.not_eq_true] at h
      simp [kleeneInterpretation, kleeneOp, kleeneOr, h]

/-! ### Evaluating gate lists -/

/-- One step of `kleeneEval`: append the value of a gate, reading its arguments by position. -/
def kleeneStep (values : List (Option Bool)) (g : Op × List ℕ) : List (Option Bool) :=
  values ++ [kleeneOp g.1 (g.2.map (values.getD · none))]

/-- **Evaluation of a gate list in Kleene's logic**: start from the input values and append the
value of each gate in turn. -/
def kleeneEval (ρ : List (Option Bool)) (gates : List (Op × List ℕ)) : List (Option Bool) :=
  gates.foldl kleeneStep ρ

/-- On gates with as many arguments as their arities, `kleeneEval` is `evalCode` for
`kleeneInterpretation`, with unknown values for missing wires. -/
theorem kleeneEval_eq_evalCode (ρ : List (Option Bool)) {gates : List (Op × List ℕ)}
    (h : ∀ g ∈ gates, g.2.length = g.1.arity) :
    kleeneEval ρ gates = evalCode kleeneInterpretation none ρ gates :=
  foldl_eq_evalCode (σ := signature) kleeneOp none ρ h

/-- The gates of the code of a program have as many arguments as their arities. -/
theorem length_eq_arity_of_isCodeFrom {n k : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n k gates) : ∀ g ∈ gates, g.2.length = g.1.arity := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  exact (h.getElem j hj).1

/-- **Kleene evaluation approximates Boolean evaluation**: from input values approximating
Boolean inputs, every value that Kleene evaluation knows is the Boolean value. -/
theorem approx_kleeneEval {ρ : List (Option Bool)} {x : List Bool} (hx : List.Forall₂ Approx ρ x)
    {gates : List (Op × List ℕ)} (h : ∀ g ∈ gates, g.2.length = g.1.arity) (i : ℕ) :
    Approx ((kleeneEval ρ gates).getD i none)
      ((evalCode interpretation false x gates).getD i false) := by
  rw [kleeneEval_eq_evalCode ρ h]
  exact forall₂_getD (evalCode_rel (σ := signature) Approx kleeneInterpretation_approx
    (approx_none false) hx gates) (approx_none false) i

/-- Kleene evaluation adds one value per gate. -/
@[simp] theorem length_kleeneEval (ρ : List (Option Bool)) (gates : List (Op × List ℕ)) :
    (kleeneEval ρ gates).length = ρ.length + gates.length := by
  induction gates generalizing ρ with
  | nil => rfl
  | cons g gates ih =>
    change (kleeneEval (kleeneStep ρ g) gates).length = _
    rw [ih, kleeneStep, List.length_append, List.length_singleton, List.length_cons]
    omega

/-- Kleene evaluation keeps the input values. -/
theorem getD_kleeneEval_of_lt (ρ : List (Option Bool)) (gates : List (Op × List ℕ)) {i : ℕ}
    (hi : i < ρ.length) : (kleeneEval ρ gates).getD i none = ρ.getD i none := by
  induction gates generalizing ρ with
  | nil => rfl
  | cons g gates ih =>
    change (kleeneEval (kleeneStep ρ g) gates).getD i none = _
    rw [ih _ (by simp only [kleeneStep, List.length_append, List.length_singleton]; omega),
      kleeneStep, List.getD_append _ _ _ _ hi]

/-- On known arguments, as many as the arity, a Kleene operation is known. -/
theorem kleeneOp_map_some_ne_none (op : Op) {l : List Bool} (hl : l.length = op.arity) :
    kleeneOp op (l.map some) ≠ none := by
  cases op with
  | not =>
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 hl
    simp [kleeneOp]
  | and m =>
    simp only [kleeneOp, kleeneAnd]
    split_ifs <;> simp_all
  | or m =>
    simp only [kleeneOp, kleeneOr]
    split_ifs <;> simp_all

/-- **The Kleene value of a gate** of a well-formed gate list is its operation applied to the
values of its arguments. -/
theorem getD_kleeneEval_add {ρ : List (Option Bool)} {n : ℕ} (hρ : ρ.length = n)
    {gates : List (Op × List ℕ)} (h : Program.IsCodeFrom signature n 0 gates) {j : ℕ}
    {gate : Op × List ℕ} (hg : gates[j]? = some gate) :
    (kleeneEval ρ gates).getD (n + j) none =
      kleeneOp gate.1 (gate.2.map ((kleeneEval ρ gates).getD · none)) := by
  rw [kleeneEval_eq_evalCode ρ (length_eq_arity_of_isCodeFrom h)]
  exact getD_evalCode_eq_map (σ := signature) kleeneOp (fun _ _ => rfl) none hρ h hg

/-! ### Polynomial time -/

/-- `kleeneOp` by the number of the operation: `0` for negation, odd for conjunction. -/
private theorem kleeneOp_eq_ite (op : Op) (l : List (Option Bool)) :
    kleeneOp op l = if op.toNat == 0 then (l.headD none).map (!·)
      else if op.toNat % 2 == 1 then kleeneAnd l else kleeneOr l := by
  cases op with
  | not => rfl
  | and m => simp [Op.toNat, kleeneOp]
  | or m => simp [Op.toNat, kleeneOp]

private theorem computableInPolyTime_kleeneAnd :
    ComputableInPolyTime kleeneAnd (encList (encOption encBool)) (encOption encBool) := by
  unfold kleeneAnd
  fun_prop

private theorem computableInPolyTime_kleeneOr :
    ComputableInPolyTime kleeneOr (encList (encOption encBool)) (encOption encBool) := by
  unfold kleeneOr
  fun_prop

private theorem computableInPolyTime_kleeneStep :
    ComputableInPolyTime (fun p : List (Option Bool) × (Op × List ℕ) => kleeneStep p.1 p.2)
      (encPair (encList (encOption encBool)) (Circuit.encGate encOp))
      (encList (encOption encBool)) := by
  have hp := ComputableInPolyTime.id' (encIn :=
    encPair (encList (encOption encBool)) (Circuit.encGate encOp))
  have hvals := hp.fst'
  have hop : ComputableInPolyTime (fun p : List (Option Bool) × (Op × List ℕ) => p.2.1.toNat)
      (encPair (encList (encOption encBool)) (Circuit.encGate encOp)) encUnary :=
    hp.snd'.fst'.of_enc_eq fun _ => rfl
  have hargs : ComputableInPolyTime
      (fun p : List (Option Bool) × (Op × List ℕ) => p.2.2.map (p.1.getD · none))
      (encPair (encList (encOption encBool)) (Circuit.encGate encOp))
      (encList (encOption encBool)) := by
    refine ComputableInPolyTime.mapWithInput hp.snd'.snd' ?_
    have hq := ComputableInPolyTime.id' (encIn :=
      encPair (encPair (encList (encOption encBool)) (Circuit.encGate encOp)) encNat)
    exact ComputableInPolyTime.listGetD_binary (encA := encOption encBool) none hq.fst'.fst'
      hq.snd'
  have hand := computableInPolyTime_kleeneAnd.comp hargs
  have hor := computableInPolyTime_kleeneOr.comp hargs
  have hnot : ComputableInPolyTime
      (fun p : List (Option Bool) × (Op × List ℕ) =>
        ((p.2.2.map (p.1.getD · none)).headD none).map (!·))
      (encPair (encList (encOption encBool)) (Circuit.encGate encOp)) (encOption encBool) :=
    (ComputableInPolyTime.of_finite (fun a : Option Bool => a.map (!·))).comp
      ((ComputableInPolyTime.headD (encA := encOption encBool)
        (encL := encList (encOption encBool)) none).comp hargs)
  have hzero : ComputableInPolyTime
      (fun p : List (Option Bool) × (Op × List ℕ) => p.2.1.toNat == 0)
      (encPair (encList (encOption encBool)) (Circuit.encGate encOp)) encBool :=
    ComputableInPolyTime.unary_beq' hop (ComputableInPolyTime.const 0)
  have hodd : ComputableInPolyTime
      (fun p : List (Option Bool) × (Op × List ℕ) => p.2.1.toNat % 2 == 1)
      (encPair (encList (encOption encBool)) (Circuit.encGate encOp)) encBool :=
    ComputableInPolyTime.unary_beq' (ComputableInPolyTime.unary_mod.comp
      (hop.prod (ComputableInPolyTime.const 2))) (ComputableInPolyTime.const 1)
  have hval : ComputableInPolyTime
      (fun p : List (Option Bool) × (Op × List ℕ) => kleeneOp p.2.1 (p.2.2.map (p.1.getD · none)))
      (encPair (encList (encOption encBool)) (Circuit.encGate encOp)) (encOption encBool) := by
    simp only [kleeneOp_eq_ite]
    exact ComputableInPolyTime.ite' hzero hnot (ComputableInPolyTime.ite' hodd hand hor)
  exact ComputableInPolyTime.listAppend' hvals
    (ComputableInPolyTime.cons' hval (ComputableInPolyTime.const []))

/-- **Kleene evaluation is polynomial-time**, for input values and gates computed in polynomial
time. -/
@[fun_prop]
theorem computableInPolyTime_kleeneEval {γ : Type} {encIn : γ ↪ List Bool}
    {ρ : γ → List (Option Bool)} {gates : γ → List (Op × List ℕ)}
    (hρ : ComputableInPolyTime ρ encIn (encList (encOption encBool)))
    (hgates : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp))) :
    ComputableInPolyTime (fun a => kleeneEval (ρ a) (gates a)) encIn
      (encList (encOption encBool)) :=
  ComputableInPolyTime.foldl_of_bounded_growth hgates hρ computableInPolyTime_kleeneStep
    (growth := 7) fun values g => by
      simp only [kleeneStep, encList_append, List.length_append, encList_cons, encList_nil,
        List.append_nil, length_frame]
      rcases kleeneOp g.1 (g.2.map (values.getD · none)) with _ | b <;> simp

end Boolean.Unbounded

end Cslib.Circuits
