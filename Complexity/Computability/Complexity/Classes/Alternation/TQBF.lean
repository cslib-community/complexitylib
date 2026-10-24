/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Alternation.Game
public import Complexity.Computability.Complexity.Classes.Space.TQBF
public import Complexity.Computability.Complexity.Classes.Space.TQBF.Reduction
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.Space.TQBF.PolyTime
import Complexity.Computability.Complexity.CookLevin.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Games of polynomially many moves reduce to `TQBF`

A game of `2 * w` alternate single-bit moves, the existential first, whose winning condition is
computed by a polynomial-time machine, is a closed quantified Boolean formula: rounds of
quantifiers `∃ x, ∀ y` over the moves (`Cslib.Logic.PL.QBF.rounds`,
`Cslib.Logic.PL.QBF.eval_rounds_eq_true_iff`), followed by the Cook–Levin tableau of the machine
on the instance and the moves, its certificate bits linked to the variables of the moves and all
its other variables quantified existentially. The variables of the moves are the blocks of level
`0` of the reduction of `Cslib.Computability.Complexity.Classes.Space.TQBF.Reduction`, and the
tableau is its formula of level `0` (`Cslib.Complexity.TQBF.baseFormula`), so the formula of a game
(`Cslib.Complexity.TQBF.gameFormula`) holds exactly when the existential player wins the game in
which the tableau has a satisfying assignment with the moves as certificate
(`Cslib.Complexity.TQBF.eval_gameFormula`).

For a polynomial-time game verifier, the formula of the game on an instance
(`Cslib.Complexity.TQBF.gameReduce`) is computed in polynomial time and is a true closed formula
exactly when the instance is accepted (`Cslib.Complexity.TQBF.gameReduce_mem_TQBF_iff`). Since
`TQBF` is in `PSPACE` and `PSPACE` is closed under polynomial-time reductions, every problem with a
polynomial-time game verifier is in `PSPACE` (`Cslib.Complexity.IsGameVerifier.mem_PSPACE`), and
in particular every problem in `AP` (`Cslib.Complexity.AP_subset_PSPACE`): the inclusion
`AP ⊆ PSPACE` [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013].

## Main definitions

* `Cslib.Logic.PL.QBF.rounds`: rounds of quantifiers `∃ x, ∀ y`.
* `Cslib.Logic.PL.QBF.updates`: an assignment updated along a list of variables.
* `Cslib.Complexity.TQBF.gameFormula`: the formula of a game on a tableau.
* `Cslib.Complexity.TQBF.gameReduce`: the reduction of a game verifier to `TQBF`.

## Main results

* `Cslib.Logic.PL.QBF.eval_rounds_eq_true_iff`: rounds of quantifiers are a game of moves.
* `Cslib.Logic.PL.QBF.rounds_append`, `Cslib.Logic.PL.QBF.eval_rounds_congr`,
  `Cslib.Logic.PL.QBF.eval_exs_congr`: rounds and blocks of quantifiers.
* `Cslib.Logic.PL.QBF.eval_rounds_map_pair`: universal quantifiers over a variable that does not
  occur are vacuous.
* `Cslib.Logic.PL.QBF.length_roundVars`, `Cslib.Logic.PL.QBF.closed_rounds_ofCNF_iff`: the
  variables of rounds, and closed formulas in alternating prenex conjunctive normal form.
* `Cslib.Complexity.TQBF.eval_gameFormula`, `Cslib.Complexity.TQBF.closed_gameFormula`: the
  formula of a game.
* `Cslib.Complexity.TQBF.gameReduce_mem_TQBF_iff`,
  `Cslib.Complexity.TQBF.computableInPolyTime_gameReduce`: the reduction is correct and
  polynomial-time.
* `Cslib.Complexity.IsGameVerifier.mem_PSPACE`: games of polynomially many moves with a
  polynomial-time winning condition are decided in polynomial space.
* `Cslib.Complexity.AP_subset_PSPACE`: `AP ⊆ PSPACE`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL.QBF

variable {V : Type*}

/-! ### Rounds of quantifiers -/

/-- Rounds of quantifiers: `∃ x, ∀ y` for each pair `(x, y)`, the first pair outermost. -/
def rounds (ps : List (V × V)) (φ : QBF V) : QBF V :=
  ps.foldr (fun p ψ => ex p.1 (all p.2 ψ)) φ

/-- The variables of rounds of quantifiers, in order. -/
def roundVars (ps : List (V × V)) : List V :=
  ps.flatMap fun p => [p.1, p.2]

/-- The tokens of rounds of quantifiers. -/
theorem tokens_rounds (ps : List (ℕ × ℕ)) (φ : QBF ℕ) :
    (rounds ps φ).tokens = ps.flatMap (fun p => [(Kind.ex, p.1), (Kind.all, p.2)]) ++ φ.tokens := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [rounds, List.foldr_cons] at ih ⊢
    simp [tokens, ih]

/-- Rounds of quantifiers over a concatenation of lists nest. -/
theorem rounds_append (ps qs : List (V × V)) (φ : QBF V) :
    rounds (ps ++ qs) φ = rounds ps (rounds qs φ) :=
  List.foldr_append ..

/-- Rounds of quantifiers quantify two variables each. -/
theorem length_roundVars (ps : List (V × V)) : (roundVars ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [roundVars, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

variable [DecidableEq V]

/-- An assignment updated at a list of variables, in order, by a list of values. -/
def updates (σ : V → Bool) : List V → List Bool → V → Bool
  | v :: vs, b :: bs => updates (Function.update σ v b) vs bs
  | _, _ => σ

/-- Updating other variables does not change the value of a variable. -/
theorem updates_of_notMem {σ : V → Bool} {vs : List V} {x : V} (hx : x ∉ vs) (bs : List Bool) :
    updates σ vs bs x = σ x := by
  induction vs generalizing σ bs with
  | nil => cases bs <;> rfl
  | cons v vs ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [List.mem_cons, not_or] at hx
      rw [updates, ih hx.2, Function.update_of_ne hx.1]

/-- Updating distinct variables by as many values sets them to these values. -/
private theorem map_updates {σ : V → Bool} {vs : List V} (hvs : vs.Nodup) {bs : List Bool}
    (hlen : bs.length = vs.length) : vs.map (updates σ vs bs) = bs := by
  induction vs generalizing σ bs with
  | nil => exact (List.length_eq_zero_iff.mp hlen).symm
  | cons v vs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      rw [List.nodup_cons] at hvs
      rw [List.map_cons, updates, updates_of_notMem hvs.1, Function.update_self,
        ih hvs.2 (by simpa using hlen)]

/-- **Rounds of quantifiers are a game** of alternate single-bit moves, the existential first: the
formula holds exactly when the existential player wins the game in which the moves set the
variables of the rounds, in order. -/
theorem eval_rounds_eq_true_iff (ps : List (V × V)) (φ : QBF V) (σ : V → Bool) :
    (rounds ps φ).eval σ = true ↔ Complexity.Alternation true (List.replicate (2 * ps.length) 1)
      fun z => φ.eval (updates σ (roundVars ps) z) = true := by
  induction ps generalizing σ with
  | nil => simp [rounds, roundVars, updates]
  | cons p ps ih =>
    rw [List.length_cons, Complexity.alternation_replicate_succ]
    simp only [rounds, List.foldr_cons, eval_ex_eq_true_iff, eval_all_eq_true_iff]
    simp only [rounds] at ih
    simp only [ih]
    rfl

/-- The free variables of rounds of quantifiers are those of the body not quantified. -/
theorem mem_freeVars_rounds {ps : List (V × V)} {φ : QBF V} {x : V} :
    x ∈ (rounds ps φ).freeVars ↔ x ∈ φ.freeVars ∧ x ∉ roundVars ps := by
  induction ps with
  | nil => simp [rounds, roundVars]
  | cons p ps ih =>
    simp only [rounds, List.foldr_cons] at ih ⊢
    simp only [freeVars_ex, freeVars_all, Finset.mem_erase, ih, roundVars, List.flatMap_cons,
      List.cons_append, List.nil_append, List.mem_cons, not_or]
    tauto

/-- Rounds of quantifiers over formulas with the same values have the same values. -/
theorem eval_rounds_congr {φ ψ : QBF V} (h : ∀ σ, φ.eval σ = ψ.eval σ) (ps : List (V × V))
    (σ : V → Bool) : (rounds ps φ).eval σ = (rounds ps ψ).eval σ := by
  induction ps generalizing σ with
  | nil => exact h σ
  | cons p ps ih => simp only [rounds, List.foldr_cons] at ih ⊢; simp only [eval_ex, eval_all, ih]

/-- Existential quantifiers over formulas with the same values have the same values. -/
theorem eval_exs_congr {φ ψ : QBF V} (h : ∀ σ, φ.eval σ = ψ.eval σ) (vs : List V)
    (σ : V → Bool) : (exs vs φ).eval σ = (exs vs ψ).eval σ := by
  induction vs generalizing σ with
  | nil => exact h σ
  | cons v vs ih => simp only [exs, List.foldr_cons] at ih ⊢; simp only [eval_ex, ih]

/-- **Vacuous universal quantifiers**: the rounds `∃ v, ∀ d` for the variables `v` of a list, over
a variable `d` that is not free in the body, are existential quantifiers over the list. -/
theorem eval_rounds_map_pair {φ : QBF V} {d : V} (hd : d ∉ φ.freeVars) (vs : List V)
    (σ : V → Bool) : (rounds (vs.map fun v => (v, d)) φ).eval σ = (exs vs φ).eval σ := by
  induction vs generalizing σ with
  | nil => rfl
  | cons v vs ih =>
    have hd' : d ∉ (rounds (vs.map fun v => (v, d)) φ).freeVars := fun h =>
      hd (mem_freeVars_rounds.1 h).1
    change (ex v (all d (rounds (vs.map fun v => (v, d)) φ))).eval σ = (ex v (exs vs φ)).eval σ
    simp only [eval_ex, eval_all_of_notMem_freeVars hd', ih]

/-- A formula in alternating prenex conjunctive normal form is closed exactly when all the
variables of its clauses are quantified. -/
theorem closed_rounds_ofCNF_iff (ps : List (V × V)) (ψ : CNF V) :
    (rounds ps (ofCNF ψ)).Closed ↔ ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ roundVars ps := by
  rw [Closed, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_freeVars_rounds, mem_freeVars_ofCNF, CNF.vars, List.mem_map,
    List.mem_flatten, not_and, not_not]
  constructor
  · intro h c hc l hl
    exact h _ ⟨l, ⟨c, hc, hl⟩, rfl⟩
  · rintro h _ ⟨l, ⟨c, hc, hl⟩, rfl⟩
    exact h c hc l hl

end Cslib.Logic.PL.QBF

namespace Cslib.Complexity.TQBF

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL

/-! ### The formula of a game -/

/-- Pairs of values of a function at consecutive even and odd numbers list its values. -/
private theorem flatMap_range_pairs (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map fun i => (f (2 * i), f (2 * i + 1))).flatMap (fun p => [p.1, p.2]) =
      (List.range (2 * n)).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, ih,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ]
    simp

/-- The rounds of a game of `2 * w` moves: the move `j` sets the variable `certVar w j` of the
blocks of level `0`. -/
def gamePairs (w : ℕ) : List (ℕ × ℕ) :=
  (List.range w).map fun i => (certVar w (2 * i), certVar w (2 * i + 1))

private theorem length_gamePairs (w : ℕ) : (gamePairs w).length = w := by
  simp [gamePairs]

/-- The variables of the moves are those of the blocks of level `0`. -/
theorem roundVars_gamePairs (w : ℕ) :
    QBF.roundVars (gamePairs w) = blockVars w 0 0 ++ blockVars w 1 0 := by
  rw [QBF.roundVars, gamePairs, flatMap_range_pairs, two_mul, List.range_add, List.map_append,
    List.map_map]
  congr 1
  · refine List.map_congr_left fun j hj => ?_
    simp [certVar, List.mem_range.mp hj]
  · refine List.map_congr_left fun j _ => ?_
    simp [certVar]

/-- **The formula of a game** on a tableau: rounds of quantifiers over the blocks of level `0`,
then the tableau as the formula of level `0`. -/
noncomputable def gameFormula {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : ℕ) : QBF ℕ :=
  QBF.rounds (gamePairs w) (baseFormula tab w)

section GameFormula

variable {k : ℕ} {State : Type} [Fintype State]

/-- **The formula of a game holds** exactly when the existential player wins the game of `2 * w`
moves in which the tableau has a satisfying assignment with the moves as its first `2 * w`
certificate bits. -/
theorem eval_gameFormula (tab : CNF (CookLevin.Var k State)) (w : ℕ) (σ : ℕ → Bool) :
    (gameFormula tab w).eval σ = true ↔ Alternation true (List.replicate (2 * w) 1)
      fun z => ∃ τ : CookLevin.Var k State → Bool,
        CookLevin.certWord τ (2 * w) = z ∧ tab.eval τ = true := by
  rw [gameFormula, QBF.eval_rounds_eq_true_iff, length_gamePairs]
  refine alternation_congr_of_length fun z hz => ?_
  rw [sum_replicate_one] at hz
  rw [eval_baseFormula]
  have hblocks : block (QBF.updates σ (QBF.roundVars (gamePairs w)) z) w 0 0 ++
      block (QBF.updates σ (QBF.roundVars (gamePairs w)) z) w 1 0 = z := by
    rw [block, block, ← List.map_append, ← roundVars_gamePairs]
    exact QBF.map_updates (roundVars_gamePairs w ▸ nodup_blockVars_append w 0)
      (by rw [hz, roundVars_gamePairs, List.length_append, blockVars, blockVars, List.length_map,
        List.length_map, List.length_range, two_mul])
  rw [hblocks]

/-- The formula of a game is closed. -/
theorem closed_gameFormula (tab : CNF (CookLevin.Var k State)) (w : ℕ) :
    (gameFormula tab w).Closed := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
  rw [gameFormula, QBF.mem_freeVars_rounds, roundVars_gamePairs, List.mem_append] at hx
  exact hx.2 (mem_freeVars_baseFormula tab w x hx.1)

end GameFormula

/-! ### The reduction -/

section Reduction

variable {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ)

/-- **The reduction of a game to `TQBF`**: the formula of the game of `2 * p (enc a).length` moves
on the Cook–Levin tableau of a machine `tmV`, on the input `frame (enc a)` and the moves, unrolled
for `cV * (2 * (enc a).length + 2 * p (enc a).length + 2) ^ dV` steps. -/
noncomputable def gameReduce {kV : ℕ} {StateV : Type} [Fintype StateV] [DecidableEq StateV]
    (tmV : MultiTapeTM kV Bool StateV) (cV dV : ℕ) (a : α) : QBF ℕ :=
  gameFormula (CookLevin.tableau tmV (frame (enc a)) (2 * p.eval (enc a).length)
    (cV * (2 * (enc a).length + 2 * p.eval (enc a).length + 2) ^ dV)) (p.eval (enc a).length)

variable {enc p}

/-- **The reduction of a game is correct.** If `tmV` computes the winning condition `V` tidily
within time `cV * (n + 1) ^ dV`, then the formula of the game on `a` is a true closed formula
exactly when the existential player wins the game of `2 * p (enc a).length` moves with winning
condition `V (a, ·)`. -/
theorem gameReduce_mem_TQBF_iff {V : α × List Bool → Bool} {kV : ℕ} {StateV : Type}
    [Fintype StateV] [DecidableEq StateV] {tmV : MultiTapeTM kV Bool StateV} {cV dV : ℕ}
    {sV : α × List Bool → ℕ}
    (htm : tmV.ComputesFunTidilyInTimeAndSpace (encPair enc encBits) encBool V
      (fun x => cV * ((encPair enc encBits x).length + 1) ^ dV) sV) (a : α) :
    gameReduce enc p tmV cV dV a ∈ TQBF ↔
      Alternation true (List.replicate (2 * p.eval (enc a).length) 1) fun z => V (a, z) = true := by
  set w := p.eval (enc a).length
  rw [gameReduce, mem_TQBF_iff_of_closed (closed_gameFormula _ _) (fun _ => false),
    eval_gameFormula]
  refine alternation_congr_of_length fun z hz => ?_
  rw [sum_replicate_one] at hz
  have hrun := (htm (a, z)).runFrom_initCfg
  have hlen : (encPair enc encBits (a, z)).length = 2 * (enc a).length + 2 * w + 1 := by
    rw [length_encPair, encBits_apply, hz]
    dsimp only
    omega
  dsimp only at hrun
  rw [hlen, encPair_apply, encBits_apply] at hrun
  have htab := CookLevin.exists_eval_tableau_iff (tm := tmV) (u := frame (enc a))
    (T := cV * (2 * (enc a).length + 2 * w + 2) ^ dV) (z := z)
  rw [hz] at htab
  rw [htab, show 2 * (enc a).length + 2 * w + 2 = 2 * (enc a).length + 2 * w + 1 + 1 by ring,
    hrun.2]
  simp only [encBool_apply, List.cons.injEq, and_true]
  exact ⟨fun h => h.2, fun h => ⟨hrun.1, h⟩⟩

/-- The tokens of a round of the game. -/
def roundTokens (w i : ℕ) : List (QBF.Kind × ℕ) :=
  [(.ex, certVar w (2 * i))] ++ [(.all, certVar w (2 * i + 1))]

private theorem tokens_gameFormula {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : ℕ) :
    (gameFormula tab w).tokens = (List.range w).flatMap (roundTokens w) ++
      (baseFormula tab w).tokens := by
  rw [gameFormula, QBF.tokens_rounds, gamePairs, List.flatMap_map]
  rfl

section PolyTime

open ComputableTidilyInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- The tokens of a round, from the width and the round in unary. -/
@[fun_prop]
theorem computableInPolyTime_roundTokens {w i : γ → ℕ}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hi : Turing.MultiTapeTM.ComputableInPolyTime i encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => roundTokens (w x) (i x)) encIn
      (encList encToken) := by
  unfold roundTokens
  fun_prop

/-- **The formula of a game is polynomial-time** in the tableau and the number of rounds in
unary. -/
@[fun_prop]
theorem computableInPolyTime_gameFormula {k : ℕ} {State : Type} [Fintype State]
    {tab : γ → CNF (CookLevin.Var k State)} {w : γ → ℕ}
    (htab : Turing.MultiTapeTM.ComputableInPolyTime tab encIn
      (encList (encList (encPair CookLevin.encVar encBool))))
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => gameFormula (tab x) (w x)) encIn encQBF :=
  computableInPolyTime_of_tokens
    (l := fun x => (List.range (w x)).flatMap (roundTokens (w x)) ++
      (baseFormula (tab x) (w x)).tokens) (by fun_prop) fun _ => tokens_gameFormula ..

@[local fun_prop]
private theorem computableTidilyInPolyTime_gameFormula
    {k : ℕ} {State : Type} [Fintype State]
    {tab : γ → CNF (CookLevin.Var k State)} {w : γ → ℕ}
    (htab : ComputableTidilyInPolyTime tab encIn
      (encList (encList (encPair CookLevin.encVar encBool))))
    (hw : ComputableTidilyInPolyTime w encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => gameFormula (tab x) (w x)) encIn encQBF :=
  (ComputableInPolyTime.tidy (computableInPolyTime_gameFormula (.of_tidy htab) (.of_tidy hw)))

/-- **The reduction of a game is polynomial-time.** -/
theorem computableInPolyTime_gameReduce {kV : ℕ} {StateV : Type} [Fintype StateV]
    [DecidableEq StateV] (tmV : MultiTapeTM kV Bool StateV) (cV dV : ℕ) :
    Turing.MultiTapeTM.ComputableInPolyTime (gameReduce enc p tmV cV dV) enc encQBF := by
  have htab := CookLevin.computableInPolyTime_tableau tmV
  have hframe := Turing.MultiTapeTM.ComputableInPolyTime.bitsFrame enc
  have hp : Turing.MultiTapeTM.ComputableInPolyTime (fun a => p.eval (enc a).length) enc encUnary :=
    (Turing.MultiTapeTM.ComputableInPolyTime.unary_eval p).comp
      (Turing.MultiTapeTM.ComputableInPolyTime.encoding_length enc)
  unfold gameReduce
  fun_prop

end PolyTime

end Reduction

end Cslib.Complexity.TQBF

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
  {A : Set α}

/-- **Games with a polynomial-time winning condition reduce to `TQBF`.** -/
private theorem IsGameVerifier.polyTimeReducible
    (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool)
    (h : IsGameVerifier enc p V A) : PolyTimeReducible enc encQBF A TQBF := by
  obtain ⟨tV, sV, htV, -, kV, StateV, hfiniteV, tmV, htmV⟩ := hV
  obtain ⟨cV, dV, htV⟩ := htV.exists_le
  have := Fintype.ofFinite StateV
  classical
  exact ⟨TQBF.gameReduce enc p tmV cV dV,
    (TQBF.computableInPolyTime_gameReduce tmV cV dV),
    fun a => (h a).trans (TQBF.gameReduce_mem_TQBF_iff (htmV.mono htV fun _ => le_rfl) a).symm⟩

/-- **Games of polynomially many moves are decided in polynomial space**: a problem with a
polynomial-time game verifier is in `PSPACE`. -/
theorem IsGameVerifier.mem_PSPACE
    (hV : Turing.MultiTapeTM.ComputableInPolyTime V (encPair enc encBits) encBool)
    (h : IsGameVerifier enc p V A) : A ∈ PSPACE enc := by
  have hV := hV.tidy
  exact (h.polyTimeReducible hV).mem_PSPACE TQBF_mem_PSPACE

/-- **`AP ⊆ PSPACE`** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: a problem decided by an alternating machine within polynomial
time is a game of polynomially many moves with a polynomial-time winning condition, which reduces
to `TQBF`. -/
theorem AP_subset_PSPACE : AP enc ⊆ PSPACE enc := fun _ hA =>
  let ⟨_, _, hV, h⟩ := exists_isGameVerifier_of_mem_AP hA
  h.mem_PSPACE hV

end Cslib.Complexity
