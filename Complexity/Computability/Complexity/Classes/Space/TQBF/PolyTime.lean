/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space.TQBF.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Complexity.CookLevin.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# The reduction to `TQBF` in polynomial time

A formula is encoded by the list of its tokens in prefix order (`Cslib.Complexity.encQBF`), so a
formula is computed in polynomial time as soon as its tokens are
(`Cslib.Complexity.TQBF.computableInPolyTime_of_tokens`). The connectives of
`Cslib.Logic.PL.QBF` and the derived connectives of the midpoint formulas (blocks of quantifiers,
conjunctions of lists, implication, equivalence, literals, formulas in conjunctive normal form) get
composition rules for `fun_prop`, with their tokens written out explicitly
(`Cslib.Logic.PL.QBF.tokens_exs`, `Cslib.Logic.PL.QBF.tokens_conj`, …).

The variables of the blocks are numbered by `2 * Nat.pair (3 * i + kind) j` for a level `i` and an
index `j` below the width `w`, so they are computed in unary, where their size is polynomial in
`w`, and converted to binary. The midpoint formula of level `d` is computed from its tokens
(`Cslib.Complexity.TQBF.tokens_midpoint`): the levels from `d` down to `1`, each with `O(w)` tokens,
then the formula of level `0`. So Savitch's formula is polynomial-time in the width and depth in
unary, the two words, and the formula of level `0`
(`Cslib.Complexity.TQBF.computableInPolyTime_savitchFormula`).

The formula of level `0` numbers the variables of a Cook–Levin tableau by odd numbers
(`Cslib.Complexity.TQBF.computableInPolyTime_tabVar`), and is polynomial-time in the tableau.
Composed with the polynomial-time width and codes of the views
(`Turing.MultiTapeNTM.computableTidilyInPolyTime_codeWidth`) and the polynomial-time Cook–Levin
tableau (`Cslib.Complexity.CookLevin.computableInPolyTime_tableau`), the reduction
`Cslib.Complexity.TQBF.reduce` is polynomial-time, for every machine standing for the test of one
step or none and every polynomial time bound
(`Cslib.Complexity.TQBF.computableInPolyTime_reduce`). That test is itself polynomial-time
(`Cslib.Complexity.TQBF.computableInPolyTime_edgeTest`), which provides the machine.

## Main results

* `Cslib.Complexity.TQBF.computableInPolyTime_of_tokens`: formulas from their tokens.
* `Cslib.Complexity.TQBF.computableInPolyTime_savitchFormula`: Savitch's formula is
  polynomial-time.
* `Cslib.Complexity.TQBF.computableInPolyTime_baseFormula`: a tableau as the formula of
  level `0` is polynomial-time.
* `Cslib.Complexity.TQBF.computableInPolyTime_edgeTest`: the test of one step or none is
  polynomial-time.
* `Cslib.Complexity.TQBF.computableInPolyTime_reduce`: the reduction is polynomial-time.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.9][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.13][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.TQBF

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL ComputableTidilyInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-! ### Formulas from their tokens -/

/-- The tokens of an encoded formula, the identity on encoded values. -/
@[fun_prop]
theorem computableInPolyTime_tokens :
    Turing.MultiTapeTM.ComputableInPolyTime QBF.tokens encQBF (encList encToken) :=
  Turing.MultiTapeTM.ComputableInPolyTime.of_eq fun _ => rfl

/-- A formula is polynomial-time when its tokens are. -/
theorem computableInPolyTime_of_tokens {f : γ → QBF ℕ} {l : γ → List (QBF.Kind × ℕ)}
    (hl : Turing.MultiTapeTM.ComputableInPolyTime l encIn (encList encToken))
      (h : ∀ x, (f x).tokens = l x) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encQBF := by
  have hl := hl.tidy
  exact .of_tidy (hl.of_enc_eq fun x => by rw [encQBF_apply, h])

/-- A variable, from its number in binary. -/
@[fun_prop]
theorem computableInPolyTime_var {v : γ → ℕ}
    (hv : Turing.MultiTapeTM.ComputableInPolyTime v encIn encNat) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.var (v x)) encIn encQBF :=
  computableInPolyTime_of_tokens (l := fun x => [(.var, v x)]) (by fun_prop) fun _ => rfl

/-- Negation. -/
@[fun_prop]
theorem computableInPolyTime_not {φ : γ → QBF ℕ}
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn encQBF) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => (φ x).not) encIn encQBF :=
  computableInPolyTime_of_tokens (l := fun x => (.not, 0) :: (φ x).tokens) (by fun_prop)
    fun _ => rfl

/-- Conjunction. -/
@[fun_prop]
theorem computableInPolyTime_and {φ ψ : γ → QBF ℕ}
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn encQBF)
    (hψ : Turing.MultiTapeTM.ComputableInPolyTime ψ encIn encQBF) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => (φ x).and (ψ x)) encIn encQBF :=
  computableInPolyTime_of_tokens (l := fun x => (.and, 0) :: ((φ x).tokens ++ (ψ x).tokens))
    (by fun_prop) fun _ => rfl

/-- Disjunction. -/
@[fun_prop]
theorem computableInPolyTime_or {φ ψ : γ → QBF ℕ}
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn encQBF)
    (hψ : Turing.MultiTapeTM.ComputableInPolyTime ψ encIn encQBF) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => (φ x).or (ψ x)) encIn encQBF :=
  computableInPolyTime_of_tokens (l := fun x => (.or, 0) :: ((φ x).tokens ++ (ψ x).tokens))
    (by fun_prop) fun _ => rfl

/-- A block of existential quantifiers, over a list of variables in binary. -/
@[fun_prop]
theorem computableInPolyTime_exs {vs : γ → List ℕ} {φ : γ → QBF ℕ}
    (hvs : Turing.MultiTapeTM.ComputableInPolyTime vs encIn (encList encNat))
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn encQBF) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.exs (vs x) (φ x)) encIn encQBF :=
  computableInPolyTime_of_tokens
    (l := fun x => (vs x).map (fun v => (QBF.Kind.ex, v)) ++ (φ x).tokens) (by fun_prop)
    fun _ => QBF.tokens_exs ..

/-- A block of universal quantifiers, over a list of variables in binary. -/
@[fun_prop]
theorem computableInPolyTime_alls {vs : γ → List ℕ} {φ : γ → QBF ℕ}
    (hvs : Turing.MultiTapeTM.ComputableInPolyTime vs encIn (encList encNat))
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn encQBF) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.alls (vs x) (φ x)) encIn encQBF :=
  computableInPolyTime_of_tokens
    (l := fun x => (vs x).map (fun v => (QBF.Kind.all, v)) ++ (φ x).tokens) (by fun_prop)
    fun _ => QBF.tokens_alls ..

/-- The conjunction of a list of formulas. -/
@[fun_prop]
theorem computableInPolyTime_conj {l : γ → List (QBF ℕ)}
    (hl : Turing.MultiTapeTM.ComputableInPolyTime l encIn (encList encQBF)) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.conj (l x)) encIn encQBF :=
  computableInPolyTime_of_tokens
    (l := fun x => (l x).flatMap (fun φ => (QBF.Kind.and, 0) :: φ.tokens) ++ [(.top, 0)])
    (by fun_prop) fun _ => QBF.tokens_conj ..

/-- Implication. -/
@[fun_prop]
theorem computableInPolyTime_imp {φ ψ : γ → QBF ℕ}
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn encQBF)
    (hψ : Turing.MultiTapeTM.ComputableInPolyTime ψ encIn encQBF) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.imp (φ x) (ψ x)) encIn encQBF := by
  unfold QBF.imp
  fun_prop

/-- Equivalence. -/
@[fun_prop]
theorem computableInPolyTime_iff {φ ψ : γ → QBF ℕ}
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn encQBF)
    (hψ : Turing.MultiTapeTM.ComputableInPolyTime ψ encIn encQBF) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.iff (φ x) (ψ x)) encIn encQBF := by
  unfold QBF.iff
  fun_prop

/-- A literal, from its variable in binary and its sign. -/
@[fun_prop]
theorem computableInPolyTime_lit {v : γ → ℕ} {b : γ → Bool}
    (hv : Turing.MultiTapeTM.ComputableInPolyTime v encIn encNat)
    (hb : Turing.MultiTapeTM.ComputableInPolyTime b encIn encBool) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.lit (v x) (b x)) encIn encQBF := by
  unfold QBF.lit
  fun_prop

/-- A formula in conjunctive normal form, from its clauses in the encoding of
`Cslib.Complexity.encCNF`. -/
@[fun_prop]
theorem computableInPolyTime_ofCNF {φ : γ → CNF ℕ}
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn
      (encList (encList (encPair encNat encBool)))) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.ofCNF (φ x)) encIn encQBF :=
  computableInPolyTime_of_tokens (l := fun x => (φ x).flatMap (fun c => (QBF.Kind.and, 0) ::
      (c.flatMap (fun l => (QBF.Kind.or, 0) :: (QBF.lit l.1 l.2).tokens) ++ [(QBF.Kind.bot, 0)])) ++
      [(QBF.Kind.top, 0)]) (by fun_prop) fun _ => QBF.tokens_ofCNF _

/-! ### The midpoint formulas -/

/-- A block variable, from its kind, level and index in unary, in binary. -/
@[fun_prop]
theorem computableInPolyTime_blockVar {kind i j : γ → ℕ}
    (hkind : Turing.MultiTapeTM.ComputableInPolyTime kind encIn encUnary)
    (hi : Turing.MultiTapeTM.ComputableInPolyTime i encIn encUnary)
    (hj : Turing.MultiTapeTM.ComputableInPolyTime j encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => blockVar (kind x) (i x) (j x)) encIn encNat :=
      by
  have hkind := hkind.tidy
  have hi := hi.tidy
  have hj := hj.tidy
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime (fun x => blockVar (kind x) (i x) (j x)) encIn encUnary := by
    unfold blockVar
    fun_prop
  exact unary_to_binary.comp h

/-- The variables of a block, from the width, kind and level in unary. -/
@[fun_prop]
theorem computableInPolyTime_blockVars {w kind i : γ → ℕ}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hkind : Turing.MultiTapeTM.ComputableInPolyTime kind encIn encUnary)
    (hi : Turing.MultiTapeTM.ComputableInPolyTime i encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => blockVars (w x) (kind x) (i x)) encIn
      (encList encNat) := by
  unfold blockVars
  fun_prop

/-- The equality of two blocks. -/
@[fun_prop]
theorem computableInPolyTime_eqBlock {w k i k' i' : γ → ℕ}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hk : Turing.MultiTapeTM.ComputableInPolyTime k encIn encUnary)
    (hi : Turing.MultiTapeTM.ComputableInPolyTime i encIn encUnary)
    (hk' : Turing.MultiTapeTM.ComputableInPolyTime k' encIn encUnary)
    (hi' : Turing.MultiTapeTM.ComputableInPolyTime i' encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => eqBlock (w x) (k x) (i x) (k' x) (i' x)) encIn
      encQBF := by
  unfold eqBlock
  fun_prop

/-- A block holding a word. -/
@[fun_prop]
theorem computableInPolyTime_isBlock {w k i : γ → ℕ} {u : γ → List Bool}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hk : Turing.MultiTapeTM.ComputableInPolyTime k encIn encUnary)
    (hi : Turing.MultiTapeTM.ComputableInPolyTime i encIn encUnary)
    (hu : Turing.MultiTapeTM.ComputableInPolyTime u encIn encBits) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => isBlock (w x) (k x) (i x) (u x)) encIn
      encQBF := by
  unfold isBlock
  fun_prop

/-- The hypothesis of a level. -/
@[fun_prop]
theorem computableInPolyTime_halves {w i : γ → ℕ}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hi : Turing.MultiTapeTM.ComputableInPolyTime i encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => halves (w x) (i x)) encIn encQBF := by
  unfold halves
  fun_prop

/-- The tokens a level adds to the midpoint formula. -/
@[fun_prop]
theorem computableInPolyTime_levelTokens {w i : γ → ℕ}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hi : Turing.MultiTapeTM.ComputableInPolyTime i encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => levelTokens (w x) (i x)) encIn
      (encList encToken) := by
  unfold levelTokens
  fun_prop

/-- The midpoint formula of level `d`, from the width and level in unary and the formula of
level `0`. -/
@[fun_prop]
theorem computableInPolyTime_midpoint {w d : γ → ℕ} {base : γ → QBF ℕ}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hbase : Turing.MultiTapeTM.ComputableInPolyTime base encIn encQBF)
    (hd : Turing.MultiTapeTM.ComputableInPolyTime d encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => midpoint (w x) (base x) (d x)) encIn encQBF :=
  computableInPolyTime_of_tokens
    (l := fun x => (List.range (d x)).reverse.flatMap (levelTokens (w x)) ++ (base x).tokens)
    (by fun_prop) fun _ => tokens_midpoint ..

/-- **Savitch's formula is polynomial-time** in the width and depth in unary, the formula of
level `0`, and the two words. -/
@[fun_prop]
theorem computableInPolyTime_savitchFormula {w d : γ → ℕ} {base : γ → QBF ℕ}
    {u v : γ → List Bool}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hd : Turing.MultiTapeTM.ComputableInPolyTime d encIn encUnary)
    (hbase : Turing.MultiTapeTM.ComputableInPolyTime base encIn encQBF)
    (hu : Turing.MultiTapeTM.ComputableInPolyTime u encIn encBits)
    (hv : Turing.MultiTapeTM.ComputableInPolyTime v encIn encBits) :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun x => savitchFormula (w x) (d x) (base x) (u x) (v x)) encIn
      encQBF := by
  unfold savitchFormula
  fun_prop

/-! ### The formula of level `0` -/

section Base

variable {k : ℕ} {State : Type} [Fintype State]

/-- The index of a tableau variable in unary, the identity on encoded values. -/
private theorem computableTidilyInPolyTime_index_unary :
    ComputableTidilyInPolyTime (CookLevin.Var.index (k := k) (State := State)) CookLevin.encVar
      encUnary :=
  of_eq fun _ => rfl

/-- The numbering of the tableau variables by odd numbers, in binary. -/
@[fun_prop]
theorem computableInPolyTime_tabVar :
    Turing.MultiTapeTM.ComputableInPolyTime (tabVar (k := k) (State := State)) CookLevin.encVar
      encNat := by
  refine .of_tidy ?_
  have := computableTidilyInPolyTime_index_unary (k := k) (State := State)
  have h : ComputableTidilyInPolyTime (fun v => tabVar (k := k) (State := State) v)
      CookLevin.encVar encUnary := by
    unfold tabVar
    fun_prop
  exact unary_to_binary.comp h

attribute [local fun_prop] Turing.MultiTapeTM.ComputableInPolyTime.tidy in
/-- The block variable holding a certificate bit, from the width and the index in unary. -/
@[fun_prop]
theorem computableInPolyTime_certVar {w j : γ → ℕ}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary)
    (hj : Turing.MultiTapeTM.ComputableInPolyTime j encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => certVar (w x) (j x)) encIn encNat := by
  have hw := hw.tidy
  have hj := hj.tidy
  refine .of_tidy ?_
  unfold certVar
  fun_prop

attribute [local fun_prop] Turing.MultiTapeTM.ComputableInPolyTime.tidy in
/-- **A tableau as the formula of level `0` is polynomial-time** in the tableau and the width in
unary. -/
@[fun_prop]
theorem computableInPolyTime_baseFormula {tab : γ → CNF (CookLevin.Var k State)}
    {w : γ → ℕ}
    (htab : Turing.MultiTapeTM.ComputableInPolyTime tab encIn
      (encList (encList (encPair CookLevin.encVar encBool))))
    (hw : Turing.MultiTapeTM.ComputableInPolyTime w encIn encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => baseFormula (tab x) (w x)) encIn encQBF := by
  have htab := htab.tidy
  have hw := hw.tidy
  refine .of_tidy ?_
  have hvars : ComputableTidilyInPolyTime (fun x => (tab x).vars) encIn
      (encList CookLevin.encVar) :=
    (CNF.computableInPolyTime_vars CookLevin.encVar).tidy.comp htab
  have hrelabel : ComputableTidilyInPolyTime (fun x => CNF.relabel tabVar (tab x)) encIn
      (encList (encList (encPair encNat encBool))) :=
    (CNF.computableInPolyTime_relabel computableInPolyTime_tabVar).tidy.comp htab
  unfold baseFormula baseVars certLinks
  fun_prop

end Base

/-! ### The reduction -/

section Reduction

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {State : Type} [Finite State]
  {ntm : MultiTapeNTM k Bool State} {c d : ℕ}

/-- The width of the words of the reduction, in unary. -/
@[fun_prop]
theorem computableInPolyTime_width :
    Turing.MultiTapeTM.ComputableInPolyTime (width enc ntm c d) enc encUnary := by
  refine .of_tidy ?_
  have := MultiTapeNTM.computableTidilyInPolyTime_codeWidth (ntm := ntm) (enc := enc) c d
  unfold width
  fun_prop

/-- **The test of one step or none between codes is polynomial-time**, on the instance and the
concatenation of the two codes. -/
theorem computableInPolyTime_edgeTest :
    Turing.MultiTapeTM.ComputableInPolyTime (edgeTest enc ntm c d) (encPair enc encBits) encBool :=
      by
  refine .of_tidy ?_
  have hw : ComputableTidilyInPolyTime (fun p : α × List Bool => width enc ntm c d p.1)
      (encPair enc encBits) encUnary :=
    computableInPolyTime_width.tidy.comp (fst _ _)
  have hx : ComputableTidilyInPolyTime (fun p : α × List Bool => p.2.take (width enc ntm c d p.1))
      (encPair enc encBits) encBits := by fun_prop
  have hy : ComputableTidilyInPolyTime (fun p : α × List Bool => p.2.drop (width enc ntm c d p.1))
      (encPair enc encBits) encBits := by fun_prop
  have he := ntm.computableTidilyInPolyTime_codeEdge hx hy
  unfold edgeTest
  simp only [Cslib.Reachability.reach]
  fun_prop

attribute [local fun_prop] Turing.MultiTapeTM.ComputableInPolyTime.tidy in
/-- **The reduction to `TQBF` is polynomial-time**, for every machine `tmV` standing for the test
of one step or none and every time bound `cV * (n + 1) ^ dV` allowed to it. -/
theorem computableInPolyTime_reduce {kV : ℕ} {StateV : Type} [Fintype StateV]
    [DecidableEq StateV] (tmV : MultiTapeTM kV Bool StateV) (cV dV : ℕ) :
    Turing.MultiTapeTM.ComputableInPolyTime (reduce enc ntm c d tmV cV dV) enc encQBF := by
  refine .of_tidy ?_
  have hW := MultiTapeNTM.computableTidilyInPolyTime_codeWidth (ntm := ntm) (enc := enc) c d
  have hinit := ntm.computableTidilyInPolyTime_viewCode_initView hW (.encode enc)
  have hacc := MultiTapeNTM.computableTidilyInPolyTime_acceptCode hW
  have htab := (CookLevin.computableInPolyTime_tableau tmV).tidy
  have hframe := bitsFrame enc
  unfold reduce edgeTime
  fun_prop

end Reduction

end Cslib.Complexity.TQBF
