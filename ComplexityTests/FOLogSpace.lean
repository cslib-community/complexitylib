/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder
import Complexity.Computability.Complexity.Fagin.Layout
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
import ComplexityTests.FaginEncoding

/-!
# Tests: first-order model checking in logarithmic space

Concrete sentences over the vocabulary of graphs and over a nullary vocabulary have query
languages in `L`; the problems are nontrivial (an encoded structure in, one out, including the
empty structure), malformed inputs are out, the definable-class corollary applies, and the usual
closure properties of `L` carry over. A counter program copying its input exercises the emitting
path: it computes the identity in logarithmic space.
-/

namespace ComplexityTests.FOLogSpace

open FirstOrder Language Structure CategoryTheory Cslib.Logic Cslib.Complexity
open ComplexityTests.FaginEncoding

/-- Some vertex has a loop. -/
def hasLoop : Language.graph.Sentence :=
  (adj.boundedFormula₂ (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))).ex

/-- Every vertex has a loop. -/
def allLoops : Language.graph.Sentence :=
  (adj.boundedFormula₂ (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))).all

/-- The nullary relation holds. -/
def nullaryHolds : nullaryLanguage.Sentence := Relations.boundedFormula nullarySymbol ![]

/-! ### Fixed-list output sequencing -/

open Turing CounterProgram in
private def sampleBlock (long : Bool) (b : ℕ) : List Instr :=
  if long then [.emit true (b + 1), .emit false (b + 2)] else [.emit false (b + 1)]

private def sampleLength (long : Bool) : ℕ := if long then 2 else 1

open Turing CounterProgram in
private def sampleProgram : CounterProgram :=
  ⟨blocksCode sampleBlock sampleLength 0 [false, true, false] ++ [.halt List.nil], 0⟩

open Turing CounterProgram in
/-- Unequal block lengths and a repeated block preserve offsets and emitted word order. -/
example : sampleProgram.ReachesOut [] (sampleProgram.Active 0) (0, []) (4, [])
    [false, true, false, false] := by
  have hlen (x : Bool) (b : ℕ) : (sampleBlock x b).length = sampleLength x := by
    cases x <;> rfl
  have hcode : sampleProgram.CodeAt 0
      (blocksCode sampleBlock sampleLength 0 [false, true, false]) := by
    intro i hi
    have : i < 4 := hi
    interval_cases i <;> rfl
  obtain ⟨rs, hr, rfl⟩ := reachesOut_blocksCode (w := []) (Q := sampleProgram.Active 0)
    sampleBlock sampleLength hlen
    (fun x => if x then [true, false] else [false]) (fun rs => rs = [])
    (xs := [false, true, false]) (fun x _ b rs hc hI => by
      subst rs
      cases x
      · obtain ⟨hc, _⟩ := codeAt_cons.mp hc
        exact ⟨[], ReachesOut.emit hc (by simp) (ReachesOut.refl _), rfl⟩
      · obtain ⟨hc₀, hc₁⟩ := codeAt_cons.mp hc
        obtain ⟨hc₁, _⟩ := codeAt_cons.mp hc₁
        exact ⟨[], ReachesOut.emit hc₀ (by simp)
          (ReachesOut.emit hc₁ (by simp) (ReachesOut.refl _)), rfl⟩)
    0 [] hcode rfl
  exact hr

open Turing CounterProgram in
/-- Neither an empty sequence nor repeated zero-length blocks demand an active final state. -/
example (P : CounterProgram) (b : ℕ) (xs : List Unit) :
    P.ReachesOut [] (fun _ => False) (b, []) (b, []) [] := by
  obtain ⟨rs, hr, rfl⟩ := reachesOut_blocksCode (P := P) (w := []) (Q := fun _ => False)
    (fun (_ : Unit) _ => []) (fun _ => 0)
    (fun _ _ => rfl) (fun _ => []) (fun rs => rs = []) (xs := xs)
    (fun _ _ _ rs _ h => ⟨rs, by simpa using ReachesOut.refl _, h⟩)
    b [] (by
      have hnil : ∀ b xs, blocksCode (fun (_ : Unit) _ => []) (fun _ => 0) b xs = [] := by
        intro b xs
        induction xs generalizing b with
        | nil => rfl
        | cons x xs ih => simpa [blocksCode] using ih b
      rw [hnil]
      exact codeAt_nil) rfl
  have hout : xs.flatMap (fun _ => ([] : List Bool)) = [] :=
    List.flatMap_eq_nil_iff.mpr fun _ _ => rfl
  simpa [hout] using hr

/-! ### Membership in `L` -/

/-- Query languages of graph and nullary sentences, definable classes, and closure / inclusion into
`P` and `NL`. -/
example :
    graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ L encStructure ∧
    graphVocabulary.queryLanguage {M | M ⊨ allLoops} ∈ L encStructure ∧
    nullaryVocabulary.queryLanguage {M | M ⊨ nullaryHolds} ∈ L encStructure ∧
    (graphVocabulary.queryLanguage {M | M ⊨ hasLoop})ᶜ ∈ L encStructure ∧
    graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ P encStructure ∧
    graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∈ NL encStructure :=
  ⟨FO.Definable.queryLanguage_mem_L graphVocabulary ⟨hasLoop, fun _ _ => Iff.rfl⟩,
    graphVocabulary.queryLanguage_mem_L allLoops,
    nullaryVocabulary.queryLanguage_mem_L nullaryHolds,
    compl_mem_L (graphVocabulary.queryLanguage_mem_L hasLoop),
    L_subset_P (graphVocabulary.queryLanguage_mem_L hasLoop),
    L_subset_NL (graphVocabulary.queryLanguage_mem_L hasLoop)⟩

/-! ### The problems are nontrivial -/

theorem realize_hasLoop (a : EncodedStructure) :
    graphVocabulary.decoded a ⊨ hasLoop ↔
      ∃ x : Fin a.1, (graphVocabulary.table a ⟨2, adj⟩).getD (tupleIndex ![x, x]) false = true := by
  simp only [hasLoop, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_rel₂]
  rfl

theorem realize_allLoops (a : EncodedStructure) :
    graphVocabulary.decoded a ⊨ allLoops ↔
      ∀ x : Fin a.1, (graphVocabulary.table a ⟨2, adj⟩).getD (tupleIndex ![x, x]) false = true := by
  simp only [allLoops, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_rel₂]
  rfl

/-- A vertex with a loop is in. -/
example : ((1, [ [true] ]) : EncodedStructure) ∈
    graphVocabulary.queryLanguage {M | M ⊨ hasLoop} := by
  refine ⟨by decide +kernel, (realize_hasLoop _).mpr ⟨0, ?_⟩⟩
  decide +kernel

/-- The edge has no loop. -/
example : edge ∉ graphVocabulary.queryLanguage {M | M ⊨ hasLoop} := by
  rintro ⟨-, h⟩
  obtain ⟨x, hx⟩ := (realize_hasLoop _).mp h
  revert hx
  fin_cases x <;> decide +kernel

/-- **The empty structure** and malformed inputs: every vertex of the empty graph has a loop
vacuously and none has one, while malformed inputs are rejected. -/
example :
    ((0, [ [] ]) : EncodedStructure) ∈ graphVocabulary.queryLanguage {M | M ⊨ allLoops} ∧
    ((0, [ [] ]) : EncodedStructure) ∉ graphVocabulary.queryLanguage {M | M ⊨ hasLoop} ∧
    ((0, []) : EncodedStructure) ∉ graphVocabulary.queryLanguage {M | M ⊨ allLoops} :=
  ⟨⟨by decide +kernel, (realize_allLoops _).mpr fun x => x.elim0⟩,
    fun ⟨_, h⟩ => let ⟨x, _⟩ := (realize_hasLoop _).mp h; x.elim0,
    fun h => absurd h.1 (by decide +kernel)⟩

/-! ### Counter programs with output -/

section Copy

open Turing Turing.CounterProgram Turing.MultiTapeTM

/-- A counter program copying its input, one bit per round: register `0` is the position. -/
def copyProgram : CounterProgram where
  code :=
    [.read (.reg 0) 1 2 3,
     .emit true 4,
     .emit false 4,
     .halt [],
     .assign 0 (.add (.reg 0) (.const 1)) 0]
  registers := 1

/-- From position `k`, the copy program emits the rest of the input and halts. -/
theorem reachesOut_copyProgram (w : List Bool) :
    ∀ e k, w.length - k = e → k ≤ w.length →
      copyProgram.ReachesOut w (copyProgram.Active ((w.length + 1) ^ 1)) (0, [k])
        (3, [w.length]) (w.drop k) := by
  have hB (k : ℕ) (hk : k ≤ w.length) : ∀ r ∈ [k], r ≤ (w.length + 1) ^ 1 := by
    simp only [List.mem_singleton, pow_one]
    rintro r rfl
    omega
  intro e
  induction e with
  | zero =>
    intro k he hk
    obtain rfl : k = w.length := by omega
    refine ReachesOut.read (B := (w.length + 1) ^ 1) rfl (hB _ hk) ?_
    simp only [Expr.eval_reg, List.getD_cons_zero, List.getElem?_eq_none le_rfl, readLabel,
      List.drop_length]
    exact ReachesOut.refl _
  | succ e ih =>
    intro k he hk
    have hk' : k < w.length := by omega
    have hrest := ih (k + 1) (by omega) hk'
    rw [List.drop_eq_getElem_cons hk']
    refine ReachesOut.read (B := (w.length + 1) ^ 1) rfl (hB _ hk) ?_
    simp only [Expr.eval_reg, List.getD_cons_zero, List.getElem?_eq_getElem hk']
    cases hb : w[k] <;> simp only [readLabel]
    · refine ReachesOut.emit rfl (hB _ hk) (ReachesOut.assign rfl (hB _ hk) ?_)
      simpa using hrest
    · refine ReachesOut.emit rfl (hB _ hk) (ReachesOut.assign rfl (hB _ hk) ?_)
      simpa using hrest

/-- **The emitting path**: the copy program computes the identity in logarithmic space. -/
example : ComputableInLogSpace (fun w : List Bool => w) encBits encBits :=
  copyProgram.computableInLogSpace_of_reachesOut 1 fun w =>
    ⟨(3, [w.length]), w, [], by
      have := reachesOut_copyProgram w (w.length - 0) 0 rfl (Nat.zero_le _)
      rw [List.drop_zero] at this
      exact this, rfl, by simp, by simp⟩

end Copy

/-! ### Counting loops, quotients and free variables -/

section Pieces

open Turing Turing.CounterProgram Turing.MultiTapeTM

/-- Quotients, remainders (remainder by `0` is the number itself), and `encStructurePrefix`
length. -/
example :
    (Expr.div (.const 7) (.const 2)).eval [] = 3 ∧
    (Expr.mod (.const 7) (.const 2)).eval [] = 1 ∧
    (Expr.div (.const 7) (.const 0)).eval [] = 0 ∧
    (Expr.mod (.const 7) (.const 0)).eval [] = 7 ∧
    (graphVocabulary.encStructurePrefix edge 1).length = tableStart edge 1 ∧
    tableStart edge 1 = 14 :=
  ⟨rfl, rfl, rfl, rfl, graphVocabulary.length_encStructurePrefix (by decide) (by decide),
    by decide⟩

/-- A loop running twice, emitting `true` each time. -/
def twiceProgram : CounterProgram where
  code := forCode 0 0 (.const 2) 3 4 ++ [.emit true 2, .halt List.nil]
  registers := 1

/-- The loop emits `[true, true]` and exits with the counter at `2`. -/
example (w : List Bool) :
    ∃ regs, twiceProgram.ReachesOut w (twiceProgram.Active 5) (0, [5]) (4, regs) [true, true] ∧
      regs = [2] := by
  obtain ⟨regs, hreach, hr, -⟩ := reachesOut_forCode (P := twiceProgram) (w := w) (B := 5)
    (b := 0) (u := 0) (bound := .const 2) (body := 3) (exit := 4) (N := 2)
    (fun i hi => by
      simp only [forCode, List.length_cons, List.length_nil] at hi
      interval_cases i <;> rfl)
    (fun k r => r = [k] ∧ k ≤ 2) (fun _ => [true]) (by omega)
    (fun k r ⟨hr, hk⟩ => by subst hr; exact ⟨rfl, rfl, by simp, by simp; omega⟩)
    (fun k hk r ⟨hr, _⟩ => ⟨[k], ReachesOut.emit (B := 5) rfl (by subst hr; simp; omega)
      (by subst hr; exact ReachesOut.refl _), rfl, by simp; omega, by simp; omega⟩)
    [5] (by simp) ⟨rfl, by omega⟩
  exact ⟨regs, hreach, hr⟩

/-- A loop at a vertex `x`, a formula with a free variable. -/
def loopAt : Language.graph.Formula Unit :=
  adj.boundedFormula₂ (Term.var (Sum.inl ())) (Term.var (Sum.inl ()))

/-- The code of `loopAt` with `x` in register `1`, accepting at label `1`, rejecting at `2`. -/
noncomputable def loopProgram : CounterProgram where
  code := Vocabulary.ModelChecker.formulaCode graphVocabulary (fun _ : Unit => 1) 2 loopAt 0 1 2 ++
    [.accept, .reject]
  registers := 2

/-- **The free-variable case of the compiler**: on a vertex with a loop, with `x = 0` in register
`1`, the compiled code goes to the accepting label. -/
example : ∃ regs, loopProgram.Reaches (encStructure ((1, [ [true] ]) : EncodedStructure))
    (loopProgram.Running 1) (0, [1, 0]) (1, regs) := by
  obtain ⟨res, regs, hres, hreach, -⟩ :=
    Vocabulary.ModelChecker.reaches_formulaCode (v := graphVocabulary) (P := loopProgram)
      (a := ((1, [ [true] ]) : EncodedStructure)) (B := 1)
      (by decide +kernel) (le_refl 1) (fun _ : Unit => 1) 2 (by norm_num) (fun _ => by norm_num)
      (fun _ => 0) loopAt 0 1 2 [1, 0] default
      (codeAt_of_code_eq (pre := []) (post := [.accept, .reject]) rfl)
      (le_of_eq rfl) rfl (by simp) (fun _ => rfl) (fun i => i.elim0)
  have hres' : res = true := by
    rw [hres]
    let _ := graphVocabulary.decode ((1, [ [true] ]) : EncodedStructure)
    change RelMap adj ![(0 : Fin 1), 0]
    exact (Vocabulary.relMap_decode (v := graphVocabulary) ((1, [ [true] ]) : EncodedStructure) adj
      ![0, 0]).mpr (by decide +kernel)
  subst hres'
  exact ⟨regs, hreach⟩

end Pieces

end ComplexityTests.FOLogSpace
