/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.TFNP.SearchToDecision
import Complexity.Computability.Complexity.Classes.TFNP.Subclasses
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete clients for `FNP`, `FPSearch`, `TFNP`, `PLS`, `PPP`, `PPAD`, `PPA`, disjoint sums,
and search reductions. -/

namespace ComplexityTests.TFNP

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-! ### A total problem: the empty word solves every instance -/

/-- Every instance has exactly the empty word as solution. -/
private def emptyRel (_ : List Bool) (w : List Bool) : Prop := w = []

private theorem emptyRel_mem_FNP : emptyRel ∈ FNP encBits :=
  ⟨⟨0, fun _ w h => by simp [emptyRel] at h; simp [h]⟩, fun x => x.2.isEmpty, by fun_prop,
    fun _ w => by simp [emptyRel]⟩

private theorem emptyRel_mem_TFNP : emptyRel ∈ TFNP encBits :=
  ⟨emptyRel_mem_FNP, fun _ => ⟨[], rfl⟩⟩

private theorem emptyRel_mem_FPSearch : emptyRel ∈ FPSearch encBits :=
  mem_FPSearch_of_total emptyRel_mem_FNP (.of_tidy (ComputableTidilyInPolyTime.const [])) fun _ =>
    rfl

example : searchDomain emptyRel = Set.univ :=
  isTotalSearch_iff_searchDomain_eq_univ.1 emptyRel_mem_TFNP.2

/-! ### A partial problem: copy the instance, when it starts with `true` -/

/-- The solution of an instance starting with `true` is the instance itself; other instances have
no solution. -/
private def copyRel (a : List Bool) (w : List Bool) : Prop := a.headD false = true ∧ w = a

private theorem copyRel_mem_FNP : copyRel ∈ FNP encBits :=
  mem_FNP_iff_exists_bounded.2 ⟨Polynomial.X, fun x => x.1.headD false && decide (x.2 = x.1),
    by fun_prop, fun a w => by
      simp only [copyRel, Polynomial.eval_X, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨h, hw⟩ => ⟨by simp [hw, encBits], h, hw⟩, fun ⟨_, h, hw⟩ => ⟨h, hw⟩⟩⟩

/-- `copyRel` is not total. -/
example : ¬IsTotalSearch copyRel := fun h => by
  obtain ⟨w, hw, -⟩ := h []
  simp at hw

/-- The solver of `copyRel` checks the first bit. -/
private theorem copyRel_mem_FPSearch : copyRel ∈ FPSearch encBits := by
  refine ⟨copyRel_mem_FNP, fun a => if a.headD false then some a else none, by fun_prop,
    fun a => ⟨fun w hw => ?_, fun hw ⟨w, h, _⟩ => ?_⟩⟩
  · beta_reduce at hw
    split_ifs at hw with ha
    exact ⟨ha, (Option.some_injective _ hw).symm⟩
  · beta_reduce at hw
    rw [h] at hw
    simp at hw

example : searchDomain copyRel ∈ P encBits := searchDomain_mem_P copyRel_mem_FPSearch
example : searchDomain copyRel ∈ NP encBits := searchDomain_mem_NP copyRel_mem_FNP

/-! ### Disjoint sums -/

/-- The empty word solves exactly the instances that do not start with `true`. -/
private def notHeadRel (a : List Bool) (w : List Bool) : Prop := a.headD false = false ∧ w = []

private theorem notHeadRel_mem_FNP : notHeadRel ∈ FNP encBits :=
  ⟨⟨0, fun _ w h => by simp [h.2]⟩, fun x => !x.1.headD false && x.2.isEmpty, by fun_prop,
    fun a w => by simp [notHeadRel]⟩

private theorem cover (a : List Bool) :
    a ∈ searchDomain copyRel ∨ a ∈ searchDomain notHeadRel := by
  cases h : a.headD false
  · exact .inr ⟨[], h, rfl⟩
  · exact .inl ⟨a, h, rfl⟩

private theorem disjoint : Disjoint (searchDomain copyRel) (searchDomain notHeadRel) :=
  Set.disjoint_left.2 fun _ ⟨_, h, _⟩ ⟨_, h', _⟩ => by
    rw [h] at h'
    exact Bool.noConfusion h'

example : searchSum copyRel notHeadRel ∈ TFNP encBits :=
  searchSum_mem_TFNP copyRel_mem_FNP notHeadRel_mem_FNP cover

/-- The disjoint sum is solved in polynomial time, so the first domain is decided. -/
example : searchDomain copyRel ∈ P encBits := by
  refine searchDomain_mem_P_of_searchSum_mem_FPSearch ?_ disjoint
  refine ⟨searchSum_mem_FNP copyRel_mem_FNP notHeadRel_mem_FNP,
    fun a => some (if a.headD false then true :: a else [false]), by fun_prop,
    solvesSearch_some fun a => ?_⟩
  cases h : a.headD false
  · exact ⟨h, rfl⟩
  · exact ⟨h, rfl⟩

/-! ### Search reductions -/

private theorem emptyRel_searchReducible_emptyRel :
    SearchReducible encBits encBits emptyRel emptyRel :=
  .refl _ _

/-- The total `emptyRel` reduces to the partial `copyRel`: map every instance to `[true]`, whose
solution is `[true]`, and every solution back to the empty word. -/
private theorem emptyRel_searchReducible_copyRel :
    SearchReducible encBits encBits emptyRel copyRel :=
  ⟨fun _ => [true], fun _ => [], ComputableInPolyTime.const _,
    ComputableInPolyTime.const _, fun _ _ => ⟨[true], rfl, rfl⟩, fun _ _ _ => rfl⟩

example : SearchReducible encBits encBits emptyRel copyRel :=
  emptyRel_searchReducible_emptyRel.trans emptyRel_searchReducible_copyRel

example : emptyRel ∈ FPSearch encBits :=
  emptyRel_searchReducible_copyRel.mem_FPSearch emptyRel_mem_FNP copyRel_mem_FPSearch

example : PolyTimeReducible encBits encBits (searchDomain emptyRel) (searchDomain copyRel) :=
  emptyRel_searchReducible_copyRel.polyTimeReducible

/-- A reduction to the total `emptyRel` needs only the one-way condition on solutions. -/
example : SearchReducible encBits encBits emptyRel emptyRel :=
  .of_isTotalSearch emptyRel_mem_TFNP.2 (.of_tidy ComputableTidilyInPolyTime.id')
    (.of_tidy (ComputableTidilyInPolyTime.const [])) fun _ _ _ => rfl

/-- **A complete problem.** `emptyRel` is complete for the total problems solvable in polynomial
time: such a problem reduces to it by solving the instance in the map back. -/
example : SearchComplete (fun {α : Type} (enc : α ↪ List Bool) => TFNP enc ∩ FPSearch enc)
    encBits emptyRel := by
  refine ⟨⟨emptyRel_mem_TFNP, emptyRel_mem_FPSearch⟩, fun _ enc R ⟨hR, hR'⟩ => ?_⟩
  obtain ⟨g, hg, hgR⟩ := exists_total_of_mem_FPSearch hR' hR.2
  exact .of_isTotalSearch emptyRel_mem_TFNP.2 (.of_tidy (ComputableTidilyInPolyTime.const []))
    (hg.comp (.of_tidy (ComputableTidilyInPolyTime.fst enc encBits))) fun a _ _ => hgR a

/-! ### `SAT` -/

example : SAT.searchRel ∈ FNP encCNF := SAT.searchRel_mem_FNP
example : searchDomain SAT.searchRel ∈ NP encCNF := searchDomain_mem_NP SAT.searchRel_mem_FNP
example : SAT.searchRel ∈ FPSearch encCNF ↔ SAT ∈ P encCNF := SAT.searchRel_mem_FPSearch_iff
example : (∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc) ↔ SAT ∈ P encCNF :=
  FNP_subset_FPSearch_iff_SAT_mem_P

/-! ### `TFNP` subclasses (`PLS`, `PPP`, `PPAD`, `PPA`) and circuit problems -/

example : LocalOpt ∈ PLS encLocalOpt := LocalOpt_mem_PLS
example : Pigeon ∈ PPP encPigeon := Pigeon_mem_PPP
example : EndOfLine ∈ PPAD encEndOfLine := EndOfLine_mem_PPAD
example : Leaf ∈ PPA encLeaf := Leaf_mem_PPA

example : LocalOpt ∈ TFNP encLocalOpt := LocalOpt_mem_TFNP
example : Pigeon ∈ TFNP encPigeon := Pigeon_mem_TFNP
example : EndOfLine ∈ TFNP encEndOfLine := EndOfLine_mem_TFNP
example : Leaf ∈ TFNP encLeaf := Leaf_mem_TFNP

example : EndOfLine ∈ PPP encEndOfLine := EndOfLine_mem_PPP
example : EndOfLine ∈ PPA encEndOfLine := EndOfLine_mem_PPA

/-- Concrete 1-bit wire circuit code `x ↦ x` and negation circuit code `x ↦ ¬x`. -/
private def idCode1 : CircuitCode := ([], [0])
private def notCode1 : CircuitCode := ([(.not, [0])], [1])

/-- `[false]` is a local optimum of `(1, idCode1, idCode1)`. -/
example : LocalOpt (1, idCode1, idCode1) [false] :=
  ⟨rfl, le_rfl⟩

/-- `[false, true]` is a `Pigeon` solution for the constant-zero circuit `(1, ([], []))`. -/
example : Pigeon (1, ([], [])) [false, true] :=
  ⟨rfl, .inl rfl⟩

/-- `[true]` is the end of the line for `(1, notCode1, notCode1)`, where `0` has active edge `0 → 1`
and `1` is a sink. -/
example : EndOfLine (1, notCode1, notCode1) [true] :=
  ⟨rfl, rfl⟩

/-- The active source `[false]` in `(1, notCode1, notCode1)` has an outgoing edge `0 → 1` and is not
a solution of `EndOfLine`. -/
example : ¬EndOfLine (1, notCode1, notCode1) [false] := fun ⟨_, h⟩ =>
  Bool.noConfusion h

/-- An isolated vertex `[true] ≠ [false]` (encoded by a self-loop in `(1, idCode1, idCode1)`) is
balanced (`in-degree = out-degree = 0`) and is not a solution of `EndOfLine`. -/
example : ¬EndOfLine (1, idCode1, idCode1) [true] := fun ⟨_, h⟩ =>
  Bool.noConfusion h

/-- `[true]` is the matching leaf of `0` in `(1, notCode1, idCode1)`. -/
example : Leaf (1, notCode1, idCode1) [true] :=
  ⟨rfl, rfl⟩

/-- Every total polynomial-time search problem reduces to `EndOfLine` and therefore belongs to
`PLS`, `PPP`, `PPAD`, and `PPA`. -/
private theorem emptyRel_searchReducible_EndOfLine :
    SearchReducible encBits encEndOfLine emptyRel EndOfLine :=
  .of_isTotalSearch isTotalSearch_EndOfLine
    (.of_tidy (ComputableTidilyInPolyTime.const (0, ([], []), ([], []))))
    (.of_tidy (ComputableTidilyInPolyTime.const [])) fun _ _ _ => rfl

example : emptyRel ∈ PPAD encBits :=
  emptyRel_searchReducible_EndOfLine.mem_PPAD emptyRel_mem_FNP EndOfLine_mem_PPAD

example : emptyRel ∈ PPP encBits :=
  PPAD_subset_PPP (emptyRel_searchReducible_EndOfLine.mem_PPAD emptyRel_mem_FNP EndOfLine_mem_PPAD)

example : emptyRel ∈ PPA encBits :=
  PPAD_subset_PPA (emptyRel_searchReducible_EndOfLine.mem_PPAD emptyRel_mem_FNP EndOfLine_mem_PPAD)

/-- The family certifying a `PPAD` membership is plain (`mem_PPAD`). -/
example : ∃ n : _ → ℕ, ComputableInPolyTime n encEndOfLine encUnary := by
  obtain ⟨-, n, -, -, hn, -⟩ := mem_PPAD.mp EndOfLine_mem_PPAD
  exact ⟨n, hn⟩

/-! ### Axiom guards -/

/--
info: 'Cslib.Complexity.mem_NP_iff_exists_FNP' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_iff_exists_FNP

/--
info: 'Cslib.Complexity.NP_inter_coNP_subset_P_of_TFNP_subset_FPSearch' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_inter_coNP_subset_P_of_TFNP_subset_FPSearch

/--
info: 'Cslib.Complexity.SearchReducible.mem_FPSearch' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SearchReducible.mem_FPSearch

/--
info: 'Cslib.Complexity.FNP_subset_FPSearch_iff' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FNP_subset_FPSearch_iff

/--
info: 'Cslib.Complexity.FNP_subset_FPSearch_iff_SAT_mem_P' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FNP_subset_FPSearch_iff_SAT_mem_P

/--
info: 'Cslib.Complexity.SAT.searchRel_mem_FPSearch_iff' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT.searchRel_mem_FPSearch_iff

/--
info: 'Cslib.Complexity.PLS_subset_TFNP' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PLS_subset_TFNP

/--
info: 'Cslib.Complexity.PPP_subset_TFNP' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PPP_subset_TFNP

/--
info: 'Cslib.Complexity.PPAD_subset_TFNP' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PPAD_subset_TFNP

/--
info: 'Cslib.Complexity.PPA_subset_TFNP' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PPA_subset_TFNP

/--
info: 'Cslib.Complexity.PPAD_subset_PPP' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PPAD_subset_PPP

/--
info: 'Cslib.Complexity.PPAD_subset_PPA' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PPAD_subset_PPA

/--
info: 'Cslib.Complexity.LocalOpt_mem_PLS' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.LocalOpt_mem_PLS

/--
info: 'Cslib.Complexity.Pigeon_mem_PPP' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Pigeon_mem_PPP

/--
info: 'Cslib.Complexity.EndOfLine_mem_PPAD' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.EndOfLine_mem_PPAD

/--
info: 'Cslib.Complexity.Leaf_mem_PPA' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Leaf_mem_PPA

end ComplexityTests.TFNP
