/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Basic
public import Complexity.Logics.FirstOrder.Interpretation.Unit

/-!
# Canonical numeric expansions as sources of first-order interpretations

The existing `FO.Interpretation` accepts arbitrary source languages, including the numeric
constants, while its interpreted target remains relational. Forgetting the canonical numeric
symbols is a one-dimensional interpretation whose interpreted structure is isomorphic to the
input. Its pullback therefore preserves every input sentence, including quantified sentences.

No new interpretation syntax is introduced. Target constants and canonical full-tuple numeric
preservation are supplied separately in `Ordered.FullTuple`, using `Ordered.TupleBit`;
numeric-preserving full-tuple composition is in `Ordered.FullTuple.Composition`.
This forgetting bridge does not supply an ordered reduction or machine bound.

## Main definitions

* `Cslib.Logic.FO.Ordered.forget`: forget numeric symbols through the existing interpretation API.
* `Cslib.Logic.FO.Ordered.forgetEquiv`: its canonical isomorphism back to the input structure.

## Main results

* `Cslib.Logic.FO.Ordered.realize_forget_onSentence`: truth preservation through interpretation
  pullback from the canonical expansion.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 1.2 and Proposition 3.5.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

variable (L : Language)

/-- Forget the numeric expansion, retaining the whole input universe and its relations. -/
def forget : Interpretation (language L) L Unit where
  domain := ⊤
  rel R := (LHom.sumInl : L →ᴸ language L).onFormula (R.formula fun i => .var (i, ()))

variable {L} [L.IsRelational] {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- The relational structure obtained by forgetting the canonical numeric symbols is the input. -/
def forgetEquiv : (forget L).Model (Fin n) ≃[L] Fin n where
  toFun x := x.val ()
  invFun x := ⟨fun _ => x, Formula.realize_top.mpr trivial⟩
  left_inv _ := Interpretation.Model.ext rfl
  right_inv _ := rfl
  map_fun' f := isEmptyElim f
  map_rel' _ _ := Iff.rfl

/-- `forgetEquiv` evaluates a `Unit`-indexed tuple at `()`. -/
@[simp] theorem forgetEquiv_apply (x : (forget L).Model (Fin n)) :
    forgetEquiv x = x.val () := rfl

/-- Pullback through the existing relational interpretation recovers the input sentence's truth. -/
theorem realize_forget_onSentence (φ : L.Sentence) :
    Fin n ⊨ (forget L).onSentence φ ↔ Fin n ⊨ φ := by
  rw [Interpretation.realize_onSentence]
  exact StrongHomClass.realize_sentence (forgetEquiv (L := L) (n := n)) φ

end Cslib.Logic.FO.Ordered
