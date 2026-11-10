/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Trakhtenbrot.Undecidability

/-! # Trakhtenbrot's theorem: checked instances

Finite satisfiability on small examples: an axiom of infinity that is satisfiable but not finitely
satisfiable (so its negation is finitely valid but not valid), the standard arithmetic model, and
the reduction sentences of a halting and a non-halting code. -/

@[expose] public section

namespace Cslib.Tests.Trakhtenbrot

open Cslib.Logic.FO Cslib.Logic.FO.RawFormula Cslib.Logic.FO.Trakhtenbrot
open Nat.Partrec (Code)

theorem not_finSat_falsum : ¬FinSat falsum := fun ⟨_, _, _, _, _, h⟩ => h

theorem finSat_equal : FinSat (equal 0 0) := ⟨Unit, inferInstance, inferInstance,
  fun _ _ => False, fun _ => (), rfl⟩

/-- "Relation `0` is a strict order without a maximal element": an axiom of infinity. -/
def infAx : RawFormula :=
  conj (all 0 (neg (rel 0 [0, 0])))
    (conj (all 0 (all 1 (all 2 (imp (rel 0 [0, 1]) (imp (rel 0 [1, 2]) (rel 0 [0, 2]))))))
      (all 0 (ex 1 (rel 0 [0, 1]))))

theorem realize_infAx {M : Type} {I : ℕ → List M → Prop} {v : ℕ → M} :
    infAx.Realize I v ↔ (∀ a, ¬I 0 [a, a]) ∧
      (∀ a b c, I 0 [a, b] → I 0 [b, c] → I 0 [a, c]) ∧ ∀ a, ∃ b, I 0 [a, b] := by
  simp [infAx]

/-- The strict order of `ℕ` as relation `0`. -/
def ltInterp : ℕ → List ℕ → Prop
  | 0, [a, b] => a < b
  | _, _ => False

/-- The axiom of infinity holds in `ℕ`. -/
theorem realize_infAx_nat : infAx.Realize ltInterp fun _ => 0 :=
  realize_infAx.2 ⟨fun a => lt_irrefl a, fun _ _ _ => lt_trans, fun a => ⟨a + 1, a.lt_succ_self⟩⟩

/-- The axiom of infinity has no finite model. -/
theorem not_finSat_infAx : ¬FinSat infAx := by
  rintro ⟨M, _, ⟨m⟩, I, v, h⟩
  obtain ⟨hirr, htr, hser⟩ := realize_infAx.1 h
  let r : M → M → Prop := fun a b => I 0 [b, a]
  have : IsTrans M r := ⟨fun a b c hab hbc => htr c b a hbc hab⟩
  have : Std.Irrefl r := ⟨fun a => hirr a⟩
  obtain ⟨a, -, ha⟩ := (Finite.wellFounded_of_trans_of_irrefl r).has_min Set.univ ⟨m, trivial⟩
  obtain ⟨b, hb⟩ := hser a
  exact ha b trivial hb

/-- `¬infAx` is finitely valid, although it fails in `ℕ`. -/
theorem finValid_neg_infAx : FinValid (neg infAx) := (finValid_neg_iff _).2 not_finSat_infAx

theorem not_realize_neg_infAx_nat : ¬(neg infAx).Realize ltInterp fun _ => 0 :=
  fun h => h realize_infAx_nat

/-- The standard arithmetic relations are a model of the arithmetic axioms, at every size. -/
example (N : ℕ) :
    ∀ φ ∈ arithAxioms, φ.Realize (StdArith (N + 1)) fun _ => (⟨0, by omega⟩ : Fin (N + 1)) :=
  realize_arithAxioms.2 (arithModel_stdArith (N + 1))

/-- The constant-zero code halts, so its sentence is finitely satisfiable. -/
theorem finSat_haltSentence_zero : FinSat (haltSentence Code.zero) :=
  (eval_dom_iff_finSat _).1 trivial

/-- `rfind' succ` searches for a zero of `n ↦ n + 1`, so it diverges. -/
theorem not_dom_eval_rfind_succ : ¬(Code.eval (Code.rfind' Code.succ) 0).Dom := by
  have : ¬(Nat.rfind fun _ => Part.some false).Dom := fun h => by
    obtain ⟨n, hn, -⟩ := Nat.rfind_dom.1 h
    simp at hn
  simpa [Code.eval] using this

/-- The sentence of a diverging code has no finite model. -/
theorem not_finSat_haltSentence_rfind_succ : ¬FinSat (haltSentence (Code.rfind' Code.succ)) :=
  fun h => not_dom_eval_rfind_succ ((eval_dom_iff_finSat _).2 h)

end Cslib.Tests.Trakhtenbrot
