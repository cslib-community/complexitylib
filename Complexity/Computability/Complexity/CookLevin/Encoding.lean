/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.CookLevin.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# Encodings for constructing the Cook–Levin tableau

Intermediate features and variables are encoded by their existing indices in unary. The indices
use a fixed nesting depth of the polynomial pairing function, so constructing features from unary
times and positions has polynomial cost. States, tape numbers and symbols are fixed parameters.
The final variable numbering converts the same indices to the binary encoding used by SAT.

These certificates concern construction and numbering. They do not provide a polynomial-time
decoder or certify pattern matching on an arbitrary encoded feature.

## Main definitions

* `Cslib.Complexity.CookLevin.encFeature`, `Cslib.Complexity.CookLevin.encVar`.

## Main results

* `Cslib.Complexity.CookLevin.computableInPolyTime_inPos`,
  `.computableInPolyTime_head`, `.computableInPolyTime_cell`: varying positions.
* `Cslib.Complexity.CookLevin.computableInPolyTime_holds`,
  `.computableInPolyTime_cert`: tableau variable constructors.
* `Cslib.Complexity.CookLevin.computableInPolyTime_index`: the existing variable numbering
  with binary output.
* `Cslib.Complexity.CookLevin.computableInPolyTime_relabel`: number all variables in a
  constructed tableau, producing the SAT encoding.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {k : ℕ} {State : Type} [Fintype State]

/-- A feature is represented by its existing index in unary. -/
noncomputable def encFeature : Feature k State ↪ List Bool :=
  ⟨fun φ => encUnary (featureIndex φ), encUnary.injective.comp featureIndex_injective⟩

/-- A tableau variable is represented by its existing index in unary. -/
noncomputable def encVar : Var k State ↪ List Bool :=
  ⟨fun v => encUnary v.index, encUnary.injective.comp Var.index_injective⟩

/-- The unary feature index is already the encoded word. -/
@[fun_prop]
theorem computableInPolyTime_featureIndex :
    ComputableInPolyTime (featureIndex (k := k) (State := State)) encFeature encUnary :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Construct the input-symbol feature from an optional Boolean symbol. -/
@[fun_prop]
theorem computableInPolyTime_inRead :
    ComputableInPolyTime (Feature.inRead (k := k) (State := State))
      (encOption encBool) encFeature := ComputableInPolyTime.of_finite _

/-- Construct an input-head feature from a unary position. -/
@[fun_prop]
theorem computableInPolyTime_inPos :
    ComputableInPolyTime (Feature.inPos (k := k) (State := State)) encUnary encFeature :=
  .of_tidy ((unary_pair.comp ((const 1).prod id')).of_enc_eq fun _ => rfl)

/-- Construct a work-head feature on a fixed tape from a signed unary position. -/
@[fun_prop]
theorem computableInPolyTime_head (i : Fin k) :
    ComputableInPolyTime (Feature.head (State := State) i) encInt encFeature := by
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime (fun z => Nat.pair 2 (Nat.pair i (Equiv.intEquivNat z)))
      encInt encUnary := by fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Construct a cell feature for a fixed tape and symbol from a signed unary position. -/
@[fun_prop]
theorem computableInPolyTime_cell (i : Fin k) (s : Option Bool) :
    ComputableInPolyTime (fun z => Feature.cell (State := State) i z s)
      encInt encFeature := by
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime
      (fun z => Nat.pair 3 (Nat.pair i (Nat.pair (Equiv.intEquivNat z) (Encodable.encode s))))
      encInt encUnary := by fun_prop
  exact h.of_enc_eq fun _ => rfl

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Attach a unary time to an encoded feature. -/
@[fun_prop]
theorem computableInPolyTime_holds :
    ComputableInPolyTime (fun p : ℕ × Feature k State => Var.holds p.1 p.2)
      (encPair encUnary encFeature) encVar := by
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime
      (fun p : ℕ × Feature k State => Nat.pair 0 (Nat.pair p.1 (featureIndex p.2)))
      (encPair encUnary encFeature) encUnary := by fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Construct a certificate variable from its unary index. -/
@[fun_prop]
theorem computableInPolyTime_cert :
    ComputableInPolyTime (Var.cert (k := k) (State := State)) encUnary encVar :=
  .of_tidy ((unary_pair.comp ((const 1).prod id')).of_enc_eq fun _ => rfl)

/-- Emit the existing variable index in binary. -/
@[fun_prop]
theorem computableInPolyTime_index :
    ComputableInPolyTime (Var.index (k := k) (State := State)) encVar encNat :=
  .of_tidy (unary_to_binary.comp (of_eq (encMid := encUnary) fun _ => rfl))

/-- Convert a constructed tableau to the SAT encoding using its existing variable numbering. -/
@[fun_prop]
theorem computableInPolyTime_relabel :
    ComputableInPolyTime (Cslib.Logic.PL.CNF.relabel (Var.index (k := k) (State := State)))
      (encList (encList (encPair encVar encBool))) encCNF :=
  (Cslib.Logic.PL.CNF.computableInPolyTime_relabel computableInPolyTime_index)

end Cslib.Complexity.CookLevin
