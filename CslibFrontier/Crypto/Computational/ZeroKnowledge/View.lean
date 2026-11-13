/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Encoding

/-!
# Views and distinguishers of zero-knowledge experiments

A zero-knowledge statement compares the view of a malicious verifier interacting with the honest
prover against the output of a simulator, as seen by a distinguisher that also receives the
security parameter, the instance and an auxiliary input. This module names those parts, so that
statements need not spell out the prover run or the nested distinguisher input.

## Main definitions

* `Cslib.Crypto.zkRealView`: the law of the verifier's output after interacting with a prover.
* `Cslib.Crypto.ZKDistinguisher`: a distinguisher taking `(n, a, z)` and a view.
* `Cslib.Crypto.ZKDistinguisher.IsPPT`: one uniform strict PPT machine reads the complete encoded
  input `((1^n, (a, z)), view)` and writes the distinguisher's bit.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Complexity Turing.MultiTapeTM

/-- The real view of a zero-knowledge experiment: the law of the output of `verifier` after it
interacts with the prover `P` from `P`'s initial state, with `P`'s final state discarded. -/
noncomputable abbrev zkRealView (P : Prover Unit) (verifier : WordOracleComp Unit (List Bool)) :
    PMF (List Bool) :=
  (P.run verifier P.init).map Prod.fst

/-- A zero-knowledge distinguisher: given the security parameter `n`, the instance `a`, an
auxiliary input word `z` and a view, it outputs a bit. `ZKDistinguisher.IsPPT` states its
efficiency on encodings. -/
abbrev ZKDistinguisher (α : Type) : Type :=
  ℕ → α → List Bool → List Bool → ProbComp Bool

/-- A zero-knowledge distinguisher is PPT when one uniform strict PPT machine reads its complete
encoded input `((1^n, (a, z)), view)`, laid out by `encPair (encInstanceAuxInput enc) encBits`,
and writes its output bit. -/
def ZKDistinguisher.IsPPT {α : Type} (enc : α ↪ List Bool) (adversary : ZKDistinguisher α) :
    Prop :=
  IsPPTOn (encPair (encInstanceAuxInput enc) encBits) encBool
    (fun ((n, a, z), view) => adversary n a z view)

end Cslib.Crypto
