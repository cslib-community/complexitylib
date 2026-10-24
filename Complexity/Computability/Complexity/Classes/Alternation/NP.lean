/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Alternation
public import Complexity.Computability.Complexity.Classes.NP.GuessVerify
public import Complexity.Computability.Complexity.Classes.P
import Complexity.Computability.Complexity.Reduction

/-!
# `NP ⊆ AP`

An alternating machine without universal states is a nondeterministic machine
(`Turing.MultiTapeATM.accepts_iff_toNTM_accepts`). Guessing a certificate and verifying it is
done by a finite fair-coin machine whose nondeterministic machine decides a problem in `NP` within
polynomial time (`Cslib.Complexity.IsVerifier.exists_decidesInTime`); labelling all its states
existential decides the problem as an alternating machine, so `NP ⊆ AP`
(`Cslib.Complexity.NP_subset_AP`) [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981].

## Main results

* `Cslib.Complexity.NP_subset_AP`, `Cslib.Complexity.P_subset_AP`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **`NP ⊆ AP`**: the machine guessing and verifying a certificate, with every state labelled
existential, decides the problem within the same polynomial time bound. -/
theorem NP_subset_AP : NP enc ⊆ AP enc := by
  rintro A ⟨p, V, hV, hA⟩
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, -⟩ := hA.exists_decidesInTime hV
  refine ⟨_, .of_forall_le c d fun _ => le_rfl, k, State, hfinite, ⟨machine, fun _ => false⟩,
    fun a => ⟨(hdecides a).1, ?_⟩⟩
  rw [(hdecides a).2]
  exact (MultiTapeATM.accepts_iff_toNTM_accepts (atm := ⟨machine, fun _ => false⟩)
    (fun _ => rfl) (hdecides a).1).symm

/-- **`P ⊆ AP`**, through `NP`. -/
theorem P_subset_AP : P enc ⊆ AP enc :=
  P_subset_NP.trans NP_subset_AP

end Cslib.Complexity
