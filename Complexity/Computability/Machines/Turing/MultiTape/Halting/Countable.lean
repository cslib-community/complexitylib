/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Computable
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity

/-!
# There are countably many decidable sets

A machine with finitely many states is determined, up to renaming its states, by its description
(`Turing.MultiTapeTM.Universal.desc`), and descriptions are encoded injectively as bit words
(`Turing.MultiTapeTM.Universal.eDesc`). A set decidable by a machine is the set of inputs on which
the described machine halts with output `[true]`, so it is determined by a description, and there
are countably many decidable sets (`Turing.MultiTapeTM.countable_setOf_isDecidable`).

## Main results

* `Turing.MultiTapeTM.computes_true_iff`: a machine deciding a set halts with output `[true]`
  exactly on its members.
* `Turing.MultiTapeTM.countable_setOf_isDecidable`: there are countably many decidable sets, for
  every encoding.
-/

public section

namespace Turing.MultiTapeTM

open Universal

variable {α : Type*} {enc : α ↪ List Bool}

/-- A machine computing a Boolean function `f` halts with output `[true]` exactly where `f` is
`true`. -/
theorem computes_true_iff {k : ℕ} {State : Type*} {tm : MultiTapeTM k Bool State} {f : α → Bool}
    (htm : ∀ a, tm.Computes (enc a) [f a]) (a : α) : tm.Computes (enc a) [true] ↔ f a = true :=
  ⟨fun h => List.singleton_inj.mp (h.unique (htm a)) |>.symm, fun h => h ▸ htm a⟩

/-- **There are countably many decidable sets**: a decidable set is the set of inputs on which the
machine of some description halts with output `[true]`. -/
theorem countable_setOf_isDecidable (enc : α ↪ List Bool) :
    {A : Set α | IsDecidable A enc}.Countable := by
  have : Countable Desc := eDesc.injective.countable
  refine (Set.countable_range fun d : Desc =>
    {a | d.Computes ((enc a).map eBit) [eBit true]}).mono fun A hA => ?_
  obtain ⟨f, ⟨_, _, k, State, hfinite, tm, htm⟩, hA⟩ := isDecidable_iff.mp hA
  have := Fintype.ofFinite State
  refine ⟨desc ((Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding) eBit tm, ?_⟩
  ext a
  rw [Set.mem_ofPred_eq, ← List.map_singleton, Desc.computes_desc,
    computes_true_iff (fun a => (htm a).1), hA]

end Turing.MultiTapeTM
