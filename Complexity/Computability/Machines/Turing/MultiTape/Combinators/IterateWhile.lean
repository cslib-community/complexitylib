/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- The newer version of cslib PR #1112 @0b9e55ce, which is on an older base.

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelIterateWhile
import Mathlib.Tactic.Ring

/-!
# Iterating a function while its result is non-empty

`tm.iterateWhile mark` applies `tm` to its input, then to the result, and so on, until `tm`
produces the empty word, and then outputs the last word before the empty one. `tm` is applied at
least once, so if it maps the input itself to the empty word, the output is the input. The
computation need not terminate.

The machine keeps the current word on one work tape and the next one on another. A round copies
the next word to the current tape (`Turing.MultiTapeTM.copyWord`) and computes the new next word
from it with `tm`. Rounds are repeated by `Turing.MultiTapeTM.repeatUntilBlank` until the next word
is empty.

## Main definitions

* `Turing.MultiTapeTM.iterateWhile`: the iterating machine.

## Main results

* `Turing.MultiTapeTM.computesTidily_iterateWhile`: if `tm` computes `w (n + 1)` from `w n` tidily
  for every `n ≤ r`, and `w (n + 1)` is empty exactly for `n = r`, then `tm.iterateWhile mark`
  computes `w r` from `w 0` tidily.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterateWhile`: if `f` is tidily computable,
  so is `a ↦ f^[r a] a`, where `r a` is the least `n` such that `f^[n + 1] a` has the empty
  encoding.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.iterateWhile`: the same, with bounds
  on the number of rounds and on the lengths of all intermediate values in terms of the length of
  the input.
-/

namespace Turing.MultiTapeTM

/-! ### Iterating a computable function -/

/-- If `f` is tidily computable, so is `a ↦ f^[r a] a`, where `r a` is the least `n` such that
`f^[n + 1] a` has the empty encoding. Each of the `r a + 1` rounds costs at most the largest time
of `f` on the values `f^[n] a` for `n ≤ r a` plus a term linear in their longest encoding; the
space is linear in the largest space of `f` on these values and their longest encoding. -/
public theorem ComputableTidilyInTimeAndSpace.iterateWhile {α : Type*} {f : α → α}
    {enc : α ↪ List Bool} {t s r : α → ℕ} (hf : ComputableTidilyInTimeAndSpace f enc enc t s)
    (hr : ∀ a, IsLeast {n | enc (f^[n + 1] a) = []} (r a)) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun a => f^[r a] a) enc enc
      (fun a => (r a + 1) * ((Finset.Iic (r a)).sup (fun n => t (f^[n] a)) +
        c * ((Finset.Iic (r a)).sup (fun n => (enc (f^[n] a)).length) + 1)))
      (fun a => c * ((Finset.Iic (r a)).sup (fun n => s (f^[n] a)) +
        (Finset.Iic (r a)).sup (fun n => (enc (f^[n] a)).length) + 1)) := by
  obtain ⟨k, State, _, tm, htm⟩ := hf
  refine ⟨2 * (k + 3) * (6 * k + 54) + (4 * k + 42), k + 1 + 2, _, inferInstance,
    tm.iterateWhile true, fun a => ?_⟩
  have h := computesTidily_iterateWhile (w := fun n => enc (f^[n] a)) (r := r a)
    (fun n hn => by
      simpa only [Function.iterate_succ_apply'] using TransformsTapes.mono (htm (f^[n] a))
        (Finset.le_sup (f := fun n => t (f^[n] a)) (Finset.mem_Iic.mpr hn))
        (Finset.le_sup (f := fun n => s (f^[n] a)) (Finset.mem_Iic.mpr hn)))
    (fun n hn => Finset.le_sup (f := fun n => (enc (f^[n] a)).length) (Finset.mem_Iic.mpr hn))
    (fun n hn hnil => absurd ((hr a).2 hnil) (by omega)) (hr a).1 true
  refine TransformsTapes.mono h ?_ ?_ <;> beta_reduce <;> ring_nf <;> omega

/-- If `f` is tidily computable in time `t` and space `s` of the length of its input, for monotone
`t` and `s`, so is `a ↦ f^[r a] a`, where `r a` is the least `n` such that `f^[n + 1] a` has the
empty encoding, provided that for inputs of length `n`, `r a ≤ ρ n` and the encodings of all
`f^[i] a` for `i ≤ r a` have length at most `l n`. -/
public theorem ComputableTidilyInTimeAndSpaceOfLength.iterateWhile {α : Type*} {f : α → α}
    {enc : α ↪ List Bool} {t s l ρ : ℕ → ℕ} {r : α → ℕ} (ht : Monotone t) (hs : Monotone s)
    (hf : ComputableTidilyInTimeAndSpaceOfLength f enc enc t s)
    (hr : ∀ a, IsLeast {n | enc (f^[n + 1] a) = []} (r a))
    (hρ : ∀ a, r a ≤ ρ (enc a).length)
    (hl : ∀ a, ∀ n ≤ r a, (enc (f^[n] a)).length ≤ l (enc a).length) :
    ∃ c, ComputableTidilyInTimeAndSpaceOfLength (fun a => f^[r a] a) enc enc
      (fun n => (ρ n + 1) * (t (l n) + c * (l n + 1))) (fun n => c * (s (l n) + l n + 1)) := by
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.iterateWhile hf hr
  refine ⟨c, h.mono (fun a => ?_) (fun a => ?_)⟩ <;> dsimp only <;> gcongr
  all_goals first
    | exact hρ a
    | refine Finset.sup_le fun n hn => ?_
      have := hl a n (Finset.mem_Iic.mp hn)
      first | exact this | exact ht this | exact hs this

end Turing.MultiTapeTM
