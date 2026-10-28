/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Bounds up to constants on plain machines

`Turing.MultiTapeTM.ComputableInO`, computability within time `O(T a)` and space `O(S a)` by any
machine, agrees with its tidy counterpart `Turing.MultiTapeTM.ComputableTidilyInO`, with the same
bounds. A tidy machine is a machine, with the same bounds. Conversely, the tidy normal form makes a
machine within time `t` and space `s` tidy within time `2 t + 3 s + c` and space `c (s + 1)`
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`). A machine
within time `t` visits at most `k t + k` work-tape cells, where `k` is its number of work tapes, so
the space in the time bound may be replaced by the time: the overhead is a constant factor in each
bound separately (`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInO`), which the
notion absorbs.

Proofs switch between the notions with `Turing.MultiTapeTM.ComputableInO.tidy` and
`Turing.MultiTapeTM.ComputableInO.of_tidy`.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInO`: a machine within time `t` and
  space `s` whose values fit in space `s` gives tidy computability within time `O(t)` and space
  `O(s)`.
* `Turing.MultiTapeTM.computableInO_iff_computableTidilyInO`: the plain and tidy notions agree,
  with the shortcuts `Turing.MultiTapeTM.ComputableInO.tidy`,
  `Turing.MultiTapeTM.ComputableInO.of_tidy` and
  `Turing.MultiTapeTM.ComputableTidilyInO.computableInO`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-! ### Plain bounds are tidy bounds up to constants -/

/-- **Plain bounds are tidy bounds up to constant factors.** A function computable within time `t`
and space `s`, whose encoded values fit in space `s`, is tidily computable within time `O(t)` and
space `O(s)`. -/
theorem ComputableInTimeAndSpace.computableTidilyInO {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (hl : ∀ a, (encOut (f a)).length ≤ s a) :
    ComputableTidilyInO f encIn encOut t s := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  -- the machine also runs within space `k t + k`, so the smaller of the two space bounds holds
  have hmin : ComputableInTimeAndSpace f encIn encOut t fun a => min (s a) (k * t a + k) :=
    ⟨k, State, hfin, tm, fun a => by
      dsimp only
      rcases min_cases (s a) (k * t a + k) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he]
      exacts [htm a, (htm a).space_linear]⟩
  obtain ⟨d, hd⟩ := hmin.exists_computableTidilyInTimeAndSpace
  refine ⟨3 * k + d + 2, hd.mono (fun a => ?_) (fun a => ?_), fun a => ?_⟩
  · have := min_le_right (s a) (k * t a + k)
    nlinarith
  · have := min_le_left (s a) (k * t a + k)
    nlinarith
  · have := hl a
    nlinarith

/-! ### Plain and tidy bounds up to constants -/

variable {T S : α → ℕ}

/-- **Plain and tidy computability within bounds up to constants agree.** -/
theorem computableInO_iff_computableTidilyInO :
    ComputableInO f encIn encOut T S ↔ ComputableTidilyInO f encIn encOut T S :=
  ⟨ComputableInO.tidy, ComputableInO.of_tidy⟩

end Turing.MultiTapeTM
