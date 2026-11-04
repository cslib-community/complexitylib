/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Computable.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime

/-!
# Computable functions and decidable sets

A function is computable (`Turing.MultiTapeTM.IsComputable`) when it is computable within some
bounds in the sense of cslib's `Turing.MultiTapeTM.ComputableInTimeAndSpace`: some machine with a
binary alphabet and finitely many states halts on every encoded input with the encoded value. The
bounds are arbitrary, so this is computability by a total machine
(`Turing.MultiTapeTM.isComputable_iff`). A set is decidable (`Turing.MultiTapeTM.IsDecidable`) when
it is decidable within some bounds in the sense of `Turing.MultiTapeTM.DecidableInTimeAndSpace`,
that is, when its Boolean indicator is computable.

Computable functions compose (`Turing.MultiTapeTM.IsComputable.comp`): both machines are first put
into the tidy normal form
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`), whose
machines compose. Functions computable within bounds in the senses of
`Turing.MultiTapeTM.ComputableInTimeAndSpace`, `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace`,
`Turing.MultiTapeTM.ComputableTidilyInDegree` and
`Turing.MultiTapeTM.ComputableTidilyInPolyTime` are computable (their `.isComputable` lemmas), and
decidable sets are closed under complement.

These are the decidable sets of [Sipser, Definition 3.6][Sipser2013], for the library's native
multi-tape machines. Mathlib's `ComputablePred` is the analogous notion for its partial recursive
functions; `Turing.MultiTapeTM.IsComputable.computable` and
`Turing.MultiTapeTM.IsDecidable.computablePred` in `MultiTape.Halting.Partrec` connect the two
models.

## Main definitions

* `Turing.MultiTapeTM.IsComputable`: computability by a total machine.
* `Turing.MultiTapeTM.IsDecidable`: decidability by a total machine.

## Main results

* `Turing.MultiTapeTM.isComputable_iff`: computability is the existence of a machine computing the
  function without bounds.
* `Turing.MultiTapeTM.IsComputable.comp`, `.prod`, `Turing.MultiTapeTM.isComputable_id`,
  `Turing.MultiTapeTM.IsComputable.of_finite`: closure properties.
* `Turing.MultiTapeTM.isDecidable_iff`: decidability through any computable Boolean function.
* `Turing.MultiTapeTM.IsDecidable.compl`: decidable sets are closed under complement.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

universe u

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-! ### Computable functions -/

/-- Functions tidily computable within bounds are computable. -/
theorem ComputableTidilyInTimeAndSpace.isComputable {f : α → β} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encMid t s) : IsComputable f encIn encMid :=
  h.computableInTimeAndSpace.isComputable

/-- Functions tidily computable within bounds of given degrees are computable. -/
theorem ComputableTidilyInDegree.isComputable {f : α → β} {d e : ℕ}
    (h : ComputableTidilyInDegree f encIn encMid d e) : IsComputable f encIn encMid :=
  let ⟨⟨_, _, _, _, h⟩, _⟩ := h
  h.isComputable

/-- Functions tidily computable in polynomial time are computable. -/
theorem ComputableTidilyInPolyTime.isComputable {f : α → β}
    (h : ComputableTidilyInPolyTime f encIn encMid) : IsComputable f encIn encMid :=
  let ⟨_, _, _, _, h⟩ := h
  h.isComputable

/-- A computable function is tidily computable within some bounds. -/
theorem IsComputable.exists_computableTidilyInTimeAndSpace {f : α → β}
    (h : IsComputable f encIn encMid) :
    ∃ t s : α → ℕ, ComputableTidilyInTimeAndSpace f encIn encMid t s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, h⟩ := h.exists_computableTidilyInTimeAndSpace
  ⟨_, _, h⟩

/-- **Computable functions compose.** -/
theorem IsComputable.comp {f : β → γ} {g : α → β} (hf : IsComputable f encMid encOut)
    (hg : IsComputable g encIn encMid) : IsComputable (f ∘ g) encIn encOut :=
  let ⟨_, _, hf⟩ := hf.exists_computableTidilyInTimeAndSpace
  let ⟨_, _, hg⟩ := hg.exists_computableTidilyInTimeAndSpace
  let ⟨_, h⟩ := hf.computableInTimeAndSpace_comp hg
  h.isComputable

/-- The identity is computable. -/
theorem isComputable_id (enc : α ↪ List Bool) : IsComputable id enc enc :=
  (ComputableTidilyInDegree.of_eq fun _ => rfl).isComputable

/-- Functions on finite types are computable. -/
theorem IsComputable.of_finite [Finite α] (f : α → β) : IsComputable f encIn encMid :=
  (ComputableTidilyInDegree.of_finite f).isComputable

/-- Pairs of computable functions are computable. -/
theorem IsComputable.prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : IsComputable f encIn enc₁) (hg : IsComputable g encIn enc₂) :
    IsComputable (fun a => (f a, g a)) encIn enc :=
  let ⟨_, _, hf⟩ := hf.exists_computableTidilyInTimeAndSpace
  let ⟨_, _, hg⟩ := hg.exists_computableTidilyInTimeAndSpace
  let ⟨_, h⟩ := PairEncoding.pair_mono hf.computableInTimeAndSpace hg.computableInTimeAndSpace
  h.isComputable

/-! ### Decidable sets -/

/-- `L` is decidable with respect to the encoding `enc`: its Boolean indicator is computable, by a
machine with a binary alphabet and finitely many states within some time and space bounds. -/
def IsDecidable (L : Set α) (enc : α ↪ List Bool) : Prop :=
  ∃ t s : α → ℕ, DecidableInTimeAndSpace L enc t s

variable {L : Set α} {enc : α ↪ List Bool}

/-- A set is decidable exactly when its Boolean indicator is computable. -/
theorem isDecidable_iff_isComputable_indicator :
    IsDecidable L enc ↔ IsComputable (indicator L) enc encBool :=
  Iff.rfl

/-- **A set is decidable exactly when some computable Boolean function decides membership.** -/
theorem isDecidable_iff :
    IsDecidable L enc ↔ ∃ f : α → Bool, IsComputable f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true := by
  classical
  rw [isDecidable_iff_isComputable_indicator]
  refine ⟨fun h => ⟨_, h, fun a => by simp [indicator]⟩, fun ⟨f, hf, hL⟩ => ?_⟩
  convert hf using 1
  funext a
  by_cases ha : a ∈ L <;> simp only [indicator, ha, ↓reduceIte]
  · exact ((hL a).mp ha).symm
  · exact (Bool.not_eq_true _).mp (mt (hL a).mpr ha) |>.symm

/-- Membership in a decidable set is decided by a computable Boolean function. -/
theorem IsDecidable.exists_isComputable (h : IsDecidable L enc) :
    ∃ f : α → Bool, IsComputable f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true :=
  isDecidable_iff.mp h

/-- **Decidable sets are closed under complement.** -/
theorem IsDecidable.compl (h : IsDecidable L enc) : IsDecidable Lᶜ enc :=
  let ⟨f, hf, hL⟩ := h.exists_isComputable
  isDecidable_iff.mpr ⟨fun a => !f a, (IsComputable.of_finite (fun b : Bool => !b)).comp hf,
    fun a => by simp [hL a]⟩

@[simp]
theorem isDecidable_compl_iff : IsDecidable Lᶜ enc ↔ IsDecidable L enc :=
  ⟨fun h => compl_compl L ▸ h.compl, IsDecidable.compl⟩

end Turing.MultiTapeTM
