/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Closure
public import Complexity.Computability.Complexity.Reduction.ManyOne

/-!
# Parsimonious reductions and #P-completeness

A *parsimonious* reduction from a counting function `f : α → ℕ` to `g : β → ℕ` is a function
`r : α → β`, computable in polynomial time, that preserves counts exactly: `f a = g (r a)` for
every instance `a` [Valiant][Valiant1979], [Arora and Barak, Section 17.3][AroraBarak09]. A
counting function is `#P`-hard when every function in `#P`, with any encoding of its instances,
reduces to it parsimoniously, and `#P`-complete when it also belongs to `#P`.

Parsimonious reductions compose (`ParsimoniousReducible.trans`) and `#P` is closed under them
(`ParsimoniousReducible.mem_SharpP`, from exact-count precomposition `SharpP.comp_mem`).

## Main definitions

* `Cslib.Complexity.ParsimoniousReducible`: parsimonious polynomial-time reductions.
* `Cslib.Complexity.SharpPHard`, `Cslib.Complexity.SharpPComplete`.

## Main results

* `Cslib.Complexity.ParsimoniousReducible.refl`, `Cslib.Complexity.ParsimoniousReducible.trans`:
  parsimonious reducibility is a preorder.
* `Cslib.Complexity.ParsimoniousReducible.mem_SharpP`: `#P` is closed under parsimonious
  reductions.
* `Cslib.Complexity.SharpPHard.trans`: hardness transfers along parsimonious reductions.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type}

/-- `f` reduces parsimoniously to `g`: some `r`, computable in polynomial time with respect to
`encA` and `encB`, satisfies `f a = g (r a)` for every `a`. -/
def ParsimoniousReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (f : α → ℕ)
    (g : β → ℕ) : Prop :=
  ∃ r : α → β, ComputableInPolyTime r encA encB ∧ ∀ a, f a = g (r a)

/-- Every function in `#P`, with any encoding of its instances, reduces parsimoniously to `g`. This
is `HardUnder` for `ParsimoniousReducible`. -/
def SharpPHard (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  HardUnder (fun enc => ParsimoniousReducible enc encB) @SharpP g

/-- `g` is in `#P` and every function in `#P` reduces parsimoniously to it. This is `CompleteUnder`
for `ParsimoniousReducible` (`sharpPComplete_iff_completeUnder`), with its second conjunct stated as
`SharpPHard`. -/
def SharpPComplete (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  g ∈ SharpP encB ∧ SharpPHard encB g

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}

/-- `#P`-hardness is hardness for `#P` under `ParsimoniousReducible`. -/
theorem sharpPHard_iff_hardUnder :
    SharpPHard encB g ↔ HardUnder (fun enc => ParsimoniousReducible enc encB) @SharpP g :=
  Iff.rfl

/-- `#P`-completeness is completeness for `#P` under `ParsimoniousReducible`. -/
theorem sharpPComplete_iff_completeUnder :
    SharpPComplete encB g ↔
      CompleteUnder (fun enc => ParsimoniousReducible enc encB) @SharpP encB g :=
  Iff.rfl

/-- Every counting function reduces parsimoniously to itself by the identity function. -/
@[refl]
theorem ParsimoniousReducible.refl (encA : α ↪ List Bool) (f : α → ℕ) :
    ParsimoniousReducible encA encA f f :=
  ⟨id, ComputableInPolyTime.id', fun _ => rfl⟩

/-- Parsimonious reductions compose. -/
@[trans]
theorem ParsimoniousReducible.trans (hfg : ParsimoniousReducible encA encB f g)
    (hgh : ParsimoniousReducible encB encC g h) : ParsimoniousReducible encA encC f h :=
  let ⟨r, hr, hfg⟩ := hfg
  let ⟨s, hs, hgh⟩ := hgh
  ⟨s ∘ r, hs.comp hr, fun a => (hfg a).trans (hgh (r a))⟩

/-- **`#P` is closed under parsimonious reductions.** -/
theorem ParsimoniousReducible.mem_SharpP (hfg : ParsimoniousReducible encA encB f g)
    (hg : g ∈ SharpP encB) : f ∈ SharpP encA := by
  obtain ⟨r, hr, hfg⟩ := hfg
  have h := SharpP.comp_mem hg hr
  rwa [show g ∘ r = f from funext fun a => (hfg a).symm] at h

/-- `#P`-hardness transfers along a parsimonious reduction. -/
theorem SharpPHard.trans (hg : SharpPHard encB g) (hgh : ParsimoniousReducible encB encC g h) :
    SharpPHard encC h :=
  HardUnder.trans (fun _ _ h h' => h.trans h') hg hgh

end Cslib.Complexity
