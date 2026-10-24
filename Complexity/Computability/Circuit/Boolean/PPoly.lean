/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (redo of the withdrawn cslib PR #1100, without frame encodings;
-- needs #1067 and `PolynomialBound/Closure`)

public import Complexity.Computability.Circuit.Boolean.Synthesis
public import Complexity.Computability.Languages.Slice
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# P/poly

A language over `Bool` is in `P/poly` when it has circuits of polynomial size: for every input
length `n`, a circuit over the De Morgan basis computing the slice of the language at `n`
(`Language.slice`), with size bounded by a polynomially bounded function of `n`
[Arora and Barak, Definition 6.5][AroraBarak09]. There is no requirement that the circuits for
different lengths be related, so `P/poly` contains undecidable languages.

`PPoly` is defined through the minimal circuit size of each slice (`Cslib.Circuits.complexity`);
`mem_PPoly_iff_exists_circuits` is the textbook formulation with an explicit family of circuits.
Size counts gates, constants included, which changes sizes by at most a constant factor and so does
not change the class.

## Main definitions

* `Cslib.Circuits.Boolean.SIZE`: the languages with circuits of size at most `s n` at each length.
* `Cslib.Circuits.Boolean.PPoly`.

## Main results

* `Cslib.Circuits.Boolean.mem_PPoly_iff_exists_circuits`: the formulation with circuit families.
* `Cslib.Circuits.Boolean.mem_PPoly_iff_exists_mem_SIZE`: `P/poly` is the union of the classes
  `SIZE (c (n + 1) ^ c)`.
* `Cslib.Circuits.Boolean.PPoly.of_synthesis`: languages whose slices are synthesised within a
  polynomial budget are in `P/poly`.
* `Cslib.Circuits.Boolean.PPoly.compl`, `PPoly.sup`, `PPoly.inf`: closure under the Boolean
  operations.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The languages over `Bool` that have, for every input length `n`, a circuit of size at most
`s n` [Arora and Barak, Definition 6.2][AroraBarak09]. Size counts gates
(`Cslib.Circuits.Circuit.size`), while Arora and Barak count all vertices, inputs included, so
`SIZE s` is their `SIZE (s + n)` up to the output vertex. -/
def SIZE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, complexity interpretation (single (L.slice n)) ≤ s n}

/-- `SIZE` is monotone in the size bound. -/
theorem SIZE_mono : Monotone SIZE := fun _ _ h _ hL n => (hL n).trans (h n)

/-- The languages over `Bool` whose slices have circuits of polynomial size. -/
def PPoly : Set (Language Bool) :=
  {L | PolynomiallyBounded fun n => complexity interpretation (single (L.slice n))}

/-- A language is in `P/poly` if and only if the circuit complexity of its slices is polynomially
bounded. -/
theorem mem_PPoly {L : Language Bool} :
    L ∈ PPoly ↔ PolynomiallyBounded fun n => complexity interpretation (single (L.slice n)) :=
  Iff.rfl

/-- **P/poly with circuit families.** A language is in `P/poly` exactly when it has a family of
circuits, one for each input length, whose sizes are polynomially bounded. -/
theorem mem_PPoly_iff_exists_circuits {L : Language Bool} :
    L ∈ PPoly ↔ ∃ (C : ∀ n, Circuit signature n 1) (p : ℕ → ℕ), PolynomiallyBounded p ∧
      ∀ n, (C n).size ≤ p n ∧ (C n).Computes interpretation (single (L.slice n)) := by
  constructor
  · intro hL
    choose C hC hsize using fun n =>
      exists_computes_size_eq_complexity (I := interpretation) (f := single (L.slice n))
    exact ⟨C, _, hL, fun n => ⟨(hsize n).le, hC n⟩⟩
  · rintro ⟨C, p, hp, hC⟩
    exact hp.mono_of_le fun n => (complexity_le_of_computes (C n) (hC n).2).trans (hC n).1

/-- `P/poly` is the union of the classes `SIZE (c (n + 1) ^ c)`. -/
theorem mem_PPoly_iff_exists_mem_SIZE {L : Language Bool} :
    L ∈ PPoly ↔ ∃ c, L ∈ SIZE fun n => c * (n + 1) ^ c := by
  rw [mem_PPoly, polynomiallyBounded_iff_le]
  constructor
  · rintro ⟨c, d, h⟩
    refine ⟨max c d, fun n => (h n).trans ?_⟩
    exact Nat.mul_le_mul (le_max_left c d)
      (Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_right c d))
  · rintro ⟨c, h⟩
    exact ⟨c, c, h⟩

namespace PPoly

variable {L M : Language Bool}

/-- A language whose slices are synthesised from the inputs within a polynomial budget is in
`P/poly`. -/
theorem of_synthesis {cost : ℕ → ℕ} (hcost : PolynomiallyBounded cost)
    (h : ∀ n, Synthesis interpretation (inputs n) {L.slice n} (cost n)) : L ∈ PPoly :=
  hcost.mono_of_le fun n => (h n).complexity_le

/-- A language whose slices are constant is in `P/poly`. -/
theorem of_slice_const (b : ℕ → Bool) (h : ∀ n x, L.slice n x = b n) : L ∈ PPoly :=
  of_synthesis (PolynomiallyBounded.const 1) fun n => Synthesis.of_forall_eq_const _ (h n)

/-- The empty language is in `P/poly`. -/
theorem zero_mem : (0 : Language Bool) ∈ PPoly :=
  of_slice_const (fun _ => false) fun _ _ => Language.slice_zero

/-- The universal language is in `P/poly`. -/
theorem top_mem : (⊤ : Language Bool) ∈ PPoly :=
  of_slice_const (fun _ => true) fun _ _ => Language.slice_top

/-- `P/poly` is closed under complement. -/
theorem compl (hL : L ∈ PPoly) : Lᶜ ∈ PPoly := by
  refine (hL.add (PolynomiallyBounded.const 1)).mono_of_le fun n => ?_
  have : Lᶜ.slice n = fun x => !L.slice n x := funext fun _ => Language.slice_compl
  simpa [this] using complexity_not_le (L.slice n)

/-- `P/poly` is closed under union. -/
theorem sup (hL : L ∈ PPoly) (hM : M ∈ PPoly) : L ⊔ M ∈ PPoly := by
  refine ((hL.add hM).add (PolynomiallyBounded.const 1)).mono_of_le fun n => ?_
  have : (L ⊔ M).slice n = fun x => L.slice n x || M.slice n x :=
    funext fun _ => Language.slice_sup
  simpa [this] using complexity_or_le (L.slice n) (M.slice n)

/-- `P/poly` is closed under intersection. -/
theorem inf (hL : L ∈ PPoly) (hM : M ∈ PPoly) : L ⊓ M ∈ PPoly := by
  refine ((hL.add hM).add (PolynomiallyBounded.const 1)).mono_of_le fun n => ?_
  have : (L ⊓ M).slice n = fun x => L.slice n x && M.slice n x :=
    funext fun _ => Language.slice_inf
  simpa [this] using complexity_and_le (L.slice n) (M.slice n)

end PPoly

end Cslib.Circuits.Boolean
