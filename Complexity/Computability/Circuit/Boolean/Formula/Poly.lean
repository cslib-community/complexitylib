/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula.Restriction
public import Complexity.Computability.Languages.Slice
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Formula-Size Complexity Classes (`Formula[s]` and `Formula[poly]`)

A language over `Bool` lies in `FormulaSIZE s` (`Formula[s]` in
[Oliveira and Santhanam, Sections 1.2 and 3.1][OliveiraSanthanam2018]) when for every input length
`n`, its `n`-bit slice (`Language.slice`) has a De Morgan formula of leaf size at most `s n`
(`Cslib.Circuits.Boolean.formulaSize`) [Jukna, Chapter 6][Jukna2012]. It lies in `FormulaPoly`
(`Formula[poly]`) when the formula leaf size of its `n`-bit slice is polynomially bounded in `n`.

For decision problems over an arbitrary type `α` with encoding `enc : α ↪ List Bool`,
`FormulaSIZEOn enc s` and `FormulaPolyOn enc` are the classes of problems whose image under `enc`
agrees with a language in `FormulaSIZE s` or `FormulaPoly`, respectively, mirroring `PPoly` and
`PPolyOn` (`Complexity.Computability.Circuit.Boolean.PPoly`).

## Main definitions

* `Cslib.Circuits.Boolean.FormulaSIZE`: languages with De Morgan formulas of leaf size at most
  `s n` at each input length `n`.
* `Cslib.Circuits.Boolean.FormulaPoly`: languages over `Bool` with De Morgan formulas of polynomial
  leaf size.
* `Cslib.Circuits.Boolean.FormulaSIZEOn`, `Cslib.Circuits.Boolean.FormulaPolyOn`: problems with De
  Morgan formulas of leaf size `s` or polynomial leaf size under an encoding `enc`.

## Main results

* `Cslib.Circuits.Boolean.formulaSize_not`, `Cslib.Circuits.Boolean.formulaSize_and_le`,
  `Cslib.Circuits.Boolean.formulaSize_or_le`: leaf-size bounds for Boolean operations on functions.
* `Cslib.Circuits.Boolean.FormulaSIZE_mono`: monotonicity of `FormulaSIZE`.
* `Cslib.Circuits.Boolean.mem_FormulaPoly_iff_exists_formulas`: characterization of `FormulaPoly` by
  explicit formula families.
* `Cslib.Circuits.Boolean.mem_FormulaPoly_iff_exists_mem_FormulaSIZE`: `FormulaPoly` is the union of
  `FormulaSIZE (fun n => c * (n + 1) ^ c)`.
* `Cslib.Circuits.Boolean.FormulaPoly.compl`, `Cslib.Circuits.Boolean.FormulaPoly.sup`,
  `Cslib.Circuits.Boolean.FormulaPoly.inf`: closure of `FormulaPoly` under the Boolean operations.
* `Cslib.Circuits.Boolean.mem_FormulaSIZEOn_encBits_iff`,
  `Cslib.Circuits.Boolean.mem_FormulaPolyOn_encBits_iff`,
  `Cslib.Circuits.Boolean.FormulaPolyOn.compl`: agreement on `encBits` and closure under complement.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Formula

variable {n : ℕ}

/-- Negating a Boolean function does not increase its De Morgan formula leaf size. -/
theorem formulaSize_not_le (f : BooleanFunction n) :
    formulaSize (fun x => !f x) ≤ formulaSize f := by
  obtain ⟨F, hF, hL⟩ := exists_computes_leafSize_eq f
  have hnot : F.not.Computes interpretation (fun x => !f x) := fun x => by
    rw [eval_not, hF]
  exact (formulaSize_le hnot).trans (by rw [leafSize_not, hL])

/-- Negating a Boolean function preserves its De Morgan formula leaf size. -/
@[simp] theorem formulaSize_not (f : BooleanFunction n) :
    formulaSize (fun x => !f x) = formulaSize f := by
  refine le_antisymm (formulaSize_not_le f) ?_
  have h := formulaSize_not_le (fun x => !f x)
  simpa only [Bool.not_not] using h

/-- The De Morgan formula leaf size of a conjunction is at most the sum of the leaf sizes of its
conjuncts. -/
theorem formulaSize_and_le (f g : BooleanFunction n) :
    formulaSize (fun x => f x && g x) ≤ formulaSize f + formulaSize g := by
  obtain ⟨F, hF, hFL⟩ := exists_computes_leafSize_eq f
  obtain ⟨G, hG, hGL⟩ := exists_computes_leafSize_eq g
  have hand : (F.and G).Computes interpretation (fun x => f x && g x) := fun x => by
    rw [eval_and, hF, hG]
  exact (formulaSize_le hand).trans (by rw [leafSize_and, hFL, hGL])

/-- The De Morgan formula leaf size of a disjunction is at most the sum of the leaf sizes of its
disjuncts. -/
theorem formulaSize_or_le (f g : BooleanFunction n) :
    formulaSize (fun x => f x || g x) ≤ formulaSize f + formulaSize g := by
  obtain ⟨F, hF, hFL⟩ := exists_computes_leafSize_eq f
  obtain ⟨G, hG, hGL⟩ := exists_computes_leafSize_eq g
  have hor : (F.or G).Computes interpretation (fun x => f x || g x) := fun x => by
    rw [eval_or, hF, hG]
  exact (formulaSize_le hor).trans (by rw [leafSize_or, hFL, hGL])

/-- The languages over `Bool` that have, for every input length `n`, a De Morgan formula of leaf
size at most `s n` (`Formula[s]` in [OliveiraSanthanam2018, Sections 1.2 and 3.1]). -/
def FormulaSIZE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, formulaSize (L.slice n) ≤ s n}

/-- `FormulaSIZE` is monotone in the leaf-size bound. -/
theorem FormulaSIZE_mono : Monotone FormulaSIZE := fun _ _ h _ hL n => (hL n).trans (h n)

/-- The languages over `Bool` whose slices have De Morgan formulas of polynomial leaf size
(`Formula[poly]` in [OliveiraSanthanam2018, Sections 1.2 and 3.1]). -/
def FormulaPoly : Set (Language Bool) :=
  {L | PolynomiallyBounded fun n => formulaSize (L.slice n)}

/-- A language is in `FormulaPoly` if and only if the formula leaf size of its slices is
polynomially bounded. -/
theorem mem_FormulaPoly {L : Language Bool} :
    L ∈ FormulaPoly ↔ PolynomiallyBounded fun n => formulaSize (L.slice n) :=
  Iff.rfl

/-- **`FormulaPoly` with formula families.** A language is in `FormulaPoly` exactly when it has a
family of De Morgan formulas, one for each input length, whose leaf sizes are polynomially
bounded. -/
theorem mem_FormulaPoly_iff_exists_formulas {L : Language Bool} :
    L ∈ FormulaPoly ↔ ∃ (F : ∀ n, Formula signature n) (p : ℕ → ℕ), PolynomiallyBounded p ∧
      ∀ n, (F n).leafSize ≤ p n ∧ (F n).Computes interpretation (L.slice n) := by
  constructor
  · intro hL
    choose F hF hsize using fun n => exists_computes_leafSize_eq (L.slice n)
    exact ⟨F, _, hL, fun n => ⟨(hsize n).le, hF n⟩⟩
  · rintro ⟨F, p, hp, hF⟩
    exact hp.mono_of_le fun n => (formulaSize_le (hF n).2).trans (hF n).1

/-- `FormulaPoly` is the union of the classes `FormulaSIZE (fun n => c * (n + 1) ^ c)`. -/
theorem mem_FormulaPoly_iff_exists_mem_FormulaSIZE {L : Language Bool} :
    L ∈ FormulaPoly ↔ ∃ c, L ∈ FormulaSIZE fun n => c * (n + 1) ^ c := by
  rw [mem_FormulaPoly, polynomiallyBounded_iff_le]
  constructor
  · rintro ⟨c, d, h⟩
    refine ⟨max c d, fun n => (h n).trans ?_⟩
    exact Nat.mul_le_mul (le_max_left c d)
      (Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_right c d))
  · rintro ⟨c, h⟩
    exact ⟨c, c, h⟩

namespace FormulaPoly

variable {L M : Language Bool}

/-- A language whose slices are constant is in `FormulaPoly`. -/
theorem of_slice_const (b : ℕ → Bool) (h : ∀ n x, L.slice n x = b n) : L ∈ FormulaPoly := by
  refine (PolynomiallyBounded.const 0).mono_of_le fun n => ?_
  have heq : L.slice n = fun _ => b n := funext (h n)
  rw [heq, formulaSize_const]

/-- The empty language is in `FormulaPoly`. -/
theorem zero_mem : (0 : Language Bool) ∈ FormulaPoly :=
  of_slice_const (fun _ => false) fun _ _ => Language.slice_zero

/-- The universal language is in `FormulaPoly`. -/
theorem top_mem : (⊤ : Language Bool) ∈ FormulaPoly :=
  of_slice_const (fun _ => true) fun _ _ => Language.slice_top

/-- `FormulaPoly` is closed under complement. -/
theorem compl (hL : L ∈ FormulaPoly) : Lᶜ ∈ FormulaPoly := by
  refine hL.mono_of_le fun n => ?_
  have : Lᶜ.slice n = fun x => !L.slice n x := funext fun _ => Language.slice_compl
  rw [this, formulaSize_not]

/-- `FormulaPoly` is closed under union. -/
theorem sup (hL : L ∈ FormulaPoly) (hM : M ∈ FormulaPoly) : L ⊔ M ∈ FormulaPoly := by
  refine (hL.add hM).mono_of_le fun n => ?_
  have : (L ⊔ M).slice n = fun x => L.slice n x || M.slice n x :=
    funext fun _ => Language.slice_sup
  rw [this]
  exact formulaSize_or_le (L.slice n) (M.slice n)

/-- `FormulaPoly` is closed under intersection. -/
theorem inf (hL : L ∈ FormulaPoly) (hM : M ∈ FormulaPoly) : L ⊓ M ∈ FormulaPoly := by
  refine (hL.add hM).mono_of_le fun n => ?_
  have : (L ⊓ M).slice n = fun x => L.slice n x && M.slice n x :=
    funext fun _ => Language.slice_inf
  rw [this]
  exact formulaSize_and_le (L.slice n) (M.slice n)

end FormulaPoly

/-- **Problems with De Morgan formulas of leaf size `s`.** A decision problem `A : Set α`, with
encoding `enc : α ↪ List Bool` of its instances, lies in `FormulaSIZEOn enc s` when some language
`L ∈ FormulaSIZE s` agrees with `A` along `enc`. -/
def FormulaSIZEOn {α : Type*} (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ L ∈ FormulaSIZE s, ∀ a, a ∈ A ↔ enc a ∈ L}

/-- Membership in `FormulaSIZEOn enc s` unfolds to agreement with a language in `FormulaSIZE s`. -/
theorem mem_FormulaSIZEOn {α : Type*} {enc : α ↪ List Bool} {s : ℕ → ℕ} {A : Set α} :
    A ∈ FormulaSIZEOn enc s ↔ ∃ L ∈ FormulaSIZE s, ∀ a, a ∈ A ↔ enc a ∈ L :=
  Iff.rfl

/-- Over bitstrings (`encBits`), membership in `FormulaSIZEOn encBits s` is membership in
`FormulaSIZE s`. -/
@[simp]
theorem mem_FormulaSIZEOn_encBits_iff {s : ℕ → ℕ} {A : Language Bool} :
    (A : Set (List Bool)) ∈ FormulaSIZEOn Turing.MultiTapeTM.encBits s ↔ A ∈ FormulaSIZE s :=
  ⟨fun ⟨L, hL, h⟩ => (Language.ext fun w => h w : A = L) ▸ hL,
    fun hA => ⟨A, hA, fun _ => Iff.rfl⟩⟩

/-- **Problems with De Morgan formulas of polynomial leaf size.** A decision problem `A : Set α`,
with encoding `enc : α ↪ List Bool` of its instances, lies in `FormulaPolyOn enc` when some
language `L ∈ FormulaPoly` agrees with `A` along `enc`. -/
def FormulaPolyOn {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ L ∈ FormulaPoly, ∀ a, a ∈ A ↔ enc a ∈ L}

/-- A problem is in `FormulaPolyOn enc` if and only if some language in `FormulaPoly` agrees with it
along `enc`. -/
theorem mem_FormulaPolyOn {α : Type*} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ FormulaPolyOn enc ↔ ∃ L ∈ FormulaPoly, ∀ a, a ∈ A ↔ enc a ∈ L :=
  Iff.rfl

/-- `FormulaPolyOn enc` is the union of `FormulaSIZEOn enc (fun n => c * (n + 1) ^ c)`. -/
theorem mem_FormulaPolyOn_iff_exists_mem_FormulaSIZEOn {α : Type*} {enc : α ↪ List Bool}
    {A : Set α} :
    A ∈ FormulaPolyOn enc ↔ ∃ c, A ∈ FormulaSIZEOn enc fun n => c * (n + 1) ^ c := by
  simp only [mem_FormulaPolyOn, mem_FormulaSIZEOn, mem_FormulaPoly_iff_exists_mem_FormulaSIZE]
  exact ⟨fun ⟨L, ⟨c, hc⟩, h⟩ => ⟨c, L, hc, h⟩, fun ⟨c, L, hc, h⟩ => ⟨L, ⟨c, hc⟩, h⟩⟩

/-- Over bitstrings (`encBits`), membership in `FormulaPolyOn encBits` is membership in
`FormulaPoly`. -/
@[simp]
theorem mem_FormulaPolyOn_encBits_iff {A : Language Bool} :
    (A : Set (List Bool)) ∈ FormulaPolyOn Turing.MultiTapeTM.encBits ↔ A ∈ FormulaPoly :=
  ⟨fun ⟨L, hL, h⟩ => (Language.ext fun w => h w : A = L) ▸ hL,
    fun hA => ⟨A, hA, fun _ => Iff.rfl⟩⟩

/-- `FormulaPolyOn` is closed under complement. -/
theorem FormulaPolyOn.compl {α : Type*} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ FormulaPolyOn enc) : Aᶜ ∈ FormulaPolyOn enc := by
  obtain ⟨L, hL, h⟩ := hA
  exact ⟨Lᶜ, FormulaPoly.compl hL, fun a => not_congr (h a)⟩

/-- A complement lies in `FormulaPolyOn enc` if and only if the problem does. -/
@[simp]
theorem compl_mem_FormulaPolyOn_iff {α : Type*} {enc : α ↪ List Bool} {A : Set α} :
    Aᶜ ∈ FormulaPolyOn enc ↔ A ∈ FormulaPolyOn enc :=
  ⟨fun h => by simpa using FormulaPolyOn.compl h, FormulaPolyOn.compl⟩

end Cslib.Circuits.Boolean
