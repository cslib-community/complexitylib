/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Monoid programs

For a monoid `M`, a *program over `M`* reads an input `x : ι → α`, a word over the alphabet `α`
with positions in `ι`. It is a word of instructions (`MonoidProgram`), each of which reads the
letter at a position `i` and selects an element of `M` by a function `α → M` (`Instruction`). On
an input the program computes the product of the selected elements, the first instruction leftmost
(`MonoidProgram.eval`); evaluation is a monoid homomorphism from programs under concatenation
(`MonoidProgram.eval_mul`) [BarringtonTherien1988]. Programs are covariant in the monoid
(`MonoidProgram.map`), and contravariant in the alphabet (`MonoidProgram.comap`) and in the
positions (`MonoidProgram.rename`).

Branching programs of width `w` are the programs over `Function.End (Fin w)`, and permutation
branching programs those over `Equiv.Perm (Fin w)`; since `(σ * τ) a = σ (τ a)`, the last
instruction acts first. A program *`σ`-computes* a Boolean-valued function `f` of its input when
its value is `σ` where `f` is true and `1` elsewhere (`MonoidProgram.Computes`) [Barrington1989].

Programs over groups can be inverted (`MonoidProgram.eval_inv`), and every program can be pushed
along a monoid homomorphism, for instance a conjugation (`MonoidProgram.eval_map`). So computed
functions can be negated (`MonoidProgram.Computes.not`) and combined by commutators
(`MonoidProgram.Computes.and`), the two steps of Barrington's theorem.

## Main definitions

* `Cslib.BranchingPrograms.Instruction`, `Cslib.BranchingPrograms.Instruction.eval`: an
  instruction (a position and a function from the alphabet to the monoid) and the element it
  selects on an input.
* `Cslib.BranchingPrograms.Instruction.cond`, `Cslib.BranchingPrograms.Instruction.const`:
  instructions selecting one of two elements by a bit, or a fixed element.
* `Cslib.BranchingPrograms.Instruction.map`, `Cslib.BranchingPrograms.Instruction.comap`,
  `Cslib.BranchingPrograms.Instruction.rename`: change of monoid, alphabet and positions for an
  instruction.
* `Cslib.BranchingPrograms.MonoidProgram`: a program over a monoid, a word of instructions.
* `Cslib.BranchingPrograms.MonoidProgram.eval`: the value of a program on an input.
* `Cslib.BranchingPrograms.MonoidProgram.map`, `Cslib.BranchingPrograms.MonoidProgram.comap`,
  `Cslib.BranchingPrograms.MonoidProgram.rename`: change of monoid, alphabet and positions.
* `Cslib.BranchingPrograms.MonoidProgram.inv`, `Cslib.BranchingPrograms.MonoidProgram.mulLeft`:
  the inverse of a program over a group, and left multiplication of its value.
* `Cslib.BranchingPrograms.MonoidProgram.Computes`: `σ`-computing a Boolean-valued function.

## Main results

* `Cslib.BranchingPrograms.MonoidProgram.Computes.not`,
  `Cslib.BranchingPrograms.MonoidProgram.Computes.and`: negation and conjunction of computed
  functions.

## Implementation notes

An instruction selects by a function `α → M`, as in [BarringtonTherien1988], rather than by an
element of `M` for each letter. Barrington's instructions over Boolean inputs, which select one of
two elements according to the bit read [Barrington1989], are the instructions with `α := Bool`
built by `Instruction.cond`, and every instruction over `Bool` is one of them
(`Instruction.cond_var_select`). Barrington's programs over `n` Boolean variables are thus the
programs over `Fin n → Bool`, the bit strings `BitString n`, with `ι := Fin n` and `α := Bool`.

## References

* [D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [D. A. Mix Barrington, D. Thérien, *Finite monoids and the fine structure of
  NC¹*][BarringtonTherien1988]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

/-- An instruction of a program over `M` on inputs `x : ι → α`: read the letter `x var` and select
the element `select (x var)` of `M`. -/
structure Instruction (ι α M : Type*) where
  /-- The position read. -/
  var : ι
  /-- The element selected for each letter. -/
  select : α → M

namespace Instruction

variable {ι κ α β M N : Type*}

/-- The element an instruction selects on an input. -/
def eval (I : Instruction ι α M) (x : ι → α) : M :=
  I.select (x I.var)

/-- Evaluating `⟨i, f⟩` on `x` applies `f` to `x i`. -/
@[simp] theorem eval_mk (i : ι) (f : α → M) (x : ι → α) :
    (⟨i, f⟩ : Instruction ι α M).eval x = f (x i) :=
  rfl

/-- The instruction over Boolean inputs that reads the bit at position `i` and selects `t` when it
is true and `e` when it is false. -/
@[simps]
def cond (i : ι) (t e : M) : Instruction ι Bool M :=
  ⟨i, fun b => bif b then t else e⟩

/-- Evaluating `cond i t e` on `x` selects `t` when `x i` is true and `e` when `x i` is false. -/
@[simp] theorem eval_cond (i : ι) (t e : M) (x : ι → Bool) :
    (cond i t e).eval x = bif x i then t else e :=
  rfl

/-- Every instruction over Boolean inputs selects one of two elements by the bit it reads. -/
theorem cond_var_select (I : Instruction ι Bool M) :
    cond I.var (I.select true) (I.select false) = I := by
  obtain ⟨i, f⟩ := I
  refine congrArg (Instruction.mk i) (funext fun b => ?_)
  cases b <;> rfl

/-- The instruction that reads position `i` and selects `m` whatever the letter. -/
@[simps]
def const (i : ι) (m : M) : Instruction ι α M :=
  ⟨i, fun _ => m⟩

/-- A constant instruction evaluates to its fixed element on every input. -/
@[simp] theorem eval_const (i : ι) (m : M) (x : ι → α) : (const i m).eval x = m :=
  rfl

/-- The instruction selecting `φ m` instead of each `m`. -/
@[simps]
def map (φ : M → N) (I : Instruction ι α M) : Instruction ι α N :=
  ⟨I.var, φ ∘ I.select⟩

/-- Mapping an instruction by `φ` applies `φ` to the element it selects. -/
@[simp] theorem eval_map (φ : M → N) (I : Instruction ι α M) (x : ι → α) :
    (I.map φ).eval x = φ (I.eval x) :=
  rfl

/-- The instruction on inputs over `β` that reads each letter `b` as `g b`. -/
@[simps]
def comap (g : β → α) (I : Instruction ι α M) : Instruction ι β M :=
  ⟨I.var, I.select ∘ g⟩

/-- Pulling an instruction back along `g` evaluates it on `g ∘ x`. -/
@[simp] theorem eval_comap (g : β → α) (I : Instruction ι α M) (x : ι → β) :
    (I.comap g).eval x = I.eval (g ∘ x) :=
  rfl

/-- The instruction that reads position `f I.var` instead of `I.var`. -/
@[simps]
def rename (f : ι → κ) (I : Instruction ι α M) : Instruction κ α M :=
  ⟨f I.var, I.select⟩

/-- Renaming the position of an instruction by `f` evaluates it on `x ∘ f`. -/
@[simp] theorem eval_rename (f : ι → κ) (I : Instruction ι α M) (x : κ → α) :
    (I.rename f).eval x = I.eval (x ∘ f) :=
  rfl

end Instruction

/-- A program over `M` on inputs `ι → α`: a word of instructions. -/
abbrev MonoidProgram (ι α M : Type*) : Type _ :=
  FreeMonoid (Instruction ι α M)

namespace MonoidProgram

variable {ι κ α β M N G : Type*} [Monoid M] [Monoid N] [Group G]

/-- The product of the elements a program selects on an input, the first instruction leftmost. -/
def eval (P : MonoidProgram ι α M) (x : ι → α) : M :=
  FreeMonoid.lift (·.eval x) P

/-- The value of a program on `x` is the list product of the elements its instructions select. -/
theorem eval_eq_prod (P : MonoidProgram ι α M) (x : ι → α) :
    P.eval x = (P.toList.map (·.eval x)).prod :=
  FreeMonoid.lift_apply _ P

/-- The empty program evaluates to `1`. -/
@[simp] theorem eval_one (x : ι → α) : (1 : MonoidProgram ι α M).eval x = 1 :=
  map_one _

/-- A single-instruction program evaluates to the element that instruction selects. -/
@[simp] theorem eval_of (I : Instruction ι α M) (x : ι → α) :
    eval (FreeMonoid.of I) x = I.eval x :=
  FreeMonoid.lift_eval_of _ I

/-- Concatenating two programs multiplies their values. -/
@[simp] theorem eval_mul (P Q : MonoidProgram ι α M) (x : ι → α) :
    (P * Q).eval x = P.eval x * Q.eval x :=
  map_mul _ P Q

/-- A program `σ`-computes a Boolean-valued function `f` of its input when its value is `σ` on the
inputs where `f` is true and `1` elsewhere. -/
def Computes (P : MonoidProgram ι α M) (σ : M) (f : (ι → α) → Bool) : Prop :=
  ∀ x, P.eval x = if f x then σ else 1

/-- The program selecting `φ m` instead of each `m`. -/
def map (φ : M →* N) (P : MonoidProgram ι α M) : MonoidProgram ι α N :=
  FreeMonoid.map (Instruction.map φ) P

/-- Mapping a program by a monoid homomorphism preserves its length. -/
@[simp] theorem length_map (φ : M →* N) (P : MonoidProgram ι α M) :
    (P.map φ).length = P.length :=
  List.length_map _

/-- Mapping a program by a monoid homomorphism `φ` applies `φ` to its value. -/
@[simp] theorem eval_map (φ : M →* N) (P : MonoidProgram ι α M) (x : ι → α) :
    (P.map φ).eval x = φ (P.eval x) := by
  simp only [eval_eq_prod, map, FreeMonoid.toList_map, List.map_map, map_list_prod]
  rfl

/-- Pushing a program that `σ`-computes `f` along a monoid homomorphism `φ` gives a program that
`(φ σ)`-computes `f`. -/
theorem Computes.map {P : MonoidProgram ι α M} {σ : M} {f : (ι → α) → Bool}
    (h : P.Computes σ f) (φ : M →* N) : (P.map φ).Computes (φ σ) f := fun x => by
  rw [eval_map, h x]
  split_ifs <;> simp

/-- The program on inputs over `β` that reads each letter `b` as `g b`. -/
def comap (g : β → α) (P : MonoidProgram ι α M) : MonoidProgram ι β M :=
  FreeMonoid.map (Instruction.comap g) P

omit [Monoid M] in
/-- Pulling a program back along `g` preserves its length. -/
@[simp] theorem length_comap (g : β → α) (P : MonoidProgram ι α M) :
    (P.comap g).length = P.length :=
  List.length_map _

/-- Pulling a program back along `g` evaluates it on `g ∘ x`. -/
@[simp] theorem eval_comap (g : β → α) (P : MonoidProgram ι α M) (x : ι → β) :
    (P.comap g).eval x = P.eval (g ∘ x) := by
  simp only [eval_eq_prod, comap, FreeMonoid.toList_map, List.map_map]
  rfl

/-- The program that reads position `f i` wherever `P` reads position `i`. -/
def rename (f : ι → κ) (P : MonoidProgram ι α M) : MonoidProgram κ α M :=
  FreeMonoid.map (Instruction.rename f) P

omit [Monoid M] in
/-- Renaming the positions of a program preserves its length. -/
@[simp] theorem length_rename (f : ι → κ) (P : MonoidProgram ι α M) :
    (P.rename f).length = P.length :=
  List.length_map _

/-- Renaming the positions of a program by `f` evaluates it on `x ∘ f`. -/
@[simp] theorem eval_rename (f : ι → κ) (P : MonoidProgram ι α M) (x : κ → α) :
    (P.rename f).eval x = P.eval (x ∘ f) := by
  simp only [eval_eq_prod, rename, FreeMonoid.toList_map, List.map_map]
  rfl

/-- The program with the instructions in reverse order and their elements inverted. -/
def inv (P : MonoidProgram ι α G) : MonoidProgram ι α G :=
  FreeMonoid.reverse (FreeMonoid.map (Instruction.map (·⁻¹)) P)

/-- The instruction list of `P.inv` is the reversed list of elementwise-inverted instructions of
`P`. -/
theorem toList_inv (P : MonoidProgram ι α G) :
    P.inv.toList = (P.toList.map (Instruction.map (·⁻¹))).reverse :=
  rfl

/-- Inverting a program over a group preserves its length. -/
@[simp] theorem length_inv (P : MonoidProgram ι α G) : P.inv.length = P.length := by
  simp [FreeMonoid.length, toList_inv]

/-- The inverse of a program over a group evaluates to the inverse of its value. -/
@[simp] theorem eval_inv (P : MonoidProgram ι α G) (x : ι → α) :
    P.inv.eval x = (P.eval x)⁻¹ := by
  simp [eval_eq_prod, toList_inv, List.prod_inv_reverse, Function.comp_def]

variable [Inhabited ι]

/-- Multiply the value of a program by `g` on the left, without making it longer unless it is
empty. -/
def mulLeft (g : M) (P : MonoidProgram ι α M) : MonoidProgram ι α M :=
  match P.toList with
  | [] => FreeMonoid.of (.const default g)
  | I :: l => FreeMonoid.ofList (I.map (g * ·) :: l)

/-- `mulLeft g P` evaluates to `g * P.eval x`. -/
@[simp] theorem eval_mulLeft (g : M) (P : MonoidProgram ι α M) (x : ι → α) :
    (mulLeft g P).eval x = g * P.eval x := by
  unfold mulLeft
  split <;> rename_i h
  · simp [eval_eq_prod, h]
  · simp [eval_eq_prod, h, mul_assoc]

/-- `mulLeft g P` has length `max 1 P.length`. -/
theorem length_mulLeft (g : M) (P : MonoidProgram ι α M) :
    (mulLeft g P).length = max 1 P.length := by
  unfold mulLeft FreeMonoid.length
  split <;> rename_i h <;> simp [h]

/-- If `P` `σ⁻¹`-computes `f`, multiplying by `σ` makes it `σ`-compute the negation of `f`. -/
theorem Computes.not {σ : G} {f : (ι → α) → Bool} {P : MonoidProgram ι α G}
    (h : P.Computes σ⁻¹ f) : (mulLeft σ P).Computes σ fun x => !f x := fun x => by
  rw [eval_mulLeft, h x]
  cases hf : f x <;> simp [hf]

omit [Inhabited ι] in
/-- The commutator of programs `σ`- and `τ`-computing `f` and `g` computes `f ∧ g` with the
commutator `σ τ σ⁻¹ τ⁻¹`. -/
theorem Computes.and {σ τ : G} {f g : (ι → α) → Bool} {P Q : MonoidProgram ι α G}
    (hP : P.Computes σ f) (hQ : Q.Computes τ g) :
    (P * Q * P.inv * Q.inv).Computes (σ * τ * σ⁻¹ * τ⁻¹) fun x => f x && g x := fun x => by
  rw [eval_mul, eval_mul, eval_mul, eval_inv, eval_inv, hP x, hQ x]
  cases hf : f x <;> cases hg : g x <;> simp [hf, hg]

end MonoidProgram

end Cslib.BranchingPrograms
