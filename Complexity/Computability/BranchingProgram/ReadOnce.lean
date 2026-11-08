/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.BranchingProgram.MonoidProgram
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Group.End
import Batteries.Data.Fin.Fold
import Mathlib.Data.List.OfFn

/-!
# Read-once branching programs

A *read-once branching program* of length `L` over an alphabet `X`, with states `S`, reads a word
`x : Fin L → X` letter by letter in the standard order: it starts in the state `start`, at time
`i` it moves from its current state `s` to `step i s (x i)`, and it accepts when the final state
satisfies `accept` (`ReadOnceProgram`, `ReadOnceProgram.eval`). Its *width* is the number of
states `Fintype.card S`. Read-once branching programs of width `w` and length `L` model
computations of length `L` with `log w` bits of memory reading a one-way stream of random letters,
the tests fooled by Nisan's generator. These are the standard-order read-once branching programs
of [Hatami and Hoza, Definition 1.5][HatamiHoza2024], the oblivious read-once branching programs of
[Vadhan, Section 8.2.1][Vadhan2012] (with layers of states `S` and edges labelled by letters). A
program of length `m * n` over `X` regroups into a program of length `m` over the blocks
`Fin n → X` with the same states (`ReadOnceProgram.blocks`, `ReadOnceProgram.eval_blocks`).

The run of a time-dependent transition function `δ : ℕ → S → X → S` on a list of letters, starting
at time `t` in state `s`, is `runFrom δ t s` (`runFrom_append` splits runs). A program runs its
transition function extended by the identity after time `L` (`ReadOnceProgram.finalState_eq`).

Read-once branching programs are a sequential form of monoid programs
(`Cslib.BranchingPrograms.MonoidProgram`) over the transformation monoid `Function.End S`. That
model fixes a monoid element for each letter read, but lets instructions read positions in any
order and any number of times, and measures length rather than width. A read-once program is the
monoid program whose `i`-th instruction from the end reads position `i` and selects
`step i · a` on the letter `a`; since the last instruction of a program over `Function.End S` acts
first, it maps the start state to the final state (`ReadOnceProgram.toMonoidProgram`,
`ReadOnceProgram.eval_toMonoidProgram`). The read-once nondeterministic programs
`Cslib.Circuits.Frontier.ReadOnceNBP` instead read sets of coordinates in a layout order, with
nondeterministic transitions.

## Main definitions

* `Cslib.BranchingPrograms.runFrom`: the run of a time-dependent transition function on a list.
* `Cslib.BranchingPrograms.ReadOnceProgram`: a read-once branching program in standard order.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval`: its output on a word.
* `Cslib.BranchingPrograms.ReadOnceProgram.flattenEquiv`: blocks of letters as words.
* `Cslib.BranchingPrograms.ReadOnceProgram.blocks`: the program on blocks of `n` letters.
* `Cslib.BranchingPrograms.ReadOnceProgram.toMonoidProgram`: the program as a monoid program over
  `Function.End S`.

## Main results

* `Cslib.BranchingPrograms.ReadOnceProgram.finalState_eq`: the final state is the run of the
  extended transition function.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval_blocks`: regrouping into blocks preserves outputs.
* `Cslib.BranchingPrograms.ReadOnceProgram.eval_toMonoidProgram`: the monoid program evaluates to
  the map from start states to final states.

## References

* [P. Hatami, W. Hoza, *Paradigms for Unconditional Pseudorandom Generators*][HatamiHoza2024]
* [S. Vadhan, *Pseudorandomness*][Vadhan2012]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

variable {S X : Type*}

/-! ### Runs of time-dependent transition functions -/

/-- The run of the time-dependent transition function `δ` on a list of letters, starting at time
`t` in state `s`: at time `t + i` it reads the `i`-th letter. -/
def runFrom (δ : ℕ → S → X → S) : ℕ → S → List X → S
  | _, s, [] => s
  | t, s, a :: l => runFrom δ (t + 1) (δ t s a) l

@[simp] theorem runFrom_nil (δ : ℕ → S → X → S) (t : ℕ) (s : S) : runFrom δ t s [] = s :=
  rfl

@[simp] theorem runFrom_cons (δ : ℕ → S → X → S) (t : ℕ) (s : S) (a : X) (l : List X) :
    runFrom δ t s (a :: l) = runFrom δ (t + 1) (δ t s a) l :=
  rfl

/-- **Splitting a run**: the run on `l₁ ++ l₂` is the run on `l₂`, started at the time and state
where the run on `l₁` ends. -/
theorem runFrom_append (δ : ℕ → S → X → S) (t : ℕ) (s : S) (l₁ l₂ : List X) :
    runFrom δ t s (l₁ ++ l₂) = runFrom δ (t + l₁.length) (runFrom δ t s l₁) l₂ := by
  induction l₁ generalizing t s with
  | nil => rfl
  | cons a l ih =>
    rw [List.cons_append, runFrom_cons, ih, runFrom_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1]

/-- Runs on mapped letters are runs of the transition function precomposed with the map. -/
theorem runFrom_map {Y : Type*} (δ : ℕ → S → X → S) (f : Y → X) (t : ℕ) (s : S) (l : List Y) :
    runFrom δ t s (l.map f) = runFrom (fun t s a => δ t s (f a)) t s l := by
  induction l generalizing t s with
  | nil => rfl
  | cons a l ih => exact ih _ _

/-- **Runs on blocks**: if every block of the list `L` has length `n`, the run on the concatenated
blocks is the run on the list of blocks, reading a whole block at each time. -/
theorem runFrom_flatten (δ : ℕ → S → X → S) {n : ℕ} (L : List (List X))
    (hL : ∀ l ∈ L, l.length = n) (t : ℕ) (s : S) :
    runFrom δ (n * t) s L.flatten = runFrom (fun t s l => runFrom δ (n * t) s l) t s L := by
  induction L generalizing t s with
  | nil => rfl
  | cons l L ih =>
    rw [List.flatten_cons, runFrom_append, hL l List.mem_cons_self, runFrom_cons, ← Nat.mul_succ,
      ih (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))]

/-- Folding a time-shifted transition function over the positions of a word is its run. -/
theorem foldl_eq_runFrom (δ : ℕ → S → X → S) (t : ℕ) {m : ℕ} (x : Fin m → X) (s : S) :
    Fin.foldl m (fun s i => δ (t + i) s (x i)) s = runFrom δ t s (List.ofFn x) := by
  induction m generalizing t s with
  | zero => rfl
  | succ m ih =>
    rw [Fin.foldl_succ, List.ofFn_succ, runFrom_cons, ← ih (t + 1)]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

/-! ### Read-once branching programs -/

/-- A *read-once branching program* in standard order, of length `L` over the alphabet `X` with
states `S`: from the state `start`, at time `i` it moves from state `s` to `step i s a` on reading
the `i`-th letter `a`, and it accepts when the final state satisfies `accept`. Its width is
`Fintype.card S` [Hatami and Hoza, Definition 1.5][HatamiHoza2024]. -/
structure ReadOnceProgram (L : ℕ) (S X : Type*) where
  /-- The start state. -/
  start : S
  /-- The transition at each time, on the current state and the letter read. -/
  step : Fin L → S → X → S
  /-- The accepting final states. -/
  accept : S → Bool

namespace ReadOnceProgram

variable {L : ℕ} (P : ReadOnceProgram L S X)

/-- The state of the program after reading the word `x`. -/
def finalState (x : Fin L → X) : S :=
  Fin.foldl L (fun s i => P.step i s (x i)) P.start

/-- The output of the program on the word `x`: whether its final state is accepting. -/
def eval (x : Fin L → X) : Bool :=
  P.accept (P.finalState x)

/-- The transition function of the program at every time, the identity from time `L` on. -/
def stepAt (t : ℕ) (s : S) (a : X) : S :=
  if h : t < L then P.step ⟨t, h⟩ s a else s

/-- The final state is the run of the extended transition function `stepAt` on the word. -/
theorem finalState_eq (x : Fin L → X) :
    P.finalState x = runFrom P.stepAt 0 P.start (List.ofFn x) := by
  rw [← foldl_eq_runFrom]
  simp only [finalState, stepAt, Nat.zero_add, Fin.is_lt, dite_true]

/-! ### Blocks -/

/-- The word of `m * n` letters whose `i`-th block of `n` letters is `x i`, in order. -/
def flatten {m n : ℕ} (x : Fin m → Fin n → X) : Fin (m * n) → X :=
  fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

@[simp] theorem flatten_apply {m n : ℕ} (x : Fin m → Fin n → X) (i : Fin m) (j : Fin n) :
    flatten x (finProdFinEquiv (i, j)) = x i j := by
  simp only [flatten, Equiv.symm_apply_apply]

/-- Flattening is a bijection between `m` blocks of `n` letters and words of `m * n` letters. -/
def flattenEquiv (m n : ℕ) : (Fin m → Fin n → X) ≃ (Fin (m * n) → X) :=
  (Equiv.curry (Fin m) (Fin n) X).symm.trans (finProdFinEquiv.arrowCongr (Equiv.refl X))

@[simp] theorem flattenEquiv_apply {m n : ℕ} (x : Fin m → Fin n → X) :
    flattenEquiv m n x = flatten x :=
  rfl

/-- Concatenating the blocks of a word as lists. -/
theorem ofFn_flatten {m n : ℕ} (x : Fin m → Fin n → X) :
    List.ofFn (flatten x) = (List.ofFn fun i => List.ofFn (x i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => List.ofFn_inj.2 (funext fun j => ?_))
  rw [← flatten_apply x i j]
  congr 1
  ext
  simp only [finProdFinEquiv_apply_val]
  rw [Nat.add_comm, Nat.mul_comm]

/-- The program of length `m` on blocks of `n` letters: at time `i` it runs `P` on the `i`-th
block, from time `n * i`. It has the same states, hence the same width. -/
def blocks {m n : ℕ} (P : ReadOnceProgram (m * n) S X) : ReadOnceProgram m S (Fin n → X) where
  start := P.start
  step i s y := runFrom P.stepAt (n * i) s (List.ofFn y)
  accept := P.accept

/-- **Regrouping into blocks** preserves final states. -/
theorem finalState_blocks {m n : ℕ} (P : ReadOnceProgram (m * n) S X) (x : Fin m → Fin n → X) :
    P.blocks.finalState x = P.finalState (flatten x) := by
  have hrun := runFrom_flatten P.stepAt (List.ofFn fun i => List.ofFn (x i))
    (fun l hl => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      exact List.length_ofFn) 0 P.start
  rw [Nat.mul_zero, ← ofFn_flatten, ← finalState_eq, List.ofFn_comp', runFrom_map,
    ← foldl_eq_runFrom] at hrun
  rw [hrun]
  simp only [finalState, Nat.zero_add, blocks]

/-- **Regrouping into blocks** preserves outputs. -/
theorem eval_blocks {m n : ℕ} (P : ReadOnceProgram (m * n) S X) (x : Fin m → Fin n → X) :
    P.blocks.eval x = P.eval (flatten x) := by
  rw [eval, finalState_blocks]
  rfl

/-! ### Monoid programs -/

/-- The program as a monoid program over `Function.End S`: the `i`-th instruction from the end
reads position `i` and selects `step i · a` on the letter `a`. -/
def toMonoidProgram (P : ReadOnceProgram L S X) : MonoidProgram (Fin L) X (Function.End S) :=
  FreeMonoid.ofList <| List.ofFn fun i : Fin L =>
    ⟨i.rev, fun a => (fun s => P.step i.rev s a : Function.End S)⟩

private theorem prod_ofFn_rev_apply {m : ℕ} (g : Fin m → Function.End S) (s : S) :
    (List.ofFn fun i : Fin m => g i.rev).prod s =
      Fin.foldl m (fun s i => g i s) s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton,
      Fin.foldl_succ]
    simp only [Fin.rev_castSucc, Fin.rev_last]
    exact ih (fun i => g i.succ) (g 0 s)

/-- **Read-once programs are monoid programs**: the monoid program `P.toMonoidProgram` evaluates on
`x` to the map sending the start state to the final state of `P` on `x`. -/
theorem eval_toMonoidProgram (x : Fin L → X) :
    P.toMonoidProgram.eval x P.start = P.finalState x := by
  rw [MonoidProgram.eval_eq_prod, toMonoidProgram, FreeMonoid.toList_ofList, List.map_ofFn]
  exact prod_ofFn_rev_apply (fun i => (fun s => P.step i s (x i) : Function.End S)) P.start

end ReadOnceProgram

end Cslib.BranchingPrograms
