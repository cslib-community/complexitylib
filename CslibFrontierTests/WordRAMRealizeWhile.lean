/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Realization.Client.MemoryStack
import CslibFrontier.Tactic.Realize

/-! `realize` on guarded loops (`boundedWhile`).

Three loop shapes the migrations need, each closed by `realize` and a short discharge of the loop
domain it leaves: a countdown whose body reads memory, the queue's transfer between two array
stacks counted down by the items left, and a sift-shaped descent `i ↦ 2i + 1` with logarithmic
rank. Guards are written in the client's terms (`0 < r`, `r ≠ 0`, `i < n`), with any
decidability instance; `realize` tests them natively and computes the `0` of `0 < r` before the
loop. The cutoff is a ghost bound, never computed. The controls pin the unsupported forms and
show that a truncating cutoff leaves an unsatisfiable domain. -/

namespace CslibFrontierTests.WordRAMRealizeWhile

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization MemoryStack

/-- One word. -/
abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- Two words. -/
abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) :=
  (word.prodMap word).trans (Fin.appendEquiv 1 1).toEmbedding

/-! ## A countdown whose body reads memory -/

/-- Load the count at `b`, then count it down, reading the cell after `b` on every step. -/
def countdown (b : ℕ) : Memory.Prog ℕ := do
  let n ← Memory.read b
  boundedWhile (fun _ r => 0 < r) (fun (c, r) => do
    let _ ← Memory.read c
    pure (r - 1)) (b + 1) n n

/-- The remaining count is the rank, and the loaded count the cutoff. -/
example : Realizes .exact countdown word word (fun w b _ => Fits w (b + 1)) (fun _ _ => 0) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun r _ => r)
    (fun r _ _ hr hg => by omega) (fun r t _ hg _ => ⟨⟨h, hg⟩, trivial, ?_⟩) trivial le_rfl hv
  change r - 1 < r
  omega

/-- The same countdown with the guard `r ≠ 0` under a classical decidability instance. -/
noncomputable def countdownNe (b : ℕ) : Memory.Prog ℕ := do
  let n ← Memory.read b
  @boundedWhile _ _ (fun _ r => r ≠ 0) (fun _ _ => Classical.propDecidable _) (fun (c, r) => do
    let _ ← Memory.read c
    pure (r - 1)) (b + 1) n n

/-- `r ≠ 0` is tested as `0 < r`, whatever its decidability instance. -/
example : Realizes .exact countdownNe word word (fun w b _ => Fits w (b + 1)) (fun _ _ => 0) := by
  realize
  intro hv
  refine @whileSafe_of_measure _ _ _ (fun _ _ => Classical.propDecidable _) _ _ w _
    (fun _ _ => True) (fun r _ => r) (fun r _ _ hr hg => hg hr)
    (fun r t _ hg _ => ⟨⟨h, by omega⟩, trivial, ?_⟩) _ _ _ trivial le_rfl hv
  change r - 1 < r
  omega

/-- Count up to `b`, reading `b` on every step: the guard and the step capture the environment,
and the loop's own environment is `()`. -/
def countUp (b : ℕ) : Memory.Prog ℕ :=
  boundedWhile (fun _ r => r < b) (fun ((_ : Unit), r) => do
    let _ ← Memory.read b
    pure (r + 1)) () b 0

/-- The distance to `b` is the rank. -/
example : Realizes .exact countUp word word (fun w b _ => Fits w (b + 1)) (fun _ _ => 0) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun r _ => r ≤ d) (fun r _ => d - r)
    (fun r _ _ hr hg => by omega) (fun r t hi hg _ => ⟨h.of_le (by omega), ?_, ?_⟩)
    (Nat.zero_le _) (by omega) hv
  · change r + 1 ≤ d
    omega
  · change d - (r + 1) < d - r
    omega

/-! ## The queue's transfer, counted down by the items left -/

/-- Front and rear stack layouts. -/
def queueWords : Stack.Memory.Layout × Stack.Memory.Layout ↪ (Fin 8 → ℕ) :=
  (layoutWords.prodMap layoutWords).trans (Fin.appendEquiv 4 4).toEmbedding

/-- One transfer step: pop the rear; push a popped item on the front and count down, and stop on
an empty rear. -/
def transferStep (F R : Stack.Memory.Layout) (r : ℕ) : Memory.Prog ℕ := do
  match ← Stack.Memory.pop R with
  | none => pure 0
  | some v => do
    Stack.Memory.push F v
    pure (r - 1)

/-- Read the rear's size, then move that many items while some remain. -/
def transfer : Stack.Memory.Layout × Stack.Memory.Layout → Memory.Prog ℕ
  | (F, R) => do
    let n ← Stack.Memory.size R
    boundedWhile (fun _ r => 0 < r) (fun ((F, R), r) => transferStep F R r) (F, R) n n

/-- What one step needs at a reached memory: a nonempty rear's top item and the front's next
slot are addressable, and the front's count can grow. -/
def StepReady (w : ℕ) (F R : Stack.Memory.Layout) (s : Memory.State) : Prop :=
  s.mem R.count.base ≠ 0 → Fits w (R.items.base + (s.mem R.count.base - 1)) ∧
    Fits w (F.items.base + s.mem F.count.base) ∧ Fits w (s.mem F.count.base + 1)

set_option maxHeartbeats 40000 in
-- Performance guard: about 3k heartbeats are needed, side conditions included.
/-- `realize` certifies the size query and the loop, with the pop's `match` and the push in the
body. Each step's domain follows from `StepReady` at the reached memory. What remains,
`whileSafe … StepReady …`, is what a queue migration discharges with its transfer invariant
(`whileSafe_of_measure`, rank `r`). -/
example : Realizes .exact transfer queueWords word
    (fun w (F, R) s => F.count.base ≠ R.count.base ∧
      whileSafe (fun _ r => 0 < r) (fun ((F, R), r) => transferStep F R r)
        (fun w ((F, R), _) s => StepReady w F R s) w (F, R) (s.mem R.count.base)
        (s.mem R.count.base) s)
    (fun _ _ => 0) := by
  realize
  intro _
  refine whileSafe_imp _ _ (fun _ => Iff.rfl) (fun _ => rfl) (fun r t hg hr => ?_) h.2
  by_cases hc : t.mem d.2.count.base = 0
  · simp [hc, Stack.Memory.runClient_pop_of_eq_zero _ t hc, StateTransitionSpec.clientResult]
  · obtain ⟨h₁, h₂, h₃⟩ := hr hc
    simp only [hc, ↓reduceIte, StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      Stack.Memory.runClient_pop_of_pos _ t hc, optionWords_some, Matrix.cons_val_zero,
      Nat.one_ne_zero, Function.update_of_ne h.1]
    exact ⟨⟨⟨by omega, h₁⟩, by omega, h₃.of_le (by omega)⟩, ⟨h₂, h₃⟩, hg⟩

/-! ## A sift-shaped descent with logarithmic rank -/

/-- Descend from the root of a heap of size `n` at `b` through left children `i ↦ 2i + 1`,
reading each visited item. -/
def descend : ℕ × ℕ → Memory.Prog ℕ
  | (b, n) => boundedWhile (fun (_, n) i => i < n)
      (fun ((b, _), i) => do
        let _ ← Memory.read (b + i)
        pure (i + i + 1)) (b, n) (Nat.log 2 n + 1) 0

/-- The levels left below index `i` in a heap of size `n`. -/
def levels (n i : ℕ) : ℕ := Nat.log 2 n + 1 - Nat.log 2 (i + 1)

/-- A left child within the heap has one level fewer left. -/
theorem levels_child {n i : ℕ} (h : i < n) : levels n (i + i + 1) < levels n i := by
  have hle : Nat.log 2 (i + 1) ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
  have hlog : Nat.log 2 (i + i + 1 + 1) = Nat.log 2 (i + 1) + 1 := by
    rw [show i + i + 1 + 1 = (i + 1) * 2 by ring, Nat.log_mul_base (by norm_num) (by omega)]
  unfold levels
  omega

/-- The rank is the levels left; the cutoff `log₂ n + 1` is a ghost bound. -/
example : Realizes .exact descend pairWords word
    (fun w (b, n) _ => Fits w (b + n) ∧ Fits w (n + n)) (fun _ _ => 0) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun i _ => levels d.2 i)
    (fun i _ _ hr hg => ?_) (fun i t _ hg _ => ⟨?_, trivial, ?_⟩) trivial (Nat.sub_le _ _) hv
  · have := levels_child (n := d.2) hg
    omega
  · exact ⟨h.1.of_le (by dsimp only at hg ⊢; omega), h.2.of_le (by dsimp only at hg ⊢; omega)⟩
  · exact levels_child hg

/-! ## Controls -/

/-- A truncating cutoff leaves an unsatisfiable domain: at cutoff `0` the guard must be false. -/
example (w : ℕ) (s : Memory.State) :
    ¬whileSafe (fun _ r => 0 < r) (fun ((_ : ℕ), r) => pure (r - 1)) (fun _ _ _ => True)
      w 0 0 1 s :=
  fun h => h Nat.one_pos

/-- A query-free loop keeps a graded charge, which `whileWork_le` bounds by the cutoff. -/
example (n i : ℕ) (s : Memory.State) :
    whileWork (fun n i => i < n) (fun ((_ : ℕ), i) => pure (i + i + 1)) (fun _ _ => 5) n
      (Nat.log 2 n + 1) i s ≤ (Nat.log 2 n + 1) * 6 :=
  whileWork_le _ _ (fun _ _ => le_rfl) n _ i s

/-- A query-free body has no memory charge to pay for its iterations. -/
def halve (a : ℕ) : Memory.Prog ℕ :=
  boundedWhile (fun _ a => 0 < a) (fun ((_ : ℕ), a) => pure (a >>> 1)) a (a + 1) a

/--
error: realize: a loop body must begin with a memory query, which pays for the iteration;
the body begins with
  PFunctor.FreeM.pure (x.2 >>> 1)
-/
#guard_msgs in
example : Realizes .exact halve word word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- A non-strict comparison is not a native test. -/
def upTo (n : ℕ) : Memory.Prog ℕ :=
  boundedWhile (fun n i => i ≤ n) (fun (_, i) => do let _ ← Memory.read i; pure (i + 1)) n (n + 1) 0

/--
error: realize: a loop guard must be `a = b`, `a < b`, `a > b` or `a ≠ 0` on words, got
  a ≤ d
-/
#guard_msgs in
example : Realizes .exact upTo word word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- The guard compares live words; a computed function of the state is not one. -/
def doubling (n : ℕ) : Memory.Prog ℕ :=
  boundedWhile (fun n i => i + i < n) (fun (_, i) => do let _ ← Memory.read i; pure (i + 1)) n n 0

/--
error: realize: a loop guard compares words; the operand
  a + a
depends on the loop state but is not one of its words
-/
#guard_msgs in
example : Realizes .exact doubling word word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

end CslibFrontierTests.WordRAMRealizeWhile
