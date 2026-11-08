/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.BitString
public import Cslib.Probability.PMF
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Card
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Embedding.Set

/-!
# One-pass streaming algorithms

A deterministic one-pass **streaming algorithm** (`Cslib.Streaming.Algorithm σ α β`) reads a stream
`s : List α` of items from left to right. It starts in a memory state `init : σ`, replaces its state
`q` by `update q a` on reading each item `a`, and finally reports `output q : β`. Updates are
arbitrary functions, so the model is non-uniform: it charges only the memory that survives between
items, which is the resource bounded by communication arguments [AlonMatiasSzegedy1999, Section 3].

**Space.** `A.SpaceLE m b` says that the memory states `A` reaches on streams of at most `m` items
(`Cslib.Streaming.Algorithm.reachable`) have an injective encoding by `b`-bit strings, that is,
there are at most `2 ^ b` of them (`Cslib.Streaming.Algorithm.spaceLE_of_subset_finset`). The
space of an algorithm is thus `log₂` of the number of its reachable states, rounded up; it does not
count states that no short stream reaches.

**Randomness.** A randomized streaming algorithm (`Cslib.Streaming.Randomized σ α β`) is a
distribution over deterministic ones: its random choices are drawn before the stream is read, as
for public-coin protocols (`Cslib.Communication.PublicCoin`). Its memory bound
(`Cslib.Streaming.Randomized.SpaceLE`) is checked separately for each algorithm in the support.
Since the update function of a drawn algorithm may depend on the random choices, the random bits
are free: they are not charged to the memory. This is the convention under which communication
lower bounds transfer. An algorithm that tosses fresh coins at each item becomes such a
distribution, for example after it counts the items it has read, which costs `⌈log₂ (m + 1)⌉`
more bits on streams of at most `m` items; so lower bounds of order `n` still apply to it, up to
that additive term. `μ.Solves ε R m` says that on every stream of at most `m` items, the answer of
a random algorithm drawn from `μ` is related to the stream by `R` except with probability at most
`ε`.

`Cslib.Streaming.Algorithm.reduce` prefixes fixed items to the stream, translates the items and
post-processes the answer; it preserves memory bounds, which is how streaming lower bounds pass
between problems.

## Main definitions

* `Cslib.Streaming.Algorithm`: deterministic one-pass streaming algorithms, with
  `Cslib.Streaming.Algorithm.state` and `Cslib.Streaming.Algorithm.run`.
* `Cslib.Streaming.Algorithm.SpaceLE`: at most `b` bits of memory on streams of at most `m` items.
* `Cslib.Streaming.Algorithm.reduce`: prefixing, translating items and post-processing answers.
* `Cslib.Streaming.Randomized`, `Cslib.Streaming.Randomized.errorProb`,
  `Cslib.Streaming.Randomized.Solves`, `Cslib.Streaming.Randomized.SpaceLE`: randomized streaming
  algorithms, their error and their memory.

## Main results

* `Cslib.Streaming.Algorithm.spaceLE_of_subset_finset`,
  `Cslib.Streaming.Algorithm.spaceLE_of_card_le`: counting reachable states bounds the memory.
* `Cslib.Streaming.abs_sum_map_le`: a sum of at most unit integers is bounded by the stream length.
* `Cslib.Streaming.card_piFinset_Icc`: the number of states of a grid of bounded integer counters.
* `Cslib.Streaming.Algorithm.SpaceLE.reduce`, `Cslib.Streaming.Randomized.SpaceLE.map_reduce`,
  `Cslib.Streaming.Randomized.errorProb_map_reduce_le`: reductions keep memory and error.
* `Cslib.Streaming.Randomized.solves_pure`, `Cslib.Streaming.Randomized.spaceLE_pure`:
  deterministic algorithms as randomized ones.
* `Cslib.Streaming.Randomized.errorProb_map_uniformOfFintype`: the error of an algorithm drawn
  with a uniform seed is the fraction of bad seeds.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*][AlonMatiasSzegedy1999]
-/

public section

namespace Cslib.Streaming

/-- A deterministic one-pass **streaming algorithm** over items of type `α` with outputs in `β`:
memory states `σ`, an initial state, an update reading one item, and an output function. -/
structure Algorithm (σ α β : Type*) where
  /-- The initial memory state. -/
  init : σ
  /-- The memory state after reading one more item. -/
  update : σ → α → σ
  /-- The answer reported in a memory state. -/
  output : σ → β

namespace Algorithm

variable {σ α β : Type*} (A : Algorithm σ α β)

/-- The memory state after reading the stream `s` from `q`. -/
@[expose] def stateFrom (q : σ) (s : List α) : σ :=
  s.foldl A.update q

/-- The memory state after reading the stream `s`. -/
@[expose] def state (s : List α) : σ :=
  A.stateFrom A.init s

/-- The answer after reading the stream `s`. -/
@[expose] def run (s : List α) : β :=
  A.output (A.state s)

@[simp] theorem stateFrom_nil (q : σ) : A.stateFrom q [] = q := rfl

@[simp] theorem stateFrom_cons (q : σ) (a : α) (s : List α) :
    A.stateFrom q (a :: s) = A.stateFrom (A.update q a) s := rfl

theorem stateFrom_append (q : σ) (s t : List α) :
    A.stateFrom q (s ++ t) = A.stateFrom (A.stateFrom q s) t :=
  List.foldl_append

theorem state_append (s t : List α) : A.state (s ++ t) = A.stateFrom (A.state s) t :=
  A.stateFrom_append _ s t

/-- The memory states reachable on streams of length at most `m`. -/
@[expose] def reachable (m : ℕ) : Set σ :=
  {q | ∃ s : List α, s.length ≤ m ∧ A.state s = q}

theorem state_mem_reachable {m : ℕ} {s : List α} (hs : s.length ≤ m) :
    A.state s ∈ A.reachable m :=
  ⟨s, hs, rfl⟩

theorem reachable_mono {m m' : ℕ} (h : m ≤ m') : A.reachable m ⊆ A.reachable m' :=
  fun _ ⟨s, hs, hq⟩ => ⟨s, hs.trans h, hq⟩

/-- `A` **uses at most `b` bits of memory on streams of length at most `m`**: the memory states it
reaches on such streams have an injective encoding by `b`-bit strings, that is, there are at most
`2 ^ b` of them. -/
@[expose] def SpaceLE (m b : ℕ) : Prop :=
  ∃ enc : σ → BitString b, Set.InjOn enc (A.reachable m)

variable {A}

theorem SpaceLE.mono {m m' b : ℕ} (h : A.SpaceLE m' b) (hm : m ≤ m') : A.SpaceLE m b :=
  let ⟨enc, henc⟩ := h
  ⟨enc, henc.mono (A.reachable_mono hm)⟩

/-- A set of states contained in a finite set of at most `2 ^ b` states has an injective `b`-bit
encoding. -/
theorem exists_injOn_of_subset_finset {S : Set σ} {T : Finset σ} (hST : S ⊆ T) {b : ℕ}
    (hT : T.card ≤ 2 ^ b) : ∃ enc : σ → BitString b, Set.InjOn enc S := by
  classical
  have hcard : Fintype.card T ≤ Fintype.card (BitString b) := by
    simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hT
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun q => if hq : q ∈ T then e ⟨q, hq⟩ else fun _ => false, fun q hq q' hq' h => ?_⟩
  dsimp only at h
  rw [dite_eq_left (Finset.mem_coe.1 (hST hq)), dite_eq_left (Finset.mem_coe.1 (hST hq'))] at h
  exact congrArg Subtype.val (e.injective h)

/-- An algorithm whose reachable states lie in a finite set of at most `2 ^ b` states uses at most
`b` bits of memory. -/
theorem spaceLE_of_subset_finset {m b : ℕ} {T : Finset σ} (hT : A.reachable m ⊆ T)
    (hcard : T.card ≤ 2 ^ b) : A.SpaceLE m b :=
  exists_injOn_of_subset_finset hT hcard

/-- An algorithm with at most `2 ^ b` memory states uses at most `b` bits of memory. -/
theorem spaceLE_of_card_le [Fintype σ] {m b : ℕ} (h : Fintype.card σ ≤ 2 ^ b) : A.SpaceLE m b :=
  spaceLE_of_subset_finset (T := Finset.univ) (fun q _ => Finset.mem_coe.2 (Finset.mem_univ q)) h

variable (A) in
/-- The algorithm that first reads the items `p`, then reads each item `a` as `g a`, and answers
`d` of the answer of `A`. -/
def reduce {α' β' : Type*} (p : List α) (g : α' → α) (d : β → β') : Algorithm σ α' β' where
  init := A.state p
  update q a := A.update q (g a)
  output q := d (A.output q)

theorem state_reduce {α' β' : Type*} (p : List α) (g : α' → α) (d : β → β') (s : List α') :
    (A.reduce p g d).state s = A.state (p ++ s.map g) := by
  simp only [state, stateFrom, reduce, List.foldl_append, List.foldl_map]

theorem run_reduce {α' β' : Type*} (p : List α) (g : α' → α) (d : β → β') (s : List α') :
    (A.reduce p g d).run s = d (A.run (p ++ s.map g)) := by
  rw [run, state_reduce]
  rfl

/-- Reductions keep memory bounds, with the prefix counted in the stream length. -/
theorem SpaceLE.reduce {α' β' : Type*} {m b : ℕ} (p : List α) (h : A.SpaceLE (p.length + m) b)
    (g : α' → α) (d : β → β') : (A.reduce p g d).SpaceLE m b := by
  obtain ⟨enc, henc⟩ := h
  refine ⟨enc, henc.mono ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨p ++ s.map g, ?_, (state_reduce p g d s).symm⟩
  simp only [List.length_append, List.length_map]
  omega

end Algorithm

/-! ### Counter bounds -/

/-- A sum of at most unit integers is bounded by the number of terms. -/
theorem abs_sum_map_le {α : Type*} {f : α → ℤ} (hf : ∀ a, |f a| ≤ 1) (s : List α) :
    |(s.map f).sum| ≤ s.length := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    exact (abs_add_le _ _).trans (by linarith [hf a])

alias _root_.List.abs_sum_map_le := abs_sum_map_le

/-- The number of values of an `ι × κ` grid of integer counters in `[-m, m]`. -/
theorem card_piFinset_Icc {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (m : ℕ) :
    (Fintype.piFinset fun _ : ι => Fintype.piFinset fun _ : κ =>
      Finset.Icc (-(m : ℤ)) m).card = (2 * m + 1) ^ (Fintype.card ι * Fintype.card κ) := by
  have : (↑m + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
  simp only [Fintype.card_piFinset, Int.card_Icc, this, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (Fintype.card κ)]

/-! ### Randomized streaming algorithms -/

/-- A randomized streaming algorithm with **public randomness**: a distribution over deterministic
streaming algorithms. -/
abbrev Randomized (σ α β : Type*) : Type _ :=
  PMF (Algorithm σ α β)

namespace Randomized

variable {σ α β : Type*}

/-- The probability that the algorithm drawn from `μ` gives an answer on the stream `s` that is not
related to `s` by `R`. -/
@[expose] noncomputable def errorProb (μ : Randomized σ α β) (R : List α → β → Prop)
    (s : List α) : ℝ :=
  (μ.toOuterMeasure {A | ¬R s (A.run s)}).toReal

/-- `μ` answers `R` with error at most `ε` on streams of length at most `m`. -/
@[expose] def Solves (μ : Randomized σ α β) (ε : ℝ) (R : List α → β → Prop) (m : ℕ) : Prop :=
  ∀ s : List α, s.length ≤ m → μ.errorProb R s ≤ ε

/-- Every algorithm that `μ` can draw uses at most `b` bits of memory on streams of length at most
`m`. -/
@[expose] def SpaceLE (μ : Randomized σ α β) (m b : ℕ) : Prop :=
  ∀ A ∈ μ.support, A.SpaceLE m b

theorem Solves.mono {μ : Randomized σ α β} {ε ε' : ℝ} {R : List α → β → Prop} {m m' : ℕ}
    (h : μ.Solves ε R m) (hε : ε ≤ ε') (hm : m' ≤ m) : μ.Solves ε' R m' :=
  fun s hs => (h s (hs.trans hm)).trans hε

theorem SpaceLE.mono {μ : Randomized σ α β} {m m' b : ℕ} (h : μ.SpaceLE m b) (hm : m' ≤ m) :
    μ.SpaceLE m' b :=
  fun A hA => (h A hA).mono hm

/-- A deterministic algorithm that is always correct solves with error zero. -/
theorem solves_pure (A : Algorithm σ α β) {R : List α → β → Prop} {m : ℕ}
    (hA : ∀ s : List α, s.length ≤ m → R s (A.run s)) :
    Solves (PMF.pure A) 0 R m := by
  classical
  intro s hs
  unfold errorProb
  rw [PMF.toOuterMeasure_pure_apply]
  split_ifs with h
  · exact absurd (hA s hs) h
  · rfl

/-- A deterministic algorithm keeps its memory bound as a randomized one. -/
theorem spaceLE_pure {A : Algorithm σ α β} {m b : ℕ} (hA : A.SpaceLE m b) :
    SpaceLE (PMF.pure A) m b := by
  intro A' hA'
  rw [PMF.support_pure, Set.mem_singleton_iff] at hA'
  exact hA' ▸ hA

/-- The error of an algorithm drawn with a uniformly random seed is the fraction of the seeds on
which it errs. -/
theorem errorProb_map_uniformOfFintype {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (F : Ω → Algorithm σ α β) (R : List α → β → Prop) (s : List α)
    [DecidablePred fun ω => ¬R s ((F ω).run s)] :
    errorProb ((Probability.PMF.uniformOfFintype Ω).map F) R s =
      Finset.dens {ω | ¬R s ((F ω).run s)} := by
  unfold errorProb
  rw [PMF.toOuterMeasure_map_apply, Finset.nnratCast_dens]
  exact Probability.PMF.toOuterMeasure_uniformOfFintype_toReal {ω | ¬R s ((F ω).run s)}

/-- Reducing every algorithm drawn from `μ` to `R'` by `Algorithm.reduce` keeps the error, when
the answer of `A` related to the reduced stream by `R` is mapped by `d` to an answer related to the
original stream by `R'`. -/
theorem errorProb_map_reduce_le {α' β' : Type*} (μ : Randomized σ α β) (p : List α) (g : α' → α)
    (d : β → β') {R : List α → β → Prop} {R' : List α' → β' → Prop} (s : List α')
    (hR : ∀ c, R (p ++ s.map g) c → R' s (d c)) :
    errorProb (μ.map fun A => A.reduce p g d) R' s ≤ μ.errorProb R (p ++ s.map g) := by
  unfold errorProb
  rw [PMF.toOuterMeasure_map_apply]
  refine ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (μ.toOuterMeasure.mono fun A hA => ?_)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Algorithm.run_reduce] at hA ⊢
  exact fun h => hA (hR _ h)

/-- Reducing every algorithm drawn from `μ` keeps the memory bound, with the prefix counted in the
stream length. -/
theorem SpaceLE.map_reduce {α' β' : Type*} {μ : Randomized σ α β} {m b : ℕ} (p : List α)
    (h : μ.SpaceLE (p.length + m) b) (g : α' → α) (d : β → β') :
    SpaceLE (μ.map fun A => A.reduce p g d) m b := by
  intro A' hA'
  rw [PMF.support_map] at hA'
  obtain ⟨A, hA, rfl⟩ := hA'
  exact (h A hA).reduce p g d

end Randomized

end Cslib.Streaming
