/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Protocol
public import Cslib.Foundations.Data.BitString
public import Cslib.Probability.PMF
public import Mathlib.Basic.Real.Basic
import Complexity.Probability.PMF.Event
import Complexity.Probability.Minimax
import Complexity.Probability.PMF
import Mathlib.Order.SuccPred.ENat

/-!
# Randomized communication protocols

In a *public-coin* protocol the players share random bits, which they use to draw a deterministic
protocol from a distribution and run it; so a public-coin protocol is a distribution over
deterministic protocols (`PublicCoin`). In a *private-coin* protocol Alice and Bob hold separate
uniformly random bit strings of `a` and `b` bits, and a deterministic protocol computes the bits
sent from each player's input and random bits (`PrivateCoin`)
[Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997].

A randomized protocol solves a relation `R` on `A × B` with error `ε` when, on every pair of inputs
from `A × B`, its output is not related to the inputs with probability at most `ε`
(`PublicCoin.Solves`, `PrivateCoin.Solves`). Cost bounds the tree depth over the random choices,
including branches unreachable by any input (`PublicCoin.depth`, `Protocol.depth`). The public- and
private-coin communication complexities are the least costs (`PublicCoin.ecomplexity`,
`PrivateCoin.ecomplexity`).

Deterministic protocols are both (`PublicCoin.ecomplexity_le_protocol`,
`PrivateCoin.ecomplexity_le_protocol`), and the players of a private-coin protocol can draw their
random bits from public coins (`PrivateCoin.toPublicCoin`,
`PublicCoin.ecomplexity_le_privateCoin`). Newman's theorem bounds the converse
(`PrivateCoin.ecomplexity_le_add`).

If a public-coin protocol has error at most `ε` on every pair of inputs from `A × B`, then for every
distribution `ν` on `A × B` some protocol it can draw has error at most `ε` on inputs drawn from `ν`
(`PublicCoin.Solves.exists_distributionalError_le`). This averaging argument
(`Probability.PMF.exists_mem_support_toOuterMeasure_le`) is the easy direction of Yao's principle
[Yao1977], and turns lower bounds on deterministic protocols over a distribution into lower bounds
on randomized ones.

## Main definitions

* `Cslib.Communication.PublicCoin`: public-coin protocols, as distributions over deterministic
  protocols, with `PublicCoin.depth`, `PublicCoin.errorProb`, `PublicCoin.Solves` and
  `PublicCoin.ecomplexity`.
* `Cslib.Communication.PrivateCoin`: private-coin protocols, with `PrivateCoin.errorProb`,
  `PrivateCoin.Solves` and `PrivateCoin.ecomplexity`.
* `Cslib.Communication.PrivateCoin.toPublicCoin`: drawing the private random bits publicly.
* `Cslib.Communication.Protocol.distributionalError`: the error of a deterministic protocol on
  inputs drawn from a distribution.

## Main results

* `Cslib.Communication.PublicCoin.ecomplexity_le_protocol`,
  `Cslib.Communication.PrivateCoin.ecomplexity_le_protocol`: randomness does not hurt.
* `Cslib.Communication.PublicCoin.ecomplexity_le_privateCoin`: public coins can replace private
  coins.
* `Cslib.Communication.PublicCoin.Solves.exists_distributionalError_le`: the averaging argument.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

@[expose] public section

namespace Cslib.Communication

open Probability

variable {X Y Z : Type*}

/-- A public-coin protocol between Alice, holding `x : X`, and Bob, holding `y : Y`: the players
use shared random bits to draw a deterministic protocol from this distribution, and run it. -/
abbrev PublicCoin (X Y Z : Type*) : Type _ :=
  PMF (Protocol X Y Z)

/-- The error of a deterministic protocol on inputs drawn from `ν`: the probability that its output
on a pair of inputs drawn from `ν` is not related to them by `R`. -/
noncomputable def Protocol.distributionalError (p : Protocol X Y Z) (ν : PMF (X × Y))
    (R : X → Y → Z → Prop) : ℝ :=
  (ν.toOuterMeasure {q | ¬R q.1 q.2 (p.run q.1 q.2)}).toReal

namespace PublicCoin

/-- The supremum of the tree depths of protocols in the support, or `⊤` if these depths are
unbounded. Each tree's depth counts even branches unreachable by any input. -/
noncomputable def depth (μ : PublicCoin X Y Z) : ℕ∞ :=
  ⨆ p ∈ μ.support, (p.depth : ℕ∞)

/-- The probability that the protocol drawn from `μ` gives an output on `x` and `y` that is not
related to them by `R`. -/
noncomputable def errorProb (μ : PublicCoin X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) : ℝ :=
  (μ.toOuterMeasure {p | ¬R x y (p.run x y)}).toReal

/-- A public-coin protocol `μ` solves `R` on `A × B` with error `ε` when on every pair of inputs
from `A × B` its output is not related to them with probability at most `ε`. -/
def Solves (μ : PublicCoin X Y Z) (ε : ℝ) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, μ.errorProb R x y ≤ ε

/-- The public-coin communication complexity of `R` on `A × B` with error `ε`: the least cost of
a public-coin protocol solving it with error `ε`, or `⊤` if there is none. -/
noncomputable def ecomplexity (ε : ℝ) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : ℕ∞ :=
  ⨅ μ : {μ : PublicCoin X Y Z // μ.Solves ε R A B}, μ.1.depth

/-- The public-coin communication complexity of computing `f` with error `ε`: `ecomplexity` of the
relation `f x y = z` on all inputs. -/
noncomputable def ecomplexityFun (ε : ℝ) (f : X → Y → Z) : ℕ∞ :=
  ecomplexity ε (fun x y z => f x y = z) Set.univ Set.univ

variable {μ : PublicCoin X Y Z} {p : Protocol X Y Z} {R : X → Y → Z → Prop} {A A' : Set X}
  {B B' : Set Y} {ε ε' : ℝ} {x : X} {y : Y}

theorem depth_le_iff {c : ℕ∞} : μ.depth ≤ c ↔ ∀ p ∈ μ.support, (p.depth : ℕ∞) ≤ c :=
  iSup₂_le_iff

theorem depth_le_depth (hp : p ∈ μ.support) : (p.depth : ℕ∞) ≤ μ.depth :=
  le_iSup₂ (f := fun p (_ : p ∈ μ.support) => (p.depth : ℕ∞)) p hp

@[simp] theorem depth_pure (p : Protocol X Y Z) : depth (PMF.pure p) = p.depth :=
  le_antisymm (depth_le_iff.mpr fun q hq => by rw [(PMF.mem_support_pure_iff _ _).mp hq])
    (depth_le_depth ((PMF.mem_support_pure_iff _ _).mpr rfl))

theorem errorProb_nonneg : 0 ≤ μ.errorProb R x y :=
  ENNReal.toReal_nonneg

theorem errorProb_le_one : μ.errorProb R x y ≤ 1 := by
  simpa [errorProb] using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.toOuterMeasure_le_one μ _)

open Classical in
theorem errorProb_pure (p : Protocol X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) :
    errorProb (PMF.pure p) R x y = if R x y (p.run x y) then 0 else 1 := by
  rw [errorProb, PMF.toOuterMeasure_pure_apply]
  split_ifs <;> simp_all

theorem Solves.mono (h : μ.Solves ε R A B) (hε : ε ≤ ε') (hA : A' ⊆ A) (hB : B' ⊆ B) :
    μ.Solves ε' R A' B' :=
  fun x hx y hy => (h x (hA hx) y (hB hy)).trans hε

/-- A deterministic protocol solving `R` is a public-coin protocol solving it with any
nonnegative error. -/
theorem solves_pure (hp : p.Solves R A B) (hε : 0 ≤ ε) :
    Solves (PMF.pure p) ε R A B :=
  fun x hx y hy => by simpa [errorProb_pure, hp x hx y hy] using hε

/-- **The averaging argument**, the easy direction of Yao's principle: if `μ` solves `R` on
`A × B` with error `ε`, then for every distribution `ν` on `A × B` some protocol that `μ` can draw
errs with probability at most `ε` on inputs drawn from `ν`. -/
theorem Solves.exists_distributionalError_le (h : μ.Solves ε R A B) (ν : PMF (X × Y))
    (hν : ∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B) :
    ∃ p ∈ μ.support, p.distributionalError ν R ≤ ε :=
  PMF.exists_mem_support_toOuterMeasure_le μ ν (fun p q => ¬R q.1 q.2 (p.run q.1 q.2))
    fun q hq => h _ (hν q hq).1 _ (hν q hq).2

theorem ecomplexity_le_depth (h : μ.Solves ε R A B) : ecomplexity ε R A B ≤ μ.depth :=
  iInf_le (fun μ : {μ : PublicCoin X Y Z // μ.Solves ε R A B} => μ.1.depth) ⟨μ, h⟩

theorem le_ecomplexity_iff {k : ℕ∞} :
    k ≤ ecomplexity ε R A B ↔ ∀ μ : PublicCoin X Y Z, μ.Solves ε R A B → k ≤ μ.depth := by
  simp only [ecomplexity, le_iInf_iff, Subtype.forall]

theorem ecomplexity_le_iff {k : ℕ} :
    ecomplexity ε R A B ≤ k ↔ ∃ μ : PublicCoin X Y Z, μ.Solves ε R A B ∧ μ.depth ≤ k := by
  refine ⟨fun h => ?_, fun ⟨μ, hμ, hk⟩ => (ecomplexity_le_depth hμ).trans hk⟩
  by_contra! hlt
  have : ((k + 1 : ℕ) : ℕ∞) ≤ ecomplexity ε R A B :=
    le_ecomplexity_iff.mpr fun μ hμ => by exact_mod_cast Order.add_one_le_of_lt (hlt μ hμ)
  have := this.trans h
  norm_cast at this
  omega

/-- Allowing more error makes a relation easier. -/
theorem ecomplexity_anti (hε : ε ≤ ε') : ecomplexity ε' R A B ≤ ecomplexity ε R A B :=
  le_iInf fun μ => iInf_le_of_le ⟨μ.1, μ.2.mono hε subset_rfl subset_rfl⟩ le_rfl

/-- Solving a relation on larger sets is harder. -/
theorem ecomplexity_mono (hA : A' ⊆ A) (hB : B' ⊆ B) :
    ecomplexity ε R A' B' ≤ ecomplexity ε R A B :=
  le_iInf fun μ => iInf_le_of_le ⟨μ.1, μ.2.mono le_rfl hA hB⟩ le_rfl

/-- Public-coin protocols with nonnegative error are at least as good as deterministic ones. -/
theorem ecomplexity_le_protocol (hε : 0 ≤ ε) :
    ecomplexity ε R A B ≤ Protocol.ecomplexity R A B :=
  le_iInf fun p => (ecomplexity_le_depth (solves_pure p.2 hε)).trans_eq (depth_pure p.1)

theorem ecomplexityFun_le_protocol {f : X → Y → Z} (hε : 0 ≤ ε) :
    ecomplexityFun ε f ≤ Protocol.ecomplexityFun f :=
  ecomplexity_le_protocol hε

/-- Precomposing the inputs does not make a function harder: the players apply `a` and `b` to
their inputs and run a protocol for `f`. -/
theorem ecomplexityFun_comap_le {X' Y' : Type*} (f : X → Y → Z) (a : X' → X) (b : Y' → Y) :
    ecomplexityFun ε (fun x y => f (a x) (b y)) ≤ ecomplexityFun ε f := by
  refine le_ecomplexity_iff.mpr fun μ hμ => ?_
  refine (ecomplexity_le_depth (μ := μ.map (Protocol.comap a b)) fun x _ y _ => ?_).trans ?_
  · have h := hμ (a x) trivial (b y) trivial
    rw [errorProb] at h ⊢
    rw [PMF.toOuterMeasure_map_apply]
    convert h using 3
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Protocol.run_comap]
  · refine depth_le_iff.mpr fun p hp => ?_
    obtain ⟨p', hp', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    rw [Protocol.depth_comap]
    exact depth_le_depth hp'

end PublicCoin

/-- A private-coin protocol in which Alice, holding `x : X`, also holds `a` and Bob, holding
`y : Y`, also holds `b` private uniformly random bits: a deterministic protocol whose inputs are
each player's input together with their random bits. -/
abbrev PrivateCoin (a b : ℕ) (X Y Z : Type*) : Type _ :=
  Protocol (X × BitString a) (Y × BitString b) Z

namespace PrivateCoin

variable {a b : ℕ}

/-- The deterministic protocol obtained by fixing Alice's random bits to `r.1` and Bob's to
`r.2`. -/
def fix (P : PrivateCoin a b X Y Z) (r : BitString a × BitString b) : Protocol X Y Z :=
  Protocol.comap (fun x => (x, r.1)) (fun y => (y, r.2)) P

@[simp] theorem run_fix (P : PrivateCoin a b X Y Z) (r : BitString a × BitString b) (x : X)
    (y : Y) : (P.fix r).run x y = P.run (x, r.1) (y, r.2) :=
  Protocol.run_comap _ _ P x y

@[simp] theorem depth_fix (P : PrivateCoin a b X Y Z) (r : BitString a × BitString b) :
    (P.fix r).depth = P.depth :=
  Protocol.depth_comap _ _ P

/-- The probability, over both players' random bits, that the output of `P` on `x` and `y` is not
related to them by `R`. -/
noncomputable def errorProb (P : PrivateCoin a b X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) :
    ℝ :=
  ((PMF.uniformOfFintype (BitString a × BitString b)).toOuterMeasure
    {r | ¬R x y (P.run (x, r.1) (y, r.2))}).toReal

/-- A private-coin protocol `P` solves `R` on `A × B` with error `ε` when on every pair of inputs
from `A × B` its output is not related to them with probability at most `ε`. -/
def Solves (P : PrivateCoin a b X Y Z) (ε : ℝ) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) :
    Prop :=
  ∀ x ∈ A, ∀ y ∈ B, P.errorProb R x y ≤ ε

/-- The private-coin communication complexity of `R` on `A × B` with error `ε`: the least depth
of a private-coin protocol solving it with error `ε`, with any numbers of random bits, or `⊤` if
there is none. -/
noncomputable def ecomplexity (ε : ℝ) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : ℕ∞ :=
  ⨅ (a : ℕ) (b : ℕ) (P : {P : PrivateCoin a b X Y Z // P.Solves ε R A B}), (P.1.depth : ℕ∞)

/-- The private-coin communication complexity of computing `f` with error `ε`: `ecomplexity` of
the relation `f x y = z` on all inputs. -/
noncomputable def ecomplexityFun (ε : ℝ) (f : X → Y → Z) : ℕ∞ :=
  ecomplexity ε (fun x y z => f x y = z) Set.univ Set.univ

/-- The public-coin protocol in which the players draw the random bits of `P` from shared coins:
it draws `P.fix r` for uniformly random `r`. -/
noncomputable def toPublicCoin (P : PrivateCoin a b X Y Z) : PublicCoin X Y Z :=
  (PMF.uniformOfFintype (BitString a × BitString b)).map P.fix

variable {P : PrivateCoin a b X Y Z} {R : X → Y → Z → Prop} {A A' : Set X} {B B' : Set Y}
  {ε ε' : ℝ}

@[simp] theorem errorProb_toPublicCoin (P : PrivateCoin a b X Y Z) (R : X → Y → Z → Prop)
    (x : X) (y : Y) : P.toPublicCoin.errorProb R x y = P.errorProb R x y := by
  simp only [PublicCoin.errorProb, toPublicCoin, PMF.toOuterMeasure_map_apply, errorProb]
  congr 2
  ext r
  simp

theorem depth_toPublicCoin_le (P : PrivateCoin a b X Y Z) : P.toPublicCoin.depth ≤ P.depth := by
  refine PublicCoin.depth_le_iff.mpr fun p hp => ?_
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  simp

theorem Solves.toPublicCoin (h : P.Solves ε R A B) : P.toPublicCoin.Solves ε R A B :=
  fun x hx y hy => (errorProb_toPublicCoin P R x y).trans_le (h x hx y hy)

theorem Solves.mono (h : P.Solves ε R A B) (hε : ε ≤ ε') (hA : A' ⊆ A) (hB : B' ⊆ B) :
    P.Solves ε' R A' B' :=
  fun x hx y hy => (h x (hA hx) y (hB hy)).trans hε

/-- A deterministic protocol solving `R`, run while ignoring the random bits, solves it with any
nonnegative error. -/
theorem solves_comap {p : Protocol X Y Z} (hp : p.Solves R A B) (hε : 0 ≤ ε) :
    Solves (p.comap Prod.fst Prod.fst : PrivateCoin a b X Y Z) ε R A B := by
  intro x hx y hy
  have : {r : BitString a × BitString b |
      ¬R x y ((p.comap Prod.fst Prod.fst).run (x, r.1) (y, r.2))} = ∅ := by
    ext r
    simpa using hp x hx y hy
  rw [errorProb, this, MeasureTheory.measure_empty, ENNReal.toReal_zero]
  exact hε

theorem ecomplexity_le_depth (h : P.Solves ε R A B) : ecomplexity ε R A B ≤ P.depth :=
  (iInf_le _ a).trans <| (iInf_le _ b).trans <|
    iInf_le (fun P : {P : PrivateCoin a b X Y Z // P.Solves ε R A B} => (P.1.depth : ℕ∞)) ⟨P, h⟩

theorem le_ecomplexity_iff {k : ℕ∞} :
    k ≤ ecomplexity ε R A B ↔
      ∀ a b (P : PrivateCoin a b X Y Z), P.Solves ε R A B → k ≤ P.depth := by
  simp only [ecomplexity, le_iInf_iff, Subtype.forall]

theorem ecomplexity_le_iff {k : ℕ} :
    ecomplexity ε R A B ≤ k ↔
      ∃ a b, ∃ P : PrivateCoin a b X Y Z, P.Solves ε R A B ∧ P.depth ≤ k := by
  refine ⟨fun h => ?_, fun ⟨a, b, P, hP, hk⟩ =>
    (ecomplexity_le_depth hP).trans (by exact_mod_cast hk)⟩
  by_contra! hlt
  have : ((k + 1 : ℕ) : ℕ∞) ≤ ecomplexity ε R A B :=
    le_ecomplexity_iff.mpr fun a b P hP => by exact_mod_cast hlt a b P hP
  have := this.trans h
  norm_cast at this
  omega

/-- Allowing more error makes a relation easier. -/
theorem ecomplexity_anti (hε : ε ≤ ε') : ecomplexity ε' R A B ≤ ecomplexity ε R A B :=
  le_ecomplexity_iff.mpr fun _ _ _ hP => ecomplexity_le_depth (hP.mono hε subset_rfl subset_rfl)

/-- Solving a relation on larger sets is harder. -/
theorem ecomplexity_mono (hA : A' ⊆ A) (hB : B' ⊆ B) :
    ecomplexity ε R A' B' ≤ ecomplexity ε R A B :=
  le_ecomplexity_iff.mpr fun _ _ _ hP => ecomplexity_le_depth (hP.mono le_rfl hA hB)

/-- Private-coin protocols with nonnegative error are at least as good as deterministic ones. -/
theorem ecomplexity_le_protocol (hε : 0 ≤ ε) :
    ecomplexity ε R A B ≤ Protocol.ecomplexity R A B :=
  le_iInf fun p => (ecomplexity_le_depth (a := 0) (b := 0) (solves_comap p.2 hε)).trans_eq
    (by rw [Protocol.depth_comap])

theorem ecomplexityFun_le_protocol {f : X → Y → Z} (hε : 0 ≤ ε) :
    ecomplexityFun ε f ≤ Protocol.ecomplexityFun f :=
  ecomplexity_le_protocol hε

end PrivateCoin

namespace PublicCoin

variable {R : X → Y → Z → Prop} {A : Set X} {B : Set Y} {ε : ℝ}

/-- Public coins can replace private coins. -/
theorem ecomplexity_le_privateCoin :
    ecomplexity ε R A B ≤ PrivateCoin.ecomplexity ε R A B :=
  PrivateCoin.le_ecomplexity_iff.mpr fun _ _ P hP =>
    (ecomplexity_le_depth hP.toPublicCoin).trans P.depth_toPublicCoin_le

theorem ecomplexityFun_le_privateCoin {f : X → Y → Z} :
    ecomplexityFun ε f ≤ PrivateCoin.ecomplexityFun ε f :=
  ecomplexity_le_privateCoin

end PublicCoin

end Cslib.Communication
