/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.ENat.Lattice

/-!
# Deterministic communication protocols

Alice holds `x : X` and Bob holds `y : Y`. A deterministic protocol is a binary tree whose internal
nodes are owned by one of the players, who sends one bit computed from their input to choose the
branch, and whose leaves are labelled by outputs (`Protocol.run`)
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]. Its depth is the number of bits sent in
the worst case, and a protocol of depth `d` has at most `2 ^ d` leaves
(`Protocol.leafCount_le_two_pow_depth`). A function of the two inputs *solves* a relation `R` on
inputs from `A × B` when its value on every such pair is related to the pair (`Solves`), and a
protocol solves `R` when its output does (`Protocol.Solves`); the communication complexity of `R`
on `A × B` is the least depth of a protocol solving it, or `⊤` if there is none
(`Protocol.ecomplexity`) [Kushilevitz and Nisan, Chapter 5][KushilevitzNisan1997]. The
communication complexity of computing a function `f` is that of the relation `f x y = z` on all
inputs (`Protocol.ecomplexityFun`), and a protocol solves that relation exactly when it computes
`f` (`Protocol.solves_univ_iff`). A protocol can be run on transformed inputs (`Protocol.comap`).

Alice can send a bit string in as many bits (`Protocol.aliceSend`), so every Boolean function of
Alice's `n` bits and Bob's input has a protocol with `n + 1` bits: Alice sends her input and Bob
announces the value (`Protocol.ecomplexityFun_le_succ`).

## Main definitions

* `Cslib.Communication.Solves`: a function of the two inputs solves a relation.
* `Cslib.Communication.Protocol`: deterministic two-party protocols.
* `Cslib.Communication.Protocol.run`, `Cslib.Communication.Protocol.depth`,
  `Cslib.Communication.Protocol.leafCount`, `Cslib.Communication.Protocol.Solves`.
* `Cslib.Communication.Protocol.ecomplexity`: the communication complexity of a relation.
* `Cslib.Communication.Protocol.ecomplexityFun`: the communication complexity of a function.
* `Cslib.Communication.Protocol.comap`: running a protocol on transformed inputs.
* `Cslib.Communication.Protocol.aliceSend`: Alice sends a bit string.

## Main results

* `Cslib.Communication.Protocol.leafCount_pos`,
  `Cslib.Communication.Protocol.leafCount_le_two_pow_depth`: a protocol has at least one and at
  most `2 ^ depth` leaves.
* `Cslib.Communication.Protocol.ecomplexity_le_iff`,
  `Cslib.Communication.Protocol.le_ecomplexity_iff`: upper and lower bounds on communication
  complexity.
* `Cslib.Communication.Protocol.ecomplexityFun_le_iff`,
  `Cslib.Communication.Protocol.le_ecomplexityFun_iff`: the same for functions.
* `Cslib.Communication.Protocol.ecomplexityFun_le_succ`: the trivial protocol.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

section Solves

variable {X Y Z : Type*}

/-- A function `f` of Alice's input `x : X` and Bob's input `y : Y` *solves* the relation `R` on
`A × B` when `f x y` is related to `x` and `y` for every pair from `A × B`. A protocol solves a
relation when its output does (`Protocol.Solves`). -/
def Solves (f : X → Y → Z) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, R x y (f x y)

variable {f : X → Y → Z} {R R' : X → Y → Z → Prop} {A A' : Set X} {B B' : Set Y}

/-- A function solving a relation on `A × B` solves it on smaller sets. -/
theorem Solves.mono (h : Solves f R A B) (hA : A' ⊆ A) (hB : B' ⊆ B) : Solves f R A' B' :=
  fun x hx y hy => h x (hA hx) y (hB hy)

/-- A function solving a relation solves every weaker relation. -/
theorem Solves.of_imp (h : Solves f R A B) (hR : ∀ x y z, R x y z → R' x y z) :
    Solves f R' A B :=
  fun x hx y hy => hR x y _ (h x hx y hy)

end Solves

/-- A deterministic protocol between Alice, holding `x : X`, and Bob, holding `y : Y`, with
outputs in `Z`. -/
inductive Protocol (X Y Z : Type*) where
  /-- Output `z`. -/
  | output (z : Z)
  /-- Alice sends `send x` and the protocol continues with `ifFalse` or `ifTrue`. -/
  | alice (send : X → Bool) (ifFalse ifTrue : Protocol X Y Z)
  /-- Bob sends `send y` and the protocol continues with `ifFalse` or `ifTrue`. -/
  | bob (send : Y → Bool) (ifFalse ifTrue : Protocol X Y Z)

namespace Protocol

variable {X Y Z : Type*}

/-- The output of a protocol when Alice holds `x` and Bob holds `y`. -/
def run : Protocol X Y Z → X → Y → Z
  | output z, _, _ => z
  | alice send p₀ p₁, x, y => cond (send x) (p₁.run x y) (p₀.run x y)
  | bob send p₀ p₁, x, y => cond (send y) (p₁.run x y) (p₀.run x y)

/-- The number of bits sent in the worst case. -/
def depth : Protocol X Y Z → ℕ
  | output _ => 0
  | alice _ p₀ p₁ => max p₀.depth p₁.depth + 1
  | bob _ p₀ p₁ => max p₀.depth p₁.depth + 1

/-- The number of leaves. -/
def leafCount : Protocol X Y Z → ℕ
  | output _ => 1
  | alice _ p₀ p₁ => p₀.leafCount + p₁.leafCount
  | bob _ p₀ p₁ => p₀.leafCount + p₁.leafCount

@[simp] theorem run_output (z : Z) (x : X) (y : Y) : (output z : Protocol X Y Z).run x y = z :=
  rfl

@[simp] theorem run_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z) (x : X) (y : Y) :
    (alice send p₀ p₁).run x y = cond (send x) (p₁.run x y) (p₀.run x y) :=
  rfl

@[simp] theorem run_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z) (x : X) (y : Y) :
    (bob send p₀ p₁).run x y = cond (send y) (p₁.run x y) (p₀.run x y) :=
  rfl

@[simp] theorem depth_output (z : Z) : (output z : Protocol X Y Z).depth = 0 :=
  rfl

@[simp] theorem depth_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z) :
    (alice send p₀ p₁).depth = max p₀.depth p₁.depth + 1 :=
  rfl

@[simp] theorem depth_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z) :
    (bob send p₀ p₁).depth = max p₀.depth p₁.depth + 1 :=
  rfl

@[simp] theorem leafCount_output (z : Z) : (output z : Protocol X Y Z).leafCount = 1 :=
  rfl

@[simp] theorem leafCount_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z) :
    (alice send p₀ p₁).leafCount = p₀.leafCount + p₁.leafCount :=
  rfl

@[simp] theorem leafCount_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z) :
    (bob send p₀ p₁).leafCount = p₀.leafCount + p₁.leafCount :=
  rfl

/-- A protocol sending `d` bits has at most `2 ^ d` leaves. -/
theorem leafCount_le_two_pow_depth (p : Protocol X Y Z) : p.leafCount ≤ 2 ^ p.depth := by
  induction p with
  | output z => simp
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀.trans (Nat.pow_le_pow_right (by decide) (le_max_left p₀.depth p₁.depth))
    have h₁ := ih₁.trans (Nat.pow_le_pow_right (by decide) (le_max_right p₀.depth p₁.depth))
    simp only [leafCount_alice, leafCount_bob, depth_alice, depth_bob, pow_succ]
    omega

/-- Every protocol has a leaf. -/
theorem leafCount_pos (p : Protocol X Y Z) : 0 < p.leafCount := by
  induction p with
  | output z => simp
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ =>
    simp only [leafCount_alice, leafCount_bob]
    omega

/-- A protocol solves the relation `R` on `A × B` when its output does: its output on every pair
of inputs from `A × B` is related to them. `Communication.Solves.mono` and
`Communication.Solves.of_imp` apply to it. -/
def Solves (p : Protocol X Y Z) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : Prop :=
  Communication.Solves p.run R A B

variable {p : Protocol X Y Z} {R R' : X → Y → Z → Prop} {A A' : Set X} {B B' : Set Y}

/-- The communication complexity of `R` on `A × B`: the least depth of a protocol solving it, or
`⊤` if there is none. -/
noncomputable def ecomplexity (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : ℕ∞ :=
  ⨅ p : {p : Protocol X Y Z // p.Solves R A B}, (p.1.depth : ℕ∞)

theorem ecomplexity_le_depth (hp : p.Solves R A B) : ecomplexity R A B ≤ p.depth :=
  iInf_le (fun p : {p : Protocol X Y Z // p.Solves R A B} => (p.1.depth : ℕ∞)) ⟨p, hp⟩

theorem ecomplexity_ne_top_iff :
    ecomplexity R A B ≠ ⊤ ↔ ∃ p : Protocol X Y Z, p.Solves R A B := by
  rw [ecomplexity, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- When some protocol solves `R`, the least depth is attained. -/
theorem exists_solves_depth_eq_ecomplexity (h : ∃ p : Protocol X Y Z, p.Solves R A B) :
    ∃ p : Protocol X Y Z, p.Solves R A B ∧ (p.depth : ℕ∞) = ecomplexity R A B := by
  have : Nonempty {p : Protocol X Y Z // p.Solves R A B} := nonempty_subtype.mpr h
  obtain ⟨⟨p, hp⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun p : {p : Protocol X Y Z // p.Solves R A B} => (p.1.depth : ℕ∞))
  exact ⟨p, hp, hmin⟩

/-- Upper bounds on communication complexity: `R` has communication complexity at most `k` on
`A × B` exactly when some protocol of depth at most `k` solves it. -/
theorem ecomplexity_le_iff {k : ℕ} :
    ecomplexity R A B ≤ k ↔ ∃ p : Protocol X Y Z, p.Solves R A B ∧ p.depth ≤ k := by
  constructor
  · intro h
    obtain ⟨p, hp, hdepth⟩ := exists_solves_depth_eq_ecomplexity
      (ecomplexity_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top k) h))
    exact ⟨p, hp, by exact_mod_cast hdepth.trans_le h⟩
  · rintro ⟨p, hp, hk⟩
    exact (ecomplexity_le_depth hp).trans (by exact_mod_cast hk)

/-- Lower bounds on communication complexity are lower bounds on the depth of every protocol
solving the relation, including when there is none. -/
theorem le_ecomplexity_iff {k : ℕ∞} :
    k ≤ ecomplexity R A B ↔ ∀ p : Protocol X Y Z, p.Solves R A B → k ≤ p.depth := by
  simp only [ecomplexity, le_iInf_iff, Subtype.forall]

/-- Solving a relation on larger sets is harder. -/
theorem ecomplexity_mono (hA : A' ⊆ A) (hB : B' ⊆ B) : ecomplexity R A' B' ≤ ecomplexity R A B :=
  le_iInf fun p => iInf_le_of_le ⟨p.1, p.2.mono hA hB⟩ le_rfl

/-! ### Computing a function -/

section Fun

/-- The communication complexity of computing `f` on all inputs: the least depth of a protocol
whose output is `f x y` on every `x` and `y`, or `⊤` if there is none. It is `ecomplexity` of the
relation `f x y = z` on all inputs. -/
noncomputable def ecomplexityFun (f : X → Y → Z) : ℕ∞ :=
  ecomplexity (fun x y z => f x y = z) Set.univ Set.univ

variable {f : X → Y → Z}

/-- A protocol solves the relation `f x y = z` on all inputs when it computes `f`. -/
theorem solves_univ_iff : p.Solves (fun x y z => f x y = z) Set.univ Set.univ ↔ p.run = f :=
  ⟨fun h => funext₂ fun x y => (h x trivial y trivial).symm, fun h x _ y _ => by rw [h]⟩

theorem ecomplexityFun_le_depth (hp : p.run = f) : ecomplexityFun f ≤ p.depth :=
  ecomplexity_le_depth (solves_univ_iff.mpr hp)

/-- Computing `f` has communication complexity at most `k` exactly when some protocol of depth at
most `k` computes `f`. -/
theorem ecomplexityFun_le_iff {k : ℕ} :
    ecomplexityFun f ≤ k ↔ ∃ p : Protocol X Y Z, p.run = f ∧ p.depth ≤ k := by
  simp only [ecomplexityFun, ecomplexity_le_iff, solves_univ_iff]

/-- Lower bounds on the communication complexity of `f` are lower bounds on the depth of every
protocol computing `f`, including when there is none. -/
theorem le_ecomplexityFun_iff {k : ℕ∞} :
    k ≤ ecomplexityFun f ↔ ∀ p : Protocol X Y Z, p.run = f → k ≤ p.depth := by
  simp only [ecomplexityFun, le_ecomplexity_iff, solves_univ_iff]

end Fun

/-! ### Changing the inputs -/

variable {X' Y' : Type*}

/-- The protocol `p` run on `f x'` and `g y'`: Alice computes her bits from `f x'` and Bob his
from `g y'`. -/
def comap (f : X' → X) (g : Y' → Y) : Protocol X Y Z → Protocol X' Y' Z
  | output z => output z
  | alice send p₀ p₁ => alice (fun x => send (f x)) (p₀.comap f g) (p₁.comap f g)
  | bob send p₀ p₁ => bob (fun y => send (g y)) (p₀.comap f g) (p₁.comap f g)

@[simp] theorem run_comap (f : X' → X) (g : Y' → Y) (p : Protocol X Y Z) (x : X') (y : Y') :
    (p.comap f g).run x y = p.run (f x) (g y) := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [comap, ih₀, ih₁]

@[simp] theorem depth_comap (f : X' → X) (g : Y' → Y) (p : Protocol X Y Z) :
    (p.comap f g).depth = p.depth := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [comap, ih₀, ih₁]

@[simp] theorem leafCount_comap (f : X' → X) (g : Y' → Y) (p : Protocol X Y Z) :
    (p.comap f g).leafCount = p.leafCount := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [comap, ih₀, ih₁]

/-! ### Sending a bit string -/

/-- Alice sends the `n` bits of `msg x`, first bit first, after which the protocol continues with
`cont` of the bits sent. -/
def aliceSend : (n : ℕ) → (X → BitString n) → (BitString n → Protocol X Y Z) → Protocol X Y Z
  | 0, _, cont => cont Fin.elim0
  | n + 1, msg, cont => alice (fun x => msg x 0)
      (aliceSend n (fun x => Fin.tail (msg x)) fun m => cont (Fin.cons false m))
      (aliceSend n (fun x => Fin.tail (msg x)) fun m => cont (Fin.cons true m))

@[simp] theorem run_aliceSend (n : ℕ) (msg : X → BitString n) (cont : BitString n → Protocol X Y Z)
    (x : X) (y : Y) : (aliceSend n msg cont).run x y = (cont (msg x)).run x y := by
  induction n with
  | zero => rw [aliceSend, Subsingleton.elim (msg x) Fin.elim0]
  | succ n ih =>
    simp only [aliceSend, run_alice, ih]
    conv_rhs => rw [← Fin.cons_self_tail (msg x)]
    cases msg x 0 <;> rfl

/-- Sending `n` bits adds at most `n` to the depth. -/
theorem depth_aliceSend_le {n d : ℕ} {msg : X → BitString n} {cont : BitString n → Protocol X Y Z}
    (h : ∀ m, (cont m).depth ≤ d) : (aliceSend n msg cont).depth ≤ n + d := by
  induction n generalizing d with
  | zero => simpa [aliceSend] using h _
  | succ n ih =>
    simp only [aliceSend, depth_alice]
    have h₀ := ih (cont := fun m => cont (Fin.cons false m)) (msg := fun x => Fin.tail (msg x))
      fun m => h _
    have h₁ := ih (cont := fun m => cont (Fin.cons true m)) (msg := fun x => Fin.tail (msg x))
      fun m => h _
    omega

/-- **The trivial protocol.** Every Boolean function of Alice's `n` bits and Bob's input has a
protocol with `n + 1` bits: Alice sends her input and Bob announces the value. -/
theorem ecomplexityFun_le_succ {n : ℕ} (f : BitString n → Y → Bool) :
    ecomplexityFun f ≤ n + 1 := by
  have h := ecomplexityFun_le_iff (f := f) (k := n + 1)
  push_cast at h
  refine h.mpr ⟨aliceSend n id fun m => bob (f m) (output false) (output true),
    funext₂ fun x y => ?_, depth_aliceSend_le fun m => by simp⟩
  simp only [run_aliceSend, id, run_bob, run_output]
  cases f x y <;> rfl

end Protocol

end Cslib.Communication
