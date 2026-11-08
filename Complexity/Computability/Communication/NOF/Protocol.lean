/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Logic.Function.Basic

/-!
# Number-on-forehead protocols

In the *number-on-forehead* (NOF) model of multiparty communication, introduced by Chandra, Furst
and Lipton, players indexed by `ι` jointly hold an input `x : ∀ i, X i`, and player `i` sees every
part of the input except their own part `x i`, which is written on their forehead
[Jukna, Section 5.4, p. 140][Jukna2012]. What player `i` sees is `NOF.view i x : NOF.View X i`, the
input restricted to the other players. The players write bits on a shared blackboard.

A deterministic NOF protocol (`NOF.Protocol`) is a binary tree whose inner nodes are owned by a
player `i`, who writes a bit computed from what they see (a function of `NOF.View X i`), and whose
leaves are labelled by outputs (`NOF.Protocol.run`). Since the bit at a node of player `i` is a
function of `NOF.view i x`, it cannot depend on `x i` (`NOF.view_update_self`). The depth of the
tree bounds the number of bits written on any input. A protocol *solves* a relation `R` on a set `A`
of inputs when its output on every input of `A` is related to it (`NOF.Protocol.Solves`); the
communication complexity of `R` on `A` is the least depth of a protocol solving it, or `⊤` if there
is none (`NOF.Protocol.ecomplexity`), and the communication complexity of computing `f` is that of
the relation `f x = z` on all inputs (`NOF.Protocol.ecomplexityFun`). With two players the model is
the two-party model of `Cslib.Communication.Protocol`, since each player then sees exactly the other
player's input.

Player `i` can write `n` bits computed from what they see (`NOF.Protocol.sendBits`). So when player
`i`'s input is determined by `n` bits that another player `j ≠ i` sees, every Boolean function has
a protocol with `n + 1` bits: `j` writes those bits, after which `i` knows the whole input and
announces the value (`NOF.Protocol.ecomplexityFun_le_succ`).

## Main definitions

* `Cslib.Communication.NOF.View`, `Cslib.Communication.NOF.view`: what a player sees.
* `Cslib.Communication.NOF.Protocol`: deterministic NOF protocols, with
  `Cslib.Communication.NOF.Protocol.run` and `Cslib.Communication.NOF.Protocol.depth`.
* `Cslib.Communication.NOF.Protocol.Solves`, `Cslib.Communication.NOF.Protocol.ecomplexity`,
  `Cslib.Communication.NOF.Protocol.ecomplexityFun`: solving relations and communication
  complexity.
* `Cslib.Communication.NOF.Protocol.sendBits`: a player writes a bit string.

## Main results

* `Cslib.Communication.NOF.view_update_self`: a player does not see their own input.
* `Cslib.Communication.NOF.Protocol.ecomplexity_le_iff`,
  `Cslib.Communication.NOF.Protocol.le_ecomplexity_iff`: upper and lower bounds on communication
  complexity, and `Cslib.Communication.NOF.Protocol.ecomplexityFun_le_iff`,
  `Cslib.Communication.NOF.Protocol.le_ecomplexityFun_iff` for functions.
* `Cslib.Communication.NOF.Protocol.ecomplexityFun_le_succ`: the trivial protocol.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Communication.NOF

universe u v w

variable {ι : Type u} {X : ι → Type v} {Z : Type w}

/-- What player `i` sees: the parts of the input held on the other players' foreheads. -/
abbrev View (X : ι → Type v) (i : ι) : Type (max u v) :=
  ∀ j : {j // j ≠ i}, X j

/-- The part of the input `x` that player `i` sees. -/
def view (i : ι) (x : ∀ j, X j) : View X i :=
  fun j => x j

@[simp] theorem view_apply (i : ι) (x : ∀ j, X j) (j : {j // j ≠ i}) : view i x j = x j :=
  rfl

/-- **A player does not see their own input**: changing `x i` does not change what player `i`
sees. -/
theorem view_update_self [DecidableEq ι] (i : ι) (x : ∀ j, X j) (a : X i) :
    view i (Function.update x i a) = view i x :=
  funext fun j => Function.update_of_ne j.2 a x

/-- A deterministic number-on-forehead protocol with output in `Z`: a leaf labelled by an output,
or a node at which player `i` writes the bit `send (view i x)`, computed from what they see, and the
protocol continues with `ifFalse` or `ifTrue`. -/
inductive Protocol (X : ι → Type v) (Z : Type w) : Type (max u v w) where
  /-- The protocol ends with output `z`. -/
  | output (z : Z)
  /-- Player `i` writes the bit `send (view i x)` and the protocol continues accordingly. -/
  | speak (i : ι) (send : View X i → Bool) (ifFalse ifTrue : Protocol X Z)

namespace Protocol

/-- The output of the protocol on the input `x`. -/
def run : Protocol X Z → (∀ i, X i) → Z
  | output z, _ => z
  | speak i send p₀ p₁, x => cond (send (view i x)) (p₁.run x) (p₀.run x)

/-- The number of bits written in the worst case: the depth of the tree. -/
def depth : Protocol X Z → ℕ
  | output _ => 0
  | speak _ _ p₀ p₁ => max p₀.depth p₁.depth + 1

@[simp] theorem run_output (z : Z) (x : ∀ i, X i) : (output z : Protocol X Z).run x = z :=
  rfl

@[simp] theorem run_speak (i : ι) (send : View X i → Bool) (p₀ p₁ : Protocol X Z)
    (x : ∀ i, X i) : (speak i send p₀ p₁).run x = cond (send (view i x)) (p₁.run x) (p₀.run x) :=
  rfl

@[simp] theorem depth_output (z : Z) : (output z : Protocol X Z).depth = 0 :=
  rfl

@[simp] theorem depth_speak (i : ι) (send : View X i → Bool) (p₀ p₁ : Protocol X Z) :
    (speak i send p₀ p₁).depth = max p₀.depth p₁.depth + 1 :=
  rfl

/-! ### Solving relations and communication complexity -/

/-- A protocol solves the relation `R` on the set `A` of inputs when its output on every input of
`A` is related to it. -/
def Solves (p : Protocol X Z) (R : (∀ i, X i) → Z → Prop) (A : Set (∀ i, X i)) : Prop :=
  ∀ x ∈ A, R x (p.run x)

variable {p : Protocol X Z} {R R' : (∀ i, X i) → Z → Prop} {A A' : Set (∀ i, X i)}

theorem Solves.mono (h : p.Solves R A) (hA : A' ⊆ A) : p.Solves R A' :=
  fun x hx => h x (hA hx)

theorem Solves.of_imp (h : p.Solves R A) (hR : ∀ x z, R x z → R' x z) : p.Solves R' A :=
  fun x hx => hR _ _ (h x hx)

/-- The communication complexity of `R` on `A`: the least depth of a protocol solving it, or `⊤`
if there is none. -/
noncomputable def ecomplexity (R : (∀ i, X i) → Z → Prop) (A : Set (∀ i, X i)) : ℕ∞ :=
  ⨅ p : {p : Protocol X Z // p.Solves R A}, (p.1.depth : ℕ∞)

theorem ecomplexity_le_depth (hp : p.Solves R A) : ecomplexity R A ≤ p.depth :=
  iInf_le (fun p : {p : Protocol X Z // p.Solves R A} => (p.1.depth : ℕ∞)) ⟨p, hp⟩

theorem ecomplexity_ne_top_iff : ecomplexity R A ≠ ⊤ ↔ ∃ p : Protocol X Z, p.Solves R A := by
  rw [ecomplexity, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- When some protocol solves `R`, the least depth is attained. -/
theorem exists_solves_depth_eq_ecomplexity (h : ∃ p : Protocol X Z, p.Solves R A) :
    ∃ p : Protocol X Z, p.Solves R A ∧ (p.depth : ℕ∞) = ecomplexity R A := by
  have : Nonempty {p : Protocol X Z // p.Solves R A} := nonempty_subtype.mpr h
  obtain ⟨⟨p, hp⟩, hmin⟩ :=
    ENat.exists_eq_iInf (fun p : {p : Protocol X Z // p.Solves R A} => (p.1.depth : ℕ∞))
  exact ⟨p, hp, hmin⟩

/-- Upper bounds on communication complexity: `R` has communication complexity at most `k` on `A`
exactly when some protocol of depth at most `k` solves it. -/
theorem ecomplexity_le_iff {k : ℕ} :
    ecomplexity R A ≤ k ↔ ∃ p : Protocol X Z, p.Solves R A ∧ p.depth ≤ k := by
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
    k ≤ ecomplexity R A ↔ ∀ p : Protocol X Z, p.Solves R A → k ≤ p.depth := by
  simp only [ecomplexity, le_iInf_iff, Subtype.forall]

/-- Solving a relation on a larger set is harder. -/
theorem ecomplexity_mono (hA : A' ⊆ A) : ecomplexity R A' ≤ ecomplexity R A :=
  le_iInf fun p => iInf_le_of_le ⟨p.1, p.2.mono hA⟩ le_rfl

/-- The communication complexity of computing `f` on all inputs: `ecomplexity` of the relation
`f x = z` on all inputs. -/
noncomputable def ecomplexityFun (f : (∀ i, X i) → Z) : ℕ∞ :=
  ecomplexity (fun x z => f x = z) Set.univ

variable {f : (∀ i, X i) → Z}

/-- A protocol solves the relation `f x = z` on all inputs when it computes `f`. -/
theorem solves_univ_iff : p.Solves (fun x z => f x = z) Set.univ ↔ p.run = f :=
  ⟨fun h => funext fun x => (h x trivial).symm, fun h x _ => by rw [h]⟩

theorem ecomplexityFun_le_depth (hp : p.run = f) : ecomplexityFun f ≤ p.depth :=
  ecomplexity_le_depth (solves_univ_iff.mpr hp)

/-- Computing `f` has communication complexity at most `k` exactly when some protocol of depth at
most `k` computes `f`. -/
theorem ecomplexityFun_le_iff {k : ℕ} :
    ecomplexityFun f ≤ k ↔ ∃ p : Protocol X Z, p.run = f ∧ p.depth ≤ k := by
  simp only [ecomplexityFun, ecomplexity_le_iff, solves_univ_iff]

/-- Lower bounds on the communication complexity of `f` are lower bounds on the depth of every
protocol computing `f`, including when there is none. -/
theorem le_ecomplexityFun_iff {k : ℕ∞} :
    k ≤ ecomplexityFun f ↔ ∀ p : Protocol X Z, p.run = f → k ≤ p.depth := by
  simp only [ecomplexityFun, le_ecomplexity_iff, solves_univ_iff]

/-! ### Writing a bit string -/

/-- Player `i` writes the `n` bits of `msg (view i x)`, first bit first, after which the protocol
continues with `cont` of the bits written. -/
def sendBits (i : ι) :
    (n : ℕ) → (View X i → BitString n) → (BitString n → Protocol X Z) → Protocol X Z
  | 0, _, cont => cont Fin.elim0
  | n + 1, msg, cont => speak i (fun v => msg v 0)
      (sendBits i n (fun v => Fin.tail (msg v)) fun m => cont (Fin.cons false m))
      (sendBits i n (fun v => Fin.tail (msg v)) fun m => cont (Fin.cons true m))

@[simp] theorem run_sendBits (i : ι) (n : ℕ) (msg : View X i → BitString n)
    (cont : BitString n → Protocol X Z) (x : ∀ i, X i) :
    (sendBits i n msg cont).run x = (cont (msg (view i x))).run x := by
  induction n with
  | zero => rw [sendBits, Subsingleton.elim (msg (view i x)) Fin.elim0]
  | succ n ih =>
    simp only [sendBits, run_speak, ih]
    conv_rhs => rw [← Fin.cons_self_tail (msg (view i x))]
    cases msg (view i x) 0 <;> rfl

/-- Writing `n` bits adds at most `n` to the depth. -/
theorem depth_sendBits_le {i : ι} {n d : ℕ} {msg : View X i → BitString n}
    {cont : BitString n → Protocol X Z} (h : ∀ m, (cont m).depth ≤ d) :
    (sendBits i n msg cont).depth ≤ n + d := by
  induction n generalizing d with
  | zero => simpa [sendBits] using h _
  | succ n ih =>
    simp only [sendBits, depth_speak]
    have h₀ := ih (cont := fun m => cont (Fin.cons false m)) (msg := fun v => Fin.tail (msg v))
      fun m => h _
    have h₁ := ih (cont := fun m => cont (Fin.cons true m)) (msg := fun v => Fin.tail (msg v))
      fun m => h _
    omega

/-- **The trivial protocol.** If player `i`'s input is recovered by `decode` from `n` bits
`encode` that player `j ≠ i` computes from what they see, then every Boolean function has a
protocol with `n + 1` bits: player `j` writes the `n` bits, after which player `i` knows the whole
input and announces the value. -/
theorem ecomplexityFun_le_succ {i j : ι} (hij : i ≠ j) {n : ℕ}
    (encode : View X j → BitString n) (decode : BitString n → X i)
    (hdecode : ∀ x : ∀ k, X k, decode (encode (view j x)) = x i) (f : (∀ k, X k) → Bool) :
    ecomplexityFun f ≤ n + 1 := by
  classical
  -- After reading `m`, player `i` evaluates `f` with its own part replaced by `decode m`.
  let answer (m : BitString n) (v : View X i) : Bool :=
    f fun k => if h : k = i then h ▸ decode m else v ⟨k, h⟩
  have hanswer (x : ∀ k, X k) : answer (encode (view j x)) (view i x) = f x := by
    simp only [answer]
    congr 1
    funext k
    by_cases h : k = i
    · subst h
      simp [hdecode]
    · simp [h]
  have h := ecomplexityFun_le_iff (f := f) (k := n + 1)
  push_cast at h
  refine h.mpr ⟨sendBits j n encode fun m => speak i (answer m) (output false) (output true),
    funext fun x => ?_, depth_sendBits_le fun m => by simp⟩
  simp only [run_sendBits, run_speak, run_output, hanswer]
  cases f x <;> rfl

end Protocol

end Cslib.Communication.NOF
