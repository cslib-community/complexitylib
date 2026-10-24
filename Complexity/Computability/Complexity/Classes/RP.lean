/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP.Amplification
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.RepeatedTrials
public import Mathlib.Data.Fintype.Pi
import Complexity.Computability.Complexity.Classes.SharpP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.Fintype.BigOperators

/-!
# The classes RP and coRP

`RP` is defined like `BPP` (`Cslib.Complexity.BPP`), through deterministic polynomial-time
machines that read a random string, but with one-sided error
[Arora and Barak, Section 7.3][AroraBarak09]: `A ∈ RP enc` when there are a polynomial `p` and
a function `V : α × List Bool → Bool`, computable in polynomial time on inputs
`frame (enc a) ++ r`, such that for every member `a` of `A` at least half of the random strings
`r` of length `p (enc a).length` are accepted, and for every non-member none is. `coRP` contains
the complements of problems in `RP`.

Since an accepted random string is a certificate, `RP ⊆ NP` (`RP_subset_NP`). `ZPP`, with
`ZPP = RP ∩ coRP`, is defined in `Cslib.Complexity.ZPP`.

The error `1 / 2` can be made exponentially small [Arora and Barak, Chapter 7][AroraBarak09]: for
a polynomial `q`, run the decider on `q(n)` independent blocks of random bits, where `n` is the
length of the encoded instance, and accept when some run accepts (`Cslib.Complexity.repeatAny`).
A member is then rejected on at most a `2 ^ (-q(n))` fraction of the random strings
(`Cslib.Complexity.DecidesWithOneSidedErrorExponent`), and a non-member is still never accepted.
Two runs reject a member with probability at most `1 / 4`, so `RP ⊆ BPP`.

## Main definitions

* `Cslib.Complexity.DecidesWithOneSidedError`: the one-sided error condition.
* `Cslib.Complexity.RP`, `Cslib.Complexity.coRP`.
* `Cslib.Complexity.DecidesWithOneSidedErrorExponent`: one-sided error at most `2 ^ (-q(n))`.

## Main results

* `Cslib.Complexity.RP_subset_NP`, `Cslib.Complexity.coRP_subset_coNP`.
* `Cslib.Complexity.DecidesWithOneSidedError.repeatAny`: repetition reduces the error to
  `2 ^ (-q(n))`.
* `Cslib.Complexity.mem_RP_iff_forall_decidesWithOneSidedErrorExponent`: error reduction for `RP`.
* `Cslib.Complexity.RP_subset_BPP`, `Cslib.Complexity.coRP_subset_BPP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` decides `A` with one-sided error, using random strings whose length is `p` evaluated at the
length of the encoded instance: for every member `a` of `A` at least half of the random strings are
accepted, and for every non-member none is. -/
def DecidesWithOneSidedError (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 ^ p.eval (enc a).length ≤
      2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).card) ∧
    (a ∉ A → ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = false)

/-- The problems decided with one-sided error by polynomial-time machines reading polynomially
long random strings, with respect to the encoding `enc` of instances
[Arora and Barak, Section 7.3][AroraBarak09]. -/
def RP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      DecidesWithOneSidedError enc p V A}

/-- The problems whose complements are in `RP` [Arora and Barak, Section 7.3][AroraBarak09]. -/
def coRP (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ RP enc}

variable {enc : α ↪ List Bool}

theorem mem_RP {A : Set α} : A ∈ RP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      DecidesWithOneSidedError enc p V A :=
  Iff.rfl

theorem mem_coRP {A : Set α} : A ∈ coRP enc ↔ Aᶜ ∈ RP enc := Iff.rfl

/-- A random string accepted by a one-sided-error decider is a certificate: one-sided error gives
a verifier. -/
theorem DecidesWithOneSidedError.isVerifier {p : Polynomial ℕ} {V : α × List Bool → Bool}
    {A : Set α} (h : DecidesWithOneSidedError enc p V A) : IsVerifier enc p V A := by
  intro a
  constructor
  · intro ha
    have hpos := Nat.one_le_two_pow (n := p.eval (enc a).length)
    obtain ⟨r, hr⟩ : (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).Nonempty := by
      rw [← Finset.card_pos]
      have := (h a).1 ha
      omega
    exact ⟨List.ofFn r, List.length_ofFn, (Finset.mem_filter.1 hr).2⟩
  · rintro ⟨w, hw, hV⟩
    by_contra ha
    have := (h a).2 ha fun i => w[i.val]'(by omega)
    rw [show (List.ofFn fun i : Fin (p.eval (enc a).length) => w[i.val]'(by omega)) = w from
      List.ext_getElem (by simp [hw]) fun i _ _ => by simp] at this
    rw [hV] at this
    exact Bool.noConfusion this

/-- `RP ⊆ NP`: a random string accepted by a one-sided-error decider is a certificate. -/
theorem RP_subset_NP : RP enc ⊆ NP enc := fun _ ⟨p, V, hV, h⟩ => ⟨p, V, hV, h.isVerifier⟩

/-- `coRP ⊆ coNP`. -/
theorem coRP_subset_coNP : coRP enc ⊆ coNP enc := fun _ hA => RP_subset_NP hA

/-! ### Error reduction -/

/-- `V` decides `A` with one-sided error at most `2 ^ (-q(n))`, using random strings whose length is
`p` evaluated at the length `n` of the encoded instance: for every member `a` of `A` the rejected
random strings make up at most a `2 ^ (-q(n))` fraction, and for every non-member none is
accepted. -/
def DecidesWithOneSidedErrorExponent (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 ^ q.eval (enc a).length *
      (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = false).card ≤ 2 ^ p.eval (enc a).length) ∧
    (a ∉ A → ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = false)

/-- **Error reduction for `RP`** [Arora and Barak, Chapter 7][AroraBarak09]. The disjunction of
`q(n)` runs of a one-sided-error decider, on independent blocks of random bits, rejects a member
on at most a `2 ^ (-q(n))` fraction of the random strings, and never accepts a non-member. -/
theorem DecidesWithOneSidedError.repeatAny {p : Polynomial ℕ} {V : α × List Bool → Bool}
    {A : Set α} (h : DecidesWithOneSidedError enc p V A) (q : Polynomial ℕ) :
    DecidesWithOneSidedErrorExponent enc q (q * p) (Complexity.repeatAny enc q p V) A := by
  intro a
  -- on a member, a run rejects on at most half of its random strings
  have hR (ha : a ∈ A) : 2 * (Finset.univ.filter fun u : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn u) = false).card ≤ 2 ^ p.eval (enc a).length := by
    have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
    have hhalf := (h a).1 ha
    rw [← acceptCount] at hhalf
    omega
  have hlen : (q * p).eval (enc a).length = q.eval (enc a).length * p.eval (enc a).length :=
    Polynomial.eval_mul
  rw [hlen]
  set k := q.eval (enc a).length
  set m := p.eval (enc a).length
  set R := Finset.univ.filter fun u : Fin m → Bool => V (a, List.ofFn u) = false
  constructor
  · -- so all `k` runs reject on at most a `2 ^ (-k)` fraction
    intro ha
    replace hR := hR ha
    have hcard : (Finset.univ.filter fun x : BitString (k * m) =>
        Complexity.repeatAny enc q p V (a, List.ofFn x) = false).card ≤ R.card ^ k := by
      rw [← Fintype.card_piFinset_const, ← Finset.card_map BitString.blocksEquiv.toEmbedding]
      refine Finset.card_le_card fun ω hω => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hω
      rw [Finset.mem_filter, ← Bool.not_eq_true, repeatAny_ofFn_eq_true_iff] at hx
      simpa [Fintype.mem_piFinset, R] using hx.2
    calc 2 ^ k * (Finset.univ.filter fun x : BitString (k * m) =>
          Complexity.repeatAny enc q p V (a, List.ofFn x) = false).card
        ≤ 2 ^ k * R.card ^ k := Nat.mul_le_mul_left _ hcard
      _ = (2 * R.card) ^ k := (mul_pow _ _ _).symm
      _ ≤ (2 ^ m) ^ k := Nat.pow_le_pow_left hR k
      _ = 2 ^ (k * m) := by rw [← pow_mul, Nat.mul_comm]
  · -- on a non-member, no run accepts
    intro ha x
    rw [← Bool.not_eq_true, repeatAny_ofFn_eq_true_iff]
    simpa using fun i => (h a).2 ha (BitString.block x i)

namespace DecidesWithOneSidedErrorExponent

variable {q p : Polynomial ℕ} {V : α × List Bool → Bool} {A : Set α}

/-- One-sided error at most `2 ^ (-q(n)) ≤ 1 / 2` is one-sided error. -/
theorem decidesWithOneSidedError (h : DecidesWithOneSidedErrorExponent enc q p V A)
    (hq : ∀ n, 1 ≤ q.eval n) : DecidesWithOneSidedError enc p V A := fun a => by
  refine ⟨fun ha => ?_, (h a).2⟩
  have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
  have h2 : 2 ^ 1 ≤ 2 ^ q.eval (enc a).length := Nat.pow_le_pow_right (by norm_num) (hq _)
  have := (Nat.mul_le_mul_right _ h2).trans ((h a).1 ha)
  rw [← acceptCount]
  omega

/-- One-sided error at most `2 ^ (-q(n))` is error at most `2 ^ (-q(n))`. -/
theorem decidesWithErrorExponent (h : DecidesWithOneSidedErrorExponent enc q p V A) :
    DecidesWithErrorExponent enc q p V A := fun a => by
  refine ⟨(h a).1, fun ha => ?_⟩
  rw [Finset.filter_false_of_mem fun r _ => by simp [(h a).2 ha r]]
  simp

end DecidesWithOneSidedErrorExponent

/-- **Error reduction for `RP`** [Arora and Barak, Chapter 7][AroraBarak09]: a problem is in `RP`
exactly when, for every polynomial `q`, it is decided in polynomial time with one-sided error at
most `2 ^ (-q(n))`. -/
theorem mem_RP_iff_forall_decidesWithOneSidedErrorExponent {A : Set α} :
    A ∈ RP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithOneSidedErrorExponent enc q p V A := by
  have this : A ∈ RP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧ DecidesWithOneSidedErrorExponent
      enc q p V A := by
    refine ⟨fun ⟨p, V, hV, h⟩ q => ⟨q * p, _,
      (computableInPolyTime_repeatAny hV _ _).tidy, h.repeatAny q⟩, fun h => ?_⟩
    obtain ⟨p, V, hV, h⟩ := h 1
    exact ⟨p, V, .of_tidy hV, h.decidesWithOneSidedError fun _ => by simp⟩
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

/-- **`RP ⊆ BPP`** [Arora and Barak, Chapter 7][AroraBarak09]: two runs of a one-sided-error
decider reject a member with probability at most `1 / 4`. -/
theorem RP_subset_BPP : RP enc ⊆ BPP enc := fun _ hA => by
  obtain ⟨p, V, hV, h⟩ := mem_RP_iff_forall_decidesWithOneSidedErrorExponent.1 hA 2
  exact ⟨p, V, hV, h.decidesWithErrorExponent.decidesWithBoundedError fun _ => by simp⟩

/-- **`coRP ⊆ BPP`**: `BPP` is closed under complement. -/
theorem coRP_subset_BPP : coRP enc ⊆ BPP enc := fun A hA => by
  simpa using compl_mem_BPP (RP_subset_BPP hA)

end Cslib.Complexity
