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
# The classes RP and coRP, and their promise versions

`RP` is defined like `BPP` (`Cslib.Complexity.BPP`), through deterministic polynomial-time
machines that read a random string, but with one-sided error
[Arora and Barak, Section 7.3][AroraBarak09]: `A ∈ RP enc` when there are a polynomial `p` and
a function `V : α × List Bool → Bool`, computable in polynomial time on inputs
`frame (enc a) ++ r`, such that for every member `a` of `A` at least half of the random strings
`r` of length `p (enc a).length` are accepted, and for every non-member none is. `coRP` contains
the complements of problems in `RP`.

As for `BPP`, the one-sided error condition is stated once, for promise problems
(`Cslib.Complexity.PromiseProblem.SolvesWithOneSidedError`) [Goldreich, Section 6.2][Goldreich2006],
and `A ∈ RP enc` is, by definition, `ofSet A ∈ PromiseRP enc`
(`Cslib.Complexity.ofSet_mem_PromiseRP`). Since an accepted random string is a certificate,
`PromiseRP ⊆ PromiseNP` and `RP ⊆ NP`. `ZPP`, with `ZPP = RP ∩ coRP`, is defined in
`Cslib.Complexity.ZPP`.

The error `1 / 2` can be made exponentially small [Arora and Barak, Chapter 7][AroraBarak09]: for
a polynomial `q`, run the solver on `q(n)` independent blocks of random bits, where `n` is the
length of the encoded instance, and accept when some run accepts (`Cslib.Complexity.repeatAny`).
A yes-instance is then rejected on at most a `2 ^ (-q(n))` fraction of the random strings
(`Cslib.Complexity.PromiseProblem.SolvesWithOneSidedErrorExponent`), and a no-instance is still
never accepted. Two runs reject a yes-instance with probability at most `1 / 4`, so
`PromiseRP ⊆ PromiseBPP`, and `RP ⊆ BPP`.

## Main definitions

* `Cslib.Complexity.PromiseProblem.SolvesWithOneSidedError`: the one-sided error condition, and
  its specialization `Cslib.Complexity.DecidesWithOneSidedError` to decision problems.
* `Cslib.Complexity.PromiseRP`, `Cslib.Complexity.PromiseCoRP`, `Cslib.Complexity.RP`,
  `Cslib.Complexity.coRP`.
* `Cslib.Complexity.PromiseProblem.SolvesWithOneSidedErrorExponent`: one-sided error at most
  `2 ^ (-q(n))`, and its specialization `Cslib.Complexity.DecidesWithOneSidedErrorExponent`.

## Main results

* `Cslib.Complexity.mem_PromiseRP_iff`: unfolding `PromiseRP` to a polynomial-time verifier.
* `Cslib.Complexity.ofSet_mem_PromiseRP`, `Cslib.Complexity.ofSet_mem_PromiseCoRP`.
* `Cslib.Complexity.PromiseProblem.SolvesWithOneSidedError.exists_certificate`,
  `Cslib.Complexity.DecidesWithOneSidedError.isVerifier`, `Cslib.Complexity.RP_subset_NP`,
  `Cslib.Complexity.PromiseRP_subset_PromiseNP`, `Cslib.Complexity.coRP_subset_coNP`.
* `Cslib.Complexity.PromiseProblem.SolvesWithOneSidedError.repeatAny`: repetition reduces the
  error to `2 ^ (-q(n))`.
* `Cslib.Complexity.mem_PromiseRP_iff_forall_solvesWithOneSidedErrorExponent`,
  `Cslib.Complexity.mem_RP_iff_forall_decidesWithOneSidedErrorExponent`: error reduction for
  `PromiseRP` and `RP`.
* `Cslib.Complexity.PromiseRP_subset_PromiseBPP`, `Cslib.Complexity.PromiseCoRP_subset_PromiseBPP`,
  `Cslib.Complexity.RP_subset_BPP`, `Cslib.Complexity.coRP_subset_BPP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

namespace PromiseProblem

/-- `V` solves the promise problem `Q` with one-sided error, using random strings whose length is
`p` evaluated at the length of the encoded instance: for every yes-instance at least half of the
random strings are accepted, and for every no-instance none is
[Goldreich, Section 6.2][Goldreich2006]. Nothing is required on
instances outside the promise. -/
def SolvesWithOneSidedError (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (Q : PromiseProblem α) : Prop :=
  ∀ a, (a ∈ Q.yes → 2 ^ p.eval (enc a).length ≤
      2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).card) ∧
    (a ∈ Q.no → ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = false)

/-- A one-sided-error solver for a promise problem is a polynomial-time verifier on the promise: a
random string accepted on a yes-instance is a certificate, and no certificate of the right length
is accepted on a no-instance. -/
theorem SolvesWithOneSidedError.exists_certificate {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {Q : PromiseProblem α} (h : Q.SolvesWithOneSidedError enc p V) :
    (∀ a ∈ Q.yes, ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true) ∧
      ∀ a ∈ Q.no, ∀ w : List Bool, w.length = p.eval (enc a).length → V (a, w) = false := by
  refine ⟨fun a ha => ?_, fun a ha w hw => ?_⟩
  · have hpos := Nat.one_le_two_pow (n := p.eval (enc a).length)
    obtain ⟨r, hr⟩ : (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).Nonempty := by
      rw [← Finset.card_pos]
      have := (h a).1 ha
      omega
    exact ⟨List.ofFn r, List.length_ofFn, (Finset.mem_filter.1 hr).2⟩
  · have hno := (h a).2 ha fun i => w[i.val]'(by omega)
    rwa [show (List.ofFn fun i : Fin (p.eval (enc a).length) => w[i.val]'(by omega)) = w from
      List.ext_getElem (by simp [hw]) fun i _ _ => by simp] at hno

end PromiseProblem

open PromiseProblem

/-- `V` decides `A` with one-sided error, using random strings whose length is `p` evaluated at the
length of the encoded instance: it solves the promise problem `ofSet A` with one-sided error. For
every member `a` of `A` at least half of the random strings are accepted, and for every non-member
none is. -/
def DecidesWithOneSidedError (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  (ofSet A).SolvesWithOneSidedError enc p V

/-- The promise problems solved with one-sided error (no false positives on no-instances) by
polynomial-time algorithms reading polynomially long random strings
[Goldreich, Section 6.2][Goldreich2006]. -/
def PromiseRP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ Q.SolvesWithOneSidedError enc p V}

/-- The promise problems solved with one-sided error (no false negatives on yes-instances) by
polynomial-time algorithms reading polynomially long random strings: those whose complements are
in `PromiseRP` [Goldreich, Section 6.2][Goldreich2006]. -/
def PromiseCoRP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | Qᶜ ∈ PromiseRP enc}

/-- The problems decided with one-sided error by polynomial-time machines reading polynomially
long random strings, with respect to the encoding `enc` of instances
[Arora and Barak, Section 7.3][AroraBarak09]. -/
def RP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      DecidesWithOneSidedError enc p V A}

/-- The problems whose complements are in `RP` [Arora and Barak, Section 7.3][AroraBarak09]. -/
def coRP (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ RP enc}

variable {enc : α ↪ List Bool} {Q : PromiseProblem α} {A : Set α}

/-- Membership in `PromiseRP` unfolded to a polynomial coin bound and a polynomial-time
one-sided-error solver. -/
theorem mem_PromiseRP_iff : Q ∈ PromiseRP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧ Q.SolvesWithOneSidedError enc p V :=
  Iff.rfl

theorem mem_RP : A ∈ RP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      DecidesWithOneSidedError enc p V A :=
  Iff.rfl

theorem mem_coRP : A ∈ coRP enc ↔ Aᶜ ∈ RP enc := Iff.rfl

/-- A decision problem, as a promise problem, is in `PromiseRP` exactly when it is in `RP`; this
holds by definition. -/
@[simp]
theorem ofSet_mem_PromiseRP : ofSet A ∈ PromiseRP enc ↔ A ∈ RP enc :=
  Iff.rfl

/-- A decision problem, as a promise problem, is in `PromiseCoRP` exactly when it is in `coRP`. -/
@[simp]
theorem ofSet_mem_PromiseCoRP : ofSet A ∈ PromiseCoRP enc ↔ A ∈ coRP enc := by
  rw [PromiseCoRP, Set.mem_ofPred_eq, ← ofSet_compl, ofSet_mem_PromiseRP, mem_coRP]

/-- A random string accepted by a one-sided-error decider is a certificate: one-sided error gives
a verifier. -/
theorem DecidesWithOneSidedError.isVerifier {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : DecidesWithOneSidedError enc p V A) : IsVerifier enc p V A := fun a =>
  ⟨h.exists_certificate.1 a, fun ⟨w, hw, hV⟩ => by_contra fun ha => by
    simp [h.exists_certificate.2 a ha w hw] at hV⟩

/-- `PromiseRP ⊆ PromiseNP`: a random string accepted by a one-sided-error solver is a
certificate. -/
theorem PromiseRP_subset_PromiseNP : PromiseRP enc ⊆ PromiseNP enc := fun _ ⟨p, V, hV, h⟩ =>
  mem_PromiseNP_iff.2 ⟨p, V, hV, h.exists_certificate⟩

/-- `RP ⊆ NP`: a random string accepted by a one-sided-error decider is a certificate. -/
theorem RP_subset_NP : RP enc ⊆ NP enc := fun _ hA =>
  ofSet_mem_PromiseNP.1 (PromiseRP_subset_PromiseNP (ofSet_mem_PromiseRP.2 hA))

/-- `coRP ⊆ coNP`. -/
theorem coRP_subset_coNP : coRP enc ⊆ coNP enc := fun _ hA => RP_subset_NP hA

/-! ### Error reduction -/

namespace PromiseProblem

/-- `V` solves the promise problem `Q` with one-sided error at most `2 ^ (-q(n))`, using random
strings whose length is `p` evaluated at the length `n` of the encoded instance: for every
yes-instance the rejected random strings make up at most a `2 ^ (-q(n))` fraction, and for every
no-instance none is accepted. Nothing is required on instances outside the promise. -/
def SolvesWithOneSidedErrorExponent (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (Q : PromiseProblem α) : Prop :=
  ∀ a, (a ∈ Q.yes → 2 ^ q.eval (enc a).length *
      (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = false).card ≤ 2 ^ p.eval (enc a).length) ∧
    (a ∈ Q.no → ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = false)

/-- **Error reduction for one-sided error**: the repetition argument of
[Arora and Barak, Chapter 7][AroraBarak09], which the book states for languages, applied to promise
problems. The disjunction of `q(n)` runs of a one-sided-error solver, on independent blocks of
random bits, rejects a yes-instance on at most a `2 ^ (-q(n))` fraction of the random strings, and
never accepts a no-instance. -/
theorem SolvesWithOneSidedError.repeatAny {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : Q.SolvesWithOneSidedError enc p V) (q : Polynomial ℕ) :
    Q.SolvesWithOneSidedErrorExponent enc q (q * p) (Complexity.repeatAny enc q p V) := by
  intro a
  -- on a yes-instance, a run rejects on at most half of its random strings
  have hR (ha : a ∈ Q.yes) : 2 * (Finset.univ.filter fun u : Fin (p.eval (enc a).length) → Bool =>
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
  · -- on a no-instance, no run accepts
    intro ha x
    rw [← Bool.not_eq_true, repeatAny_ofFn_eq_true_iff]
    simpa using fun i => (h a).2 ha (BitString.block x i)

namespace SolvesWithOneSidedErrorExponent

variable {q p : Polynomial ℕ} {V : α × List Bool → Bool}

/-- One-sided error at most `2 ^ (-q(n)) ≤ 1 / 2` is one-sided error. -/
theorem solvesWithOneSidedError (h : Q.SolvesWithOneSidedErrorExponent enc q p V)
    (hq : ∀ n, 1 ≤ q.eval n) : Q.SolvesWithOneSidedError enc p V := fun a => by
  refine ⟨fun ha => ?_, (h a).2⟩
  have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
  have h2 : 2 ^ 1 ≤ 2 ^ q.eval (enc a).length := Nat.pow_le_pow_right (by norm_num) (hq _)
  have := (Nat.mul_le_mul_right _ h2).trans ((h a).1 ha)
  rw [← acceptCount]
  omega

/-- One-sided error at most `2 ^ (-q(n))` is error at most `2 ^ (-q(n))`. -/
theorem solvesWithErrorExponent (h : Q.SolvesWithOneSidedErrorExponent enc q p V) :
    Q.SolvesWithErrorExponent enc q p V := fun a => by
  refine ⟨(h a).1, fun ha => ?_⟩
  simp only [ErrorExponentAt, Bool.not_false]
  rw [Finset.filter_false_of_mem fun r _ => by simp [(h a).2 ha r]]
  simp

end SolvesWithOneSidedErrorExponent

end PromiseProblem

/-- `V` decides `A` with one-sided error at most `2 ^ (-q(n))`, using random strings whose length is
`p` evaluated at the length `n` of the encoded instance: it solves `ofSet A` with that error. For
every member `a` of `A` the rejected random strings make up at most a `2 ^ (-q(n))` fraction, and
for every non-member none is accepted. -/
def DecidesWithOneSidedErrorExponent (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  (ofSet A).SolvesWithOneSidedErrorExponent enc q p V

/-- **Error reduction for `PromiseRP`**, the promise-problem form of the `RP` error reduction of
[Arora and Barak, Chapter 7][AroraBarak09]: a promise problem is in `PromiseRP` exactly when, for
every polynomial `q`, it is solved in polynomial time with one-sided error at most `2 ^ (-q(n))`. -/
theorem mem_PromiseRP_iff_forall_solvesWithOneSidedErrorExponent :
    Q ∈ PromiseRP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        Q.SolvesWithOneSidedErrorExponent enc q p V :=
  ⟨fun ⟨p, V, hV, h⟩ q => ⟨q * p, _, computableInPolyTime_repeatAny hV _ _, h.repeatAny q⟩,
    fun h => let ⟨p, V, hV, h⟩ := h 1
      ⟨p, V, hV, h.solvesWithOneSidedError fun _ => by simp⟩⟩

/-- **Error reduction for `RP`** [Arora and Barak, Chapter 7][AroraBarak09]: a problem is in `RP`
exactly when, for every polynomial `q`, it is decided in polynomial time with one-sided error at
most `2 ^ (-q(n))`. -/
theorem mem_RP_iff_forall_decidesWithOneSidedErrorExponent :
    A ∈ RP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithOneSidedErrorExponent enc q p V A :=
  mem_PromiseRP_iff_forall_solvesWithOneSidedErrorExponent (Q := ofSet A)

/-- **`PromiseRP ⊆ PromiseBPP`**, the promise-problem form of `RP ⊆ BPP`
[Arora and Barak, Chapter 7][AroraBarak09]: two runs of a one-sided-error solver reject a
yes-instance with probability at most `1 / 4`. -/
theorem PromiseRP_subset_PromiseBPP : PromiseRP enc ⊆ PromiseBPP enc := fun _ hQ => by
  obtain ⟨p, V, hV, h⟩ := mem_PromiseRP_iff_forall_solvesWithOneSidedErrorExponent.1 hQ 2
  exact ⟨p, V, hV, h.solvesWithErrorExponent.solvesWithBoundedError fun _ => by simp⟩

/-- **`PromiseCoRP ⊆ PromiseBPP`**: `PromiseBPP` is closed under complement. -/
theorem PromiseCoRP_subset_PromiseBPP : PromiseCoRP enc ⊆ PromiseBPP enc := fun Q hQ => by
  simpa using compl_mem_PromiseBPP (PromiseRP_subset_PromiseBPP hQ)

/-- **`RP ⊆ BPP`** [Arora and Barak, Chapter 7][AroraBarak09]: two runs of a one-sided-error
decider reject a member with probability at most `1 / 4`. -/
theorem RP_subset_BPP : RP enc ⊆ BPP enc := fun _ hA =>
  ofSet_mem_PromiseBPP.1 (PromiseRP_subset_PromiseBPP (ofSet_mem_PromiseRP.2 hA))

/-- **`coRP ⊆ BPP`**: `BPP` is closed under complement. -/
theorem coRP_subset_BPP : coRP enc ⊆ BPP enc := fun A hA => by
  simpa using compl_mem_BPP (RP_subset_BPP hA)

end Cslib.Complexity
