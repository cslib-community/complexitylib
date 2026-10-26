/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Crypto.Computational.OneWay
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# One-way functions separate P from NP

If one-way functions exist then `P ≠ NP` [Goldreich, Chapter 2][Goldreich2001],
[Katz and Lindell, Exercise 8.11][KatzLindell2020]. For a function `f` computable in polynomial
time, the *preimage-prefix problem* (`Cslib.Crypto.preimagePrefix`) asks, given `n` in unary, an
image `y` and a word `u`, whether some input `x` of length `n` that starts with `u` satisfies
`f x = y`. It is in `NP`, with the missing bits of `x` as certificate
(`Cslib.Crypto.preimagePrefix_mem_NP`).

A decision procedure for it finds preimages bit by bit (`Cslib.Crypto.preimageSearch`): starting
from the empty prefix, extend the prefix by `false` if a preimage of length `n` still starts with
the extension, and by `true` otherwise. After `n` steps the prefix is itself a preimage of `y`
whenever `y` has a preimage of length `n` (`Cslib.Crypto.apply_preimageSearch`), and the search
runs in polynomial time when the decision procedure does. So if the problem is in `P`, a
deterministic polynomial-time algorithm inverts `f` on every image
(`Cslib.Crypto.exists_inverse_of_preimagePrefix_mem_P`), which a one-way function forbids
(`Cslib.Crypto.OneWay.preimagePrefix_notMem_P`). By the Cook–Levin theorem, `SAT` is then not in
`P` either (`Cslib.Crypto.OneWay.SAT_notMem_P`).

One-wayness is the uniform notion of `Cslib.Crypto.OneWay`: the inverter is uniform strict PPT
and receives the unary length of the sampled input. The inverter built here is deterministic; the
randomized version, for a decision procedure in `BPP`, is in
`Complexity.Crypto.Computational.OneWay.BPP`.

## Main definitions

* `Cslib.Crypto.preimagePrefix`: the preimage-prefix problem of a function.
* `Cslib.Crypto.preimageSearch`: the bit-by-bit search for a preimage with a decision procedure.

## Main results

* `Cslib.Crypto.isVerifier_preimagePrefixVerifier`, `Cslib.Crypto.preimagePrefix_mem_NP`: the
  preimage-prefix problem of a polynomial-time function is in `NP`.
* `Cslib.Crypto.apply_preimageSearch`, `Cslib.Crypto.preimageSearch_congr`: with correct answers
  the search finds a preimage, and only the answers to its own `n` queries matter.
* `Cslib.Crypto.computableInPolyTime_preimageSearch`,
  `Cslib.Crypto.computableInPolyTime_preimageSearch_of_input`: the search is polynomial-time
  when the decision procedure is.
* `Cslib.Crypto.exists_inverse_of_preimagePrefix_mem_P`: if it is in `P`, a deterministic
  polynomial-time algorithm finds a preimage of every image.
* `Cslib.Crypto.not_oneWay_of_lengthInverse`: an efficient deterministic inverter that is told
  the input length refutes one-wayness (`Cslib.Crypto.not_oneWay_of_inverse` for inverters
  certified on the pair encoding).
* `Cslib.Crypto.OneWay.preimagePrefix_notMem_P`, `Cslib.Crypto.OneWay.P_ne_NP`,
  `Cslib.Crypto.OneWay.SAT_notMem_P`, `Cslib.Crypto.not_oneWay_of_SAT_mem_P`: one-way functions
  imply `P ≠ NP`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 1*][Goldreich2001]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- **The preimage-prefix problem** of `f`: the instances `(n, y, u)` such that some input `x` of
length `n` that starts with `u` satisfies `f x = y`. -/
def preimagePrefix (f : List Bool → List Bool) : Set (ℕ × List Bool × List Bool) :=
  {p | ∃ x : List Bool, x.length = p.1 ∧ p.2.2 <+: x ∧ f x = p.2.1}

/-- The encoding of instances of the preimage-prefix problem: the length `n` in unary, then the
image and the prefix. -/
abbrev encPreimagePrefix : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

variable {f : List Bool → List Bool}

/-! ### Membership in `NP` -/

/-- The verifier of the preimage-prefix problem: the certificate supplies the bits after the
prefix. -/
def preimagePrefixVerifier (f : List Bool → List Bool)
    (p : (ℕ × List Bool × List Bool) × List Bool) : Bool :=
  decide (p.1.2.2.length ≤ p.1.1) && f (p.1.2.2 ++ p.2.take (p.1.1 - p.1.2.2.length)) == p.1.2.1

/-- The unary length is at most as long as the encoded instance. -/
private theorem le_length_encPreimagePrefix (p : ℕ × List Bool × List Bool) :
    p.1 ≤ (encPreimagePrefix p).length := by
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
  omega

/-- The verifier accepts some certificate of the length of the encoded instance exactly for the
members. -/
theorem isVerifier_preimagePrefixVerifier (f : List Bool → List Bool) :
    IsVerifier encPreimagePrefix Polynomial.X (preimagePrefixVerifier f) (preimagePrefix f) := by
  refine IsVerifier.of_padding (fun ⟨n, y, u⟩ w hw h => ?_) fun ⟨n, y, u⟩ ⟨x, hx, hux, hfx⟩ => ?_
  · rw [Polynomial.eval_X] at hw
    have hn := le_length_encPreimagePrefix (n, y, u)
    simp only [preimagePrefixVerifier, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    refine ⟨u ++ w.take (n - u.length), ?_, List.prefix_append _ _, h.2⟩
    simp only [List.length_append, List.length_take] at hw ⊢
    omega
  · obtain ⟨v, rfl⟩ := hux
    have hn := le_length_encPreimagePrefix (n, y, u)
    simp only [List.length_append] at hx
    refine ⟨v, ?_, fun k => ?_⟩
    · rw [Polynomial.eval_X]
      omega
    · have hv : n - u.length = v.length := by omega
      simp only [preimagePrefixVerifier, hv, List.take_left, hfx, beq_self_eq_true,
        Bool.and_true, decide_eq_true_eq]
      omega

/-- The verifier is polynomial-time when `f` is. -/
@[fun_prop]
theorem computableInPolyTime_preimagePrefixVerifier
    (hf : ComputableInPolyTime f encBits encBits) :
    ComputableInPolyTime (preimagePrefixVerifier f) (encPair encPreimagePrefix encBits)
      encBool := by
  unfold preimagePrefixVerifier
  fun_prop

/-- **The preimage-prefix problem is in `NP`** for every function computable in polynomial
time. -/
theorem preimagePrefix_mem_NP (hf : ComputableInPolyTime f encBits encBits) :
    preimagePrefix f ∈ NP encPreimagePrefix := by
  have hf := hf.tidy
  exact ⟨_, _, (computableInPolyTime_preimagePrefixVerifier (.of_tidy hf)),
    isVerifier_preimagePrefixVerifier f⟩

/-! ### Search to decision -/

/-- One step of the search for a preimage of length `q.1` of `q.2`: extend the prefix `u` by
`false` when `D` says that a preimage starts with `u ++ [false]`, and by `true` otherwise. -/
def preimageSearchStep (D : ℕ × List Bool × List Bool → Bool) (q : ℕ × List Bool)
    (u : List Bool) : List Bool :=
  u ++ [!D (q.1, q.2, u ++ [false])]

/-- **The bit-by-bit search** for a preimage of length `q.1` of `q.2`, with the decision
procedure `D` for the preimage-prefix problem: `q.1` steps of `preimageSearchStep`. -/
def preimageSearch (D : ℕ × List Bool × List Bool → Bool) (q : ℕ × List Bool) : List Bool :=
  (preimageSearchStep D q)^[q.1] []

/-- The search extends the prefix by one bit at each step. -/
theorem length_iterate_preimageSearchStep (D : ℕ × List Bool × List Bool → Bool)
    (q : ℕ × List Bool) (i : ℕ) : ((preimageSearchStep D q)^[i] []).length = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', preimageSearchStep, List.length_append, ih]
    rfl

/-- A correct step keeps the prefix extendable to a preimage. -/
theorem preimageSearchStep_mem {D : ℕ × List Bool × List Bool → Bool}
    (hD : ∀ p, p ∈ preimagePrefix f ↔ D p = true) {n : ℕ} {y u : List Bool}
    (hu : (n, y, u) ∈ preimagePrefix f) (hlen : u.length < n) :
    (n, y, preimageSearchStep D (n, y) u) ∈ preimagePrefix f := by
  rw [preimageSearchStep]
  cases hb : D (n, y, u ++ [false])
  · obtain ⟨x, hx, ⟨v, rfl⟩, hfx⟩ := hu
    simp only [List.length_append] at hx
    obtain ⟨b, v, rfl⟩ : ∃ b v', v = b :: v' := List.exists_cons_of_length_pos (by omega)
    cases b
    · have hmem : (n, y, u ++ [false]) ∈ preimagePrefix f :=
        ⟨u ++ false :: v, by simpa using hx, ⟨v, by simp⟩, hfx⟩
      rw [hD, hb] at hmem
      exact absurd hmem Bool.false_ne_true
    · exact ⟨u ++ true :: v, by simpa using hx, ⟨v, by simp⟩, hfx⟩
  · exact (hD _).2 hb

/-- **Search to decision.** With a decision procedure for the preimage-prefix problem, the search
for a preimage of length `x.length` of `f x` finds a preimage of `f x`. -/
theorem apply_preimageSearch {D : ℕ × List Bool × List Bool → Bool}
    (hD : ∀ p, p ∈ preimagePrefix f ↔ D p = true) (x : List Bool) :
    f (preimageSearch D (x.length, f x)) = f x := by
  have hmem : ∀ i ≤ x.length,
      (x.length, f x, (preimageSearchStep D (x.length, f x))^[i] []) ∈ preimagePrefix f := by
    intro i hi
    induction i with
    | zero => exact ⟨x, rfl, List.nil_prefix, rfl⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact preimageSearchStep_mem hD (ih (by omega))
        (by rw [length_iterate_preimageSearchStep]; omega)
  obtain ⟨x', hx', hpre, hfx'⟩ := hmem x.length le_rfl
  have heq := hpre.eq_of_length (by rw [length_iterate_preimageSearchStep]; exact hx'.symm)
  dsimp only at heq hfx'
  change f ((preimageSearchStep D (x.length, f x))^[x.length] []) = f x
  rw [heq]
  exact hfx'

/-- The search with `D'` follows the search with `D` as long as `D'` answers the queries of the
search with `D` as `D` does. -/
theorem iterate_preimageSearchStep_congr {D D' : ℕ × List Bool × List Bool → Bool}
    {q : ℕ × List Bool} : ∀ i, (∀ j < i, D' (q.1, q.2, (preimageSearchStep D q)^[j] [] ++ [false]) =
      D (q.1, q.2, (preimageSearchStep D q)^[j] [] ++ [false])) →
    (preimageSearchStep D' q)^[i] [] = (preimageSearchStep D q)^[i] []
  | 0, _ => rfl
  | i + 1, h => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      iterate_preimageSearchStep_congr i fun j hj => h j (by omega)]
    simp only [preimageSearchStep, h i (by omega)]

/-- A decision procedure that answers the queries of the search with `D` as `D` does finds the
same word. Only these `q.1` queries matter, not correctness on all instances. -/
theorem preimageSearch_congr {D D' : ℕ × List Bool × List Bool → Bool} {q : ℕ × List Bool}
    (h : ∀ j < q.1, D' (q.1, q.2, (preimageSearchStep D q)^[j] [] ++ [false]) =
      D (q.1, q.2, (preimageSearchStep D q)^[j] [] ++ [false])) :
    preimageSearch D' q = preimageSearch D q :=
  iterate_preimageSearchStep_congr q.1 h

/-- **The search is polynomial-time** when the decision procedure is, also for a decision
procedure `D x` and a target `q x` that depend on the input `x`. -/
theorem computableInPolyTime_preimageSearch_of_input {γ : Type} {encIn : γ ↪ List Bool}
    {D : γ → ℕ × List Bool × List Bool → Bool} {q : γ → ℕ × List Bool}
    (hD : ComputableInPolyTime (fun p : γ × (ℕ × List Bool × List Bool) => D p.1 p.2)
      (encPair encIn encPreimagePrefix) encBool)
    (hq : ComputableInPolyTime q encIn (encPair encUnary encBits)) :
    ComputableInPolyTime (fun x => preimageSearch (D x) (q x)) encIn encBits := by
  have hD := hD.tidy
  have hq := hq.tidy
  refine .of_tidy ?_
  unfold preimageSearch
  refine iterateWithInput_of_bounded_growth hq.fst' (const []) ?_ ⟨.const 1, fun x u => ?_⟩
  · have hinst : ComputableTidilyInPolyTime (fun p : γ × List Bool =>
        (p.1, ((q p.1).1, (q p.1).2, p.2 ++ [false])))
        (encPair encIn encBits) (encPair encIn encPreimagePrefix) :=
      (fst _ _).prod ((hq.comp (fst _ _)).fst'.prod ((hq.comp (fst _ _)).snd'.prod
        (bitsAppend (snd _ _) (const [false]))))
    unfold preimageSearchStep
    exact bitsAppend (snd _ _) (bitsCons (bool_not.comp (hD.comp hinst)) (const []))
  · simp [preimageSearchStep]

/-- **The search is polynomial-time** when the decision procedure is. -/
@[fun_prop]
theorem computableInPolyTime_preimageSearch {D : ℕ × List Bool × List Bool → Bool}
    (hD : ComputableInPolyTime D encPreimagePrefix encBool) :
    ComputableInPolyTime (preimageSearch D) (encPair encUnary encBits) encBits :=
  computableInPolyTime_preimageSearch_of_input (D := fun _ => D) (hD.comp
    (ComputableInPolyTime.snd _ _)) ComputableInPolyTime.id'

/-- **Inversion from the preimage-prefix problem.** If the preimage-prefix problem of `f` is in
`P`, a deterministic polynomial-time algorithm, told the length of the input, finds a preimage of
every image. -/
theorem exists_inverse_of_preimagePrefix_mem_P (h : preimagePrefix f ∈ P encPreimagePrefix) :
    ∃ inverse : ℕ × List Bool → List Bool,
      ComputableInPolyTime inverse (encPair encUnary encBits) encBits ∧
        ∀ x, f (inverse (x.length, f x)) = f x := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  obtain ⟨D, hD, hDf⟩ := h
  exact ⟨preimageSearch D, (computableInPolyTime_preimageSearch hD).tidy,
    apply_preimageSearch hDf⟩

/-! ### One-way functions -/

/-- **Efficient inversion refutes one-wayness.** A deterministic polynomial-time algorithm that,
told the length of the input, finds a preimage of every image, inverts with probability one. This
is `Cslib.Crypto.not_oneWay_of_inverse` for an inverter certified on the pair encoding. -/
theorem not_oneWay_of_lengthInverse (inverse : ℕ × List Bool → List Bool)
    (hinverse : ComputableInPolyTime inverse (encPair encUnary encBits) encBits)
    (h : ∀ x, f (inverse (x.length, f x)) = f x) : ¬ OneWay f := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hinverse
  exact not_oneWay_of_inverse f (fun n y => inverse (n, y)) hinverse.isPPTOn.isPPT h

/-- **One-way functions have hard preimage-prefix problems**: the preimage-prefix problem of a
one-way function is not in `P`. -/
theorem OneWay.preimagePrefix_notMem_P (hf : OneWay f) :
    preimagePrefix f ∉ P encPreimagePrefix := fun h =>
  let ⟨inverse, hinverse, hinv⟩ := exists_inverse_of_preimagePrefix_mem_P h
  not_oneWay_of_lengthInverse inverse hinverse hinv hf

/-- **One-way functions imply `P ≠ NP`**, for instances of the preimage-prefix problem. -/
theorem OneWay.P_ne_NP (hf : OneWay f) : P encPreimagePrefix ≠ NP encPreimagePrefix := fun h =>
  hf.preimagePrefix_notMem_P (h ▸ preimagePrefix_mem_NP hf.polyTime)

/-- **One-way functions imply `SAT ∉ P`**: by the Cook–Levin theorem, the preimage-prefix problem
reduces to `SAT`. -/
theorem OneWay.SAT_notMem_P (hf : OneWay f) : SAT ∉ P encCNF := fun h =>
  hf.preimagePrefix_notMem_P
    ((CookLevin.SAT_npComplete.2 encPreimagePrefix _
      (preimagePrefix_mem_NP hf.polyTime)).mem_P h)

/-- If `SAT` is in `P`, no function is one-way. -/
theorem not_oneWay_of_SAT_mem_P (h : SAT ∈ P encCNF) : ¬ OneWay f := fun hf =>
  hf.SAT_notMem_P h

end Cslib.Crypto
