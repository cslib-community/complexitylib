/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Complexity.Classes.ParityP
public import Complexity.Computability.Complexity.Classes.Toda.Isolation
import Complexity.Foundations.Data.BitString.WordCount
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# The polynomial hierarchy is in `BP·⊕P`

The first half of Toda's theorem [Toda][Toda1991], [Arora and Barak, Section 17.4][AroraBarak09]:
every problem in the polynomial hierarchy is decided with bounded error by the parity of a number
of witnesses of a polynomial-time verifier (`Cslib.Complexity.PH_subset_BPOp_ParityP`).

## Random parity representations

A predicate `P a u` of instances `a` and strings `u` of length `ℓ` (`ℓ`, like every length here, a
polynomial of the length of the encoded instance) is *represented with error `2 ^ (-e)`* by a
verifier `W`, random strings of length `ρ` and witnesses of length `ζ`
(`Cslib.Complexity.Toda.IsRandomParityRep`) when for every `a` and `u`, all but a `2 ^ (-e)`
fraction of the random strings `r` have an odd number of witnesses `z` with `W (a, u ++ r ++ z)`
exactly when `P a u`. Representations are built along the quantifier prefix of a verifier of the
hierarchy, from the innermost quantifier out:

* A polynomial-time predicate of `u` is represented without randomness by itself
  (`Cslib.Complexity.Toda.isRandomParityRep_base`).
* Negation adds one witness (`Cslib.Complexity.Toda.IsRandomParityRep.not`), as `⊕P` is closed
  under complement.
* An existential quantifier over strings `w` of length `m`, appended to `u`, is the randomized
  isolation step of `Complexity.Computability.Complexity.Classes.Toda.Isolation`
  (`Cslib.Complexity.Toda.IsRandomParityRep.exists`): from a representation of the inner predicate
  with error `2 ^ (-(e + m + 1))`, the same random string `r` serving every `w`, the verifier
  `Cslib.Complexity.Toda.existsVerifier` reads further seeds for `4 (e + 1) (m + 3)` trials and
  represents the quantified predicate with error `2 ^ (-e)`.

A universal quantifier is a negated existential one. Since the error of the inner representation
can be chosen after the outer one, every predicate given by alternating quantifiers is represented
with every polynomial error (`Cslib.Complexity.Toda.exists_isRandomParityRep_alternation`). Error
`1 / 4` gives `BP·⊕P`, after padding the witnesses to a polynomial of the length of the encoded
pair of instance and random string.

## Main definitions

* `Cslib.Complexity.Toda.IsRandomParityRep`: random parity representations.
* `Cslib.Complexity.Toda.notVerifier`, `Cslib.Complexity.Toda.existsVerifier`: the verifiers of
  negation and of the existential quantifier.

## Main results

* `Cslib.Complexity.Toda.IsRandomParityRep.not`, `Cslib.Complexity.Toda.IsRandomParityRep.exists`:
  the quantifier steps.
* `Cslib.Complexity.Toda.exists_isRandomParityRep_alternation`: representations of alternating
  quantifiers with every error.
* `Cslib.Complexity.PH_subset_BPOp_ParityP`: **`PH ⊆ BP·⊕P`**.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

namespace Toda

variable {α : Type} {enc : α ↪ List Bool}

/-! Tidy views of the plain certificates of `ParityP` and `Toda.Isolation`, for tidy `fun_prop`
below. -/

@[local fun_prop]
private theorem computableTidilyInPolyTime_hashesToZero
    {γ : Type} {input : γ ↪ List Bool} {k : γ → ℕ}
    {seed w : γ → List Bool}
    (hk : ComputableTidilyInPolyTime k input encUnary)
    (hseed : ComputableTidilyInPolyTime seed input encBits)
    (hw : ComputableTidilyInPolyTime w input encBits) :
    ComputableTidilyInPolyTime (fun x => hashesToZero (k x) (seed x) (w x)) input encBool :=
  (ComputableInPolyTime.tidy (computableInPolyTime_hashesToZero (.of_tidy hk) (.of_tidy hseed)
      (.of_tidy hw)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_succTest
    {γ : Type} {input : γ ↪ List Bool}
    {g : γ → List Bool → Bool} {w : γ → List Bool}
    (hg : ComputableTidilyInPolyTime (fun p : γ × List Bool => g p.1 p.2) (encPair input encBits)
      encBool)
    (hw : ComputableTidilyInPolyTime w input encBits) :
    ComputableTidilyInPolyTime (fun x => succTest (g x) (w x)) input encBool :=
  (ComputableInPolyTime.tidy (computableInPolyTime_succTest (.of_tidy hg) (.of_tidy hw)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_succVerifier
    {enc : α ↪ List Bool}
    {V : α × List Bool → Bool} (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool) :
    ComputableTidilyInPolyTime (succVerifier V) (encPair enc encBits) encBool :=
  (ComputableInPolyTime.tidy (computableInPolyTime_succVerifier (.of_tidy hV)))

/-! ### Random parity representations -/

open Classical in
/-- `W` **represents `P` with error `2 ^ (-e)`** at prefix length `ℓ`, with random strings of
length `ρ` and witnesses of length `ζ`, all polynomials of the length of the encoded instance:
for every instance `a` and string `u` of length `ℓ`, all but a `2 ^ (-e)` fraction of the random
strings `r` have an odd number of witnesses `z` with `W (a, u ++ r ++ z) = true` exactly when
`P a u`. -/
def IsRandomParityRep (enc : α ↪ List Bool) (ℓ e ρ ζ : Polynomial ℕ) (W : α × List Bool → Bool)
    (P : α → List Bool → Prop) : Prop :=
  ∀ (a : α) (u : List Bool), u.length = ℓ.eval (enc a).length →
    2 ^ e.eval (enc a).length * (univ.filter fun r : Fin (ρ.eval (enc a).length) → Bool =>
      ¬(Odd (acceptCount (fun x => W (x.1, u ++ List.ofFn r ++ x.2)) a (ζ.eval (enc a).length)) ↔
        P a u)).card ≤ 2 ^ ρ.eval (enc a).length

namespace IsRandomParityRep

variable {ℓ e ρ ζ : Polynomial ℕ} {W : α × List Bool → Bool} {P Q : α → List Bool → Prop}

/-- A representation of `P` represents every predicate agreeing with `P` on strings of length
`ℓ`. -/
theorem congr (h : IsRandomParityRep enc ℓ e ρ ζ W P)
    (hPQ : ∀ (a : α) (u : List Bool), u.length = ℓ.eval (enc a).length → (P a u ↔ Q a u)) :
    IsRandomParityRep enc ℓ e ρ ζ W Q := fun a u hu =>
  (Nat.mul_le_mul_left _ (card_le_card fun r hr => by
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    rwa [hPQ a u hu])).trans (h a u hu)

/-- A verifier right on every random string represents `P` with every error. -/
private theorem of_forall
    (h : ∀ (a : α) (u : List Bool), u.length = ℓ.eval (enc a).length →
      ∀ r : Fin (ρ.eval (enc a).length) → Bool,
        Odd (acceptCount (fun x => W (x.1, u ++ List.ofFn r ++ x.2)) a (ζ.eval (enc a).length)) ↔
          P a u) :
    IsRandomParityRep enc ℓ e ρ ζ W P := fun a u hu => by
  classical
  rw [Finset.filter_false_of_mem fun r _ => not_not.2 (h a u hu r), card_empty, mul_zero]
  exact Nat.zero_le _

end IsRandomParityRep

/-- **The base case**: a verifier of `u`, reading the first `ℓ` bits, represents itself without
randomness and with one witness, the empty one. -/
theorem isRandomParityRep_base (ℓ e : Polynomial ℕ) (V : α × List Bool → Bool) :
    IsRandomParityRep enc ℓ e 0 0 (fun x => V (x.1, x.2.take (ℓ.eval (enc x.1).length)))
      (fun a u => V (a, u) = true) := by
  refine IsRandomParityRep.of_forall fun a u hu => ?_
  simp only [Polynomial.eval_zero]
  intro r
  cases hV : V (a, u) <;> simp [acceptCount, ← hu, hV]

/-! ### Negation -/

/-- The verifier of the negation: `succVerifier` applied after the prefix and the random string,
accepting one more witness. -/
def notVerifier (enc : α ↪ List Bool) (ℓ ρ : Polynomial ℕ) (W : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  succVerifier (fun y => W (y.1, x.2.take (ℓ.eval (enc x.1).length + ρ.eval (enc x.1).length) ++
      y.2))
    (x.1, x.2.drop (ℓ.eval (enc x.1).length + ρ.eval (enc x.1).length))

private theorem computableTidilyInPolyTime_notVerifier (ℓ ρ : Polynomial ℕ)
    {W : α × List Bool → Bool}
    (hW : ComputableTidilyInPolyTime W (encPair enc encBits) encBool) :
    ComputableTidilyInPolyTime (notVerifier enc ℓ ρ W) (encPair enc encBits) encBool := by
  unfold notVerifier succVerifier
  fun_prop

/-- **Negation** adds one witness, with the same error. -/
theorem IsRandomParityRep.not {ℓ e ρ ζ : Polynomial ℕ} {W : α × List Bool → Bool}
    {P : α → List Bool → Prop} (h : IsRandomParityRep enc ℓ e ρ ζ W P) :
    IsRandomParityRep enc ℓ e ρ (ζ + 1) (notVerifier enc ℓ ρ W) (fun a u => ¬P a u) := by
  intro a u hu
  have hcount (r : Fin (ρ.eval (enc a).length) → Bool) :
      acceptCount (fun x => notVerifier enc ℓ ρ W (x.1, u ++ List.ofFn r ++ x.2)) a
        ((ζ + 1).eval (enc a).length) =
      acceptCount (fun x => W (x.1, u ++ List.ofFn r ++ x.2)) a (ζ.eval (enc a).length) + 1 := by
    rw [Polynomial.eval_add, Polynomial.eval_one, ← acceptCount_succVerifier]
    refine acceptCount_congr (fun w => ?_) _
    have hlen : (u ++ List.ofFn r).length =
        ℓ.eval (enc a).length + ρ.eval (enc a).length := by
      rw [List.length_append, List.length_ofFn, hu]
    simp only [notVerifier]
    rw [← hlen, List.take_left', List.drop_left']
    all_goals rfl
  refine le_of_eq_of_le ?_ (h a u hu)
  congr 2
  ext r
  simp only [mem_filter, mem_univ, true_and, hcount, Nat.odd_add_one]
  tauto

/-! ### The existential quantifier -/

/-- One trial on a block `w ++ z` of `M + ζ` bits: `w` passes the Valiant–Vazirani test of level
`level` with seed `seed`, and `W` accepts `u ++ w ++ r ++ z`. -/
def trialVerifier (W : α × List Bool → Bool) (a : α) (u r : List Bool) (M level : ℕ)
    (seed block : List Bool) : Bool :=
  hashesToZero level seed (block.take M) && W (a, u ++ block.take M ++ r ++ block.drop M)

/-- All trials: the `j`-th of the `T` rows of `M + Z + 1` bits of `y` is accepted by `succTest`
of the `j`-th trial, at level `j % (M + 3)`, with the `j`-th seed of `B` bits. -/
def trialsVerifier (W : α × List Bool → Bool) (a : α) (u r seeds : List Bool) (M Z T B : ℕ)
    (y : List Bool) : Bool :=
  (BitString.listRows T (M + Z + 1) y).zipIdx.all fun p =>
    succTest (trialVerifier W a u r M (p.2 % (M + 3)) (BitString.listRow B p.2 seeds)) p.1

/-- **The verifier of the existential quantifier** over strings of length `m`: after the prefix
`u` of length `ℓ` come the inner random string `r` of length `ρ` and the seeds of
`T = 4 (e + 1) (m + 3)` trials of `B = (m + 2) (m + 1)` bits each; the witnesses are accepted by
`succTest` of all trials. -/
def existsVerifier (enc : α ↪ List Bool) (ℓ m ρ ζ e : Polynomial ℕ) (W : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  succTest (trialsVerifier W x.1 (x.2.take (ℓ.eval (enc x.1).length))
      ((x.2.drop (ℓ.eval (enc x.1).length)).take (ρ.eval (enc x.1).length))
      ((x.2.drop (ℓ.eval (enc x.1).length + ρ.eval (enc x.1).length)).take
        (4 * (e.eval (enc x.1).length + 1) * (m.eval (enc x.1).length + 3) *
          ((m.eval (enc x.1).length + 2) * (m.eval (enc x.1).length + 1))))
      (m.eval (enc x.1).length)
      (ζ.eval (enc x.1).length) (4 * (e.eval (enc x.1).length + 1) * (m.eval (enc x.1).length + 3))
      ((m.eval (enc x.1).length + 2) * (m.eval (enc x.1).length + 1)))
    (x.2.drop (ℓ.eval (enc x.1).length + ρ.eval (enc x.1).length +
      4 * (e.eval (enc x.1).length + 1) * (m.eval (enc x.1).length + 3) *
        ((m.eval (enc x.1).length + 2) * (m.eval (enc x.1).length + 1))))

private theorem computableTidilyInPolyTime_trialVerifier {W : α × List Bool → Bool}
    (hW : ComputableTidilyInPolyTime W (encPair enc encBits) encBool)
    {γ : Type} {input : γ ↪ List Bool} {a : γ → α} {u r seed block : γ → List Bool}
    {M level : γ → ℕ}
    (ha : ComputableTidilyInPolyTime a input enc)
    (hu : ComputableTidilyInPolyTime u input encBits)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hM : ComputableTidilyInPolyTime M input encUnary)
    (hlevel : ComputableTidilyInPolyTime level input encUnary)
    (hseed : ComputableTidilyInPolyTime seed input encBits)
    (hblock : ComputableTidilyInPolyTime block input encBits) :
    ComputableTidilyInPolyTime (fun x => trialVerifier W (a x) (u x) (r x) (M x) (level x)
      (seed x) (block x)) input encBool := by
  unfold trialVerifier
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_trialVerifier

@[fun_prop]
theorem computableInPolyTime_trialVerifier {W : α × List Bool → Bool}
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool)
    {γ : Type} {input : γ ↪ List Bool} {a : γ → α} {u r seed block : γ → List Bool}
    {M level : γ → ℕ}
    (ha : ComputableInPolyTime a input enc)
    (hu : ComputableInPolyTime u input encBits)
    (hr : ComputableInPolyTime r input encBits)
    (hM : ComputableInPolyTime M input encUnary)
    (hlevel : ComputableInPolyTime level input encUnary)
    (hseed : ComputableInPolyTime seed input encBits)
    (hblock : ComputableInPolyTime block input encBits) :
    ComputableInPolyTime (fun x => trialVerifier W (a x) (u x) (r x) (M x) (level x)
      (seed x) (block x)) input encBool :=
  .of_tidy (computableTidilyInPolyTime_trialVerifier hW.tidy ha.tidy hu.tidy hr.tidy hM.tidy
    hlevel.tidy hseed.tidy hblock.tidy)

private theorem computableTidilyInPolyTime_trialsVerifier {W : α × List Bool → Bool}
    (hW : ComputableTidilyInPolyTime W (encPair enc encBits) encBool)
    {γ : Type} {input : γ ↪ List Bool} {a : γ → α} {u r seeds y : γ → List Bool}
    {M Z T B : γ → ℕ}
    (ha : ComputableTidilyInPolyTime a input enc)
    (hu : ComputableTidilyInPolyTime u input encBits)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hseeds : ComputableTidilyInPolyTime seeds input encBits)
    (hM : ComputableTidilyInPolyTime M input encUnary)
    (hZ : ComputableTidilyInPolyTime Z input encUnary)
    (hT : ComputableTidilyInPolyTime T input encUnary)
    (hB : ComputableTidilyInPolyTime B input encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits) :
    ComputableTidilyInPolyTime (fun x => trialsVerifier W (a x) (u x) (r x) (seeds x) (M x) (Z x)
      (T x) (B x) (y x)) input encBool := by
  unfold trialsVerifier
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_trialsVerifier

@[fun_prop]
theorem computableInPolyTime_trialsVerifier {W : α × List Bool → Bool}
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool)
    {γ : Type} {input : γ ↪ List Bool} {a : γ → α} {u r seeds y : γ → List Bool}
    {M Z T B : γ → ℕ}
    (ha : ComputableInPolyTime a input enc)
    (hu : ComputableInPolyTime u input encBits)
    (hr : ComputableInPolyTime r input encBits)
    (hseeds : ComputableInPolyTime seeds input encBits)
    (hM : ComputableInPolyTime M input encUnary)
    (hZ : ComputableInPolyTime Z input encUnary)
    (hT : ComputableInPolyTime T input encUnary)
    (hB : ComputableInPolyTime B input encUnary)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun x => trialsVerifier W (a x) (u x) (r x) (seeds x) (M x) (Z x)
      (T x) (B x) (y x)) input encBool :=
  .of_tidy (computableTidilyInPolyTime_trialsVerifier hW.tidy ha.tidy hu.tidy hr.tidy hseeds.tidy
    hM.tidy hZ.tidy hT.tidy hB.tidy hy.tidy)

private theorem computableTidilyInPolyTime_existsVerifier (ℓ m ρ ζ e : Polynomial ℕ)
    {W : α × List Bool → Bool} (hW : ComputableTidilyInPolyTime W (encPair enc encBits) encBool) :
    ComputableTidilyInPolyTime (existsVerifier enc ℓ m ρ ζ e W) (encPair enc encBits) encBool := by
  unfold existsVerifier
  fun_prop

/-- One trial accepts, with the strings `w` passing the test as prefixes, the witnesses of `W`
after `u ++ w ++ r`. -/
private theorem acceptCount_trialVerifier (W : α × List Bool → Bool) (a : α) (u r seed : List Bool)
    (M Z level : ℕ) :
    acceptCount (fun x => trialVerifier W a u r M level seed x.2) a (M + Z) =
      ∑ x : Fin M → Bool with hashesToZero level seed (List.ofFn x) = true,
        acceptCount (fun y => W (y.1, u ++ List.ofFn x ++ r ++ y.2)) a Z := by
  classical
  rw [acceptCount_add, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hlen : (List.ofFn x).length = M := List.length_ofFn
  have htrial (w : List Bool) : trialVerifier W a u r M level seed (List.ofFn x ++ w) =
      (hashesToZero level seed (List.ofFn x) && W (a, u ++ List.ofFn x ++ r ++ w)) := by
    rw [trialVerifier, List.take_left' hlen, List.drop_left' hlen]
  split
  · rename_i hx
    refine acceptCount_congr (fun w => ?_) _
    rw [htrial, hx, Bool.true_and]
  · rename_i hx
    simp [acceptCount, htrial, hx]

/-- All trials accept the product over the trials of one more than the count of one trial. -/
private theorem acceptCount_trialsVerifier (W : α × List Bool → Bool) (a : α) (u r : List Bool)
    (M Z T B : ℕ) (σ : Fin (T * B) → Bool) :
    acceptCount (fun x => trialsVerifier W a u r (List.ofFn σ) M Z T B x.2) a (T * (M + Z + 1)) =
      ∏ j : Fin T, (∑ x : Fin M → Bool with hashesToZero (j % (M + 3))
        (List.ofFn (BitString.blocksEquiv σ j)) (List.ofFn x) = true,
          acceptCount (fun y => W (y.1, u ++ List.ofFn x ++ r ++ y.2)) a Z + 1) := by
  change (univ.filter fun w : Fin (T * (M + Z + 1)) → Bool =>
    trialsVerifier W a u r (List.ofFn σ) M Z T B (List.ofFn w) = true).card = _
  unfold trialsVerifier
  rw [BitString.card_filter_listRows_all T (M + Z + 1) fun j b =>
    succTest (trialVerifier W a u r M (j % (M + 3)) (BitString.listRow B j (List.ofFn σ))) b]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hseed : BitString.listRow B j (List.ofFn σ) = List.ofFn (BitString.blocksEquiv σ j) := by
    rw [BitString.listRow_eq_ofFn (count := T) B j, BitString.ofList_ofFn]
    rfl
  rw [hseed, ← acceptCount_trialVerifier]
  exact acceptCount_succTest _ a (M + Z)

/-- The verifier of the existential quantifier on `u ++ (r ++ σ) ++ w` reads the prefix `u`, the
inner random string `r` and the seeds `σ`, and runs `succTest` of all trials on `w`. -/
private theorem existsVerifier_append (ℓ m ρ ζ e : Polynomial ℕ) (W : α × List Bool → Bool) (a : α)
    (u r σ w : List Bool) (hu : u.length = ℓ.eval (enc a).length)
    (hr : r.length = ρ.eval (enc a).length)
    (hσ : σ.length = 4 * (e.eval (enc a).length + 1) * (m.eval (enc a).length + 3) *
      ((m.eval (enc a).length + 2) * (m.eval (enc a).length + 1))) :
    existsVerifier enc ℓ m ρ ζ e W (a, u ++ (r ++ σ) ++ w) =
      succTest (trialsVerifier W a u r σ (m.eval (enc a).length) (ζ.eval (enc a).length)
        (4 * (e.eval (enc a).length + 1) * (m.eval (enc a).length + 3))
        ((m.eval (enc a).length + 2) * (m.eval (enc a).length + 1))) w := by
  have hx : u ++ (r ++ σ) ++ w = u ++ (r ++ (σ ++ w)) := by simp only [List.append_assoc]
  simp only [existsVerifier]
  rw [hx, ← hu, ← hr, ← hσ, List.take_left' rfl, List.drop_left' rfl, List.take_left' rfl,
    ← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl, List.take_left' rfl,
    ← List.drop_drop, ← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl,
    List.drop_left' rfl]

/-- **The existential quantifier.** From a representation of `P` at prefix length `ℓ + m` with
error `2 ^ (-(e + m + 1))`, `existsVerifier` represents `∃ w, |w| = m ∧ P a (u ++ w)` at prefix
length `ℓ` with error `2 ^ (-e)`, reading `4 (e + 1) (m + 3) (m + 2) (m + 1)` more random bits and
witnesses of `4 (e + 1) (m + 3) (m + ζ + 1) + 1` bits. -/
theorem IsRandomParityRep.exists {ℓ m ρ ζ e : Polynomial ℕ} {W : α × List Bool → Bool}
    {P : α → List Bool → Prop} (h : IsRandomParityRep enc (ℓ + m) (e + m + 1) ρ ζ W P) :
    IsRandomParityRep enc ℓ e (ρ + 4 * (e + 1) * (m + 3) * ((m + 2) * (m + 1)))
      (4 * (e + 1) * (m + 3) * (m + ζ + 1) + 1) (existsVerifier enc ℓ m ρ ζ e W)
      (fun a u => ∃ w, w.length = m.eval (enc a).length ∧ P a (u ++ w)) := by
  classical
  intro a u hu
  set n := (enc a).length with hn
  set M := m.eval n with hM
  set R := ρ.eval n with hR
  set Z := ζ.eval n with hZ
  set E := e.eval n with hE
  set T := 4 * (E + 1) * (M + 3) with hT
  set B := (M + 2) * (M + 1) with hB
  have hρ : (ρ + 4 * (e + 1) * (m + 3) * ((m + 2) * (m + 1))).eval n = R + T * B := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, hT, hB, hM, hE, hR]
  have hζ : (4 * (e + 1) * (m + 3) * (m + ζ + 1) + 1).eval n = T * (M + Z + 1) + 1 := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, hT, hM, hE, hZ]
  rw [hρ, hζ]
  -- the count of witnesses for the inner random string `r` and the seeds `σ`
  have hcount (r : Fin R → Bool) (σ : Fin (T * B) → Bool) :
      acceptCount (fun x => existsVerifier enc ℓ m ρ ζ e W
        (x.1, u ++ List.ofFn (Fin.append r σ) ++ x.2)) a (T * (M + Z + 1) + 1) =
      1 + ∏ j : Fin T, (1 + ∑ x : Fin M → Bool with hashesToZero (j % (M + 3))
        (List.ofFn (BitString.blocksEquiv σ j)) (List.ofFn x) = true,
          acceptCount (fun y => W (y.1, u ++ List.ofFn x ++ List.ofFn r ++ y.2)) a Z) := by
    rw [List.ofFn_fin_append]
    rw [acceptCount_congr (W := fun x => succTest (trialsVerifier W a u (List.ofFn r)
      (List.ofFn σ) M Z T B) x.2) (fun w => existsVerifier_append ℓ m ρ ζ e W a u _ _ w hu
        List.length_ofFn List.length_ofFn), acceptCount_succTest, acceptCount_trialsVerifier,
      Nat.add_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => Nat.add_comm _ _
  -- the set of strings `w` satisfying the inner predicate
  set S := univ.filter fun x : Fin M → Bool => P a (u ++ List.ofFn x) with hS
  have hQ : (∃ w : List Bool, w.length = M ∧ P a (u ++ w)) ↔ S.Nonempty := by
    constructor
    · rintro ⟨w, hw, hP⟩
      refine ⟨BitString.ofList M w, ?_⟩
      rw [hS, mem_filter, BitString.ofFn_ofList hw]
      exact ⟨mem_univ _, hP⟩
    · rintro ⟨x, hx⟩
      exact ⟨List.ofFn x, List.length_ofFn, (mem_filter.1 hx).2⟩
  have hbad := two_pow_mul_card_filter_not_odd_iff_le (B := B) (E := E) (e' := E + M + 1)
    (fun r x => acceptCount (fun y => W (y.1, u ++ List.ofFn x ++ List.ofFn r ++ y.2)) a Z) S
    (fun x => by
      have := h a (u ++ List.ofFn x) (by simp [hu, hn, hM])
      simp only [Polynomial.eval_add, Polynomial.eval_one] at this
      refine le_of_eq_of_le ?_ this
      congr 2
      ext r
      simp only [mem_filter, mem_univ, true_and, hS]
      exact Iff.rfl)
    le_rfl le_rfl
  rw [pow_add]
  refine le_of_eq_of_le ?_ hbad
  congr 1
  -- random strings of length `R + T B` are pairs of an inner random string and `T` seeds
  let eqv : (Fin R → Bool) × (Fin T → BitString B) ≃ (Fin (R + T * B) → Bool) :=
    (Equiv.prodCongr (Equiv.refl _) BitString.blocksEquiv.symm).trans (Fin.appendEquiv R (T * B))
  refine Finset.card_equiv eqv.symm fun r' => ?_
  obtain ⟨⟨r, s⟩, rfl⟩ := eqv.surjective r'
  simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply]
  have : eqv (r, s) = Fin.append r (BitString.blocksEquiv.symm s) := rfl
  rw [this, hcount, Equiv.apply_symm_apply, hQ]

/-! ### Alternating quantifiers -/

/-- **Alternating quantifiers are represented with every error.** For a polynomial-time verifier
`V` and certificate lengths `ps`, the alternating quantifiers over `ps` applied to `V (a, u ++ ·)`
have a polynomial-time random parity representation at every prefix length `ℓ` with every error
`2 ^ (-e)`. -/
theorem exists_isRandomParityRep_alternation {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (ps : List (Polynomial ℕ)) :
    ∀ (q : Bool) (ℓ e : Polynomial ℕ), ∃ (ρ ζ : Polynomial ℕ) (W : α × List Bool → Bool),
      ComputableInPolyTime W (encPair enc encBits) encBool ∧
      IsRandomParityRep enc ℓ e ρ ζ W fun a u =>
        Alternation q (ps.map fun p => p.eval (enc a).length) fun w => V (a, u ++ w) = true := by
  have hV := hV.tidy
  have this : ∀ (q : Bool) (ℓ e : Polynomial ℕ), ∃ (ρ ζ : Polynomial ℕ) (W : α × List Bool → Bool),
      ComputableTidilyInPolyTime W (encPair enc encBits) encBool ∧ IsRandomParityRep enc ℓ e ρ ζ W
      fun a u => Alternation q (ps.map fun p => p.eval (enc a).length) fun w => V (a, u ++ w) =
      true := by
    induction ps with
    | nil =>
      intro q ℓ e
      refine ⟨0, 0, _, by fun_prop, (isRandomParityRep_base ℓ e V).congr fun a u _ => ?_⟩
      simp
    | cons p ps ih =>
      intro q ℓ e
      cases q
      · -- `∀ w, P (u ++ w)` is `¬∃ w, ¬P (u ++ w)`
        obtain ⟨ρ, ζ, W, hW, h⟩ := ih true (ℓ + p) (e + p + 1)
        refine ⟨_, _, _, computableTidilyInPolyTime_notVerifier _ _
          (computableTidilyInPolyTime_existsVerifier ℓ p ρ (ζ + 1) e
            (computableTidilyInPolyTime_notVerifier _ _ hW)), (h.not.exists.not).congr
            fun a u _ => ?_⟩
        simp only [List.map_cons, alternation_false_cons, List.append_assoc, not_exists, not_and,
          not_not]
      · obtain ⟨ρ, ζ, W, hW, h⟩ := ih false (ℓ + p) (e + p + 1)
        refine ⟨_, _, _, computableTidilyInPolyTime_existsVerifier ℓ p ρ ζ e hW, h.exists.congr
          fun a u _ => ?_⟩
        simp only [List.map_cons, alternation_true_cons, List.append_assoc]
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

/-- Padding the witnesses of length `Z` to length `N ≥ Z` with `false`s keeps their number. -/
private theorem acceptCount_padWitness (W : α × List Bool → Bool) (a : α) (r : List Bool) {Z N : ℕ}
    (hZN : Z ≤ N) :
    acceptCount (fun x : (α × List Bool) × List Bool =>
        W (x.1.1, x.1.2 ++ x.2.take Z) && !(x.2.drop Z).any fun b => b) (a, r) N =
      acceptCount (fun x => W (x.1, r ++ x.2)) a Z := by
  classical
  obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le hZN
  rw [acceptCount_add]
  simp only [acceptCount, Finset.card_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hlen : (List.ofFn u).length = Z := List.length_ofFn
  simp only [List.take_left' hlen, List.drop_left' hlen, Bool.and_eq_true]
  split
  · rename_i hW
    have := BitString.card_filter_not_any D
    simp only [Finset.card_filter] at this
    simp only [hW, true_and]
    exact this
  · rename_i hW
    simp [hW]

end Toda

/-! ### The polynomial hierarchy -/

variable {α : Type} {enc : α ↪ List Bool}

open Classical Toda in
/-- **Toda's theorem, first half: `PH ⊆ BP·⊕P`.** Every problem in the polynomial hierarchy is
decided with bounded error, using random strings of polynomial length, by a problem in `⊕P` about
pairs of an instance and a random string. -/
theorem PH_subset_BPOp_ParityP : PH enc ⊆ BPOp enc (ParityP (encPair enc encBits)) := by
  intro L hL
  obtain ⟨k, ps, V, -, hV, hLV⟩ := mem_PH.1 hL
  obtain ⟨ρ, ζ, W, hW, h⟩ := exists_isRandomParityRep_alternation hV ps true 0 2
  set L' : Set (α × List Bool) :=
    {x | Odd (acceptCount (fun y => W (y.1, x.2 ++ y.2)) x.1 (ζ.eval (enc x.1).length))} with hL'
  refine ⟨ρ, L', ?_, fun a => ?_⟩
  · -- the inner problem is in `⊕P`, after padding the witnesses
    refine mem_ParityP.2 ⟨ζ, fun x => W (x.1.1, x.1.2 ++ x.2.take (ζ.eval (enc x.1.1).length)) &&
      !(x.2.drop (ζ.eval (enc x.1.1).length)).any fun b => b, by fun_prop, fun x => ?_⟩
    obtain ⟨a, r⟩ := x
    rw [acceptCount_congr (W := fun x : (α × List Bool) × List Bool =>
        W (x.1.1, x.1.2 ++ x.2.take (ζ.eval (enc a).length)) &&
          !(x.2.drop (ζ.eval (enc a).length)).any fun b => b) (fun w => rfl),
      acceptCount_padWitness W a r (Polynomial.eval_mono _ (length_le_encPair_left _ _ (a, r)))]
    rfl
  · -- error `1 / 4` is bounded error
    have ha := h a [] (by simp)
    simp only [Polynomial.eval_ofNat, List.nil_append] at ha
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin (ρ.eval (enc a).length) → Bool)))
      (fun r => Odd (acceptCount (fun x => W (x.1, List.ofFn r ++ x.2)) a (ζ.eval (enc a).length)))
    simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsplit
    simp only [hL', Set.mem_ofPred_eq, decide_eq_true_eq, decide_eq_false_iff_not]
    rw [← hLV a] at ha
    constructor
    · intro haL
      simp only [haL, iff_true] at ha
      omega
    · intro haL
      simp only [haL, iff_false, not_not] at ha
      omega

end Cslib.Complexity
