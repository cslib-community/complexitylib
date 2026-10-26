/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Classes.PP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Characterisations and closure properties of PP

`PP` (`Cslib.Complexity.PP`) is defined by a strict majority of accepted random strings
[Gill][Gill1977]. This file proves that a non-strict majority defines the same class, that `PP`
is closed under polynomial-time reductions, and the characterisations of `PP` through `#P` and
`GapP` [Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994].

* **Non-strict majority.** A verifier decides `A` by strict majority exactly when its negation
  decides the complement `Aᶜ` by non-strict majority
  (`Cslib.Complexity.decidesByMajority_iff_decidesByNonstrictMajority_compl`). Since `PP` is closed
  under complement (`Cslib.Complexity.compl_mem_PP`), the two majority conditions give the same
  class (`Cslib.Complexity.mem_PP_iff_decidesByNonstrictMajority`).
* **Reductions.** For a reduction `f` from `A` to `B` and a verifier `W` for `B` reading `q(m)`
  random bits on an instance of length `m`, the verifier for `A` runs `W` on `f a` and the first
  `q (|f a|)` random bits. Since `|f a|` is polynomial in `|a|`, the random string is padded to a
  polynomial `r(|a|)`; the ignored bits multiply the counts on both sides of the majority
  condition by the same power of two.
* **`#P`.** `A ∈ PP` exactly when `a ∈ A ↔ 2 ^ q(n) < 2 f(a)` for some `f ∈ #P` and some
  polynomial `q`, not necessarily the length of the certificates counted by `f`, where `n` is the
  length of the encoded instance
  (`Cslib.Complexity.mem_PP_iff_exists_SharpP`). For `f` counting the certificates of length
  `k = p(n)` that `V` accepts and `j = q(n)`, the verifier on random strings of length
  `k + j + 2` lets the first bit choose: on `true` it accepts the `2 f(a)` strings formed by a
  certificate accepted by `V`, a free bit, and `j` bits `false`; on `false` it accepts the
  `2 ^ (k + j + 1) - 2 ^ j` strings whose first `k + 1` bits are not all `false`. More than half
  of the strings are accepted exactly when `2 ^ j < 2 f(a)`.
* **`GapP`.** `A ∈ PP` exactly when `A = {a | 0 < g a}` for some `g ∈ GapP`
  (`Cslib.Complexity.mem_PP_iff_exists_GapP`).

## Main definitions

* `Cslib.Complexity.DecidesByNonstrictMajority`: the non-strict majority condition.

## Main results

* `Cslib.Complexity.mem_PP_iff_decidesByNonstrictMajority`: non-strict majority defines `PP`.
* `Cslib.Complexity.PolyTimeReducible.mem_PP`: `PP` is closed under polynomial-time reductions.
* `Cslib.Complexity.mem_PP_iff_exists_SharpP`, `Cslib.Complexity.mem_PP_iff_exists_GapP`.

## References

* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-! ### Non-strict majority -/

/-- `V` decides `A` by non-strict majority, using random strings whose length is `p` evaluated at
the length of the encoded instance: `a ∈ A` exactly when at least half of the random strings `r`
give `V (a, r) = true`. -/
def DecidesByNonstrictMajority (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ 2 ^ p.eval (enc a).length ≤ 2 * acceptCount V a (p.eval (enc a).length)

/-- A verifier decides `A` by strict majority exactly when its negation decides `Aᶜ` by
non-strict majority. -/
theorem decidesByMajority_iff_decidesByNonstrictMajority_compl {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} :
    DecidesByMajority enc p V A ↔ DecidesByNonstrictMajority enc p (fun x => !V x) Aᶜ := by
  refine forall_congr' fun a => ?_
  have h := acceptCount_add_acceptCount_not V a (p.eval (enc a).length)
  have key : 2 ^ p.eval (enc a).length ≤
        2 * acceptCount (fun x => !V x) a (p.eval (enc a).length) ↔
      ¬2 ^ p.eval (enc a).length < 2 * acceptCount V a (p.eval (enc a).length) := by
    omega
  rw [Set.mem_compl_iff, key, not_iff_not]

/-- **Non-strict majority defines `PP`**: a problem is in `PP` exactly when a polynomial-time
verifier accepts the members of the problem, and only them, on at least half of the random
strings. -/
theorem mem_PP_iff_decidesByNonstrictMajority {A : Set α} :
    A ∈ PP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesByNonstrictMajority enc p V A := by
  have this : A ∈ PP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧ DecidesByNonstrictMajority enc p
      V A := by
    constructor
    · intro hA
      obtain ⟨p, V, hV, h⟩ := mem_PP.mp (compl_mem_PP hA)
      refine ⟨p, fun x => !V x, ComputableTidilyInPolyTime.bool_not.comp hV.tidy, ?_⟩
      simpa using decidesByMajority_iff_decidesByNonstrictMajority_compl.1 h
    · rintro ⟨p, V, hV, h⟩
      have h' : DecidesByMajority enc p (fun x => !V x) Aᶜ := by
        rw [decidesByMajority_iff_decidesByNonstrictMajority_compl]
        simpa using h
      simpa using compl_mem_PP ⟨p, _, .of_tidy (ComputableTidilyInPolyTime.bool_not.comp hV), h'⟩
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

/-! ### Reductions -/

/-- **`PP` is closed under polynomial-time reductions.** The verifier runs the verifier for the
target problem on the reduced instance; the random string is padded to a polynomial in the length
of the encoded instance, and the ignored bits multiply both sides of the majority condition by
the same power of two. -/
theorem PolyTimeReducible.mem_PP {β : Type} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ PP encB) : A ∈ PP enc := by
  rw [Complexity.mem_PP] at hB ⊢
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨q, W, hW, hWB⟩ := hB
  have hf := hf.tidy
  have hW := hW.tidy
  have hlen : ComputableTidilyInPolyTime (fun a => q.eval (encB (f a)).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval q).comp
      ((ComputableTidilyInPolyTime.encoding_length encB).comp hf)
  obtain ⟨p, hle⟩ := hlen.polyBounded.exists_polynomial
  refine ⟨p,
    andVerifier (fun a => q.eval (encB (f a)).length) (fun x => W (f x.1, x.2)) fun _ => true,
    .of_tidy (computableTidilyInPolyTime_andVerifier hlen
      (hW.comp ((hf.comp (.fst enc encBits)).prod (.snd enc encBits))) (.const true)),
    fun a => ?_⟩
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (hle a)
  rw [hAB a, hWB (f a), hj, acceptCount_andVerifier_true, pow_add, ← mul_assoc]
  exact (Nat.mul_lt_mul_right (by positivity)).symm


/-! ### `PP` through `#P` and `GapP` -/

/-- **`PP` through `#P`**: a problem is in `PP` exactly when, for a function `f` in `#P` and a
polynomial `q`, its members are the instances `a` with `2 ^ q(n) < 2 f(a)`, where `n` is the
length of the encoded instance. The polynomial `q` need not be the length of the certificates
counted by `f`. -/
theorem mem_PP_iff_exists_SharpP {A : Set α} :
    A ∈ PP enc ↔ ∃ f ∈ SharpP enc, ∃ q : Polynomial ℕ,
      ∀ a, a ∈ A ↔ 2 ^ q.eval (enc a).length < 2 * f a := by
  constructor
  · rintro ⟨p, V, hV, h⟩
    exact ⟨_, ⟨p, V, hV, fun _ => rfl⟩, p, h⟩
  · rintro ⟨f, ⟨p, V, hV, hf⟩, q, h⟩
    replace hV := hV.tidy
    -- on `false`, accept unless the first `k + 1` bits are `false`; on `true`, accept a
    -- certificate of `V` followed by a free bit and bits `false`
    refine ⟨p + q + 1 + 1, selectVerifier
        (fun x => !andVerifier (fun a => p.eval (enc a).length + 1) allFalseVerifier
          (fun _ => true) x)
        (andVerifier (fun a => p.eval (enc a).length) V
          (selectVerifier allFalseVerifier allFalseVerifier)), by fun_prop, fun a => ?_⟩
    have hev : (p + q + 1 + 1).eval (enc a).length =
        p.eval (enc a).length + q.eval (enc a).length + 1 + 1 := by simp
    have e₀ := acceptCount_andVerifier_true (fun a => p.eval (enc a).length + 1) allFalseVerifier
      a (q.eval (enc a).length)
    have e₁ := acceptCount_andVerifier (fun a => p.eval (enc a).length) V
      (selectVerifier allFalseVerifier allFalseVerifier) a (q.eval (enc a).length + 1)
    rw [acceptCount_allFalseVerifier, one_mul] at e₀
    rw [acceptCount_selectVerifier, acceptCount_allFalseVerifier, ← hf a] at e₁
    rw [h a, hev, acceptCount_selectVerifier, acceptCount_not,
      show p.eval (enc a).length + q.eval (enc a).length + 1 =
        p.eval (enc a).length + 1 + q.eval (enc a).length by omega, e₀,
      show p.eval (enc a).length + 1 + q.eval (enc a).length =
        p.eval (enc a).length + (q.eval (enc a).length + 1) by omega, e₁]
    have hj : 2 ^ q.eval (enc a).length ≤
        2 ^ (p.eval (enc a).length + (q.eval (enc a).length + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ _ (p.eval (enc a).length + (q.eval (enc a).length + 1))]
    omega

/-- **`PP` through `GapP`** [Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]: a problem is in
`PP` exactly when its members are the instances where some function in `GapP` is positive. -/
theorem mem_PP_iff_exists_GapP {A : Set α} :
    A ∈ PP enc ↔ ∃ g ∈ GapP enc, ∀ a, a ∈ A ↔ 0 < g a := by
  constructor
  · rintro ⟨p, V, hV, h⟩
    have hf : (fun a => acceptCount V a (p.eval (enc a).length)) ∈ SharpP enc :=
      ⟨p, V, hV, fun _ => rfl⟩
    refine ⟨fun a => ((acceptCount V a (p.eval (enc a).length) +
        acceptCount V a (p.eval (enc a).length) : ℕ) : ℤ) - ((2 ^ p.eval (enc a).length : ℕ) : ℤ),
      ⟨_, SharpP.add_mem hf hf, _, SharpP.two_pow_mem p, fun a => rfl⟩, fun a => ?_⟩
    rw [h a, sub_pos, Nat.cast_lt]
    omega
  · rintro ⟨g, ⟨f₁, hf₁, f₂, hf₂, hg⟩, h⟩
    obtain ⟨p, hle, hsub⟩ := SharpP.exists_two_pow_sub_mem hf₂
    refine mem_PP_iff_exists_SharpP.2 ⟨_, SharpP.add_mem hf₁ hsub, p + 1, fun a => ?_⟩
    have := hle a
    rw [h a, hg a, Polynomial.eval_add, Polynomial.eval_one, pow_succ, Pi.add_apply]
    omega

end Cslib.Complexity
