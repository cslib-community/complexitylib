/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: candidate
public import CslibFrontier.Crypto.Primitives.BlockCipher.Modes
public import CslibFrontier.Foundations.Data.BitString.PadBlocks
public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Control.Monad.Writer
import CslibFrontier.Foundations.Data.Fintype.AgreeOn
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Finset.Density
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# CBC-MAC Finite Security Bounds and Forgery Separations

Formalizes the Cipher Block Chaining Message Authentication Code (CBC-MAC) over `BitString n`, its
prefix-free smoothness and information-theoretic adaptive decision-tree PRF bound
([KatzLindell2020], Section 4.4, Construction 4.9, Theorem 4.12, and Claim 4.13), and explicit
forgery counterexamples for each of the six relaxations in [KatzLindell2020], Exercises
4.13–4.16.

## Main definitions

* `cbcMacBlocks`, `CBCInput`, `cbcInputBlocks`, `cbcMacFinite`: basic CBC-MAC block folding and
  bounded nonempty block-vector domain.
* `CBCPrefixFree`, `CBCSmooth`: prefix-free query-list predicate and `(q, ℓ, δ)`-smoothness for
  random-function CBC-MAC.
* `CBCOracleSpec`, `cbcQueryRun`, `CBCAdmissible`, `cbcRealSuccess`, `cbcIdealSuccess`: adaptive
  oracle distinguishers as `OracleComp (CBCOracleSpec n ℓ) Bool` programs, their query-logging run
  through `OracleComp.interpret`, the execution-based prefix-free query budget, and real/ideal
  acceptance probabilities for the information-theoretic step of Theorem 4.12.
* `CBCTagForgery`, `cbcForgeryValid`, `cbcTwoToFourAttack`, `cbcToThreeAttack`, `cbcAllTagsTwo`,
  `cbcLeakedTagsAttack`, `cbcRandomIVMac`, `cbcRandomIVAttack`, `lengthAppendedCBC`,
  `cbcLengthSuffixAttack`, `zeroPadCBC`, `zeroPadAttack`: explicit CBC-MAC forgery constructions
  for Exercises 4.13–4.16 (the all-ones block is `(1 : BitString n)`, zero padding is
  `List.rightpad`, and block splitting is `BitString.padBlocks`).

## Main results

* `cbcMacBlocks_append`, `getLast_cbcEncryptBlocks_eq_cbcMacBlocks`: chaining composition identity
  and equivalence between the final block of `cbcEncryptBlocks` and `cbcMacBlocks`.
* `cbcSmooth_iff`, `cbcSmooth_of_prefixFree`: counting characterization and `(q, ℓ, q^2 * ℓ^2 /
  2^n)`-smoothness of prefix-free CBC-MAC ([KatzLindell2020], Claim 4.13).
* `abs_cbcRealSuccess_sub_cbcIdealSuccess_le`: adaptive oracle-program PRF bound
  `|cbcRealSuccess - cbcIdealSuccess| ≤ q^2 * ℓ^2 / 2^n` ([KatzLindell2020], Theorem 4.12).
* `cbcTwoToFourAttack_valid`, `cbcToThreeAttack_valid`, `cbcLeakedTagsAttack_valid`,
  `cbcRandomIVAttack_valid`, `cbcLengthSuffixAttack_valid_any_encoding`,
  `cbcLengthSuffixAttack_valid`, `rightpad_false_true_collide`, `zeroPadAttack_valid`:
  probability-`1` forgery attacks when prefix-freeness, tag hiding, fixed zero IV, length
  prepending, or injective padding is violated ([KatzLindell2020], Exercises 4.13–4.16).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 4.4 (pp. 121–127) and Exercises 4.13–4.16 (p. 142).
-/
@[expose] public section
namespace Cslib.Crypto
open Cslib.Probability
open scoped ENNReal
variable {n : ℕ}

/-! ### Section 1: Basic CBC-MAC Chaining ([KatzLindell2020], Section 4.4, Construction 4.9) -/
/-- **CBC-MAC chaining ([KatzLindell2020], Section 4.4, Construction 4.9)**: folds the CBC step
  `state ↦ g (state + block)` across a list of `n`-bit blocks starting from `iv` (which is `0` in
  standard basic CBC-MAC). -/
def cbcMacBlocks (g : BitString n → BitString n) (iv : BitString n)
    (msg : List (BitString n)) : BitString n :=
  msg.foldl (fun state block => g (state + block)) iv
@[simp] theorem cbcMacBlocks_nil (g : BitString n → BitString n) (iv : BitString n) :
    cbcMacBlocks g iv [] = iv := rfl
@[simp] theorem cbcMacBlocks_cons (g : BitString n → BitString n) (iv b : BitString n)
    (bs : List (BitString n)) : cbcMacBlocks g iv (b :: bs) = cbcMacBlocks g (g (iv + b)) bs := rfl
@[simp] theorem cbcMacBlocks_singleton (g : BitString n → BitString n) (iv b : BitString n) :
    cbcMacBlocks g iv [b] = g (iv + b) := rfl
/-- Chaining identity for `cbcMacBlocks`: processing `xs ++ ys` from `iv` is identical to
  processing `ys` from the intermediate tag `cbcMacBlocks g iv xs`. -/
@[simp] theorem cbcMacBlocks_append (g : BitString n → BitString n) (iv : BitString n)
    (xs ys : List (BitString n)) :
    cbcMacBlocks g iv (xs ++ ys) = cbcMacBlocks g (cbcMacBlocks g iv xs) ys := by
  simp [cbcMacBlocks, List.foldl_append]
/-- The final block of multi-block CBC encryption (`cbcEncryptBlocks`) on a nonempty message
  equals the `cbcMacBlocks` tag from the same initial state `iv`. -/
theorem getLast_cbcEncryptBlocks_eq_cbcMacBlocks (g : BitString n → BitString n)
    (iv b : BitString n) (bs : List (BitString n)) :
    (cbcEncryptBlocks g iv (b :: bs)).getLast (by simp) = cbcMacBlocks g iv (b :: bs) := by
  induction bs generalizing iv b with
  | nil => rfl
  | cons b' bs ih =>
    simp only [cbcEncryptBlocks_cons, cbcMacBlocks_cons]; rw [List.getLast_cons (by simp)]
    exact ih (g (iv + b)) b'
/-- Nonempty block vectors of length between `1` and `ℓ` blocks (`Σ k : Fin ℓ, Fin (k + 1) →
  BitString n`), matching the non-empty bounded-length domain of [KatzLindell2020], Section 4.4. -/
abbrev CBCInput (n ℓ : ℕ) := Σ k : Fin ℓ, Fin (k.val + 1) → BitString n
/-- Decidable equality on `CBCInput n ℓ`, transported from the sigma type. Instance search does not
  find it through the `abbrev` inside compound types such as `List (CBCInput n ℓ × BitString n)`. -/
instance instDecidableEqCBCInput {ℓ : ℕ} : DecidableEq (CBCInput n ℓ) :=
  inferInstanceAs (DecidableEq (Σ k : Fin ℓ, Fin (k.val + 1) → BitString n))
/-- Convert a `CBCInput n ℓ` into its underlying nonempty list of `n`-bit blocks. -/
def cbcInputBlocks {ℓ : ℕ} (x : CBCInput n ℓ) : List (BitString n) :=
  List.ofFn x.2
@[simp] theorem length_cbcInputBlocks {ℓ : ℕ} (x : CBCInput n ℓ) :
    (cbcInputBlocks x).length = x.1.val + 1 := by
  simp [cbcInputBlocks]
theorem cbcInputBlocks_ne_nil {ℓ : ℕ} (x : CBCInput n ℓ) : cbcInputBlocks x ≠ [] := by
  intro h; have := length_cbcInputBlocks x; rw [h] at this; simp at this
/-- Basic CBC-MAC with zero initial state on a bounded nonempty block input `CBCInput n ℓ`. -/
def cbcMacFinite {ℓ : ℕ} (g : BitString n → BitString n) (x : CBCInput n ℓ) : BitString n :=
  cbcMacBlocks g 0 (cbcInputBlocks x)
/-! ### Section 2: Prefix-Free CBC-MAC Smoothness ([KatzLindell2020], Claim 4.13) -/
/-- A list of `CBCInput n ℓ` queries is prefix-free if no two distinct inputs have one block list
  as a prefix of the other ([KatzLindell2020], Section 4.4, p. 124). -/
def CBCPrefixFree {ℓ : ℕ} (queries : List (CBCInput n ℓ)) : Prop :=
  ∀ x ∈ queries, ∀ y ∈ queries, x ≠ y →
    ¬ (cbcInputBlocks x).IsPrefix (cbcInputBlocks y)
/-- **CBC smoothness ([KatzLindell2020], Section 4.4, p. 125)**: `CBCSmooth n q ℓ δ` states that
  for every injective family of `q` prefix-free queries of at most `ℓ` blocks and every
  assignment of target tags `tags : Fin q → BitString n`, a uniform random function `g :
  BitString n → BitString n` satisfies `∀ i, cbcMacFinite g (inputs i) = tags i` with probability
  at least `(1 - δ) * 2^(-n * q)`. -/
def CBCSmooth (n q ℓ : ℕ) (δ : ℝ) : Prop :=
  ∀ inputs : Fin q → CBCInput n ℓ, Function.Injective inputs →
    CBCPrefixFree (List.ofFn inputs) → ∀ tags : Fin q → BitString n,
    (1 - δ) * (2 : ℝ) ^ (-((n * q : ℕ) : ℤ)) ≤
      (((PMF.uniformOfFintype (BitString n → BitString n)).map fun g =>
        decide (∀ i, cbcMacFinite g (inputs i) = tags i)) true).toReal
private def cbcRevChain (g : BitString n → BitString n) : List (BitString n) → BitString n
  | [] => 0
  | b :: r => g (cbcRevChain g r + b)
private def cbcRevLastInput (g : BitString n → BitString n) : List (BitString n) → BitString n
  | [] => 0
  | b :: r => cbcRevChain g r + b
private theorem cbcRevChain_cons (g : BitString n → BitString n) (b : BitString n)
    (r : List (BitString n)) : cbcRevChain g (b :: r) = g (cbcRevLastInput g (b :: r)) := rfl
private theorem cbcRevChain_ne_nil (g : BitString n → BitString n) {l : List (BitString n)}
    (h : l ≠ []) : cbcRevChain g l = g (cbcRevLastInput g l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons b r => rfl
private theorem cbcMacBlocks_zero_eq_cbcRevChain (g : BitString n → BitString n)
    (l : List (BitString n)) : cbcMacBlocks g 0 l = cbcRevChain g l.reverse := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    simp [cbcMacBlocks_append, ih, cbcRevChain]
private theorem cbcMacFinite_eq_cbcRevChain {ℓ : ℕ} (g : BitString n → BitString n)
    (x : CBCInput n ℓ) : cbcMacFinite g x = cbcRevChain g (cbcInputBlocks x).reverse :=
  cbcMacBlocks_zero_eq_cbcRevChain g (cbcInputBlocks x)
private theorem cbcRevChain_congr (g g' : BitString n → BitString n) : ∀ r : List (BitString n),
      (∀ a, a <:+ r → a ≠ [] → g' (cbcRevLastInput g a) = g (cbcRevLastInput g a)) →
      cbcRevChain g' r = cbcRevChain g r
  | [], _ => rfl
  | b :: r, h => by
    have ih := cbcRevChain_congr g g' r
      (fun a ha hne => h a (ha.trans (List.suffix_cons b r)) hne)
    have e : cbcRevLastInput g' (b :: r) = cbcRevLastInput g (b :: r) := by
      simp [cbcRevLastInput, ih]
    rw [cbcRevChain_cons, cbcRevChain_cons, e]
    exact h _ (List.suffix_refl _) (List.cons_ne_nil _ _)
private theorem cbcRevLastInput_congr (g g' : BitString n → BitString n) (u : List (BitString n))
    (h : ∀ a, a <:+ u.tail → a ≠ [] → g' (cbcRevLastInput g a) = g (cbcRevLastInput g a)) :
    cbcRevLastInput g' u = cbcRevLastInput g u := by
  cases u with
  | nil => rfl
  | cons b r => simp only [cbcRevLastInput]; rw [cbcRevChain_congr g g' r h]
private def cbcNodeFresh (g : BitString n → BitString n) (u p : List (BitString n)) : Prop :=
  (∀ a, a <:+ u.tail → a ≠ [] → cbcRevLastInput g a ≠ cbcRevLastInput g p) ∧
    (∀ a, a <:+ p.tail → a ≠ [] → cbcRevLastInput g a ≠ cbcRevLastInput g p)
private def cbcNodeCollisionEvent (g : BitString n → BitString n) (u v : List (BitString n)) :
    Prop :=
  v.tail ≠ [] ∧ cbcNodeFresh g u v.tail ∧ cbcRevLastInput g u = cbcRevLastInput g v
private theorem cbcNodeCollisionEvent_update (g : BitString n → BitString n)
    (u : List (BitString n)) (b : BitString n) (p : List (BitString n))
    (h : cbcNodeCollisionEvent g u (b :: p)) (z : BitString n) :
    cbcRevLastInput (Function.update g (cbcRevLastInput g p) z) p = cbcRevLastInput g p ∧
    cbcRevLastInput (Function.update g (cbcRevLastInput g p) z) u = cbcRevLastInput g u ∧
    g = Function.update (Function.update g (cbcRevLastInput g p) z)
      (cbcRevLastInput (Function.update g (cbcRevLastInput g p) z) p)
      (cbcRevLastInput (Function.update g (cbcRevLastInput g p) z) u + b) ∧
    z = (Function.update g (cbcRevLastInput g p) z)
      (cbcRevLastInput (Function.update g (cbcRevLastInput g p) z) p) := by
  obtain ⟨hp, ⟨fu, fp⟩, c⟩ := h
  simp only [List.tail_cons] at hp fu fp c
  have e1 : cbcRevLastInput (Function.update g (cbcRevLastInput g p) z) p =
      cbcRevLastInput g p :=
    cbcRevLastInput_congr _ _ _ (fun a ha hne => Function.update_of_ne (fp a ha hne) _ _)
  have e2 : cbcRevLastInput (Function.update g (cbcRevLastInput g p) z) u =
      cbcRevLastInput g u :=
    cbcRevLastInput_congr _ _ _ (fun a ha hne => Function.update_of_ne (fu a ha hne) _ _)
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e1, e2, Function.update_idem]
    have : g (cbcRevLastInput g p) = cbcRevLastInput g u + b := by
      rw [c, show cbcRevLastInput g (b :: p) = cbcRevChain g p + b from rfl,
        BitString.add_cancel_right, cbcRevChain_ne_nil g hp]
    rw [← this, Function.update_eq_self]
  · rw [e1]; simp
open Classical in private theorem card_cbcNodeCollisionEvent (u v : List (BitString n)) :
    (Finset.univ.filter (fun g : BitString n → BitString n =>
      cbcNodeCollisionEvent g u v)).card * 2 ^ n ≤
        Fintype.card (BitString n → BitString n) := by
  rcases v with _ | ⟨b, p⟩
  · simp [cbcNodeCollisionEvent]
  set S := Finset.univ.filter
    (fun g : BitString n → BitString n => cbcNodeCollisionEvent g u (b :: p))
  have hcard : (S ×ˢ (Finset.univ : Finset (BitString n))).card = S.card * 2 ^ n := by
    simp [Finset.card_product]
  rw [← hcard, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn
    (fun gz : (BitString n → BitString n) × BitString n =>
      Function.update gz.1 (cbcRevLastInput gz.1 p) gz.2)
  · intro _ _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  · rintro ⟨g1, z1⟩ h1 ⟨g2, z2⟩ h2 heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, S, Finset.mem_filter,
      Finset.mem_univ, true_and, and_true] at h1 h2
    simp only at heq
    obtain ⟨-, -, r1, s1⟩ := cbcNodeCollisionEvent_update g1 u b p h1 z1
    obtain ⟨-, -, r2, s2⟩ := cbcNodeCollisionEvent_update g2 u b p h2 z2
    rw [heq] at r1 s1
    have hg : g1 = g2 := r1.trans r2.symm
    subst hg
    rw [s1, ← s2]
private def cbcRevBlocks {ℓ : ℕ} (x : CBCInput n ℓ) : List (BitString n) :=
  (cbcInputBlocks x).reverse
private theorem length_cbcRevBlocks {ℓ : ℕ} (x : CBCInput n ℓ) :
    (cbcRevBlocks x).length = x.1.val + 1 := by
  simp [cbcRevBlocks]
private theorem cbcRevBlocks_ne_nil {ℓ : ℕ} (x : CBCInput n ℓ) : cbcRevBlocks x ≠ [] := by
  intro h; have := length_cbcRevBlocks x; rw [h] at this; simp at this
private def cbcNodeSet {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ) : Finset (List (BitString n)) :=
  Finset.univ.biUnion (fun i => (cbcRevBlocks (inputs i)).tails.toFinset.filter (· ≠ []))
private theorem mem_cbcNodeSet {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ) (a : List (BitString n)) :
    a ∈ cbcNodeSet inputs ↔ a ≠ [] ∧ ∃ i, a <:+ cbcRevBlocks (inputs i) := by
  simp [cbcNodeSet, List.mem_tails]; tauto
private theorem cbcNodeSet_suffix {q ℓ : ℕ} {inputs : Fin q → CBCInput n ℓ}
    {a a' : List (BitString n)} (ha : a ∈ cbcNodeSet inputs) (h : a' <:+ a) (hne : a' ≠ []) :
    a' ∈ cbcNodeSet inputs := by
  rw [mem_cbcNodeSet] at ha ⊢; obtain ⟨-, i, hi⟩ := ha; exact ⟨hne, i, h.trans hi⟩
private theorem cbcRevBlocks_mem_cbcNodeSet {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ) (i : Fin q) :
    cbcRevBlocks (inputs i) ∈ cbcNodeSet inputs :=
  (mem_cbcNodeSet _ _).2 ⟨cbcRevBlocks_ne_nil _, i, List.suffix_refl _⟩
private theorem card_cbcNodeSet_le {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ) :
    (cbcNodeSet inputs).card ≤ q * ℓ := by
  unfold cbcNodeSet
  refine Finset.card_biUnion_le.trans ?_
  have hstep : ∀ i : Fin q,
      ((cbcRevBlocks (inputs i)).tails.toFinset.filter (· ≠ [])).card ≤ ℓ := by
    intro i
    have h1 : (cbcRevBlocks (inputs i)).tails.toFinset.filter (· ≠ [])
        ⊆ (cbcRevBlocks (inputs i)).tails.toFinset.erase [] := by
      intro a ha; simp only [Finset.mem_filter] at ha
      exact Finset.mem_erase.2 ⟨ha.2, ha.1⟩
    have h2 : [] ∈ (cbcRevBlocks (inputs i)).tails.toFinset := by
      simp [List.mem_tails]
    have h3 := Finset.card_erase_of_mem h2
    have h4 := List.toFinset_card_le (cbcRevBlocks (inputs i)).tails
    rw [List.length_tails, length_cbcRevBlocks] at h4
    have h5 := (inputs i).1.isLt
    have h6 := Finset.card_le_card h1
    omega
  calc ∑ i : Fin q, ((cbcRevBlocks (inputs i)).tails.toFinset.filter (· ≠ [])).card
      ≤ ∑ _i : Fin q, ℓ := Finset.sum_le_sum (fun i _ => hstep i)
    _ = q * ℓ := by simp
private def cbcGoodFunction {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ)
    (g : BitString n → BitString n) : Prop :=
  ∀ a ∈ cbcNodeSet inputs, ∀ a' ∈ cbcNodeSet inputs,
    a ≠ a' → cbcRevLastInput g a ≠ cbcRevLastInput g a'
@[simp] private theorem cbcRevLastInput_singleton (g : BitString n → BitString n)
    (c : BitString n) : cbcRevLastInput g [c] = c :=
  zero_add c
private theorem exists_cbcNodeCollisionEvent {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ)
    (g : BitString n → BitString n) : ∀ m : ℕ, ∀ u ∈ cbcNodeSet inputs, ∀ v ∈ cbcNodeSet inputs,
      u ≠ v → cbcRevLastInput g u = cbcRevLastInput g v → u.length ≤ m → v.length ≤ m →
      ∃ u ∈ cbcNodeSet inputs, ∃ v ∈ cbcNodeSet inputs, cbcNodeCollisionEvent g u v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  have core : ∀ u ∈ cbcNodeSet inputs, ∀ v ∈ cbcNodeSet inputs,
      u ≠ v → cbcRevLastInput g u = cbcRevLastInput g v →
      u.length ≤ v.length → v.length ≤ m →
      ∃ u ∈ cbcNodeSet inputs, ∃ v ∈ cbcNodeSet inputs, cbcNodeCollisionEvent g u v := by
    intro u hu v hv huv hc hle hvm
    have hune := ((mem_cbcNodeSet _ _).1 hu).1
    rcases v with _ | ⟨b, p⟩
    · exact absurd rfl ((mem_cbcNodeSet _ _).1 hv).1
    by_cases hp : p = []
    · subst hp
      rcases u with _ | ⟨c, _ | ⟨d, r⟩⟩
      · exact absurd rfl hune
      · rw [cbcRevLastInput_singleton, cbcRevLastInput_singleton] at hc
        subst hc; exact absurd rfl huv
      · simp at hle
    have hpN : p ∈ cbcNodeSet inputs := cbcNodeSet_suffix hv (List.suffix_cons b p) hp
    by_cases hF : cbcNodeFresh g u p
    · exact ⟨u, hu, b :: p, hv, by simpa using hp, by simpa using hF, hc⟩
    · have hsmall : ∃ a ∈ cbcNodeSet inputs, a ≠ p ∧
          cbcRevLastInput g a = cbcRevLastInput g p ∧ a.length < (b :: p).length := by
        unfold cbcNodeFresh at hF
        rcases not_and_or.1 hF with h | h
        · push Not at h
          obtain ⟨a, ha, hne, he⟩ := h
          have haN : a ∈ cbcNodeSet inputs :=
            cbcNodeSet_suffix hu (ha.trans (List.tail_suffix u)) hne
          have hal : a.length < u.length := by
            have := ha.length_le; rw [List.length_tail] at this
            have : 0 < u.length := List.length_pos_iff.2 hune
            omega
          refine ⟨a, haN, ?_, he, by omega⟩
          rintro rfl
          have hlen : a.length = u.tail.length := by
            rw [List.length_tail]; simp at hle; omega
          have hut := ha.eq_of_length hlen
          rcases u with _ | ⟨c, u'⟩
          · exact hune rfl
          · simp only [List.tail_cons] at hut; subst hut
            have : c = b := add_left_cancel hc
            subst this; exact huv rfl
        · push Not at h
          obtain ⟨a, ha, hne, he⟩ := h
          have haN : a ∈ cbcNodeSet inputs :=
            cbcNodeSet_suffix hpN (ha.trans (List.tail_suffix p)) hne
          have hal : a.length < p.length := by
            have := ha.length_le; rw [List.length_tail] at this
            have : 0 < p.length := List.length_pos_iff.2 hp
            omega
          exact ⟨a, haN, by rintro rfl; omega, he, Nat.lt_succ_of_lt hal⟩
      obtain ⟨a, haN, hap, he, hal⟩ := hsmall
      have hm : (b :: p).length - 1 < m := by simp at hvm ⊢; omega
      exact IH _ hm a haN p hpN hap he (by simp at hal ⊢; omega) (by simp)
  intro u hu v hv huv hc hum hvm
  rcases le_total u.length v.length with h | h
  · exact core u hu v hv huv hc h hvm
  · exact core v hv u hu (Ne.symm huv) hc.symm h hum
open Classical in
private theorem card_not_cbcGoodFunction {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ) :
    (Finset.univ.filter (fun g : BitString n → BitString n =>
      ¬ cbcGoodFunction inputs g)).card * 2 ^ n ≤
        (cbcNodeSet inputs).card ^ 2 * Fintype.card (BitString n → BitString n) := by
  have hsub : Finset.univ.filter
      (fun g : BitString n → BitString n => ¬ cbcGoodFunction inputs g) ⊆
      (cbcNodeSet inputs ×ˢ cbcNodeSet inputs).biUnion
        (fun uv => Finset.univ.filter
          (fun g : BitString n → BitString n => cbcNodeCollisionEvent g uv.1 uv.2)) := by
    intro g hg; rw [Finset.mem_filter] at hg; replace hg := hg.2
    simp only [cbcGoodFunction] at hg; push Not at hg
    obtain ⟨u, hu, v, hv, huv, hc⟩ := hg
    obtain ⟨u', hu', v', hv', hE⟩ :=
      exists_cbcNodeCollisionEvent inputs g (max u.length v.length) u hu v hv huv hc
        (le_max_left _ _) (le_max_right _ _)
    simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨(u', v'), ⟨hu', hv'⟩, hE⟩
  calc (Finset.univ.filter
        (fun g : BitString n → BitString n => ¬ cbcGoodFunction inputs g)).card * 2 ^ n
      ≤ ((cbcNodeSet inputs ×ˢ cbcNodeSet inputs).biUnion
        (fun uv => Finset.univ.filter
          (fun g : BitString n → BitString n =>
            cbcNodeCollisionEvent g uv.1 uv.2))).card * 2 ^ n :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ uv ∈ cbcNodeSet inputs ×ˢ cbcNodeSet inputs,
          (Finset.univ.filter (fun g : BitString n → BitString n =>
            cbcNodeCollisionEvent g uv.1 uv.2)).card) * 2 ^ n :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ uv ∈ cbcNodeSet inputs ×ˢ cbcNodeSet inputs,
          (Finset.univ.filter (fun g : BitString n → BitString n =>
            cbcNodeCollisionEvent g uv.1 uv.2)).card * 2 ^ n :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ _uv ∈ cbcNodeSet inputs ×ˢ cbcNodeSet inputs,
          Fintype.card (BitString n → BitString n) :=
        Finset.sum_le_sum (fun uv _ => card_cbcNodeCollisionEvent uv.1 uv.2)
    _ = (cbcNodeSet inputs).card ^ 2 * Fintype.card (BitString n → BitString n) := by
        simp [Finset.card_product, sq]
private theorem cbcLeaf_not_ancestor {q ℓ : ℕ} {inputs : Fin q → CBCInput n ℓ}
    (hpf : CBCPrefixFree (List.ofFn inputs))
    (i : Fin q) {a : List (BitString n)} (ha : a ∈ cbcNodeSet inputs) :
    ¬ cbcRevBlocks (inputs i) <:+ a.tail := by
  intro h; obtain ⟨hne, j, hj⟩ := (mem_cbcNodeSet _ _).1 ha
  have hl1 := h.length_le; have hl2 := hj.length_le
  have hpos : 0 < a.length := List.length_pos_iff.2 hne
  rw [List.length_tail] at hl1
  have hij : inputs i ≠ inputs j := by
    intro e; rw [e] at hl1; omega
  have hsuf : cbcRevBlocks (inputs i) <:+ cbcRevBlocks (inputs j) :=
    h.trans ((List.tail_suffix a).trans hj)
  simp only [cbcRevBlocks, List.reverse_suffix] at hsuf
  exact hpf (inputs i) (List.mem_ofFn.2 ⟨i, rfl⟩) (inputs j) (List.mem_ofFn.2 ⟨j, rfl⟩)
    hij hsuf
private theorem cbcRevBlocks_inj {q ℓ : ℕ} {inputs : Fin q → CBCInput n ℓ}
    (hinj : Function.Injective inputs) (hpf : CBCPrefixFree (List.ofFn inputs))
    {i j : Fin q} (h : cbcRevBlocks (inputs i) = cbcRevBlocks (inputs j)) : i = j := by
  by_contra hij; have hij' : inputs i ≠ inputs j := fun e => hij (hinj e)
  have : cbcInputBlocks (inputs i) = cbcInputBlocks (inputs j) := by
    simpa [cbcRevBlocks] using h
  exact hpf (inputs i) (List.mem_ofFn.2 ⟨i, rfl⟩) (inputs j) (List.mem_ofFn.2 ⟨j, rfl⟩) hij'
    (this ▸ List.prefix_refl _)
open Classical in private noncomputable def cbcRetag {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ)
    (tags : Fin q → BitString n) (g : BitString n → BitString n) : BitString n → BitString n :=
  fun z =>
    if h : ∃ i, cbcRevLastInput g (cbcRevBlocks (inputs i)) = z then
      tags (Classical.choose h)
    else
      g z
open Classical in private theorem cbcRetag_lastInput {q ℓ : ℕ} {inputs : Fin q → CBCInput n ℓ}
    (hpf : CBCPrefixFree (List.ofFn inputs))
    (tags : Fin q → BitString n) {g : BitString n → BitString n}
    (hg : cbcGoodFunction inputs g) {a : List (BitString n)} (ha : a ∈ cbcNodeSet inputs) :
    cbcRevLastInput (cbcRetag inputs tags g) a = cbcRevLastInput g a := by
  apply cbcRevLastInput_congr
  intro a' ha' hne
  have ha'N : a' ∈ cbcNodeSet inputs :=
    cbcNodeSet_suffix ha (ha'.trans (List.tail_suffix a)) hne
  unfold cbcRetag; simp only [dite_eq_right_iff]; rintro ⟨i, hi⟩
  have hne' : a' ≠ cbcRevBlocks (inputs i) := by
    rintro rfl; exact cbcLeaf_not_ancestor hpf i ha ha'
  exact False.elim (hg _ ha'N _ (cbcRevBlocks_mem_cbcNodeSet inputs i) hne' hi.symm)
open Classical in private theorem card_cbcGoodFunction_le {q ℓ : ℕ} (inputs : Fin q → CBCInput n ℓ)
    (hinj : Function.Injective inputs) (hpf : CBCPrefixFree (List.ofFn inputs))
    (tags : Fin q → BitString n) :
    (Finset.univ.filter (fun g : BitString n → BitString n =>
      cbcGoodFunction inputs g)).card ≤
        (Finset.univ.filter (fun g : BitString n → BitString n =>
          ∀ i, cbcMacFinite g (inputs i) = tags i)).card * (2 ^ n) ^ q := by
  have hT : (Finset.univ.filter (fun g : BitString n → BitString n =>
        ∀ i, cbcMacFinite g (inputs i) = tags i)).card * (2 ^ n) ^ q =
      ((Finset.univ.filter (fun g : BitString n → BitString n =>
        ∀ i, cbcMacFinite g (inputs i) = tags i)) ×ˢ
          (Finset.univ : Finset (Fin q → BitString n))).card := by
    simp [Finset.card_product]
  rw [hT]
  apply Finset.card_le_card_of_injOn
    (fun g => (cbcRetag inputs tags g,
      fun i => g (cbcRevLastInput g (cbcRevBlocks (inputs i)))))
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true]
    intro i
    rw [cbcMacFinite_eq_cbcRevChain, ← cbcRevBlocks,
      cbcRevChain_ne_nil _ (cbcRevBlocks_ne_nil _),
      cbcRetag_lastInput hpf tags hg (cbcRevBlocks_mem_cbcNodeSet inputs i)]
    unfold cbcRetag
    have h : ∃ j, cbcRevLastInput g (cbcRevBlocks (inputs j)) =
        cbcRevLastInput g (cbcRevBlocks (inputs i)) := ⟨i, rfl⟩
    simp only [h, ↓reduceDIte]
    have hc := Classical.choose_spec h
    have hci : Classical.choose h = i := by
      by_contra hne
      exact hg _ (cbcRevBlocks_mem_cbcNodeSet inputs _) _
        (cbcRevBlocks_mem_cbcNodeSet inputs i)
        (fun e => hne (cbcRevBlocks_inj hinj hpf e)) hc
    rw [hci]
  · intro g1 hg1 g2 hg2 heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg1 hg2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hpts : ∀ i, cbcRevLastInput g1 (cbcRevBlocks (inputs i)) =
        cbcRevLastInput g2 (cbcRevBlocks (inputs i)) := by
      intro i
      rw [← cbcRetag_lastInput hpf tags hg1 (cbcRevBlocks_mem_cbcNodeSet inputs i), h1,
        cbcRetag_lastInput hpf tags hg2 (cbcRevBlocks_mem_cbcNodeSet inputs i)]
    funext z
    by_cases hz : ∃ i, cbcRevLastInput g1 (cbcRevBlocks (inputs i)) = z
    · obtain ⟨i, rfl⟩ := hz
      have := congrFun h2 i
      rw [this, hpts i]
    · have hz2 : ¬ ∃ i, cbcRevLastInput g2 (cbcRevBlocks (inputs i)) = z := by
        rintro ⟨i, hi⟩; exact hz ⟨i, (hpts i).trans hi⟩
      have := congrFun h1 z
      unfold cbcRetag at this
      simp only [hz, hz2, ↓reduceDIte] at this
      exact this
/-- Counting characterization of `CBCSmooth`. -/
theorem cbcSmooth_iff (n q ℓ : ℕ) (δ : ℝ) : CBCSmooth n q ℓ δ ↔
      ∀ inputs : Fin q → CBCInput n ℓ, Function.Injective inputs →
        CBCPrefixFree (List.ofFn inputs) → ∀ tags : Fin q → BitString n,
        (1 - δ) * (2 : ℝ) ^ (-((n * q : ℕ) : ℤ)) ≤
          ((Finset.univ.filter (fun g : BitString n → BitString n =>
            ∀ i, cbcMacFinite g (inputs i) = tags i)).card : ℝ) /
            Fintype.card (BitString n → BitString n) := by
  unfold CBCSmooth
  simp only [PMF.toReal_uniformOfFintype_map_apply_true, Finset.nnratCast_dens,
    decide_eq_true_eq]
/-- **Prefix-Free CBC-MAC Smoothness ([KatzLindell2020], Section 4.4, Claim 4.13, p. 125)**: for
  every block width `n` and all query parameters `q, ℓ`, random-function CBC-MAC is `(q, ℓ, q^2 *
  ℓ^2 / 2^n)`-smooth on prefix-free queries. -/
theorem cbcSmooth_of_prefixFree (n q ℓ : ℕ) :
    CBCSmooth n q ℓ ((q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n) := by
  classical
  rw [cbcSmooth_iff]
  intro inputs hinj hpf tags
  set N := Fintype.card (BitString n → BitString n)
  set K := (Finset.univ.filter (fun g : BitString n → BitString n =>
    ∀ i, cbcMacFinite g (inputs i) = tags i)).card
  set G := (Finset.univ.filter (fun g : BitString n → BitString n =>
    cbcGoodFunction inputs g)).card
  set B := (Finset.univ.filter (fun g : BitString n → BitString n =>
    ¬ cbcGoodFunction inputs g)).card
  set M := (cbcNodeSet inputs).card
  have hGB : G + B = N := Finset.card_filter_add_card_filter_not _
  have hB : B * 2 ^ n ≤ M ^ 2 * N := card_not_cbcGoodFunction inputs
  have hG : G ≤ K * (2 ^ n) ^ q := card_cbcGoodFunction_le inputs hinj hpf tags
  have hM : M ≤ q * ℓ := card_cbcNodeSet_le inputs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  have hX : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hY : (0 : ℝ) < ((2 : ℝ) ^ n) ^ q := by positivity
  have hpow : (2 : ℝ) ^ (-((n * q : ℕ) : ℤ)) = 1 / ((2 : ℝ) ^ n) ^ q := by
    rw [zpow_neg, zpow_natCast, pow_mul, one_div]
  rw [hpow, le_div_iff₀ hNpos]
  have hGBr : (G : ℝ) + B = N := by exact_mod_cast hGB
  have hBr : (B : ℝ) * (2 : ℝ) ^ n ≤ (M : ℝ) ^ 2 * N := by exact_mod_cast hB
  have hGr : (G : ℝ) ≤ K * ((2 : ℝ) ^ n) ^ q := by exact_mod_cast hG
  have hMr : (M : ℝ) ≤ q * ℓ := by exact_mod_cast hM
  have hM2 : (M : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hMr 2
  have hBd : (B : ℝ) ≤ (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n * N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hX]
    exact hBr.trans (mul_le_mul_of_nonneg_right hM2 (le_of_lt hNpos))
  rw [show (1 - (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n) * (1 / ((2 : ℝ) ^ n) ^ q) * N =
      ((1 - (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n) * N) / ((2 : ℝ) ^ n) ^ q by ring,
    div_le_iff₀ hY]
  nlinarith
/-! ### Section 3: Adaptive Oracle-Program PRF Bound ([KatzLindell2020], Theorem 4.12) -/
/-- The oracle interface of CBC-MAC distinguishers: a query is a bounded nonempty block input
  `CBCInput n ℓ`, answered by an `n`-bit tag. -/
abbrev CBCOracleSpec (n ℓ : ℕ) : OracleSpec (CBCInput n ℓ) := fun _ => BitString n
/-- Run an oracle program against a fixed oracle `CBCInput n ℓ → BitString n`, interpreting each
  call with `OracleComp.interpret` in the writer monad that logs the query. Returns the output
  together with the list of queried inputs, in order and with repetitions. -/
def cbcQueryRun {ℓ : ℕ} {α : Type} (oracle : CBCInput n ℓ → BitString n)
    (program : OracleComp (CBCOracleSpec n ℓ) α) : α × List (CBCInput n ℓ) :=
  (OracleComp.interpret (m := WriterT (List (CBCInput n ℓ)) Id)
    (fun x => WriterT.mk ((oracle x, [x]) : Id _)) program).run
@[simp] theorem cbcQueryRun_pure {ℓ : ℕ} {α : Type} (oracle : CBCInput n ℓ → BitString n)
    (a : α) : cbcQueryRun oracle (pure a : OracleComp (CBCOracleSpec n ℓ) α) = (a, []) := rfl
/-- One oracle call: the output and log of the continuation on the answer, after the query. -/
theorem cbcQueryRun_liftBind {ℓ : ℕ} {α : Type} (oracle : CBCInput n ℓ → BitString n)
    (x : CBCInput n ℓ) (next : BitString n → OracleComp (CBCOracleSpec n ℓ) α) :
    cbcQueryRun oracle (PFunctor.FreeM.liftBind (P := ⟨CBCInput n ℓ, CBCOracleSpec n ℓ⟩) x next) =
      ((cbcQueryRun oracle (next (oracle x))).1, x :: (cbcQueryRun oracle (next (oracle x))).2) :=
  rfl
@[simp] theorem cbcQueryRun_query_bind {ℓ : ℕ} {α : Type} (oracle : CBCInput n ℓ → BitString n)
    (x : CBCInput n ℓ) (next : BitString n → OracleComp (CBCOracleSpec n ℓ) α) :
    cbcQueryRun oracle (OracleComp.query x >>= next) =
      ((cbcQueryRun oracle (next (oracle x))).1, x :: (cbcQueryRun oracle (next (oracle x))).2) :=
  rfl
/-- The output of `cbcQueryRun` is the plain interpretation of the program with the oracle. -/
theorem cbcQueryRun_fst {ℓ : ℕ} {α : Type} (oracle : CBCInput n ℓ → BitString n) :
    ∀ program : OracleComp (CBCOracleSpec n ℓ) α,
      (cbcQueryRun oracle program).1 = OracleComp.interpret (m := Id) oracle program
  | .pure _ => rfl
  | .liftBind x next => cbcQueryRun_fst oracle (next (oracle x))
/-- An oracle program is `q`-admissible if, run against every fixed oracle, its queries are
  prefix-free and it makes at most `q` of them. Quantifying over executions keeps paths that no
  consistent oracle produces (inconsistent answers to repeated queries) out of the restriction. -/
def CBCAdmissible {ℓ : ℕ} (q : ℕ) (tree : OracleComp (CBCOracleSpec n ℓ) Bool) : Prop :=
  ∀ oracle, CBCPrefixFree (cbcQueryRun oracle tree).2 ∧
    (cbcQueryRun oracle tree).2.length ≤ q
/-- Real-world acceptance probability of a distribution `D` over adaptive oracle programs when
  interacting with `cbcMacFinite g` for a uniform random function `g : BitString n → BitString
  n`. -/
noncomputable def cbcRealSuccess (n ℓ : ℕ) (D : PMF (OracleComp (CBCOracleSpec n ℓ) Bool)) : ℝ :=
  ((do
    let g ← PMF.uniformOfFintype (BitString n → BitString n)
    let tree ← D
    return (cbcQueryRun (cbcMacFinite g) tree).1 : PMF Bool) true).toReal
/-- Ideal-world acceptance probability of a distribution `D` over adaptive oracle programs when
  interacting with a uniform random function `f : CBCInput n ℓ → BitString n`. -/
noncomputable def cbcIdealSuccess (n ℓ : ℕ) (D : PMF (OracleComp (CBCOracleSpec n ℓ) Bool)) : ℝ :=
  ((do
    let f ← PMF.uniformOfFintype (CBCInput n ℓ → BitString n)
    let tree ← D
    return (cbcQueryRun f tree).1 : PMF Bool) true).toReal
private def cbcDecisionTrace {ℓ : ℕ} (o : CBCInput n ℓ → BitString n) :
    OracleComp (CBCOracleSpec n ℓ) Bool → List (CBCInput n ℓ × BitString n)
  | .pure _ => []
  | .liftBind x next => (x, o x) :: cbcDecisionTrace o (next (o x))
private theorem cbcDecisionTrace_map_fst {ℓ : ℕ} (o : CBCInput n ℓ → BitString n) :
    ∀ T : OracleComp (CBCOracleSpec n ℓ) Bool,
      (cbcDecisionTrace o T).map Prod.fst = (cbcQueryRun o T).2
  | .pure _ => rfl
  | .liftBind x next => by
    rw [cbcQueryRun_liftBind]
    simp only [cbcDecisionTrace, List.map_cons, cbcDecisionTrace_map_fst o (next (o x))]
private theorem cbcDecisionTrace_eq_iff {ℓ : ℕ} (o o' : CBCInput n ℓ → BitString n) :
    ∀ T : OracleComp (CBCOracleSpec n ℓ) Bool, cbcDecisionTrace o T = cbcDecisionTrace o' T ↔
        ∀ e ∈ cbcDecisionTrace o' T, o e.1 = e.2
  | .pure _ => by simp [cbcDecisionTrace]
  | .liftBind x next => by
    simp only [cbcDecisionTrace, List.cons.injEq, Prod.mk.injEq, true_and, List.mem_cons,
      forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h1] at h2
      exact (cbcDecisionTrace_eq_iff o o' (next (o' x))).1 h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h1]
      exact (cbcDecisionTrace_eq_iff o o' (next (o' x))).2 h2
private theorem cbcQueryRun_fst_eq_of_trace {ℓ : ℕ} (o o' : CBCInput n ℓ → BitString n) :
    ∀ T : OracleComp (CBCOracleSpec n ℓ) Bool, cbcDecisionTrace o T = cbcDecisionTrace o' T →
      (cbcQueryRun o T).1 = (cbcQueryRun o' T).1
  | .pure _, _ => rfl
  | .liftBind x next, h => by
    simp only [cbcDecisionTrace, List.cons.injEq, Prod.mk.injEq, true_and] at h
    obtain ⟨h1, h2⟩ := h; rw [h1] at h2; simp only [cbcQueryRun_liftBind]; rw [h1]
    exact cbcQueryRun_fst_eq_of_trace o o' _ h2
private def reachableTraces {ℓ : ℕ} (T : OracleComp (CBCOracleSpec n ℓ) Bool) :
    Finset (List (CBCInput n ℓ × BitString n)) :=
  Finset.univ.image (fun o : CBCInput n ℓ → BitString n => cbcDecisionTrace o T)
open Classical in private noncomputable def traceOutput {ℓ : ℕ}
    (T : OracleComp (CBCOracleSpec n ℓ) Bool)
    (p : List (CBCInput n ℓ × BitString n)) : Bool :=
  if h : ∃ o, cbcDecisionTrace o T = p then
    (cbcQueryRun (Classical.choose h) T).1
  else
    false
open Classical in private theorem traceOutput_cbcDecisionTrace {ℓ : ℕ}
    (T : OracleComp (CBCOracleSpec n ℓ) Bool)
    (o : CBCInput n ℓ → BitString n) :
    traceOutput T (cbcDecisionTrace o T) = (cbcQueryRun o T).1 := by
  have h : ∃ o', cbcDecisionTrace o' T = cbcDecisionTrace o T := ⟨o, rfl⟩
  unfold traceOutput; simp only [h, ↓reduceDIte]
  exact cbcQueryRun_fst_eq_of_trace _ _ T (Classical.choose_spec h)
private theorem card_reachableTraces_sum {ℓ : ℕ} {X : Type*} [Fintype X]
    (O : X → CBCInput n ℓ → BitString n) (T : OracleComp (CBCOracleSpec n ℓ) Bool) :
    ∑ p ∈ reachableTraces T,
      (Finset.univ.filter (fun x => cbcDecisionTrace (O x) T = p)).card = Fintype.card X := by
  rw [← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := fun x => cbcDecisionTrace (O x) T)
      (t := reachableTraces T)]
  intro x _
  exact Finset.mem_image.2 ⟨O x, Finset.mem_univ _, rfl⟩
private theorem card_accept_eq_sum_reachableTraces {ℓ : ℕ} {X : Type*} [Fintype X]
    (O : X → CBCInput n ℓ → BitString n) (T : OracleComp (CBCOracleSpec n ℓ) Bool) :
    (Finset.univ.filter (fun x => (cbcQueryRun (O x) T).1 = true)).card =
      ∑ p ∈ (reachableTraces T).filter (fun p => traceOutput T p = true),
        (Finset.univ.filter (fun x => cbcDecisionTrace (O x) T = p)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => cbcDecisionTrace (O x) T)
    (t := reachableTraces T)]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.filter_filter]
    split_ifs with hp
    · congr 1
      apply Finset.filter_congr
      intro x _
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [← traceOutput_cbcDecisionTrace, h]
        exact hp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x _ ⟨h1, h2⟩
      apply hp
      rw [← h2, traceOutput_cbcDecisionTrace]
      exact h1
  · intro x _
    exact Finset.mem_image.2 ⟨O x, Finset.mem_univ _, rfl⟩
private theorem sum_filter_abs_sub_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (P : ι → Prop) [DecidablePred P] (δ : ℝ) (_hδ : 0 ≤ δ) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hab : ∀ i ∈ s, (1 - δ) * b i ≤ a i) (ha1 : ∑ i ∈ s, a i = 1) (hb1 : ∑ i ∈ s, b i = 1) :
    |∑ i ∈ s.filter P, a i - ∑ i ∈ s.filter P, b i| ≤ δ := by
  have key : ∀ Q : ι → Prop, ∀ _ : DecidablePred Q,
      ∑ i ∈ s.filter Q, b i - δ ≤ ∑ i ∈ s.filter Q, a i := by
    intro Q _
    have h1 : ∑ i ∈ s.filter Q, b i ≤ 1 := by
      rw [← hb1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi _ => hb i hi)
    have h0 : 0 ≤ ∑ i ∈ s.filter Q, b i :=
      Finset.sum_nonneg (fun i hi => hb i (Finset.mem_filter.1 hi).1)
    have h2 : (1 - δ) * ∑ i ∈ s.filter Q, b i ≤ ∑ i ∈ s.filter Q, a i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i hi => hab i (Finset.mem_filter.1 hi).1)
    nlinarith
  have k1 := key P inferInstance; have k2 := key (fun i => ¬ P i) inferInstance
  have sa := Finset.sum_filter_add_sum_filter_not s P a
  have sb := Finset.sum_filter_add_sum_filter_not s P b
  rw [abs_le]; constructor <;> linarith
private theorem tsum_pmf_abs_sub_le {α : Type*} (D : PMF α) (a b : α → ENNReal)
    (δ : ℝ) (hδ : 0 ≤ δ) (ha : ∀ T, a T ≤ 1) (hb : ∀ T, b T ≤ 1)
    (h : ∀ T, D T ≠ 0 → |(a T).toReal - (b T).toReal| ≤ δ) :
    |(∑' T, D T * a T).toReal - (∑' T, D T * b T).toReal| ≤ δ := by
  have one : ∀ c : α → ENNReal, (∀ T, c T ≤ 1) → ∑' T, D T * c T ≠ ⊤ := by
    intro c hc
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc ∑' T, D T * c T ≤ ∑' T, D T := tsum_le_tsum (fun T =>
            (mul_le_mul_right (hc T) _).trans_eq (mul_one _))
      _ = 1 := D.tsum_coe
  have side : ∀ a b : α → ENNReal, (∀ T, a T ≤ 1) → (∀ T, b T ≤ 1) →
      (∀ T, D T ≠ 0 → (a T).toReal ≤ (b T).toReal + δ) →
      (∑' T, D T * a T).toReal ≤ (∑' T, D T * b T).toReal + δ := by
    intro a b ha hb h
    have hle : ∑' T, D T * a T ≤ ∑' T, D T * b T + ENNReal.ofReal δ := by
      calc ∑' T, D T * a T ≤ ∑' T, (D T * b T + D T * ENNReal.ofReal δ) := by
            apply tsum_le_tsum; intro T; dsimp only
            by_cases hD : D T = 0
            · simp [hD]
            rw [← mul_add]; apply mul_le_mul_right
            have haT : a T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ha T)
            have hbT : b T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hb T)
            rw [← ENNReal.ofReal_toReal haT, ← ENNReal.ofReal_toReal hbT,
              ← ENNReal.ofReal_add ENNReal.toReal_nonneg hδ]
            exact ENNReal.ofReal_le_ofReal (h T hD)
        _ = ∑' T, D T * b T + ENNReal.ofReal δ := by
            rw [tsum_add, ENNReal.tsum_mul_right, D.tsum_coe, one_mul]
    have := ENNReal.toReal_le_add hle (one b hb) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hδ] at this
  have s1 := side a b ha hb (fun T hT => by have := h T hT; rw [abs_le] at this; linarith)
  have s2 := side b a hb ha (fun T hT => by have := h T hT; rw [abs_le] at this; linarith)
  rw [abs_le]; constructor <;> linarith
private theorem cbcDecisionTrace_prob_lower_bound {ℓ : ℕ} (q : ℕ)
    (T : OracleComp (CBCOracleSpec n ℓ) Bool)
    (hT : CBCAdmissible q T) (p : List (CBCInput n ℓ × BitString n)) (hp : p ∈ reachableTraces T) :
    (1 - (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n) * (((Finset.univ.filter
        (fun f : CBCInput n ℓ → BitString n => cbcDecisionTrace f T = p)).card : ℝ) /
          Fintype.card (CBCInput n ℓ → BitString n)) ≤ ((Finset.univ.filter
        (fun g : BitString n → BitString n => cbcDecisionTrace (cbcMacFinite g) T = p)).card : ℝ) /
          Fintype.card (BitString n → BitString n) := by
  obtain ⟨o0, -, rfl⟩ := Finset.mem_image.1 hp
  set S := (cbcQueryRun o0 T).2.toFinset with hS
  have self : ∀ e ∈ cbcDecisionTrace o0 T, o0 e.1 = e.2 :=
    (cbcDecisionTrace_eq_iff o0 o0 T).1 rfl
  have memS : ∀ x, x ∈ S ↔ ∃ e ∈ cbcDecisionTrace o0 T, e.1 = x := by
    intro x
    rw [hS, List.mem_toFinset, ← cbcDecisionTrace_map_fst, List.mem_map]
  have hagree : ∀ o, cbcDecisionTrace o T = cbcDecisionTrace o0 T ↔
      ∀ x ∈ S, o x = o0 x := by
    intro o
    rw [cbcDecisionTrace_eq_iff]
    constructor
    · intro h x hx
      obtain ⟨e, he, rfl⟩ := (memS x).1 hx
      rw [h e he, self e he]
    · intro h e he
      rw [h e.1 ((memS _).2 ⟨e, he, rfl⟩), self e he]
  have hpf := (hT o0).1; have hkq : S.card ≤ q := (List.toFinset_card_le _).trans (hT o0).2
  set k := S.card; set N := Fintype.card (CBCInput n ℓ); have hkN : k ≤ N := Finset.card_le_univ S
  have hI : (Finset.univ.filter (fun f : CBCInput n ℓ → BitString n =>
      cbcDecisionTrace f T = cbcDecisionTrace o0 T)).card = (2 ^ n) ^ (N - k) := by
    rw [Finset.filter_congr (fun f _ => hagree f), Fintype.card_filter_forall_mem_eq,
      Finset.card_compl]
    congr 1; simp
  have hF : Fintype.card (CBCInput n ℓ → BitString n) = (2 ^ n) ^ N := by
    rw [Fintype.card_fun]; congr 1; simp
  let e : Fin k ≃ S := S.equivFin.symm
  let inputs : Fin k → CBCInput n ℓ := fun i => (e i).1
  have hinj : Function.Injective inputs := fun i j h => e.injective (Subtype.ext h)
  have hmem : ∀ x, x ∈ List.ofFn inputs → x ∈ (cbcQueryRun o0 T).2 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact List.mem_toFinset.1 (e i).2
  have hpf' : CBCPrefixFree (List.ofFn inputs) := fun x hx y hy hxy =>
    hpf x (hmem x hx) y (hmem y hy) hxy
  have hsm := (cbcSmooth_iff n k ℓ _).1 (cbcSmooth_of_prefixFree n k ℓ) inputs hinj hpf'
    (fun i => o0 (inputs i))
  have hR : (Finset.univ.filter (fun g : BitString n → BitString n =>
      cbcDecisionTrace (cbcMacFinite g) T = cbcDecisionTrace o0 T)) =
        Finset.univ.filter (fun g : BitString n → BitString n =>
          ∀ i, cbcMacFinite g (inputs i) = o0 (inputs i)) := by
    apply Finset.filter_congr
    intro g _
    rw [hagree]
    constructor
    · intro h i; exact h _ (e i).2
    · intro h x hx
      have := h (e.symm ⟨x, hx⟩)
      simpa [inputs] using this
  rw [hR]
  refine le_trans ?_ hsm
  rw [hI, hF]
  have hX : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpow : (2 : ℝ) ^ (-((n * k : ℕ) : ℤ)) = 1 / ((2 : ℝ) ^ n) ^ k := by
    rw [zpow_neg, zpow_natCast, pow_mul, one_div]
  have hratio : (((2 ^ n) ^ (N - k) : ℕ) : ℝ) / (((2 ^ n) ^ N : ℕ) : ℝ) =
      1 / ((2 : ℝ) ^ n) ^ k := by
    push_cast
    rw [show N = (N - k) + k by omega, pow_add, Nat.add_sub_cancel]
    field_simp
  rw [hratio, hpow]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hk2 : (k : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by
    have : (k : ℝ) ≤ q := by exact_mod_cast hkq
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hdiv : (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n ≤
      (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n := by
    apply div_le_div_of_nonneg_right _ hX.le
    exact mul_le_mul_of_nonneg_right hk2 (by positivity)
  linarith
private theorem cbcDecisionTree_gap {ℓ : ℕ} (q : ℕ) (T : OracleComp (CBCOracleSpec n ℓ) Bool)
    (hT : CBCAdmissible q T) :
    |((Finset.univ.filter (fun g : BitString n → BitString n =>
        (cbcQueryRun (cbcMacFinite g) T).1 = true)).card : ℝ) /
        Fintype.card (BitString n → BitString n) -
      ((Finset.univ.filter (fun f : CBCInput n ℓ → BitString n =>
        (cbcQueryRun f T).1 = true)).card : ℝ) /
        Fintype.card (CBCInput n ℓ → BitString n)| ≤
      (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  rw [card_accept_eq_sum_reachableTraces (fun g : BitString n → BitString n => cbcMacFinite g) T,
    card_accept_eq_sum_reachableTraces (fun f : CBCInput n ℓ → BitString n => f) T]
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  have hG : (0 : ℝ) < Fintype.card (BitString n → BitString n) := by
    exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < Fintype.card (CBCInput n ℓ → BitString n) := by
    exact_mod_cast Fintype.card_pos
  apply sum_filter_abs_sub_le (reachableTraces T) _ _ _ _ (by positivity)
  · intro i _; positivity
  · intro p hp; exact cbcDecisionTrace_prob_lower_bound q T hT p hp
  · rw [← Finset.sum_div, div_eq_one_iff_eq hG.ne']
    exact_mod_cast card_reachableTraces_sum
      (fun g : BitString n → BitString n => cbcMacFinite g) T
  · rw [← Finset.sum_div, div_eq_one_iff_eq hF.ne']
    exact_mod_cast card_reachableTraces_sum
      (fun f : CBCInput n ℓ → BitString n => f) T
private theorem uniformOfFintype_bind_comm {ℓ : ℕ} {G : Type} [Fintype G] [Nonempty G]
    (D : PMF (OracleComp (CBCOracleSpec n ℓ) Bool))
    (h : G → OracleComp (CBCOracleSpec n ℓ) Bool → Bool) : (do
      let g ← PMF.uniformOfFintype G let T ← D return h g T) =
      D.bind (fun T => (PMF.uniformOfFintype G).map (fun g => h g T)) :=
  PMF.bind_comm _ D fun g T => PMF.pure (h g T)
/-- **Prefix-Free CBC-MAC Adaptive PRF Security Bound ([KatzLindell2020], Section 4.4, Theorem
  4.12, p. 124)**: for every block width `n`, query budget `q`, maximum block length `ℓ`, and
  distribution `D` over `q`-admissible adaptive oracle programs, the distinguishing advantage
  between `cbcMacFinite g` (for uniform `g : BitString n → BitString n`) and a uniform random
  function `f : CBCInput n ℓ → BitString n` is at most `q^2 * ℓ^2 / 2^n`. -/
theorem abs_cbcRealSuccess_sub_cbcIdealSuccess_le (n q ℓ : ℕ)
    (D : PMF (OracleComp (CBCOracleSpec n ℓ) Bool))
    (hD : ∀ tree, D tree ≠ 0 → CBCAdmissible q tree) :
    |cbcRealSuccess n ℓ D - cbcIdealSuccess n ℓ D| ≤
      (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  have hδ : (0 : ℝ) ≤ (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (2 : ℝ) ^ n := by positivity
  unfold cbcRealSuccess cbcIdealSuccess
  rw [uniformOfFintype_bind_comm D (fun g T => (cbcQueryRun (cbcMacFinite g) T).1),
    uniformOfFintype_bind_comm D
      (fun (f : CBCInput n ℓ → BitString n) T => (cbcQueryRun f T).1),
    PMF.bind_apply, PMF.bind_apply]
  apply tsum_pmf_abs_sub_le D _ _ _ hδ (fun T => PMF.coe_le_one _ _)
    (fun T => PMF.coe_le_one _ _)
  intro T hT
  rw [PMF.toReal_uniformOfFintype_map_apply_true, PMF.toReal_uniformOfFintype_map_apply_true,
    Finset.nnratCast_dens, Finset.nnratCast_dens]
  exact cbcDecisionTree_gap q T (hD T hT)
/-! ### Section 4: Explicit CBC-MAC Forgery Attacks ([KatzLindell2020], Exercises 4.13–4.16) -/
/-- A CBC-MAC forgery trace `(queriedMessages, forgedMessage, forgedTag)`. -/
abbrev CBCTagForgery (n : ℕ) := List (List (BitString n)) × List (BitString n) × BitString n
/-- A forgery trace `(qs, m*, t*)` is valid against `cbcMacBlocks g 0` if `m* ∉ qs` and
  `cbcMacBlocks g 0 m* = t*`. -/
def cbcForgeryValid (g : BitString n → BitString n) (trace : CBCTagForgery n) : Prop :=
  trace.2.1 ∉ trace.1 ∧ cbcMacBlocks g 0 trace.2.1 = trace.2.2
/-- **Two-block-to-four-block length-extension attack ([KatzLindell2020], Exercise 4.13(a),
  p. 142)**: queries `[0, 0]` to obtain tag `t = g(g(0))`, then forges `[0, 0, t, 0]` with the same
  tag `t`. -/
def cbcTwoToFourAttack (oracle : List (BitString n) → BitString n) : CBCTagForgery n :=
  let t := oracle [0, 0]
  ([[0, 0]], [0, 0, t, 0], t)
/-- `cbcTwoToFourAttack` succeeds with probability `1` against every round function `g` using a
  single 2-block query and forging a fresh 4-block message ([KatzLindell2020], Exercise 4.13(a),
  p. 142). -/
theorem cbcTwoToFourAttack_valid (g : BitString n → BitString n) :
    let trace := cbcTwoToFourAttack (cbcMacBlocks g 0)
    trace.1.length = 1 ∧ (∀ q ∈ trace.1, q.length = 2) ∧
      trace.2.1.length = 4 ∧ cbcForgeryValid g trace := by
  simp [cbcTwoToFourAttack, cbcForgeryValid, cbcMacBlocks]
/-- **One-and-two-block-to-three-block splicing attack ([KatzLindell2020], Exercise 4.13(b),
  p. 142)**: queries `[0]` (getting `t = g(0)`) and `[0, 0]` (getting `u = g(g(0))`), then forges
  `[0, t, 0]` with tag `u`. -/
def cbcToThreeAttack (oracle : List (BitString n) → BitString n) : CBCTagForgery n :=
  let t := oracle [0]
  let u := oracle [0, 0]
  ([[0], [0, 0]], [0, t, 0], u)
/-- `cbcToThreeAttack` succeeds with probability `1` against every round function `g` using two
  queries (`[0]` and `[0, 0]`) and forging the fresh 3-block message `[0, g(0), 0]`
  ([KatzLindell2020], Exercise 4.13(b), p. 142). -/
theorem cbcToThreeAttack_valid (g : BitString n → BitString n) :
    let trace := cbcToThreeAttack (cbcMacBlocks g 0)
    trace.1.length = 2 ∧ trace.2.1.length = 3 ∧ cbcForgeryValid g trace := by
  simp [cbcToThreeAttack, cbcForgeryValid, cbcMacBlocks]
/-- Insecure two-block CBC-MAC variant that outputs both intermediate chaining values `(g(m₁),
  g(g(m₁) + m₂))` ([KatzLindell2020], Exercise 4.14(a), p. 142). -/
def cbcAllTagsTwo (g : BitString n → BitString n) (msg : BitString n × BitString n) :
    BitString n × BitString n :=
  (g msg.1, g (g msg.1 + msg.2))
/-- **Leaked-intermediate-tags forgery attack ([KatzLindell2020], Exercise 4.14(a), p. 142)**:
  queries `(0, 0)`, `(1^n, 0)`, and `(1^n, 1^n)`, and uses the leaked first-block tags to forge a
  fresh 2-block message. -/
def cbcLeakedTagsAttack (oracle : (BitString n × BitString n) → BitString n × BitString n) :
    List (BitString n × BitString n) × (BitString n × BitString n) × (BitString n × BitString n) :=
  let z : BitString n := 0; let o : BitString n := 1
  let a := oracle (z, z); let b := oracle (o, z); let c := oracle (o, o)
  let forge := if a.1 = b.1 then ((z, o), c) else ((z, a.1 + b.1), b)
  ([(z, z), (o, z), (o, o)], forge.1, forge.2)
private theorem zero_ne_one_of_pos (hn : 0 < n) : (0 : BitString n) ≠ 1 := by
  intro h; exact Bool.false_ne_true (congrFun h ⟨0, hn⟩)
/-- `cbcLeakedTagsAttack` makes `3` queries and outputs a fresh 2-block message with a valid
  final tag for every round function `g` whenever `0 < n` ([KatzLindell2020], Exercise 4.14(a),
  p. 142). -/
theorem cbcLeakedTagsAttack_valid (hn : 0 < n) (g : BitString n → BitString n) :
    let trace := cbcLeakedTagsAttack (cbcAllTagsTwo g)
    trace.1.length = 3 ∧ trace.2.1 ∉ trace.1 ∧
      (cbcAllTagsTwo g trace.2.1).2 = trace.2.2.2 := by
  have hzo : (0 : BitString n) ≠ 1 := zero_ne_one_of_pos hn
  by_cases h : g 0 = g ((1 : BitString n))
  · simp [cbcLeakedTagsAttack, cbcAllTagsTwo, h, hzo, Ne.symm hzo]
  · have hx : g 0 + g ((1 : BitString n)) ≠ 0 := fun e =>
      h (by simpa using congrArg (· + g ((1 : BitString n))) e)
    simp [cbcLeakedTagsAttack, cbcAllTagsTwo, h, hzo, hx]
/-- Insecure random-IV CBC-MAC variant that outputs `(iv, cbcMacBlocks g iv msg)`
  ([KatzLindell2020], Exercise 4.14(b), p. 142). -/
def cbcRandomIVMac (g : BitString n → BitString n) (iv : BitString n)
    (msg : List (BitString n)) : BitString n × BitString n :=
  (iv, cbcMacBlocks g iv msg)
/-- **Random-IV CBC-MAC forgery attack ([KatzLindell2020], Exercise 4.14(b), p. 142)**: given
  `(iv, t)` for message `[0]`, outputs message `1^n` with modified IV `iv + 1^n` and tag `t`. -/
def cbcRandomIVAttack (tag : BitString n × BitString n) :
    BitString n × (BitString n × BitString n) :=
  let o := (1 : BitString n); (o, (tag.1 + o, tag.2))
/-- `cbcRandomIVAttack` produces a fresh 1-block message `1^n ≠ 0` whose random-IV CBC-MAC tag
  (`cbcRandomIVMac`) validates for every `iv` and `g` whenever `0 < n` ([KatzLindell2020],
  Exercise 4.14(b), p. 142). -/
theorem cbcRandomIVAttack_valid (hn : 0 < n) (g : BitString n → BitString n) (iv : BitString n) :
    let forged := cbcRandomIVAttack (cbcRandomIVMac g iv [0])
    forged.1 ≠ 0 ∧ cbcRandomIVMac g forged.2.1 [forged.1] = forged.2 :=
  ⟨(zero_ne_one_of_pos hn).symm, by simp [cbcRandomIVAttack, cbcRandomIVMac]⟩
/-- Insecure CBC-MAC variant that appends `encodeLength (msg.length * n)` at the end of `msg`
  ([KatzLindell2020], Exercise 4.15, p. 142). -/
def lengthAppendedCBC (g : BitString n → BitString n)
    (encodeLength : ℕ → List (BitString n)) (msg : List (BitString n)) : BitString n :=
  cbcMacBlocks g 0 (msg ++ encodeLength (msg.length * n))
/-- **Append-length CBC-MAC forgery attack ([KatzLindell2020], Exercise 4.15, p. 142)**: queries
  `[0]`, `[1^n]`, and `[0] ++ encodeLength n ++ [t]`, and forges
  `[1^n] ++ encodeLength n ++ [u]`. -/
def cbcLengthSuffixAttack (encodeLength : ℕ → List (BitString n))
    (oracle : List (BitString n) → BitString n) : CBCTagForgery n :=
  let z : BitString n := 0; let o : BitString n := 1
  let t := oracle [z]; let u := oracle [o]; let query := [z] ++ encodeLength n ++ [t]
  ([[z], [o], query], [o] ++ encodeLength n ++ [u], oracle query)
/-- `cbcLengthSuffixAttack` succeeds with `3` queries against `lengthAppendedCBC` for every
  `encodeLength` and `g` whenever `0 < n` ([KatzLindell2020], Exercise 4.15, p. 142). -/
theorem cbcLengthSuffixAttack_valid_any_encoding (hn : 0 < n)
    (encodeLength : ℕ → List (BitString n)) (g : BitString n → BitString n) :
    let trace := cbcLengthSuffixAttack encodeLength (lengthAppendedCBC g encodeLength)
    trace.1.length = 3 ∧ trace.2.1 ∉ trace.1 ∧
      lengthAppendedCBC g encodeLength trace.2.1 = trace.2.2 := by
  have hzo : (0 : BitString n) ≠ 1 := zero_ne_one_of_pos hn
  refine ⟨rfl, ?_, by simp [cbcLengthSuffixAttack, lengthAppendedCBC]⟩
  simp only [cbcLengthSuffixAttack, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h1 | h2 | h3)
  · have := congrArg List.length h1; simp at this
  · have := congrArg List.length h2; simp at this
  · have := congrArg List.head? h3; simp [Ne.symm hzo] at this
/-- For a single-block length encoding and `4 ≤ n`, all queries and the forged message of
  `cbcLengthSuffixAttack` also satisfy the `< 2^n` bit-length bound ([KatzLindell2020], Exercise
  4.15, p. 142). -/
theorem cbcLengthSuffixAttack_valid (hn : 4 ≤ n) (encodeBlock : ℕ → BitString n)
    (g : BitString n → BitString n) :
    let encodeLength : ℕ → List (BitString n) := fun len => [encodeBlock len]
    let trace := cbcLengthSuffixAttack encodeLength (lengthAppendedCBC g encodeLength)
    trace.1.length = 3 ∧ (∀ q ∈ trace.1, q.length * n < 2 ^ n) ∧
      trace.2.1.length * n < 2 ^ n ∧ trace.2.1 ∉ trace.1 ∧
      lengthAppendedCBC g encodeLength trace.2.1 = trace.2.2 := by
  have hpow : ∀ m : ℕ, 4 ≤ m → 3 * m < 2 ^ m := by
    intro m hm; induction m, hm using Nat.le_induction with
    | base => decide
    | succ m _ ih => rw [pow_succ]; omega
  have hp := hpow n hn; have hp1 : n < 2 ^ n := by omega
  have hvalid := cbcLengthSuffixAttack_valid_any_encoding (by omega)
    (fun len => [encodeBlock len]) g
  refine ⟨hvalid.1, ?_, by simp [cbcLengthSuffixAttack, hp], hvalid.2.1, hvalid.2.2⟩
  intro q hq; simp only [cbcLengthSuffixAttack, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> simp [hp1, hp]
/-- Insecure zero-padded CBC-MAC for messages of length at most `ℓ * 2^n` bits: right-pad with
  `false` bits to length `ℓ * 2^n` (`List.rightpad`), then split into the `(ℓ * 2^n) / n` blocks of
  `BitString.padBlocks` (the floor block count; exact when `n ∣ ℓ * 2^n`) ([KatzLindell2020],
  Exercise 4.16, p. 142). -/
def zeroPadCBC (g : BitString n → BitString n) (ℓ : ℕ) (m : List Bool) : BitString n :=
  cbcMacBlocks g 0 (BitString.padBlocks n (ℓ * 2 ^ n) (List.rightpad (ℓ * 2 ^ n) false m))
/-- **Zero-padded CBC-MAC forgery attack ([KatzLindell2020], Exercise 4.16, p. 142)**: queries
  `[true]` and outputs the distinct message `[true, false]` with the same tag. -/
def zeroPadAttack (oracle : List Bool → BitString n) :
    List (List Bool) × List Bool × BitString n := ([[true]], [true, false], oracle [true])
/-- For any `L ≥ 2`, right-padding `[true]` and `[true, false]` with `false` to length `L`
  produces the same bit string. -/
theorem rightpad_false_true_collide (L : ℕ) (hL : 2 ≤ L) :
    List.rightpad L false [true] = List.rightpad L false [true, false] := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 2 := ⟨L - 2, by omega⟩
  simp [List.rightpad, List.replicate_succ]
/-- `zeroPadAttack` succeeds with `1` query against `zeroPadCBC` for every `0 < n`, `0 < ℓ`, and
  `g` ([KatzLindell2020], Exercise 4.16, p. 142). -/
theorem zeroPadAttack_valid {ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (g : BitString n → BitString n) :
    let trace := zeroPadAttack (zeroPadCBC g ℓ)
    trace.1.length = 1 ∧ (∀ q ∈ trace.1, q.length ≤ ℓ * 2 ^ n) ∧
      trace.2.1.length ≤ ℓ * 2 ^ n ∧ trace.2.1 ∉ trace.1 ∧
      zeroPadCBC g ℓ trace.2.1 = trace.2.2 := by
  have hpow : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 2 ≤ ℓ * 2 ^ n := (by omega : 2 ≤ 1 * 2 ^ n).trans (Nat.mul_le_mul_right _ hℓ)
  refine ⟨rfl, ?_, by simp [zeroPadAttack]; omega, by simp [zeroPadAttack], ?_⟩
  · intro q hq; simp only [zeroPadAttack, List.mem_singleton] at hq; subst hq; simp; omega
  · simp only [zeroPadAttack, zeroPadCBC]; rw [rightpad_false_true_collide _ h2]
end Cslib.Crypto
