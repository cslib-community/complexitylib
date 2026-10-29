/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.FewP
public import Complexity.Computability.Complexity.Classes.SPP
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Foundations.Data.BitString.WordCount

/-!
# FewP is in SPP

`FewP ⊆ SPP` [Köbler, Schöning, Toda and Torán][KoeblerSchoeningTodaToran1992], in the gap
formulation of [Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]. For a problem in `FewP`, let
`T` be the set of certificates of length `len` accepted on an instance, of size `m ≤ q`. The subsets
`U ⊆ T` cancel in pairs by parity: `∑ U ⊆ T, (-1) ^ |U| = (1 - 1) ^ m` is `1` when `m = 0` and `0`
otherwise. Every subset has at most `q` elements, so it is listed, in increasing order, in `q`
slots of `len + 1` bits, each a flag followed by a certificate. The numbers `E` and `O` of such
listings of the subsets of even and of odd size are counted by polynomial-time verifiers, so they
are in `#P`, and `1 + O - E` is a `GapP` function equal to `1` on members and `0` on the other
instances.

## The listings

A word of `q` slots is read from the left (`Cslib.Complexity.SortedSubsets.step`). A flagged slot
lists its certificate, which must be accepted, come before every empty slot and exceed the last
certificate listed in binary value; an empty slot must hold only bits `false`. The well-formed
words are exactly the increasing listings of the subsets of `T` with at most `q` elements. The
proof does not construct this bijection; it shows by induction on the number of slots that the
well-formed words, counted with the sign of the parity of their number of certificates, sum to
the sign of the starting state when no accepted certificate is above the last one listed, and to
`0` otherwise (`Cslib.Complexity.SortedSubsets.signedSum_eq`): a first empty slot leaves one
well-formed completion, and a first certificate `c` contributes, by induction, the opposite sign
exactly when `c` is the largest certificate above the last one listed.

## Main definitions

* `Cslib.Complexity.SortedSubsets.step`: read one slot of a listing.
* `Cslib.Complexity.SortedSubsets.verifier`: the verifier counting the listings of a given parity.

## Main results

* `Cslib.Complexity.SortedSubsets.signedSum_eq`: the signed count of the listings.
* `Cslib.Complexity.SortedSubsets.computableInPolyTime_verifier`: the verifier is
  polynomial-time.
* `Cslib.Complexity.FewP_subset_SPP`: **`FewP ⊆ SPP`**.

## References

* [J. Köbler, U. Schöning, S. Toda, J. Torán, *Turing machines with few accepting computations
  and low sets for PP*][KoeblerSchoeningTodaToran1992]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM BitString

namespace SortedSubsets

/-- The state of a scan of slots: whether the slots read so far are well formed, the parity of the
number of certificates listed, whether an empty slot has been read, whether a certificate has been
listed, and the last certificate listed. -/
abbrev State := Bool × Bool × Bool × Bool × List Bool

/-- The state before any slot is read. -/
def init : State := (true, false, false, false, [])

/-- Read one slot, a flag bit followed by a certificate. A flagged slot lists its certificate, which
must be accepted by `acc`, come before every empty slot, and exceed the last certificate listed in
binary value; an empty slot must hold only bits `false`. -/
def step (acc : List Bool → Bool) (s : State) (slot : List Bool) : State :=
  if slot.headD false then
    (s.1 && !s.2.2.1 && acc slot.tail &&
        (!s.2.2.2.1 || decide (binaryValue s.2.2.2.2 < binaryValue slot.tail)),
      !s.2.1, s.2.2.1, true, slot.tail)
  else (s.1 && !slot.tail.any (fun b => b), s.2.1, true, s.2.2.2.1, s.2.2.2.2)

/-- A final state is accepted for the parity `b` when it is well formed and lists a number of
certificates of parity `b`. -/
def accepts (b : Bool) (s : State) : Bool := s.1 && s.2.1 == b

/-- The sign of a final state: `0` if malformed, otherwise `1` or `-1` by the parity of the number
of certificates listed. -/
def sign (s : State) : ℤ := if s.1 then (if s.2.1 then -1 else 1) else 0

/-- The sign of a state is its acceptance for the even parity minus its acceptance for the odd
parity. -/
private theorem sign_eq_sub (s : State) : sign s =
    (if accepts false s = true then 1 else 0) - (if accepts true s = true then 1 else 0) := by
  obtain ⟨ok, par, _⟩ := s
  cases ok <;> cases par <;> simp [accepts, sign]

/-- The certificates of length `len` accepted by `acc` that may be listed after the state `s`: above
the last certificate listed, if any. -/
def above (acc : List Bool → Bool) (len : ℕ) (s : State) : Finset (Fin len → Bool) :=
  univ.filter fun x => acc (List.ofFn x) = true ∧
    (s.2.2.2.1 = false ∨ binaryValue s.2.2.2.2 < binaryValue (List.ofFn x))

/-- The words of `k` slots of `len + 1` bits read from the state `s`, counted with the sign of the
final state. -/
def signedSum (acc : List Bool → Bool) (len k : ℕ) (s : State) : ℤ :=
  ∑ w : Fin (k * (len + 1)) → Bool, sign ((listRows k (len + 1) (List.ofFn w)).foldl (step acc) s)

variable {acc : List Bool → Bool} {len : ℕ}

/-- Sums over the words of equal lengths agree. -/
private theorem sum_ofFn_congr {M : Type*} [AddCommMonoid M] (F : List Bool → M) {n n' : ℕ}
    (h : n = n') : ∑ w : Fin n → Bool, F (List.ofFn w) = ∑ w : Fin n' → Bool, F (List.ofFn w) := by
  subst h
  rfl

/-- The signed count of `k + 1` slots, by the first slot. -/
private theorem signedSum_succ (k : ℕ) (s : State) :
    signedSum acc len (k + 1) s = ∑ c : Fin len → Bool,
      (signedSum acc len k (step acc s (false :: List.ofFn c)) +
        signedSum acc len k (step acc s (true :: List.ofFn c))) := by
  unfold signedSum
  rw [sum_ofFn_congr (fun l => sign ((listRows (k + 1) (len + 1) l).foldl (step acc) s))
    (show (k + 1) * (len + 1) = (len + 1) + k * (len + 1) by ring),
    ← (Fin.appendEquiv (len + 1) (k * (len + 1))).sum_comp, Fintype.sum_prod_type]
  simp only [show ∀ (u : Fin (len + 1) → Bool) (v : Fin (k * (len + 1)) → Bool),
    List.ofFn (Fin.appendEquiv (len + 1) (k * (len + 1)) (u, v)) = List.ofFn u ++ List.ofFn v from
      fun u v => List.ofFn_fin_append u v]
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun v _ => ?_ <;>
    rw [listRows_succ_append _ _ (by simp), List.foldl_cons]

/-- In a nonempty finite set of words of length `len`, exactly one has the largest binary value. -/
private theorem card_filter_isGreatest {A : Finset (Fin len → Bool)} (hA : A.Nonempty) :
    (A.filter fun c => ∀ x ∈ A, binaryValue (List.ofFn x) ≤ binaryValue (List.ofFn c)).card =
      1 := by
  obtain ⟨c, hc, hmax⟩ := A.exists_max_image (fun x => binaryValue (List.ofFn x)) hA
  refine card_eq_one.2 ⟨c, ext fun d => ?_⟩
  simp only [mem_filter, mem_singleton]
  refine ⟨fun ⟨hd, hdmax⟩ => List.ofFn_injective (binaryValue_injective_of_length_eq (by simp)
    (le_antisymm (hmax d hd) (hdmax c hc))), fun h => h ▸ ⟨hc, hmax⟩⟩

/-- Listing `c` leaves no accepted certificate above it exactly when `c` is the largest accepted
certificate that may be listed. -/
private theorem above_eq_empty_iff {s : State} {c : Fin len → Bool} (hc : c ∈ above acc len s)
    (o p e : Bool) : above acc len (o, p, e, true, List.ofFn c) = ∅ ↔
      ∀ x ∈ above acc len s, binaryValue (List.ofFn x) ≤ binaryValue (List.ofFn c) := by
  simp only [above, mem_filter, mem_univ, true_and, Bool.true_eq_false, false_or] at hc ⊢
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [mem_filter, mem_univ, true_and, not_and, not_lt]
  refine ⟨fun h x hx => h x hx.1, fun h x hx => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (h x ⟨hx, hc.2.imp_right fun hp => hp.trans hlt⟩) (not_le.2 hlt)

/-- A flagged slot read from a well-formed state before any empty slot. -/
private theorem step_true_cons (par started : Bool) (prev : List Bool) (c : Fin len → Bool) :
    step acc (true, par, false, started, prev) (true :: List.ofFn c) =
      (acc (List.ofFn c) && (!started || decide (binaryValue prev < binaryValue (List.ofFn c))),
        !par, false, true, List.ofFn c) :=
  rfl

/-- A flagged slot holding `c` keeps the state `(true, par, false, started, prev)` well formed
exactly when `c` may be listed after it. -/
private theorem cond_eq_true_iff {par started : Bool} {prev : List Bool} {c : Fin len → Bool} :
    (acc (List.ofFn c) && (!started || decide (binaryValue prev < binaryValue (List.ofFn c)))) =
      true ↔ c ∈ above acc len (true, par, false, started, prev) := by
  cases started <;> simp [above]

/-- **The signed count of the listings.** From a well-formed state, the words of `k` slots,
counted with the sign of the parity of the certificates listed, sum to the sign of the state
when an empty slot has been read or no accepted certificate is above the last one listed, and to
`0` otherwise, provided at most `k` accepted certificates are above it. -/
theorem signedSum_eq (k : ℕ) (s : State)
    (hk : s.1 = true → s.2.2.1 = false → (above acc len s).card ≤ k) :
    signedSum acc len k s = if s.2.2.1 = false ∧ (above acc len s).Nonempty then 0 else sign s := by
  induction k generalizing s with
  | zero =>
    unfold signedSum
    rw [sum_ofFn_congr (fun l => sign ((listRows 0 (len + 1) l).foldl (step acc) s))
      (Nat.zero_mul (len + 1))]
    simp only [listRows, List.range_zero, List.map_nil, List.foldl_nil, Finset.univ_unique,
      Finset.sum_singleton]
    split_ifs with h
    · obtain ⟨hended, hne⟩ := h
      cases hok : s.1
      · simp [sign, hok]
      · exact absurd (card_eq_zero.1 (Nat.le_zero.1 (hk hok hended))) hne.ne_empty
    · rfl
  | succ k ih =>
    rw [signedSum_succ]
    obtain ⟨ok, par, ended, started, prev⟩ := s
    cases ok
    · -- a malformed state stays malformed
      have hfail (slot : List Bool) : (step acc (false, par, ended, started, prev) slot).1 =
          false := by
        unfold step
        split <;> simp
      simp only [sign, Bool.false_eq_true, ite_false, ite_self]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [ih _ (fun h => absurd h (by rw [hfail]; decide)),
        ih _ (fun h => absurd h (by rw [hfail]; decide))]
      simp [sign, hfail]
    -- an empty first slot
    have hsum₀ : ∑ c : Fin len → Bool, signedSum acc len k
        (step acc (true, par, ended, started, prev) (false :: List.ofFn c)) =
          if par then -1 else 1 := by
      have hc (c : Fin len → Bool) : signedSum acc len k
          (step acc (true, par, ended, started, prev) (false :: List.ofFn c)) =
            if (!(List.ofFn c).any (fun b => b)) = true then (if par then -1 else 1) else 0 := by
        have hstep : step acc (true, par, ended, started, prev) (false :: List.ofFn c) =
            (!(List.ofFn c).any (fun b => b), par, true, started, prev) := by
          simp [step]
        rw [hstep, ih _ (fun _ h => by simp at h)]
        simp [sign]
      simp only [hc]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, card_filter_not_any,
        one_smul]
    cases ended
    · -- before any empty slot
      have hcard := hk rfl rfl
      set A := above acc len (true, par, false, started, prev) with hA
      have hc (c : Fin len → Bool) : signedSum acc len k
          (step acc (true, par, false, started, prev) (true :: List.ofFn c)) =
            if c ∈ A ∧ ∀ x ∈ A, binaryValue (List.ofFn x) ≤ binaryValue (List.ofFn c) then
              (if par then 1 else -1) else 0 := by
        rw [step_true_cons]
        by_cases hmem : c ∈ A
        · have hsub : above acc len (true, !par, false, true, List.ofFn c) ⊆ A.erase c := by
            intro x hx
            simp only [hA, above, mem_filter, mem_univ, true_and, Bool.true_eq_false,
              false_or] at hmem hx
            refine mem_erase.2 ⟨fun h => lt_irrefl _ (h ▸ hx.2), ?_⟩
            simp only [hA, above, mem_filter, mem_univ, true_and]
            refine ⟨hx.1, ?_⟩
            rcases hmem.2 with h | h
            · exact Or.inl h
            · exact Or.inr (h.trans hx.2)
          have hle : (above acc len (true, !par, false, true, List.ofFn c)).card ≤ k := by
            have := card_le_card hsub
            rw [card_erase_of_mem hmem] at this
            omega
          rw [(cond_eq_true_iff (par := par)).2 hmem, ih (true, !par, false, true, List.ofFn c)
            (fun _ _ => hle)]
          have hiff := above_eq_empty_iff hmem true (!par) false
          by_cases hmax : ∀ x ∈ A, binaryValue (List.ofFn x) ≤ binaryValue (List.ofFn c)
          · have hempty : ¬ (above acc len (true, !par, false, true, List.ofFn c)).Nonempty :=
              Finset.not_nonempty_iff_eq_empty.2 (hiff.2 hmax)
            rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hempty h.2),
              ite_eq_left_of_eq_true _ _ (eq_true ⟨hmem, hmax⟩)]
            cases par <;> rfl
          · have hne : (above acc len (true, !par, false, true, List.ofFn c)).Nonempty :=
              Finset.nonempty_iff_ne_empty.2 fun h => hmax (hiff.1 h)
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hne⟩),
              ite_eq_right_of_eq_false _ _ (eq_false fun h => hmax h.2)]
        · have hcond : (acc (List.ofFn c) &&
              (!started || decide (binaryValue prev < binaryValue (List.ofFn c)))) = false :=
            Bool.eq_false_iff.2 fun h => hmem ((cond_eq_true_iff (par := par)).1 h)
          rw [hcond, ih _ (fun h => by simp at h)]
          simp [hmem, sign]
      rw [Finset.sum_add_distrib, hsum₀]
      simp only [hc]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        show (univ.filter fun c => c ∈ A ∧ ∀ x ∈ A,
          binaryValue (List.ofFn x) ≤ binaryValue (List.ofFn c)) =
            A.filter fun c => ∀ x ∈ A, binaryValue (List.ofFn x) ≤ binaryValue (List.ofFn c) by
          ext c
          simp]
      by_cases hne : A.Nonempty
      · rw [card_filter_isGreatest hne]
        simp only [hne, and_self, ite_true, one_smul]
        cases par <;> rfl
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
        simp [sign]
    · -- after an empty slot only the words of `false`s are well formed
      have hfail (c : Fin len → Bool) : signedSum acc len k
          (step acc (true, par, true, started, prev) (true :: List.ofFn c)) = 0 := by
        have hstep : (step acc (true, par, true, started, prev) (true :: List.ofFn c)).1 =
            false := by
          simp [step]
        rw [ih _ (fun h => by rw [hstep] at h; exact absurd h (by simp))]
        simp [sign, hstep]
      rw [Finset.sum_add_distrib, hsum₀]
      simp [hfail, sign]

/-! ### The verifiers -/

variable {α : Type}

/-- The verifier counting the listings of parity `b`: on an instance `a`, the certificate, read as
`q` slots of `len + 1` bits, where `len = p (enc a).length`, is a well-formed increasing listing of
certificates of length `len` accepted by `V` with a number of certificates of parity `b`. -/
def verifier (enc : α ↪ List Bool) (p q : Polynomial ℕ) (V : α × List Bool → Bool) (b : Bool)
    (x : α × List Bool) : Bool :=
  accepts b ((listRows (q.eval (enc x.1).length) (p.eval (enc x.1).length + 1) x.2).foldl
    (step fun c => V (x.1, c)) init)

/-- The encoding of the states of a scan. -/
private abbrev encState : State ↪ List Bool :=
  encPair encBool (encPair encBool (encPair encBool (encPair encBool encBits)))

/-- A slot grows the encoded state by at most its length. -/
private theorem length_encState_step (acc : List Bool → Bool) (s : State) (slot : List Bool) :
    (encState (step acc s slot)).length ≤ (encState s).length + slot.length := by
  unfold step
  split <;> simp only [length_encPair, encBool_apply, List.length_singleton, encBits_apply,
    List.length_tail] <;> omega

/-- **The verifiers are polynomial-time.** -/
theorem computableInPolyTime_verifier {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (p q : Polynomial ℕ)
    (b : Bool) :
    ComputableInPolyTime (verifier enc p q V b) (encPair enc encBits) encBool := by
  have hP : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length + 1)
      (encPair enc encBits) encUnary := by fun_prop
  have hQ : ComputableInPolyTime (fun x : α × List Bool => q.eval (enc x.1).length)
      (encPair enc encBits) encUnary := by fun_prop
  have hlt : ComputableInPolyTime
      (fun x : (α × State) × List Bool => decide (binaryValue x.1.2.2.2.2.2 < binaryValue x.2.tail))
      (encPair (encPair enc encState) encBits) encBool :=
    ComputableInPolyTime.binary_lt' (by fun_prop) (by fun_prop)
  have hstep : ComputableInPolyTime
      (fun x : (α × State) × List Bool => step (fun c => V (x.1.1, c)) x.1.2 x.2)
      (encPair (encPair enc encState) encBits) encState := by
    unfold step
    fun_prop
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (par := fun x : α × List Bool => x.1) (encP := enc)
    (list := fun x => listRows (q.eval (enc x.1).length) (p.eval (enc x.1).length + 1) x.2)
    (init := fun _ => init) (step := fun a s slot => step (fun c => V (a, c)) s slot)
    (ComputableInPolyTime.fst enc encBits) (by fun_prop)
    (ComputableInPolyTime.const init) hstep hP.polyBounded
    (fun x s slot hslot => by
      have := length_encState_step (fun c => V (x.1, c)) s slot
      rw [length_of_mem_listRows hslot] at this
      exact this)
  have hacc : ComputableInPolyTime (accepts b) encState encBool := by
    unfold accepts
    fun_prop
  exact hacc.comp hfold

end SortedSubsets

variable {α : Type} {enc : α ↪ List Bool}

open SortedSubsets in
/-- **`FewP ⊆ SPP`** [Köbler, Schöning, Toda and Torán][KoeblerSchoeningTodaToran1992],
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]. For a problem in `FewP` whose instances have
at most `q` accepted certificates, the numbers `E` and `O` of increasing listings, in `q` slots, of
sets of accepted certificates of even and of odd size are in `#P`, and `1 + O - E`, in `GapP`, is
`1` on members and `0` on the other instances. -/
theorem FewP_subset_SPP : FewP enc ⊆ SPP enc := by
  rintro A ⟨f, ⟨p, V, hV, hf⟩, q, hq, hA⟩
  set E : α → ℕ := fun a =>
    acceptCount (verifier enc p q V false) a ((q * (p + 1)).eval (enc a).length) with hE_def
  set O : α → ℕ := fun a =>
    acceptCount (verifier enc p q V true) a ((q * (p + 1)).eval (enc a).length) with hO_def
  have hE : E ∈ SharpP enc :=
    ⟨q * (p + 1), _, (computableInPolyTime_verifier hV p q false), fun _ => rfl⟩
  have hO : O ∈ SharpP enc :=
    ⟨q * (p + 1), _, (computableInPolyTime_verifier hV p q true), fun _ => rfl⟩
  have hdiff (a : α) : (E a : ℤ) - O a = if 0 < f a then 0 else 1 := by
    have hsum : (E a : ℤ) - O a =
        signedSum (fun c => V (a, c)) (p.eval (enc a).length) (q.eval (enc a).length) init := by
      have hlen : (q * (p + 1)).eval (enc a).length =
          q.eval (enc a).length * (p.eval (enc a).length + 1) := by
        simp
      simp only [hE_def, hO_def]
      rw [hlen]
      simp only [acceptCount, signedSum, Finset.card_filter]
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      exact (sign_eq_sub _).symm
    have hcard : (above (fun c => V (a, c)) (p.eval (enc a).length) init).card = f a := by
      rw [hf a]
      simp [above, init, acceptCount]
    rw [hsum, signedSum_eq _ _ (fun _ _ => hcard ▸ hq a)]
    simp only [← Finset.card_pos, hcard]
    simp [init, sign]
  refine ⟨fun a => ((O a + 1 : ℕ) : ℤ) - E a, ⟨_, SharpP.add_one_mem hO, _, hE, fun _ => rfl⟩,
    fun a => ?_, fun a => ?_⟩
  · have := hdiff a
    split_ifs at this <;> push_cast <;> omega
  · have := hdiff a
    rw [hA a]
    split_ifs at this with h <;> push_cast <;> simp only [h, true_iff, false_iff] <;> omega


end Cslib.Complexity
