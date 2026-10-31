/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Sparse
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Data.Set.Finite.List
import Mathlib.NumberTheory.Chebyshev

/-!
# Tally problems

A *tally* language consists of words over a one-letter alphabet: here, words all of whose letters
are `true` (`Cslib.Complexity.TALLY`). The words `true ^ n` are the unary encodings of the natural
numbers, so a conjunctive reduction to a set `A` of natural numbers written in unary is one to the
tally language `encUnary '' A` (`Cslib.Complexity.PolyTimeCTTReducible.image_encUnary`).

**Sparse problems reduce conjunctively to tally problems**
(`Cslib.Complexity.exists_polyTimeCTTReducible_encUnary_of_mem_SPARSE`), a theorem of Buhrman,
Longpré and Spaan, cited by Arvind, Köbler and Mundhenk [Arvind, Köbler and Mundhenk, proof of
Lemma 3.2][ArvindKoblerMundhenk1992]. The reduction asks, for a word `u` of length `n` and each
`m < M`, whether some member of the sparse problem of length `n` has the same residue as `u`
modulo `m + 1` (`Cslib.Complexity.Tally.fingerprint`); members of the sparse problem pass every
test. For a word `u` outside it, let `Y` be the at most `s` members of length `n`. If every
modulus `m + 1 ≤ M` were matched by some `y ∈ Y`, it would divide `|u - y|`, read as binary
numbers, so the least common multiple of `1, …, M` would divide the nonzero product of the
`|u - y|`, which is at most `2 ^ (n s)`. Since that least common multiple is at least `2 ^ M`
for `M ≥ 7` (`Chebyshev.two_pow_le_lcmUpto`), `M = n s + 7` moduli suffice
(`Cslib.Complexity.Tally.exists_fingerprint_notMem`). This route through `Nat.lcmUpto` is the
library's own; it needs no bound on the number of primes.

Conjunctive reductions to tally problems are closed under intersection, by asking both batches of
queries tagged by their reduction, and under union, by asking for every pair of queries whether one
of them is in its target; pairs of unary numbers are unary numbers again (`Nat.pair`). Sparse
targets do not allow the second construction, which is why the tally step is needed.

## Main definitions

* `Cslib.Complexity.TALLY`: the tally languages.
* `Cslib.Complexity.Tally.residue`, `Cslib.Complexity.Tally.fingerprint`,
  `Cslib.Complexity.Tally.fingerprints`: the tests of the reduction and the tally set they ask.

## Main results

* `Cslib.Complexity.TALLY_subset_SPARSE`, `Cslib.Complexity.image_encUnary_mem_TALLY`: tally
  languages are sparse, and sets of natural numbers written in unary are tally.
* `Cslib.Complexity.Tally.exists_fingerprint_notMem`: few moduli separate a word from the members
  of a sparse problem.
* `Cslib.Complexity.exists_polyTimeCTTReducible_encUnary_of_mem_SPARSE`,
  `Cslib.Complexity.exists_mem_TALLY_polyTimeCTTReducible_of_mem_SPARSE`: `SPARSE ⊆ R_ctt(TALLY)`.
* `Cslib.Complexity.exists_polyTimeCTTReducible_encUnary_of_mem_P`,
  `Cslib.Complexity.PolyTimeCTTReducible.exists_encUnary_inter`,
  `Cslib.Complexity.PolyTimeCTTReducible.exists_encUnary_union`: problems in `P` reduce
  conjunctively to tally problems, and such reductions are closed under intersection and union
  [Arvind, Köbler and Mundhenk, proof of Lemma 3.2][ArvindKoblerMundhenk1992]. With
  `SPARSE ⊆ R_ctt(TALLY)` this makes the problems with conjunctive reductions to sparse problems a
  set ring, as their Lemma 3.2 states.

## References

* [V. Arvind, J. Köbler, M. Mundhenk, *On Bounded Truth-Table, Conjunctive, and Randomized
  Reductions to Sparse Sets*][ArvindKoblerMundhenk1992]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-! ### Tally languages -/

/-- The tally languages: languages of words all of whose letters are `true`. -/
def TALLY : Set (Set (List Bool)) :=
  {T | ∀ w ∈ T, ∀ b ∈ w, b = true}

theorem mem_TALLY {T : Set (List Bool)} : T ∈ TALLY ↔ ∀ w ∈ T, ∀ b ∈ w, b = true :=
  Iff.rfl

/-- Tally languages are sparse. -/
theorem TALLY_subset_SPARSE : TALLY ⊆ SPARSE encBits :=
  fun _ hT => mem_SPARSE_of_unary hT

/-- The unary encodings of a set of natural numbers form a tally language. -/
theorem image_encUnary_mem_TALLY (A : Set ℕ) : encUnary '' A ∈ TALLY := by
  rintro _ ⟨n, -, rfl⟩ b hb
  rw [encUnary_apply] at hb
  exact List.eq_of_mem_replicate hb

/-- A conjunctive reduction to a set of natural numbers written in unary is a conjunctive reduction
to the tally language of their unary encodings. -/
theorem PolyTimeCTTReducible.image_encUnary {α : Type} {encA : α ↪ List Bool} {L : Set α}
    {A : Set ℕ} (h : PolyTimeCTTReducible encA encUnary L A) :
    PolyTimeCTTReducible encA encBits L (encUnary '' A) := by
  obtain ⟨r, q, hr, hq, hL⟩ := h
  refine ⟨r, fun x => encUnary (q x), hr, ComputableInPolyTime.encoding_comp hq, fun a => ?_⟩
  simp only [hL a, encUnary.injective.mem_set_image]

/-! ### Fingerprints modulo small numbers -/

namespace Tally

open Cslib.BitString

/-- The residue of the binary value of the word `u`, most significant bit first, modulo `m + 1`,
computed digit by digit. -/
def residue (m : ℕ) (u : List Bool) : ℕ :=
  u.foldl (fun r b => (2 * r + b.toNat) % (m + 1)) 0

/-- The `m`-th fingerprint of the word `u`: its length, `m`, and its residue modulo `m + 1`. -/
def fingerprint (u : List Bool) (m : ℕ) : ℕ :=
  Nat.pair u.length (Nat.pair m (residue m u))

/-- The fingerprints of the members of `S`. -/
def fingerprints (S : Set (List Bool)) : Set ℕ :=
  {c | ∃ u ∈ S, ∃ m, fingerprint u m = c}

private theorem foldl_residue (m : ℕ) (u : List Bool) (r v : ℕ) (hrv : r = v % (m + 1)) :
    u.foldl (fun r b => (2 * r + b.toNat) % (m + 1)) r =
      u.foldl (fun v b => 2 * v + b.toNat) v % (m + 1) := by
  induction u generalizing r v with
  | nil => simpa using hrv
  | cons b u ih =>
    simp only [List.foldl_cons]
    refine ih _ _ ?_
    rw [hrv, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- The residue is that of the binary value. -/
theorem residue_eq (m : ℕ) (u : List Bool) : residue m u = binaryValue u % (m + 1) :=
  foldl_residue m u 0 0 (by simp)

/-- **Few moduli separate a word from the members of a sparse problem.** If at most `s` members
of `S` have the length of `u`, `u` is not in `S` and `M ≥ |u| s + 7`, then some fingerprint
`fingerprint u m` with `m < M` is not a fingerprint of a member of `S`. -/
theorem exists_fingerprint_notMem {S : Set (List Bool)} {u : List Bool} {s M : ℕ}
    (hs : ∀ T : Finset (List Bool), (∀ w ∈ T, w ∈ S ∧ w.length = u.length) → T.card ≤ s)
    (hM : u.length * s + 7 ≤ M) (hu : u ∉ S) : ∃ m < M, fingerprint u m ∉ fingerprints S := by
  classical
  by_contra hall
  push Not at hall
  set n := u.length
  have hfin : {w ∈ S | w.length = n}.Finite :=
    (List.finite_length_eq Bool n).subset fun w hw => hw.2
  set Y := hfin.toFinset
  have hmemY : ∀ y, y ∈ Y ↔ y ∈ S ∧ y.length = n := fun y => by simp [Y]
  have hY : Y.card ≤ s := hs Y fun w hw => (hmemY w).1 hw
  set D := ∏ y ∈ Y, ((binaryValue y : ℤ) - binaryValue u).natAbs
  /- Every modulus `m + 1 ≤ M` divides the distance from `u` to some member of length `n`. -/
  have hdvd : ∀ m < M, m + 1 ∣ D := by
    intro m hm
    obtain ⟨y, hyS, m', hfp⟩ := hall m hm
    simp only [fingerprint, Nat.pair_eq_pair] at hfp
    obtain ⟨hlen, rfl, hres⟩ := hfp
    have hyY : y ∈ Y := (hmemY y).2 ⟨hyS, hlen⟩
    rw [residue_eq, residue_eq] at hres
    have hmod : ((m' + 1 : ℕ) : ℤ) ∣ (binaryValue y : ℤ) - binaryValue u :=
      (Nat.ModEq.dvd hres.symm)
    exact (Int.natCast_dvd.1 hmod).trans (Finset.dvd_prod_of_mem _ hyY)
  have hDpos : 0 < D := by
    refine Finset.prod_pos fun y hy => Int.natAbs_pos.2 (sub_ne_zero.2 fun h => hu ?_)
    obtain ⟨hyS, hylen⟩ := (hmemY y).1 hy
    rwa [← binaryValue_injective_of_length_eq hylen (by exact_mod_cast h)]
  have hDle : D ≤ 2 ^ (n * s) := by
    calc D ≤ ∏ _y ∈ Y, 2 ^ n := by
          refine Finset.prod_le_prod fun y hy => ?_
          have hy' : binaryValue y < 2 ^ n := ((hmemY y).1 hy).2 ▸ binaryValue_lt_two_pow y
          have hu' : binaryValue u < 2 ^ n := binaryValue_lt_two_pow u
          omega
      _ = 2 ^ (n * Y.card) := by rw [Finset.prod_const, ← pow_mul]
      _ ≤ 2 ^ (n * s) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hY)
  have hlcm : Nat.lcmUpto M ∣ D := Finset.lcm_dvd fun m hm => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hm
    simpa [Nat.sub_add_cancel h1] using hdvd (m - 1) (by omega)
  have h2M := (Chebyshev.two_pow_le_lcmUpto (by omega : 7 ≤ M)).trans
    ((Nat.le_of_dvd hDpos hlcm).trans hDle)
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2M
  omega

end Tally

/-! ### Sparse problems reduce conjunctively to tally problems -/

open ComputableInPolyTime

/-- The natural-number pairing function on unary naturals is polynomial-time. -/
private theorem computableInPolyTime_unary_pair :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2) (encPair encUnary encUnary)
      encUnary := by
  have hleft : ComputableInPolyTime (fun p : ℕ × ℕ => p.2 * p.2 + p.1)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hright : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.1 + p.1 + p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  simpa [Nat.pair] using unary_lt.ite hleft hright

/-- The residue modulo a computed unary `m + 1` of a computed word is polynomial-time. -/
private theorem computableInPolyTime_residue {γ : Type} {encIn : γ ↪ List Bool} {m : γ → ℕ}
    {u : γ → List Bool} (hm : ComputableInPolyTime m encIn encUnary)
    (hu : ComputableInPolyTime u encIn encBits) :
    ComputableInPolyTime (fun x => Tally.residue (m x) (u x)) encIn encUnary := by
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × Bool => (2 * p.1.2 + p.2.toNat) % (p.1.1 + 1))
      (encPair (encPair encUnary encUnary) encBool) encUnary := by
    have hbool : ComputableInPolyTime Bool.toNat encBool encUnary := of_finite _
    have hnum : ComputableInPolyTime (fun p : (ℕ × ℕ) × Bool => 2 * p.1.2 + p.2.toNat)
        (encPair (encPair encUnary encUnary) encBool) encUnary := by fun_prop
    have hden : ComputableInPolyTime (fun p : (ℕ × ℕ) × Bool => p.1.1 + 1)
        (encPair (encPair encUnary encUnary) encBool) encUnary := by fun_prop
    exact unary_mod.comp (hnum.prod hden)
  exact foldlWith_of_bounded_growth (encA := encBool) (encL := encBits) (encP := encUnary)
    (encB := encUnary) (step := fun m r b => (2 * r + b.toNat) % (m + 1)) hm hu (const 0) hstep
    (growth := fun x => m x + 1) (hm.polyBounded.add (.const 1)) fun x r b _ => by
      have : (2 * r + b.toNat) % (m x + 1) < m x + 1 := Nat.mod_lt _ (by omega)
      simp only [encUnary_apply, List.length_replicate]
      omega

/-- **Sparse problems reduce conjunctively to tally problems** (Buhrman, Longpré and Spaan; cited
in [Arvind, Köbler and Mundhenk, proof of Lemma 3.2][ArvindKoblerMundhenk1992]): a sparse problem
has a polynomial-time conjunctive reduction to a set of natural numbers written in unary. The
queries are the fingerprints of the encoding of an instance with `M = n s + 7` moduli, where `n` is
its length and `s` bounds the members of length at most `n`; the target is the set of fingerprints
of the encodings of members. -/
theorem exists_polyTimeCTTReducible_encUnary_of_mem_SPARSE {β : Type} {encB : β ↪ List Bool}
    {S : Set β} (hS : S ∈ SPARSE encB) : ∃ A : Set ℕ, PolyTimeCTTReducible encB encUnary S A := by
  obtain ⟨C, E, hCE⟩ := exists_card_le_of_mem_SPARSE (image_mem_SPARSE_encBits_iff.mpr hS)
  let P : Polynomial ℕ :=
    Polynomial.X * (Polynomial.C C * (Polynomial.X + 1) ^ E) + 7
  have hP (n : ℕ) : P.eval n = n * (C * (n + 1) ^ E) + 7 := by simp [P]
  have hencB : ComputableInPolyTime (fun b => encB b) encB encBits :=
    of_eq (encIn := encB) (encOut := encBits) (f := fun b => encB b) fun _ => rfl
  refine ⟨Tally.fingerprints (encB '' S), fun b => P.eval (encB b).length,
    fun p => Tally.fingerprint (encB p.1) p.2, (unary_eval P).comp (encoding_length encB), ?_,
    fun b => ⟨fun hb i _ => ⟨encB b, ⟨b, hb, rfl⟩, i, rfl⟩, fun h => ?_⟩⟩
  · have hlen : ComputableInPolyTime (fun p : β × ℕ => (encB p.1).length) (encPair encB encUnary)
        encUnary := (encoding_length encB).comp (fst _ _)
    have hres : ComputableInPolyTime (fun p : β × ℕ => Tally.residue p.2 (encB p.1))
        (encPair encB encUnary) encUnary :=
      computableInPolyTime_residue (snd _ _) (hencB.comp (fst _ _))
    exact computableInPolyTime_unary_pair.comp
      (hlen.prod (computableInPolyTime_unary_pair.comp ((snd _ _).prod hres)))
  · by_contra hb
    have hu : encB b ∉ encB '' S := fun hmem => hb (encB.injective.mem_set_image.1 hmem)
    obtain ⟨m, hm, hnot⟩ := Tally.exists_fingerprint_notMem
      (s := C * ((encB b).length + 1) ^ E)
      (fun T hT => hCE _ T fun w hw => ⟨(hT w hw).1, by simp [(hT w hw).2]⟩)
      (by rw [← hP]) hu
    exact hnot (h m (by simpa using hm))

/-- **`SPARSE ⊆ R_ctt(TALLY)`:** a sparse problem has a polynomial-time conjunctive reduction to a
tally language. -/
theorem exists_mem_TALLY_polyTimeCTTReducible_of_mem_SPARSE {β : Type} {encB : β ↪ List Bool}
    {S : Set β} (hS : S ∈ SPARSE encB) :
    ∃ T ∈ TALLY, PolyTimeCTTReducible encB encBits S T :=
  let ⟨A, hA⟩ := exists_polyTimeCTTReducible_encUnary_of_mem_SPARSE hS
  ⟨encUnary '' A, image_encUnary_mem_TALLY A, hA.image_encUnary⟩

/-! ### Closure of conjunctive reductions to tally problems -/

section Closure

variable {α : Type} {encA : α ↪ List Bool} {L L₁ L₂ : Set α} {A₁ A₂ : Set ℕ}

/-- A problem in `P` reduces conjunctively to a tally problem: no query for members and an
unanswerable one otherwise. -/
theorem exists_polyTimeCTTReducible_encUnary_of_mem_P (h : L ∈ P encA) :
    ∃ A : Set ℕ, PolyTimeCTTReducible encA encUnary L A := by
  obtain ⟨f, hf, hL⟩ := mem_P.mp h
  refine ⟨∅, fun a => if f a then 0 else 1, fun _ => 0, ?_, const _, fun a => ?_⟩
  · exact ite' hf (const 0) (const 1)
  · rw [hL a]
    rcases hfa : f a <;> simp [hfa]

/-- **Conjunctive reductions to tally problems are closed under intersection**: ask the queries of
both reductions, tagged by the reduction they come from. -/
theorem PolyTimeCTTReducible.exists_encUnary_inter (h₁ : PolyTimeCTTReducible encA encUnary L₁ A₁)
    (h₂ : PolyTimeCTTReducible encA encUnary L₂ A₂) :
    ∃ A : Set ℕ, PolyTimeCTTReducible encA encUnary (L₁ ∩ L₂) A := by
  obtain ⟨r₁, q₁, hr₁, hq₁, hL₁⟩ := h₁
  obtain ⟨r₂, q₂, hr₂, hq₂, hL₂⟩ := h₂
  refine ⟨{c | ((Nat.unpair c).1 = 0 ∧ (Nat.unpair c).2 ∈ A₁) ∨
      ((Nat.unpair c).1 = 1 ∧ (Nat.unpair c).2 ∈ A₂)}, fun a => r₁ a + r₂ a,
    fun p => if p.2 < r₁ p.1 then Nat.pair 0 (q₁ p) else Nat.pair 1 (q₂ (p.1, p.2 - r₁ p.1)),
    by fun_prop, ?_, fun a => ?_⟩
  · have hfst : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair encA encUnary) encA :=
      fst _ _
    have hsnd : ComputableInPolyTime (fun p : α × ℕ => p.2) (encPair encA encUnary) encUnary :=
      snd _ _
    have hq₂' : ComputableInPolyTime (fun p : α × ℕ => q₂ (p.1, p.2 - r₁ p.1))
        (encPair encA encUnary) encUnary := hq₂.comp (hfst.prod (unary_sub' hsnd (hr₁.comp hfst)))
    have h := ite' (unary_lt' hsnd (hr₁.comp hfst))
      (computableInPolyTime_unary_pair.comp ((const 0).prod hq₁))
      (computableInPolyTime_unary_pair.comp ((const 1).prod hq₂'))
    simpa only [Function.comp_def, decide_eq_true_eq] using h
  · simp only [Set.mem_inter_iff, hL₁ a, hL₂ a]
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases hir : i < r₁ a
      · simp [hir, h₁ i hir]
      · simp [hir, h₂ (i - r₁ a) (by omega)]
    · intro h
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · simpa [hi] using h i (by omega)
      · simpa [show ¬ r₁ a + j < r₁ a by omega] using h (r₁ a + j) (by omega)

/-- **Conjunctive reductions to tally problems are closed under union**: ask, for every pair of a
query of each reduction, whether one of the two is in its target. -/
theorem PolyTimeCTTReducible.exists_encUnary_union (h₁ : PolyTimeCTTReducible encA encUnary L₁ A₁)
    (h₂ : PolyTimeCTTReducible encA encUnary L₂ A₂) :
    ∃ A : Set ℕ, PolyTimeCTTReducible encA encUnary (L₁ ∪ L₂) A := by
  obtain ⟨r₁, q₁, hr₁, hq₁, hL₁⟩ := h₁
  obtain ⟨r₂, q₂, hr₂, hq₂, hL₂⟩ := h₂
  refine ⟨{c | (Nat.unpair c).1 ∈ A₁ ∨ (Nat.unpair c).2 ∈ A₂}, fun a => r₁ a * r₂ a,
    fun p => Nat.pair (q₁ (p.1, p.2 / r₂ p.1)) (q₂ (p.1, p.2 % r₂ p.1)), by fun_prop, ?_,
    fun a => ?_⟩
  · have hfst : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair encA encUnary) encA :=
      fst _ _
    have hdiv : ComputableInPolyTime (fun p : α × ℕ => p.2 / r₂ p.1) (encPair encA encUnary)
        encUnary := unary_div.comp ((snd _ _).prod (hr₂.comp hfst))
    have hmod : ComputableInPolyTime (fun p : α × ℕ => p.2 % r₂ p.1) (encPair encA encUnary)
        encUnary := unary_mod.comp ((snd _ _).prod (hr₂.comp hfst))
    exact computableInPolyTime_unary_pair.comp
      ((hq₁.comp (hfst.prod hdiv)).prod (hq₂.comp (hfst.prod hmod)))
  · simp only [Set.mem_union, hL₁ a, hL₂ a, Set.mem_ofPred_eq, Nat.unpair_pair]
    constructor
    · intro h i hi
      have hr₂ : 0 < r₂ a := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
      rcases h with h | h
      · exact .inl (h _ (Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hi)))
      · exact .inr (h _ (Nat.mod_lt _ hr₂))
    · intro h
      by_contra hne
      push Not at hne
      obtain ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩ := hne
      have hr₂ : 0 < r₂ a := by omega
      have hdiv : (j + r₂ a * i) / r₂ a = i := by
        rw [Nat.add_mul_div_left _ _ hr₂, Nat.div_eq_of_lt hj, Nat.zero_add]
      have hmod : (j + r₂ a * i) % r₂ a = j := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      have hidx : j + r₂ a * i < r₁ a * r₂ a := by nlinarith
      rcases h _ hidx with h | h
      · exact hi' (hdiv ▸ h)
      · exact hj' (hmod ▸ h)

end Closure

end Cslib.Complexity
