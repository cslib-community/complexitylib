/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Complexity.Classes.NP.GuessVerify
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Clock
import CslibFrontier.Computability.Probabilistic.Sampling.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Padding

If `P = NP`, then `EXP = NEXP` and `E = NE` [Arora and Barak, Section 2.6][AroraBarak09]:
collapses of polynomial classes translate upwards, by the padding argument of Book
[Book][Book1974]. The proof pads instances until a slow nondeterministic machine is fast in the
length of the padded instance, decides the padded problem deterministically, and pays for writing
the padding.

## Timed reductions

The general timed-reduction API lives in
`CslibFrontier.Computability.Complexity.Classes.Time`. In particular,
`Cslib.Complexity.preimage_mem_DTIME` computes a reduction and then tidily decides its output;
the padding arguments below apply this API to their padded instances. The unconditional
deterministic exponential-padding lemma
`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad` lives in
`CslibFrontier.Computability.Complexity.Classes.EXP`.

## The padded problem

A nondeterministic machine `ntm` decides `A` within time `t`. The padded problem
`Turing.MultiTapeNTM.padded ntm c` consists of the bit words `x` such that some `c * |x|` coins
encode an accepting computation of `ntm` on the word `unframe x` framed at the start of `x`, read
as coins of the choice table (`Turing.MultiTapeNTM.checkChoices`). The general certificate
characterization `Turing.MultiTapeNTM.DecidesInTime.mem_iff_exists_checkChoices` lives with
`checkChoices` in `CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic`. The padded
problem is in `NP` with respect to `encBits` by definition: checking the coins is polynomial-time.
If every computation path on
`enc a` with at least `t a` steps has halted, and `c * |x|` is at least `M * t a` for the number
`M` of actions, the padded word `x = frame (enc a) ++ u` is in the padded problem exactly when
`a ∈ A` (`Turing.MultiTapeNTM.DecidesInTime.frame_append_mem_padded_iff`).

## The translation lemma

If `NP ⊆ P` for problems on bit words, and `t n` is computable in unary from any word of length `n`
within time `O(T n)`, then `NTIME t ⊆ ⋃ d, DTIME ((n + T n + 1) ^ d)`
(`Cslib.Complexity.NTIME_subset_iUnion_DTIME_of_NP_subset_P`): the padded problem with padding
`t n` is decided in time polynomial in `n + t n`. For `t n = 2 ^ f n` with `f` computable in unary
in polynomial time and `n ≤ f n`, `2 ^ f n` is computed in unary by doubling, within time
`O((f n + 1) * 2 ^ f n)` using the quantitative machine API
(`Turing.MultiTapeTM.ComputableInO.unary_two_pow`), and
`NTIME (2 ^ f n) ⊆ ⋃ d, DTIME (2 ^ (d * f n))`
(`Cslib.Complexity.NTIME_two_pow_subset_iUnion_DTIME_of_NP_subset_P`). With `f n = (k + 1) * n`
and `f n = n ^ (k + 1)` this gives `NE ⊆ E` and `NEXP ⊆ EXP`.

The hypothesis is `NP ⊆ P` for problems on bit words, under `encBits`; the conclusions hold for
problems on any type, under any encoding.

The proof only uses the `P` decider of a padded problem on padded instances. So the translation
lemma holds under the weaker hypothesis that every problem in `NP` agrees with some problem in `P`
on the padded words `frame u ++ 1^{t |u|}`
(`Cslib.Complexity.NTIME_subset_iUnion_DTIME_of_agree_padded`). For exponential padding this is
`Cslib.Complexity.ExpPaddedNPEasy`, the hypothesis that `NP` is easy on exponentially padded
instances. It gives `NE ⊆ E` and `NEXP ⊆ EXP`, and it also follows from easiness of `NP` on
average (`CslibFrontier.Computability.Complexity.Classes.AverageCase.WorstCase`).

The unconditional pullback lemmas `Cslib.Complexity.preimage_mem_NTIME_of_mem_NP` and
`Cslib.Complexity.preimage_pad_mem_NEXP` compose a timed deterministic map with an `NP` verifier;
exponential padding yields an `NEXP` decider without a collapse hypothesis.

## Main definitions

* `Turing.MultiTapeNTM.checkPadded`: the verifier of padded instances.
* `Turing.MultiTapeNTM.padded`: the padded problem of a nondeterministic machine.
* `Cslib.Complexity.ExpPaddedNPEasy`: every problem in `NP` agrees with a problem in `P` on
  exponentially padded instances.

## Main results

* `Cslib.Complexity.preimage_mem_NTIME_of_mem_NP`, `Cslib.Complexity.preimage_pad_mem_NEXP`,
  `Cslib.Complexity.preimage_append_two_pow_mem_NEXP`:
  unconditional timed pullback of `NP`, including exponentially padded inputs.
* `Cslib.Complexity.preimage_pad_prod_id_mem_EXP`,
  `Cslib.Complexity.preimage_pad_prod_two_pow_mem_EXP`:
  unconditional exponential-padding pullback of `P` on paired inputs into `EXP`.
* `Turing.MultiTapeNTM.padded_mem_NP`,
  `Turing.MultiTapeNTM.DecidesInTime.frame_append_mem_padded_iff`: the padded problem is in `NP`,
  and decides the original problem on padded instances.
* `Cslib.Complexity.NTIME_subset_iUnion_DTIME_of_NP_subset_P`: the translation lemma;
  `Cslib.Complexity.NTIME_subset_iUnion_DTIME_of_agree_padded`: the same from agreement on padded
  instances.
* `Cslib.Complexity.NE_subset_E_of_expPaddedNPEasy`,
  `Cslib.Complexity.NEXP_subset_EXP_of_expPaddedNPEasy`: if `NP` is easy on exponentially padded
  instances, then `NE ⊆ E` and `NEXP ⊆ EXP`.
* `Cslib.Complexity.NEXP_subset_EXP_of_NP_subset_P`, `Cslib.Complexity.EXP_eq_NEXP_of_P_eq_NP`:
  if `P = NP`, then `EXP = NEXP`.
* `Cslib.Complexity.NE_subset_E_of_NP_subset_P`, `Cslib.Complexity.E_eq_NE_of_P_eq_NP`: if
  `P = NP`, then `E = NE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. V. Book, *Comparing complexity classes*][Book1974]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] {α : Type} {enc : α ↪ List Bool}

/-- **The verifier of padded instances.** It accepts when the certificate, read as coins of the
choice table, replays a computation path of `ntm` on the word framed at the start of the instance
that halts with output `[true]`; the rest of the instance is padding. -/
noncomputable def checkPadded (ntm : MultiTapeNTM k Bool State) (x : List Bool × List Bool) :
    Bool :=
  ntm.checkChoices encBits (unframe x.1, x.2)

/-- Checking a padded instance is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_checkPadded (ntm : MultiTapeNTM k Bool State) :
    ComputableInPolyTime ntm.checkPadded (encPair encBits encBits) encBool := by
  exact ntm.computableInPolyTime_checkChoices.comp
    ((ComputableInPolyTime.unframe.comp (.fst encBits encBits)).prod (.snd encBits encBits))

/-- **The padded problem** of `ntm`: the bit words `x` such that some `c * |x|` coins encode an
accepting computation of `ntm` on the word `unframe x` framed at the start of `x`. -/
def padded (ntm : MultiTapeNTM k Bool State) (c : ℕ) : Set (List Bool) :=
  {x | ∃ w : List Bool, w.length = c * x.length ∧ ntm.checkPadded (x, w) = true}

/-- The padded problem is in `NP`, with certificates of length `c * |x|`. -/
theorem padded_mem_NP (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ntm.padded c ∈ Cslib.Complexity.NP encBits :=
  ⟨Polynomial.C c * Polynomial.X, ntm.checkPadded,
    (ntm.computableInPolyTime_checkPadded),
    fun x => by simp [padded]⟩

/-- **Padded instances.** If `ntm` decides `A` within `t`, then the padded word
`frame (enc a) ++ u` is in the padded problem of `ntm` with `c` coins per bit exactly when `a ∈ A`,
as soon as `c * |frame (enc a) ++ u|` is at least `M * t a`, for the number `M` of actions. -/
theorem DecidesInTime.frame_append_mem_padded_iff {ntm : MultiTapeNTM k Bool State} {A : Set α}
    {t : α → ℕ} (h : ntm.DecidesInTime enc A t) {a : α} {c : ℕ} {u : List Bool}
    (hc : Nat.card (Turing.Action k Bool State) * t a ≤ c * (frame (enc a) ++ u).length) :
    frame (enc a) ++ u ∈ ntm.padded c ↔ a ∈ A := by
  rw [h.mem_iff_exists_checkChoices hc]
  simp only [padded, checkPadded, unframe_frame_append, Set.mem_ofPred_eq]
  rfl

end Turing.MultiTapeNTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}

/-! ### The translation lemma -/

/-- **`NP` is easy on exponentially padded instances**: every problem `B ∈ NP` agrees with some
problem `B' ∈ P` on the words `frame u ++ 1^m` with `2 ^ |u| ≤ m`. This holds if `NP ⊆ P`
(`Cslib.Complexity.expPaddedNPEasy_of_NP_subset_P`), and also if every distributional `NP` problem
with a polynomial-time computable ensemble has a polynomial-time heuristic scheme
(`Cslib.Complexity.expPaddedNPEasy_of_DistNP_subset_HeurP`). It suffices for the padding
arguments below. -/
def ExpPaddedNPEasy : Prop :=
  ∀ B ∈ NP encBits, ∃ B' ∈ P encBits, ∀ (u : List Bool) (m : ℕ), 2 ^ u.length ≤ m →
    (frame u ++ List.replicate m true ∈ B' ↔ frame u ++ List.replicate m true ∈ B)

/-- If `NP ⊆ P`, then `NP` is easy on exponentially padded instances. -/
theorem expPaddedNPEasy_of_NP_subset_P (hNP : NP encBits ⊆ P encBits) : ExpPaddedNPEasy :=
  fun B hB => ⟨B, hNP hB, fun _ _ _ => Iff.rfl⟩

/-! ### Writing padded instances -/

/-- Framing an instance and appending `t |x|` ones costs linear time plus the cost of writing
`t |x|` in unary. -/
private theorem computableInO_frame_append_replicate {t : ℕ → ℕ} {T S : List Bool → ℕ}
    (hpad : ComputableInO (fun x : List Bool => t x.length) encBits encUnary T S) :
    ComputableInO (fun a => frame (enc a) ++ List.replicate (t (enc a).length) true) enc encBits
      (fun a => (enc a).length + T (enc a)) fun a => (enc a).length + S (enc a) :=
  (ComputableInO.of_linear (.of_frame (f := id) (encMid := encFramed enc) fun _ => rfl)).append
    (hpad.comp_enc enc) fun _ => rfl

/-- Writing `2 ^ f |x|` in unary, for `f` polynomial-time in unary: compute `f |x|`, then double
`f |x|` times. -/
private theorem exists_computableInO_two_pow_length {f : ℕ → ℕ}
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f encUnary encUnary) :
    ∃ d, ComputableInO (fun x : List Bool => 2 ^ f x.length) encBits encUnary
      (fun x => x.length + (x.length + 1) ^ d + (f x.length + 1) * 2 ^ f x.length)
      fun x => x.length + (x.length + 1) ^ d + 2 ^ f x.length := by
  obtain ⟨d, e, hd⟩ := hf.exists_degree
  exact ⟨d, (ComputableInO.unary_two_pow.comp (hd.inO.comp ComputableInO.lengthUnary)).mono_le
    (fun x => by simp [encUnary_apply]) fun x => by simp [encUnary_apply]⟩

/-- The cost of writing an exponentially padded instance: with `n, m ≤ M`, the instance length
`n`, a polynomial `(n + 1) ^ d` and the doubling cost `(m + 1) * 2 ^ m` of `2 ^ m` stay within
`2 ^ ((d + 2) * M + 2)`. -/
private theorem padTime_add_one_le {n m d M : ℕ} (hn : n ≤ M) (hm : m ≤ M) :
    n + (n + (n + 1) ^ d + (m + 1) * 2 ^ m) + 1 ≤ 2 ^ ((d + 2) * M + 2) := by
  have hM : M < 2 ^ M := Nat.lt_two_pow_self
  have hpow : (n + 1) ^ d ≤ 2 ^ (d * M) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left (by omega) d
  have hdbl : (m + 1) * 2 ^ m ≤ 2 ^ (2 * M) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hm)
  have h₁ : 2 ^ M ≤ 2 ^ ((d + 2) * M) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h₂ : 2 ^ (d * M) ≤ 2 ^ ((d + 2) * M) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h₃ : 2 ^ (2 * M) ≤ 2 ^ ((d + 2) * M) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  rw [pow_add]
  omega

/-- **The translation lemma on padded instances.** Suppose every problem in `NP` agrees with some
problem in `P` on the words `frame u ++ 1^{t |u|}`, and `t n` is computable in unary from any word
of length `n` within time `O(T n)`. Then every problem decidable by a nondeterministic machine
within time `O(t n)` is decidable deterministically within time `O((n + T n + 1) ^ d)` for some
`d`: the padded problem with padding `t n` agrees with a problem in `P` on padded instances, and
the padding is written within time `O(n + T n)`. -/
theorem NTIME_subset_iUnion_DTIME_of_agree_padded {t T : ℕ → ℕ}
    (hNP : ∀ B ∈ NP encBits, ∃ B' ∈ P encBits, ∀ u : List Bool,
      (frame u ++ List.replicate (t u.length) true ∈ B' ↔
        frame u ++ List.replicate (t u.length) true ∈ B))
    {S : List Bool → ℕ}
    (hpad : Turing.MultiTapeTM.ComputableInO (fun x : List Bool => t x.length) encBits encUnary
      (fun x => T x.length) S) :
    NTIME enc t ⊆ ⋃ d, DTIME enc fun n => (n + T n + 1) ^ d := by
  rintro A ⟨c₁, c₂, k, State, hfinite, ntm, hA⟩
  set c := Nat.card (Turing.Action k Bool State) * (c₁ + c₂)
  obtain ⟨B', hB', hagree⟩ := hNP _ (ntm.padded_mem_NP c)
  obtain ⟨d, hd⟩ := mem_P_iff_exists_mem_DTIME.mp hB'
  -- the reduction: frame the instance and append `t n` ones
  let g (a : α) : List Bool := frame (enc a) ++ List.replicate (t (enc a).length) true
  have hg : ComputableInO g enc encBits (fun a => (enc a).length + T (enc a).length)
      fun a => (enc a).length + S (enc a) :=
    computableInO_frame_append_replicate hpad
  obtain ⟨c', hc'⟩ := hpad.length_le_time
  have hlen (a : α) : (g a).length = 2 * (enc a).length + 1 + t (enc a).length := by
    simp [g]
  have ht (a : α) : t (enc a).length ≤ c' * (T (enc a).length + 1) := by
    simpa only [encUnary_apply, List.length_replicate] using hc' (enc a)
  have hpre : A = g ⁻¹' B' := by
    ext a
    refine Iff.trans ?_ (hagree (enc a)).symm
    refine (hA.frame_append_mem_padded_iff ?_).symm
    rw [List.length_append, List.length_replicate, length_frame]
    have : c₁ * t (enc a).length + c₂ ≤ (c₁ + c₂) * (2 * (enc a).length + 1 + t (enc a).length) :=
      by nlinarith
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ this
  refine Set.mem_iUnion.mpr ⟨d + 1, hpre ▸ preimage_mem_DTIME (C := (c' + 2) ^ d + 1) hd hg
    fun a => ?_⟩
  rw [encBits_apply, hlen]
  set n := (enc a).length
  set X := n + T n + 1
  have hX : 1 ≤ X := by omega
  have hL : 2 * n + 1 + t n ≤ (c' + 2) * X := by
    have := ht a
    simp only [X]
    nlinarith
  have h₁ : (2 * n + 1 + t n) ^ d ≤ (c' + 2) ^ d * X ^ (d + 1) := by
    calc (2 * n + 1 + t n) ^ d ≤ ((c' + 2) * X) ^ d := Nat.pow_le_pow_left hL d
      _ = (c' + 2) ^ d * X ^ d := Nat.mul_pow _ _ _
      _ ≤ (c' + 2) ^ d * X ^ (d + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (Nat.le_succ d))
  have h₂ : n + T n ≤ X ^ (d + 1) := (Nat.le_succ _).trans (Nat.le_self_pow (by omega) X)
  calc n + T n + (2 * n + 1 + t n) ^ d ≤ X ^ (d + 1) + (c' + 2) ^ d * X ^ (d + 1) :=
        Nat.add_le_add h₂ h₁
    _ = ((c' + 2) ^ d + 1) * X ^ (d + 1) := by ring
    _ ≤ _ := Nat.le_add_right _ _

/-- **The translation lemma.** If `NP ⊆ P` for problems on bit words, and `t n` is computable in
unary from any word of length `n` within time `O(T n)`, then every problem decidable by a
nondeterministic machine within time `O(t n)` is decidable deterministically within time
`O((n + T n + 1) ^ d)` for some `d`: the padded problem with padding `t n` is in `NP`, hence in
`P`, and the padding is written within time `O(n + T n)`. -/
theorem NTIME_subset_iUnion_DTIME_of_NP_subset_P (hNP : NP encBits ⊆ P encBits) {t T : ℕ → ℕ}
    {S : List Bool → ℕ}
    (hpad : Turing.MultiTapeTM.ComputableInO (fun x : List Bool => t x.length) encBits encUnary
      (fun x => T x.length) S) :
    NTIME enc t ⊆ ⋃ d, DTIME enc fun n => (n + T n + 1) ^ d :=
  NTIME_subset_iUnion_DTIME_of_agree_padded (fun B hB => ⟨B, hNP hB, fun _ => Iff.rfl⟩) hpad

/-- **Padding exponential time on padded instances.** If `NP` is easy on exponentially padded
instances, and `f` is computable in unary in polynomial time with `n ≤ f n`, then every problem
decidable by a nondeterministic machine within time `O(2 ^ f n)` is decidable deterministically
within time `O(2 ^ (d * f n))` for some `d`. -/
theorem NTIME_two_pow_subset_iUnion_DTIME_of_expPaddedNPEasy (hNP : ExpPaddedNPEasy)
    {f : ℕ → ℕ} (hf : Turing.MultiTapeTM.ComputableInPolyTime f encUnary encUnary)
      (hn : ∀ n, n ≤ f n) :
    NTIME enc (fun n => 2 ^ f n) ⊆ ⋃ d, DTIME enc fun n => 2 ^ (d * f n) := by
  intro A hA
  obtain ⟨d, hpad⟩ := exists_computableInO_two_pow_length hf
  have hagree : ∀ B ∈ NP encBits, ∃ B' ∈ P encBits, ∀ u : List Bool,
      (frame u ++ List.replicate (2 ^ f u.length) true ∈ B' ↔
        frame u ++ List.replicate (2 ^ f u.length) true ∈ B) := fun B hB => by
    obtain ⟨B', hB', h⟩ := hNP B hB
    exact ⟨B', hB', fun u => h u _ (Nat.pow_le_pow_right (by norm_num) (hn _))⟩
  obtain ⟨D, hD⟩ := Set.mem_iUnion.mp (NTIME_subset_iUnion_DTIME_of_agree_padded hagree
    (T := fun n => n + (n + 1) ^ d + (f n + 1) * 2 ^ f n) hpad hA)
  -- the padded instances are written within time `2 ^ O(f n)`
  refine Set.mem_iUnion.mpr ⟨(d + 2) * D, DTIME_mono_of_le_mul_add (C := 2 ^ (2 * D))
    (fun n => ?_) hD⟩
  calc (n + (n + (n + 1) ^ d + (f n + 1) * 2 ^ f n) + 1) ^ D
      ≤ (2 ^ ((d + 2) * f n + 2)) ^ D := Nat.pow_le_pow_left (padTime_add_one_le (hn n) le_rfl) D
    _ = 2 ^ (2 * D) * 2 ^ ((d + 2) * D * f n) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.le_add_right _ _

/-- **Padding exponential time.** If `NP ⊆ P` for problems on bit words, and `f` is computable in
unary in polynomial time with `n ≤ f n`, then every problem decidable by a nondeterministic machine
within time `O(2 ^ f n)` is decidable deterministically within time `O(2 ^ (d * f n))` for some
`d`. -/
theorem NTIME_two_pow_subset_iUnion_DTIME_of_NP_subset_P (hNP : NP encBits ⊆ P encBits)
    {f : ℕ → ℕ} (hf : Turing.MultiTapeTM.ComputableInPolyTime f encUnary encUnary)
      (hn : ∀ n, n ≤ f n) :
    NTIME enc (fun n => 2 ^ f n) ⊆ ⋃ d, DTIME enc fun n => 2 ^ (d * f n) :=
  NTIME_two_pow_subset_iUnion_DTIME_of_expPaddedNPEasy (expPaddedNPEasy_of_NP_subset_P hNP) hf hn

/-! ### Exponential time -/

/-- **If `NP` is easy on exponentially padded instances, then `NE ⊆ E`**, by the padding argument
of Book [Book][Book1974]. -/
theorem NE_subset_E_of_expPaddedNPEasy (hNP : ExpPaddedNPEasy) : NE enc ⊆ E enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_NE_iff.mp hA
  have hk' : A ∈ NTIME enc fun n => 2 ^ ((k + 1) * n) :=
    NTIME_mono (fun n => Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right n (Nat.le_succ k))) hk
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (NTIME_two_pow_subset_iUnion_DTIME_of_expPaddedNPEasy hNP
    (f := fun n => (k + 1) * n) (by fun_prop)
      (fun n => Nat.le_mul_of_pos_left n (Nat.succ_pos k))
    hk')
  exact mem_E_iff.mpr ⟨d * (k + 1), by simpa only [Nat.mul_assoc] using hd⟩

/-- **If `NP ⊆ P`, then `NE ⊆ E`**, by padding [Book][Book1974]. -/
theorem NE_subset_E_of_NP_subset_P (hNP : NP encBits ⊆ P encBits) : NE enc ⊆ E enc :=
  NE_subset_E_of_expPaddedNPEasy (expPaddedNPEasy_of_NP_subset_P hNP)

/-- **If `NP` is easy on exponentially padded instances, then `NEXP ⊆ EXP`**, by padding. -/
theorem NEXP_subset_EXP_of_expPaddedNPEasy (hNP : ExpPaddedNPEasy) : NEXP enc ⊆ EXP enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_NEXP_iff.mp hA
  have hk' : A ∈ NTIME enc fun n => 2 ^ n ^ (k + 1) :=
    NTIME_mono_of_eventually_le (Filter.eventually_atTop.mpr ⟨1, fun n hn =>
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right hn (Nat.le_succ k))⟩) hk
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (NTIME_two_pow_subset_iUnion_DTIME_of_expPaddedNPEasy hNP
    (ComputableInPolyTime.unary_pow (k + 1))
      (fun n => Nat.le_self_pow (by omega) n) hk')
  exact DTIME_two_pow_subset_EXP (h := fun n => d * n ^ (k + 1)) (by fun_prop) hd

/-- **If `NP ⊆ P`, then `NEXP ⊆ EXP`** [Arora and Barak, Section 2.6][AroraBarak09]. -/
theorem NEXP_subset_EXP_of_NP_subset_P (hNP : NP encBits ⊆ P encBits) : NEXP enc ⊆ EXP enc :=
  NEXP_subset_EXP_of_expPaddedNPEasy (expPaddedNPEasy_of_NP_subset_P hNP)

/-- **If `P = NP`, then `E = NE`**, by padding [Book][Book1974]. -/
theorem E_eq_NE_of_P_eq_NP (h : P encBits = NP encBits) : E enc = NE enc :=
  E_subset_NE.antisymm (NE_subset_E_of_NP_subset_P h.ge)

/-- **If `P = NP`, then `EXP = NEXP`** [Arora and Barak, Section 2.6][AroraBarak09]. -/
theorem EXP_eq_NEXP_of_P_eq_NP (h : P encBits = NP encBits) : EXP enc = NEXP enc :=
  EXP_subset_NEXP.antisymm (NEXP_subset_EXP_of_NP_subset_P h.ge)

/-- **If `EXP ≠ NEXP`, then `P ≠ NP`.** -/
theorem P_ne_NP_of_EXP_ne_NEXP (h : EXP enc ≠ NEXP enc) : P encBits ≠ NP encBits :=
  fun hP => h (EXP_eq_NEXP_of_P_eq_NP hP)

/-! ### Upward translation from `NP` to `NTIME` and `NEXP` -/

section Translation

open Cslib.Probability

variable {α : Type} {enc : α ↪ List Bool}

/-- Pulling back a problem `B ∈ NP encBits` along a function `g : α → List Bool` computable within
time `O(T₀ (enc a).length)` places `g ⁻¹' B` in `NTIME enc (fun n => (T₀ n + 1) ^ d)` for
some `d`: a deterministic machine writes `g a` to a buffer tape and hands off to the halting
fair-coin certificate verifier for `B`. -/
theorem preimage_mem_NTIME_of_mem_NP {B : Set (List Bool)} {g : α → List Bool} {T₀ : ℕ → ℕ}
    {S : α → ℕ} (hB : B ∈ NP encBits)
    (hg : Turing.MultiTapeTM.ComputableInO g enc encBits (fun a => T₀ (enc a).length) S) :
    ∃ d, g ⁻¹' B ∈ NTIME enc fun n => (T₀ n + 1) ^ d := by
  have hg := hg.tidy
  obtain ⟨c₀, ⟨k₀, State₀, hfinite₀, tm, htm⟩, -⟩ := hg
  set t₁ : α → ℕ := fun a => c₀ * (T₀ (enc a).length + 1)
  have htm_run (a : α) :
      tm.runFrom (tm.initCfg (enc a)) (t₁ a) = wordsCfg (enc a) none (fun _ => []) (g a) := by
    obtain ⟨p, hh, hl, ht, -⟩ := computesTidily_iff.mp (htm a)
    have hhead : p.head = tm.initCfg (enc a) := hh.trans (Cfg.init_eq_wordsCfg tm.q₀ (enc a)).symm
    have hrun : tm.runFrom (tm.initCfg (enc a)) p.time =
        wordsCfg (enc a) none (fun _ => []) (g a) :=
      hhead ▸ (MultiTapeTM.runPath_apply_eq_runFrom p (.last _)).symm.trans hl
    have hhalt : (tm.runFrom (tm.initCfg (enc a)) p.time).state = none := by rw [hrun]; rfl
    exact (tm.runFrom_eq_of_halt (tm.initCfg (enc a)) ht hhalt).trans hrun
  have hg_len (a : α) : (g a).length ≤ t₁ a := (htm a).length_output_le
  let M_pad : MultiTapePTM k₀ Bool State₀ := MultiTapePTM.ofDeterministic tm
  have hfirst (a : α) :
      ∀ final ∈ (ProbComp.eval
        (M_pad.runClosedConfigFrom (t₁ a) (M_pad.initialConfig (enc a)))).support,
        final.tapes.state = none := by
    intro final hfinal
    rw [MultiTapePTM.eval_runClosedConfigFrom_ofDeterministic, PMF.mem_support_pure_iff] at hfinal
    subst hfinal
    change (tm.runFrom (tm.initCfg (enc a)) (t₁ a)).state = none
    rw [htm_run a]
    rfl
  have hout₁ (a : α) :
      ProbComp.eval (M_pad.runClosed (t₁ a) (enc a)) = PMF.pure (g a) := by
    rw [MultiTapePTM.eval_runClosed_ofDeterministic, htm_run a]
    rfl
  -- Unpack `B ∈ NP encBits` into a halting fair-coin machine `M_NP`
  obtain ⟨p, V, hV, hVer⟩ := hB
  obtain ⟨k₁, State₁, hfinite₁, M_NP, c₁, d₁, heval₂, hhalt₂⟩ :=
    (isPPTOn_sampleVerify p hV).exists_halting_machine
  set t₂ : α → ℕ := fun a => c₁ * (t₁ a + 1) ^ d₁
  have ht₂_le (a : α) : c₁ * ((g a).length + 1) ^ d₁ ≤ t₂ a :=
    Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (Nat.add_le_add_right (hg_len a) 1) d₁)
  have hsecond (a : α) :
      ∀ word ∈ (ProbComp.eval (M_pad.runClosed (t₁ a) (enc a))).support,
        ∀ final ∈ (ProbComp.eval
          (M_NP.runClosedConfigFrom (t₂ a) (M_NP.initialConfig word))).support,
          final.tapes.state = none := by
    intro word hword final hfinal
    rw [hout₁ a, PMF.mem_support_pure_iff] at hword
    subst hword
    rw [M_NP.eval_runClosedConfigFrom_eq_of_halted _ (ht₂_le a) (hhalt₂ (g a))] at hfinal
    exact hhalt₂ (g a) final hfinal
  let M_comp := M_NP.comp M_pad false
  set totalTime : α → ℕ := fun a => t₁ a + (t₁ a + 4 + t₂ a)
  have hdecides : M_comp.toNTM.DecidesInTime enc (g ⁻¹' B) totalTime := by
    intro a
    have htime : M_comp.toNTM.RunsInTime (enc a) (totalTime a) :=
      M_comp.runsInTime_toNTM (M_pad.comp_halted M_NP false (enc a) (t₁ a) (t₂ a)
        (hfirst a) (hsecond a))
    refine ⟨htime, ?_⟩
    rw [Set.mem_preimage, hVer (g a), MultiTapeNTM.accepts_iff_exists_time_eq htime,
      M_comp.exists_computationPath_toNTM_iff (P := fun cfg => cfg.output = [true])]
    have hcomp_eval :
        ProbComp.eval (M_comp.runClosed (totalTime a) (enc a)) =
          ProbComp.eval (M_NP.runClosed (c₁ * ((g a).length + 1) ^ d₁) (g a)) := by
      rw [M_pad.eval_comp M_NP false (enc a) (t₁ a) (t₂ a) (hfirst a) (hsecond a),
        hout₁ a, Probability.PMF.monad_bind_eq_bind, PMF.pure_bind,
        M_NP.eval_runClosed_eq_of_halted (g a) (ht₂_le a) (hhalt₂ (g a))]
    -- both sides say that `[true]` is a supported output
    rw [← singleton_true_mem_support_sampleVerify_iff V (g a),
      (heval₂ (g a)).trans hcomp_eval.symm, MultiTapePTM.runClosed_eq_map, ProbComp.eval_map,
      PMF.mem_support_map_iff]
  refine ⟨d₁ + 1, (2 * c₀ + 4 + c₁ * (c₀ + 1) ^ d₁), 0, k₁ + k₀ + 2, _, inferInstance,
    M_comp.toNTM, hdecides.mono fun a => ?_⟩
  set X := T₀ (enc a).length + 1
  have hX : 1 ≤ X := Nat.succ_pos _
  have ht₁_bound : t₁ a + 1 ≤ (c₀ + 1) * X := by simp only [t₁, X]; nlinarith
  have ht₂_bound : t₂ a ≤ c₁ * (c₀ + 1) ^ d₁ * X ^ (d₁ + 1) := by
    calc t₂ a = c₁ * (t₁ a + 1) ^ d₁ := rfl
      _ ≤ c₁ * ((c₀ + 1) * X) ^ d₁ := Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left ht₁_bound d₁)
      _ = c₁ * (c₀ + 1) ^ d₁ * X ^ d₁ := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ c₁ * (c₀ + 1) ^ d₁ * X ^ (d₁ + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (Nat.le_succ d₁))
  have hX_pow : X ≤ X ^ (d₁ + 1) := Nat.le_self_pow (by lia) X
  calc totalTime a
      = 2 * c₀ * X + 4 + t₂ a := by simp only [totalTime, t₁, X]; ring
    _ ≤ 2 * c₀ * X ^ (d₁ + 1) + 4 * X ^ (d₁ + 1) + c₁ * (c₀ + 1) ^ d₁ * X ^ (d₁ + 1) := by
        have : 4 ≤ 4 * X ^ (d₁ + 1) := Nat.le_mul_of_pos_right 4 (Nat.pow_pos hX)
        nlinarith
    _ = (2 * c₀ + 4 + c₁ * (c₀ + 1) ^ d₁) * X ^ (d₁ + 1) + 0 := by ring

/-- Pulling back `B ∈ NP encBits` along the exponential-padding map
`a ↦ frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true`, where `f` is polynomial-time in
unary with `n ≤ f n`, gives a problem in `NEXP enc`. -/
theorem preimage_pad_mem_NEXP {B : Set (List Bool)} (hB : B ∈ NP encBits) {f : ℕ → ℕ}
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f encUnary encUnary) (hn : ∀ n, n ≤ f n) :
    (fun a : α => frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true) ⁻¹' B ∈
      NEXP enc := by
  obtain ⟨d, hpad⟩ := exists_computableInO_two_pow_length hf
  obtain ⟨D, hD⟩ := preimage_mem_NTIME_of_mem_NP hB
    (T₀ := fun n => n + (n + (n + 1) ^ d + (f n + 1) * 2 ^ f n))
    (computableInO_frame_append_replicate (t := fun n => 2 ^ f n) hpad)
  -- the padded instance is written within time `2 ^ O(f n)`, and `f` is polynomially bounded
  have := hf.polynomiallyBounded
  refine NTIME_two_pow_subset_NEXP (h := fun n => ((d + 2) * f n + 2) * D) (by fun_prop)
    (NTIME_mono (fun n => ?_) hD)
  rw [pow_mul]
  exact Nat.pow_le_pow_left (padTime_add_one_le (hn n) le_rfl) D

/-- Pulling back `B ∈ NP encBits` along `x ↦ x ++ List.replicate (2 ^ x.length) true` gives a
problem in `NEXP encBits`. -/
theorem preimage_append_two_pow_mem_NEXP {B : Set (List Bool)} (hB : B ∈ NP encBits) :
    (fun x : List Bool => x ++ List.replicate (2 ^ x.length) true) ⁻¹' B ∈ NEXP encBits := by
  have hpad := ComputableInO.unary_two_pow.comp ComputableInO.lengthUnary
  let g (x : List Bool) : List Bool := x ++ List.replicate (2 ^ x.length) true
  let T₀ (n : ℕ) : ℕ := n + (n + (n + 1) * 2 ^ n)
  have hg : ComputableInO g encBits encBits (fun x => T₀ x.length)
      (fun x => x.length + (x.length + 2 ^ x.length)) :=
    (ComputableInO.of_linear (.of_eq (f := id) (encIn := encBits) (encMid := encBits)
      fun _ => rfl)).append hpad fun _ => rfl
  obtain ⟨D, hD⟩ := preimage_mem_NTIME_of_mem_NP hB hg
  -- the padded word is written within time `2 ^ O(n)`
  refine NTIME_two_pow_subset_NEXP (h := fun n => (2 * n + 2) * D) (by fun_prop)
    (NTIME_mono (fun n => ?_) hD)
  rw [pow_mul]
  refine Nat.pow_le_pow_left ?_ D
  have := padTime_add_one_le (d := 0) (le_refl n) (le_refl n)
  rw [pow_zero, zero_add] at this
  simp only [T₀]
  omega

/-- Pulling back `B ∈ P (encPair encBits encBits)` along
`(a, y) ↦ (frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true, y)`, where `f` is
polynomial-time in unary, gives a problem in `EXP (encPair enc encBits)`. -/
theorem preimage_pad_prod_id_mem_EXP {B : Set (List Bool × List Bool)}
    (hB : B ∈ P (encPair encBits encBits)) {f : ℕ → ℕ}
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f encUnary encUnary) :
    (fun p : α × List Bool =>
      (frame (enc p.1) ++ List.replicate (2 ^ f (enc p.1).length) true, p.2)) ⁻¹' B ∈
      EXP (encPair enc encBits) := by
  obtain ⟨d, hd⟩ := mem_P_iff_exists_mem_DTIME.mp hB
  obtain ⟨d₀, hpad⟩ := exists_computableInO_two_pow_length hf
  have hg := ((computableInO_frame_append_replicate (t := fun n => 2 ^ f n) hpad).comp
    (ComputableInO.fst enc encBits)).prod (ComputableInO.snd enc encBits)
  -- `f` is bounded by a monotone polynomial
  obtain ⟨c, e, hce⟩ := polynomiallyBounded_iff_le.mp hf.polynomiallyBounded
  refine DTIME_two_pow_subset_EXP (h := fun N => (d₀ + d + 2) * (N + c * (N + 1) ^ e + 3))
    (by fun_prop) (preimage_mem_DTIME (C := 4) hd hg fun p => ?_)
  set n := (enc p.1).length
  set N := (encPair enc encBits p).length
  have hnN : 2 * n + 1 + p.2.length = N := by simp [N, n]
  set X := N + c * (N + 1) ^ e with hX
  have hfX : f n ≤ X := (hce n).trans
    ((Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) e)).trans (Nat.le_add_left _ _))
  have hXX : X < 2 ^ X := Nat.lt_two_pow_self
  -- each part of the cost is within `2 ^ E`
  set E := (d₀ + d + 2) * (X + 3) with hE
  have hXE : 2 ^ X ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hT := (padTime_add_one_le (n := n) (d := d₀) (by omega) hfX).trans
    (Nat.pow_le_pow_right (by norm_num) (by nlinarith : (d₀ + 2) * X + 2 ≤ E))
  have hlen : (encPair encBits encBits
      (frame (enc p.1) ++ List.replicate (2 ^ f n) true, p.2)).length + 1 ≤ 2 ^ (X + 3) := by
    have h2f : 2 ^ f n ≤ 2 ^ X := Nat.pow_le_pow_right (by norm_num) hfX
    simp only [length_encPair, encBits_apply, List.length_append, length_frame,
      List.length_replicate]
    rw [pow_add]
    omega
  have hpow : (encPair encBits encBits
      (frame (enc p.1) ++ List.replicate (2 ^ f n) true, p.2)).length ^ d ≤ 2 ^ E :=
    calc _ ≤ (2 ^ (X + 3)) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ (d * (X + 3)) := (pow_mul' 2 d (X + 3)).symm
      _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
  omega

/-- Pulling back `B ∈ P (encPair encBits encUnary)` along
`a ↦ (frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true, 2 ^ g (enc a).length)`, where
`f` and `g` are polynomial-time in unary with `n ≤ f n`, gives a problem in `EXP enc`. -/
theorem preimage_pad_prod_two_pow_mem_EXP {B : Set (List Bool × ℕ)}
    (hB : B ∈ P (encPair encBits encUnary)) {f g : ℕ → ℕ}
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f encUnary encUnary) (hnf : ∀ n, n ≤ f n)
    (hg : Turing.MultiTapeTM.ComputableInPolyTime g encUnary encUnary) :
    (fun a : α =>
      (frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true,
        2 ^ g (enc a).length)) ⁻¹' B ∈ EXP enc := by
  obtain ⟨d, hd⟩ := mem_P_iff_exists_mem_DTIME.mp hB
  obtain ⟨d₀, hpad_f⟩ := exists_computableInO_two_pow_length hf
  obtain ⟨d₁, hpad_g⟩ := exists_computableInO_two_pow_length hg
  have hφ := (computableInO_frame_append_replicate (t := fun n => 2 ^ f n) hpad_f).prod
    (hpad_g.comp_enc enc)
  have := hf.polynomiallyBounded
  have := hg.polynomiallyBounded
  refine DTIME_two_pow_subset_EXP (h := fun n => (d₀ + d₁ + d + 2) * (f n + g n + 3))
    (by fun_prop) (preimage_mem_DTIME (C := 3) hd hφ fun a => ?_)
  set n := (enc a).length
  set X := f n + g n with hX
  have hnX : n ≤ X := (hnf n).trans (Nat.le_add_right _ _)
  have hXX : X < 2 ^ X := Nat.lt_two_pow_self
  -- each part of the cost is within `2 ^ E`
  set E := (d₀ + d₁ + d + 2) * (X + 3) with hE
  have hT_f := (padTime_add_one_le (d := d₀) hnX (Nat.le_add_right (f n) (g n))).trans
    (Nat.pow_le_pow_right (by norm_num) (by nlinarith : (d₀ + 2) * X + 2 ≤ E))
  have hT_g := (padTime_add_one_le (d := d₁) hnX (Nat.le_add_left (g n) (f n))).trans
    (Nat.pow_le_pow_right (by norm_num) (by nlinarith : (d₁ + 2) * X + 2 ≤ E))
  have hlen : (encPair encBits encUnary
      (frame (enc a) ++ List.replicate (2 ^ f n) true, 2 ^ g n)).length + 1 ≤ 2 ^ (X + 3) := by
    have h2f : 2 ^ f n ≤ 2 ^ X := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
    have h2g : 2 ^ g n ≤ 2 ^ X := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
    simp only [length_encPair, encBits_apply, encUnary_apply, List.length_append, length_frame,
      List.length_replicate]
    rw [pow_add]
    omega
  have hpow : (encPair encBits encUnary
      (frame (enc a) ++ List.replicate (2 ^ f n) true, 2 ^ g n)).length ^ d ≤ 2 ^ E :=
    calc _ ≤ (2 ^ (X + 3)) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ (d * (X + 3)) := (pow_mul' 2 d (X + 3)).symm
      _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
  omega

end Translation

end Cslib.Complexity
