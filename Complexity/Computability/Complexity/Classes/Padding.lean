/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.NP.Nondeterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Complexity.Classes.NP.GuessVerify
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.PPT.Clock
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Padding

If `P = NP`, then `EXP = NEXP` and `E = NE` [Arora and Barak, Section 2.6][AroraBarak09]:
collapses of polynomial classes translate upwards, by the padding argument of Book
[Book][Book1974]. The proof pads instances until a slow nondeterministic machine is fast in the
length of the padded instance, decides the padded problem deterministically, and pays for writing
the padding.

## Timed reductions

The general timed-reduction API lives in
`Complexity.Computability.Complexity.Classes.Time`. In particular,
`Cslib.Complexity.preimage_mem_DTIME` computes a reduction and then tidily decides its output;
the padding arguments below apply this API to their padded instances. The unconditional
deterministic exponential-padding lemma
`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad` lives in
`Complexity.Computability.Complexity.Classes.EXP`.

## The padded problem

A nondeterministic machine `ntm` decides `A` within time `t`. The padded problem
`Turing.MultiTapeNTM.padded ntm c` consists of the bit words `x` such that some `c * |x|` coins
encode an accepting computation of `ntm` on the word `unframe x` framed at the start of `x`, read
as coins of the choice table (`Turing.MultiTapeNTM.checkChoices`). The general certificate
characterization `Turing.MultiTapeNTM.DecidesInTime.mem_iff_exists_checkChoices` lives with
`checkChoices` in `Complexity.Computability.Complexity.Classes.NP.Nondeterministic`. The padded
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
(`Turing.MultiTapeTM.ComputableTidilyInO.unary_two_pow`), and
`NTIME (2 ^ f n) ⊆ ⋃ d, DTIME (2 ^ (d * f n))`
(`Cslib.Complexity.NTIME_two_pow_subset_iUnion_DTIME_of_NP_subset_P`). With `f n = (k + 1) * n`
and `f n = n ^ (k + 1)` this gives `NE ⊆ E` and `NEXP ⊆ EXP`.

The hypothesis is `NP ⊆ P` for problems on bit words, under `encBits`; the conclusions hold for
problems on any type, under any encoding.

The unconditional pullback lemmas `Cslib.Complexity.preimage_mem_NTIME_of_mem_NP` and
`Cslib.Complexity.preimage_pad_mem_NEXP` compose a timed deterministic map with an `NP` verifier;
exponential padding yields an `NEXP` decider without a collapse hypothesis.

## Main definitions

* `Turing.MultiTapeNTM.checkPadded`: the verifier of padded instances.
* `Turing.MultiTapeNTM.padded`: the padded problem of a nondeterministic machine.

## Main results

* `Cslib.Complexity.preimage_mem_NTIME_of_mem_NP`, `Cslib.Complexity.preimage_pad_mem_NEXP`:
  unconditional timed pullback of `NP`, including exponentially padded inputs.
* `Turing.MultiTapeNTM.padded_mem_NP`,
  `Turing.MultiTapeNTM.DecidesInTime.frame_append_mem_padded_iff`: the padded problem is in `NP`,
  and decides the original problem on padded instances.
* `Cslib.Complexity.NTIME_subset_iUnion_DTIME_of_NP_subset_P`: the translation lemma.
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
  refine .of_tidy ?_
  have hunframe : ComputableTidilyInPolyTime unframe encBits encBits :=
    .of_linear (.of_unframe fun _ => rfl)
  exact (ntm.computableInPolyTime_checkChoices).tidy.comp
    ((hunframe.comp (.fst encBits encBits)).prod (.snd encBits encBits))

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

/-- **The translation lemma.** If `NP ⊆ P` for problems on bit words, and `t n` is computable in
unary from any word of length `n` within time `O(T n)`, then every problem decidable by a
nondeterministic machine within time `O(t n)` is decidable deterministically within time
`O((n + T n + 1) ^ d)` for some `d`: the padded problem with padding `t n` is in `NP`, hence in
`P`, and the padding is written within time `O(n + T n)`. -/
theorem NTIME_subset_iUnion_DTIME_of_NP_subset_P (hNP : NP encBits ⊆ P encBits) {t T : ℕ → ℕ}
    {S : List Bool → ℕ}
    (hpad : Turing.MultiTapeTM.ComputableInO (fun x : List Bool => t x.length) encBits encUnary
      (fun x => T x.length) S) :
    NTIME enc t ⊆ ⋃ d, DTIME enc fun n => (n + T n + 1) ^ d := by
  have hpad := hpad.tidy
  rintro A ⟨c₁, c₂, k, State, hfinite, ntm, hA⟩
  set c := Nat.card (Turing.Action k Bool State) * (c₁ + c₂)
  obtain ⟨d, hd⟩ := mem_P_iff_exists_mem_DTIME.mp (hNP (ntm.padded_mem_NP c))
  -- the reduction: frame the instance and append `t n` ones
  let g (a : α) : List Bool := frame (enc a) ++ List.replicate (t (enc a).length) true
  have hg : ComputableTidilyInO g enc encBits (fun a => (enc a).length + T (enc a).length)
      fun a => (enc a).length + S (enc a) :=
    (ComputableTidilyInO.of_linear (.of_frame (f := id) (encOut := encFramed enc)
      fun _ => rfl)).append (hpad.comp_enc enc) fun _ => rfl
  obtain ⟨c', hc'⟩ := hpad.length_le_time
  have hlen (a : α) : (g a).length = 2 * (enc a).length + 1 + t (enc a).length := by
    simp [g]
  have ht (a : α) : t (enc a).length ≤ c' * (T (enc a).length + 1) := by
    simpa only [encUnary_apply, List.length_replicate] using hc' (enc a)
  have hpre : A = g ⁻¹' ntm.padded c := by
    ext a
    refine (hA.frame_append_mem_padded_iff ?_).symm
    rw [List.length_append, List.length_replicate, length_frame]
    have : c₁ * t (enc a).length + c₂ ≤ (c₁ + c₂) * (2 * (enc a).length + 1 + t (enc a).length) :=
      by nlinarith
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ this
  refine Set.mem_iUnion.mpr ⟨d + 1, hpre ▸ preimage_mem_DTIME (C := (c' + 2) ^ d + 1) hd
    (.of_tidy hg)
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

/-- **Padding exponential time.** If `NP ⊆ P` for problems on bit words, and `f` is computable in
unary in polynomial time with `n ≤ f n`, then every problem decidable by a nondeterministic machine
within time `O(2 ^ f n)` is decidable deterministically within time `O(2 ^ (d * f n))` for some
`d`. -/
theorem NTIME_two_pow_subset_iUnion_DTIME_of_NP_subset_P (hNP : NP encBits ⊆ P encBits)
    {f : ℕ → ℕ} (hf : Turing.MultiTapeTM.ComputableInPolyTime f encUnary encUnary)
      (hn : ∀ n, n ≤ f n) :
    NTIME enc (fun n => 2 ^ f n) ⊆ ⋃ d, DTIME enc fun n => 2 ^ (d * f n) := by
  have hf := hf.tidy
  intro A hA
  obtain ⟨d, e, hd⟩ := hf.exists_degree
  have hpad := ComputableTidilyInO.unary_two_pow.comp (hd.inO.comp ComputableTidilyInO.lengthUnary)
  have hpad' : ComputableTidilyInO (fun x : List Bool => 2 ^ f x.length) encBits encUnary
      (fun x => x.length + (x.length + 1) ^ d + (f x.length + 1) * 2 ^ f x.length)
      fun x => x.length + (x.length + 1) ^ d + 2 ^ f x.length :=
    hpad.mono_le (fun x => by simp [encUnary_apply]) fun x => by simp [encUnary_apply]
  obtain ⟨D, hD⟩ := Set.mem_iUnion.mp (NTIME_subset_iUnion_DTIME_of_NP_subset_P hNP
    (T := fun n => n + (n + 1) ^ d + (f n + 1) * 2 ^ f n) (.of_tidy hpad') hA)
  obtain ⟨C₀, hC₀⟩ := (PolynomiallyBounded.of_forall_le 1 d fun n => by
    simp only [one_mul]; exact le_rfl).exists_le_mul_two_pow (p := fun n => (n + 1) ^ d)
  refine Set.mem_iUnion.mpr ⟨2 * D, DTIME_mono_of_le_mul_add (C := (C₀ + 3) ^ D)
    (fun n => ?_) hD⟩
  have h₁ : 2 ^ n ≤ 2 ^ f n := Nat.pow_le_pow_right (by norm_num) (hn n)
  have h₂ : 2 * n + 1 ≤ 2 * 2 ^ n := by have := @Nat.lt_two_pow_self n; omega
  have h₃ : f n + 1 ≤ 2 ^ f n := Nat.lt_two_pow_self
  have h₄ : 2 ^ f n ≤ 2 ^ (2 * f n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h₅ : (f n + 1) * 2 ^ f n ≤ 2 ^ (2 * f n) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul_right _ h₃
  have hle : n + (n + (n + 1) ^ d + (f n + 1) * 2 ^ f n) + 1 ≤ (C₀ + 3) * 2 ^ (2 * f n) := by
    have := hC₀ n
    have : C₀ * 2 ^ n ≤ C₀ * 2 ^ (2 * f n) := Nat.mul_le_mul_left _ (h₁.trans h₄)
    nlinarith
  calc (n + (n + (n + 1) ^ d + (f n + 1) * 2 ^ f n) + 1) ^ D
      ≤ ((C₀ + 3) * 2 ^ (2 * f n)) ^ D := Nat.pow_le_pow_left hle D
    _ = (C₀ + 3) ^ D * 2 ^ (2 * D * f n) := by rw [Nat.mul_pow, ← Nat.pow_mul]; ring_nf
    _ ≤ _ := Nat.le_add_right _ _

/-! ### Exponential time -/

/-- **If `NP ⊆ P`, then `NE ⊆ E`**, by padding [Book][Book1974]. -/
theorem NE_subset_E_of_NP_subset_P (hNP : NP encBits ⊆ P encBits) : NE enc ⊆ E enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_NE_iff.mp hA
  have hk' : A ∈ NTIME enc fun n => 2 ^ ((k + 1) * n) :=
    NTIME_mono (fun n => Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right n (Nat.le_succ k))) hk
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (NTIME_two_pow_subset_iUnion_DTIME_of_NP_subset_P hNP
    (f := fun n => (k + 1) * n) (.of_tidy (by fun_prop))
      (fun n => Nat.le_mul_of_pos_left n (Nat.succ_pos k))
    hk')
  exact mem_E_iff.mpr ⟨d * (k + 1), by simpa only [Nat.mul_assoc] using hd⟩

/-- **If `NP ⊆ P`, then `NEXP ⊆ EXP`** [Arora and Barak, Section 2.6][AroraBarak09]. -/
theorem NEXP_subset_EXP_of_NP_subset_P (hNP : NP encBits ⊆ P encBits) : NEXP enc ⊆ EXP enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_NEXP_iff.mp hA
  have hk' : A ∈ NTIME enc fun n => 2 ^ n ^ (k + 1) :=
    NTIME_mono_of_eventually_le (Filter.eventually_atTop.mpr ⟨1, fun n hn =>
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right hn (Nat.le_succ k))⟩) hk
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (NTIME_two_pow_subset_iUnion_DTIME_of_NP_subset_P hNP
    (.of_tidy (ComputableTidilyInPolyTime.unary_pow (k + 1)))
      (fun n => Nat.le_self_pow (by omega) n) hk')
  refine mem_EXP_iff.mpr ⟨k + 2, DTIME_mono_of_eventually_le (Filter.eventually_atTop.mpr
    ⟨d, fun n hn => Nat.pow_le_pow_right (by norm_num) ?_⟩) hd⟩
  rw [pow_succ' n (k + 1)]
  exact Nat.mul_le_mul_right _ hn

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
open _root_.Turing.MultiTapeTM.ComputableTidilyInPolyTime

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
  let program (x : List Bool) : ProbComp Bool :=
    (fun w => V (x, w)) <$> BitString.sampleList (p.eval x.length)
  have hcount : ComputableTidilyInPolyTime (fun x : List Bool => p.eval x.length)
      encBits encUnary :=
    (unary_eval p).comp (encoding_length encBits)
  have hprogram : IsPPTOn encBits encBool program := hcount.sampleList.map_with hV
  obtain ⟨k₁, State₁, hfinite₁, M_NP, c₁, d₁, heval₂, hhalt₂⟩ := hprogram.exists_halting_machine
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
    have hsupport := congrArg (fun μ => [true] ∈ μ.support)
      ((heval₂ (g a)).trans hcomp_eval.symm)
    simp only [MultiTapePTM.runClosed_eq_map, ProbComp.eval_map, PMF.mem_support_map_iff,
      program, BitString.eval_sampleList, BitString.mem_support_uniformList_iff, encBool_apply,
      List.cons.injEq, and_true] at hsupport
    rw [← hsupport]
    exact ⟨fun ⟨w, hw, hV⟩ => ⟨true, ⟨w, hw, hV⟩, rfl⟩,
      fun ⟨_, ⟨w, hw, hV⟩, rfl⟩ => ⟨w, hw, hV⟩⟩
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
  have hf := hf.tidy
  obtain ⟨d₀, e₀, hd₀⟩ := hf.exists_degree
  have hpad := ComputableTidilyInO.unary_two_pow.comp (hd₀.inO.comp ComputableTidilyInO.lengthUnary)
  have hpad' : ComputableTidilyInO (fun x : List Bool => 2 ^ f x.length) encBits encUnary
      (fun x => x.length + (x.length + 1) ^ d₀ + (f x.length + 1) * 2 ^ f x.length)
      (fun x => x.length + (x.length + 1) ^ d₀ + 2 ^ f x.length) :=
    hpad.mono_le (fun x => by simp [encUnary_apply]) fun x => by simp [encUnary_apply]
  let g (a : α) : List Bool := frame (enc a) ++ List.replicate (2 ^ f (enc a).length) true
  let T₀ (n : ℕ) : ℕ := n + (n + (n + 1) ^ d₀ + (f n + 1) * 2 ^ f n)
  have hg : ComputableTidilyInO g enc encBits (fun a => T₀ (enc a).length)
      (fun a => (enc a).length + ((enc a).length + ((enc a).length + 1) ^ d₀ +
        2 ^ f (enc a).length)) :=
    (ComputableTidilyInO.of_linear (.of_frame (f := id) (encOut := encFramed enc)
      fun _ => rfl)).append (hpad'.comp_enc enc) fun _ => rfl
  obtain ⟨D, hD⟩ := preimage_mem_NTIME_of_mem_NP hB (.of_tidy hg)
  obtain ⟨C₀, hC₀⟩ := (PolynomiallyBounded.of_forall_le 1 d₀ fun n => by
    simp only [one_mul]; exact le_rfl).exists_le_mul_two_pow (p := fun n => (n + 1) ^ d₀)
  obtain ⟨c_f, d_f, hf_le⟩ := hf.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hf_le
  have hNTIME : g ⁻¹' B ∈ NTIME enc fun n => 2 ^ (2 * D * f n) := by
    obtain ⟨c₁, c₂, k, State, hfinite, ntm, hdec⟩ := hD
    refine ⟨c₁ * (C₀ + 3) ^ D, c₂, k, State, hfinite, ntm, hdec.mono fun a => ?_⟩
    set n := (enc a).length
    have h₁ : 2 ^ n ≤ 2 ^ f n := Nat.pow_le_pow_right (by norm_num) (hn n)
    have h₂ : 2 * n + 1 ≤ 2 * 2 ^ n := by have := @Nat.lt_two_pow_self n; lia
    have h₃ : f n + 1 ≤ 2 ^ f n := Nat.lt_two_pow_self
    have h₄ : 2 ^ f n ≤ 2 ^ (2 * f n) := Nat.pow_le_pow_right (by norm_num) (by lia)
    have h₅ : (f n + 1) * 2 ^ f n ≤ 2 ^ (2 * f n) := by
      rw [two_mul, pow_add]
      exact Nat.mul_le_mul_right _ h₃
    have hle : T₀ n + 1 ≤ (C₀ + 3) * 2 ^ (2 * f n) := by
      have := hC₀ n
      have : C₀ * 2 ^ n ≤ C₀ * 2 ^ (2 * f n) := Nat.mul_le_mul_left _ (h₁.trans h₄)
      simp only [T₀]
      nlinarith
    have hpow : (T₀ n + 1) ^ D ≤ (C₀ + 3) ^ D * 2 ^ (2 * D * f n) := by
      calc (T₀ n + 1) ^ D
          ≤ ((C₀ + 3) * 2 ^ (2 * f n)) ^ D := Nat.pow_le_pow_left hle D
        _ = (C₀ + 3) ^ D * 2 ^ (2 * D * f n) := by rw [Nat.mul_pow, ← Nat.pow_mul]; ring_nf
    calc c₁ * (T₀ n + 1) ^ D + c₂
        ≤ c₁ * ((C₀ + 3) ^ D * 2 ^ (2 * D * f n)) + c₂ :=
          Nat.add_le_add_right (Nat.mul_le_mul_left c₁ hpow) c₂
      _ = c₁ * (C₀ + 3) ^ D * 2 ^ (2 * D * f n) + c₂ := by ring
  refine mem_NEXP_iff.mpr ⟨d_f + 1, NTIME_mono_of_eventually_le (Filter.eventually_atTop.mpr
    ⟨2 * D * c_f * 2 ^ d_f + 2, fun n hn' => Nat.pow_le_pow_right (by norm_num) ?_⟩) hNTIME⟩
  have hn1 : n + 1 ≤ 2 * n := by lia
  have hpow_n1 : (n + 1) ^ d_f ≤ 2 ^ d_f * n ^ d_f := by
    calc (n + 1) ^ d_f ≤ (2 * n) ^ d_f := Nat.pow_le_pow_left hn1 d_f
      _ = 2 ^ d_f * n ^ d_f := Nat.mul_pow 2 n d_f
  have hfn : f n ≤ c_f * (2 ^ d_f * n ^ d_f) :=
    (hf_le n).trans (Nat.mul_le_mul_left c_f hpow_n1)
  calc 2 * D * f n
      ≤ 2 * D * (c_f * (2 ^ d_f * n ^ d_f)) := Nat.mul_le_mul_left (2 * D) hfn
    _ = (2 * D * c_f * 2 ^ d_f) * n ^ d_f := by ring
    _ ≤ n * n ^ d_f := Nat.mul_le_mul_right (n ^ d_f) (by lia)
    _ = n ^ (d_f + 1) := (pow_succ' n d_f).symm

end Translation

end Cslib.Complexity
