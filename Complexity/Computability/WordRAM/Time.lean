/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (based on edemaine/lean-trominoes @6d5b36c1)

public import Complexity.Computability.WordRAM.Defs
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Time-bounded decision on the word RAM

Time bounds and input encodings may depend on word size. A predicate `allowed : α → ℕ → Prop`
selects admissible input/width pairs. `WordSizeDependentProgram` selects code using only width,
with a fixed register count. `DecidableInTime` requires one instruction-list length bound for all
widths. Literal values may depend on width. Code selection and the input encoding are uncharged.
`UniformDecidableInTime` uses one fixed program, which may read the width, branch on it,
and have width-dependent execution time.

All contracts are conditional on `InputFits`. Empty conditions or inputs that never fit can make
them vacuous. A logarithmic lower threshold is not an input-fit certificate: word-count size alone
does not bound input words. An input-dependent width schedule can communicate advice. No effective
code/encoding selection or identification with Turing-machine complexity is asserted.

## Main definitions

* `Program.Answers`, `logWidth`: bounded-time decision of a proposition on a single input and the
  logarithmic word-size schedule `k (⌊log₂ n⌋ + 1)`.
* `WordSizeDependentProgram`, `WordSizeDependentProgram.const`: code selected by word size, with a
  fixed register count, and constant families.
* `WordSizeDependentProgram.BoundedCode`: one instruction-list length bound for every word size.
* `WordSizeDependentProgram.DecidesInTime`, `Program.DecidesInTime`, `DecidableInTime`,
  `UniformDecidableInTime`: nonuniform and uniform instruction bounds.
* `DecidableInTimeLogWord`, `UniformDecidableInTimeLogWord`: transdichotomous word-size conventions.
* `DecidableInO`, `UniformDecidableInO`: asymptotic time with constants shared by all widths.
* `LinearTime`, `PolynomialTime`, `UniformLinearTime`, `UniformPolynomialTime`: size-based classes.

## Main results

* `UniformDecidableInTime.decidableInTime`: constant families give nonuniform certificates.
* `WordSizeDependentProgram.DecidesInTime.mono`: increase time and restrict admissible widths.
* `WordSizeDependentProgram.DecidesInTime.of_inputFits`: discharge input fitting with a certificate.
* `LinearTime.polynomialTime`, `UniformLinearTime.polynomialTime`: linear time is polynomial.
* `fits_of_lt_pow`, `two_pow_logWidth_le`: polynomially bounded values fit logarithmic words,
  and a logarithmic word holds only polynomially bounded values.

## References

* [T. H. Cormen et al., *Introduction to Algorithms*][CLRS2009]
* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound with fusion
  trees*][FredmanWillard1993]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; the
  fixed-program decision predicate is adapted from its accompanying Lean formalization.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ} {α β : Type*}

/-! ## Answering a question -/

/-- `p.Answers w input b time`: run at word size `w` on `input`, the program `p` halts after at
most `time` instructions with output `1` if `b` holds and `0` otherwise. -/
def Program.Answers (p : Program B r) (w : ℕ) (input : List ℕ) (b : Prop) (time : ℕ) : Prop :=
  ∃ v n, Executes w p (.init input) v n ∧ n ≤ time ∧ v ≤ 1 ∧ (v = 1 ↔ b)

namespace Program.Answers

variable {p : Program B r} {w : ℕ} {input : List ℕ} {b b' : Prop} {time time' : ℕ}

/-- A time bound can be increased. -/
theorem mono (h : p.Answers w input b time) (ht : time ≤ time') : p.Answers w input b time' :=
  let ⟨v, n, he, hn, hv⟩ := h
  ⟨v, n, he, hn.trans ht, hv⟩

/-- Equivalent propositions have the same `Program.Answers` specification. -/
theorem congr (h : p.Answers w input b time) (hb : b ↔ b') : p.Answers w input b' time :=
  let ⟨v, n, he, hn, hv, hb'⟩ := h
  ⟨v, n, he, hn, hv, hb'.trans hb⟩

/-- A program that does not read the word size answers in the same way at every larger word
size. -/
theorem mono_width (hp : ¬p.ReadsWidth) (h : p.Answers w input b time) {w' : ℕ} (hw : w ≤ w') :
    p.Answers w' input b time :=
  let ⟨v, n, he, hn⟩ := h
  ⟨v, n, he.mono_width hp hw, hn⟩

end Program.Answers

/-! ## Word sizes and program families -/

/-- The word size `k (⌊log₂ n⌋ + 1)`, taking one digit at zero. -/
def logWidth (k n : ℕ) : ℕ := k * (Nat.log 2 n + 1)

/-- A number below `(n + 1) ^ k` fits a word of `logWidth k n` bits. -/
theorem fits_of_lt_pow {k n v : ℕ} (hv : v < (n + 1) ^ k) : Fits (logWidth k n) v := by
  have hn : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  calc v < (n + 1) ^ k := hv
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ k := Nat.pow_le_pow_left hn k
    _ = 2 ^ logWidth k n := by rw [← pow_mul, logWidth, Nat.mul_comm]

/-- Monotonicity of `logWidth` in both multiplier and size argument. -/
theorem logWidth_mono {k k' n n' : ℕ} (hk : k ≤ k') (hn : n ≤ n') :
    logWidth k n ≤ logWidth k' n' :=
  Nat.mul_le_mul hk (Nat.add_le_add_right (Nat.log_mono_right hn) 1)

/-- A word of `logWidth k n` bits holds a number polynomial in `n`. -/
theorem two_pow_logWidth_le (k n : ℕ) : 2 ^ logWidth k n ≤ 2 ^ k * (n + 1) ^ k := by
  unfold logWidth
  rw [mul_comm, pow_mul, ← mul_pow]
  refine Nat.pow_le_pow_left ?_ k
  rw [pow_succ, mul_comm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Nat.pow_log_le_self 2 hn.ne'
    omega

/-- A big-O bound on a natural-valued width schedule is an eventual upper-width condition
with a fixed positive natural multiplier. Swapping `width` and `bound` expresses a big-Omega
bound, as `bound n ≤ k * width n`; the reciprocal lower constant need not be integral. -/
theorem isBigO_natCast_iff_eventually_le_mul (width bound : ℕ → ℕ) :
    Asymptotics.IsBigO Filter.atTop (fun n => (width n : ℝ)) (fun n => (bound n : ℝ)) ↔
      ∃ k : ℕ, 0 < k ∧ ∀ᶠ n in Filter.atTop, width n ≤ k * bound n := by
  constructor
  · intro h
    obtain ⟨c, _, hc⟩ := h.exists_pos
    refine ⟨⌈c⌉₊ + 1, by omega, ?_⟩
    filter_upwards [hc.bound] with n hn
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    have hk : c ≤ ((⌈c⌉₊ + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil c).trans (by exact_mod_cast Nat.le_add_right ⌈c⌉₊ 1)
    have hb := hn.trans (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg (bound n)))
    exact_mod_cast hb
  · rintro ⟨k, _, hk⟩
    apply Asymptotics.isBigO_iff.2
    refine ⟨k, ?_⟩
    filter_upwards [hk] with n hn
    rw [Real.norm_natCast, Real.norm_natCast]
    exact_mod_cast hn

/-- Code selected using only word size, with a fixed finite register file. -/
abbrev WordSizeDependentProgram (B : Basis) (r : ℕ) := ℕ → Program B r

namespace WordSizeDependentProgram

/-- One instruction-list length bound works at every width. Literal values may depend on width;
no computability or construction cost for selecting code is asserted. -/
def BoundedCode (P : WordSizeDependentProgram B r) : Prop := ∃ L, ∀ w, (P w).length ≤ L

/-- The constant family associated to a uniform program. -/
def const (p : Program B r) : WordSizeDependentProgram B r := fun _ => p

/-- Constant families have bounded code. -/
theorem const_boundedCode (p : Program B r) : (const p).BoundedCode :=
  ⟨p.length, fun _ => le_rfl⟩

/-- A family answers correctly within a width-dependent bound on every admitted fitting input.
The raw contract does not impose a code-length bound. -/
def DecidesInTime (P : WordSizeDependentProgram B r) (encode : ℕ → α → List ℕ) (A : Set α)
    (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∀ a w, allowed a w → InputFits w (encode w a) →
    (P w).Answers w (encode w a) (a ∈ A) (time a w)

variable {P : WordSizeDependentProgram B r} {encode : ℕ → α → List ℕ} {A : Set α}
  {time time' : α → ℕ → ℕ} {allowed allowed' : α → ℕ → Prop}

/-- Increase time and restrict admitted input/width pairs. -/
theorem DecidesInTime.mono (h : P.DecidesInTime encode A time allowed)
    (ht : ∀ a w, time a w ≤ time' a w) (hw : ∀ a w, allowed' a w → allowed a w) :
    P.DecidesInTime encode A time' allowed' :=
  fun a w ha hi => (h a w (hw a w ha) hi).mono (ht a w)

/-- A fit certificate removes the conditional input-fit premise. -/
theorem DecidesInTime.of_inputFits (h : P.DecidesInTime encode A time allowed)
    (hi : ∀ a w, allowed a w → InputFits w (encode w a)) :
    ∀ a w, allowed a w → (P w).Answers w (encode w a) (a ∈ A) (time a w) :=
  fun a w ha => h a w ha (hi a w ha)

/-- Evaluate a family contract along any admitted width schedule. -/
theorem DecidesInTime.at_width (h : P.DecidesInTime encode A time allowed)
    (width : α → ℕ) (hw : ∀ a, allowed a (width a)) :
    ∀ a, InputFits (width a) (encode (width a) a) →
      (P (width a)).Answers (width a) (encode (width a) a) (a ∈ A) (time a (width a)) :=
  fun a hi => h a (width a) (hw a) hi

/-- Transfer without a charged conversion when the encoded input words agree. -/
theorem DecidesInTime.recode {encode' : ℕ → β → List ℕ} {A' : Set β}
    {timeB : β → ℕ → ℕ} {allowedB : β → ℕ → Prop} (f : α → β)
    (hf : ∀ w a, encode w a = encode' w (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (ht : ∀ a w, timeB (f a) w ≤ time a w)
    (hw : ∀ a w, allowed a w → allowedB (f a) w)
    (h : P.DecidesInTime encode' A' timeB allowedB) : P.DecidesInTime encode A time allowed :=
  fun a w ha hi => by
    rw [hf] at hi ⊢
    exact ((h (f a) w (hw a w ha) hi).mono (ht a w)).congr (hA a).symm

end WordSizeDependentProgram

/-- One fixed program answers correctly at every admitted fitting width. Reading word size is
allowed; uniformity concerns code selection, not the runtime or execution path. -/
def Program.DecidesInTime (p : Program B r) (encode : ℕ → α → List ℕ) (A : Set α)
    (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  (WordSizeDependentProgram.const p).DecidesInTime encode A time allowed

/-- Nonuniform decision: width selects code, with one register count and one code-length bound
shared by every width. The time bound and encoding may depend on width. -/
def DecidableInTime (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ)
    (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∃ r, ∃ P : WordSizeDependentProgram B r, P.BoundedCode ∧ P.DecidesInTime encode A time allowed

/-- Uniform decision by one fixed program, possibly reading word size. -/
def UniformDecidableInTime (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ)
    (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∃ r, ∃ p : Program B r, p.DecidesInTime encode A time allowed

variable {encode : ℕ → α → List ℕ} {A : Set α}
  {time time' : α → ℕ → ℕ} {allowed allowed' : α → ℕ → Prop}

/-- Increase time and restrict admissible widths for a fixed program. -/
theorem Program.DecidesInTime.mono {p : Program B r}
    (h : p.DecidesInTime encode A time allowed) (ht : ∀ a w, time a w ≤ time' a w)
    (hw : ∀ a w, allowed' a w → allowed a w) :
    p.DecidesInTime encode A time' allowed' :=
  WordSizeDependentProgram.DecidesInTime.mono h ht hw

/-- A fixed program gives a bounded nonuniform family. -/
theorem UniformDecidableInTime.decidableInTime
    (h : UniformDecidableInTime B A encode time allowed) :
    DecidableInTime B A encode time allowed :=
  let ⟨r, p, hp⟩ := h
  ⟨r, .const p, WordSizeDependentProgram.const_boundedCode p, hp⟩

/-- Increase time and restrict admitted widths without changing code. -/
theorem DecidableInTime.mono (h : DecidableInTime B A encode time allowed)
    (ht : ∀ a w, time a w ≤ time' a w) (hw : ∀ a w, allowed' a w → allowed a w) :
    DecidableInTime B A encode time' allowed' :=
  let ⟨r, P, hP, hp⟩ := h
  ⟨r, P, hP, hp.mono ht hw⟩

/-- Increase time and restrict admitted widths for a uniform certificate. -/
theorem UniformDecidableInTime.mono (h : UniformDecidableInTime B A encode time allowed)
    (ht : ∀ a w, time a w ≤ time' a w) (hw : ∀ a w, allowed' a w → allowed a w) :
    UniformDecidableInTime B A encode time' allowed' :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, hp.mono ht hw⟩

/-- Transfer nonuniform decision along a map preserving encoded words. -/
theorem DecidableInTime.recode {encode' : ℕ → β → List ℕ} {A' : Set β}
    {timeB : β → ℕ → ℕ} {allowedB : β → ℕ → Prop} (f : α → β)
    (hf : ∀ w a, encode w a = encode' w (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (ht : ∀ a w, timeB (f a) w ≤ time a w)
    (hw : ∀ a w, allowed a w → allowedB (f a) w)
    (h : DecidableInTime B A' encode' timeB allowedB) : DecidableInTime B A encode time allowed :=
  let ⟨r, P, hP, hp⟩ := h
  ⟨r, P, hP, hp.recode f hf hA ht hw⟩

/-- Transfer uniform decision along a map preserving encoded words. -/
theorem UniformDecidableInTime.recode {encode' : ℕ → β → List ℕ} {A' : Set β}
    {timeB : β → ℕ → ℕ} {allowedB : β → ℕ → Prop} (f : α → β)
    (hf : ∀ w a, encode w a = encode' w (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (ht : ∀ a w, timeB (f a) w ≤ time a w)
    (hw : ∀ a w, allowed a w → allowedB (f a) w)
    (h : UniformDecidableInTime B A' encode' timeB allowedB) :
    UniformDecidableInTime B A encode time allowed :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p, WordSizeDependentProgram.DecidesInTime.recode f hf hA ht hw hp⟩

/-! ## The transdichotomous word-size assumption and asymptotic time -/

/-- Nonuniform decision under the transdichotomous word-size assumption: every fitting
width above some positive multiple of the logarithmic input size is admitted.
This lower threshold is not an input-fit guarantee. -/
def DecidableInTimeLogWord (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) (time : α → ℕ → ℕ) : Prop :=
  ∃ k, 0 < k ∧ DecidableInTime B A encode time (fun a w => logWidth k (size a) ≤ w)

/-- Uniform decision under the transdichotomous word-size assumption. The fixed program
may read the width and have width-dependent execution time. -/
def UniformDecidableInTimeLogWord (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) (time : α → ℕ → ℕ) : Prop :=
  ∃ k, 0 < k ∧ UniformDecidableInTime B A encode time (fun a w => logWidth k (size a) ≤ w)

/-- A uniform logarithmic-threshold certificate is nonuniform as well. -/
theorem UniformDecidableInTimeLogWord.decidableInTimeLogWord {size : α → ℕ}
    (h : UniformDecidableInTimeLogWord B A encode size time) :
    DecidableInTimeLogWord B A encode size time :=
  let ⟨k, hk, hd⟩ := h
  ⟨k, hk, hd.decidableInTime⟩

/-- Asymptotic nonuniform time `T n w`. Correctness holds on every admitted fitting input;
one positive constant and one size threshold bound the runtime at all admitted widths. -/
def DecidableInO (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ) (size : α → ℕ)
    (T : ℕ → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∃ time, DecidableInTime B A encode time allowed ∧
    ∃ c n₀, 0 < c ∧ ∀ a w, n₀ ≤ size a → allowed a w → time a w ≤ c * T (size a) w

/-- Uniform asymptotic time, with correctness on all admitted fitting inputs and one eventual
runtime estimate shared by every width. -/
def UniformDecidableInO (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ) (size : α → ℕ)
    (T : ℕ → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∃ time, UniformDecidableInTime B A encode time allowed ∧
    ∃ c n₀, 0 < c ∧ ∀ a w, n₀ ≤ size a → allowed a w → time a w ≤ c * T (size a) w

/-- Uniform asymptotic decision implies nonuniform asymptotic decision. -/
theorem UniformDecidableInO.decidableInO {size : α → ℕ} {T : ℕ → ℕ → ℕ}
    (h : UniformDecidableInO B A encode size T allowed) :
    DecidableInO B A encode size T allowed :=
  let ⟨time, hd, hb⟩ := h
  ⟨time, hd.decidableInTime, hb⟩

/-! ## Linear and polynomial time -/

/-- Nonuniform linear instruction time above a logarithmic lower threshold. Code length and
the time and threshold constants are bounded independently of width. -/
def LinearTime (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ) (size : α → ℕ) : Prop :=
  ∃ c, DecidableInTimeLogWord B A encode size (fun a _ => c * (size a + 1))

/-- Uniform linear instruction time above a logarithmic lower threshold. -/
def UniformLinearTime (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) : Prop :=
  ∃ c, UniformDecidableInTimeLogWord B A encode size (fun a _ => c * (size a + 1))

/-- Nonuniform polynomial instruction time in size above a logarithmic lower threshold.
This does not assert effective code selection or Turing-machine computability. -/
def PolynomialTime (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ) (size : α → ℕ) : Prop :=
  ∃ T, PolynomiallyBounded T ∧ DecidableInTimeLogWord B A encode size (fun a _ => T (size a))

/-- Uniform polynomial instruction time in size above a logarithmic lower threshold. -/
def UniformPolynomialTime (B : Basis) (A : Set α) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) : Prop :=
  ∃ T, PolynomiallyBounded T ∧ UniformDecidableInTimeLogWord B A encode size (fun a _ => T (size a))

/-- Uniform linear time implies nonuniform linear time. -/
theorem UniformLinearTime.linearTime {size : α → ℕ} (h : UniformLinearTime B A encode size) :
    LinearTime B A encode size :=
  let ⟨c, hd⟩ := h
  ⟨c, hd.decidableInTimeLogWord⟩

/-- Uniform polynomial time implies nonuniform polynomial time. -/
theorem UniformPolynomialTime.polynomialTime {size : α → ℕ}
    (h : UniformPolynomialTime B A encode size) : PolynomialTime B A encode size :=
  let ⟨T, hT, hd⟩ := h
  ⟨T, hT, hd.decidableInTimeLogWord⟩

/-- Linear time is polynomial time, using the same family. -/
theorem LinearTime.polynomialTime {size : α → ℕ} (h : LinearTime B A encode size) :
    PolynomialTime B A encode size :=
  let ⟨c, hd⟩ := h
  ⟨fun n => c * (n + 1), polynomiallyBounded_iff_le.2 ⟨c, 1, fun n => by simp⟩, hd⟩

/-- Uniform linear time is uniform polynomial time, using the same program. -/
theorem UniformLinearTime.polynomialTime {size : α → ℕ} (h : UniformLinearTime B A encode size) :
    UniformPolynomialTime B A encode size :=
  let ⟨c, hd⟩ := h
  ⟨fun n => c * (n + 1), polynomiallyBounded_iff_le.2 ⟨c, 1, fun n => by simp⟩, hd⟩

/-- Linear time transfers without charged conversion when words and sizes agree. -/
theorem LinearTime.recode {encode' : ℕ → β → List ℕ} {A' : Set β} {size : α → ℕ}
    {size' : β → ℕ} (f : α → β) (hf : ∀ w a, encode w a = encode' w (f a))
    (hs : ∀ a, size a = size' (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (h : LinearTime B A' encode' size') : LinearTime B A encode size :=
  let ⟨c, k, hk, hd⟩ := h
  ⟨c, k, hk, hd.recode f hf hA (fun a _ => by rw [hs]) (fun a _ ha => by
      simpa only [hs] using ha)⟩

/-- Uniform linear time transfers when words and sizes agree. -/
theorem UniformLinearTime.recode {encode' : ℕ → β → List ℕ} {A' : Set β} {size : α → ℕ}
    {size' : β → ℕ} (f : α → β) (hf : ∀ w a, encode w a = encode' w (f a))
    (hs : ∀ a, size a = size' (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (h : UniformLinearTime B A' encode' size') : UniformLinearTime B A encode size :=
  let ⟨c, k, hk, hd⟩ := h
  ⟨c, k, hk, hd.recode f hf hA (fun a _ => by rw [hs]) (fun a _ ha => by
      simpa only [hs] using ha)⟩

/-- Polynomial time transfers when words and sizes agree. -/
theorem PolynomialTime.recode {encode' : ℕ → β → List ℕ} {A' : Set β} {size : α → ℕ}
    {size' : β → ℕ} (f : α → β) (hf : ∀ w a, encode w a = encode' w (f a))
    (hs : ∀ a, size a = size' (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (h : PolynomialTime B A' encode' size') : PolynomialTime B A encode size :=
  let ⟨T, hT, k, hk, hd⟩ := h
  ⟨T, hT, k, hk, hd.recode f hf hA (fun a _ => by rw [hs])
    (fun a _ ha => by
      simpa only [hs] using ha)⟩

/-- Uniform polynomial time transfers when words and sizes agree. -/
theorem UniformPolynomialTime.recode {encode' : ℕ → β → List ℕ} {A' : Set β} {size : α → ℕ}
    {size' : β → ℕ} (f : α → β) (hf : ∀ w a, encode w a = encode' w (f a))
    (hs : ∀ a, size a = size' (f a)) (hA : ∀ a, a ∈ A ↔ f a ∈ A')
    (h : UniformPolynomialTime B A' encode' size') : UniformPolynomialTime B A encode size :=
  let ⟨T, hT, k, hk, hd⟩ := h
  ⟨T, hT, k, hk, hd.recode f hf hA (fun a _ => by rw [hs])
    (fun a _ ha => by
      simpa only [hs] using ha)⟩

end Cslib.WordRAM

end
