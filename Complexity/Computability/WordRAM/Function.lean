/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Compile
public import Complexity.Computability.WordRAM.MapOp
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Word-valued computation by word-RAM program families

The primary computability predicates allow code and constants to depend on word size, with
one register count and a uniform bound on program length. Their `Uniform` counterparts use
one program at every width; that program may read the width, branch on it, and have
width-dependent execution time. Both permit arbitrary
admissible-width conditions, width-dependent input encodings and width-dependent time bounds.
Instruction counts include halt. Input placement follows `State.init`; loading registers and
constructing maintained representations must be part of the certified program.

The `LogWord` wrappers express the transdichotomous assumption: a positive multiple of
`logWidth 1 (size a)`, where `logWidth k n = k * (Nat.log 2 n + 1)`, is a lower
threshold, independently of input fit. Applications claiming successful execution must supply
the separate fit guarantee. Outputs also have to fit, since a machine register returns them.
No cost is assigned to the mathematical input encoding, and no conversion to Turing-machine
polynomial time is asserted.

## Main definitions

* `Program.ComputesInTime`, `WordSizeDependentProgram.ComputesInTime`: a fixed program or
  program family computes a word-valued function.
* `ComputableInTime`: existence of a family with bounded program length.
* `UniformComputableInTime`: existence of one fixed program.
* `ComputableInTimeLogWord`, `UniformComputableInTimeLogWord`: transdichotomous word-size wrappers.
* `ComputableInO`, `UniformComputableInO`: asymptotic running-time bounds.
* `ComputableInPolyTime`, `UniformComputableInPolyTime`: polynomial instruction bounds.

## Main results

* `UniformComputableInTime.computableInTime`: uniform computation gives a bounded-code family.
* `Code.computesInTime_program`: a structured certificate charges the final halt.
* `UniformComputableInPolyTime.of_code`: structured execution yields polynomial RAM time.

## References

See `WordRAM.Time` for the transdichotomous word-size convention and its sources.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B B' : Basis} {r : ℕ} {α β : Type*}

/-- One program returns `f a` at every admitted fitting width within `time a w` instructions.
The final halt is counted; the mathematical input encoding is a convention. -/
def Program.ComputesInTime (p : Program B r) (encode : ℕ → α → List ℕ)
    (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) (f : α → ℕ) : Prop :=
  ∀ a w, allowed a w → InputFits w (encode w a) →
    ∃ n, Executes w p (.init (encode w a)) (f a) n ∧ n ≤ time a w

/-- At width `w`, the selected program computes every admitted fitting input. The selected
program depends only on the width, and the running-time bound may depend on both parameters. -/
def WordSizeDependentProgram.ComputesInTime (P : WordSizeDependentProgram B r)
    (encode : ℕ → α → List ℕ) (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) (f : α → ℕ) : Prop :=
  ∀ a w, allowed a w → InputFits w (encode w a) →
    ∃ n, Executes w (P w) (.init (encode w a)) (f a) n ∧ n ≤ time a w

/-- A width-indexed family with uniformly bounded program length computes the function. -/
@[fun_prop]
def ComputableInTime (B : Basis) (f : α → ℕ) (encode : ℕ → α → List ℕ)
    (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∃ r, ∃ P : WordSizeDependentProgram B r, P.BoundedCode ∧ P.ComputesInTime encode time allowed f

/-- One program computes the function uniformly at every admitted fitting width. -/
@[fun_prop]
def UniformComputableInTime (B : Basis) (f : α → ℕ) (encode : ℕ → α → List ℕ)
    (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∃ r, ∃ p : Program B r, p.ComputesInTime encode time allowed f

/-- Computation under the transdichotomous word-size assumption: every fitting width
above some positive multiple of the logarithmic input size is admitted. -/
@[fun_prop]
def ComputableInTimeLogWord (B : Basis) (f : α → ℕ) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) (time : α → ℕ → ℕ) : Prop :=
  ∃ k, 0 < k ∧ ComputableInTime B f encode time (fun a w => logWidth k (size a) ≤ w)

/-- Uniform computation under the transdichotomous word-size assumption. The fixed
program may read the width and have width-dependent execution time. -/
@[fun_prop]
def UniformComputableInTimeLogWord (B : Basis) (f : α → ℕ) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) (time : α → ℕ → ℕ) : Prop :=
  ∃ k, 0 < k ∧ UniformComputableInTime B f encode time (fun a w => logWidth k (size a) ≤ w)

/-- Correct computation on every admitted fitting input, with an eventual runtime bound using
one positive multiplicative constant and one size threshold shared by every admitted width. -/
@[fun_prop]
def ComputableInO (B : Basis) (f : α → ℕ) (encode : ℕ → α → List ℕ) (size : α → ℕ)
    (T : ℕ → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∃ time, ComputableInTime B f encode time allowed ∧
    ∃ c n₀, 0 < c ∧ ∀ a w, n₀ ≤ size a → allowed a w → time a w ≤ c * T (size a) w

/-- Uniform asymptotic computation, with constants shared by every admitted width. -/
@[fun_prop]
def UniformComputableInO (B : Basis) (f : α → ℕ) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) (T : ℕ → ℕ → ℕ) (allowed : α → ℕ → Prop) : Prop :=
  ∃ time, UniformComputableInTime B f encode time allowed ∧
    ∃ c n₀, 0 < c ∧ ∀ a w, n₀ ≤ size a → allowed a w → time a w ≤ c * T (size a) w

/-- A bounded-code family computes the function in polynomially many instructions in `size a`,
at every fitting width above a positive logarithmic threshold. -/
@[fun_prop]
def ComputableInPolyTime (B : Basis) (f : α → ℕ) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) : Prop :=
  ∃ T, PolynomiallyBounded T ∧ ComputableInTimeLogWord B f encode size (fun a _ => T (size a))

/-- A fixed program computes the function in polynomially many instructions in `size a`,
at every fitting width above a positive logarithmic threshold. -/
@[fun_prop]
def UniformComputableInPolyTime (B : Basis) (f : α → ℕ) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) : Prop :=
  ∃ T, PolynomiallyBounded T ∧
    UniformComputableInTimeLogWord B f encode size (fun a _ => T (size a))

/-- Increase a fixed program's time bound and restrict its admitted widths. -/
theorem Program.ComputesInTime.mono {p : Program B r} {encode : ℕ → α → List ℕ}
    {time time' : α → ℕ → ℕ} {allowed allowed' : α → ℕ → Prop} {f : α → ℕ}
    (h : p.ComputesInTime encode time allowed f) (ht : ∀ a w, time a w ≤ time' a w)
    (ha : ∀ a w, allowed' a w → allowed a w) :
    p.ComputesInTime encode time' allowed' f := by
  intro a w hw hi
  obtain ⟨n, he, hn⟩ := h a w (ha a w hw) hi
  exact ⟨n, he, hn.trans (ht a w)⟩

/-- Increase a family's time bound and restrict its admitted widths. -/
theorem WordSizeDependentProgram.ComputesInTime.mono {P : WordSizeDependentProgram B r}
    {encode : ℕ → α → List ℕ} {time time' : α → ℕ → ℕ}
    {allowed allowed' : α → ℕ → Prop} {f : α → ℕ}
    (h : P.ComputesInTime encode time allowed f) (ht : ∀ a w, time a w ≤ time' a w)
    (ha : ∀ a w, allowed' a w → allowed a w) :
    P.ComputesInTime encode time' allowed' f := by
  intro a w hw hi
  obtain ⟨n, he, hn⟩ := h a w (ha a w hw) hi
  exact ⟨n, he, hn.trans (ht a w)⟩

/-- Transfer fixed-program computation along a change of instances. -/
theorem Program.ComputesInTime.recode {p : Program B r} {encode : ℕ → α → List ℕ}
    {encode' : ℕ → β → List ℕ} {time : α → ℕ → ℕ} {time' : β → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {allowed' : β → ℕ → Prop} {f : α → ℕ} {f' : β → ℕ}
    (g : α → β) (he : ∀ w a, encode w a = encode' w (g a))
    (hf : ∀ a, f a = f' (g a)) (ht : ∀ a w, time' (g a) w ≤ time a w)
    (ha : ∀ a w, allowed a w → allowed' (g a) w)
    (h : p.ComputesInTime encode' time' allowed' f') :
    p.ComputesInTime encode time allowed f := by
  intro a w hw hi
  rw [he] at hi ⊢
  rw [hf]
  obtain ⟨n, hn, hb⟩ := h (g a) w (ha a w hw) hi
  exact ⟨n, hn, hb.trans (ht a w)⟩

/-- Transfer a program family along a change of instances. -/
theorem WordSizeDependentProgram.ComputesInTime.recode {P : WordSizeDependentProgram B r}
    {encode : ℕ → α → List ℕ} {encode' : ℕ → β → List ℕ}
    {time : α → ℕ → ℕ} {time' : β → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {allowed' : β → ℕ → Prop} {f : α → ℕ} {f' : β → ℕ}
    (g : α → β) (he : ∀ w a, encode w a = encode' w (g a))
    (hf : ∀ a, f a = f' (g a)) (ht : ∀ a w, time' (g a) w ≤ time a w)
    (ha : ∀ a w, allowed a w → allowed' (g a) w)
    (h : P.ComputesInTime encode' time' allowed' f') :
    P.ComputesInTime encode time allowed f := by
  intro a w hw hi
  rw [he] at hi ⊢
  rw [hf]
  obtain ⟨n, hn, hb⟩ := h (g a) w (ha a w hw) hi
  exact ⟨n, hn, hb.trans (ht a w)⟩

/-- A fit certificate removes the conditional input-fit premise. -/
theorem WordSizeDependentProgram.ComputesInTime.of_inputFits {P : WordSizeDependentProgram B r}
    {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop}
    {f : α → ℕ} (h : P.ComputesInTime encode time allowed f)
    (hi : ∀ a w, allowed a w → InputFits w (encode w a)) :
    ∀ a w, allowed a w →
      ∃ n, Executes w (P w) (.init (encode w a)) (f a) n ∧ n ≤ time a w :=
  fun a w ha => h a w ha (hi a w ha)

/-- A uniform certificate gives a nonuniform certificate using a constant family. -/
theorem UniformComputableInTime.computableInTime {encode : ℕ → α → List ℕ}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} {f : α → ℕ}
    (h : UniformComputableInTime B f encode time allowed) :
    ComputableInTime B f encode time allowed := by
  obtain ⟨r, p, hp⟩ := h
  exact ⟨r, .const p, WordSizeDependentProgram.const_boundedCode p, hp⟩

/-- Increase an existential family's time bound and restrict its admitted widths. -/
theorem ComputableInTime.mono {encode : ℕ → α → List ℕ} {time time' : α → ℕ → ℕ}
    {allowed allowed' : α → ℕ → Prop} {f : α → ℕ}
    (h : ComputableInTime B f encode time allowed) (ht : ∀ a w, time a w ≤ time' a w)
    (ha : ∀ a w, allowed' a w → allowed a w) :
    ComputableInTime B f encode time' allowed' := by
  obtain ⟨r, P, hb, hp⟩ := h
  exact ⟨r, P, hb, hp.mono ht ha⟩

/-- Increase an existential fixed program's time bound and restrict its admitted widths. -/
theorem UniformComputableInTime.mono {encode : ℕ → α → List ℕ} {time time' : α → ℕ → ℕ}
    {allowed allowed' : α → ℕ → Prop} {f : α → ℕ}
    (h : UniformComputableInTime B f encode time allowed) (ht : ∀ a w, time a w ≤ time' a w)
    (ha : ∀ a w, allowed' a w → allowed a w) :
    UniformComputableInTime B f encode time' allowed' := by
  obtain ⟨r, p, hp⟩ := h
  exact ⟨r, p, hp.mono ht ha⟩

/-- Transfer bounded-code computation along an encoding-preserving instance map. -/
theorem ComputableInTime.recode {encode : ℕ → α → List ℕ}
    {encode' : ℕ → β → List ℕ} {time : α → ℕ → ℕ} {time' : β → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {allowed' : β → ℕ → Prop} {f : α → ℕ} {f' : β → ℕ}
    (g : α → β) (he : ∀ w a, encode w a = encode' w (g a))
    (hf : ∀ a, f a = f' (g a)) (ht : ∀ a w, time' (g a) w ≤ time a w)
    (ha : ∀ a w, allowed a w → allowed' (g a) w)
    (h : ComputableInTime B f' encode' time' allowed') :
    ComputableInTime B f encode time allowed := by
  obtain ⟨r, P, hb, hp⟩ := h
  exact ⟨r, P, hb, hp.recode g he hf ht ha⟩

/-- Transfer uniform computation along an encoding-preserving instance map. -/
theorem UniformComputableInTime.recode {encode : ℕ → α → List ℕ}
    {encode' : ℕ → β → List ℕ} {time : α → ℕ → ℕ} {time' : β → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {allowed' : β → ℕ → Prop} {f : α → ℕ} {f' : β → ℕ}
    (g : α → β) (he : ∀ w a, encode w a = encode' w (g a))
    (hf : ∀ a, f a = f' (g a)) (ht : ∀ a w, time' (g a) w ≤ time a w)
    (ha : ∀ a w, allowed a w → allowed' (g a) w)
    (h : UniformComputableInTime B f' encode' time' allowed') :
    UniformComputableInTime B f encode time allowed := by
  obtain ⟨r, p, hp⟩ := h
  exact ⟨r, p, hp.recode g he hf ht ha⟩

/-- Basis translation preserves fixed-program computation with the same instruction count. -/
theorem Program.ComputesInTime.mapOp {p : Program B r} {encode : ℕ → α → List ℕ}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} {f : α → ℕ}
    (φ : B.Hom B') (h : p.ComputesInTime encode time allowed f) :
    (p.mapOp φ).ComputesInTime encode time allowed f := by
  intro a w hw hi
  obtain ⟨n, he, hn⟩ := h a w hw hi
  exact ⟨n, (executes_mapOp_iff φ).2 he, hn⟩

/-- Basis translation preserves family computation with the same instruction count. -/
theorem WordSizeDependentProgram.ComputesInTime.mapOp {P : WordSizeDependentProgram B r}
    {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} {f : α → ℕ}
    (φ : B.Hom B') (h : P.ComputesInTime encode time allowed f) :
    (P.mapOp φ).ComputesInTime encode time allowed f := by
  intro a w hw hi
  obtain ⟨n, he, hn⟩ := h a w hw hi
  exact ⟨n, (executes_mapOp_iff φ).2 he, hn⟩

/-- Computation transfers to a basis implementing the original operations. -/
theorem ComputableInTime.mapOp {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {f : α → ℕ} (φ : B.Hom B')
    (h : ComputableInTime B f encode time allowed) :
    ComputableInTime B' f encode time allowed := by
  obtain ⟨r, P, hP, hp⟩ := h
  exact ⟨r, P.mapOp φ, hP.mapOp φ, hp.mapOp φ⟩

/-- Uniform computation transfers to a basis implementing the original operations. -/
theorem UniformComputableInTime.mapOp {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {f : α → ℕ} (φ : B.Hom B')
    (h : UniformComputableInTime B f encode time allowed) :
    UniformComputableInTime B' f encode time allowed := by
  obtain ⟨r, p, hp⟩ := h
  exact ⟨r, p.mapOp φ, hp.mapOp φ⟩

/-- Uniform logarithmic-threshold computation gives bounded-code computation. -/
theorem UniformComputableInTimeLogWord.computableInTimeLogWord {encode : ℕ → α → List ℕ}
    {size : α → ℕ} {time : α → ℕ → ℕ} {f : α → ℕ}
    (h : UniformComputableInTimeLogWord B f encode size time) :
    ComputableInTimeLogWord B f encode size time := by
  obtain ⟨k, hk, hp⟩ := h
  exact ⟨k, hk, hp.computableInTime⟩

/-- Uniform asymptotic computation gives bounded-code asymptotic computation. -/
theorem UniformComputableInO.computableInO {encode : ℕ → α → List ℕ} {size : α → ℕ}
    {T : ℕ → ℕ → ℕ} {allowed : α → ℕ → Prop} {f : α → ℕ}
    (h : UniformComputableInO B f encode size T allowed) :
    ComputableInO B f encode size T allowed := by
  obtain ⟨time, hp, ht⟩ := h
  exact ⟨time, hp.computableInTime, ht⟩

/-- Uniform polynomial computation is a special case of bounded-code polynomial computation. -/
theorem UniformComputableInPolyTime.computableInPolyTime {encode : ℕ → α → List ℕ}
    {size f : α → ℕ} (h : UniformComputableInPolyTime B f encode size) :
    ComputableInPolyTime B f encode size := by
  obtain ⟨T, hT, hp⟩ := h
  exact ⟨T, hT, hp.computableInTimeLogWord⟩

/-- Structured computation followed by halt gives the same word in one additional instruction. -/
theorem Code.computesInTime_program {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {f : α → ℕ} (c : Code B r) (out : Fin r)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      ∃ y, ExecWithin w c (.init (encode w a)) y (time a w) ∧ y.regs out = f a) :
    (c.program out).ComputesInTime encode (fun a w => time a w + 1) allowed f := by
  intro a w hw hi
  obtain ⟨y, ⟨n, hn, he⟩, hy⟩ := h a w hw hi
  exact ⟨n + 1, hy ▸ he.executes out, Nat.add_le_add_right hn 1⟩

/-- A width-indexed structured certificate includes one instruction for the final halt. -/
theorem WordSizeDependentProgram.computesInTime_program {encode : ℕ → α → List ℕ}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} {f : α → ℕ}
    (c : ℕ → Code B r) (out : Fin r)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      ∃ y, ExecWithin w (c w) (.init (encode w a)) y (time a w) ∧ y.regs out = f a) :
    WordSizeDependentProgram.ComputesInTime (fun w => (c w).program out) encode
      (fun a w => time a w + 1) allowed f := by
  intro a w hw hi
  obtain ⟨y, ⟨n, hn, he⟩, hy⟩ := h a w hw hi
  exact ⟨n + 1, hy ▸ he.executes out, Nat.add_le_add_right hn 1⟩

/-- A structured fixed-program execution certificate yields computation including halt. -/
theorem UniformComputableInTime.of_code {encode : ℕ → α → List ℕ}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} {f : α → ℕ}
    (c : Code B r) (out : Fin r)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      ∃ y, ExecWithin w c (.init (encode w a)) y (time a w) ∧ y.regs out = f a) :
    UniformComputableInTime B f encode (fun a w => time a w + 1) allowed :=
  ⟨r, c.program out, c.computesInTime_program out h⟩

/-- Structured families with uniformly bounded assembled size yield computation including halt. -/
theorem ComputableInTime.of_code {encode : ℕ → α → List ℕ}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} {f : α → ℕ}
    (c : ℕ → Code B r) (out : Fin r) (hsize : ∃ L, ∀ w, (c w).size ≤ L)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      ∃ y, ExecWithin w (c w) (.init (encode w a)) y (time a w) ∧ y.regs out = f a) :
    ComputableInTime B f encode (fun a w => time a w + 1) allowed := by
  refine ⟨r, fun w => (c w).program out, ?_,
    WordSizeDependentProgram.computesInTime_program c out h⟩
  obtain ⟨L, hL⟩ := hsize
  refine ⟨L + 1, fun w => ?_⟩
  simpa only [Code.program, List.length_append, List.length_cons, List.length_nil,
    Code.length_assemble] using Nat.add_le_add_right (hL w) 1

/-- A supplied polynomial bound for complete flat execution yields a uniform certificate. -/
theorem UniformComputableInPolyTime.of_program {encode : ℕ → α → List ℕ} {size f : α → ℕ}
    (p : Program B r) {T : ℕ → ℕ} (hT : PolynomiallyBounded T) (k : ℕ) (hk : 0 < k)
    (h : p.ComputesInTime encode (fun a _ => T (size a)) (fun a w => logWidth k (size a) ≤ w) f) :
    UniformComputableInPolyTime B f encode size := ⟨T, hT, k, hk, r, p, h⟩

/-- A supplied polynomial bound and bounded program length yield a family certificate. -/
theorem ComputableInPolyTime.of_family {encode : ℕ → α → List ℕ} {size f : α → ℕ}
    (P : WordSizeDependentProgram B r) (hP : P.BoundedCode) {T : ℕ → ℕ}
    (hT : PolynomiallyBounded T) (k : ℕ) (hk : 0 < k)
    (h : P.ComputesInTime encode (fun a _ => T (size a)) (fun a w => logWidth k (size a) ≤ w) f) :
    ComputableInPolyTime B f encode size := ⟨T, hT, k, hk, r, P, hP, h⟩

/-- Structured execution yields uniform polynomial RAM time, including the final halt. -/
theorem UniformComputableInPolyTime.of_code {encode : ℕ → α → List ℕ} {size f : α → ℕ}
    (c : Code B r) (out : Fin r) {T : ℕ → ℕ} (hT : PolynomiallyBounded T)
    (k : ℕ) (hk : 0 < k)
    (h : ∀ a w, logWidth k (size a) ≤ w → InputFits w (encode w a) →
      ∃ y, ExecWithin w c (.init (encode w a)) y (T (size a)) ∧ y.regs out = f a) :
    UniformComputableInPolyTime B f encode size := by
  apply of_program (c.program out) (hT.add (.const 1)) k hk
  exact c.computesInTime_program out h

/-- Bounded structured families yield polynomial RAM time, including the final halt. -/
theorem ComputableInPolyTime.of_code {encode : ℕ → α → List ℕ} {size f : α → ℕ}
    (c : ℕ → Code B r) (out : Fin r) (hsize : ∃ L, ∀ w, (c w).size ≤ L)
    {T : ℕ → ℕ} (hT : PolynomiallyBounded T) (k : ℕ) (hk : 0 < k)
    (h : ∀ a w, logWidth k (size a) ≤ w → InputFits w (encode w a) →
      ∃ y, ExecWithin w (c w) (.init (encode w a)) y (T (size a)) ∧ y.regs out = f a) :
    ComputableInPolyTime B f encode size :=
  ⟨fun n => T n + 1, hT.add (.const 1), k, hk, ComputableInTime.of_code c out hsize h⟩

end Cslib.WordRAM
