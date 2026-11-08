/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.Invariance
public import Complexity.Computability.Kolmogorov.SelfDelimiting
public import Complexity.Foundations.Data.Nat.Primrec
public import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List

/-!
# Partial recursive description methods and the invariance theorem

A code `c` of a partial recursive function (Mathlib's `Nat.Partrec.Code`) gives a description
method `ofCode c` for natural numbers: a program `p` is the input `encode p` of `c`, and after `t`
steps its output is `Nat.Partrec.Code.evaln t c (encode p)`, the result of evaluating `c` with
fuel `t`. More generally, a description method is *partial recursive* (`IsPartrec`) when a partial
recursive function of the programs has exactly its outputs, whatever its clock.

The *universal* description method `universal` reads a program as the self-delimiting code of the
binary representation of `encode c`, for a code `c`, followed by a program `p`, and runs `p` under
`ofCode c`, with the same clock. The header of `c` costs a constant number of bits, so `universal`
is at most a constant worse than `ofCode c` (`ecomplexity_universal_le`). It is itself partial
recursive, since the decoder of the self-delimiting code is primitive recursive and evaluating
codes is partial recursive (`Nat.Partrec.Code.eval_part`), and every partial recursive method has
the outputs of some `ofCode c`. So `universal` is additively optimal for the class of partial
recursive description methods: this is the invariance theorem of Kolmogorov complexity
[Li and Vitányi, Section 2.1][LiVitanyi2019], and by
`Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal.invariance` any two additively optimal
partial recursive methods have complexities within an additive constant of each other. Every
natural number has a description under `universal`, so its complexity is a natural number
(`natCast_complexity_universal`).

The simulation of `ofCode c` by `universal` has no time overhead, which gives the time-bounded
invariance `C_U^t(x) ≤ C_{ofCode c}^t(x) + |header c|`
(`etimeBoundedComplexity_universal_le`). Its clock, however, is the fuel of `evaln`, which bounds
the depth of the evaluation and the size of the numbers it inspects rather than counting the steps
of a machine; time-bounded complexity for a machine model needs a universal machine for that model.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.ofCode`: the description method of a code.
* `Cslib.Kolmogorov.DescriptionMethod.IsPartrec`: partial recursive description methods.
* `Cslib.Kolmogorov.DescriptionMethod.codeHeader`: the header announcing a code.
* `Cslib.Kolmogorov.DescriptionMethod.universal`: the universal description method.
* `Cslib.Kolmogorov.DescriptionMethod.universalSimulation`: the simulation of `ofCode c` by
  `universal`.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.ofCode_produces_iff`: `ofCode c` describes `x` by `p`
  exactly when `c` outputs `x` on `encode p`.
* `Cslib.Kolmogorov.primrec_decodeSelfDelimiting`: the decoder of the self-delimiting code is
  primitive recursive.
* `Cslib.Kolmogorov.DescriptionMethod.isPartrec_universal`: the universal method is partial
  recursive.
* `Cslib.Kolmogorov.DescriptionMethod.isAdditivelyOptimal_universal`: the **invariance theorem**.
* `Cslib.Kolmogorov.DescriptionMethod.IsPartrec.of_partrec_eval`,
  `Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universal_le_of_partrec_eval`: generic
  partial-recursiveness and additive-optimality bridges for description methods with a `Partrec`
  evaluation function.
* `Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universal_le_of_partrec`: a partial
  recursive decoder costs a constant number of extra bits.
* `Cslib.Kolmogorov.DescriptionMethod.primrec₂_universal_runFor`: the clocked runs of `universal`
  are primitive recursive.
* `Cslib.Kolmogorov.DescriptionMethod.ecomplexity_universal_le`,
  `Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_universal_le`: the constant is the
  length of the header.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

@[expose] public section

namespace Cslib.Kolmogorov

open Encodable Denumerable Nat.Partrec

/-- The decoder of the self-delimiting code is primitive recursive. -/
theorem primrec_decodeSelfDelimiting : Primrec decodeSelfDelimiting := by
  have hk : Primrec fun q : List Bool => q.idxOf false :=
    Primrec.list_idxOf.comp (Primrec.const false) Primrec.id
  have hr : Primrec fun q : List Bool => q.drop (q.idxOf false + 1) :=
    Primrec.list_drop.comp (Primrec.succ.comp hk) Primrec.id
  have hn := Primrec.list_foldr_nat_bit.comp (Primrec.list_take.comp hk hr)
  have hs := Primrec.list_drop.comp hk hr
  exact (Primrec.pair (Primrec.list_take.comp hn hs) (Primrec.list_drop.comp hn hs)).of_eq
    fun _ => rfl

namespace DescriptionMethod

/-! ### The description method of a code -/

/-- The description method of the code `c` of a partial recursive function: the program `p` is the
input `encode p` of `c`, and after `t` steps its output is `Code.evaln t c (encode p)`, the result
of evaluating `c` with fuel `t`. -/
def ofCode (c : Code) : DescriptionMethod ℕ where
  run p := ⟨fun t => Code.evaln t c (encode p), fun t _ h => Code.evaln_mono t.le_succ h⟩

variable {c : Code} {p : List Bool} {t x : ℕ}

theorem mem_ofCode_runFor : x ∈ ((ofCode c).run p).runFor t ↔ x ∈ Code.evaln t c (encode p) :=
  Iff.rfl

/-- A program describes `x` under `ofCode c` exactly when `c` outputs `x` on its encoding. -/
@[simp]
theorem ofCode_produces_iff : (ofCode c).Produces p x ↔ x ∈ c.eval (encode p) :=
  produces_iff_exists_mem_runFor.trans Code.evaln_complete.symm

/-! ### Partial recursive description methods -/

/-- A description method for natural numbers is *partial recursive* when a partial recursive
function of the programs has exactly its outputs. Nothing is assumed about its clock. -/
def IsPartrec (M : DescriptionMethod ℕ) : Prop :=
  ∃ f : List Bool →. ℕ, Partrec f ∧ ∀ p x, M.Produces p x ↔ x ∈ f p

theorem isPartrec_ofCode (c : Code) : (ofCode c).IsPartrec :=
  ⟨fun p => c.eval (encode p), Code.eval_part.comp (Computable.const c) Computable.encode,
    fun _ _ => ofCode_produces_iff⟩

/-- A partial recursive description method has the outputs of the description method of some
code. -/
theorem IsPartrec.exists_produces_iff {M : DescriptionMethod ℕ} (h : M.IsPartrec) :
    ∃ c : Code, ∀ p x, M.Produces p x ↔ (ofCode c).Produces p x := by
  obtain ⟨f, hf, hM⟩ := h
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  refine ⟨c, fun p x => ?_⟩
  rw [hM, ofCode_produces_iff, hc]
  simp

/-- If `M : DescriptionMethod α` has a partial recursive evaluation function `eval : List Bool →. α`
characterizing `M.Produces`, then mapping any computable decoder `dec : α → ℕ` over `M` yields a
partial recursive description method. -/
theorem IsPartrec.of_partrec_eval {α : Type*} [Primcodable α] {M : DescriptionMethod α}
    {eval : List Bool →. α} (heval : Partrec eval) (hprod : ∀ p x, M.Produces p x ↔ x ∈ eval p)
    {dec : α → ℕ} (hdec : Computable dec) :
    (M.map dec).IsPartrec := by
  refine ⟨fun p => (eval p).map dec, heval.map (hdec.comp Computable.snd).to₂, fun p n => ?_⟩
  simp [Part.mem_map_iff, hprod]

/-! ### The universal description method -/

/-- The header announcing the code `c` to the universal method: the self-delimiting code of the
binary representation of `encode c`. -/
def codeHeader (c : Code) : List Bool :=
  selfDelimitingCode (encode c).bits

theorem length_codeHeader (c : Code) :
    (codeHeader c).length = (encode c).size + (2 * (encode c).size.size + 1) := by
  rw [codeHeader, length_selfDelimitingCode, Nat.size_eq_bits_len]

/-- The *universal* description method: the decoder of the self-delimiting code splits a program
into the binary representation of a number `n` and a program `p` (`decodeSelfDelimiting`), and `p`
runs under the description method of the code `ofNat Code n`, with the same clock. -/
def universal : DescriptionMethod ℕ where
  run q := (ofCode (ofNat Code ((decodeSelfDelimiting q).1.foldr Nat.bit 0))).run
    (decodeSelfDelimiting q).2

@[simp]
theorem universal_run_codeHeader_append (c : Code) (p : List Bool) :
    universal.run (codeHeader c ++ p) = (ofCode c).run p := by
  simp [universal, codeHeader]

theorem universal_produces_codeHeader_append :
    universal.Produces (codeHeader c ++ p) x ↔ (ofCode c).Produces p x := by
  rw [Produces, universal_run_codeHeader_append, Produces]

/-- The universal description method is partial recursive. -/
theorem isPartrec_universal : universal.IsPartrec := by
  have hd := primrec_decodeSelfDelimiting
  refine ⟨fun q => (ofNat Code ((decodeSelfDelimiting q).1.foldr Nat.bit 0)).eval
    (encode (decodeSelfDelimiting q).2), ?_, fun _ _ => ofCode_produces_iff⟩
  exact Code.eval_part.comp
    ((Computable.ofNat Code).comp (Primrec.list_foldr_nat_bit.comp (Primrec.fst.comp hd)).to_comp)
    (Computable.encode.comp (Primrec.snd.comp hd).to_comp)

/-- The universal method simulates the description method of every code `c`, with the header of
`c` as program overhead and no time overhead. -/
def universalSimulation (c : Code) :
    Simulation (ofCode c) universal (codeHeader c).length fun _ t => t where
  compile p := codeHeader c ++ p
  length_compile_le p := by rw [List.length_append, Nat.add_comm]
  mem_runFor_compile h := by rwa [universal_run_codeHeader_append]

/-- **Invariance**: the universal method is at most `|codeHeader c|` worse than the description
method of the code `c`. -/
theorem ecomplexity_universal_le (c : Code) (x : ℕ) :
    universal.ecomplexity x ≤ (ofCode c).ecomplexity x + (codeHeader c).length :=
  (universalSimulation c).ecomplexity_le x

/-- **Time-bounded invariance** for the clock of `evaln`: the universal method is at most
`|codeHeader c|` worse than the description method of the code `c`, within the same fuel. -/
theorem etimeBoundedComplexity_universal_le (c : Code) (t x : ℕ) :
    universal.etimeBoundedComplexity t x ≤
      (ofCode c).etimeBoundedComplexity t x + (codeHeader c).length :=
  (universalSimulation c).etimeBoundedComplexity_le (σ := id) t x

/-- **Invariance theorem** [Li and Vitányi, Section 2.1][LiVitanyi2019]. The universal method is
additively optimal for the class of partial recursive description methods: it is partial
recursive, and at most a constant worse than every partial recursive description method. -/
theorem isAdditivelyOptimal_universal : universal.IsAdditivelyOptimal {M | M.IsPartrec} :=
  isAdditivelyOptimal_of_simulation isPartrec_universal fun M hM => by
    obtain ⟨c, hc⟩ := IsPartrec.exists_produces_iff hM
    obtain ⟨τ, hS⟩ := exists_simulation_of_produces (M := M) (N := universal)
      (codeHeader c ++ ·) (fun p => by rw [List.length_append, Nat.add_comm])
      fun hp => universal_produces_codeHeader_append.mpr ((hc _ _).mp hp)
    exact ⟨_, τ, hS⟩

/-- If `M : DescriptionMethod α` has a partial recursive evaluation function `eval : List Bool →. α`
characterizing `M.Produces`, then for every computable decoder `dec : α → ℕ`, `universal` is at most
an additive constant worse than `M`. -/
theorem exists_ecomplexity_universal_le_of_partrec_eval {α : Type*} [Primcodable α]
    {M : DescriptionMethod α} {eval : List Bool →. α} (heval : Partrec eval)
    (hprod : ∀ p x, M.Produces p x ↔ x ∈ eval p) {dec : α → ℕ} (hdec : Computable dec) :
    ∃ c : ℕ, ∀ x : α, universal.ecomplexity (dec x) ≤ M.ecomplexity x + c := by
  obtain ⟨c, hc⟩ := isAdditivelyOptimal_universal.exists_ecomplexity_le (M.map dec)
    (IsPartrec.of_partrec_eval heval hprod hdec)
  exact ⟨c, fun x => (hc (dec x)).trans (add_le_add_left (M.ecomplexity_map_le dec x) c)⟩

/-- **Invariance for partial recursive decoders**: if a partial recursive function `f` outputs `x`
on the program `q`, then `x` has a description under `universal` at most a constant longer than
`q`, the constant depending only on `f`. -/
theorem exists_ecomplexity_universal_le_of_partrec {f : List Bool →. ℕ} (hf : Partrec f) :
    ∃ c : ℕ, ∀ q x, x ∈ f q → universal.ecomplexity x ≤ q.length + c := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  refine ⟨(codeHeader c).length, fun q x hx => ?_⟩
  have h : universal.Produces (codeHeader c ++ q) x := by
    rw [universal_produces_codeHeader_append, ofCode_produces_iff, hc]
    simpa using hx
  exact (ecomplexity_le_length h).trans (by rw [List.length_append, Nat.cast_add, add_comm])

/-- The clocked runs of the universal method are primitive recursive in the program and the
fuel. -/
theorem primrec₂_universal_runFor :
    Primrec₂ fun (q : List Bool) (t : ℕ) => (universal.run q).runFor t := by
  have hd := primrec_decodeSelfDelimiting
  exact Primrec₂.mk <| (Code.primrec_evaln.comp (Primrec.pair (Primrec.pair Primrec.snd
    ((Primrec.ofNat Code).comp
      (Primrec.list_foldr_nat_bit.comp (Primrec.fst.comp (hd.comp Primrec.fst)))))
    (Primrec.encode.comp (Primrec.snd.comp (hd.comp Primrec.fst))))).of_eq fun _ => rfl

/-- Every natural number has a description under the universal method. -/
theorem ecomplexity_universal_ne_top (x : ℕ) : universal.ecomplexity x ≠ ⊤ :=
  ecomplexity_ne_top_iff.mpr ⟨codeHeader (Code.const x) ++ [],
    universal_produces_codeHeader_append.mpr (by simp)⟩

@[simp]
theorem natCast_complexity_universal (x : ℕ) :
    (universal.complexity x : ℕ∞) = universal.ecomplexity x :=
  natCast_complexity (ecomplexity_universal_ne_top x)

end DescriptionMethod

end Cslib.Kolmogorov
