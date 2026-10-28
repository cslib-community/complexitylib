/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Output
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
public import Complexity.Logics.FirstOrder.Interpretation.Rank
import Complexity.Foundations.Data.List.Lookup

/-!
# The domain-counting interpretation transducer

A first-order interpretation whose formulas are written in a language `Ls` is computed, on
encoded finite relational structures, by one logarithmic-space transducer. The language `Ls` is
the input vocabulary itself for order-free interpretations, or its canonical numeric expansion for
ordered ones; a `FormulaCompiler` supplies the atomic handlers for `Ls`, the least admissible
input cardinality, and the semantics of `Ls` on admissible inputs.

The transducer checks the input shape and cardinality, counts the tuples satisfying the domain
formula to emit the unary output cardinality, and emits each relation table by repeatedly
reconstructing the tuples of the requested ranks. Tuples are numbered through a fixed
enumeration `e : ι ≃ Fin d` of the coordinates (`tupleEquiv e`); lexicographic order is the
instance `e = Fin.revPerm`. Each loop counter is polynomially bounded in the input length; the
counter-program simulation therefore supplies a total `ComputableInLogSpace` machine. Neither the
output structure nor its tables are stored.

Inputs with invalid table shapes or a cardinality below the compiler's bound map to a fixed
malformed target instance. Raw bit strings outside the image of `encStructure` are outside the
encoded-input contract. Empty domains, nullary relations and zero-dimensional interpretations are
included.

## Main definitions

* `Cslib.Logic.Vocabulary.ModelChecker.FormulaCompiler`: atomic handlers with their semantics and
  admissibility bound.
* `Cslib.Logic.FO.Interpretation.encodedMapWith`: the encoded interpreted structure, numbered by
  domain rank, with inadmissible inputs sent to a malformed target encoding.

## Main results

* `Cslib.Logic.FO.Interpretation.computableInLogSpace_encodedMapWith`: the encoded map has a total
  logarithmic-space transducer.

## References

* [N. Immerman, *Descriptive Complexity*, Theorem 3.1][Immerman1999]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

universe u v u' v' u'' v''

open FirstOrder Language Structure Turing Turing.CounterProgram

namespace Cslib.Logic

namespace Vocabulary.ModelChecker

/-- A formula compiler for the domain-counting transducer, over input vocabulary `v` and formula
language `Ls`: the least admissible cardinality `minCard`, the structure on `Ls` built from the
decoded input on admissible cardinalities, and atomic handlers that realize it on every well-formed
admissible input. -/
structure FormulaCompiler {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)
    (Ls : Language.{u', v'}) where
  /-- The least admissible input cardinality. -/
  minCard : ℕ
  /-- The `Ls`-structure on an admissible universe, from its input relations. -/
  expand : ∀ {n : ℕ}, minCard ≤ n → L.Structure (Fin n) → Ls.Structure (Fin n)
  /-- The atomic handlers, for free variables in registers `fv` and bound variables from `base`. -/
  atomic : ∀ {α : Type}, (α → ℕ) → ℕ → AtomicCompiler Ls α
  /-- The handlers realize the expanded structure on well-formed admissible inputs. -/
  atomic_correct : ∀ {a : EncodedStructure}, v.WellFormed a → ∀ (hn : minCard ≤ a.1) {α : Type}
    (fv : α → ℕ) (base : ℕ) (val : α → Fin a.1),
    letI := expand hn (v.decode a)
    (atomic fv base).Correct (encStructure a) fv base val

end Vocabulary.ModelChecker

namespace FO.Interpretation

open Vocabulary.ModelChecker

section Output

variable {L : Language.{u, v}} [L.IsRelational] {v : Vocabulary L} {Ls : Language.{u', v'}}
  {L' : Language.{u'', v''}} [L'.IsRelational] {ι : Type} {d : ℕ}
  (I : Interpretation Ls L' ι) (C : FormulaCompiler v Ls) (v' : Vocabulary L') (e : ι ≃ Fin d)

/-- Encode the structure interpreted by `I` in an admissible input, with the formula semantics of
`C`, numbering its elements by the ranks of their tuple indices under `e`. Malformed inputs and
cardinalities below `C.minCard` map to a fixed malformed structure encoding. -/
noncomputable def encodedMapWith (a : EncodedStructure) : EncodedStructure :=
  if h : v.WellFormed a ∧ C.minCard ≤ a.1 then
    letI := C.expand h.2 (v.decode a)
    v'.encode (I.Model (Fin a.1)) (rankEquiv I e a.1)
  else (0, List.replicate (v'.count + 1) [])

variable {a : EncodedStructure}

theorem encodedMapWith_of_admissible (ha : v.WellFormed a) (hn : C.minCard ≤ a.1) :
    I.encodedMapWith C v' e a = (letI := C.expand hn (v.decode a);
      v'.encode (I.Model (Fin a.1)) (rankEquiv I e a.1)) :=
  dite_eq_left ⟨ha, hn⟩

theorem encodedMapWith_of_not_admissible (ha : ¬(v.WellFormed a ∧ C.minCard ≤ a.1)) :
    I.encodedMapWith C v' e a = (0, List.replicate (v'.count + 1) []) :=
  dite_eq_right ha

/-- The output cardinality is the number of domain tuples. -/
theorem card_encodedMapWith (ha : v.WellFormed a) (hn : C.minCard ≤ a.1) :
    (I.encodedMapWith C v' e a).1 = (letI := C.expand hn (v.decode a); modelCard I e a.1) := by
  rw [I.encodedMapWith_of_admissible C v' e ha hn]
  rfl

/-- Shape validity of the output is exactly admissibility of the input. -/
@[simp] theorem wellFormed_encodedMapWith_iff :
    v'.WellFormed (I.encodedMapWith C v' e a) ↔ v.WellFormed a ∧ C.minCard ≤ a.1 := by
  by_cases h : v.WellFormed a ∧ C.minCard ≤ a.1
  · rw [I.encodedMapWith_of_admissible C v' e h.1 h.2]
    let _ := C.expand h.2 (v.decode a)
    exact iff_of_true (Vocabulary.wellFormed_encode _ _) h
  · rw [I.encodedMapWith_of_not_admissible C v' e h]
    refine iff_of_false (fun h' => ?_) h
    have := h'.1
    simp only [List.length_replicate] at this
    omega

end Output

namespace Transducer

open Vocabulary.ModelChecker.Writer Expr

section Code


/-! ### Registers and code -/

variable {P : CounterProgram} {w : List Bool} {B : ℕ}

/-! ### Frames of counted bits -/

open scoped Classical in
/-- Emitting `true, true` for every number below `N` passing a test, then `false`, frames as many
copies of `true`. -/
private theorem flatMap_pair_append_false (p : ℕ → Prop) (N : ℕ) :
    ((List.range N).flatMap fun k => if p k then [true, true] else []) ++ [false] =
      MultiTapeTM.frame (List.replicate ((Finset.range N).filter p).card true) := by
  rw [MultiTapeTM.frame]
  congr 1
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p N
    · rw [ite_eq_left hp, Finset.card_insert_of_notMem (by simp), List.replicate_succ',
        List.flatMap_append]
      simp [hp]
    · simp [hp]

variable {L : Language.{u, v}} {L' : Language.{u', v'}}
  (C : ∀ {α : Type}, (α → ℕ) → ℕ → AtomicCompiler L α)
  (v' : Vocabulary L') {ι : Type} {d : ℕ} (e : ι ≃ Fin d) (I : Interpretation L L' ι)

/-- The largest arity of a symbol of the vocabulary `v'`. -/
private def maxArity : ℕ := Finset.univ.sup v'.arity

/-- The first register of the bound variables of the compiled formulas: after the blocks `0` to
`maxArity v'` of `d` coordinates. -/
private def base (d : ℕ) : ℕ := 8 + d * (maxArity v' + 1)

/-- The code of the domain formula, on the tuple in block `m`. -/
private def domCode (m b T F : ℕ) : List Instr :=
  formulaCodeWith (C (fun i => tupleReg d m (e i)) (base v' d)) (base v' d) I.domain b T F

/-- The code counting and framing the elements of the interpreted structure, placed at the label
`b`: register `4` runs over the indices of the tuples, register `3` counts those of the domain, and
`true, true` is emitted for each of them; then `false` ends the frame. It continues at
`b + d + codeLength I.domain + 8`. -/
private def scanCode (b : ℕ) : List Instr :=
  [.assign 3 (const 0) (b + 1)] ++
  forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + codeLength I.domain + 7) ++
  coordinatesCode d 0 (b + 4) ++
  domCode C v' e I 0 (b + 4 + d) (b + 4 + d + codeLength I.domain) (b + 3) ++
  [.emit true (b + 4 + d + codeLength I.domain + 1),
   .emit true (b + 4 + d + codeLength I.domain + 2),
   .assign 3 (add (reg 3) (const 1)) (b + 3),
   .emit false (b + d + codeLength I.domain + 8)]

private theorem length_domCode (m b T F : ℕ) :
    (domCode C v' e I m b T F).length = codeLength I.domain :=
  length_formulaCodeWith _ _ _ _ _ _

private theorem tupleReg_le_base {m : ℕ} (hm : m ≤ maxArity v') : tupleReg d m d ≤ base v' d := by
  unfold tupleReg base
  have : d * m + d ≤ d * (maxArity v' + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left d hm) d
  omega

private theorem tupleReg_lt_base {m i : ℕ} (hm : m ≤ maxArity v') (hi : i < d) :
    tupleReg d m i < base v' d := by
  unfold tupleReg base
  have : d * m + d ≤ d * (maxArity v' + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left d hm) d
  omega

private theorem le_base : 8 ≤ base v' d := Nat.le_add_right _ _

variable {C v' e I} {P : CounterProgram} {n B : ℕ} [L.Structure (Fin n)]

variable (n) in
/-- The atomic compiler family is correct for every assignment into `Fin n`, on the input `w`. -/
private abbrev Correct (C : ∀ {α : Type}, (α → ℕ) → ℕ → AtomicCompiler L α) (w : List Bool) :
    Prop :=
  ∀ {α : Type} (fv : α → ℕ) (base : ℕ) (val : α → Fin n), (C fv base).Correct w fv base val

/-- The domain formula holds of the tuple with index `k < n ^ d` exactly when `k` is an index of
the domain. -/
private theorem inDomain_iff {k : ℕ} (hk : k < n ^ d) :
    I.InDomain e n k ↔ I.domain.Realize ((tupleEquiv e).symm ⟨k, hk⟩) :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk, h⟩⟩

private theorem codeAt_scanCode {b : ℕ} (hP : P.CodeAt b (scanCode C v' e I b)) :
    let cs := codeLength I.domain
    P.instr b = .assign 3 (const 0) (b + 1) ∧
    P.CodeAt (b + 1) (forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + cs + 7)) ∧
    P.CodeAt (b + 4) (coordinatesCode d 0 (b + 4)) ∧
    P.CodeAt (b + 4 + d) (domCode C v' e I 0 (b + 4 + d) (b + 4 + d + cs) (b + 3)) ∧
    P.instr (b + 4 + d + cs) = .emit true (b + 4 + d + cs + 1) ∧
    P.instr (b + 4 + d + cs + 1) = .emit true (b + 4 + d + cs + 2) ∧
    P.instr (b + 4 + d + cs + 2) = .assign 3 (add (reg 3) (const 1)) (b + 3) ∧
    P.instr (b + d + cs + 7) = .emit false (b + d + cs + 8) := by
  intro cs
  rw [scanCode] at hP
  have hl1 : ([Instr.assign 3 (const 0) (b + 1)] ++
      forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + cs + 7)).length = 4 := rfl
  have hl2 : ([Instr.assign 3 (const 0) (b + 1)] ++
      forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + cs + 7) ++
      coordinatesCode d 0 (b + 4)).length = 4 + d := by
    rw [List.length_append, hl1, length_coordinatesCode]
  have hl3 : ([Instr.assign 3 (const 0) (b + 1)] ++
      forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + cs + 7) ++
      coordinatesCode d 0 (b + 4) ++
      domCode C v' e I 0 (b + 4 + d) (b + 4 + d + cs) (b + 3)).length = 4 + d + cs := by
    rw [List.length_append, hl2, length_domCode]
  rw [codeAt_append, codeAt_append, codeAt_append, codeAt_append] at hP
  obtain ⟨⟨⟨⟨h₀, hfor⟩, hcoords⟩, hdom⟩, htail⟩ := hP
  rw [hl3] at htail; rw [hl2, show b + (4 + d) = b + 4 + d by omega] at hdom
  rw [hl1] at hcoords; rw [List.length_singleton] at hfor; rw [codeAt_cons] at h₀
  simp only [codeAt_cons] at htail
  obtain ⟨hy₀, hy₁, hy₂, hx, -⟩ := htail
  exact ⟨h₀.1, hfor, hcoords, hdom, by convert hy₀ using 2; omega, by convert hy₁ using 2; omega,
    by convert hy₂ using 2; omega, by convert hx using 2; omega⟩

private theorem reaches_scanCode_dom (hC : Correct n C w) {b k : ℕ}
    (hcoords : P.CodeAt (b + 4) (coordinatesCode d 0 (b + 4)))
    (hdom : P.CodeAt (b + 4 + d) (domCode C v' e I 0 (b + 4 + d)
      (b + 4 + d + codeLength I.domain) (b + 3)))
    (hnB : n ≤ B) (regs : List ℕ) (hlen : base v' d + boundDepth I.domain ≤ regs.length)
    (hk : k < n ^ d) (r : List ℕ) (h4 : r.getD 4 0 = k) (h0' : r.getD 0 0 = n)
    (hl : r.length = regs.length) (hB' : ∀ x ∈ r, x ≤ B) :
    ∃ (res : Bool) (regs₂ : List ℕ), (res = true ↔ I.InDomain e n k) ∧
      P.ReachesOut w (P.Active B) (b + 4, r)
        (if res then b + 4 + d + codeLength I.domain else b + 3, regs₂) [] ∧
      regs₂.length = regs.length ∧ (∀ x < 8, regs₂.getD x 0 = r.getD x 0) ∧
      ∀ x ∈ regs₂, x ≤ B := by
  classical
  have hbase := le_base v' (d := d); have htupleReg0 := tupleReg_le_base v' (d := d) (Nat.zero_le _)
  obtain ⟨regs₁, hreach₁, hlen₁, hset₁, hkeep₁, hB₁⟩ :=
    reaches_coordinatesCode (w := w) hcoords hk hnB r h0' h4 (by rw [hl]; omega) hB'
  have hreg (x : ℕ) (_ : x < 8) : regs₁.getD x 0 = r.getD x 0 :=
    hkeep₁ x fun _ _ => by unfold tupleReg; omega
  obtain ⟨res, regs₂, hres, hreach₂, hlen₂, hkeep₂, hB₂⟩ :=
    reaches_formulaCodeWith hnB (fun i => tupleReg d 0 (e i)) (base v' d) (by omega)
      (fun i => tupleReg_lt_base v' (Nat.zero_le _) (e i).2) ((tupleEquiv e).symm ⟨k, hk⟩) _
      (hC _ _ _) I.domain (b + 4 + d) (b + 4 + d + codeLength I.domain) (b + 3) regs₁ default hdom
      (by rw [hlen₁, hl]; exact hlen) (by rw [hreg 0 (by omega), h0']) hB₁
      (fun i => by rw [hset₁ _ (e i).2, tupleEquiv_symm_apply_val]) (fun i => i.elim0)
  exact ⟨res, regs₂, by rw [hres, inDomain_iff hk]; rfl,
    by simpa using hreach₁.reachesOut.trans hreach₂.reachesOut, by rw [hlen₂, hlen₁, hl],
    fun x hx => (hkeep₂ x (by omega)).trans (hreg x hx), hB₂⟩

open Classical in
private theorem reachesOut_scanCode_step (hC : Correct n C w) {b : ℕ}
    (hcoords : P.CodeAt (b + 4) (coordinatesCode d 0 (b + 4)))
    (hdom : P.CodeAt (b + 4 + d) (domCode C v' e I 0 (b + 4 + d)
      (b + 4 + d + codeLength I.domain) (b + 3)))
    (hy₀ : P.instr (b + 4 + d + codeLength I.domain) =
      .emit true (b + 4 + d + codeLength I.domain + 1))
    (hy₁ : P.instr (b + 4 + d + codeLength I.domain + 1) =
      .emit true (b + 4 + d + codeLength I.domain + 2))
    (hy₂ : P.instr (b + 4 + d + codeLength I.domain + 2) =
      .assign 3 (add (reg 3) (const 1)) (b + 3))
    (hnB : n ≤ B) (hNB : n ^ d ≤ B) (regs : List ℕ)
    (hlen : base v' d + boundDepth I.domain ≤ regs.length)
    (k : ℕ) (hk : k < n ^ d) (r : List ℕ)
    (hinv : r.getD 4 0 = k ∧ r.getD 0 0 = n ∧ r.getD 3 0 = I.domainRank e n k ∧
      r.length = regs.length ∧ ∀ x ∈ r, x ≤ B) :
    ∃ r', P.ReachesOut w (P.Active B) (b + 4, r) (b + 3, r')
        (if I.InDomain e n k then [true, true] else []) ∧
      r'.getD 4 0 = k ∧ (∀ x ∈ r', x ≤ B) ∧
      (r'.set 4 (k + 1)).getD 4 0 = k + 1 ∧ (r'.set 4 (k + 1)).getD 0 0 = n ∧
      (r'.set 4 (k + 1)).getD 3 0 = I.domainRank e n (k + 1) ∧
      (r'.set 4 (k + 1)).length = regs.length ∧ ∀ x ∈ r'.set 4 (k + 1), x ≤ B := by
  classical
  obtain ⟨h4, h0', h3, hl, hB'⟩ := hinv
  have hbase := le_base v' (d := d)
  have hrank : I.domainRank e n (k + 1) ≤ B :=
    (domainRank_mono (show k + 1 ≤ n ^ d by omega)).trans (modelCard_le_pow.trans hNB)
  obtain ⟨res, regs₂, hdomk, hreach₁₂, hlen₂', hk₂, hB₂⟩ :=
    reaches_scanCode_dom hC hcoords hdom hnB regs hlen hk r h4 h0' hl hB'
  cases res with
  | true =>
    have hin : I.InDomain e n k := hdomk.mp rfl
    have hB₃ : ∀ x ∈ regs₂.set 3 (I.domainRank e n k + 1), x ≤ B :=
      List.forall_mem_set_of_forall_mem hB₂
        (by rw [domainRank_succ, ite_eq_left hin] at hrank; exact hrank)
    refine ⟨regs₂.set 3 (I.domainRank e n k + 1), ?_,
      by rw [List.getD_set_ne (by omega), hk₂ 4 (by omega), h4], hB₃,
      List.getD_set_self (by simp only [List.length_set]; omega),
      by rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), hk₂ 0 (by omega), h0'],
      by rw [List.getD_set_ne (by omega), List.getD_set_self (by omega), domainRank_succ,
        ite_eq_left hin],
      by simp only [List.length_set, hlen₂'], List.forall_mem_set_of_forall_mem hB₃ (by omega)⟩
    have hreach := hreach₁₂.trans (ReachesOut.emit hy₀ hB₂
      (ReachesOut.emit hy₁ hB₂ (ReachesOut.assign hy₂ hB₂ (ReachesOut.refl _))))
    simp only [eval_add, eval_reg, eval_const, hk₂ 3 (by omega), h3, List.nil_append] at hreach
    simpa only [hin, ↓reduceIte] using hreach
  | false =>
    have hnot : ¬ I.InDomain e n k := fun h => Bool.false_ne_true (hdomk.mpr h)
    refine ⟨regs₂, ?_, by rw [hk₂ 4 (by omega), h4], hB₂, List.getD_set_self (by omega),
      by rw [List.getD_set_ne (by omega), hk₂ 0 (by omega), h0'],
      by rw [List.getD_set_ne (by omega), hk₂ 3 (by omega), h3, domainRank_succ,
        ite_eq_right hnot]; rfl,
      by simp only [List.length_set, hlen₂'], List.forall_mem_set_of_forall_mem hB₂ (by omega)⟩
    simpa only [Bool.false_eq_true, hnot, ↓reduceIte] using hreach₁₂

/-- **Counting and framing the elements of the interpreted structure**: from the scan code, with
the cardinality of a well-formed input in register `0`, the program emits the frame of as many
copies of `true` as the interpreted structure has elements, and puts that number in register
`3`. -/
private theorem reachesOut_scanCode (hC : Correct n C w) {b : ℕ}
    (hP : P.CodeAt b (scanCode C v' e I b))
    (hnB : n ≤ B) (hNB : n ^ d ≤ B) (regs : List ℕ) (h0 : regs.getD 0 0 = n)
    (hlen : base v' d + boundDepth I.domain ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.ReachesOut w (P.Active B) (b, regs)
      (b + d + codeLength I.domain + 8, regs')
      (MultiTapeTM.frame (List.replicate (modelCard I e n) true)) ∧
      regs'.length = regs.length ∧ regs'.getD 0 0 = n ∧
      regs'.getD 3 0 = modelCard I e n ∧ ∀ r ∈ regs', r ≤ B := by
  classical
  obtain ⟨h₀, hfor, hcoords, hdom, hy₀, hy₁, hy₂, hx⟩ := codeAt_scanCode hP
  have hbase := le_base v' (d := d)
  let Inv : ℕ → List ℕ → Prop := fun k r => r.getD 4 0 = k ∧ r.getD 0 0 = n ∧
    r.getD 3 0 = I.domainRank e n k ∧ r.length = regs.length ∧ ∀ x ∈ r, x ≤ B
  let o : ℕ → List Bool := fun k => if I.InDomain e n k then [true, true] else []
  have hB₀ : ∀ r ∈ regs.set 3 0, r ≤ B := List.forall_mem_set_of_forall_mem hB (Nat.zero_le _)
  obtain ⟨regsN, hloop, -, h0N, h3N, hlN, hBN⟩ :=
    reachesOut_forCode (B := B) (w := w) hfor Inv o hNB
    (fun k r ⟨h4, h0', _, hl, hB'⟩ => ⟨h4, by simp only [eval_pow, eval_reg, h0'],
      by rw [hl]; omega, hB'⟩)
    (reachesOut_scanCode_step hC hcoords hdom hy₀ hy₁ hy₂ hnB hNB regs hlen)
    (regs.set 3 0) hB₀
    ⟨List.getD_set_self (by simp only [List.length_set]; omega),
      by rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), h0],
      by rw [List.getD_set_ne (by omega), List.getD_set_self (by omega), domainRank_zero],
      by simp only [List.length_set], List.forall_mem_set_of_forall_mem hB₀ (Nat.zero_le _)⟩
  refine ⟨regsN, ?_, hlN, h0N, h3N, hBN⟩
  have hreach := ReachesOut.assign h₀ hB (hloop.trans (ReachesOut.emit hx hBN (ReachesOut.refl _)))
  rw [modelCard, domainRank, Nat.count_eq_card_filter_range, ← flatMap_pair_append_false]
  simpa only [eval_const] using hreach

variable (C v' e I) in
/-- The code finding, by counting, the element of rank `t / n' ^ m % n'` of the interpreted
structure, for `t` in register `6` and its number `n'` of elements in register `3`, and writing its
coordinates into block `m`; placed at `A`, it continues at `A + d + codeLength I.domain + 6`.
Register `7` holds the rank sought, register `4` runs over the indices of the tuples and register
`5` counts those of the domain. -/
private def unrankCode (m A : ℕ) : List Instr :=
  [.assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1),
   .assign 4 (const 0) (A + 2),
   .assign 5 (const 0) (A + 3)] ++
  coordinatesCode d m (A + 3) ++
  domCode C v' e I m (A + 3 + d) (A + 3 + d + codeLength I.domain)
    (A + 3 + d + codeLength I.domain + 2) ++
  [.lt (reg 5) (reg 7) (A + 3 + d + codeLength I.domain + 1)
     (A + 3 + d + codeLength I.domain + 3),
   .assign 5 (add (reg 5) (const 1)) (A + 3 + d + codeLength I.domain + 2),
   .assign 4 (add (reg 4) (const 1)) (A + 3)]

private theorem length_unrankCode (m A : ℕ) :
    (unrankCode C v' e I m A).length = d + codeLength I.domain + 6 := by
  simp only [unrankCode, List.length_append, length_coordinatesCode, length_domCode,
    List.length_cons,
    List.length_nil]
  omega

private theorem codeAt_unrankCode {m A : ℕ} (hP : P.CodeAt A (unrankCode C v' e I m A)) :
    P.instr A = .assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1) ∧
    P.instr (A + 1) = .assign 4 (const 0) (A + 2) ∧
    P.instr (A + 2) = .assign 5 (const 0) (A + 3) ∧
    P.CodeAt (A + 3) (coordinatesCode d m (A + 3)) ∧
    P.CodeAt (A + 3 + d) (domCode C v' e I m (A + 3 + d)
      (A + 3 + d + codeLength I.domain) (A + 3 + d + codeLength I.domain + 2)) ∧
    P.instr (A + 3 + d + codeLength I.domain) = .lt (reg 5) (reg 7)
      (A + 3 + d + codeLength I.domain + 1) (A + 3 + d + codeLength I.domain + 3) ∧
    P.instr (A + 3 + d + codeLength I.domain + 1) = .assign 5 (add (reg 5) (const 1))
      (A + 3 + d + codeLength I.domain + 2) ∧
    P.instr (A + 3 + d + codeLength I.domain + 2) = .assign 4 (add (reg 4) (const 1)) (A + 3) := by
  rw [unrankCode] at hP
  generalize hcs : codeLength I.domain = cs at hP ⊢
  have hl2 : ([Instr.assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1),
      .assign 4 (const 0) (A + 2), .assign 5 (const 0) (A + 3)] ++
      coordinatesCode d m (A + 3)).length = 3 + d := by
    rw [List.length_append, length_coordinatesCode]; rfl
  have hl3 : ([Instr.assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1),
      .assign 4 (const 0) (A + 2), .assign 5 (const 0) (A + 3)] ++
      coordinatesCode d m (A + 3) ++
      domCode C v' e I m (A + 3 + d) (A + 3 + d + cs) (A + 3 + d + cs + 2)).length =
      3 + d + cs := by
    rw [List.length_append, hl2, length_domCode, hcs]
  rw [codeAt_append, codeAt_append, codeAt_append] at hP
  obtain ⟨⟨⟨hinit, hcoords⟩, hdom⟩, htail⟩ := hP
  rw [hl3] at htail; rw [hl2, show A + (3 + d) = A + 3 + d by omega] at hdom
  rw [show ([Instr.assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1),
      .assign 4 (const 0) (A + 2), .assign 5 (const 0) (A + 3)] : List Instr).length = 3 from rfl]
    at hcoords
  simp only [codeAt_cons] at hinit htail
  obtain ⟨hi₀, hi₁, hi₂, -⟩ := hinit
  obtain ⟨hc₀, hc₁, hc₂, -⟩ := htail
  exact ⟨hi₀, hi₁, by convert hi₂ using 2, hcoords, hdom, by convert hc₀ using 2; omega,
    by convert hc₁ using 2; omega, by convert hc₂ using 2; omega⟩

private theorem reaches_unrankCode_dom (hC : Correct n C w) {m A r u : ℕ} (hm : m ≤ maxArity v')
    (hcoords : P.CodeAt (A + 3) (coordinatesCode d m (A + 3)))
    (hdom : P.CodeAt (A + 3 + d) (domCode C v' e I m (A + 3 + d)
      (A + 3 + d + codeLength I.domain) (A + 3 + d + codeLength I.domain + 2)))
    (hnB : n ≤ B) (regs : List ℕ) (h0 : regs.getD 0 0 = n)
    (hlen : base v' d + boundDepth I.domain ≤ regs.length)
    (huN : u < n ^ d) (rs : List ℕ) (h4 : rs.getD 4 0 = u)
    (h5 : rs.getD 5 0 = I.domainRank e n u) (h7 : rs.getD 7 0 = r) (hl : rs.length = regs.length)
    (hkeep : ∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ tupleReg d m i) →
      rs.getD x 0 = regs.getD x 0)
    (hB' : ∀ x ∈ rs, x ≤ B) :
    ∃ (res : Bool) (regs₂ : List ℕ), (res = true ↔ I.InDomain e n u) ∧
      P.Reaches w (P.Running B) (A + 3, rs)
        (if res then A + 3 + d + codeLength I.domain
          else A + 3 + d + codeLength I.domain + 2, regs₂) ∧
      regs₂.length = regs.length ∧ regs₂.getD 4 0 = u ∧
      regs₂.getD 5 0 = I.domainRank e n u ∧ regs₂.getD 7 0 = r ∧
      (∀ i : ι, regs₂.getD (tupleReg d m (e i)) 0 = ((tupleEquiv e).symm ⟨u, huN⟩ i : ℕ)) ∧
      (∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ tupleReg d m i) →
        regs₂.getD x 0 = regs.getD x 0) ∧
      ∀ x ∈ regs₂, x ≤ B := by
  classical
  have hbase := le_base v' (d := d)
  have htupleRegm := tupleReg_le_base v' (d := d) hm
  have h0s : rs.getD 0 0 = n := by
    rw [hkeep 0 (by omega) (by omega) (by omega) (by omega)
      (fun i _ => by unfold tupleReg; omega), h0]
  obtain ⟨regs₁, hreach₁, hlen₁, hset₁, hkeep₁, hB₁⟩ :=
    reaches_coordinatesCode (w := w) hcoords huN hnB rs h0s h4 (by omega) hB'
  obtain ⟨res, regs₂, hres, hreach₂, hlen₂, hkeep₂, hB₂⟩ :=
    reaches_formulaCodeWith hnB (fun i => tupleReg d m (e i)) (base v' d) (by omega)
      (fun i => tupleReg_lt_base v' hm (e i).2) ((tupleEquiv e).symm ⟨u, huN⟩) _
      (hC _ _ _) I.domain (A + 3 + d) (A + 3 + d + codeLength I.domain)
      (A + 3 + d + codeLength I.domain + 2) regs₁ default hdom (by rw [hlen₁, hl]; exact hlen)
      (by rw [hkeep₁ 0 (fun i _ => by unfold tupleReg; omega), h0s]) hB₁
      (fun i => by rw [hset₁ _ (e i).2, tupleEquiv_symm_apply_val]) (fun i => i.elim0)
  have hk₂ (x : ℕ) (hx : x < base v' d) (hxm : ∀ i < d, x ≠ tupleReg d m i) :
      regs₂.getD x 0 = rs.getD x 0 := by rw [hkeep₂ x (by omega), hkeep₁ x hxm]
  refine ⟨res, regs₂, by rw [hres, inDomain_iff huN]; rfl, hreach₁.trans hreach₂,
    by rw [hlen₂, hlen₁, hl],
    by rw [hk₂ 4 (by omega) (fun _ _ => by unfold tupleReg; omega), h4],
    by rw [hk₂ 5 (by omega) (fun _ _ => by unfold tupleReg; omega), h5],
    by rw [hk₂ 7 (by omega) (fun _ _ => by unfold tupleReg; omega), h7],
    fun i => by rw [hkeep₂ _ (tupleReg_lt_base v' hm (e i).2), hset₁ _ (e i).2,
      tupleEquiv_symm_apply_val],
    fun x hx h4' h5' h7' hxm => by rw [hk₂ x hx hxm, hkeep x hx h4' h5' h7' hxm], hB₂⟩

private theorem reaches_unrankCode_step (hC : Correct n C w) {m A r u₀ u : ℕ}
    (hm : m ≤ maxArity v')
    (hcoords : P.CodeAt (A + 3) (coordinatesCode d m (A + 3)))
    (hdom : P.CodeAt (A + 3 + d) (domCode C v' e I m (A + 3 + d)
      (A + 3 + d + codeLength I.domain) (A + 3 + d + codeLength I.domain + 2)))
    (hc₀ : P.instr (A + 3 + d + codeLength I.domain) = .lt (reg 5) (reg 7)
      (A + 3 + d + codeLength I.domain + 1) (A + 3 + d + codeLength I.domain + 3))
    (hc₁ : P.instr (A + 3 + d + codeLength I.domain + 1) = .assign 5 (add (reg 5) (const 1))
      (A + 3 + d + codeLength I.domain + 2))
    (hc₂ : P.instr (A + 3 + d + codeLength I.domain + 2) = .assign 4 (add (reg 4) (const 1))
      (A + 3))
    (hnB : n ≤ B) (hNB : n ^ d ≤ B) (hrB : r ≤ B) (regs : List ℕ) (h0 : regs.getD 0 0 = n)
    (hlen : base v' d + boundDepth I.domain ≤ regs.length)
    (hu₀ : I.InDomain e n u₀) (hru₀ : I.domainRank e n u₀ = r) (hu : u < u₀)
    (rs : List ℕ) (h4 : rs.getD 4 0 = u) (h5 : rs.getD 5 0 = I.domainRank e n u)
    (h7 : rs.getD 7 0 = r) (hl : rs.length = regs.length)
    (hkeep : ∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ tupleReg d m i) →
      rs.getD x 0 = regs.getD x 0)
    (hB' : ∀ x ∈ rs, x ≤ B) :
    ∃ rs', P.Reaches w (P.Running B) (A + 3, rs) (A + 3, rs') ∧
      rs'.getD 4 0 = u + 1 ∧ rs'.getD 5 0 = I.domainRank e n (u + 1) ∧
      rs'.getD 7 0 = r ∧ rs'.length = regs.length ∧
      (∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ tupleReg d m i) →
        rs'.getD x 0 = regs.getD x 0) ∧ ∀ x ∈ rs', x ≤ B := by
  classical
  have hbase := le_base v' (d := d)
  have hu₀N : u₀ < n ^ d := hu₀.1
  obtain ⟨res, regs₂, hres', hreach₁₂, hlen₂', h4₂, h5₂, h7₂, -, hkeep₂, hB₂⟩ :=
    reaches_unrankCode_dom hC hm hcoords hdom hnB regs h0 hlen (by omega) rs h4 h5 h7 hl hkeep hB'
  cases res with
  | false =>
    have hnot : ¬ I.InDomain e n u := fun h => Bool.false_ne_true (hres'.mpr h)
    refine ⟨regs₂.set 4 (u + 1), hreach₁₂.trans (Reaches.assign hc₂ hB₂ ?_),
      List.getD_set_self (by omega),
      by rw [List.getD_set_ne (by omega), h5₂, domainRank_succ, ite_eq_right hnot]; rfl,
      by rw [List.getD_set_ne (by omega), h7₂], by rw [List.length_set, hlen₂'],
      fun x hx h4' h5' h7' hxm => by
        rw [List.getD_set_ne (Ne.symm h4'), hkeep₂ x hx h4' h5' h7' hxm],
      List.forall_mem_set_of_forall_mem hB₂ (by omega)⟩
    simpa only [eval_add, eval_reg, eval_const, h4₂] using Reaches.refl _
  | true =>
    have hin : I.InDomain e n u := hres'.mp rfl
    have hlt : I.domainRank e n u < r := hru₀ ▸ domainRank_lt_of_inDomain hin hu
    have hB₃ : ∀ x ∈ regs₂.set 5 (I.domainRank e n u + 1), x ≤ B :=
      List.forall_mem_set_of_forall_mem hB₂ (by omega)
    refine ⟨(regs₂.set 5 (I.domainRank e n u + 1)).set 4 (u + 1),
      hreach₁₂.trans (Reaches.lt hc₀ hB₂ ?_),
      List.getD_set_self (by simp only [List.length_set]; omega),
      by rw [List.getD_set_ne (by omega), List.getD_set_self (by omega), domainRank_succ,
        ite_eq_left hin],
      by rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), h7₂],
      by simp only [List.length_set, hlen₂'],
      fun x hx h4' h5' h7' hxm => by
        rw [List.getD_set_ne (Ne.symm h4'), List.getD_set_ne (Ne.symm h5'),
          hkeep₂ x hx h4' h5' h7' hxm],
      List.forall_mem_set_of_forall_mem hB₃ (by omega)⟩
    simp only [eval_reg, h5₂, h7₂, hlt, ↓reduceIte]
    refine Reaches.assign hc₁ hB₂ ?_
    simp only [eval_add, eval_reg, eval_const, h5₂]
    refine Reaches.assign hc₂ hB₃ ?_
    simpa only [eval_add, eval_reg, eval_const, List.getD_set_ne (show 5 ≠ 4 by omega),
      h4₂] using Reaches.refl _

private theorem reaches_unrankCode_loop (hC : Correct n C w) {m A r u₀ : ℕ} (hm : m ≤ maxArity v')
    (hcoords : P.CodeAt (A + 3) (coordinatesCode d m (A + 3)))
    (hdom : P.CodeAt (A + 3 + d) (domCode C v' e I m (A + 3 + d)
      (A + 3 + d + codeLength I.domain) (A + 3 + d + codeLength I.domain + 2)))
    (hc₀ : P.instr (A + 3 + d + codeLength I.domain) = .lt (reg 5) (reg 7)
      (A + 3 + d + codeLength I.domain + 1) (A + 3 + d + codeLength I.domain + 3))
    (hc₁ : P.instr (A + 3 + d + codeLength I.domain + 1) = .assign 5 (add (reg 5) (const 1))
      (A + 3 + d + codeLength I.domain + 2))
    (hc₂ : P.instr (A + 3 + d + codeLength I.domain + 2) = .assign 4 (add (reg 4) (const 1))
      (A + 3))
    (hnB : n ≤ B) (hNB : n ^ d ≤ B) (hrB : r ≤ B) (regs : List ℕ) (h0 : regs.getD 0 0 = n)
    (hlen : base v' d + boundDepth I.domain ≤ regs.length)
    (hB₅ : ∀ x ∈ ((regs.set 7 r).set 4 0).set 5 0, x ≤ B)
    (hu₀ : I.InDomain e n u₀) (hru₀ : I.domainRank e n u₀ = r) :
    ∀ u ≤ u₀, ∃ rs, P.Reaches w (P.Running B)
      (A + 3, ((regs.set 7 r).set 4 0).set 5 0) (A + 3, rs) ∧
      rs.getD 4 0 = u ∧ rs.getD 5 0 = I.domainRank e n u ∧ rs.getD 7 0 = r ∧
      rs.length = regs.length ∧
      (∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ tupleReg d m i) →
        rs.getD x 0 = regs.getD x 0) ∧ ∀ x ∈ rs, x ≤ B := by
  have hbase := le_base v' (d := d)
  intro u
  induction u with
  | zero =>
    exact fun _ => ⟨_, Reaches.refl _,
      by rw [List.getD_set_ne (by omega),
        List.getD_set_self (by simp only [List.length_set]; omega)],
      by rw [List.getD_set_self (by simp only [List.length_set]; omega), domainRank_zero],
      by rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega),
        List.getD_set_self (by omega)],
      by simp only [List.length_set],
      fun x _ h4' h5' h7' _ => by
        rw [List.getD_set_ne (Ne.symm h5'), List.getD_set_ne (Ne.symm h4'),
          List.getD_set_ne (Ne.symm h7')], hB₅⟩
  | succ u ih =>
    intro hu
    obtain ⟨rs, hreach, h4, h5, h7, hl, hkeep, hB'⟩ := ih (by omega)
    obtain ⟨rs', hstep, h4', h5', h7', hl', hkeep', hB''⟩ :=
      reaches_unrankCode_step hC hm hcoords hdom hc₀ hc₁ hc₂ hnB hNB hrB regs h0 hlen
        hu₀ hru₀ (by omega) rs h4 h5 h7 hl hkeep hB'
    exact ⟨rs', hreach.trans hstep, h4', h5', h7', hl', hkeep', hB''⟩

/-- **Finding the element of a given rank**: from the unranking code for block `m`, with the
cardinality of a well-formed input in register `0`, the number `n' > 0` of elements of the
interpreted structure in register `3` and `t` in register `6`, the program writes into block `m`
the coordinates of the element of rank `t / n' ^ m % n'`, and changes no register below the base
other than `4`, `5`, `7` and those of block `m`. -/
private theorem reaches_unrankCode (hC : Correct n C w) {m A t : ℕ} (hm : m ≤ maxArity v')
    (hP : P.CodeAt A (unrankCode C v' e I m A)) (hnB : n ≤ B) (hNB : n ^ d ≤ B)
    (regs : List ℕ) (h0 : regs.getD 0 0 = n)
    (h3 : regs.getD 3 0 = modelCard I e n) (h6 : regs.getD 6 0 = t)
    (hpos : 0 < modelCard I e n)
    (hlen : base v' d + boundDepth I.domain ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.Reaches w (P.Running B) (A, regs)
      (A + d + codeLength I.domain + 6, regs') ∧ regs'.length = regs.length ∧
      (∀ i : ι, regs'.getD (tupleReg d m (e i)) 0 =
        (((rankEquiv I e n).symm
          ⟨t / modelCard I e n ^ m % modelCard I e n, Nat.mod_lt _ hpos⟩).1 i : ℕ)) ∧
      (∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ tupleReg d m i) →
        regs'.getD x 0 = regs.getD x 0) ∧ ∀ r ∈ regs', r ≤ B := by
  classical
  obtain ⟨hi₀, hi₁, hi₂, hcoords, hdom, hc₀, hc₁, hc₂⟩ := codeAt_unrankCode hP
  set n' := modelCard I e n
  set r := t / n' ^ m % n'
  have hrn : r < n' := Nat.mod_lt _ hpos
  have hn'N : n' ≤ n ^ d := modelCard_le_pow (I := I) (e := e) (n := n)
  have hbase := le_base v' (d := d)
  obtain ⟨u₀, hu₀, hru₀⟩ := exists_inDomain_of_lt (I := I) (e := e) (n := n) hrn
  have hB₇ : ∀ x ∈ regs.set 7 r, x ≤ B := List.forall_mem_set_of_forall_mem hB (by omega)
  have hB₄ : ∀ x ∈ (regs.set 7 r).set 4 0, x ≤ B :=
    List.forall_mem_set_of_forall_mem hB₇ (Nat.zero_le _)
  have hB₅ : ∀ x ∈ ((regs.set 7 r).set 4 0).set 5 0, x ≤ B :=
    List.forall_mem_set_of_forall_mem hB₄ (Nat.zero_le _)
  obtain ⟨rs, hreach, h4, h5, h7, hl, hkeep, hB'⟩ :=
    reaches_unrankCode_loop hC hm hcoords hdom hc₀ hc₁ hc₂ hnB hNB (by omega) regs h0 hlen
      hB₅ hu₀ hru₀ u₀ le_rfl
  obtain ⟨res, regs', hres, hdomRun, hlen', -, h5', h7', hset', hkeep', hB''⟩ :=
    reaches_unrankCode_dom hC hm hcoords hdom hnB regs h0 hlen hu₀.1 rs h4 h5 h7 hl hkeep hB'
  have hresT : res = true := hres.mpr hu₀
  subst hresT
  refine ⟨regs', Reaches.assign hi₀ hB ?_, hlen', fun i => by
    rw [hset' i, rankEquiv_symm_val (r := ⟨r, hrn⟩) hu₀ hru₀], hkeep', hB''⟩
  simp only [eval_mod, eval_div, eval_pow, eval_reg, h6, h3]
  refine Reaches.assign hi₁ hB₇ ?_
  simp only [eval_const]
  refine Reaches.assign hi₂ hB₄ ?_
  simp only [eval_const, ↓reduceIte] at hdomRun ⊢
  rw [show A + d + codeLength I.domain + 6 = A + 3 + d + codeLength I.domain + 3 by omega]
  refine hreach.trans (hdomRun.trans (Reaches.lt hc₀ hB'' ?_))
  simp only [eval_reg, h5', h7', hru₀, lt_irrefl, ↓reduceIte]
  exact Reaches.refl _

variable (v' I) in
/-- The number of instructions of the code of the defining formula of the symbol `j`. -/
private def relLength (j : Fin v'.count) : ℕ := codeLength (I.rel (v'.symbol j).2)

variable (v' I d) in
/-- The number of instructions of the code of the table of the symbol `j`. -/
private def tableLength (j : Fin v'.count) : ℕ :=
  3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 5

variable (C v' e I) in
/-- The code emitting the framed truth table of the symbol `j` of the interpreted structure,
placed at `b`: register `6` runs over the indices `t` of the tuples of elements, the elements of
the tuple are found by their ranks using `unrankCode`, and
`true` followed by the truth value of the defining formula is emitted for each; then `false` ends
the frame. It continues at `b + tableLength v' d I j`. -/
private def relTableCode (j : Fin v'.count) (b : ℕ) : List Instr :=
  forCode b 6 (pow (reg 3) (v'.symbol j).1) (b + 3)
    (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 4) ++
  (List.range (v'.symbol j).1).flatMap
    (fun m => unrankCode C v' e I m (b + 3 + (d + codeLength I.domain + 6) * m)) ++
  formulaCodeWith (C (fun p : Fin (v'.symbol j).1 × ι => tupleReg d p.1 (e p.2)) (base v' d))
    (base v' d) (I.rel (v'.symbol j).2) (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1)
    (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j)
    (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 2) ++
  [.emit true (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 1),
   .emit true (b + 2),
   .emit true (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 3),
   .emit false (b + 2),
   .emit false (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 5)]

private theorem arity_le_maxArity (j : Fin v'.count) : (v'.symbol j).1 ≤ maxArity v' :=
  Finset.le_sup (f := v'.arity) (Finset.mem_univ j)

private theorem length_unranks (b k : ℕ) :
    ((List.range k).flatMap fun m =>
      unrankCode C v' e I m (b + 3 + (d + codeLength I.domain + 6) * m)).length =
      (d + codeLength I.domain + 6) * k := by
  rw [List.length_flatMap]
  simp only [length_unrankCode, List.map_const', List.length_range, List.sum_replicate,
    smul_eq_mul, Nat.mul_comm]

variable (C v' e I) in
/-- The codes of the tables of some symbols, one after the other from the label `b`. -/
private def tablesCode : ℕ → List (Fin v'.count) → List Instr :=
  blocksCode (relTableCode C v' e I) (tableLength v' d I)

private theorem length_tablesCode : ∀ (b : ℕ) (js : List (Fin v'.count)),
    (tablesCode C v' e I b js).length = (js.map (tableLength v' d I)).sum :=
  length_blocksCode _ _ fun j b => by
    simp only [relTableCode, List.length_append, length_unranks, length_formulaCodeWith,
      List.length_cons, List.length_nil, tableLength, relLength]
    rfl

private theorem codeAt_relTableCode (j : Fin v'.count) {b : ℕ}
    (hP : P.CodeAt b (relTableCode C v' e I j b)) :
    let Rl := b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1
    let cr := relLength v' I j
    P.CodeAt b (forCode b 6 (pow (reg 3) (v'.symbol j).1) (b + 3) (Rl + cr + 4)) ∧
    P.CodeAt (b + 3) ((List.range (v'.symbol j).1).flatMap fun m =>
      unrankCode C v' e I m (b + 3 + (d + codeLength I.domain + 6) * m)) ∧
    P.CodeAt Rl (formulaCodeWith (C (fun p : Fin (v'.symbol j).1 × ι => tupleReg d p.1 (e p.2))
      (base v' d)) (base v' d) (I.rel (v'.symbol j).2) Rl (Rl + cr) (Rl + cr + 2)) ∧
    P.instr (Rl + cr) = .emit true (Rl + cr + 1) ∧
    P.instr (Rl + cr + 1) = .emit true (b + 2) ∧
    P.instr (Rl + cr + 2) = .emit true (Rl + cr + 3) ∧
    P.instr (Rl + cr + 3) = .emit false (b + 2) ∧
    P.instr (Rl + cr + 4) = .emit false (Rl + cr + 5) := by
  have hlu := length_unranks (C := C) (v' := v') (e := e) (I := I) b (v'.symbol j).1
  rw [relTableCode] at hP
  generalize hcs : codeLength I.domain = cs at hP hlu ⊢
  generalize hcr : relLength v' I j = cr at hP ⊢
  rw [codeAt_append, codeAt_append, codeAt_append] at hP
  obtain ⟨⟨⟨hfor, hunr⟩, hrel⟩, htail⟩ := hP
  have hlf : (forCode b 6 (pow (reg 3) (v'.symbol j).1) (b + 3)
      (b + 3 + (d + cs + 6) * (v'.symbol j).1 + cr + 4)).length = 3 := rfl
  rw [List.length_append, hlu, hlf] at hrel
  rw [List.length_append, List.length_append, hlu, hlf, length_formulaCodeWith,
    show codeLength (I.rel (v'.symbol j).2) = cr from hcr] at htail
  rw [hlf] at hunr
  rw [show b + (3 + (d + cs + 6) * (v'.symbol j).1) = b + 3 + (d + cs + 6) * (v'.symbol j).1 by
    omega] at hrel
  simp only [codeAt_cons] at htail
  obtain ⟨hy₀, hy₁, hn₀, hn₁, hx, -⟩ := htail
  exact ⟨hfor, hunr, hrel, by convert hy₀ using 2; omega, by convert hy₁ using 2; omega,
    by convert hn₀ using 2; omega, by convert hn₁ using 2; omega, by convert hx using 2; omega⟩

private theorem reaches_unranks (hC : Correct n C w) (j : Fin v'.count) {b t : ℕ}
    (hunr : P.CodeAt (b + 3) ((List.range (v'.symbol j).1).flatMap fun m =>
      unrankCode C v' e I m (b + 3 + (d + codeLength I.domain + 6) * m)))
    (hnB : n ≤ B) (hNB : n ^ d ≤ B) (regs : List ℕ)
    (hlenD : base v' d + boundDepth I.domain ≤ regs.length)
    (ht : t < modelCard I e n ^ (v'.symbol j).1) (rs : List ℕ) (h6 : rs.getD 6 0 = t)
    (h0' : rs.getD 0 0 = n) (h3' : rs.getD 3 0 = modelCard I e n) (hl : rs.length = regs.length)
    (hB' : ∀ x ∈ rs, x ≤ B) :
    ∀ m (hmk : m ≤ (v'.symbol j).1), ∃ rs', P.Reaches w (P.Running B)
      (b + 3, rs) (b + 3 + (d + codeLength I.domain + 6) * m, rs') ∧ rs'.length = regs.length ∧
      rs'.getD 0 0 = n ∧ rs'.getD 3 0 = modelCard I e n ∧ rs'.getD 6 0 = t ∧ (∀ x ∈ rs', x ≤ B) ∧
      ∀ m' (hm' : m' < m) (i : ι), rs'.getD (tupleReg d m' (e i)) 0 =
        (((rankEquiv I e n).symm
          (finFunctionFinEquiv.symm ⟨t, ht⟩ ⟨m', lt_of_lt_of_le hm' hmk⟩)).1 i : ℕ) := by
  have hkm := arity_le_maxArity (v' := v') j
  have hbase := le_base v' (d := d)
  intro m
  induction m with
  | zero =>
    exact fun _ => ⟨rs, Reaches.refl _, hl, h0', h3', h6, hB', fun _ h => absurd h (by omega)⟩
  | succ m ih =>
    intro hm
    obtain ⟨rs₁, hreach₁, hl₁, h0₁, h3₁, h6₁, hB₁, htupleReg₁⟩ := ih (by omega)
    have hpos : 0 < modelCard I e n := by
      rcases Nat.eq_zero_or_pos (modelCard I e n) with h | h
      · rw [h, zero_pow (by omega)] at ht; omega
      · exact h
    have hcode := CodeAt.flatMap_range
      (f := fun m => unrankCode C v' e I m (b + 3 + (d + codeLength I.domain + 6) * m))
      (fun i => length_unrankCode (C := C) (v' := v') (e := e) (I := I) i _) hunr m (by omega)
    obtain ⟨rs₂, hreach₂, hl₂, htupleReg₂, hkeep₂, hB₂⟩ :=
      reaches_unrankCode hC (show m ≤ maxArity v' by omega) hcode hnB hNB rs₁ h0₁ h3₁
        h6₁ hpos (by rw [hl₁]; exact hlenD) hB₁
    refine ⟨rs₂, hreach₁.trans ?_, hl₂.trans hl₁,
      by rw [hkeep₂ 0 (by omega) (by omega) (by omega) (by omega)
        (fun i _ => by unfold tupleReg; omega), h0₁],
      by rw [hkeep₂ 3 (by omega) (by omega) (by omega) (by omega)
        (fun i _ => by unfold tupleReg; omega), h3₁],
      by rw [hkeep₂ 6 (by omega) (by omega) (by omega) (by omega)
        (fun i _ => by unfold tupleReg; omega), h6₁],
      hB₂, fun m' hm' i => ?_⟩
    · rw [show b + 3 + (d + codeLength I.domain + 6) * m + d + codeLength I.domain + 6 =
        b + 3 + (d + codeLength I.domain + 6) * (m + 1) by rw [Nat.mul_succ]; omega] at hreach₂
      exact hreach₂
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm') with hlt | rfl
      · rw [hkeep₂ _ (tupleReg_lt_base v' (by omega) (e i).2) (by unfold tupleReg; omega)
          (by unfold tupleReg; omega) (by unfold tupleReg; omega)
          (fun i' hi' => tupleReg_ne (by omega) (e i).2 hi'), htupleReg₁ m' hlt i]
      · rw [htupleReg₂ i]; congr 3

variable [L'.IsRelational]

open Classical in
private theorem reachesOut_relTableCode_step (hC : Correct n C w) (j : Fin v'.count) {b : ℕ}
    (hunr : P.CodeAt (b + 3) ((List.range (v'.symbol j).1).flatMap fun m =>
      unrankCode C v' e I m (b + 3 + (d + codeLength I.domain + 6) * m)))
    (hrel : P.CodeAt (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1)
      (formulaCodeWith (C (fun p : Fin (v'.symbol j).1 × ι => tupleReg d p.1 (e p.2))
        (base v' d)) (base v' d) (I.rel (v'.symbol j).2)
        (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1)
        (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j)
        (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 2)))
    (hy₀ : P.instr (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j) =
      .emit true (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 1))
    (hy₁ : P.instr (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 +
      relLength v' I j + 1) = .emit true (b + 2))
    (hn₀ : P.instr (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 +
      relLength v' I j + 2) =
      .emit true (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 3))
    (hn₁ : P.instr (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 +
      relLength v' I j + 3) = .emit false (b + 2))
    (hnB : n ≤ B) (hNB : n ^ d ≤ B) (hTB : modelCard I e n ^ (v'.symbol j).1 ≤ B)
    (regs : List ℕ) (hlenD : base v' d + boundDepth I.domain ≤ regs.length)
    (hlenR : base v' d + boundDepth (I.rel (v'.symbol j).2) ≤ regs.length)
    (t : ℕ) (ht : t < modelCard I e n ^ (v'.symbol j).1) (rs : List ℕ)
    (hinv : rs.getD 6 0 = t ∧ rs.getD 0 0 = n ∧ rs.getD 3 0 = modelCard I e n ∧
      rs.length = regs.length ∧ ∀ x ∈ rs, x ≤ B) :
    ∃ rs₂, P.ReachesOut w (P.Active B) (b + 3, rs) (b + 2, rs₂)
        [true, if h : t < modelCard I e n ^ (v'.symbol j).1 then
          decide (RelMap (v'.symbol j).2 ((rankEquiv I e n).symm ∘ finFunctionFinEquiv.symm ⟨t, h⟩))
        else false] ∧
      rs₂.getD 6 0 = t ∧ (∀ x ∈ rs₂, x ≤ B) ∧
      (rs₂.set 6 (t + 1)).getD 6 0 = t + 1 ∧ (rs₂.set 6 (t + 1)).getD 0 0 = n ∧
      (rs₂.set 6 (t + 1)).getD 3 0 = modelCard I e n ∧
      (rs₂.set 6 (t + 1)).length = regs.length ∧ ∀ x ∈ rs₂.set 6 (t + 1), x ≤ B := by
  classical
  obtain ⟨h6, h0', h3', hl, hB'⟩ := hinv
  have hkm := arity_le_maxArity (v' := v') j
  have hbase := le_base v' (d := d)
  obtain ⟨rs₁, hreach₁, hl₁, h0₁, h3₁, h6₁, hB₁, htupleReg₁⟩ :=
    reaches_unranks hC j hunr hnB hNB regs hlenD ht rs h6 h0' h3' hl hB' _ le_rfl
  obtain ⟨res, rs₂, hres, hreach₂, hl₂, hkeep₂, hB₂⟩ :=
    reaches_formulaCodeWith hnB
      (fun p : Fin (v'.symbol j).1 × ι => tupleReg d p.1 (e p.2)) (base v' d) (by omega)
      (fun p => tupleReg_lt_base v' (show (p.1 : ℕ) ≤ maxArity v' by omega) (e p.2).2)
      (fun p => ((rankEquiv I e n).symm (finFunctionFinEquiv.symm ⟨t, ht⟩ p.1)).1 p.2)
      _ (hC _ _ _) (I.rel (v'.symbol j).2) _ _ _ rs₁ default hrel
      (by rw [hl₁]; exact hlenR) h0₁ hB₁ (fun p => htupleReg₁ p.1 p.1.2 p.2) (fun i => i.elim0)
  have hbit : (if h : t < modelCard I e n ^ (v'.symbol j).1 then
      decide (RelMap (v'.symbol j).2 ((rankEquiv I e n).symm ∘ finFunctionFinEquiv.symm ⟨t, h⟩))
      else false) = res := by
    have hiff : RelMap (v'.symbol j).2
        ((rankEquiv I e n).symm ∘ finFunctionFinEquiv.symm ⟨t, ht⟩) ↔ res = true := hres.symm
    simp only [ht, ↓reduceDIte]
    cases res <;> simpa using hiff
  refine ⟨rs₂, ?_, by rw [hkeep₂ 6 (by omega), h6₁], hB₂,
    List.getD_set_self (by rw [hl₂, hl₁]; omega),
    by rw [List.getD_set_ne (by omega), hkeep₂ 0 (by omega), h0₁],
    by rw [List.getD_set_ne (by omega), hkeep₂ 3 (by omega), h3₁],
    by rw [List.length_set, hl₂, hl₁], List.forall_mem_set_of_forall_mem hB₂ (by omega)⟩
  refine hreach₁.reachesOut.trans (hreach₂.reachesOut.trans ?_)
  rw [hbit]
  cases res
  · exact ReachesOut.emit hn₀ hB₂ (ReachesOut.emit hn₁ hB₂ (ReachesOut.refl _))
  · exact ReachesOut.emit hy₀ hB₂ (ReachesOut.emit hy₁ hB₂ (ReachesOut.refl _))

/-- **Emitting the truth table of a symbol of the interpreted structure**: from the table code
for the symbol `j`, with the cardinality of a well-formed input in register `0` and the number `n'`
of elements of the interpreted structure in register `3`, the program emits the framed truth table
of the symbol in the interpreted structure, numbered by ranks. -/
private theorem reachesOut_relTableCode (hC : Correct n C w) (j : Fin v'.count) {b : ℕ}
    (hP : P.CodeAt b (relTableCode C v' e I j b)) (hnB : n ≤ B) (hNB : n ^ d ≤ B)
    (hTB : modelCard I e n ^ (v'.symbol j).1 ≤ B)
    (regs : List ℕ) (h0 : regs.getD 0 0 = n)
    (h3 : regs.getD 3 0 = modelCard I e n)
    (hlenD : base v' d + boundDepth I.domain ≤ regs.length)
    (hlenR : base v' d + boundDepth (I.rel (v'.symbol j).2) ≤ regs.length)
    (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.ReachesOut w (P.Active B) (b, regs)
      (b + tableLength v' d I j, regs')
      (MultiTapeTM.frame (
        Vocabulary.relTable (I.Model (Fin n)) (rankEquiv I e n) (v'.symbol j))) ∧
      regs'.length = regs.length ∧ regs'.getD 0 0 = n ∧
      regs'.getD 3 0 = modelCard I e n ∧ ∀ r ∈ regs', r ≤ B := by
  classical
  obtain ⟨hfor, hunr, hrel, hy₀, hy₁, hn₀, hn₁, hx⟩ := codeAt_relTableCode j hP
  have hbase := le_base v' (d := d)
  let bit : ℕ → Bool := fun t => if h : t < modelCard I e n ^ (v'.symbol j).1 then
    decide (RelMap (v'.symbol j).2 ((rankEquiv I e n).symm ∘ finFunctionFinEquiv.symm ⟨t, h⟩))
    else false
  let Inv : ℕ → List ℕ → Prop := fun t rs => rs.getD 6 0 = t ∧ rs.getD 0 0 = n ∧
    rs.getD 3 0 = modelCard I e n ∧ rs.length = regs.length ∧ ∀ x ∈ rs, x ≤ B
  obtain ⟨regsN, hloop, -, h0N, h3N, hlN, hBN⟩ := reachesOut_forCode (B := B) (w := w) hfor Inv
    (fun t => [true, bit t]) hTB
    (fun t rs ⟨h6, _, h3', hl, hB'⟩ => ⟨h6, by simp only [eval_pow, eval_reg, h3'],
      by rw [hl]; omega, hB'⟩)
    (reachesOut_relTableCode_step hC j hunr hrel hy₀ hy₁ hn₀ hn₁ hnB hNB hTB regs hlenD hlenR)
    regs hB ⟨List.getD_set_self (by omega), by rw [List.getD_set_ne (by omega), h0],
      by rw [List.getD_set_ne (by omega), h3], by rw [List.length_set],
      List.forall_mem_set_of_forall_mem hB (Nat.zero_le _)⟩
  refine ⟨regsN, ?_, hlN, h0N, h3N, hBN⟩
  have hreach := hloop.trans (ReachesOut.emit hx hBN (ReachesOut.refl _))
  rw [tableLength,
    show b + (3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 5) =
      b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 5 by omega,
    Vocabulary.relTable, ← flatMap_range_pair_append_false]
  exact hreach

/-- **Emitting the truth tables of some symbols**, one after the other. -/
private theorem reachesOut_tablesCode (hC : Correct n C w) (hnB : n ≤ B) (hNB : n ^ d ≤ B) :
    ∀ (js : List (Fin v'.count)) (b : ℕ) (regs : List ℕ),
      P.CodeAt b (tablesCode C v' e I b js) →
      (∀ j ∈ js, modelCard I e n ^ (v'.symbol j).1 ≤ B) →
      regs.getD 0 0 = n → regs.getD 3 0 = modelCard I e n →
      base v' d + boundDepth I.domain ≤ regs.length →
      (∀ j ∈ js, base v' d + boundDepth (I.rel (v'.symbol j).2) ≤ regs.length) →
      (∀ r ∈ regs, r ≤ B) →
      ∃ regs', P.ReachesOut w (P.Active B) (b, regs)
        (b + (js.map (tableLength v' d I)).sum, regs')
        (js.flatMap fun j => MultiTapeTM.frame (
          Vocabulary.relTable (I.Model (Fin n)) (rankEquiv I e n) (v'.symbol j))) ∧
        regs'.length = regs.length ∧ regs'.getD 0 0 = n ∧
        regs'.getD 3 0 = modelCard I e n ∧ ∀ r ∈ regs', r ≤ B := by
  intro js b regs hP hTB h0 h3 hlenD hlenR hB
  let Inv := fun rs : List ℕ => rs.length = regs.length ∧ rs.getD 0 0 = n ∧
    rs.getD 3 0 = modelCard I e n ∧ ∀ r ∈ rs, r ≤ B
  apply reachesOut_blocksCode (relTableCode C v' e I) (tableLength v' d I)
    (fun j b => by
      have := length_tablesCode (C := C) (v' := v') (e := e) (I := I) b [j]
      simpa [tablesCode, blocksCode] using this) _ Inv ?_ b regs hP ⟨rfl, h0, h3, hB⟩
  intro j hj c rs hc ⟨hl, h0', h3', hB'⟩
  obtain ⟨rs', hr, hl', h0'', h3'', hB''⟩ :=
    reachesOut_relTableCode hC j hc hnB hNB (hTB j hj) rs h0' h3'
      (hl ▸ hlenD) (hl ▸ hlenR j hj) hB'
  exact ⟨rs', hr, hl'.trans hl, h0'', h3'', hB''⟩

end Code

/-! ### The complete transducer -/

section Program

variable {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L) {Ls : Language.{u', v'}}
  {L' : Language.{u'', v''}} [L'.IsRelational] (C : FormulaCompiler v Ls) (v' : Vocabulary L')
  {ι : Type} (d : ℕ) (e : ι ≃ Fin d) (I : Interpretation Ls L' ι)

/-- The label of the cardinality guard, immediately after the shape check. -/
private def guardLabel : ℕ := 4 + 6 * v.count

/-- The starting label of the domain scan, immediately after the cardinality guard. -/
private def scanStart : ℕ := guardLabel v + 1

/-- The starting label of the relation tables, immediately after the domain scan. -/
private def tablesStart : ℕ := scanStart v + d + codeLength I.domain + 8

/-- The accepting halt label, immediately after the relation tables. -/
private def haltLabel : ℕ := tablesStart v d I +
  ((List.finRange v'.count).map (tableLength v' d I)).sum

/-- Enough registers for each relation formula and the domain formula. -/
private def registerCount : ℕ := base v' d +
  max (boundDepth I.domain) (Finset.univ.sup fun j => boundDepth (I.rel (v'.symbol j).2))

/-- The counter program checking shape and cardinality, enumerating the interpreted domain, and
emitting its relation tables. An inadmissible input produces a fixed malformed output. -/
private def program : CounterProgram where
  code := shapeCode v 0 (guardLabel v) (haltLabel v v' d I + 1) ++
    [.lt (reg 0) (const C.minCard) (haltLabel v v' d I + 1) (scanStart v)] ++
    scanCode C.atomic v' e I (scanStart v) ++
    tablesCode C.atomic v' e I (tablesStart v d I) (List.finRange v'.count) ++
    [.halt List.nil] ++ rejectCode v' (haltLabel v v' d I + 1)
  registers := registerCount v' d I

/-- A polynomial exponent bounding every register of the transducer. -/
private def exponent : ℕ := v.maxArity + d * (maxArity v' + 1) + 1

end Program

end Transducer

variable {L : Language.{u, v}} [L.IsRelational] {v : Vocabulary L} {Ls : Language.{u', v'}}
  {L' : Language.{u'', v''}} [L'.IsRelational] {ι : Type} {d : ℕ}
  (I : Interpretation Ls L' ι) (C : FormulaCompiler v Ls) (v' : Vocabulary L') (e : ι ≃ Fin d)

open Transducer Vocabulary.ModelChecker.Writer Expr in
omit [L'.IsRelational] in
private theorem codeAt_program :
    let P := program v C v' d e I
    P.CodeAt 0 (shapeCode v 0 (guardLabel v) (haltLabel v v' d I + 1)) ∧
    P.instr (guardLabel v) =
      .lt (reg 0) (const C.minCard) (haltLabel v v' d I + 1) (scanStart v) ∧
    P.CodeAt (scanStart v) (scanCode C.atomic v' e I (scanStart v)) ∧
    P.CodeAt (tablesStart v d I)
      (tablesCode C.atomic v' e I (tablesStart v d I) (List.finRange v'.count)) ∧
    P.instr (haltLabel v v' d I) = .halt List.nil ∧
    P.CodeAt (haltLabel v v' d I + 1) (rejectCode v' (haltLabel v v' d I + 1)) := by
  let P := program v C v' d e I
  have hcode : P.CodeAt 0 P.code := codeAt_of_code_eq (pre := []) (post := []) (by simp)
  change P.CodeAt 0 (_ ++ _ ++ _ ++ _ ++ _ ++ _) at hcode
  rw [codeAt_append, codeAt_append, codeAt_append, codeAt_append, codeAt_append] at hcode
  obtain ⟨⟨⟨⟨⟨hshape, hguard⟩, hscan⟩, htables⟩, hhalt⟩, hreject⟩ := hcode
  have hscanLen : (scanCode C.atomic v' e I (scanStart v)).length =
      d + codeLength I.domain + 8 := by
    simp only [scanCode, List.length_append, List.length_cons, List.length_nil,
      length_coordinatesCode, length_domCode, forCode]; omega
  simp only [List.length_append, length_shapeCode, hscanLen, length_tablesCode,
    List.length_cons, List.length_nil, Nat.zero_add] at hguard hscan htables hhalt hreject
  change P.CodeAt (guardLabel v) [_] at hguard
  change P.CodeAt (scanStart v) _ at hscan
  have htabStart : 4 + 6 * v.count + 1 + (d + codeLength I.domain + 8) = tablesStart v d I := by
    unfold tablesStart scanStart guardLabel; omega
  rw [htabStart] at htables hhalt hreject
  change P.CodeAt (haltLabel v v' d I) [.halt List.nil] at hhalt
  change P.CodeAt (haltLabel v v' d I + 1) _ at hreject
  exact ⟨hshape, (codeAt_cons.mp hguard).1, hscan, htables, (codeAt_cons.mp hhalt).1, hreject⟩

open Transducer Vocabulary.ModelChecker.Writer Expr in
private theorem reachesOut_program_admissible (a : EncodedStructure) (ha : v.WellFormed a)
    (hn : C.minCard ≤ a.1) {B : ℕ}
    (hpow : ∀ k ≤ exponent v v' d, a.1 ^ k ≤ B) (hnB : a.1 ≤ B) (hNB : a.1 ^ d ≤ B)
    (rs : List ℕ)
    (hshapeRun : (program v C v' d e I).Reaches (encStructure a)
      ((program v C v' d e I).Running B) (0, List.replicate (program v C v' d e I).registers 0)
      (guardLabel v, rs))
    (hlen : rs.length = (program v C v' d e I).registers)
    (h0 : rs.getD 0 0 = a.1) (hB : ∀ r ∈ rs, r ≤ B) :
    ∃ (c' : ℕ × List ℕ) (o₁ o₂ : List Bool),
      (program v C v' d e I).ReachesOut (encStructure a) ((program v C v' d e I).Active B)
        (0, List.replicate (program v C v' d e I).registers 0) c' o₁ ∧
      (program v C v' d e I).instr c'.1 = .halt o₂ ∧
      encStructure (I.encodedMapWith C v' e a) = o₁ ++ o₂ ∧ ∀ r ∈ c'.2, r ≤ B := by
  classical
  let P := program v C v' d e I
  let _ := C.expand hn (v.decode a)
  obtain ⟨-, hguard', hscan, htables, hhalt', -⟩ := codeAt_program I C v' e
  have hlenD : base v' d + boundDepth I.domain ≤ P.registers :=
    Nat.add_le_add_left (le_max_left _ _) _
  have hlenR (j : Fin v'.count) : base v' d + boundDepth (I.rel (v'.symbol j).2) ≤ P.registers :=
    Nat.add_le_add_left ((Finset.le_sup (f := fun j => boundDepth (I.rel (v'.symbol j).2))
      (Finset.mem_univ j)).trans (le_max_right _ _)) _
  have hcheck : P.Reaches (encStructure a) (P.Running B) (guardLabel v, rs) (scanStart v, rs) := by
    refine Reaches.lt hguard' hB ?_
    simp only [eval_reg, eval_const, h0, Nat.not_lt.mpr hn, ↓reduceIte]
    exact Reaches.refl _
  obtain ⟨rs₁, hscanRun, hlen₁, h0₁, h3₁, hB₁⟩ := reachesOut_scanCode (C.atomic_correct ha hn)
    hscan hnB hNB rs h0 (by rw [hlen]; exact hlenD) hB
  change P.ReachesOut _ _ _ (tablesStart v d I, rs₁) _ at hscanRun
  have hTB (j : Fin v'.count) : modelCard I e a.1 ^ (v'.symbol j).1 ≤ B := by
    calc modelCard I e a.1 ^ (v'.symbol j).1 ≤ (a.1 ^ d) ^ (v'.symbol j).1 :=
          Nat.pow_le_pow_left modelCard_le_pow _
      _ = a.1 ^ (d * (v'.symbol j).1) := (pow_mul _ _ _).symm
      _ ≤ B := hpow _ (by
          have hmul : d * (v'.symbol j).1 ≤ d * (maxArity v' + 1) :=
            Nat.mul_le_mul_left d ((arity_le_maxArity j).trans (Nat.le_succ _))
          unfold exponent; omega)
  obtain ⟨rs₂, htablesRun, _, _, _, hB₂⟩ := reachesOut_tablesCode (C.atomic_correct ha hn) hnB
    hNB (List.finRange v'.count) _ rs₁ htables (fun j _ => hTB j) h0₁ h3₁
    (by rw [hlen₁, hlen]; exact hlenD) (fun j _ => by rw [hlen₁, hlen]; exact hlenR j) hB₁
  refine ⟨(haltLabel v v' d I, rs₂), _, [], hshapeRun.reachesOut.trans
    (hcheck.reachesOut.trans (hscanRun.trans htablesRun)), hhalt', ?_, hB₂⟩
  rw [I.encodedMapWith_of_admissible C v' e ha hn]
  simp only [List.nil_append, List.append_nil, encStructure_eq, Vocabulary.encode]
  congr 1; rw [List.ofFn_eq_map, List.flatMap_map]

open Transducer Vocabulary.ModelChecker.Writer Expr in
/-- **The domain-counting transducer**: computing a first-order interpretation, with the formula
semantics of a compiler `C`, on encoded finite relational structures uses logarithmic work space.
The output is streamed, including its unary cardinality frame; inadmissible inputs map to a fixed
malformed output. -/
theorem computableInLogSpace_encodedMapWith :
    MultiTapeTM.ComputableInLogSpace (I.encodedMapWith C v' e) encStructure encStructure := by
  classical
  let P := program v C v' d e I
  refine P.computableInLogSpace_of_reachesOut (exponent v v' d) fun a => ?_
  let B := ((encStructure a).length + 1) ^ exponent v v' d
  have hpow (k : ℕ) (hk : k ≤ exponent v v' d) : a.1 ^ k ≤ B :=
    (Nat.pow_le_pow_left ((card_le_length_encStructure a).trans (Nat.le_succ _)) k).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) hk)
  have hE : v.maxArity ≤ exponent v v' d := by unfold exponent; omega
  have hwB : (encStructure a).length ≤ B :=
    (length_le_pow_maxArity v a).trans (Nat.pow_le_pow_right (Nat.succ_pos _) hE)
  have hnB : a.1 ≤ B := (card_le_length_encStructure a).trans hwB
  have hdE : d ≤ exponent v v' d := by
    have := Nat.mul_le_mul_left d (show 1 ≤ maxArity v' + 1 by omega)
    simp only [Nat.mul_one] at this; unfold exponent; omega
  obtain ⟨hshape, hguard', -, -, -, hreject⟩ := codeAt_program I C v' e
  have hlenD : base v' d + boundDepth I.domain ≤ P.registers :=
    Nat.add_le_add_left (le_max_left _ _) _
  have hbase := le_base v' (d := d)
  obtain ⟨rs, hshapeRun, hlen, h0, hB⟩ := reaches_shapeCode (B := B) (a := a) hshape
    (fun i => (pow_arityAt_le v a i).trans (Nat.pow_le_pow_right (Nat.succ_pos _) hE))
    hwB (List.replicate P.registers 0) (by simp) (by simp only [List.length_replicate]; omega)
    (by simp)
  by_cases ha : v.WellFormed a
  · rw [ite_eq_left ha] at hshapeRun
    by_cases hn : C.minCard ≤ a.1
    · exact reachesOut_program_admissible I C v' e a ha hn hpow hnB (hpow d hdE) rs hshapeRun
        (by rw [hlen, List.length_replicate]) (h0 ha) hB
    · obtain ⟨hrun, hhalt⟩ := reachesOut_rejectCode (w := encStructure a) hreject rs hB
      refine ⟨(_, rs), List.replicate (v'.count + 2) false, [],
        hshapeRun.reachesOut.trans (ReachesOut.lt hguard' hB ?_), hhalt, ?_, hB⟩
      · simpa only [eval_reg, eval_const, h0 ha, Nat.lt_of_not_ge hn, ↓reduceIte,
          List.replicate_succ] using hrun
      · rw [I.encodedMapWith_of_not_admissible C v' e (fun h => hn h.2)]
        simpa only [List.nil_append, List.append_nil] using encStructure_reject (v' := v')
  · rw [ite_eq_right ha] at hshapeRun
    obtain ⟨hrun, hhalt⟩ := reachesOut_rejectCode (w := encStructure a) hreject rs hB
    refine ⟨(_, rs), _, [], hshapeRun.reachesOut.trans hrun, hhalt, ?_, hB⟩
    rw [I.encodedMapWith_of_not_admissible C v' e (fun h => ha h.1)]
    simpa only [List.nil_append, List.append_nil] using encStructure_reject (v' := v')

end FO.Interpretation

end Cslib.Logic
