/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.STCON
public import Complexity.Computability.Complexity.Problems.TwoSAT
public import Complexity.Computability.Complexity.Problems.TwoSAT.Layout
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Tactic.IntervalCases

/-!
# Unreachability as 2SAT

An instance `I` of directed `s`–`t` connectivity becomes the formula
`Cslib.Complexity.TwoSAT.reachabilityFormula I` whose variables are the vertices: the unit
clauses `x_s` and `¬x_t`, and a clause `¬x_u ∨ x_v` for each arc from `u` to `v`. In a satisfying
assignment every vertex reachable from `s` is true, so `t` is not reachable; conversely, making
exactly the reachable vertices true satisfies the formula when `t` is not reachable
(`Cslib.Complexity.TwoSAT.reachabilityFormula_mem_TwoSAT_iff`). This is the reduction from the
complement of reachability in the proof that 2SAT is `NL`-complete
[Papadimitriou, Theorem 16.3][Papadimitriou94].

The formula is written in logarithmic space by a counter program with output
(`Cslib.Complexity.TwoSAT.writer`), which reads the header of the encoded instance and then the
matrix entry by entry, keeping the header values, two vertices and a copy of one of them whose
binary digits it writes (`Cslib.Complexity.TwoSAT.computableInLogSpace_reachabilityFormula`).

## Main definitions

* `Cslib.Complexity.TwoSAT.reachabilityFormula`: the formula of an instance.
* `Cslib.Complexity.TwoSAT.writer`: the counter program writing its encoding.

## Main results

* `Cslib.Complexity.TwoSAT.reachabilityFormula_mem_TwoSAT_iff`: the formula is in `TwoSAT`
  exactly when `t` is not reachable from `s`.
* `Cslib.Complexity.TwoSAT.computableInLogSpace_reachabilityFormula`: the formula is computed in
  logarithmic space.

## References

* [C. H. Papadimitriou, *Computational Complexity*, Theorem 16.3][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

namespace TwoSAT

open Cslib.Logic.PL

/-- The arcs of an instance on natural numbers, with no arc outside the vertices. -/
def arc (I : STCONInstance) (u v : ℕ) : Bool :=
  if h : u < I.n ∧ v < I.n then I.adj ⟨u, h.1⟩ ⟨v, h.2⟩ else false

/-- **The formula of an instance**: a variable for each vertex, true when the vertex is reachable
from `s`; the unit clauses `x_s` and `¬x_t`, and the clause `¬x_u ∨ x_v` for each arc from `u` to
`v`, row by row. -/
def reachabilityFormula (I : STCONInstance) : CNF ℕ :=
  [[((I.s : ℕ), true)], [((I.t : ℕ), false)]] ++
    (List.range I.n).flatMap fun u => (List.range I.n).flatMap fun v =>
      if arc I u v then [[(u, false), (v, true)]] else []

theorem mem_reachabilityFormula {I : STCONInstance} {c : Clause ℕ} :
    c ∈ reachabilityFormula I ↔ c = [((I.s : ℕ), true)] ∨ c = [((I.t : ℕ), false)] ∨
      ∃ u v, arc I u v = true ∧ c = [(u, false), (v, true)] := by
  simp only [reachabilityFormula, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range]
  constructor
  · rintro ((h | h) | ⟨u, hu, v, hv, h⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · split_ifs at h with harc
      · exact .inr (.inr ⟨u, v, harc, by simpa using h⟩)
      · simp at h
  · rintro (h | h | ⟨u, v, harc, rfl⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · have h := harc
      simp only [arc] at h
      split_ifs at h with huv
      exact .inr ⟨u, huv.1, v, huv.2, by simp [harc]⟩

/-- Any satisfying assignment of `reachabilityFormula I` propagates `true` along paths from `s`,
excluding `I` from `STCON`. -/
private theorem notMem_STCON_of_eval_reachabilityFormula {I : STCONInstance} {σ : ℕ → Bool}
    (hσ : (reachabilityFormula I).eval σ = true) : I ∉ STCON := by
  -- a satisfying assignment makes every reachable vertex true
  rw [mem_STCON]
  intro hst
  have hcl : ∀ c ∈ reachabilityFormula I, ∃ l ∈ c, σ l.1 = l.2 := fun c hc =>
    (Clause.eval_eq_true_iff σ c).mp ((CNF.eval_eq_true_iff σ _).mp hσ c hc)
  have key : ∀ x, Relation.ReflTransGen I.Adj I.s x → σ x = true := by
    intro x hx
    induction hx with
    | refl =>
      obtain ⟨l, hl, hlσ⟩ := hcl _ (mem_reachabilityFormula.mpr (.inl rfl))
      rw [List.mem_singleton] at hl
      subst hl
      exact hlσ
    | @tail y z _ hyz ih =>
      have harc : arc I y z = true := by
        rw [arc, dite_eq_left ⟨y.isLt, z.isLt⟩]
        exact hyz
      obtain ⟨l, hl, hlσ⟩ := hcl _ (mem_reachabilityFormula.mpr (.inr (.inr ⟨y, z, harc, rfl⟩)))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp only at hlσ
        exact absurd (ih.symm.trans hlσ) (by decide)
      · exact hlσ
  obtain ⟨l, hl, hlσ⟩ := hcl _ (mem_reachabilityFormula.mpr (.inr (.inl rfl)))
  rw [List.mem_singleton] at hl
  subst hl
  simp only at hlσ
  exact absurd ((key _ hst).symm.trans hlσ) (by decide)

/-- **The formula is in `TwoSAT` exactly when `t` is not reachable from `s`.** -/
theorem reachabilityFormula_mem_TwoSAT_iff (I : STCONInstance) :
    reachabilityFormula I ∈ TwoSAT ↔ I ∉ STCON := by
  have hw : ∀ c ∈ reachabilityFormula I, c.length ≤ 2 := by
    intro c hc
    rcases mem_reachabilityFormula.mp hc with rfl | rfl | ⟨u, v, -, rfl⟩ <;> simp
  rw [mem_TwoSAT, and_iff_right hw]
  refine ⟨fun ⟨σ, hσ⟩ => notMem_STCON_of_eval_reachabilityFormula hσ, fun hst => ?_⟩
  -- the reachable vertices give a satisfying assignment
  rw [mem_STCON] at hst
  classical
  let σ : ℕ → Bool := fun x => decide (∃ h : x < I.n, Relation.ReflTransGen I.Adj I.s ⟨x, h⟩)
  refine ⟨σ, (CNF.eval_eq_true_iff σ _).mpr fun c hc => (Clause.eval_eq_true_iff σ c).mpr ?_⟩
  rcases mem_reachabilityFormula.mp hc with rfl | rfl | ⟨u, v, harc, rfl⟩
  · exact ⟨_, List.mem_singleton_self _, decide_eq_true ⟨I.s.isLt, .refl⟩⟩
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [σ, decide_eq_false_iff_not]
    rintro ⟨_, hr⟩
    exact hst hr
  · simp only [arc] at harc
    split_ifs at harc with huv
    by_cases hu : σ u = true
    · refine ⟨(v, true), by simp, ?_⟩
      simp only [σ, decide_eq_true_eq] at hu ⊢
      obtain ⟨_, hr⟩ := hu
      exact ⟨huv.2, hr.tail harc⟩
    · exact ⟨(u, false), by simp, by simpa using hu⟩

/-! ### The writer -/

section Writer

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr _root_.Turing.MultiTapeTM

/-- The code writing the literal of register `r` with the polarity `sign`, placed at the label
`b`, through register `5`, and continuing at `exit`: the digits of the register, least
significant first, each after seven markers, then the fixed end of the literal. -/
def literalCode (b r : ℕ) (sign : Bool) (exit : ℕ) : List Instr :=
  [assign 5 (reg r) (b + 1),
   lt (const 0) (reg 5) (b + 2) (b + 13),
   emit true (b + 3), emit true (b + 4), emit true (b + 5), emit true (b + 6),
   emit true (b + 7), emit true (b + 8), emit true (b + 9),
   lt (mod (reg 5) (const 2)) (const 1) (b + 10) (b + 11),
   emit false (b + 12),
   emit true (b + 12),
   assign 5 (div (reg 5) (const 2)) (b + 1),
   emit true (b + 14), emit true (b + 15), emit true (b + 16), emit false (b + 17),
   emit true (b + 18), emit true (b + 19), emit true (b + 20), emit sign (b + 21),
   emit true (b + 22), emit false exit]

theorem length_literalCode (b r : ℕ) (sign : Bool) (exit : ℕ) :
    (literalCode b r sign exit).length = 23 := rfl

/-- The binary digits of a positive number: its remainder by two, then those of its half. -/
private theorem bits_of_pos {q : ℕ} (hq : 0 < q) : q.bits = decide (q % 2 = 1) :: (q / 2).bits := by
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · have hq' : q = 2 * (q / 2) := by omega
    conv_lhs => rw [hq']
    rw [Nat.bit0_bits _ (by omega), h]
    rfl
  · have hq' : q = 2 * (q / 2) + 1 := by omega
    conv_lhs => rw [hq']
    rw [Nat.bit1_bits, h]
    rfl

variable {P : CounterProgram} {w : List Bool} {B : ℕ}

/-- The digit-writing loop of `literalCode`, writing the binary digits of `q` from register `5`. -/
private theorem reachesOut_literalCode_loop {b r exit : ℕ} {sign : Bool}
    (hcode : P.CodeAt b (literalCode b r sign exit)) :
    ∀ q (regs' : List ℕ), regs'.getD 5 0 = q → 5 < regs'.length → (∀ x ∈ regs', x ≤ B) →
      P.ReachesOut w (P.Active B) (b + 1, regs') (b + 13, regs'.set 5 0)
        (q.bits.flatMap fun y => List.replicate 7 true ++ [y]) := by
  have hi (i : ℕ) (h : i < 23) := hcode i (length_literalCode b r sign exit ▸ h)
  -- the seven markers before a digit
  have hmarks : ∀ (regs' : List ℕ), (∀ x ∈ regs', x ≤ B) →
      P.ReachesOut w (P.Active B) (b + 2, regs') (b + 9, regs') (List.replicate 7 true) :=
    fun _ hB' => ReachesOut.emit (hi 2 (by omega)) hB' <| ReachesOut.emit (hi 3 (by omega)) hB' <|
      ReachesOut.emit (hi 4 (by omega)) hB' <| ReachesOut.emit (hi 5 (by omega)) hB' <|
      ReachesOut.emit (hi 6 (by omega)) hB' <| ReachesOut.emit (hi 7 (by omega)) hB' <|
      ReachesOut.emit (hi 8 (by omega)) hB' <| ReachesOut.refl _
  -- the digits
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro regs' hq hlen hB'
  refine ReachesOut.lt (hi 1 (by omega)) hB' ?_
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simp only [eval_const, eval_reg, hq, lt_irrefl, ↓reduceIte, Nat.zero_bits, List.flatMap_nil]
    rw [← hq, set_getD_self hlen]
    exact ReachesOut.refl _
  · simp only [eval_const, eval_reg, hq, hq0, ↓reduceIte]
    rw [bits_of_pos hq0, List.flatMap_cons, List.append_assoc, List.singleton_append]
    refine (hmarks regs' hB').trans ?_
    have hqB : q ≤ B := by
      rw [← hq, List.getD_eq_getElem _ _ hlen]
      exact hB' _ (List.getElem_mem hlen)
    have hhalf := ih (q / 2) (by omega) (regs'.set 5 (q / 2)) (by simp [hlen])
      (by simpa using hlen) (List.forall_mem_set_of_forall_mem hB' (by omega))
    rw [List.set_set] at hhalf
    refine ReachesOut.lt (hi 9 (by omega)) hB' ?_
    simp only [eval_mod, eval_reg, eval_const, hq]
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · simp only [h, Nat.zero_lt_one, ↓reduceIte]
      refine ReachesOut.emit (hi 10 (by omega)) hB' (ReachesOut.assign (hi 12 (by omega)) hB' ?_)
      simpa only [eval_div, eval_reg, eval_const, hq] using hhalf
    · simp only [h, lt_irrefl, ↓reduceIte]
      refine ReachesOut.emit (hi 11 (by omega)) hB' (ReachesOut.assign (hi 12 (by omega)) hB' ?_)
      simpa only [eval_div, eval_reg, eval_const, hq] using hhalf

/-- **The code of a literal writes it**, through register `5`, which ends at `0`. -/
theorem reachesOut_literalCode {b r exit : ℕ} {sign : Bool}
    (hcode : P.CodeAt b (literalCode b r sign exit)) {regs : List ℕ} (h5 : 5 < regs.length)
    (hB : ∀ x ∈ regs, x ≤ B) :
    P.ReachesOut w (P.Active B) (b, regs) (exit, regs.set 5 0)
      (literalBits (regs.getD r 0) sign) := by
  have hi (i : ℕ) (h : i < 23) := hcode i (length_literalCode b r sign exit ▸ h)
  have hrB : regs.getD r 0 ≤ B := by
    rcases lt_or_ge r regs.length with hr | hr
    · rw [List.getD_eq_getElem _ _ hr]
      exact hB _ (List.getElem_mem hr)
    · rw [List.getD_eq_default _ _ hr]
      exact Nat.zero_le _
  have hB0 : ∀ x ∈ regs.set 5 0, x ≤ B :=
    List.forall_mem_set_of_forall_mem hB (Nat.zero_le _)
  -- the register, then the end of the literal
  have htail : P.ReachesOut w (P.Active B) (b + 13, regs.set 5 0) (exit, regs.set 5 0)
      [true, true, true, false, true, true, true, sign, true, false] :=
    ReachesOut.emit (hi 13 (by omega)) hB0 <| ReachesOut.emit (hi 14 (by omega)) hB0 <|
      ReachesOut.emit (hi 15 (by omega)) hB0 <| ReachesOut.emit (hi 16 (by omega)) hB0 <|
      ReachesOut.emit (hi 17 (by omega)) hB0 <| ReachesOut.emit (hi 18 (by omega)) hB0 <|
      ReachesOut.emit (hi 19 (by omega)) hB0 <| ReachesOut.emit (hi 20 (by omega)) hB0 <|
      ReachesOut.emit (hi 21 (by omega)) hB0 <| ReachesOut.emit (hi 22 (by omega)) hB0 <|
      ReachesOut.refl _
  have hdigits := reachesOut_literalCode_loop (w := w) hcode (regs.getD r 0)
    (regs.set 5 (regs.getD r 0)) (List.getD_set_self (by omega)) (by simpa using h5)
    (List.forall_mem_set_of_forall_mem hB hrB)
  rw [List.set_set] at hdigits
  refine ReachesOut.assign (hi 0 (by omega)) hB ?_
  simp only [eval_reg]
  exact (hdigits.trans htail).of_eq rfl

/-! #### The encoding of the formula -/

/-- **The encoded formula**: the two unit clauses, then the clauses of the arcs row by row. -/
theorem encCNF_reachabilityFormula (I : STCONInstance) :
    encCNF (reachabilityFormula I) =
      literalBits I.s true ++ [false] ++ (literalBits I.t false ++ [false] ++
        (List.range I.n).flatMap fun u => (List.range I.n).flatMap fun v =>
          if arc I u v then literalBits u false ++ literalBits v true ++ [false] else []) := by
  rw [encCNF_eq_flatMap]
  simp only [reachabilityFormula, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, clauseBits, List.flatMap_assoc, List.append_assoc]
  congr 4
  refine congrArg (fun f => List.flatMap f (List.range I.n)) (funext fun u => ?_)
  refine congrArg (fun f => List.flatMap f (List.range I.n)) (funext fun v => ?_)
  split_ifs <;> simp [clauseBits]

/-! #### The program -/

/-- **The writer** of the encoded formula, on the encoded instance. Registers `0`, `1` and `2`
receive the header values `n`, `s` and `t`; registers `3` and `4` run over the rows and columns
of the matrix; register `5` holds the number whose digits are written. Labels `0` to `5` read the
header, labels `6` to `53` write the unit clauses, the nested loops at labels `54` and `57` write
the clause of every arc, and label `108` halts. -/
def writer : CounterProgram where
  code :=
    [read (reg 0) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0,
     read (add (add (reg 0) (const 1)) (reg 1)) 3 4 4,
     assign 1 (add (reg 1) (const 1)) 2,
     read (add (add (add (add (reg 0) (const 1)) (reg 1)) (const 1)) (reg 2)) 5 6 6,
     assign 2 (add (reg 2) (const 1)) 4] ++
    literalCode 6 1 true 29 ++ [emit false 30] ++
    literalCode 30 2 false 53 ++ [emit false 54] ++
    forCode 54 3 (reg 0) 57 108 ++ forCode 57 4 (reg 0) 60 56 ++
    [read (add (add (add (add (reg 0) (reg 1)) (reg 2)) (const 3))
      (add (mul (reg 3) (reg 0)) (reg 4))) 61 59 59] ++
    literalCode 61 3 false 84 ++ literalCode 84 4 true 107 ++
    [emit false 59, halt []]
  registers := 6

variable (I : STCONInstance) {B : ℕ}

private theorem bounded6 {a₀ a₁ a₂ a₃ a₄ a₅ : ℕ} (h₀ : a₀ ≤ B) (h₁ : a₁ ≤ B) (h₂ : a₂ ≤ B)
    (h₃ : a₃ ≤ B) (h₄ : a₄ ≤ B) (h₅ : a₅ ≤ B) : ∀ x ∈ [a₀, a₁, a₂, a₃, a₄, a₅], x ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Reading `I.n` from the unary header into register `0`. -/
private theorem reachesOut_header_n (hB : I.n ≤ B) :
    ∀ j ≤ I.n, writer.ReachesOut I.encode (writer.Active B) (0, [j, 0, 0, 0, 0, 0])
      (2, [I.n, 0, 0, 0, 0, 0]) [] := by
  intro j hj
  induction h : I.n - j generalizing j with
  | zero =>
    obtain rfl : j = I.n := by omega
    refine ReachesOut.read (show writer.instr 0 = _ from rfl)
      (bounded6 hB (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_reg, List.getD_cons_zero, I.getElem?_encode_n le_rfl, lt_irrefl,
      decide_false, readLabel]
    exact ReachesOut.refl _
  | succ _ ih =>
    refine ReachesOut.read (show writer.instr 0 = _ from rfl)
      (bounded6 (hj.trans hB) (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_reg, List.getD_cons_zero, I.getElem?_encode_n hj,
      show j < I.n by omega, decide_true, readLabel]
    refine ReachesOut.assign (show writer.instr 1 = _ from rfl)
      (bounded6 (hj.trans hB) (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simpa using ih (j + 1) (by omega) (by omega)

/-- Reading `I.s` from the unary header into register `1`. -/
private theorem reachesOut_header_s (hB : I.n ≤ B) :
    ∀ j ≤ (I.s : ℕ), writer.ReachesOut I.encode (writer.Active B)
      (2, [I.n, j, 0, 0, 0, 0]) (4, [I.n, I.s, 0, 0, 0, 0]) [] := by
  have hs := I.s.isLt
  intro j hj
  induction h : (I.s : ℕ) - j generalizing j with
  | zero =>
    obtain rfl : j = I.s := by omega
    refine ReachesOut.read (show writer.instr 2 = _ from rfl)
      (bounded6 hB (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_add, eval_reg, eval_const, List.getD_cons_zero, List.getD_cons_succ,
      I.getElem?_encode_s le_rfl, lt_irrefl, decide_false, readLabel]
    exact ReachesOut.refl _
  | succ _ ih =>
    refine ReachesOut.read (show writer.instr 2 = _ from rfl)
      (bounded6 hB (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_add, eval_reg, eval_const, List.getD_cons_zero, List.getD_cons_succ,
      I.getElem?_encode_s hj, show j < I.s by omega, decide_true, readLabel]
    refine ReachesOut.assign (show writer.instr 3 = _ from rfl)
      (bounded6 hB (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simpa using ih (j + 1) (by omega) (by omega)

/-- Reading `I.t` from the unary header into register `2`. -/
private theorem reachesOut_header_t (hB : I.n ≤ B) :
    ∀ j ≤ (I.t : ℕ), writer.ReachesOut I.encode (writer.Active B)
      (4, [I.n, I.s, j, 0, 0, 0]) (6, [I.n, I.s, I.t, 0, 0, 0]) [] := by
  have hs := I.s.isLt
  have ht := I.t.isLt
  intro j hj
  induction h : (I.t : ℕ) - j generalizing j with
  | zero =>
    obtain rfl : j = I.t := by omega
    refine ReachesOut.read (show writer.instr 4 = _ from rfl)
      (bounded6 hB (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_add, eval_reg, eval_const, List.getD_cons_zero, List.getD_cons_succ,
      I.getElem?_encode_t le_rfl, lt_irrefl, decide_false, readLabel]
    exact ReachesOut.refl _
  | succ _ ih =>
    refine ReachesOut.read (show writer.instr 4 = _ from rfl)
      (bounded6 hB (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_add, eval_reg, eval_const, List.getD_cons_zero, List.getD_cons_succ,
      I.getElem?_encode_t hj, show j < I.t by omega, decide_true, readLabel]
    refine ReachesOut.assign (show writer.instr 5 = _ from rfl)
      (bounded6 hB (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    simpa using ih (j + 1) (by omega) (by omega)

/-- The header is read into registers `0`, `1` and `2`. -/
private theorem reachesOut_header (hB : I.n ≤ B) :
    writer.ReachesOut I.encode (writer.Active B) (0, [0, 0, 0, 0, 0, 0])
      (6, [I.n, I.s, I.t, 0, 0, 0]) [] :=
  ((reachesOut_header_n I hB 0 (Nat.zero_le _)).trans
    ((reachesOut_header_s I hB 0 (Nat.zero_le _)).trans
      (reachesOut_header_t I hB 0 (Nat.zero_le _)))).of_eq rfl

private theorem codeAt_literal {b r exit : ℕ} {sign : Bool}
    (h : ∀ i (hi : i < 23), writer.instr (b + i) = (literalCode b r sign exit)[i]'hi) :
    writer.CodeAt b (literalCode b r sign exit) := fun i hi => h i hi

/-- Writing the clause for entry `(u, v)` of the adjacency matrix when `arc I u v` holds. -/
private theorem reachesOut_entry (hB : I.n ≤ B) {u v : ℕ} (hu : u < I.n) (hv : v < I.n) :
    writer.ReachesOut I.encode (writer.Active B)
      (60, [I.n, I.s, I.t, u, v, 0]) (59, [I.n, I.s, I.t, u, v, 0])
      (if arc I u v then literalBits u false ++ literalBits v true ++ [false] else []) := by
  -- an entry of the matrix
  have hs := I.s.isLt
  have ht := I.t.isLt
  have hb : ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), u, v, 0], z ≤ B :=
    bounded6 hB (by omega) (by omega) (hu.le.trans hB) (hv.le.trans hB) (Nat.zero_le _)
  have hlit₁ : writer.CodeAt 61 (literalCode 61 3 false 84) := codeAt_literal fun i hi => by
    interval_cases i <;> rfl
  have hlit₂ : writer.CodeAt 84 (literalCode 84 4 true 107) := codeAt_literal fun i hi => by
    interval_cases i <;> rfl
  refine ReachesOut.read (show writer.instr 60 = _ from rfl) hb ?_
  simp only [eval_add, eval_mul, eval_reg, eval_const, List.getD_cons_zero,
    List.getD_cons_succ, I.getElem?_encode_matrix hu hv]
  have harc : arc I u v = I.adj ⟨u, hu⟩ ⟨v, hv⟩ := by
    rw [arc, dite_eq_left ⟨hu, hv⟩]
  rw [← harc]
  cases arc I u v
  · exact ReachesOut.refl _
  · simp only [readLabel, ↓reduceIte]
    have h₁ := reachesOut_literalCode (w := I.encode) (B := B) hlit₁
      (regs := [I.n, I.s, I.t, u, v, 0]) (by simp) hb
    have h₂ := reachesOut_literalCode (w := I.encode) (B := B) hlit₂
      (regs := [I.n, I.s, I.t, u, v, 0]) (by simp) hb
    simp only [List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ,
      List.getD_cons_zero] at h₁ h₂
    refine (h₁.trans (h₂.trans (ReachesOut.emit (show writer.instr 107 = _ from rfl) hb
      (ReachesOut.refl _)))).of_eq ?_
    simp

/-- **The matrix row by row**: from the loop over the rows, the clauses of all arcs. -/
private theorem reachesOut_rows (hB : I.n ≤ B) {i₀ : ℕ} (hi₀ : i₀ ≤ I.n) :
    ∃ regs, writer.ReachesOut I.encode (writer.Active B)
      (54, [I.n, I.s, I.t, i₀, 0, 0]) (108, regs)
      ((List.range I.n).flatMap fun u => (List.range I.n).flatMap fun v =>
        if arc I u v then literalBits u false ++ literalBits v true ++ [false] else []) ∧
      ∀ x ∈ regs, x ≤ B := by
  have hs := I.s.isLt
  have ht := I.t.isLt
  have hreg : ∀ {u v y : ℕ}, u ≤ I.n → v ≤ I.n → y ≤ I.n →
      ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), u, v, y], z ≤ B := fun hu hv hy =>
    bounded6 hB (by omega) (by omega) (hu.trans hB) (hv.trans hB) (hy.trans hB)
  have hcode₁ : writer.CodeAt 54 (forCode 54 3 (reg 0) 57 108) := by
    simp only [forCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl⟩
  have hcode₂ : writer.CodeAt 57 (forCode 57 4 (reg 0) 60 56) := by
    simp only [forCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨regs, hreach, x, rfl, -, hx⟩ := reachesOut_forCode (w := I.encode) (N := I.n)
    (o := fun u => (List.range I.n).flatMap fun v =>
      if arc I u v then literalBits u false ++ literalBits v true ++ [false] else []) hcode₁
    (fun u regs => ∃ x, regs = [I.n, I.s, I.t, u, x, 0] ∧ u ≤ I.n ∧ x ≤ I.n) hB
    (by
      rintro u regs ⟨x, rfl, hu, hx⟩
      exact ⟨rfl, rfl, by simp, hreg hu hx (Nat.zero_le _)⟩)
    (by
      rintro u hu regs ⟨x, rfl, -, hx⟩
      obtain ⟨regs', hreach, rfl, -⟩ := reachesOut_forCode (w := I.encode) (N := I.n)
        (o := fun v => if arc I u v then literalBits u false ++ literalBits v true ++ [false]
          else []) hcode₂
        (fun v regs => regs = [I.n, I.s, I.t, u, v, 0] ∧ v ≤ I.n) hB
        (by
          rintro v regs ⟨rfl, hv⟩
          exact ⟨rfl, rfl, by simp, hreg hu.le hv (Nat.zero_le _)⟩)
        (by
          rintro v hv regs ⟨rfl, -⟩
          exact ⟨_, reachesOut_entry I hB hu hv, rfl, hreg hu.le hv.le (Nat.zero_le _), by simp,
            by omega⟩)
        [I.n, I.s, I.t, u, x, 0]
        (hreg hu.le hx (Nat.zero_le _)) ⟨by simp, by omega⟩
      exact ⟨_, hreach, rfl, hreg hu.le le_rfl (Nat.zero_le _), I.n, by simp, by omega, le_rfl⟩)
    [I.n, I.s, I.t, i₀, 0, 0]
    (hreg hi₀ (Nat.zero_le _) (Nat.zero_le _)) ⟨0, by simp, by omega, by omega⟩
  exact ⟨_, hreach, hreg le_rfl hx (Nat.zero_le _)⟩

/-- **The formula is computed in logarithmic space** from the encoded instance. -/
theorem computableInLogSpace_reachabilityFormula :
    ComputableInLogSpace reachabilityFormula encSTCON encCNF := by
  refine writer.computableInLogSpace_of_reachesOut 1 fun I => ?_
  simp only [encSTCON_apply, pow_one]
  have hlen := I.length_encode
  have hB : I.n ≤ I.encode.length + 1 := by omega
  have hs := I.s.isLt
  have ht := I.t.isLt
  have hlit₁ : writer.CodeAt 6 (literalCode 6 1 true 29) := codeAt_literal fun i hi => by
    interval_cases i <;> rfl
  have hlit₂ : writer.CodeAt 30 (literalCode 30 2 false 53) := codeAt_literal fun i hi => by
    interval_cases i <;> rfl
  have hb : ∀ x ∈ [I.n, (I.s : ℕ), (I.t : ℕ), 0, 0, 0], x ≤ I.encode.length + 1 :=
    bounded6 hB (by omega) (by omega) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have h₁ := reachesOut_literalCode (w := I.encode) hlit₁ (by simp) hb
  have h₂ := reachesOut_literalCode (w := I.encode) hlit₂ (by simp) hb
  simp only [List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ,
    List.getD_cons_zero] at h₁ h₂
  obtain ⟨regs, hrows, hregs⟩ := reachesOut_rows I hB (i₀ := 0) (Nat.zero_le _)
  have hchain := (reachesOut_header I hB).trans (h₁.trans (ReachesOut.emit
    (show writer.instr 29 = _ from rfl) hb (h₂.trans (ReachesOut.emit
      (show writer.instr 53 = _ from rfl) hb hrows))))
  refine ⟨(108, regs), _, [], hchain, rfl, ?_, hregs⟩
  rw [encCNF_reachabilityFormula]
  simp

end Writer

end TwoSAT

end Cslib.Complexity
