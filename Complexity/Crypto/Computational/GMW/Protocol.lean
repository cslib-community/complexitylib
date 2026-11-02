/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Crypto.Computational.Commitment
public import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Computability.Probabilistic.Sampling

/-!
# Three-copy masked-3SAT commitment protocol for GMW zero-knowledge

This module defines the two-round interactive protocol used to prove Goldreich, Micali, and
Wigderson's theorem [GoldreichMicaliWigderson1991] that every language in `NP` has a computational
zero-knowledge interactive proof system from one-way functions (via Naor's bit commitment scheme
[Naor1991] and `ThreeSAT_npHard`).

Rather than GMW's original 3-coloring protocol, we formalize a direct 3-copy masked-3SAT
truth-table commitment protocol: in each of 3 parallel copies, the prover samples a random mask `m`
for the variables of the 3CNF formula `φ` and commits (via `naorCommit`) to `copyLen φ` bits
consisting of `m`, the XOR-masked assignment `v = w ⊕ m`, and the 8-bit truth table of each clause
under inputs `t ⊕ m`. A 3-bit challenge `ch` selects for each copy whether to open `m` and the full
clause truth tables (`ch[j] = false`) or `v` and the active truth-table entries (`ch[j] = true`).

## Main definitions

* `Cslib.Crypto.GMW.realBits`, `Cslib.Crypto.GMW.simBits`, `Cslib.Crypto.GMW.allOpenFlags`:
  committed bit layouts and selective-opening masks across the three protocol copies.
* `Cslib.Crypto.GMW.proverReply1`, `Cslib.Crypto.GMW.proverReply2`,
  `Cslib.Crypto.GMW.verifyTranscript`: prover round functions and verifier transcript predicate.
* `Cslib.Crypto.GMW.runTwoRound`: two-round deterministic oracle handler in `ProbComp`.
* `Cslib.Crypto.GMW.gmwProver`, `Cslib.Crypto.GMW.gmwInteract`: honest prover strategy and its
  `ProbComp` realization.
* `Cslib.Crypto.GMW.gmwVerifier`: honest two-round GMW verifier.

## Main results

* `Cslib.Crypto.GMW.naorMaskBits_realBits`: selectively opening the honest committed bits under any
  challenge `ch` and valid witness `w` yields `simBits`.
* `Cslib.Crypto.GMW.run_gmwProver_fst`, `Cslib.Crypto.GMW.eval_gmwInteract`: running a verifier
  against `gmwProver` coincides with `gmwInteract`.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001], Chapter 4.
-/

@[expose] public section

namespace Cslib.Crypto.GMW

open Probability Complexity Logic.PL
open scoped NNReal ENNReal

/-! ### Masked 3SAT truth-table gadgets -/

/-- Bit 0 of a 3-bit truth-table row index `t < 8`. -/
def gmwBit0Of8 (t : ℕ) : Bool := (t == 1) || (t == 3) || (t == 5) || (t == 7)

/-- Bit 1 of a 3-bit truth-table row index `t < 8`. -/
def gmwBit1Of8 (t : ℕ) : Bool := (t == 2) || (t == 3) || (t == 6) || (t == 7)

/-- Bit 2 of a 3-bit truth-table row index `t < 8`. -/
def gmwBit2Of8 (t : ℕ) : Bool := (t == 4) || (t == 5) || (t == 6) || (t == 7)

/-- Pack three literal-variable bits into an active truth-table row index in `0..7`. -/
def gmwActiveIdx (b₀ b₁ b₂ : Bool) : ℕ :=
  (if b₀ then 1 else 0) + 2 * (if b₁ then 1 else 0) + 4 * (if b₂ then 1 else 0)

theorem gmwActiveIdx_lt_eight (b₀ b₁ b₂ : Bool) : gmwActiveIdx b₀ b₁ b₂ < 8 := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> decide

@[simp] theorem gmwBit0Of8_gmwActiveIdx (b₀ b₁ b₂ : Bool) :
    gmwBit0Of8 (gmwActiveIdx b₀ b₁ b₂) = b₀ := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> decide

@[simp] theorem gmwBit1Of8_gmwActiveIdx (b₀ b₁ b₂ : Bool) :
    gmwBit1Of8 (gmwActiveIdx b₀ b₁ b₂) = b₁ := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> decide

@[simp] theorem gmwBit2Of8_gmwActiveIdx (b₀ b₁ b₂ : Bool) :
    gmwBit2Of8 (gmwActiveIdx b₀ b₁ b₂) = b₂ := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> decide

/-- Evaluate a clause of length at most 3 given the truth values of its first three literals'
variables. -/
def clauseEvalBits (c : Clause ℕ) (b₀ b₁ b₂ : Bool) : Bool :=
  (decide (0 < c.length) && (b₀ == (c.getD 0 (0, false)).2)) ||
  (decide (1 < c.length) && (b₁ == (c.getD 1 (0, false)).2)) ||
  (decide (2 < c.length) && (b₂ == (c.getD 2 (0, false)).2))

theorem clauseEvalBits_eq_eval {c : Clause ℕ} (hc : c.length ≤ 3) (σ : ℕ → Bool) :
    clauseEvalBits c (σ (c.getD 0 (0, false)).1) (σ (c.getD 1 (0, false)).1)
      (σ (c.getD 2 (0, false)).1) = c.eval σ := by
  rcases c with _ | ⟨⟨v₀, p₀⟩, _ | ⟨⟨v₁, p₁⟩, _ | ⟨⟨v₂, p₂⟩, _ | ⟨_, _⟩⟩⟩⟩
  · rfl
  · simp [clauseEvalBits]
  · simp [clauseEvalBits]
  · simp [clauseEvalBits, Bool.or_assoc]
  · simp only [List.length_cons] at hc; omega

/-- Look up the bit for variable `v` in `vec` at its first occurrence in `φ.vars`, returning
`false` when `v ∉ φ.vars`. -/
def varBit (φ : CNF ℕ) (vec : List Bool) (v : ℕ) : Bool :=
  if φ.vars.idxOf v < φ.vars.length then vec.getD (φ.vars.idxOf v) false else false

private theorem varBit_eq_assignment {φ : CNF ℕ} (vec : List Bool) {v : ℕ} (hv : v ∈ φ.vars) :
    varBit φ vec v = SAT.assignment φ vec v := by
  simp [varBit, SAT.assignment, List.idxOf_lt_length_iff.mpr hv]

private theorem eval_varBit_eq (φ : CNF ℕ) (vec : List Bool) :
    φ.eval (varBit φ vec) = φ.eval (SAT.assignment φ vec) :=
  CNF.eval_congr (fun _ hv => varBit_eq_assignment vec hv)

@[simp] theorem varBit_listXor (φ : CNF ℕ) (w m : List Bool) (v : ℕ) :
    varBit φ (BitString.listXor φ.vars.length [w, m]) v = (varBit φ w v ^^ varBit φ m v) := by
  unfold varBit; split_ifs with hlt
  · exact BitString.getD_listXor_pair φ.vars.length w m (φ.vars.idxOf v) hlt
  · rfl

@[simp] theorem varBit_listRow (φ : CNF ℕ) (vec : List Bool) (v : ℕ) :
    varBit φ (BitString.listRow φ.vars.length 0 vec) v = varBit φ vec v := by
  unfold varBit; split_ifs with hlt
  · exact BitString.getD_listRow_zero φ.vars.length vec (φ.vars.idxOf v) hlt
  · rfl

/-- The 8-bit masked truth table of clause `c` under variable mask `m`. -/
def clauseTableRow (φ : CNF ℕ) (m : List Bool) (c : Clause ℕ) : List Bool :=
  let m₀ := varBit φ m (c.getD 0 (0, false)).1
  let m₁ := varBit φ m (c.getD 1 (0, false)).1
  let m₂ := varBit φ m (c.getD 2 (0, false)).1
  (List.range 8).map fun t =>
    clauseEvalBits c (gmwBit0Of8 t ^^ m₀) (gmwBit1Of8 t ^^ m₁) (gmwBit2Of8 t ^^ m₂)

/-- The 8-bit indicator of the active row of clause `c` under masked assignment `v`. -/
def clauseActiveRow (φ : CNF ℕ) (v : List Bool) (c : Clause ℕ) : List Bool :=
  let v₀ := varBit φ v (c.getD 0 (0, false)).1
  let v₁ := varBit φ v (c.getD 1 (0, false)).1
  let v₂ := varBit φ v (c.getD 2 (0, false)).1
  let active := gmwActiveIdx v₀ v₁ v₂
  (List.range 8).map fun t => decide (t = active)

@[simp] theorem length_clauseTableRow (φ : CNF ℕ) (m : List Bool) (c : Clause ℕ) :
    (clauseTableRow φ m c).length = 8 := by simp [clauseTableRow]

@[simp] theorem length_clauseActiveRow (φ : CNF ℕ) (v : List Bool) (c : Clause ℕ) :
    (clauseActiveRow φ v c).length = 8 := by simp [clauseActiveRow]

@[simp] theorem clauseTableRow_listRow (φ : CNF ℕ) (m : List Bool) (c : Clause ℕ) :
    clauseTableRow φ (BitString.listRow φ.vars.length 0 m) c = clauseTableRow φ m c := by
  simp [clauseTableRow]

@[simp] theorem clauseActiveRow_listRow (φ : CNF ℕ) (v : List Bool) (c : Clause ℕ) :
    clauseActiveRow φ (BitString.listRow φ.vars.length 0 v) c = clauseActiveRow φ v c := by
  simp [clauseActiveRow]

private theorem naorMaskBits_eq_self_of_imp {openFlags bits : List Bool}
    (hlen : openFlags.length = bits.length)
    (himp : ∀ i, openFlags.getD i false = true → bits.getD i false = true) :
    naorMaskBits openFlags bits = openFlags := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi hi'
  have hlt : i < bits.length := by simpa [hlen] using hi
  have h := getD_naorMaskBits openFlags bits i
  have hopen : openFlags.getD i false = openFlags[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  have hmask : (naorMaskBits openFlags bits).getD i false = (naorMaskBits openFlags bits)[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [← hmask, h, hopen]
  cases hflag : openFlags[i]
  · simp
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] using
      himp i (hopen.trans hflag)

theorem getD_clauseTableRow (φ : CNF ℕ) (m : List Bool) (c : Clause ℕ) {t : ℕ} (ht : t < 8) :
    (clauseTableRow φ m c).getD t false =
      clauseEvalBits c
        (gmwBit0Of8 t ^^ varBit φ m (c.getD 0 (0, false)).1)
        (gmwBit1Of8 t ^^ varBit φ m (c.getD 1 (0, false)).1)
        (gmwBit2Of8 t ^^ varBit φ m (c.getD 2 (0, false)).1) := by
  simp [clauseTableRow, List.getD_eq_getElem?_getD, ht]

theorem getD_clauseActiveRow (φ : CNF ℕ) (v : List Bool) (c : Clause ℕ) {t : ℕ} (ht : t < 8) :
    (clauseActiveRow φ v c).getD t false =
      decide (t = gmwActiveIdx
        (varBit φ v (c.getD 0 (0, false)).1)
        (varBit φ v (c.getD 1 (0, false)).1)
        (varBit φ v (c.getD 2 (0, false)).1)) := by
  simp [clauseActiveRow, List.getD_eq_getElem?_getD, ht]

private theorem naorMaskBits_clauseActiveRow {φ : CNF ℕ} {w m : List Bool} {c : Clause ℕ}
    (hc_len : c.length ≤ 3) (hc_eval : c.eval (varBit φ w) = true) :
    naorMaskBits (clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]) c)
      (clauseTableRow φ m c) =
      clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]) c := by
  apply naorMaskBits_eq_self_of_imp (by simp)
  intro t ht
  by_cases hlt : t < 8
  · rw [getD_clauseActiveRow φ _ c hlt, decide_eq_true_eq] at ht
    rw [getD_clauseTableRow φ m c hlt, ht, gmwBit0Of8_gmwActiveIdx, gmwBit1Of8_gmwActiveIdx,
      gmwBit2Of8_gmwActiveIdx]
    simp only [varBit_listXor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    rw [clauseEvalBits_eq_eval hc_len (varBit φ w), hc_eval]
  · have hge : (clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]) c).length ≤ t := by
      simp only [length_clauseActiveRow]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at ht

/-- The `8 * φ.length`-bit concatenation of all clause truth tables of `φ` under mask `m`. -/
def tableBits (φ : CNF ℕ) (m : List Bool) : List Bool := (φ.map (clauseTableRow φ m)).flatten

/-- The `8 * φ.length`-bit concatenation of all active-row indicators of `φ` under `v`. -/
def activeTableFlags (φ : CNF ℕ) (v : List Bool) : List Bool :=
  (φ.map (clauseActiveRow φ v)).flatten

private theorem length_flatten_map_eight {α : Type} (xs : List α) (f : α → List Bool)
    (hf : ∀ x ∈ xs, (f x).length = 8) : (xs.map f).flatten.length = 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      hf x List.mem_cons_self, ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))]
    omega

@[simp] theorem length_tableBits (φ : CNF ℕ) (m : List Bool) :
    (tableBits φ m).length = 8 * φ.length :=
  length_flatten_map_eight φ (clauseTableRow φ m) (fun _ _ => length_clauseTableRow _ _ _)

@[simp] theorem length_activeTableFlags (φ : CNF ℕ) (v : List Bool) :
    (activeTableFlags φ v).length = 8 * φ.length :=
  length_flatten_map_eight φ (clauseActiveRow φ v) (fun _ _ => length_clauseActiveRow _ _ _)

@[simp] theorem tableBits_listRow (φ : CNF ℕ) (m : List Bool) :
    tableBits φ (BitString.listRow φ.vars.length 0 m) = tableBits φ m := by
  have h : clauseTableRow φ (BitString.listRow φ.vars.length 0 m) = clauseTableRow φ m :=
    funext (clauseTableRow_listRow φ m)
  simp [tableBits, h]

@[simp] theorem activeTableFlags_listRow (φ : CNF ℕ) (v : List Bool) :
    activeTableFlags φ (BitString.listRow φ.vars.length 0 v) = activeTableFlags φ v := by
  have h : clauseActiveRow φ (BitString.listRow φ.vars.length 0 v) = clauseActiveRow φ v :=
    funext (clauseActiveRow_listRow φ v)
  simp [activeTableFlags, h]

private theorem naorMaskBits_activeTableFlags {φ : CNF ℕ} {w m : List Bool}
    (hw : ThreeSAT.verifier (φ, w) = true) :
    naorMaskBits (activeTableFlags φ (BitString.listXor φ.vars.length [w, m]))
      (tableBits φ m) =
      activeTableFlags φ (BitString.listXor φ.vars.length [w, m]) := by
  simp only [ThreeSAT.verifier, SAT.verifier, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, ← eval_varBit_eq, CNF.eval_eq_true_iff] at hw
  rcases hw with ⟨hlen, heval⟩
  unfold activeTableFlags tableBits
  have hrec : ∀ cs : List (Clause ℕ),
      (∀ c ∈ cs, c.length ≤ 3) → (∀ c ∈ cs, c.eval (varBit φ w) = true) →
      naorMaskBits (cs.map (clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]))).flatten
        (cs.map (clauseTableRow φ m)).flatten =
        (cs.map (clauseActiveRow φ (BitString.listXor φ.vars.length [w, m]))).flatten := by
    intro cs hcs_len hcs_eval
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, List.flatten_cons]
      rw [naorMaskBits_append (by simp),
        naorMaskBits_clauseActiveRow (hcs_len c List.mem_cons_self)
          (hcs_eval c List.mem_cons_self),
        ih (fun c' hc' => hcs_len c' (List.mem_cons_of_mem _ hc'))
          (fun c' hc' => hcs_eval c' (List.mem_cons_of_mem _ hc'))]
  exact hrec φ hlen heval

/-! ### Single-copy and three-copy bit layouts -/

private theorem take_drop_three_1 {w : ℕ} {a b c : List Bool} (ha : a.length = w)
    (hb : b.length = w) : ((a ++ b ++ c).drop w).take w = b := by
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hb]

private theorem take_drop_three_2 {w u : ℕ} {a b c : List Bool} (ha : a.length = w)
    (hb : b.length = w) (hc : c.length = u) : ((a ++ b ++ c).drop (2 * w)).take u = c := by
  have hab : (a ++ b).length = 2 * w := by simp [ha, hb, Nat.two_mul]
  rw [List.drop_left' hab, List.take_of_length_le hc.le]

/-- Number of committed bits in one copy of the masked 3SAT gadget:
`φ.vars.length` mask bits, `φ.vars.length` masked assignment bits, and `8 * φ.length` table bits. -/
def copyLen (φ : CNF ℕ) : ℕ := 2 * φ.vars.length + 8 * φ.length

/-- Number of committed bits across all three parallel copies. -/
def totalLen (φ : CNF ℕ) : ℕ := 3 * copyLen φ

/-- Extract the `m` segment (first `φ.vars.length` bits) of a copy. -/
def mPart (φ : CNF ℕ) (copy : List Bool) : List Bool := copy.take φ.vars.length

/-- Extract the `v` segment (second `φ.vars.length` bits) of a copy. -/
def vPart (φ : CNF ℕ) (copy : List Bool) : List Bool :=
  (copy.drop φ.vars.length).take φ.vars.length

/-- Extract the truth-table segment (`8 * φ.length` bits) of a copy. -/
def tablePart (φ : CNF ℕ) (copy : List Bool) : List Bool :=
  (copy.drop (2 * φ.vars.length)).take (8 * φ.length)

/-- Honest committed bits for one copy given witness `w` and mask `m`. -/
def realCopyBits (φ : CNF ℕ) (w m : List Bool) : List Bool :=
  BitString.listRow φ.vars.length 0 m ++ BitString.listXor φ.vars.length [w, m] ++ tableBits φ m

/-- Simulated (and selectively opened) bits for one copy given challenge bit `b` and random word
`rand` of length `φ.vars.length`. -/
def simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) : List Bool :=
  if b then
    List.replicate φ.vars.length false ++ BitString.listRow φ.vars.length 0 rand ++
      activeTableFlags φ rand
  else
    BitString.listRow φ.vars.length 0 rand ++ List.replicate φ.vars.length false ++
      tableBits φ rand

/-- Selective-opening flags for one copy under challenge bit `b`. -/
def copyOpenFlags (φ : CNF ℕ) (b : Bool) (copy : List Bool) : List Bool :=
  if b then
    List.replicate φ.vars.length false ++ List.replicate φ.vars.length true ++
      activeTableFlags φ (vPart φ copy)
  else
    List.replicate φ.vars.length true ++ List.replicate φ.vars.length false ++
      List.replicate (8 * φ.length) true

@[simp] theorem length_realCopyBits (φ : CNF ℕ) (w m : List Bool) :
    (realCopyBits φ w m).length = copyLen φ := by
  simp [realCopyBits, copyLen, Nat.two_mul, Nat.add_assoc]

@[simp] theorem length_simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) :
    (simCopyBits φ b rand).length = copyLen φ := by
  cases b <;> simp [simCopyBits, copyLen, Nat.two_mul, Nat.add_assoc]

@[simp] theorem length_copyOpenFlags (φ : CNF ℕ) (b : Bool) (copy : List Bool) :
    (copyOpenFlags φ b copy).length = copyLen φ := by
  cases b <;> simp [copyOpenFlags, copyLen, Nat.two_mul, Nat.add_assoc]

@[simp] theorem vPart_realCopyBits (φ : CNF ℕ) (w m : List Bool) :
    vPart φ (realCopyBits φ w m) = BitString.listXor φ.vars.length [w, m] :=
  take_drop_three_1 (by simp) (by simp)

@[simp] theorem mPart_simCopyBits_false (φ : CNF ℕ) (rand : List Bool) :
    mPart φ (simCopyBits φ false rand) = BitString.listRow φ.vars.length 0 rand := by
  simp only [mPart, simCopyBits, Bool.false_eq_true, ↓reduceIte]
  rw [List.append_assoc, List.take_left' (by simp)]

@[simp] theorem vPart_simCopyBits_true (φ : CNF ℕ) (rand : List Bool) :
    vPart φ (simCopyBits φ true rand) = BitString.listRow φ.vars.length 0 rand :=
  take_drop_three_1 (by simp) (by simp)

@[simp] theorem tablePart_simCopyBits_false (φ : CNF ℕ) (rand : List Bool) :
    tablePart φ (simCopyBits φ false rand) = tableBits φ rand :=
  take_drop_three_2 (by simp) (by simp) (by simp)

@[simp] theorem tablePart_simCopyBits_true (φ : CNF ℕ) (rand : List Bool) :
    tablePart φ (simCopyBits φ true rand) = activeTableFlags φ rand :=
  take_drop_three_2 (by simp) (by simp) (by simp)

private theorem naorMaskBits_replicate_true {bits : List Bool} {n : ℕ} (h : bits.length = n) :
    naorMaskBits (List.replicate n true) bits = bits := by
  subst n; induction bits with
  | nil => rfl
  | cons b bits ih => simp [naorMaskBits, List.replicate_succ, ih]

private theorem naorMaskBits_replicate_false {bits : List Bool} {n : ℕ} (h : bits.length = n) :
    naorMaskBits (List.replicate n false) bits = List.replicate n false := by
  subst n; induction bits with
  | nil => rfl
  | cons b bits ih => simp [naorMaskBits, List.replicate_succ, ih]

private theorem naorMaskBits_realCopyBits_false (φ : CNF ℕ) (w m : List Bool) :
    naorMaskBits (copyOpenFlags φ false (realCopyBits φ w m)) (realCopyBits φ w m) =
      simCopyBits φ false m := by
  simp only [copyOpenFlags, Bool.false_eq_true, ↓reduceIte, realCopyBits, simCopyBits]
  rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
    naorMaskBits_replicate_true (by simp), naorMaskBits_replicate_false (by simp),
    naorMaskBits_replicate_true (by simp)]

private theorem naorMaskBits_realCopyBits_true {φ : CNF ℕ} {w m : List Bool}
    (hw : ThreeSAT.verifier (φ, w) = true) :
    naorMaskBits (copyOpenFlags φ true (realCopyBits φ w m)) (realCopyBits φ w m) =
      simCopyBits φ true (BitString.listXor φ.vars.length [w, m]) := by
  have hrow_xor : BitString.listRow φ.vars.length 0 (BitString.listXor φ.vars.length [w, m]) =
      BitString.listXor φ.vars.length [w, m] := by
    simp [BitString.listRow, List.take_left' (BitString.length_listXor φ.vars.length [w, m])]
  simp only [copyOpenFlags, ↓reduceIte, vPart_realCopyBits]
  simp only [realCopyBits, simCopyBits, ↓reduceIte, hrow_xor]
  rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
    naorMaskBits_replicate_false (by simp), naorMaskBits_replicate_true (by simp),
    naorMaskBits_activeTableFlags hw]

private theorem copyOpenFlags_simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) :
    copyOpenFlags φ b (simCopyBits φ b rand) =
      if b then
        List.replicate φ.vars.length false ++ List.replicate φ.vars.length true ++
          activeTableFlags φ rand
      else
        List.replicate φ.vars.length true ++ List.replicate φ.vars.length false ++
          List.replicate (8 * φ.length) true := by
  cases b <;> simp [copyOpenFlags]

private theorem copyOpenFlags_realCopyBits (φ : CNF ℕ) (b : Bool) (w m : List Bool) :
    copyOpenFlags φ b (realCopyBits φ w m) =
      copyOpenFlags φ b
        (simCopyBits φ b (if b then BitString.listXor φ.vars.length [w, m] else m)) := by
  cases b <;> simp [copyOpenFlags]

@[simp] theorem naorMaskBits_simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) :
    naorMaskBits (copyOpenFlags φ b (simCopyBits φ b rand)) (simCopyBits φ b rand) =
      simCopyBits φ b rand := by
  rw [copyOpenFlags_simCopyBits]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, simCopyBits]
    rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
      naorMaskBits_replicate_true (by simp), naorMaskBits_replicate_false (by simp),
      naorMaskBits_replicate_true (by simp)]
  · simp only [↓reduceIte, simCopyBits]
    rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
      naorMaskBits_replicate_false (by simp), naorMaskBits_replicate_true (by simp),
      naorMaskBits_eq_self_of_imp (by simp) (fun _ h => h)]

/-- Check the opened bits of one copy against challenge bit `b`. -/
def verifyCopyBits (φ : CNF ℕ) (b : Bool) (copy : List Bool) : Bool :=
  if b then
    (List.range (8 * φ.length)).all fun i =>
      !(activeTableFlags φ (vPart φ copy)).getD i false || (tablePart φ copy).getD i false
  else
    tablePart φ copy == tableBits φ (mPart φ copy)

@[simp] theorem verifyCopyBits_simCopyBits (φ : CNF ℕ) (b : Bool) (rand : List Bool) :
    verifyCopyBits φ b (simCopyBits φ b rand) = true := by
  cases b
  · simp [verifyCopyBits]
  · simp only [verifyCopyBits, ↓reduceIte, vPart_simCopyBits_true, activeTableFlags_listRow,
      tablePart_simCopyBits_true, List.all_eq_true]
    intro i _; cases (activeTableFlags φ rand).getD i false <;> rfl

/-! ### Three-copy protocol messages and verification -/

/-- Extract copy 0 (`copyLen φ` bits) from a 3-copy GMW bit vector. -/
def gmwCopy0 (φ : CNF ℕ) (bits : List Bool) : List Bool := bits.take (copyLen φ)

/-- Extract copy 1 (`copyLen φ` bits) from a 3-copy GMW bit vector. -/
def gmwCopy1 (φ : CNF ℕ) (bits : List Bool) : List Bool :=
  (bits.drop (copyLen φ)).take (copyLen φ)

/-- Extract copy 2 (`copyLen φ` bits) from a 3-copy GMW bit vector. -/
def gmwCopy2 (φ : CNF ℕ) (bits : List Bool) : List Bool :=
  (bits.drop (2 * copyLen φ)).take (copyLen φ)

/-- Honest committed bits across all three copies. -/
def realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) : List Bool :=
  realCopyBits φ w m₀ ++ realCopyBits φ w m₁ ++ realCopyBits φ w m₂

/-- Simulated (and selectively opened) bits across all three copies. -/
def simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) : List Bool :=
  simCopyBits φ (ch.getD 0 false) r₀ ++ simCopyBits φ (ch.getD 1 false) r₁ ++
    simCopyBits φ (ch.getD 2 false) r₂

/-- Selective-opening flags across all three copies under challenge word `ch`. -/
def allOpenFlags (φ : CNF ℕ) (ch bits : List Bool) : List Bool :=
  copyOpenFlags φ (ch.getD 0 false) (gmwCopy0 φ bits) ++
    copyOpenFlags φ (ch.getD 1 false) (gmwCopy1 φ bits) ++
    copyOpenFlags φ (ch.getD 2 false) (gmwCopy2 φ bits)

@[simp] theorem length_realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) :
    (realBits φ w m₀ m₁ m₂).length = totalLen φ := by
  simp only [realBits, totalLen, List.length_append, length_realCopyBits]; omega

@[simp] theorem length_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    (simBits φ ch r₀ r₁ r₂).length = totalLen φ := by
  simp only [simBits, totalLen, List.length_append, length_simCopyBits]; omega

@[simp] theorem length_allOpenFlags (φ : CNF ℕ) (ch bits : List Bool) :
    (allOpenFlags φ ch bits).length = totalLen φ := by
  simp only [allOpenFlags, totalLen, List.length_append, length_copyOpenFlags]; omega

@[simp] theorem gmwCopy0_realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) :
    gmwCopy0 φ (realBits φ w m₀ m₁ m₂) = realCopyBits φ w m₀ := by
  simp only [gmwCopy0, realBits]; rw [List.append_assoc, List.take_left' (by simp)]

@[simp] theorem gmwCopy1_realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) :
    gmwCopy1 φ (realBits φ w m₀ m₁ m₂) = realCopyBits φ w m₁ :=
  take_drop_three_1 (by simp) (by simp)

@[simp] theorem gmwCopy2_realBits (φ : CNF ℕ) (w m₀ m₁ m₂ : List Bool) :
    gmwCopy2 φ (realBits φ w m₀ m₁ m₂) = realCopyBits φ w m₂ :=
  take_drop_three_2 (by simp) (by simp) (by simp)

@[simp] theorem gmwCopy0_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    gmwCopy0 φ (simBits φ ch r₀ r₁ r₂) = simCopyBits φ (ch.getD 0 false) r₀ := by
  simp only [gmwCopy0, simBits]; rw [List.append_assoc, List.take_left' (by simp)]

@[simp] theorem gmwCopy1_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    gmwCopy1 φ (simBits φ ch r₀ r₁ r₂) = simCopyBits φ (ch.getD 1 false) r₁ :=
  take_drop_three_1 (by simp) (by simp)

@[simp] theorem gmwCopy2_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    gmwCopy2 φ (simBits φ ch r₀ r₁ r₂) = simCopyBits φ (ch.getD 2 false) r₂ :=
  take_drop_three_2 (by simp) (by simp) (by simp)

private theorem naorMaskBits_realCopyBits {φ : CNF ℕ} {w m : List Bool} (b : Bool)
    (hw : ThreeSAT.verifier (φ, w) = true) :
    naorMaskBits (copyOpenFlags φ b (realCopyBits φ w m)) (realCopyBits φ w m) =
      simCopyBits φ b (if b then BitString.listXor φ.vars.length [w, m] else m) := by
  cases b
  · exact naorMaskBits_realCopyBits_false φ w m
  · exact naorMaskBits_realCopyBits_true hw

theorem naorMaskBits_realBits {φ : CNF ℕ} {w m₀ m₁ m₂ : List Bool} (ch : List Bool)
    (hw : ThreeSAT.verifier (φ, w) = true) :
    naorMaskBits (allOpenFlags φ ch (realBits φ w m₀ m₁ m₂)) (realBits φ w m₀ m₁ m₂) =
      simBits φ ch
        (if ch.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀)
        (if ch.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁)
        (if ch.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂) := by
  simp only [allOpenFlags, gmwCopy0_realBits, gmwCopy1_realBits, gmwCopy2_realBits]
  simp only [realBits, simBits]
  rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
    naorMaskBits_realCopyBits _ hw, naorMaskBits_realCopyBits _ hw, naorMaskBits_realCopyBits _ hw]

theorem allOpenFlags_realBits (φ : CNF ℕ) (ch w m₀ m₁ m₂ : List Bool) :
    allOpenFlags φ ch (realBits φ w m₀ m₁ m₂) =
      allOpenFlags φ ch
        (simBits φ ch
          (if ch.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀)
          (if ch.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁)
          (if ch.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂)) := by
  simp only [allOpenFlags, gmwCopy0_realBits, gmwCopy1_realBits, gmwCopy2_realBits,
    gmwCopy0_simBits, gmwCopy1_simBits, gmwCopy2_simBits, copyOpenFlags_realCopyBits]

@[simp] theorem naorMaskBits_simBits (φ : CNF ℕ) (ch r₀ r₁ r₂ : List Bool) :
    naorMaskBits (allOpenFlags φ ch (simBits φ ch r₀ r₁ r₂)) (simBits φ ch r₀ r₁ r₂) =
      simBits φ ch r₀ r₁ r₂ := by
  simp only [allOpenFlags, gmwCopy0_simBits, gmwCopy1_simBits, gmwCopy2_simBits]
  simp only [simBits]
  rw [naorMaskBits_append (by simp), naorMaskBits_append (by simp),
    naorMaskBits_simCopyBits, naorMaskBits_simCopyBits, naorMaskBits_simCopyBits]

/-- Prover's first-round message: flat list of `totalLen φ` Naor commitments. -/
def proverReply1 (generator : List Bool → List Bool) (m : ℕ)
    (r openFlags bits : List Bool) (seeds pads : List (List Bool)) : List Bool :=
  ((naorCommitSplit generator (BitString.listRow m 0 r) openFlags bits seeds pads).flatten).take
    (bits.length * m)

/-- Prover's second-round message: masked bits followed by flat selected seeds. -/
def proverReply2 (s : ℕ) (φ : CNF ℕ) (ch bits : List Bool) (seeds : List (List Bool)) : List Bool :=
  let flags := allOpenFlags φ ch bits
  naorMaskBits flags bits ++ (naorSelectSeeds s flags bits seeds).flatten

/-- Check that every active position `i < totalLen φ` opens to the committed word in
`commitReply`. -/
def verifyCommitments (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (r flags commitReply openedBits openSeedsFlat : List Bool) : Bool :=
  (List.range (totalLen φ)).all fun i => !flags.getD i false ||
    (naorCommit generator (BitString.listRow m 0 r) (openedBits.getD i false)
      (BitString.listRow s i openSeedsFlat) == BitString.listRow m i commitReply)

/-- Verifier's complete check on the two-round interaction transcript. -/
def verifyTranscript (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (r commitReply ch openReply : List Bool) : Bool :=
  let K := totalLen φ; let openedBits := openReply.take K; let openSeedsFlat := openReply.drop K
  let flags := allOpenFlags φ ch openedBits
  (φ.all fun c => decide (c.length ≤ 3)) &&
  verifyCopyBits φ (ch.getD 0 false) (gmwCopy0 φ openedBits) &&
  verifyCopyBits φ (ch.getD 1 false) (gmwCopy1 φ openedBits) &&
  verifyCopyBits φ (ch.getD 2 false) (gmwCopy2 φ openedBits) &&
  verifyCommitments generator s m φ r flags commitReply openedBits openSeedsFlat

theorem length_proverReply2_any (s : ℕ) (φ : CNF ℕ) (ch bits : List Bool)
    (seeds : List (List Bool)) :
    (proverReply2 s φ ch bits seeds).length = bits.length * (s + 1) := by
  have hmap : List.map List.length (naorSelectSeeds s (allOpenFlags φ ch bits) bits seeds) =
      List.replicate bits.length s := by
    apply List.ext_getElem (by simp); intro i hi _
    simp only [List.getElem_map, List.getElem_replicate]
    exact length_mem_naorSelectSeeds (List.getElem_mem _)
  simp only [proverReply2, List.length_append, length_naorMaskBits,
    List.length_flatten, hmap, List.sum_replicate, smul_eq_mul]; ring

/-! ### Two-round deterministic state handler, honest prover, and honest verifier -/

/-- Deterministic two-round state transition answering the first query with `reply1 q`, the second
query with `reply2 (BitString.listRow 3 0 q)` while recording the 3-bit challenge in the state, and
subsequent queries with `[]`. -/
def twoRoundStep (reply1 reply2 : List Bool → List Bool) (q : List Bool)
    (s : ℕ × List Bool) : List Bool × (ℕ × List Bool) :=
  if s.1 == 0 then (reply1 q, (1, s.2))
  else if s.1 == 1 then (reply2 (BitString.listRow 3 0 q), (2, BitString.listRow 3 0 q))
  else ([], s)

/-- Run a `WordOracleComp Unit` program against `twoRoundStep` inside `ProbComp`. -/
def runTwoRound {α : Type} (reply1 reply2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (s : ℕ × List Bool) : ProbComp (α × (ℕ × List Bool)) :=
  (OracleComp.interpret (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
    (fun q state => pure (twoRoundStep reply1 reply2 q.2 state))) prog).run s

@[simp] theorem runTwoRound_pure {α : Type} (reply1 reply2 : List Bool → List Bool)
    (a : α) (s : ℕ × List Bool) : runTwoRound reply1 reply2 (pure a) s = pure (a, s) := rfl

theorem runTwoRound_bind {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (next : α → WordOracleComp Unit β) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (prog >>= next) s =
      (runTwoRound reply1 reply2 prog s >>= fun x => runTwoRound reply1 reply2 (next x.1) x.2) := by
  simp only [runTwoRound, OracleComp.interpret_bind, StateT.run_bind]

theorem runTwoRound_map {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (f : α → β) (prog : WordOracleComp Unit α) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (f <$> prog) s =
      Prod.map f id <$> runTwoRound reply1 reply2 prog s := by
  simp only [runTwoRound, OracleComp.interpret_map, StateT.run_map]; rfl

@[simp] theorem runTwoRound_sample {α : Type} (reply1 reply2 : List Bool → List Bool)
    (prog : ProbComp α) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (ProbOracleComp.sample prog) s = (·, s) <$> prog := by
  simp only [runTwoRound, ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift,
    ProbComp.unifFin, OracleComp.interpret_query_eq_self]

@[simp] theorem runTwoRound_query (reply1 reply2 : List Bool → List Bool)
    (q : Unit × List Bool) (s : ℕ × List Bool) :
    runTwoRound reply1 reply2 (ProbOracleComp.query q) s =
      pure (twoRoundStep reply1 reply2 q.2 s) := by
  simp only [runTwoRound, ProbOracleComp.interpret_query]; rfl

theorem eval_runTwoRound {α : Type} (reply1 reply2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (s : ℕ × List Bool) :
    ProbComp.eval (runTwoRound reply1 reply2 prog s) =
      ProbOracleComp.runWith
        (fun q state => PMF.pure (twoRoundStep reply1 reply2 q.2 state)) prog s := by
  simpa [runTwoRound, ProbOracleComp.runWith, OracleComp.runWith] using
    ProbOracleComp.eval_run_interpret
      (fun q state => pure (twoRoundStep reply1 reply2 q.2 state)) prog s

/-- Sample the honest prover's random masks and commitment seeds, returning `(bits, seeds)`. -/
noncomputable def sampleHonestCoins (s : ℕ) (φ : CNF ℕ) (w : List Bool) :
    ProbComp (List Bool × List (List Bool)) := do
  let m₀ ← BitString.sampleList φ.vars.length
  let m₁ ← BitString.sampleList φ.vars.length
  let m₂ ← BitString.sampleList φ.vars.length
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  return (realBits φ w m₀ m₁ m₂, seeds)

/-- Honest first-round reply function for pre-sampled `(bits, seeds)`. -/
def honestReply1 (generator : List Bool → List Bool) (m : ℕ) (φ : CNF ℕ)
    (coins : List Bool × List (List Bool)) (r : List Bool) : List Bool :=
  proverReply1 generator m r (List.replicate (totalLen φ) true) coins.1 coins.2 []

/-- Honest second-round reply function for pre-sampled `(bits, seeds)`. -/
def honestReply2 (s : ℕ) (φ : CNF ℕ)
    (coins : List Bool × List (List Bool)) (ch : List Bool) : List Bool :=
  proverReply2 s φ ch coins.1 coins.2

/-- The honest GMW prover for a 3SAT formula `φ` and witness `w`. It samples its masks and
commitment seeds on the first query and answers the two rounds via `honestReply1` and
`honestReply2`. -/
noncomputable def gmwProver (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) : Prover Unit where
  State := (ℕ × List Bool) × Option (List Bool × List (List Bool))
  init := ((0, [false, false, false]), none)
  respond q state := match state.2 with
    | none => (ProbComp.eval (sampleHonestCoins s φ w)).map fun coins =>
        let step := twoRoundStep (honestReply1 generator m φ coins)
          (honestReply2 s φ coins) q.2 state.1
        (step.1, (step.2, some coins))
    | some coins =>
      let step := twoRoundStep (honestReply1 generator m φ coins)
        (honestReply2 s φ coins) q.2 state.1
      PMF.pure (step.1, (step.2, some coins))

theorem run_gmwProver_fst {α : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit α) :
    ((gmwProver generator s m φ w).run prog (gmwProver generator s m φ w).init).map Prod.fst =
      ProbComp.eval (do
        let coins ← sampleHonestCoins s φ w
        Prod.fst <$> runTwoRound (honestReply1 generator m φ coins)
          (honestReply2 s φ coins) prog (0, [false, false, false])) := by
  let P := gmwProver generator s m φ w
  let State' := (ℕ × List Bool) × (List Bool × List (List Bool))
  let relate : P.State → PMF State' := fun state => match state.2 with
    | none => (ProbComp.eval (sampleHonestCoins s φ w)).map (state.1, ·)
    | some coins => PMF.pure (state.1, coins)
  let oracle' : Unit × List Bool → StateT State' PMF (List Bool) := fun q state =>
    let step := twoRoundStep (honestReply1 generator m φ state.2)
      (honestReply2 s φ state.2) q.2 state.1
    PMF.pure (step.1, (step.2, state.2))
  have hsim := ProbOracleComp.run_interpret_simulation P.respond oracle' relate
    (fun q state => by
      rcases state with ⟨st, _ | coins⟩ <;>
        simp [P, gmwProver, relate, oracle', PMF.bind_map, Function.comp_def]) prog P.init
  have hmap := congrArg (PMF.map Prod.fst) hsim
  have hlhs : (((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) P.respond)
        prog).run P.init).bind (fun (a, s') => (relate s').map (a, ·))).map Prod.fst =
      (P.run prog P.init).map Prod.fst := by
    simp only [Prover.run, PMF.map_bind, PMF.map_comp, Function.comp_def]
    have hconst : ∀ x : α × P.State, PMF.map (fun _ : State' => x.1) (relate x.2) = PMF.pure x.1 :=
      fun _ => PMF.map_const _ _
    simp only [hconst]; rfl
  rw [hlhs] at hmap; rw [hmap]
  simp only [P, gmwProver, relate, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.map_bind, PMF.bind_map, Function.comp_def]
  congr 1; funext coins
  have hstate := ProbOracleComp.run_interpret_map_state
    (fun q (st : ℕ × List Bool) => PMF.pure (twoRoundStep (honestReply1 generator m φ coins)
        (honestReply2 s φ coins) q.2 st))
    oracle' (fun st => (st, coins)) (fun q st => by simp [oracle']) prog (0, [false, false, false])
  have hstate_fst := congrArg (PMF.map Prod.fst) hstate
  simp only [PMF.map_comp, Function.comp_def] at hstate_fst
  rw [← hstate_fst, eval_runTwoRound]; rfl

/-- The PPT program realizing the honest GMW prover's interaction with a verifier `prog`. -/
noncomputable def gmwInteract (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let coins ← sampleHonestCoins s φ w
  let p ← runTwoRound (honestReply1 generator m φ coins)
    (honestReply2 s φ coins) prog (0, [false, false, false])
  return p.1

theorem eval_gmwInteract (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (gmwInteract generator s m φ w prog) =
      ((gmwProver generator s m φ w).run prog
        (gmwProver generator s m φ w).init).map Prod.fst := by
  simpa only [gmwInteract, bind_pure_comp] using (run_gmwProver_fst generator s m φ w prog).symm

/-- The two-round GMW verifier for a problem reduced to `ThreeSAT` by `f`, at security parameter
`n` (using Naor commitments with seed length `n + 7`). -/
noncomputable def gmwVerifier {α : Type} (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (f : α → CNF ℕ) (n : ℕ) (a : α) : WordOracleComp Unit Bool := do
  let φ := f a; let s := n + 7; let m := length s; let K := totalLen φ
  let r ← ProbOracleComp.sample (BitString.sampleList m)
  let commitReply ← List.take (K * m) <$> ProbOracleComp.query ((), r)
  let ch ← ProbOracleComp.sample (BitString.sampleList 3)
  let openReply ← List.take (K * (s + 1)) <$> ProbOracleComp.query ((), ch)
  return verifyTranscript generator s m φ r commitReply ch openReply

end Cslib.Crypto.GMW
