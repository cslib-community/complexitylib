/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORClassEnumeration
public import Complexity.Computability.WordRAM.Compile
public import Complexity.Computability.WordRAM.ReadOnly
public import Complexity.Computability.WordRAM.TraceBounds

/-!
# Native packed-operator quarter evaluation

The evaluation kernel for [WangLvShenZhang2027], Lemma 8, PDF pp. 21–22,
reads actual operands and consumes an indexed operator word one bit at a time.
Bit zero selects addition and bit one selects XNOR, matching `step`. The least
significant operator bit acts first. No host evaluation is a RAM instruction.
The physical word must fit the packed index as well as the state and addresses.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Address of the first operand. -/
abbrev base : Fin 32 := 0
/-- Number of operands. -/
abbrev count : Fin 32 := 1
/-- State modulus. -/
abbrev modulus : Fin 32 := 2
/-- Packed operator word, preserved by evaluation. -/
abbrev operators : Fin 32 := 3
/-- Current full state and evaluation result. -/
abbrev state : Fin 32 := 4
/-- Unconsumed operator bits. -/
abbrev bits : Fin 32 := 5
/-- Next operand offset. -/
abbrev position : Fin 32 := 6
/-- Address scratch. -/
abbrev address : Fin 32 := 7
/-- Current operand. -/
abbrev operand : Fin 32 := 8
/-- Current operator bit. -/
abbrev bit : Fin 32 := 9
/-- Constant one. -/
abbrev one : Fin 32 := 10
/-- Constant two. -/
abbrev two : Fin 32 := 11
/-- State mask. -/
abbrev mask : Fin 32 := 12

/-- Decode exactly `n` packed bits, retaining leading zero operators. -/
@[expose] def decode : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, v => decide (v % 2 = 1) :: decode n (v / 2)

/-- Packed decoding always supplies one operator per operand. -/
@[simp] theorem decode_length (n v : ℕ) : (decode n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [decode, ih]

/-- One actual modular operation, selected by the decoded bit. -/
@[expose] def operation : Code .standard 32 :=
  .branch (.eq bit one)
    (ram[ state ← state ^^^ operand; state ← state ^^^ mask ])
    (ram[ state ← state + operand; state ← state % modulus ])

/-- Load one operand, execute its operation, and advance both iterators. -/
@[expose] def body : Code .standard 32 :=
  .seq (ram[ address ← base + position; operand ← *address; bit ← bits % two ])
    (.seq operation (ram[ bits ← bits / two; position ← position + one ]))

/-- Fixed native evaluator; the initial state is supplied in `state`. -/
@[expose] def evaluate : Code .standard 32 :=
  .seq (ram[ bits ← operators; position ← #0; one ← #1; two ← #2;
    mask ← modulus - one ]) (.loop (.lt position count) body)

private theorem operation_exec {W m : ℕ} (x : Data 32) (s a : BitVec m) (b : Bool)
    (hs : x.regs state = s.toNat) (ha : x.regs operand = a.toNat)
    (hb : x.regs bit = b.toNat) (ho : x.regs one = 1)
    (hn : x.regs modulus = 2 ^ m) (hm : x.regs mask = 2 ^ m - 1)
    (hfit : Fits W (2 * 2 ^ m)) :
    ExecWithin W operation x
      (if b then (x.set state (s.toNat ^^^ a.toNat)).set state (step b s a).toNat
       else (x.set state (s.toNat + a.toNat)).set state (step b s a).toNat) 4 := by
  have hsum : Fits W (s.toNat + a.toNat) := hfit.of_le (by have := s.isLt; have := a.isLt; omega)
  have hxor : Fits W (s.toNat ^^^ a.toNat) :=
    hfit.of_le (by have := Nat.xor_lt_two_pow s.isLt a.isLt; omega)
  have hr : Fits W (step b s a).toNat := hfit.of_le (by have := (step b s a).isLt; omega)
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply (ExecWithin.branch_neg (cond := .eq bit one)
      (pos := ram[ state ← state ^^^ operand; state ← state ^^^ mask ])
      (by simp [Cond.holds_eq, hb, ho]) ?_)
    have hmod : Fits W ((s.toNat + a.toNat) % 2 ^ m) := by
      simpa [step, BitVec.toNat_add] using hr
    ram_eval [hs, ha, hn, hsum, hmod, step, BitVec.toNat_add, state, operand, modulus,
      Fin.mk.injEq]
  | true =>
    simp only [↓reduceIte]
    apply (ExecWithin.branch_pos (cond := .eq bit one)
      (neg := ram[ state ← state + operand; state ← state % modulus ])
      (by simp [Cond.holds_eq, hb, ho]) (T := 2) ?_).mono (by omega)
    have he : (s.toNat ^^^ a.toNat) ^^^ (2 ^ m - 1) = (step true s a).toNat := by
      have h := congrArg BitVec.toNat
        (show (s ^^^ a) ^^^ BitVec.allOnes m = ~~~(s ^^^ a) from BitVec.xor_allOnes)
      simpa only [step, ↓reduceIte, BitVec.toNat_xor, BitVec.toNat_allOnes] using h
    ram_eval [hs, ha, hm, hxor, hr, he, state, operand, mask, Fin.mk.injEq]

/-- The loop evaluates the actual operand suffix. All reads and bit/admin
operations are charged. Other registers and all memory are preserved by framing.
No bound on the number of distinct states or operands is assumed. -/
theorem loop_exec {W m b j v : ℕ} (as : List (BitVec m)) (s : BitVec m) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = j + as.length)
    (hn : x.regs modulus = 2 ^ m) (hs : x.regs state = s.toNat)
    (hv : x.regs bits = v) (hfv : Fits W v) (hj : x.regs position = j)
    (ho : x.regs one = 1) (ht : x.regs two = 2) (hm : x.regs mask = 2 ^ m - 1)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + j + i) = as[i].toNat)
    (hfit : Fits W (b + j + as.length + 2 * 2 ^ m + 2)) :
    ∃ y, ExecWithin W (.loop (.lt position count) body) x y (11 * as.length + 2) ∧
      y.regs state = (eval ((decode as.length v).zip as) s).toNat ∧
      y.regs bits = v / 2 ^ as.length ∧ y.regs position = j + as.length ∧
      y.mem = x.mem := by
  induction as generalizing s x j v with
  | nil =>
    refine ⟨x, ?_, ?_, ?_, ?_, rfl⟩
    · exact ExecWithin.loop_exit (by simp [Cond.holds_lt, hj, hc])
    · simpa [decode, eval] using hs
    · simpa using hv
    · simpa using hj
  | cons a as ih =>
    have hread : x.mem (b + j) = a.toNat := by
      have h := hinput 0 (by simp)
      change x.mem (b + j + 0) = a.toNat at h
      simpa only [Nat.add_zero] using h
    have haddr : Fits W (b + j) := hfit.of_le (by omega)
    have hbit : Fits W (v % 2) := hfit.of_le (by have := Nat.mod_lt v (by decide : 0 < 2); omega)
    have hdiv : Fits W (v / 2) := hfv.of_le (Nat.div_le_self v 2)
    let loaded := x.set address (b + j) |>.set operand a.toNat |>.set bit (v % 2)
    have heLoad : ExecWithin (B := .standard) W
        (ram[ address ← base + position; operand ← *address; bit ← bits % two ]) x loaded 3 := by
      ram_eval [loaded, hb, hj, hv, ht, hread, haddr, hbit,
        base, position, address, operand, bits, two, bit, Fin.mk.injEq]
    let chosen := decide (v % 2 = 1)
    have hchosen : v % 2 = chosen.toNat := by
      have := Nat.mod_lt v (by decide : 0 < 2)
      by_cases he : v % 2 = 1
      · simp [chosen, he]
      · have hz : v % 2 = 0 := by omega
        simp [chosen, hz]
    let applied := if chosen then
      (loaded.set state (s.toNat ^^^ a.toNat)).set state (step chosen s a).toNat
      else (loaded.set state (s.toNat + a.toNat)).set state (step chosen s a).toNat
    have heOp : ExecWithin W operation loaded applied 4 := by
      apply operation_exec loaded s a chosen
      · simpa +decide [loaded, state, address, operand, bit] using hs
      · simp +decide [loaded, operand, bit]
      · simpa [loaded] using hchosen
      · simpa +decide [loaded, one, address, operand, bit] using ho
      · simpa +decide [loaded, modulus, address, operand, bit] using hn
      · simpa +decide [loaded, mask, address, operand, bit] using hm
      · exact hfit.of_le (by omega)
    have happ : applied.regs state = (step chosen s a).toNat := by
      simp only [applied]; split <;> simp
    have haBits : applied.regs bits = v := by
      rw [heOp.regs_eq (by decide)]
      simpa +decide [loaded, bits, address, operand, bit] using hv
    have haPos : applied.regs position = j := by
      rw [heOp.regs_eq (by decide)]
      simpa +decide [loaded, position, address, operand, bit] using hj
    have haOne : applied.regs one = 1 := by
      rw [heOp.regs_eq (by decide)]
      simpa +decide [loaded, one, address, operand, bit] using ho
    have haTwo : applied.regs two = 2 := by
      rw [heOp.regs_eq (by decide)]
      simpa +decide [loaded, two, address, operand, bit] using ht
    have hnext : Fits W (j + 1) := hfit.of_le (by simp only [List.length_cons]; omega)
    let next := (applied.set bits (v / 2)).set position (j + 1)
    have heNext : ExecWithin (B := .standard) W
        (ram[ bits ← bits / two; position ← position + one ]) applied next 2 := by
      ram_eval [next, haBits, haPos, haOne, haTwo, hdiv, hnext,
        bits, two, position, one, Fin.mk.injEq]
    have frame (r : Fin 32) (hr : body.Preserves r) : next.regs r = x.regs r := by
      exact (heLoad.seq (heOp.seq heNext)).regs_eq (by
        exact hr)
    have nmem : next.mem = x.mem := by
      dsimp [next, applied, loaded]
      split <;> rfl
    obtain ⟨y, heTail, hy, hyBits, hyPos, hym⟩ := ih (step chosen s a) next
      (j := j + 1) (v := v / 2)
      (by rw [frame base (by decide)]; exact hb)
      (by rw [frame count (by decide)];
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc)
      (by rw [frame modulus (by decide)]; exact hn)
      (by simpa +decide [next, state, bits, position] using happ)
      (by simp +decide [next, bits, position]) hdiv (by simp [next])
      (by rw [frame one (by decide)]; exact ho)
      (by rw [frame two (by decide)]; exact ht)
      (by rw [frame mask (by decide)]; exact hm)
      (by
        intro i hi
        rw [nmem]
        have h := hinput (i + 1) (by simp only [List.length_cons]; omega)
        change x.mem (b + j + (i + 1)) = as[i].toNat at h
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      (hfit.of_le (by simp only [List.length_cons]; omega))
    refine ⟨y, ?_, ?_, ?_, ?_, hym.trans nmem⟩
    · exact (ExecWithin.loop_iter (by simp [Cond.holds_lt, hj, hc])
        (heLoad.seq (heOp.seq heNext)) heTail).mono (by simp only [List.length_cons]; omega)
    · simpa only [List.length_cons, decode, List.zip_cons_cons, eval, chosen] using hy
    · simpa only [List.length_cons, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using hyBits
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.length_cons] using hyPos

/-- Full evaluation, including five setup instructions. Memory is unchanged and
all non-scratch registers remain available to the enclosing quarter iterator. -/
theorem evaluate_exec {W m b v : ℕ} (as : List (BitVec m)) (s : BitVec m) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hs : x.regs state = s.toNat)
    (hv : x.regs operators = v) (hfv : Fits W v)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hfit : Fits W (b + as.length + 2 * 2 ^ m + 2)) :
    ∃ y, ExecWithin W evaluate x y (11 * as.length + 7) ∧
      y.regs state = (eval ((decode as.length v).zip as) s).toNat ∧
      y.regs bits = v / 2 ^ as.length ∧ y.regs position = as.length ∧
      y.mem = x.mem ∧ y.regs one = 1 ∧ y.regs mask = 2 ^ m - 1 := by
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h2 : Fits W 2 := hfit.of_le (by omega)
  have hm : Fits W (2 ^ m - 1) := hfit.of_le (by omega)
  let z := x.set bits v |>.set position 0 |>.set one 1 |>.set two 2 |>.set mask (2 ^ m - 1)
  have he : ExecWithin (B := .standard) W
      (ram[ bits ← operators; position ← #0; one ← #1; two ← #2; mask ← modulus - one ])
      x z 5 := by
    ram_eval [z, hv, hn, h1, h2, hm, bits, operators, position, one, two, mask, modulus,
      Fin.mk.injEq]
  obtain ⟨y, hy, hstate, hbits, hpos, hmem⟩ := loop_exec as s z
    (j := 0) (v := v)
    (by simpa +decide [z, base, bits, position, one, two, mask] using hb)
    (by simpa +decide [z, count, bits, position, one, two, mask] using hc)
    (by simpa +decide [z, modulus, bits, position, one, two, mask] using hn)
    (by simpa +decide [z, state, bits, position, one, two, mask] using hs)
    (by simp +decide [z, bits, position, one, two, mask]) hfv
    (by simp +decide [z, position, one, two, mask])
    (by simp +decide [z, one, two, mask]) (by simp +decide [z, two, mask]) (by simp [z])
    (by simpa only [z, Data.set_mem, Nat.add_zero] using hinput)
    (by simpa only [Nat.add_zero] using hfit)
  refine ⟨y, (he.seq hy).mono (by omega), hstate, hbits,
    by simpa only [Nat.zero_add] using hpos, hmem, ?_, ?_⟩
  · rw [hy.regs_eq (by decide)]
    simp +decide [z, one, two, mask]
  · rw [hy.regs_eq (by decide)]
    simp [z]

/-- Packing keeps the exact indexed word; leading additions are not discarded. -/
@[expose] def encode : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * encode bs

/-- Every list of operators has a representable index of the advertised length. -/
theorem encode_lt (bs : List Bool) : encode bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp only [encode, Bool.toNat_false, Bool.toNat_true,
      List.length_cons, pow_succ] <;> omega

/-- Native bit decoding recovers every indexed operator witness. -/
theorem decode_encode (bs : List Bool) : decode bs.length (encode bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [decode, encode, Nat.add_mul_div_left, ih]

/-- Decoding does not merge distinct indexed quarter words. -/
theorem encode_decode {n v : ℕ} (hv : v < 2 ^ n) : encode (decode n v) = v := by
  induction n generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    subst v
    rfl
  | succ n ih =>
    have hdiv : v / 2 < 2 ^ n := (Nat.div_lt_iff_lt_mul (by decide)).2 (by
      simpa only [pow_succ] using hv)
    have hrem : v % 2 = (decide (v % 2 = 1)).toNat := by
      have := Nat.mod_lt v (by decide : 0 < 2)
      by_cases he : v % 2 = 1
      · simp [he]
      · have hz : v % 2 = 0 := by omega
        simp [hz]
    rw [decode, encode, ih hdiv, ← hrem]
    omega

/-- All indexed operator words occur exactly once in the numeric iterator.
Repeated evaluated states remain distinct because their indices remain distinct. -/
theorem decode_injective (n : ℕ) : Function.Injective
    (fun v : Fin (2 ^ n) => decode n v.val) := by
  intro a b h
  apply Fin.ext
  simpa only [encode_decode a.isLt, encode_decode b.isLt] using congrArg encode h

/-- The evaluator has no store instruction, so every continuing prefix preserves
all memory, including unread initial data and dirty cells. -/
theorem evaluate_no_store (a v : Fin 32) :
    Instr.op (Op.store a v) ∉ evaluate.program state := by
  simp [Code.program, Code.assemble, evaluate, body, operation, Op.bin]

/-- Prefix occupancy is unchanged; no transcript-length bound is used as space. -/
theorem evaluate_prefix_memory {W k : ℕ} (x : Data 32) (u : State 32)
    (h : Runs W (evaluate.program state) ⟨0, x⟩ u k) : u.data.mem = x.mem :=
  h.mem_eq_of_no_store evaluate_no_store

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
