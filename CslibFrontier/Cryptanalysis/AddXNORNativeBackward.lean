/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeQuery

/-!
# Native backward quarter preparation

The backward half of [WangLvShenZhang2027], Lemma 8, PDF pp. 21–22.
Enumerate fourth-quarter indices in original order and store the full inverse
state from the target, keyed by its remainder modulo the key modulus. The operand
array at `base` is reversed; `backwardEvaluate` performs charged operator reversal
and complement conjugacy. Every record stores next pointer, inverse state and
original packed index. This component does not establish the global dissection
pipeline, termination of class search, or its bit-time and space bounds.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter.Backward

open Cslib.WordRAM

/-- The actual full state attached to an indexed quarter word. -/
def indexedState {m : ℕ} (as : List (BitVec m)) (s : BitVec m) (v : ℕ) : BitVec m :=
  backward ((decode as.length v).zip as) s

/-- Actual preparation memory after `k` indexed records. The recursion observes
native stores; it does not provide the evaluator with precomputed states. -/
def preparedMemory {m : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (mem : ℕ → ℕ) (h f N : ℕ) : ℕ → ℕ → ℕ
  | 0 => mem
  | k + 1 => insertMemory (preparedMemory as s mem h f N k)
      h (f + 3 * k) N (indexedState as s k).toNat k

/-- Preparation writes only the head table and its finite record prefix.
This frame includes the full original input when the regions are disjoint. -/
theorem preparedMemory_outside {m : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (mem : ℕ → ℕ) (h f N k z : ℕ) (hN : 0 < N)
    (hh : ¬(h ≤ z ∧ z < h + N)) (hf : ¬(f ≤ z ∧ z < f + 3 * k)) :
    preparedMemory as s mem h f N k z = mem z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [preparedMemory, insertMemory_outside]
    · apply ih
      omega
    · have := Nat.mod_lt (indexedState as s k).toNat hN
      omega
    · omega
    · omega
    · omega

/-- Evaluate one indexed word and append its native record. -/
@[expose] def prepareBody : Code .standard 32 :=
  .seq (ram[ state ← initial ]) (.seq backwardEvaluate (.seq (ram[ one ← #1 ]) insert))

/-- The numeric iterator does not construct a host list of operator words. -/
@[expose] def prepareLoop : Code .standard 32 := .loop (.lt operators stop) prepareBody

/-- Execution of all remaining indexed quarter words. Dirty record memory is
allowed. The original operand region must lie outside the two writable regions.
The input operator index `j` is explicit so this theorem composes with other loops. -/
theorem prepareLoop_exec {W m b h f N j L : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (x : Data 32) (mem : ℕ → ℕ)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hs : x.regs initial = s.toNat)
    (hh : x.regs heads = h) (hf : x.regs frontier = f + 3 * j)
    (hN : x.regs keyModulus = N) (hNpos : 0 < N)
    (hv : x.regs operators = j) (hl : x.regs stop = L) (hj : j ≤ L)
    (hm : x.mem = preparedMemory as s mem h f N j)
    (hinput : ∀ i (hi : i < as.length), mem (b + i) =
      (as.reverse[i]'(by simpa only [List.length_reverse] using hi)).toNat)
    (hsep : ∀ i < as.length, ¬(h ≤ b + i ∧ b + i < h + N) ∧
      ¬(f ≤ b + i ∧ b + i < f + 3 * L))
    (hfit : Fits W (b + as.length + 2 * 2 ^ m + h + N + f + 4 * L + 2 ^ as.length + 8)) :
    ∃ y, ExecWithin W prepareLoop x y ((L - j) * (18 * as.length + 37) + 2) ∧
      y.mem = preparedMemory as s mem h f N L ∧
      y.regs operators = L ∧ y.regs frontier = f + 3 * L := by
  let I (y : Data 32) : Prop :=
    y.regs base = b ∧ y.regs count = as.length ∧ y.regs modulus = 2 ^ m ∧
    y.regs initial = s.toNat ∧ y.regs heads = h ∧ y.regs keyModulus = N ∧
    y.regs stop = L ∧ y.regs operators ≤ L ∧
    y.regs frontier = f + 3 * y.regs operators ∧
    y.mem = preparedMemory as s mem h f N (y.regs operators)
  have hi : I x := by simp only [I, hb, hc, hn, hs, hh, hN, hl, hv, hj, hf, hm, and_self]
  have step (y : Data 32) (hy : I y) (ht : (Cond.lt operators stop).Holds y) :
      ∃ z, ExecWithin W prepareBody y z (18 * as.length + 35) ∧ I z ∧
        L - z.regs operators < L - y.regs operators := by
    obtain ⟨yb, yc, yn, ys, yh, yN, yl, yj, yf, ym⟩ := hy
    simp only [operators] at *
    have hlt : y.regs operators < L := by simpa only [Cond.holds_lt, yl] using ht
    let loaded := y.set state s.toNat
    have heLoad : ExecWithin (B := .standard) W (ram[ state ← initial ]) y loaded 1 := by
      simpa only [loaded, ys] using
        (ExecWithin.copy (B := .standard) (w := W) (d := state) (s := initial) (x := y))
    have hreads : ∀ i (hi : i < as.length), loaded.mem (b + i) =
      (as.reverse[i]'(by simpa only [List.length_reverse] using hi)).toNat := by
      intro i hi
      change y.mem (b + i) = _
      rw [ym, preparedMemory_outside as s mem h f N _ _ hNpos (hsep i hi).1]
      · exact hinput i hi
      · have := (hsep i hi).2
        omega
    obtain ⟨z, heEval, zstate, zops, zmem⟩ := backwardEvaluate_exec (b := b) as s loaded
      (v := y.regs operators)
      (by simpa +decide [loaded, base, state] using yb)
      (by simpa +decide [loaded, count, state] using yc)
      (by simpa +decide [loaded, modulus, state] using yn)
      (by simp [loaded]) (by simp +decide [loaded, operators, state])
      (hfit.of_le (by
        clear * - hlt
        have hpow := Nat.two_pow_pos as.length
        dsimp only [operators] at *
        omega))
      (by simpa only [List.length_reverse] using hreads)
      (hfit.of_le (by
        clear * - hlt
        have hpow := Nat.two_pow_pos as.length
        omega))
    have frame (r : Fin 32) (hr : backwardEvaluate.Preserves r) (hr' : r ≠ state) :
        z.regs r = y.regs r := by
      rw [heEval.regs_eq hr]
      simp [loaded, hr']
    let z' := z.set one 1
    have heOne : ExecWithin (B := .standard) W (ram[ one ← #1 ]) z z' 1 := by
      have h1 : Fits W 1 := hfit.of_le (by
        clear * - hlt
        have hpow := Nat.two_pow_pos as.length
        dsimp only [operators] at *
        omega)
      simpa only [z'] using (ExecWithin.const (B := .standard) (x := z) (d := one) h1)
    obtain ⟨u, heInsert, umem, uf, uv⟩ := insert_exec (h := h) (f := f + 3 * y.regs operators) z'
      (by simpa +decide [z', heads, one] using (frame heads (by decide) (by decide)).trans yh)
      (by simpa +decide [z', frontier, one] using (frame frontier (by decide) (by decide)).trans yf)
      (by simpa +decide [z', keyModulus, one] using
        (frame keyModulus (by decide) (by decide)).trans yN)
      (by simpa +decide [z', state, one] using zstate)
      (by simpa +decide [z', operators, one] using zops) (by simp [z']) hNpos
      (hfit.of_le (by
        clear * - hlt
        have hpow := Nat.two_pow_pos as.length
        dsimp only [operators] at *
        omega))
    have e := heLoad.seq (heEval.seq (heOne.seq heInsert))
    have allframe (r : Fin 32) (hr : prepareBody.Preserves r) : u.regs r = y.regs r :=
      e.regs_eq hr
    refine ⟨u, e.mono (by omega), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [allframe base (by decide)]; exact yb
      · rw [allframe count (by decide)]; exact yc
      · rw [allframe modulus (by decide)]; exact yn
      · rw [allframe initial (by decide)]; exact ys
      · rw [allframe heads (by decide)]; exact yh
      · rw [allframe keyModulus (by decide)]; exact yN
      · rw [allframe stop (by decide)]; exact yl
      · rw [uv]; dsimp only [operators] at *; omega
      · rw [uf, uv]; dsimp only [operators] at *; omega
      · rw [umem, uv, preparedMemory]
        simp only [z', Data.set_mem, zmem, loaded, Data.set_mem]
        change insertMemory y.mem h (f + 3 * y.regs operators) N
          (indexedState as s (y.regs operators)).toNat (y.regs operators) = _
        rw [ym]
    · rw [uv]; dsimp only [operators] at *; omega
  obtain ⟨y, he, hy, ht⟩ := ExecWithin.loop_invariant I
    (fun y => L - y.regs operators) step hi
  have hyL : y.regs operators = L := by
    have := hy.2.2.2.2.2.2.2.1
    simp only [Cond.holds_lt, hy.2.2.2.2.2.2.1] at ht
    omega
  exact ⟨y, by simpa only [prepareLoop, hv] using he,
    by simpa only [hyL] using hy.2.2.2.2.2.2.2.2.2, hyL,
    by simpa only [hyL] using hy.2.2.2.2.2.2.2.2.1⟩

/-- Initialize every low-key head by actual stores, compute the numeric iterator
bound by a charged shift, then evaluate and insert every indexed quarter word. -/
@[expose] def prepare : Code .standard 32 :=
  .seq (ram[ one ← #1; headEnd ← heads + keyModulus; address ← heads; bit ← #0 ])
    (.seq (zeroFill address headEnd bit one)
      (.seq (ram[ stop ← one <<< count; operators ← #0 ]) prepareLoop))

/-- Complete quarter construction, including head allocation/initialization,
iterator-bound computation, all evaluations and all list/admin stores. It
requires only the original operands and layout registers, not a host enumeration.
The bound uses physical words; a multitape bit-time simulation is separate. -/
theorem prepare_exec {W m b h f p : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hs : x.regs initial = s.toNat)
    (hh : x.regs heads = h) (hf : x.regs frontier = f)
    (hp : x.regs keyModulus = 2 ^ p)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) =
      (as.reverse[i]'(by simpa only [List.length_reverse] using hi)).toNat)
    (hsep : ∀ i < as.length, ¬(h ≤ b + i ∧ b + i < h + 2 ^ p) ∧
      ¬(f ≤ b + i ∧ b + i < f + 3 * 2 ^ as.length))
    (hfit : Fits W (b + as.length + 2 * 2 ^ m + h + 2 ^ p + f + 5 * 2 ^ as.length + 8)) :
    ∃ y, ExecWithin W prepare x y
        (4 * 2 ^ p + 2 ^ as.length * (18 * as.length + 37) + 10) ∧
      y.mem = preparedMemory as s (clear x.mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length) ∧
      y.regs operators = 2 ^ as.length ∧ y.regs frontier = f + 3 * 2 ^ as.length := by
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hend : Fits W (h + 2 ^ p) := hfit.of_le (by omega)
  have hL : Fits W (2 ^ as.length) := hfit.of_le (by omega)
  let z := x.set one 1 |>.set headEnd (h + 2 ^ p) |>.set address h |>.set bit 0
  have heSetup : ExecWithin (B := .standard) W
      (ram[ one ← #1; headEnd ← heads + keyModulus; address ← heads; bit ← #0 ]) x z 4 := by
    ram_eval [z, hh, hp, h1, hend, one, headEnd, heads, keyModulus, address, bit, Fin.mk.injEq]
  let u : Data 32 := ⟨Function.update z.regs address (h + 2 ^ p), clear x.mem h (2 ^ p)⟩
  have heClear : ExecWithin W (zeroFill address headEnd bit one) z u (4 * 2 ^ p + 2) := by
    have he := zeroFill_exec (w := W) (x := z)
      (cur := address) (stop := headEnd) (zero := bit) (one := one)
      (by decide) (by decide) (by decide)
      (by simp [z]) (by simp +decide [z, one, headEnd, address, bit])
      (by simp +decide [z, headEnd, address, bit])
      (by simpa +decide [z, headEnd, address, bit] using hend)
    simpa +decide only [u, z, Data.set_regs, Data.set_mem, headEnd, address, bit, one,
      Function.update_apply, ↓reduceIte, Nat.add_sub_cancel_left] using he.within
  let v := (u.set stop (2 ^ as.length)).set operators 0
  have heBound : ExecWithin (B := .standard) W
      (ram[ stop ← one <<< count; operators ← #0 ]) u v 2 := by
    ram_eval [v, u, z, hc, hL, Nat.shiftLeft_eq, one_mul, stop, one, count, operators,
      headEnd, address, bit, Fin.mk.injEq]
  have frame (r : Fin 32) (hr : r ≠ one ∧ r ≠ headEnd ∧ r ≠ address ∧ r ≠ bit ∧
      r ≠ stop ∧ r ≠ operators) : v.regs r = x.regs r := by
    simp [v, u, z, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
  obtain ⟨y, he, hm, hv, hf'⟩ := prepareLoop_exec as s v (clear x.mem h (2 ^ p))
    (j := 0) (L := 2 ^ as.length)
    (by rw [frame base (by decide)]; exact hb)
    (by rw [frame count (by decide)]; exact hc)
    (by rw [frame modulus (by decide)]; exact hn)
    (by rw [frame initial (by decide)]; exact hs)
    (by rw [frame heads (by decide)]; exact hh)
    (by rw [frame frontier (by decide)]; simpa only [Nat.mul_zero, Nat.add_zero] using hf)
    (by rw [frame keyModulus (by decide)]; exact hp) (Nat.two_pow_pos p)
    (by simp +decide [v, operators, stop]) (by simp +decide [v, stop, operators])
    (Nat.zero_le _) rfl
    (by intro i hi; rw [clear_of_not_owns (hsep i hi).1]; exact hinput i hi) hsep
    (hfit.of_le (by omega))
  exact ⟨y, (heSetup.seq (heClear.seq (heBound.seq he))).mono
    (by simp only [Nat.sub_zero]; omega), hm, hv, hf'⟩

/-- Earlier record cells are unchanged by later insertions. The region disjointness
condition is required because head writes are genuine writes, not a functional map. -/
theorem preparedMemory_record {m : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (mem : ℕ → ℕ) (h f N k v : ℕ) (hN : 0 < N) (hsep : h + N ≤ f) (hv : v < k) :
    preparedMemory as s mem h f N k (f + 3 * v) =
        preparedMemory as s mem h f N v (h + (indexedState as s v).toNat % N) ∧
    preparedMemory as s mem h f N k (f + 3 * v + 1) = (indexedState as s v).toNat ∧
    preparedMemory as s mem h f N k (f + 3 * v + 2) = v := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hvk : v = k
    · subst v
      exact insertMemory_record _ _ _ _ _ _
    · have hv' : v < k := by omega
      have hmod := Nat.mod_lt (indexedState as s k).toNat hN
      have frame (d : ℕ) (hd : d ≤ 2) :
          preparedMemory as s mem h f N (k + 1) (f + 3 * v + d) =
            preparedMemory as s mem h f N k (f + 3 * v + d) := by
        apply insertMemory_outside <;> omega
      have h0 := frame 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0, frame 1 (by omega), frame 2 (by omega)]
      exact ih hv'

/-- The mathematical bucket order induced by the actual linked insertions. -/
def bucketIndices {m : ℕ} (as : List (BitVec m)) (s : BitVec m) (N g : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => if (indexedState as s k).toNat % N = g
      then k :: bucketIndices as s N g k else bucketIndices as s N g k

/-- Head pointer represented by a list of indexed records. -/
def bucketPointer (f : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: _ => f + 3 * v

/-- Every head is the pointer to its most recently inserted matching witness.
Initialization is an explicit premise supplied by the native zero-fill theorem. -/
theorem preparedMemory_head {m : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (mem : ℕ → ℕ) (h f N k g : ℕ) (hg : g < N) (hsep : h + N ≤ f)
    (hzero : mem (h + g) = 0) :
    preparedMemory as s mem h f N k (h + g) =
      bucketPointer f (bucketIndices as s N g k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    have hN : 0 < N := by omega
    have hmod := Nat.mod_lt (indexedState as s k).toNat hN
    by_cases he : (indexedState as s k).toNat % N = g
    · rw [preparedMemory, ← he, insertMemory_head _ _ _ _ _ _ hN (by omega)]
      simp [bucketIndices, he, bucketPointer]
    · rw [preparedMemory, insertMemory_outside]
      · simpa only [bucketIndices, ite_eq_right_iff.mpr (fun h => (he h).elim)] using ih
      · omega
      · omega
      · omega
      · omega

/-- Exact predicate filtering of indexed quarter words, with no distinct-state
hypothesis. This is a specification of the native bucket order, not its producer. -/
theorem bucketIndices_eq {m : ℕ} (as : List (BitVec m)) (s : BitVec m) (N g k : ℕ) :
    bucketIndices as s N g k =
      ((List.range k).filter fun v => (indexedState as s v).toNat % N == g).reverse := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bucketIndices, List.range_succ, List.filter_append, List.filter_cons,
      List.filter_nil, List.reverse_append, ← ih]
    split <;> simp_all

/-- The native head and record stores really form the filtered linked list.
Every duplicate state keeps its own index. No linked-list premise is assumed of
arbitrary caller memory: it is derived from the construction and zeroed heads. -/
theorem preparedMemory_linked {m : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (mem : ℕ → ℕ) (h f N L g : ℕ) (hg : g < N) (_hf : 0 < f) (hsep : h + N ≤ f)
    (hzero : mem (h + g) = 0) :
    Linked (preparedMemory as s mem h f N L) (f + 3 * L)
      (preparedMemory as s mem h f N L (h + g))
      ((bucketIndices as s N g L).map fun v => ((indexedState as s v).toNat, v)) := by
  rw [preparedMemory_head as s mem h f N L g hg hsep hzero]
  have all (k : ℕ) (hk : k ≤ L) :
      Linked (preparedMemory as s mem h f N L) (f + 3 * L)
        (bucketPointer f (bucketIndices as s N g k))
        ((bucketIndices as s N g k).map fun v => ((indexedState as s v).toNat, v)) := by
    induction k with
    | zero => exact .nil
    | succ k ih =>
      have hN : 0 < N := by omega
      by_cases he : (indexedState as s k).toNat % N = g
      · simp only [bucketIndices, he, ↓reduceIte, List.map_cons, bucketPointer]
        obtain ⟨hn, hs, hv⟩ := preparedMemory_record as s mem h f N L k hN hsep (by omega)
        refine .cons (by omega) (by omega) hs hv ?_
        rw [hn, he, preparedMemory_head as s mem h f N k g hg hsep hzero]
        exact ih (by omega)
      · simpa only [bucketIndices, he, ↓reduceIte] using ih (by omega)
  exact all L le_rfl

/-- Construction-derived semantic bucket records. The target is arbitrary and the
packed indices refer to the original (unreversed) operand order. No semantic
bucket or dictionary is supplied by the caller. -/
theorem prepare_linked_exec {W m b h f p : ℕ} (as : List (BitVec m)) (t : BitVec m)
    (x : Data 32) (g : Fin (2 ^ p))
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (ht : x.regs initial = t.toNat)
    (hh : x.regs heads = h) (hf : x.regs frontier = f)
    (hp : x.regs keyModulus = 2 ^ p) (hfpos : 0 < f) (hheads : h + 2 ^ p ≤ f)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hsep : ∀ i < as.length, ¬(h ≤ b + i ∧ b + i < h + 2 ^ p) ∧
      ¬(f ≤ b + i ∧ b + i < f + 3 * 2 ^ as.length))
    (hfit : Fits W (b + as.length + 2 * 2 ^ m + h + 2 ^ p + f + 5 * 2 ^ as.length + 8)) :
    ∃ y, ExecWithin W prepare x y
        (4 * 2 ^ p + 2 ^ as.length * (18 * as.length + 37) + 10) ∧
      Linked y.mem (f + 3 * 2 ^ as.length) (y.mem (h + g.val))
        ((bucketIndices as t (2 ^ p) g.val (2 ^ as.length)).map
          fun v => ((backward ((decode as.length v).zip as) t).toNat, v)) ∧
      (∀ a, ¬(h ≤ a ∧ a < h + 2 ^ p) →
        ¬(f ≤ a ∧ a < f + 3 * 2 ^ as.length) → y.mem a = x.mem a) := by
  obtain ⟨y, he, hm, _, _⟩ := prepare_exec as t x hb hc hn ht hh hf hp
    (by simpa only [List.length_reverse] using hinput) hsep hfit
  refine ⟨y, he, ?_, ?_⟩
  · rw [hm]
    exact preparedMemory_linked as t (clear x.mem h (2 ^ p)) h f (2 ^ p)
      (2 ^ as.length) g.val g.isLt hfpos hheads
      (clear_of_owns (by
        change h ≤ h + g.val ∧ h + g.val < h + 2 ^ p
        exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left g.isLt _⟩))
  · intro a ha hf'
    rw [hm, preparedMemory_outside as t _ _ _ _ _ _ (Nat.two_pow_pos p) ha hf',
      clear_of_not_owns ha]

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter.Backward
