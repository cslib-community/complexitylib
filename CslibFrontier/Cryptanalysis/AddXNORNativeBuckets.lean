/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration
public import CslibFrontier.Computability.WordRAM.Allocation

/-!
# Native quarter bucket construction

[WangLvShenZhang2027], Lemma 8, PDF pp. 21–22. Low-bit keys use a
zero-initialized direct-address head array. Each indexed first-quarter word adds
three cells: previous bucket pointer, full state and packed operator index.
The state is computed by the native evaluator, not supplied as a table.
Zero is the null pointer, so the record region must start at a positive address.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Initial state, preserved across indexed evaluations. -/
abbrev initial : Fin 32 := 13
/-- Number of low-bit keys. -/
abbrev keyModulus : Fin 32 := 14
/-- Base of the low-bit head array. -/
abbrev heads : Fin 32 := 15
/-- Next available record cell; advanced by three on each insertion. -/
abbrev frontier : Fin 32 := 16
/-- Previous bucket head. -/
abbrev previous : Fin 32 := 17
/-- Current low-bit key. -/
abbrev key : Fin 32 := 18
/-- Exclusive upper bound of the indexed iterator. -/
abbrev stop : Fin 32 := 19
/-- Exclusive upper address of the head-initialization loop. -/
abbrev headEnd : Fin 32 := 20

/-- Exact insertion observer; it is not an instruction or allocation oracle. -/
def insertMemory (mem : ℕ → ℕ) (h f N s v : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update (Function.update (Function.update mem (h + s % N) f) f (mem (h + s % N)))
      (f + 1) s) (f + 2) v

/-- Preserve every indexed collision with a linked three-cell record. -/
@[expose] def insert : Code .standard 32 := ram[
  key ← state % keyModulus; address ← heads + key; previous ← *address;
  *address ← frontier; address ← frontier; *address ← previous;
  address ← address + one; *address ← state;
  address ← address + one; *address ← operators;
  frontier ← address + one; operators ← operators + one ]

/-- One complete native insertion, including list pointers, full key, witness
index and both iterator increments. Existing head contents are read, not guessed. -/
theorem insert_exec {W h f N s v : ℕ} (x : Data 32)
    (hh : x.regs heads = h) (hf : x.regs frontier = f)
    (hN : x.regs keyModulus = N) (hs : x.regs state = s)
    (hv : x.regs operators = v) (ho : x.regs one = 1) (hNpos : 0 < N)
    (hfit : Fits W (h + N + f + v + 4)) :
    ∃ y, ExecWithin W insert x y 12 ∧
      y.mem = insertMemory x.mem h f N s v ∧
      y.regs frontier = f + 3 ∧ y.regs operators = v + 1 := by
  have hk : s % N < N := Nat.mod_lt _ hNpos
  have hkey : Fits W (s % N) := hfit.of_le (by omega)
  have haddr : Fits W (h + s % N) := hfit.of_le (by omega)
  have hf1 : Fits W (f + 1) := hfit.of_le (by omega)
  have hf2 : Fits W (f + 2) := hfit.of_le (by omega)
  have hf3 : Fits W (f + 3) := hfit.of_le (by omega)
  have hv1 : Fits W (v + 1) := hfit.of_le (by omega)
  let y := x.set key (s % N) |>.set address (h + s % N) |>.set previous (x.mem (h + s % N))
    |>.write (h + s % N) f |>.set address f |>.write f (x.mem (h + s % N))
    |>.set address (f + 1) |>.write (f + 1) s
    |>.set address (f + 2) |>.write (f + 2) v
    |>.set frontier (f + 3) |>.set operators (v + 1)
  refine ⟨y, ?_, rfl, ?_, ?_⟩
  · ram_eval [insert, y, hh, hf, hN, hs, hv, ho, hkey, haddr, hf1, hf2, hf3, hv1,
      heads, frontier, keyModulus, state, operators, one, address, previous, key,
      Nat.add_assoc, Fin.mk.injEq]
  · simp +decide [y, frontier, operators]
  · simp [y]

/-- Insertion does not change any cell outside the actual head and record writes. -/
theorem insertMemory_outside (mem : ℕ → ℕ) (h f N s v z : ℕ)
    (hh : z ≠ h + s % N) (hf : z ≠ f) (hf1 : z ≠ f + 1) (hf2 : z ≠ f + 2) :
    insertMemory mem h f N s v z = mem z := by
  simp [insertMemory, hh, hf, hf1, hf2]

/-- The actual full state attached to an indexed quarter word. -/
def indexedState {m : ℕ} (as : List (BitVec m)) (s : BitVec m) (v : ℕ) : BitVec m :=
  eval ((decode as.length v).zip as) s

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
  .seq (ram[ state ← initial ]) (.seq evaluate insert)

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
    (hinput : ∀ i (hi : i < as.length), mem (b + i) = as[i].toNat)
    (hsep : ∀ i < as.length, ¬(h ≤ b + i ∧ b + i < h + N) ∧
      ¬(f ≤ b + i ∧ b + i < f + 3 * L))
    (hfit : Fits W (b + as.length + 2 * 2 ^ m + h + N + f + 4 * L + 8)) :
    ∃ y, ExecWithin W prepareLoop x y ((L - j) * (11 * as.length + 22) + 2) ∧
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
      ∃ z, ExecWithin W prepareBody y z (11 * as.length + 20) ∧ I z ∧
        L - z.regs operators < L - y.regs operators := by
    obtain ⟨yb, yc, yn, ys, yh, yN, yl, yj, yf, ym⟩ := hy
    have hlt : y.regs operators < L := by simpa only [Cond.holds_lt, yl] using ht
    let loaded := y.set state s.toNat
    have heLoad : ExecWithin (B := .standard) W (ram[ state ← initial ]) y loaded 1 := by
      simpa only [loaded, ys] using
        (ExecWithin.copy (B := .standard) (w := W) (d := state) (s := initial) (x := y))
    have hreads : ∀ i (hi : i < as.length), loaded.mem (b + i) = as[i].toNat := by
      intro i hi
      change y.mem (b + i) = _
      rw [ym, preparedMemory_outside as s mem h f N _ _ hNpos (hsep i hi).1]
      · exact hinput i hi
      · have := (hsep i hi).2
        omega
    obtain ⟨z, heEval, zstate, _, _, zmem, zone, _⟩ := evaluate_exec as s loaded
      (v := y.regs operators)
      (by simpa +decide [loaded, base, state] using yb)
      (by simpa +decide [loaded, count, state] using yc)
      (by simpa +decide [loaded, modulus, state] using yn)
      (by simp [loaded]) (by simp +decide [loaded, operators, state])
      (hfit.of_le (by omega)) hreads (hfit.of_le (by omega))
    have frame (r : Fin 32) (hr : evaluate.Preserves r) (hr' : r ≠ state) :
        z.regs r = y.regs r := by
      rw [heEval.regs_eq hr]
      simp [loaded, hr']
    obtain ⟨u, heInsert, umem, uf, uv⟩ := insert_exec (h := h) (f := f + 3 * y.regs operators) z
      (by rw [frame heads (by decide) (by decide)]; exact yh)
      (by rw [frame frontier (by decide) (by decide)]; exact yf)
      (by rw [frame keyModulus (by decide) (by decide)]; exact yN)
      zstate
      (by rw [frame operators (by decide) (by decide)]) zone hNpos
      (hfit.of_le (by omega))
    have e := heLoad.seq (heEval.seq heInsert)
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
      · rw [uv]; omega
      · rw [uf, uv]; omega
      · rw [umem, uv, preparedMemory, zmem]
        change insertMemory y.mem h (f + 3 * y.regs operators) N
          (indexedState as s (y.regs operators)).toNat (y.regs operators) = _
        rw [ym]
    · rw [uv]; omega
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
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hsep : ∀ i < as.length, ¬(h ≤ b + i ∧ b + i < h + 2 ^ p) ∧
      ¬(f ≤ b + i ∧ b + i < f + 3 * 2 ^ as.length))
    (hfit : Fits W (b + as.length + 2 * 2 ^ m + h + 2 ^ p + f + 4 * 2 ^ as.length + 8)) :
    ∃ y, ExecWithin W prepare x y
        (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10) ∧
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
    (by intro i hi; rw [clear_of_not_owns (hsep i hi).1]; exact hinput i hi) hsep hfit
  exact ⟨y, (heSetup.seq (heClear.seq (heBound.seq he))).mono
    (by simp only [Nat.sub_zero]; omega), hm, hv, hf'⟩

/-- The three-word records retain full states as well as operator indices. The
head table contains pointers, not counts or distinct-state representatives. -/
theorem insertMemory_record (mem : ℕ → ℕ) (h f N s v : ℕ) :
    insertMemory mem h f N s v f = mem (h + s % N) ∧
    insertMemory mem h f N s v (f + 1) = s ∧
    insertMemory mem h f N s v (f + 2) = v := by
  simp [insertMemory]

/-- Head points at the new record when the head and record regions are disjoint. -/
theorem insertMemory_head (mem : ℕ → ℕ) (h f N s v : ℕ) (hN : 0 < N)
    (hsep : h + N ≤ f) : insertMemory mem h f N s v (h + s % N) = f := by
  have := Nat.mod_lt s hN
  simp [insertMemory, show h + s % N ≠ f by omega,
    show h + s % N ≠ f + 1 by omega, show h + s % N ≠ f + 2 by omega]

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

/-- A concrete null-terminated list of full-state/index records, with every node
below a fixed read-only boundary. This relation inspects actual pointer cells. -/
inductive Linked (mem : ℕ → ℕ) (boundary : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  /-- Zero terminates a list. -/
  | nil : Linked mem boundary 0 []
  /-- A three-word node keeps its next pointer, full state and indexed witness. -/
  | cons {ptr s v : ℕ} {rs : List (ℕ × ℕ)} :
      0 < ptr → ptr + 2 < boundary → mem (ptr + 1) = s → mem (ptr + 2) = v →
      Linked mem boundary (mem ptr) rs → Linked mem boundary ptr ((s, v) :: rs)

/-- Stores above the read-only boundary preserve every linked bucket node. -/
theorem Linked.frame {mem mem' : ℕ → ℕ} {boundary ptr : ℕ} {rs : List (ℕ × ℕ)}
    (h : Linked mem boundary ptr rs) (hm : ∀ a < boundary, mem' a = mem a) :
    Linked mem' boundary ptr rs := by
  induction h with
  | nil => exact .nil
  | @cons ptr s v rs hp hb hs hv tail ih =>
    refine .cons hp hb ?_ ?_ ?_
    · rw [hm _ (by omega)]; exact hs
    · rw [hm _ hb]; exact hv
    · rw [hm _ (by omega)]; exact ih

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

/-- A sufficient physical width for the actual quarter layout and packed
iterator. Unlike a state-width assumption, this also fits the index `2^a`. -/
@[expose] def preparationWidth (m p a b h f : ℕ) : ℕ :=
  (b + a + 2 * 2 ^ m + h + 2 ^ p + f + 4 * 2 ^ a + 8).log2 + 1

/-- Layout and arithmetic fit are derived, rather than compiler/runtime premises. -/
theorem preparationWidth_fits (m p a b h f : ℕ) :
    Fits (preparationWidth m p a b h f)
      (b + a + 2 * 2 ^ m + h + 2 ^ p + f + 4 * 2 ^ a + 8) := Nat.lt_log2_self

/-- Address capacity of the selected width. This is distinct from occupancy;
the resource theorem below counts actual initial support and executed stores. -/
theorem preparationWidth_capacity (m p a b h f : ℕ) :
    2 ^ preparationWidth m p a b h f ≤
      2 * (b + a + 2 * 2 ^ m + h + 2 ^ p + f + 4 * 2 ^ a + 8) := by
  have hpositive : 0 < 2 ^ p := Nat.two_pow_pos p
  have hp := Nat.log2_self_le
    (n := b + a + 2 * 2 ^ m + h + 2 ^ p + f + 4 * 2 ^ a + 8) (by omega)
  simp only [preparationWidth, pow_succ]
  omega

/-- Complete preparation through halt, including simultaneous support of every
continuing prefix. The conservative space bound uses the proved preparation
time, which is already `O*(2^a + 2^p)`; it includes dirty initial support and all
32 registers. It is not a space bound for repeated class collection or dissection. -/
theorem prepare_resources {m b h f p : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (x : Data 32) (S : Finset ℕ)
    (hx : x.Bounded (preparationWidth m p as.length b h f))
    (hS : ∀ a, x.mem a ≠ 0 → a ∈ S)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hs : x.regs initial = s.toNat)
    (hh : x.regs heads = h) (hf : x.regs frontier = f) (hp : x.regs keyModulus = 2 ^ p)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hsep : ∀ i < as.length, ¬(h ≤ b + i ∧ b + i < h + 2 ^ p) ∧
      ¬(f ≤ b + i ∧ b + i < f + 3 * 2 ^ as.length)) :
    let W := preparationWidth m p as.length b h f
    let T := 4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10
    ∃ y n ts, n + 1 ≤ T + 1 ∧ TraceExec W prepare x y n ts ∧
      Executes W (prepare.program frontier) ⟨0, x⟩ (f + 3 * 2 ^ as.length) (n + 1) ∧
      y.mem = preparedMemory as s (clear x.mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length) ∧
      ∀ k u, Runs W (prepare.program frontier) ⟨0, x⟩ u k → k ≤ n →
        u.data.Bounded W ∧ ∃ live : Finset ℕ,
          (∀ a, u.data.mem a ≠ 0 ↔ a ∈ live) ∧
          (live.card + 32) * W ≤ (S.card + T + 32) * W := by
  dsimp only
  obtain ⟨y, ⟨n, hnTime, he⟩, hm, _, hf'⟩ := prepare_exec as s x hb hc hn hs hh hf hp
    hinput hsep (preparationWidth_fits m p as.length b h f)
  obtain ⟨ts, ht⟩ := he.exists_trace
  refine ⟨y, n, ts, by omega, ht, ?_, hm, ?_⟩
  · simpa only [hf'] using he.executes frontier
  · intro k u hu hk
    obtain ⟨cover, hcard, hcover⟩ := hu.exists_memorySupport S hS
    refine ⟨hu.bounded hx, cover.filter (fun a => u.data.mem a ≠ 0), ?_, ?_⟩
    · intro a
      simp only [Finset.mem_filter]
      exact ⟨fun ha => ⟨hcover a ha, ha⟩, And.right⟩
    · apply Nat.mul_le_mul_right
      have := Finset.card_filter_le cover (fun a => u.data.mem a ≠ 0)
      omega

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
