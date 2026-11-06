/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeCounters
public import Complexity.Computability.WordRAM.ReadOnly

/-!
# Native balance computation from projected counters

[WangLvShenZhang2027], Theorem 7, PDF p. 22, computes the maximum
smaller-class size before storing a full-width class. This traversal reads the
actual two arrays, including the complemented indexing of the native backward
counter kernel. Comparisons and loop control are charged native instructions.
It neither enumerates classes nor supplies the integrated dissection endpoint.

`scan_classes_exec` gives the compositional execution theorem;
`scan_classes_resources` includes halt, bounded intermediate words and exact
nonzero support at every continuing prefix. `scan_prefix_memory` can also be
used without assumptions on the array contents.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Balance

open Cslib.WordRAM

/-- Compare the two counters and retain their minimum in `value`. -/
@[expose] def smaller : Code .standard 18 :=
  .branch (.lt left right) (ram[ value ← left ]) (ram[ value ← right ])

/-- Update the running maximum, leaving it unchanged on ties. -/
@[expose] def largest : Code .standard 18 :=
  .branch (.lt answer value) (ram[ answer ← value ]) (ram[ answer ← answer ])

/-- Read forward index `g` and backward index `2^p-1-g` without copying either array. -/
@[expose] def body : Code .standard 18 :=
  .seq (ram[ address ← source + index; left ← *address;
    address ← mask - index; address ← destination + address; right ← *address ])
    (.seq smaller (.seq largest (ram[ index ← index + one ])))

/-- Fixed traversal of the two arrays. The result is returned in `answer`. -/
@[expose] def scan : Code .standard 18 :=
  .seq (ram[ index ← #0; one ← #1; answer ← #0; mask ← modulus - one ])
    (.loop (.lt index modulus) body)

/-- Mathematical observer of a traversal prefix, never a machine instruction. -/
def prefixMax (mem : ℕ → ℕ) (b c N k : ℕ) : ℕ :=
  (Finset.range k).sup fun j => min (mem (b + j)) (mem (c + (N - 1 - j)))

private theorem prefixMax_succ (mem : ℕ → ℕ) (b c N k : ℕ) :
    prefixMax mem b c N (k + 1) =
      max (prefixMax mem b c N k) (min (mem (b + k)) (mem (c + (N - 1 - k)))) := by
  simp [prefixMax, Finset.range_add_one, max_comm]

private theorem smaller_exec {W : ℕ} (x : Data 18) :
    ExecWithin W smaller x (x.set value (min (x.regs left) (x.regs right))) 3 := by
  by_cases h : x.regs left < x.regs right
  · have he := ExecWithin.branch_pos (cond := .lt left right) (pos := ram[ value ← left ])
      (neg := ram[ value ← right ]) (by simpa only [Cond.holds_lt] using h)
      (ExecWithin.copy (B := .standard) (w := W) (d := value) (s := left) (x := x))
    simpa only [smaller, min_eq_left h.le] using he.mono (by omega)
  · have he := ExecWithin.branch_neg (cond := .lt left right) (pos := ram[ value ← left ])
      (neg := ram[ value ← right ]) (by simpa only [Cond.holds_lt] using h)
      (ExecWithin.copy (B := .standard) (w := W) (d := value) (s := right) (x := x))
    simpa only [smaller, min_eq_right (by omega : x.regs right ≤ x.regs left)] using he

private theorem largest_exec {W : ℕ} (x : Data 18) :
    ExecWithin W largest x (x.set answer (max (x.regs answer) (x.regs value))) 3 := by
  by_cases h : x.regs answer < x.regs value
  · have he := ExecWithin.branch_pos (cond := .lt answer value) (pos := ram[ answer ← value ])
      (neg := ram[ answer ← answer ]) (by simpa only [Cond.holds_lt] using h)
      (ExecWithin.copy (B := .standard) (w := W) (d := answer) (s := value) (x := x))
    simpa only [largest, max_eq_right h.le] using he.mono (by omega)
  · have he := ExecWithin.branch_neg (cond := .lt answer value) (pos := ram[ answer ← value ])
      (neg := ram[ answer ← answer ]) (by simpa only [Cond.holds_lt] using h)
      (ExecWithin.copy (B := .standard) (w := W) (d := answer) (s := answer) (x := x))
    simpa only [largest, max_eq_left (by omega : x.regs value ≤ x.regs answer)] using he

/-- All array reads, comparisons, initialization and loop tests are charged.
No memory is modified. Either buffer may overlap other read-only input; counter
values can be arbitrary naturals for this execution statement. Word-bounded
input data additionally give word-bounded intermediate configurations by the
standard native preservation theorem. -/
theorem scan_exec {W b c N : ℕ} (x : Data 18)
    (hb : x.regs source = b) (hc : x.regs destination = c)
    (hN : x.regs modulus = N) (hfit : Fits W (b + c + N + 2)) :
    ∃ y, ExecWithin W scan x y (14 * N + 6) ∧
      y.regs answer = prefixMax x.mem b c N N ∧ y.mem = x.mem ∧
      y.regs source = b ∧ y.regs destination = c ∧ y.regs modulus = N := by
  have h0 : Fits W 0 := fits_zero _
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hm : Fits W (N - 1) := hfit.of_le (by omega)
  let start := x.set index 0 |>.set one 1 |>.set answer 0 |>.set mask (N - 1)
  have hs : ExecWithin (B := .standard) W
      (ram[ index ← #0; one ← #1; answer ← #0; mask ← modulus - one ]) x start 4 := by
    ram_eval [start, hN, h0, h1, hm, index, one, answer, mask, modulus, Fin.mk.injEq]
  let I (y : Data 18) : Prop :=
    y.regs source = b ∧ y.regs destination = c ∧ y.regs modulus = N ∧
    y.regs one = 1 ∧ y.regs mask = N - 1 ∧ y.regs index ≤ N ∧
    y.regs answer = prefixMax x.mem b c N (y.regs index) ∧ y.mem = x.mem
  have hi : I start := by
    simp [I, start, prefixMax, hb, hc, hN, source, destination, modulus, one, mask, index, answer]
  have step (y : Data 18) (hy : I y) (ht : (Cond.lt index modulus).Holds y) :
      ∃ z, ExecWithin W body y z 12 ∧ I z ∧ N - z.regs index < N - y.regs index := by
    obtain ⟨yb, yc, yn, yo, ym, yi, ya, ymem⟩ := hy
    have hj : y.regs index < N := by simpa only [Cond.holds_lt, yn] using ht
    let j := y.regs index
    let l := x.mem (b + j)
    let r := x.mem (c + (N - 1 - j))
    have ha : Fits W (b + j) := hfit.of_le (by dsimp [j]; omega)
    have hr : Fits W (N - 1 - j) := hfit.of_le (by omega)
    have hac : Fits W (c + (N - 1 - j)) := hfit.of_le (by omega)
    have hnext : Fits W (j + 1) := hfit.of_le (by dsimp [j]; omega)
    let loaded := y.set address (b + j) |>.set left l |>.set address (N - 1 - j)
      |>.set address (c + (N - 1 - j)) |>.set right r
    have heLoad : ExecWithin (B := .standard) W
        (ram[ address ← source + index; left ← *address;
          address ← mask - index; address ← destination + address; right ← *address ])
        y loaded 5 := by
      ram_eval [loaded, l, r, j, yb, yc, ym, ymem, ha, hr, hac,
        source, destination, index, address, left, right, mask, Fin.mk.injEq]
    let small := loaded.set value (min l r)
    have heSmall : ExecWithin W smaller loaded small 3 := by
      simpa +decide [small, loaded, left, right, address] using smaller_exec (W := W) loaded
    let large := small.set answer (max (y.regs answer) (min l r))
    have heLarge : ExecWithin W largest small large 3 := by
      simpa +decide [large, small, loaded, value, answer, left, right, address]
        using largest_exec (W := W) small
    let z := large.set index (j + 1)
    have heNext : ExecWithin (B := .standard) W (ram[ index ← index + one ]) large z 1 := by
      ram_eval [z, large, small, loaded, j, yo, hnext,
        index, one, answer, value, address, left, right, Fin.mk.injEq]
    refine ⟨z, heLoad.seq (heSmall.seq (heLarge.seq heNext)), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide only [z, large, small, loaded, Data.set_regs,
        Data.set_mem, Function.update_apply, index, answer, value, address, left, right,
        source, destination, modulus, one, mask, ↓reduceIte]
      · exact yb
      · exact yc
      · exact yn
      · exact yo
      · exact ym
      · dsimp [j]; omega
      · rw [ya, prefixMax_succ]
      · exact ymem
    · simp only [z, Data.set_regs, Function.update_self, j]; omega
  obtain ⟨y, he, hy, ht⟩ := ExecWithin.loop_invariant I
    (fun y => N - y.regs index) step hi
  have hj : y.regs index = N := by
    have := hy.2.2.2.2.2.1
    simp only [Cond.holds_lt, hy.2.2.1] at ht
    omega
  refine ⟨y, ?_, ?_, hy.2.2.2.2.2.2.2, hy.1, hy.2.1, hy.2.2.1⟩
  · apply (hs.seq he).mono
    have hz : start.regs index = 0 := by simp [start, index, one, answer, mask]
    rw [hz]; omega
  · simpa only [hj] using hy.2.2.2.2.2.2.1

/-- The array traversal computes exactly the manuscript's maximum of minima.
The backward array is the complement-conjugated output of the existing kernel;
there is no assumed balance parameter in this statement. -/
theorem prefixMax_eq_classBalance {m p l r b c : ℕ}
    (as : Fin l → BitVec m) (bs : Fin r → BitVec m) (s t : BitVec m)
    (mem : ℕ → ℕ)
    (hf : ∀ g : BitVec p, mem (b + g.toNat) = forwardClassCount p as s g)
    (hb : ∀ g : BitVec p, mem (c + (~~~g).toNat) = backwardClassCount p bs t g) :
    prefixMax mem b c (2 ^ p) (2 ^ p) = classBalance p as bs s t := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have hj' : j < 2 ^ p := Finset.mem_range.mp hj
    let g : BitVec p := BitVec.ofNatLT j hj'
    have hg : g.toNat = j := rfl
    have h := min_classCount_le_balance p as bs s t g
    rw [← hf, ← hb, BitVec.toNat_not, hg] at h
    exact h
  · apply Finset.sup_le
    intro g _
    rw [← hf, ← hb, BitVec.toNat_not]
    exact Finset.le_sup (f := fun j => min (mem (b + j)) (mem (c + (2 ^ p - 1 - j))))
      (Finset.mem_range.mpr g.isLt)

/-- Native computed balance, from the actual counter cells, with every comparison
charged. It also returns a bound on each class the dissection may retain. This
statement is conditional on the two counter arrays; it does not silently include
their construction, quarter enumeration or a dictionary. -/
theorem scan_classes_exec {W m p l r b c : ℕ}
    (as : Fin l → BitVec m) (bs : Fin r → BitVec m) (s t : BitVec m)
    (x : Data 18) (hsource : x.regs source = b) (hdest : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ p)
    (hf : ∀ g : BitVec p, x.mem (b + g.toNat) = forwardClassCount p as s g)
    (hb : ∀ g : BitVec p, x.mem (c + (~~~g).toNat) = backwardClassCount p bs t g)
    (hfit : Fits W (b + c + 2 ^ p + 2)) :
    ∃ y, ExecWithin W scan x y (14 * 2 ^ p + 6) ∧
      y.regs answer = classBalance p as bs s t ∧ y.mem = x.mem ∧
      ∀ g : BitVec p, min (forwardClassCount p as s g) (backwardClassCount p bs t g) ≤
        y.regs answer := by
  obtain ⟨y, he, hy, hm, _⟩ := scan_exec x hsource hdest hn hfit
  rw [prefixMax_eq_classBalance as bs s t x.mem hf hb] at hy
  exact ⟨y, he, hy, hm, fun g => hy ▸ min_classCount_le_balance p as bs s t g⟩

/-- The compiled traversal contains no stores. In particular it allocates no
array of class sizes or branch decisions while computing the maximum. -/
theorem scan_no_store (a v : Fin 18) : Instr.op (Op.store a v) ∉ scan.program answer := by
  simp [Code.program, Code.assemble, scan, body, smaller, largest, Op.bin]

/-- Every native execution prefix preserves the entire memory, including unread
input. Thus the scan needs eighteen registers and no extra occupied memory cells;
its memory bound is independent of its runtime and the address capacity. -/
theorem scan_prefix_memory {W k : ℕ} (x : Data 18) (u : State 18)
    (h : Runs W (scan.program answer) ⟨0, x⟩ u k) : u.data.mem = x.mem :=
  h.mem_eq_of_no_store scan_no_store

/-- Halting native balance computation and simultaneous occupied memory at every
prefix. `S` covers actual initial nonzero cells, including untouched input. The
scan returns the exact balance and adds no occupied cells; eighteen registers
are charged at the physical word width. Counter construction is still a
separate call, not an uncharged part of this theorem. -/
theorem scan_classes_resources {W m p l r b c : ℕ}
    (as : Fin l → BitVec m) (bs : Fin r → BitVec m) (s t : BitVec m)
    (x : Data 18) (hx : x.Bounded W) (S : Finset ℕ)
    (hS : ∀ a, x.mem a ≠ 0 → a ∈ S)
    (hsource : x.regs source = b) (hdest : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ p)
    (hf : ∀ g : BitVec p, x.mem (b + g.toNat) = forwardClassCount p as s g)
    (hb : ∀ g : BitVec p, x.mem (c + (~~~g).toNat) = backwardClassCount p bs t g)
    (hfit : Fits W (b + c + 2 ^ p + 2)) :
    ∃ y n ts, n + 1 ≤ 14 * 2 ^ p + 7 ∧
      TraceExec W scan x y n ts ∧
      Executes W (scan.program answer) ⟨0, x⟩ (classBalance p as bs s t) (n + 1) ∧
      y.regs answer = classBalance p as bs s t ∧
      ∀ k u, Runs W (scan.program answer) ⟨0, x⟩ u k →
        u.data.Bounded W ∧ ∃ live : Finset ℕ,
          (∀ a, u.data.mem a ≠ 0 ↔ a ∈ live) ∧
          (live.card + 18) * W ≤ (S.card + 18) * W := by
  obtain ⟨y, ⟨n, hnTime, he⟩, hy, _, _⟩ :=
    scan_classes_exec as bs s t x hsource hdest hn hf hb hfit
  obtain ⟨ts, ht⟩ := he.exists_trace
  refine ⟨y, n, ts, by omega, ht, ?_, hy, ?_⟩
  · simpa only [hy] using he.executes answer
  · intro k u hu
    refine ⟨hu.bounded hx, S.filter (fun a => u.data.mem a ≠ 0), ?_, ?_⟩
    · intro a
      simp only [Finset.mem_filter]
      constructor
      · intro ha
        have hmem := ha
        rw [scan_prefix_memory x u hu] at hmem
        exact ⟨hS a hmem, ha⟩
      · exact And.right
    · exact Nat.mul_le_mul_right W
        (Nat.add_le_add_right (Finset.card_filter_le _ _) 18)

end Cslib.Cryptanalysis.AddXNOR.Native.Balance
