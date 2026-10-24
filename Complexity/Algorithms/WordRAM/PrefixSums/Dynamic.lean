/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PrefixSums.Query
public import Complexity.Computability.WordRAM.Dynamic

/-!
# Stateful prefix sums implemented by one fixed Word-RAM program

The abstract state is a list, independently of the tree representation. An operation either
increments one entry or returns the sum of an initial segment. A complete balanced tree stores
`n = 2 ^ h` entries in `2 n - 1` words. One fixed fourteen-register program dispatches both
operations, with every executed instruction charged, including its final halt.

The representation is supplied at entry. Installing the three operation-argument registers is
the external calling convention and is uncharged. Tree construction is a separate obligation;
these theorems do not charge or claim a construction algorithm. Natural-number sums and
increments must fit the chosen word width. This is a segment tree, not a Fenwick tree.

## Main definitions

* `Operation`, `spec`: array operations and mathematical answers, with word-fit admissibility
  conditions.
* `setup`, `setupData`, `dispatch`, `program`: the register-setup fragment, fixed dispatcher, and
  register-only calling convention.
* `Rep`, `zeroData`, `certificate`: the bounded-tree representation relation, initial zero state,
  and semantic realization on the bounded-word machine.

## Main results

* `dispatch_spec`: per-operation correctness and instruction estimate.
* `instruction_bound`: a separate cost certificate, at `13 (h + 1) + 12` instructions per call.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PrefixSums

open Cslib.WordRAM Reg

/-- Array operations. Updates use a zero-based position; queries use a prefix length. -/
inductive Operation where
  /-- Add a nonnegative increment to one array entry. -/
  | add (position increment : ℕ)
  /-- Return the sum of the given number of initial entries. -/
  | sum (length : ℕ)
  deriving DecidableEq, Repr

/-- Abstract list specification. The admissibility of an update includes the word bound on
its new total; a query does not modify the array. -/
def spec (h w : ℕ) : Stateful.Spec where
  State := List ℕ
  Op := Operation
  Result := fun _ => ℕ
  step s
    | .add i δ => (increment s i δ, 0)
    | .sum i => (s, (s.take i).sum)
  valid s
    | .add i δ => i < 2 ^ h ∧ Fits w (s.sum + δ)
    | .sum i => i ≤ 2 ^ h

/-- Initialize constants and traversal registers, charging all seven instructions. -/
def setup : Code .standard 14 := ram[
  zero ← #0; one ← #1; two ← #2;
  ptr ← root; len ← capacity; idx ← position; ans ← #0 ]

/-- One dispatcher for both operations, independent of size and word width. -/
def dispatch : Code .standard 14 := ram[
  ⟪setup⟫; if tag = zero then [⟪updateLoop⟫] else [⟪queryLoop⟫] ]

/-- Fixed code and external argument registers. Decoding reads only the answer register. -/
def program (h w : ℕ) : DynamicProgram (spec h w) 14 where
  code := dispatch
  output := ans
  input j := j == tag || j == delta || j == position
  encode o j := match o with
    | .add i δ => if j = tag then 0 else if j = delta then δ else i
    | .sum i => if j = tag then 1 else if j = delta then 0 else i
  decode _ regs := some (regs ans)

/-- Mathematical description of charged register setup. -/
def setupData (x : Data 14) : Data 14 :=
  let y := (((x.set zero 0).set one 1).set two 2).set ptr (x.regs root)
  ((y.set len (x.regs capacity)).set idx (x.regs position)).set ans 0

variable {h w b : ℕ} {x : Data 14}

private theorem setup_exec (hw : Fits w 2) : Exec w setup x (setupData x) 7 := by
  have h1 := hw.of_le (by decide : 1 ≤ 2)
  ram_eval [setup, setupData, hw, h1]

private theorem setup_entry : Entry (x.regs root) (x.regs capacity) (x.regs position)
    (x.regs delta) (setupData x) := by
  constructor <;> simp +decide [setupData]

/-- A list is represented by a bounded tree, with persistent root and capacity registers. -/
structure Rep (h b w : ℕ) (s : List ℕ) (x : Data 14) : Prop where
  bounded : x.Bounded w
  root_eq : x.regs root = b
  capacity_eq : x.regs capacity = 2 ^ h
  tree : ∃ t : Tree h, t.leaves = s ∧ t.Rep b x.mem

/-- The abstract array length is determined by the persistent tree representation. -/
theorem Rep.length {s : List ℕ} (hx : Rep h b w s x) : s.length = 2 ^ h := by
  obtain ⟨t, rfl, _⟩ := hx.tree
  exact t.length_leaves

/-- Every encoded argument of a valid operation fits in a `w`-bit word. -/
theorem arguments_fit (ha : Fits w (b + 2 * 2 ^ h)) {s : List ℕ} (o : Operation)
    (ho : (spec h w).valid s o) (j : Fin 14) : Fits w ((program h w).encode o j) := by
  have hp := Nat.two_pow_pos h
  have h1 : Fits w 1 := ha.of_le (by omega)
  cases o with
  | add i δ =>
    obtain ⟨hi, hv⟩ := ho
    have hi' : Fits w i := ha.of_le (by omega)
    have hd : Fits w δ := hv.of_le (by omega)
    simp only [program]
    split
    · exact fits_zero w
    · split <;> assumption
  | sum i =>
    have hi' : Fits w i := ha.of_le (by exact le_trans ho (by omega))
    simp only [program]
    split
    · exact h1
    · split
      · exact fits_zero w
      · exact hi'

/-- Every operation uses the same dispatcher, restores the list representation and returns
the specified result within `13 (h + 1) + 11` structured instructions. All memory outside the
`2 * 2 ^ h - 1` words of the tree is preserved. -/
theorem dispatch_spec (ha : Fits w (b + 2 * 2 ^ h)) {s : List ℕ} (o : Operation)
    (hx : Rep h b w s x) (ho : (spec h w).valid s o) :
    ∃ y, ExecWithin w dispatch ((program h w).prepare o x) y (13 * (h + 1) + 11) ∧
      y.regs ans = ((spec h w).step s o).2 ∧ Rep h b w ((spec h w).step s o).1 y ∧
      (∀ a, a < b ∨ b + Tree.words h ≤ a → y.mem a = x.mem a) := by
  have hp := Nat.two_pow_pos h
  have h2 : Fits w 2 := ha.of_le (by omega)
  obtain ⟨t, ht, hrep⟩ := hx.tree
  have hbounded := (program h w).prepare_bounded hx.bounded
    (fun j _ => arguments_fit ha o ho j)
  let z := setupData ((program h w).prepare o x)
  have he := setup_exec (x := (program h w).prepare o x) h2
  have hz := setup_entry (x := (program h w).prepare o x)
  have hroot (y : Data 14) {T : ℕ}
      (he' : ExecWithin w dispatch ((program h w).prepare o x) y T) : y.regs root = b := by
    rw [he'.regs_eq (by decide)]
    simpa +decide [program, DynamicProgram.prepare] using hx.root_eq
  have hcapacity (y : Data 14) {T : ℕ}
      (he' : ExecWithin w dispatch ((program h w).prepare o x) y T) :
      y.regs capacity = 2 ^ h := by
    rw [he'.regs_eq (by decide)]
    simpa +decide [program, DynamicProgram.prepare] using hx.capacity_eq
  cases o with
  | add i δ =>
    obtain ⟨hi, hv⟩ := ho
    have hz' : Entry b (2 ^ h) i δ z := by
      simpa +decide [z, program, DynamicProgram.prepare, hx.root_eq, hx.capacity_eq] using hz
    obtain ⟨y, hy, hyr, hyframe⟩ := updateLoop_spec t hz' hi
      (by simpa [z, setupData, DynamicProgram.prepare] using hrep) ha
      (by simpa [← ht] using hv)
    have hrun : ExecWithin w dispatch ((program h w).prepare (.add i δ) x) y
        (13 * (h + 1) + 11) := by
      exact (he.within.seq (hy.branch_pos
        (by simp +decide [Cond.Holds, setupData, program, DynamicProgram.prepare]))).mono
        (by omega)
    refine ⟨y, hrun, ?_, ⟨hrun.bounded hbounded, hroot y hrun, hcapacity y hrun,
      t.add i δ, ?_, hyr⟩, ?_⟩
    · rw [hy.regs_eq (by decide)]
      simp +decide [z, setupData, spec]
    · simpa [spec, ht] using Tree.leaves_add t i δ hi
    · simpa [z, setupData, DynamicProgram.prepare] using hyframe
  | sum i =>
    have hz' : Entry b (2 ^ h) i 0 z := by
      simpa +decide [z, program, DynamicProgram.prepare, hx.root_eq, hx.capacity_eq] using hz
    obtain ⟨y, hy, hya, hym⟩ := queryLoop_spec (a := 0) t hz' ho
      (by simp +decide [z, setupData])
      (by simpa [z, setupData, DynamicProgram.prepare] using hrep) ha
      (by simpa [hrep.root] using hx.bounded.2 b)
    have hrun : ExecWithin w dispatch ((program h w).prepare (.sum i) x) y
        (13 * (h + 1) + 11) := by
      exact (he.within.seq (hy.branch_neg
        (by simp +decide [Cond.Holds, setupData, program, DynamicProgram.prepare]))).mono
        (by omega)
    refine ⟨y, hrun, ?_, ⟨hrun.bounded hbounded, hroot y hrun, hcapacity y hrun, t, ht, ?_⟩, ?_⟩
    · simpa [spec, t.prefixSum_eq_sum_take, ht] using hya
    · simpa [hym, z, setupData, DynamicProgram.prepare] using hrep
    · intro a _
      simp [hym, z, setupData, DynamicProgram.prepare]

/-- Semantic correctness and totality of the fixed bounded-word implementation. -/
def certificate (ha : Fits w (b + 2 * 2 ^ h)) : DynamicCertificate (program h w) w where
  rep := Rep h b w
  bounded := Rep.bounded
  arguments_fit o ho j _ := arguments_fit ha o ho j
  execute o hx ho := by
    obtain ⟨y, ⟨n, _, he⟩, hans, hy, _⟩ := dispatch_spec ha o hx ho
    exact ⟨y, n, he, congrArg some hans, hy⟩

/-- Separate worst-case instruction certificate, counting the final halt. -/
theorem instruction_bound (ha : Fits w (b + 2 * 2 ^ h)) :
    Stateful.Bound (certificate ha).realization DynamicProgram.OperationTrace.instructions
      (fun _ _ => 13 * (h + 1) + 12) := by
  apply (certificate ha).instruction_bound_const
  intro s x o hx ho
  obtain ⟨z, ⟨k, hk, he'⟩, _, _⟩ := dispatch_spec ha o hx ho
  exact ⟨z, k, he', by omega⟩

/-- The same instruction certificate stated in terms of the abstract array length. -/
theorem instruction_bound_log (ha : Fits w (b + 2 * 2 ^ h)) :
    Stateful.Bound (certificate ha).realization DynamicProgram.OperationTrace.instructions
      (fun s _ => 13 * (Nat.log 2 s.length + 1) + 12) := by
  intro s x o a y trace hx ho he
  have hb := instruction_bound ha hx ho he
  simpa [Rep.length hx, Nat.log_pow Nat.one_lt_two] using hb

/-- Every actual call preserves the complement of the fixed tree region. In particular,
updates do not allocate storage depending on the number of previous operations. -/
theorem execOp_frame (ha : Fits w (b + 2 * 2 ^ h)) {s : List ℕ} {o : Operation}
    {y : Data 14} {a : ℕ} {trace : DynamicProgram.OperationTrace}
    (hx : Rep h b w s x) (ho : (spec h w).valid s o)
    (he : (program h w).ExecOp w x o a y trace) {j : ℕ}
    (hj : j < b ∨ b + Tree.words h ≤ j) : y.mem j = x.mem j := by
  obtain ⟨z, ⟨_, _, hk⟩, _, _, hf⟩ := dispatch_spec ha o hx ho
  exact (he.eq_of_exec hk).1 ▸ hf j hj

/-- Every admissible adaptive client has a concrete execution with the specified result and
final array, and at most `13 (h + 1) + 12` instructions for each selected operation. The client
controller itself is mathematical; this counts its calls into the fixed machine program. -/
theorem client_spec (ha : Fits w (b + 2 * 2 ^ h)) {α : Type}
    (p : (spec h w).Client α) {s : List ℕ} (hx : Rep h b w s x)
    (hv : (spec h w).ValidHistory s ((spec h w).runClient s p).2.2) :
    ∃ y traces, Stateful.Executes ((program h w).ExecOp w) p x
        ((spec h w).runClient s p).1 y traces ∧
      Rep h b w ((spec h w).runClient s p).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        ((spec h w).runClient s p).2.2.length * (13 * (h + 1) + 12) :=
  (certificate ha).run_client_const (instruction_bound ha) p hx hv

/-- Concrete zero memory and persistent metadata. Supplying this state is not a charged
initialization algorithm. -/
def zeroData (h b : ℕ) : Data 14 where
  regs j := if j = root then b else if j = capacity then 2 ^ h else 0
  mem _ := 0

/-- The representation assumptions are inhabited at every fitting size and root pointer. -/
theorem rep_zeroData (ha : Fits w (b + 2 * 2 ^ h)) :
    Rep h b w (Tree.zero h).leaves (zeroData h b) := by
  have hb : Fits w b := ha.of_le (by omega)
  have hn : Fits w (2 ^ h) := ha.of_le (by omega)
  refine ⟨⟨?_, fun _ => fits_zero w⟩, ?_, ?_, Tree.zero h, rfl, Tree.rep_zero h b⟩
  · intro j
    simp only [zeroData]
    split
    · exact hb
    · split
      · exact hn
      · exact fits_zero w
  · simp +decide [zeroData]
  · simp +decide [zeroData]

end Cslib.Algorithms.WordRAM.PrefixSums

end
