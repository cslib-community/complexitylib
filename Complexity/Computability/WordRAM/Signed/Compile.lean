/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.Operations

/-!
# Compiling signed RAM programs to the unsigned word RAM

Each source instruction occupies sixty-four target instruction slots. The live prefix uses
the proved data/test blocks, followed by relocated control flow; the remaining slots are
unreachable padding on successful source runs. Target control labels are natural instruction
indices and need not fit a word. Source data occupies the register bank and encoded memory.

All instructions of `GenericRAM.Signed.model` (including all five signed arithmetic operations)
are compiled. The compiler transfers successful runs; it does not promise to reproduce source
faults.

## Main definitions

* `ToWordRAM.entry`, `ToWordRAM.rawBlock`, `ToWordRAM.block`, `ToWordRAM.compileFrom`:
  fixed-size instruction blocks with relocated branches and jumps.

## Main results

* `ToWordRAM.runs_compile`: run-prefix simulation preserving registers and memory.
* `ToWordRAM.executes_compile`: whole-run forward simulation with two extra bits.

## References

The fixed-block organization follows the library's `WordRAM.ToRAM` compiler. The target
translation and the signed representation are new; no alternative source machine is defined.
-/

@[expose] public section

namespace Cslib.GenericRAM.Signed.ToWordRAM

open WordRAM (Code ExecWithin Exec)
open WordRAM.Signed

variable {r : ℕ}

/-- Native instruction address of source instruction `pc`, with code placed after `base`. -/
def entry (base pc : ℕ) : ℕ := base + 64 * pc

/-- The live prefix of an instruction block, including its terminal control instruction(s). -/
def rawBlock (base pc : ℕ) : GenericRAM.Instr model r → WordRAM.Program .standard (r + 9)
  | .op o => (compileOp o).assemble (entry base pc) ++ [.jump (entry base (pc + 1))]
  | .jump t => [.jump (entry base t)]
  | .branch c t => (compileCond c).assemble (entry base pc) ++
      [.branch (.eq result two) (entry base t), .jump (entry base (pc + 1))]
  | .halt i => [.halt (bank i)]

/-- A full sixty-four-slot block; successful runs never execute the padding. -/
def block (base pc : ℕ) (i : GenericRAM.Instr model r) : WordRAM.Program .standard (r + 9) :=
  rawBlock base pc i ++ List.replicate (64 - (rawBlock base pc i).length)
    (.jump (entry base (pc + 1)))

/-- Compile a suffix whose first source instruction has index `pc`. -/
def compileFrom (base : ℕ) : ℕ → GenericRAM.Program model r → WordRAM.Program .standard (r + 9)
  | _, [] => []
  | pc, i :: p => block base pc i ++ compileFrom base (pc + 1) p

private theorem size_arithmeticCode (f : Arithmetic) : (arithmeticCode (r := r) f).size ≤ 28 := by
  cases f <;> simp [arithmeticCode, Code.size, WordRAM.Signed.add, subtract, multiply, divide,
    modulo, unpack, addCore, addMagnitudes, finish, flipRightSign, multiplyMagnitudes,
    divideMagnitudes, moduloCore]

private theorem size_compileOp (o : GenericRAM.Op model r) : (compileOp o).size ≤ 31 := by
  cases o with
  | alu f d args =>
    simp only [compileOp, operandsCode, Code.size]
    have := size_arithmeticCode (r := r) f
    omega
  | _ => simp [compileOp, addressCode, Code.size]

private theorem size_compileCond (c : GenericRAM.Cond model r) : (compileCond c).size ≤ 20 := by
  cases c with
  | test f args => cases f <;> simp [compileCond, operandsCode, less, Code.size]

/-- Every live prefix fits in its fixed-size block. -/
theorem length_rawBlock_le (base pc : ℕ) (i : GenericRAM.Instr model r) :
    (rawBlock base pc i).length ≤ 64 := by
  cases i with
  | op o =>
    simp only [rawBlock, List.length_append, WordRAM.Code.length_assemble,
      List.length_cons, List.length_nil]
    have := size_compileOp o
    omega
  | branch c t =>
    simp only [rawBlock, List.length_append, WordRAM.Code.length_assemble,
      List.length_cons, List.length_nil]
    have := size_compileCond c
    omega
  | _ => simp [rawBlock]

/-- Every source instruction occupies exactly sixty-four target slots. -/
@[simp]
theorem length_block (base pc : ℕ) (i : GenericRAM.Instr model r) :
    (block base pc i).length = 64 := by
  have := length_rawBlock_le base pc i
  simp only [block, List.length_append, List.length_replicate]
  omega

/-- Code size is linear in source instruction-list length. -/
@[simp]
theorem length_compileFrom (base pc : ℕ) (p : GenericRAM.Program model r) :
    (compileFrom base pc p).length = 64 * p.length := by
  induction p generalizing pc with
  | nil => simp [compileFrom]
  | cons i p ih => simp [compileFrom, ih, Nat.mul_add, Nat.add_comm]

private theorem contains_raw {base start : ℕ} {p : GenericRAM.Program model r}
    {q : WordRAM.Program .standard (r + 9)}
    (hq : q.Contains (entry base start) (compileFrom base start p))
    {pc : ℕ} {i : GenericRAM.Instr model r} (hi : p[pc]? = some i) :
    q.Contains (entry base (start + pc)) (rawBlock base (start + pc) i) := by
  induction p generalizing start pc with
  | nil => simp at hi
  | cons a p ih =>
    cases pc with
    | zero =>
      have he : a = i := by simpa using hi
      subst i
      exact hq.append_left.append_left
    | succ pc =>
      have ht : q.Contains (entry base (start + 1)) (compileFrom base (start + 1) p) := by
        simpa only [length_block, entry, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
          hq.append_right
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih ht (by simpa using hi)

private theorem continue_eq {w : ℕ} {s t : GenericRAM.State model r}
    (h : GenericRAM.Outcome.continue w s = .next t) : s = t := by
  unfold GenericRAM.Outcome.continue at h
  split_ifs at h; simp_all

private theorem next_simulation {w base : ℕ} {p : GenericRAM.Program model r}
    {q : WordRAM.Program .standard (r + 9)} {s t : GenericRAM.State model r}
    {x : WordRAM.Data (r + 9)}
    (hcode : ∀ pc i, p[pc]? = some i → q.Contains (entry base pc) (rawBlock base pc i))
    (hx : Represents w s.data x) (hn : GenericRAM.Next w p s t) :
    ∃ y k, k ≤ 32 ∧ WordRAM.Runs (w + 2) q ⟨entry base s.pc, x⟩
      ⟨entry base t.pc, y⟩ k ∧ Represents w t.data y := by
  unfold GenericRAM.Next GenericRAM.step at hn
  split at hn
  next hpc =>
    cases hi : p[s.pc]? with
    | none => simp [hi] at hn
    | some i =>
      have hc := hcode s.pc i hi
      simp only [hi] at hn
      cases i with
      | op o =>
        cases he : o.eval w s.data with
        | none => simp [he] at hn
        | some d =>
          have ht : (⟨s.pc + 1, d⟩ : GenericRAM.State model r) = t :=
            continue_eq (w := w) (by simpa only [he] using hn)
          subst t
          obtain ⟨y, ⟨k, hk, hex⟩, hyr⟩ := exec_compileOp o hx he
          have hr : WordRAM.Runs (w + 2) q ⟨entry base s.pc, x⟩
              ⟨entry base s.pc + (compileOp o).size, y⟩ k := hex.runs hc.append_left
          have hj : WordRAM.Next (w + 2) q ⟨entry base s.pc + (compileOp o).size, y⟩
              ⟨entry base (s.pc + 1), y⟩ := by
            exact WordRAM.step_jump (by simpa using hc.append_right.head)
          exact ⟨y, k + 1, by omega, hr.tail _ _ _ _ hj, hyr⟩
      | jump target =>
        have ht : (⟨target, s.data⟩ : GenericRAM.State model r) = t := continue_eq (w := w) hn
        subst t
        exact ⟨x, 1, by decide, .single (WordRAM.step_jump hc.head), hx⟩
      | branch c target =>
        cases htest : c.eval w s.data with
        | none => simp [htest] at hn
        | some b =>
          have ht : (⟨if b then target else s.pc + 1, s.data⟩ : GenericRAM.State model r) = t :=
            continue_eq (w := w) (by simpa only [htest] using hn)
          subst t
          obtain ⟨y, ⟨k, hk, hex⟩, hyr, hyo, hyrep⟩ := exec_compileCond c hx htest
          have hr : WordRAM.Runs (w + 2) q ⟨entry base s.pc, x⟩
              ⟨entry base s.pc + (compileCond c).size, y⟩ k := hex.runs hc.append_left
          have hb : q[entry base s.pc + (compileCond c).size]? =
              some (.branch (.eq result two) (entry base target)) := by
            simpa using hc.append_right.head
          have hj : q[entry base s.pc + (compileCond c).size + 1]? =
              some (.jump (entry base (s.pc + 1))) := by
            simpa only [WordRAM.Code.length_assemble] using hc.append_right.cons_tail.head
          cases b with
          | false =>
            have hcond : ¬(WordRAM.Cond.eq result two).Holds y := by
              simp [WordRAM.Cond.holds_eq, hyr, hyo]
            have hfirst : WordRAM.Next (w + 2) q
                ⟨entry base s.pc + (compileCond c).size, y⟩
                ⟨entry base s.pc + (compileCond c).size + 1, y⟩ := by
              simpa only [WordRAM.Next, hcond, ite_false] using WordRAM.step_branch (w := w + 2)
                (s := ⟨entry base s.pc + (compileCond c).size, y⟩) hb
            have hlast : WordRAM.Next (w + 2) q
                ⟨entry base s.pc + (compileCond c).size + 1, y⟩
                ⟨entry base (s.pc + 1), y⟩ := WordRAM.step_jump hj
            exact ⟨y, k + 1 + 1, by omega, (hr.tail _ _ _ _ hfirst).tail _ _ _ _ hlast, hyrep⟩
          | true =>
            have hcond : (WordRAM.Cond.eq result two).Holds y := by
              simp [WordRAM.Cond.holds_eq, hyr, hyo]
            have hlast : WordRAM.Next (w + 2) q
                ⟨entry base s.pc + (compileCond c).size, y⟩
                ⟨entry base target, y⟩ := by
              simpa only [WordRAM.Next, hcond, ite_true] using WordRAM.step_branch (w := w + 2)
                (s := ⟨entry base s.pc + (compileCond c).size, y⟩) hb
            exact ⟨y, k + 1, by omega, hr.tail _ _ _ _ hlast, hyrep⟩
      | halt i =>
        change (if model.validMove w (s.data.regs i) then
          GenericRAM.Outcome.halt (s.data.regs i) else .fault) =
            (GenericRAM.Outcome.next t : GenericRAM.Outcome model r) at hn
        split at hn <;> cases hn
  next hpc => cases hn

private theorem runs_simulation {w base n : ℕ} {p : GenericRAM.Program model r}
    {q : WordRAM.Program .standard (r + 9)} {s t : GenericRAM.State model r}
    (hcode : ∀ pc i, p[pc]? = some i → q.Contains (entry base pc) (rawBlock base pc i))
    {x : WordRAM.Data (r + 9)} (hx : Represents w s.data x)
    (hr : GenericRAM.Runs w p s t n) :
    ∃ y k, k ≤ 32 * n ∧ WordRAM.Runs (w + 2) q ⟨entry base s.pc, x⟩
      ⟨entry base t.pc, y⟩ k ∧ Represents w t.data y := by
  induction hr generalizing x with
  | refl => exact ⟨x, 0, by omega, .refl _, hx⟩
  | tail s t n hsteps hnext ih =>
    obtain ⟨y, k, hk, hrun, hyr⟩ := ih hx
    obtain ⟨z, l, hl, hlast, hzr⟩ := next_simulation hcode hyr hnext
    exact ⟨z, k + l, by omega, hrun.trans hlast, hzr⟩

private theorem continue_ne_halt {w : ℕ} (s : GenericRAM.State model r) (v : ℤ) :
    GenericRAM.Outcome.continue w s ≠ .halt v := by
  unfold GenericRAM.Outcome.continue
  split_ifs <;> simp

private theorem halt_simulation {w base : ℕ} {p : GenericRAM.Program model r}
    {q : WordRAM.Program .standard (r + 9)} {s : GenericRAM.State model r} {v : ℤ}
    {x : WordRAM.Data (r + 9)}
    (hcode : ∀ pc i, p[pc]? = some i → q.Contains (entry base pc) (rawBlock base pc i))
    (hx : Represents w s.data x) (he : GenericRAM.step w p s = .halt v) :
    WordRAM.step (w + 2) q ⟨entry base s.pc, x⟩ = .halt (encode v) := by
  unfold GenericRAM.step at he
  split at he
  next hpc =>
    cases hi : p[s.pc]? with
    | none => simp [hi] at he
    | some i =>
      have hc := hcode s.pc i hi
      simp only [hi] at he
      cases i with
      | op o =>
        cases ho : o.eval w s.data with
        | none => simp [ho] at he
        | some d =>
          exact False.elim (continue_ne_halt (w := w) ⟨s.pc + 1, d⟩ v
            (by simpa only [ho] using he))
      | jump target =>
        exact False.elim (continue_ne_halt (w := w) ⟨target, s.data⟩ v he)
      | branch c target =>
        cases ho : c.eval w s.data with
        | none => simp [ho] at he
        | some b =>
          exact False.elim (continue_ne_halt (w := w)
            ⟨if b then target else s.pc + 1, s.data⟩ v (by simpa only [ho] using he))
      | halt i =>
        change (if model.validMove w (s.data.regs i) then
          GenericRAM.Outcome.halt (s.data.regs i) else .fault) =
            (GenericRAM.Outcome.halt v : GenericRAM.Outcome model r) at he
        have hv : s.data.regs i = v := by
          split at he
          · exact GenericRAM.Outcome.halt.inj he
          · cases he
        simpa only [hx.regs, hv] using WordRAM.step_halt (w := w + 2)
          (s := ⟨entry base s.pc, x⟩) hc.head
  next hpc => cases he

/-- The compiler places every live instruction prefix at its relocated address. -/
theorem contains_compileFrom (pre : WordRAM.Program .standard (r + 9))
    {p : GenericRAM.Program model r} {pc : ℕ} {i : GenericRAM.Instr model r}
    (hi : p[pc]? = some i) :
    (pre ++ compileFrom pre.length 0 p).Contains
      (entry pre.length pc) (rawBlock pre.length pc i) := by
  have hstart : (pre ++ compileFrom pre.length 0 p).Contains (entry pre.length 0)
      (compileFrom pre.length 0 p) := ⟨pre, [], by simp, by simp [entry]⟩
  simpa only [Nat.zero_add] using contains_raw hstart hi

/-- Every successful source run prefix preserves the represented register file and memory
at the translated instruction boundary, within thirty-two target instructions per step.
Execution of the supplied prefix `pre` is not included. -/
theorem runs_compile {w n : ℕ} {p : GenericRAM.Program model r}
    (pre : WordRAM.Program .standard (r + 9))
    {s t : GenericRAM.State model r} {x : WordRAM.Data (r + 9)}
    (hx : Represents w s.data x) (hr : GenericRAM.Runs w p s t n) :
    ∃ y k, k ≤ 32 * n ∧
      WordRAM.Runs (w + 2) (pre ++ compileFrom pre.length 0 p)
        ⟨entry pre.length s.pc, x⟩ ⟨entry pre.length t.pc, y⟩ k ∧ Represents w t.data y := by
  exact runs_simulation (fun pc i hi => contains_compileFrom pre hi) hx hr

/-- Every successful source run of a signed RAM program transfers to the compiled
unsigned program at width `w + 2` in at most thirty-two target instructions per source
instruction, including the final halt. Execution of `pre` is not charged here; the target
starts at the translated source instruction with already represented data. -/
theorem executes_compile {w n : ℕ} {p : GenericRAM.Program model r}
    (pre : WordRAM.Program .standard (r + 9))
    {s : GenericRAM.State model r} {x : WordRAM.Data (r + 9)} {v : ℤ}
    (hx : Represents w s.data x) (hr : GenericRAM.Executes w p s v n) :
    ∃ k ≤ 32 * n, WordRAM.Executes (w + 2) (pre ++ compileFrom pre.length 0 p)
      ⟨entry pre.length s.pc, x⟩ (encode v) k := by
  obtain ⟨t, m, hsteps, hhalt, rfl⟩ := hr
  have hc := fun pc i hi => contains_compileFrom (p := p) (pc := pc) (i := i) pre hi
  obtain ⟨y, k, hk, hrun, hyr⟩ := runs_simulation hc hx hsteps
  have ht := halt_simulation hc hyr hhalt
  exact ⟨k + 1, by omega, WordRAM.Executes.of_runs hrun (WordRAM.Executes.halt ht)⟩

end Cslib.GenericRAM.Signed.ToWordRAM
