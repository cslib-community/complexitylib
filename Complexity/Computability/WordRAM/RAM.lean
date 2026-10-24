/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.MapOp
public import Complexity.Computability.RAM.Cost
import Mathlib.Data.List.GetD

/-!
# Compiling additive word RAMs to logarithmic-cost RAMs

The additive fragment of `Cslib.WordRAM` uses constants, copying, addition, truncated
subtraction, indirect memory, comparisons and control flow. Its compiler uses the existing
natural-number `Cslib.RAM` with logarithmic instruction costs. This is a forward simulation
of successful, bounded-word executions; it does not reflect overflow faults or simulate the
word-width instruction, multiplication, division, bitwise operations or shifts.

Source registers occupy target registers `1, …, r`. Register `0` is zero until the final
output is copied to it. Four further registers hold `1`, the fixed memory offset, and two
scratch values. Source memory address `a` occupies target register `r + 5 + a`, so indirect
stores cannot alias the source registers or compiler scratch space. Every source instruction
occupies eight target instruction slots; jumps skip unused slots.

The source machine is adapted from the lean-trominoes formalization
[MIT–ULB CompGeom Group][Tromino2025]. The target is the natural-number RAM adaptation of
[Cook and Reckhow][CookReckhow1973] documented in `Cslib.RAM`, not literally their original
integer/I/O model. Neither this compiler nor its cost bound is a Turing-machine simulation.

## Main definitions

* `Cslib.WordRAM.Instr.IsAdditive`, `Cslib.WordRAM.Program.IsAdditive`: the supported instruction
  and program fragment.
* `Cslib.WordRAM.ToRAM.memoryBase`, `Cslib.WordRAM.ToRAM.one`, `Cslib.WordRAM.ToRAM.offset`,
  `Cslib.WordRAM.ToRAM.address`, `Cslib.WordRAM.ToRAM.test`, `Cslib.WordRAM.ToRAM.entry`: target
  register layout and instruction block offsets.
* `Cslib.WordRAM.ToRAM.compileInstr`, `Cslib.WordRAM.ToRAM.compile`,
  `Cslib.WordRAM.ToRAM.compileAdditive`: fixed-block instruction and program compilation, with
  explicit code placement.
* `Cslib.WordRAM.ToRAM.prologue`, `Cslib.WordRAM.ToRAM.paddedProgram`,
  `Cslib.WordRAM.ToRAM.paddedProgramAdditive`: compiler prologue and complete compiled programs
  using `paddedInput`.
* `Cslib.WordRAM.ToRAM.Represents`: the register and memory layout.

## Main results

* `Cslib.WordRAM.Fits.bitLength_le`: a fitting word has `RAM.bitLength` at most `w + 1`.
* `Cslib.WordRAM.Program.mapOp_additiveHomStandard_isAdditive`: every program translated from
  `Basis.additive` belongs to the additive fragment.
* `Cslib.WordRAM.ToRAM.executes_compile`, `Cslib.WordRAM.ToRAM.executes_compileAdditive`: a
  successful bounded-word run is simulated by the actual compiled code with logarithmic cost at
  most `8 t (bitLength (r + 5) + w + 1)`.
* `Cslib.WordRAM.ToRAM.haltsWithResultInTime_padded`,
  `Cslib.WordRAM.ToRAM.haltsWithResultInTime_padded_additive`: the complete target program,
  including its register initialization, uses logarithmic cost at most
  `8 (bitLength (r + 5) + 1) (t + 1) (w + 1)` on the stated padded input convention.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.WordRAM

variable {r : ℕ}

/-- A word fitting `w` bits has logarithmic RAM bit-length at most `w + 1`. -/
theorem Fits.bitLength_le {w v : ℕ} (h : Fits w v) : RAM.bitLength v ≤ w + 1 :=
  (RAM.bitLength_le_iff (Nat.succ_ne_zero w)).2 (h.mono (Nat.le_succ w))

/-- The fragment compiled to the logarithmic-cost natural-number RAM. -/
def Instr.IsAdditive : Instr .standard r → Prop
  | .op (.alu (.bin f) ..) => f = .add ∨ f = .sub
  | .op (.alu .width ..) => False
  | _ => True

/-- Decidability of `Instr.IsAdditive`. -/
instance (i : Instr .standard r) : Decidable i.IsAdditive :=
  match i with
  | .op (.alu (.bin f) ..) => inferInstanceAs (Decidable (f = .add ∨ f = .sub))
  | .op (.alu .width ..) => isFalse id
  | .op (.const ..) | .op (.copy ..) | .op (.load ..) | .op (.store ..) | .jump .. | .branch ..
  | .halt .. => isTrue trivial

/-- Every instruction belongs to the additive-memory fragment. -/
def Program.IsAdditive (p : Program .standard r) : Prop := ∀ i ∈ p, i.IsAdditive

/-- Decidability of `Program.IsAdditive`. -/
instance (p : Program .standard r) : Decidable p.IsAdditive :=
  inferInstanceAs (Decidable (∀ i ∈ p, i.IsAdditive))

/-- Every instruction translated from `Basis.additive` belongs to the additive fragment. -/
theorem Instr.mapOp_additiveHomStandard_isAdditive (i : Instr .additive r) :
    (i.mapOp Basis.additiveHomStandard).IsAdditive := by
  cases i with
  | op o =>
    cases o with
    | alu f d args =>
      rcases f with ⟨f, hf⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | _ => trivial
  | _ => trivial

/-- Every program translated from `Basis.additive` belongs to the additive fragment. -/
theorem Program.mapOp_additiveHomStandard_isAdditive (p : Program .additive r) :
    (p.mapOp Basis.additiveHomStandard).IsAdditive := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hi
  exact j.mapOp_additiveHomStandard_isAdditive

/-- Assembling a structured program over `Basis.additive` and translating to `Basis.standard`
produces an additive-fragment program. -/
theorem Code.program_mapOp_additiveHomStandard_isAdditive (c : Code .additive r) (out : Fin r) :
    ((c.mapOp Basis.additiveHomStandard).program out).IsAdditive := by
  rw [Code.program_mapOp]
  exact (c.program out).mapOp_additiveHomStandard_isAdditive

namespace ToRAM

/-- The first target register used to represent source memory. -/
def memoryBase (r : ℕ) : ℕ := r + 5

/-- Target register holding the constant one. -/
def one (r : ℕ) : ℕ := r + 1
/-- Target register holding the memory offset. -/
def offset (r : ℕ) : ℕ := r + 2
/-- Scratch register holding a translated indirect address. -/
def address (r : ℕ) : ℕ := r + 3
/-- Scratch register holding a truncated difference for a comparison. -/
def test (r : ℕ) : ℕ := r + 4

/-- The target instruction corresponding to a source program counter. -/
def entry (base pc : ℕ) : ℕ := base + 8 * pc

/-- One slot in the eight-instruction block for a source instruction. -/
def compileInstr (base length pc : ℕ) (i : Instr .standard r) (k : ℕ) : RAM.Instr :=
  let next := entry base (pc + 1)
  let jump := fun q => RAM.Instr.jpos (one r) q
  match i, k with
  | .op (.const d v), 0 => .const (d + 1) v
  | .op (.copy d s), 0 => .add (d + 1) (s + 1) 0
  | .op (.alu (.bin .add) d a), 0 => .add (d + 1) (a (0 : Fin 2) + 1) (a (1 : Fin 2) + 1)
  | .op (.alu (.bin .sub) d a), 0 => .sub (d + 1) (a (0 : Fin 2) + 1) (a (1 : Fin 2) + 1)
  | .op (.load _ a), 0 | .op (.store a _), 0 => .add (address r) (a + 1) (offset r)
  | .op (.load d _), 1 => .load (d + 1) (address r)
  | .op (.store _ s), 1 => .store (address r) (s + 1)
  | .jump q, 0 => jump (entry base q)
  | .branch (.lt i j) _, 0 => .sub (test r) (j + 1) (i + 1)
  | .branch (.lt _ _) q, 1 => .jpos (test r) (entry base q)
  | .branch (.eq i j) _, 0 => .sub (test r) (i + 1) (j + 1)
  | .branch (.eq _ _) _, 1 => .jpos (test r) next
  | .branch (.eq i j) _, 2 => .sub (test r) (j + 1) (i + 1)
  | .branch (.eq _ _) _, 3 => .jpos (test r) next
  | .branch (.eq _ _) q, 4 => jump (entry base q)
  | .halt i, 0 => .add 0 (i + 1) 0
  | .halt _, 1 => jump (entry base length)
  | _, _ => jump next

/-- Compile into blocks of eight instructions. `base` is the position where the result will
be inserted in the target program; jump targets are absolute. The unsupported instructions
have no correctness specification. The compiler is independent of word size and input. -/
def compile (base : ℕ) (p : Program .standard r) : RAM.Program :=
  List.ofFn fun k : Fin (8 * p.length) =>
    match p[k.1 / 8]? with
    | some i => compileInstr base p.length (k.1 / 8) i (k.1 % 8)
    | none => .jpos (one r) (entry base p.length)

/-- Each compiled source instruction occupies eight target instructions. -/
@[simp]
theorem length_compile (base : ℕ) (p : Program .standard r) :
    (compile base p).length = 8 * p.length :=
  List.length_ofFn

private theorem getElem?_compile {base pc k : ℕ} {p : Program .standard r} {i : Instr .standard r}
    (hi : p[pc]? = some i) (hk : k < 8) :
    (compile base p)[8 * pc + k]? = some (compileInstr base p.length pc i k) := by
  have hp : pc < p.length := List.getElem?_eq_some_iff.1 hi |>.1
  have hb : 8 * pc + k < 8 * p.length := by lia
  simp [compile, hb, Nat.mul_add_div,
    Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, hi]

/-- The register/memory representation at source instruction boundaries. Scratch registers
are deliberately unconstrained: each is overwritten before the compiler reads it. -/
structure Represents (x : Data r) (σ : URM.Regs) : Prop where
  /-- Register zero remains zero until the final output copy. -/
  zero : σ.read 0 = 0
  /-- A permanent positive register implements unconditional jumps. -/
  one : σ.read (one r) = 1
  /-- The memory base is available for indirect addressing. -/
  offset : σ.read (offset r) = memoryBase r
  /-- The finite source register file is disjoint from the other regions. -/
  regs : ∀ i : Fin r, σ.read (i + 1) = x.regs i
  /-- The source memory occupies the remaining target registers. -/
  mem : ∀ a, σ.read (memoryBase r + a) = x.mem a

namespace Represents

variable {x : Data r} {σ : URM.Regs}

private theorem set (h : Represents x σ) (i : Fin r) (v : ℕ) :
    Represents (x.set i v) (σ.write (i + 1) v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [URM.Regs.write_read_of_ne _ _ _ _ (by lia), h.zero]
  · rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [ToRAM.one]; have := i.isLt; lia), h.one]
  · rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [ToRAM.offset]; have := i.isLt; lia), h.offset]
  · intro j
    by_cases hj : j = i
    · subst j; simp [Data.set]
    · rw [URM.Regs.write_read_of_ne _ _ _ _ (by intro he; apply hj; apply Fin.ext; lia)]
      simp [Data.set, Function.update_of_ne hj, h.regs]
  · intro a
    rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [memoryBase]; have := i.isLt; lia)]
    exact h.mem a

/-- Writing a source memory cell corresponds to writing the offset target register. -/
theorem write (h : Represents x σ) (a v : ℕ) :
    Represents (x.write a v) (σ.write (memoryBase r + a) v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [memoryBase]; lia), h.zero]
  · rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [ToRAM.one, memoryBase]; lia), h.one]
  · rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [ToRAM.offset, memoryBase]; lia), h.offset]
  · intro i
    rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [memoryBase]; have := i.isLt; lia)]
    exact h.regs i
  · intro b
    by_cases hb : b = a
    · subst b; simp [Data.write]
    · rw [URM.Regs.write_read_of_ne _ _ _ _ (by lia)]
      simp [Data.write, Function.update_of_ne hb, h.mem]

private theorem scratch (h : Represents x σ) {a : ℕ} (ha : a = address r ∨ a = test r) (v : ℕ) :
    Represents x (σ.write a v) := by
  rcases ha with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [address, test]; lia), h.zero]
    | rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [ToRAM.one, address, test]; lia), h.one]
    | rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [ToRAM.offset, address, test]; lia), h.offset]
    | (intro i
       rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [address, test]; have := i.isLt; lia)]
       exact h.regs i)
    | (intro a
       rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [memoryBase, address, test]; lia)]
       exact h.mem a)

end Represents

private def Reaches (p : RAM.Program) (s t : RAM.State) (T : ℕ) : Prop :=
  ∃ n, RAM.run p n s = t ∧ RAM.time RAM.logCost p n s ≤ T

private theorem Reaches.step {p : RAM.Program} {s : RAM.State} {i : RAM.Instr}
    (hi : p[s.pc]? = some i) : Reaches p s (i.exec s) (RAM.logCost i s.regs) := by
  refine ⟨1, ?_, ?_⟩
  · rw [RAM.run_succ, RAM.run_zero, RAM.step_of_getElem? hi]
  · rw [RAM.time_succ, RAM.time_zero, Nat.add_zero, RAM.stepCost_of_getElem? hi]

private theorem Reaches.trans {p : RAM.Program} {s t u : RAM.State} {T U : ℕ}
    (h : Reaches p s t T) (h' : Reaches p t u U) : Reaches p s u (T + U) := by
  obtain ⟨m, hm, ht⟩ := h
  obtain ⟨n, hn, hu⟩ := h'
  exact ⟨m + n, by rw [RAM.run_add, hm, hn], by
    rw [RAM.time_add, hm]; exact Nat.add_le_add ht hu⟩

private theorem Reaches.mono {p : RAM.Program} {s t : RAM.State} {T U : ℕ}
    (h : Reaches p s t T) (hTU : T ≤ U) : Reaches p s t U := by
  obtain ⟨n, hn, ht⟩ := h
  exact ⟨n, hn, ht.trans hTU⟩

private theorem reaches_jump {p : RAM.Program} {pc target : ℕ} {σ : URM.Regs}
    (hi : p[pc]? = some (.jpos (one r) target)) (hσ : σ.read (one r) = 1) :
    Reaches p ⟨pc, σ⟩ ⟨target, σ⟩ 1 := by
  have h := Reaches.step (s := ⟨pc, σ⟩) hi
  simpa [RAM.Instr.exec, RAM.logCost, hσ, RAM.bitLength] using h

private def BlockAt (q : RAM.Program) (base length pc : ℕ) (i : Instr .standard r) : Prop :=
  ∀ k < 8, q[entry base pc + k]? = some (compileInstr base length pc i k)

private theorem BlockAt.first {q : RAM.Program} {base length pc : ℕ} {i : Instr .standard r}
    (h : BlockAt q base length pc i) :
    q[entry base pc]? = some (compileInstr base length pc i 0) := by
  simpa only [Nat.add_zero] using h 0 (by decide)

private theorem reaches_set_jump {q : RAM.Program} {pc target : ℕ} {x : Data r}
    {σ : URM.Regs} {i : RAM.Instr} {d : Fin r} {v : ℕ}
    (hσ : Represents x σ) (h0 : q[pc]? = some i)
    (he : i.exec ⟨pc, σ⟩ = ⟨pc + 1, σ.write (d + 1) v⟩)
    (h1 : q[pc + 1]? = some (.jpos (one r) target)) :
    Reaches q ⟨pc, σ⟩ ⟨target, σ.write (d + 1) v⟩ (RAM.logCost i σ + 1) := by
  have hfirst := Reaches.step (s := ⟨pc, σ⟩) h0
  rw [he] at hfirst
  exact hfirst.trans (reaches_jump h1 (hσ.set d v).one)

private theorem op_simulation {q : RAM.Program} {base length pc w : ℕ} {o : Op .standard r}
    {x y : Data r} {σ : URM.Regs} (hcode : BlockAt q base length pc (.op o))
    (ho : (Instr.op o).IsAdditive) (hσ : Represents x σ) (hx : x.Bounded w)
    (he : o.eval w x = some y) :
    ∃ τ, Reaches q ⟨entry base pc, σ⟩ ⟨entry base (pc + 1), τ⟩
      (8 * (RAM.bitLength (memoryBase r) + w + 1)) ∧ Represents y τ := by
  have hr (i : Fin r) : RAM.bitLength (x.regs i) ≤ w + 1 := (hx.1 i).bitLength_le
  have hm (a : ℕ) : RAM.bitLength (x.mem a) ≤ w + 1 := (hx.2 a).bitLength_le
  cases o with
  | const d v =>
    obtain ⟨hv, rfl⟩ := Data.put_eq_some.1 he
    refine ⟨_, (reaches_set_jump hσ hcode.first rfl (hcode 1 (by decide))).mono ?_, hσ.set d v⟩
    change RAM.bitLength v + 1 ≤ _
    have := hv.bitLength_le
    lia
  | copy d i =>
    cases he
    refine ⟨_, (reaches_set_jump hσ hcode.first ?_ (hcode 1 (by decide))).mono ?_,
      hσ.set d (x.regs i)⟩
    · simp [compileInstr, RAM.Instr.exec, hσ.regs, hσ.zero]
    · simp only [compileInstr, RAM.logCost, hσ.regs, hσ.zero, RAM.bitLength_zero]
      have := hr i
      lia
  | alu f d args =>
    cases f with
    | width => cases ho
    | bin f =>
      rcases ho with rfl | rfl
      all_goals obtain ⟨_, rfl⟩ := Data.put_eq_some.1 he
      · refine ⟨_, (reaches_set_jump hσ hcode.first ?_ (hcode 1 (by decide))).mono ?_,
          hσ.set d (x.regs (args (0 : Fin 2)) + x.regs (args (1 : Fin 2)))⟩
        · simp [compileInstr, RAM.Instr.exec, hσ.regs]
        · simp only [compileInstr, RAM.logCost, hσ.regs]
          have := hr (args (0 : Fin 2))
          have := hr (args (1 : Fin 2))
          lia
      · refine ⟨_, (reaches_set_jump hσ hcode.first ?_ (hcode 1 (by decide))).mono ?_,
          hσ.set d (x.regs (args (0 : Fin 2)) - x.regs (args (1 : Fin 2)))⟩
        · simp [compileInstr, RAM.Instr.exec, hσ.regs]
        · simp only [compileInstr, RAM.logCost, hσ.regs]
          have := hr (args (0 : Fin 2))
          have := hr (args (1 : Fin 2))
          lia
  | load d a =>
    cases he
    let σ₁ := σ.write (address r) (memoryBase r + x.regs a)
    have hσ₁ : Represents x σ₁ := hσ.scratch (Or.inl rfl) _
    have hfirst : Reaches q ⟨entry base pc, σ⟩ ⟨entry base pc + 1, σ₁⟩
        (RAM.bitLength (x.regs a) + RAM.bitLength (memoryBase r)) := by
      simpa [compileInstr, RAM.Instr.exec, RAM.logCost, hσ.regs, hσ.offset, σ₁, Nat.add_comm]
        using Reaches.step (s := ⟨entry base pc, σ⟩) hcode.first
    have hrest := reaches_set_jump hσ₁ (hcode 1 (by decide))
      (d := d) (v := x.mem (x.regs a)) (by
        simp [compileInstr, RAM.Instr.exec, σ₁, hσ₁.mem])
      (by simpa [compileInstr, Nat.add_assoc] using hcode 2 (by decide))
    refine ⟨_, (hfirst.trans hrest).mono ?_, hσ₁.set d _⟩
    simp only [compileInstr, RAM.logCost, show σ₁.read (address r) = memoryBase r + x.regs a from
      URM.Regs.write_read_self _ _ _, hσ₁.mem]
    have := RAM.bitLength_add_le (memoryBase r) (x.regs a)
    have := hr a
    have := hm (x.regs a)
    lia
  | store a i =>
    cases he
    let σ₁ := σ.write (address r) (memoryBase r + x.regs a)
    have hσ₁ : Represents x σ₁ := hσ.scratch (Or.inl rfl) _
    have hfirst : Reaches q ⟨entry base pc, σ⟩ ⟨entry base pc + 1, σ₁⟩
        (RAM.bitLength (x.regs a) + RAM.bitLength (memoryBase r)) := by
      simpa [compileInstr, RAM.Instr.exec, RAM.logCost, hσ.regs, hσ.offset, σ₁, Nat.add_comm]
        using Reaches.step (s := ⟨entry base pc, σ⟩) hcode.first
    let σ₂ := σ₁.write (memoryBase r + x.regs a) (x.regs i)
    have hσ₂ : Represents (x.write (x.regs a) (x.regs i)) σ₂ := hσ₁.write _ _
    have hsecond : Reaches q ⟨entry base pc + 1, σ₁⟩ ⟨entry base pc + 2, σ₂⟩
        (RAM.bitLength (memoryBase r + x.regs a) + RAM.bitLength (x.regs i)) := by
      simpa [compileInstr, RAM.Instr.exec, RAM.logCost, σ₂, hσ₁.regs,
        show σ₁.read (address r) = memoryBase r + x.regs a from URM.Regs.write_read_self _ _ _,
        Nat.add_assoc] using Reaches.step (s := ⟨entry base pc + 1, σ₁⟩) (hcode 1 (by decide))
    refine ⟨_, ((hfirst.trans hsecond).trans
      (reaches_jump (hcode 2 (by decide)) hσ₂.one)).mono ?_, hσ₂⟩
    have := RAM.bitLength_add_le (memoryBase r) (x.regs a)
    have := hr a
    have := hr i
    lia

private theorem branch_simulation {q : RAM.Program} {base length pc target w : ℕ}
    {c : Cond r} {x : Data r} {σ : URM.Regs}
    (hcode : BlockAt q base length pc (.branch c target)) (hσ : Represents x σ)
    (hx : x.Bounded w) :
    ∃ τ, Reaches q ⟨entry base pc, σ⟩
      ⟨entry base (if c.Holds x then target else pc + 1), τ⟩
      (8 * (RAM.bitLength (memoryBase r) + w + 1)) ∧ Represents x τ := by
  have hr (i : Fin r) : RAM.bitLength (x.regs i) ≤ w + 1 := (hx.1 i).bitLength_le
  have hd (i j : Fin r) : RAM.bitLength (x.regs i - x.regs j) ≤ w + 1 :=
    (RAM.bitLength_mono (Nat.sub_le _ _)).trans (hr i)
  cases c with
  | lt i j =>
    let σ₁ := σ.write (test r) (x.regs j - x.regs i)
    have hσ₁ : Represents x σ₁ := hσ.scratch (Or.inr rfl) _
    have hfirst : Reaches q ⟨entry base pc, σ⟩ ⟨entry base pc + 1, σ₁⟩
        (RAM.bitLength (x.regs j) + RAM.bitLength (x.regs i)) := by
      simpa [compileInstr, RAM.Instr.exec, RAM.logCost, hσ.regs, σ₁]
        using Reaches.step (s := ⟨entry base pc, σ⟩) hcode.first
    have hsecond := Reaches.step (s := ⟨entry base pc + 1, σ₁⟩) (hcode 1 (by decide))
    by_cases hij : x.regs i < x.regs j
    · have hsecond' : Reaches q ⟨entry base pc + 1, σ₁⟩ ⟨entry base target, σ₁⟩
          (RAM.bitLength (x.regs j - x.regs i)) := by
        simpa [compileInstr, RAM.Instr.exec, RAM.logCost, σ₁, Nat.sub_pos_iff_lt, hij] using hsecond
      refine ⟨_, ?_, hσ₁⟩
      simpa only [Cond.holds_lt, ite_eq_left hij] using (hfirst.trans hsecond').mono (by
        have := hr i; have := hr j; have := hd j i; lia)
    · have hsecond' : Reaches q ⟨entry base pc + 1, σ₁⟩ ⟨entry base pc + 2, σ₁⟩
          (RAM.bitLength (x.regs j - x.regs i)) := by
        simpa [compileInstr, RAM.Instr.exec, RAM.logCost, σ₁, Nat.sub_pos_iff_lt, hij,
          Nat.add_assoc] using hsecond
      refine ⟨_, ?_, hσ₁⟩
      simpa only [Cond.holds_lt, ite_eq_right hij] using
        ((hfirst.trans hsecond').trans (reaches_jump (hcode 2 (by decide)) hσ₁.one)).mono (by
          have := hr i; have := hr j; have := hd j i; lia)
  | eq i j =>
    let σ₁ := σ.write (test r) (x.regs i - x.regs j)
    have hσ₁ : Represents x σ₁ := hσ.scratch (Or.inr rfl) _
    have hfirst : Reaches q ⟨entry base pc, σ⟩ ⟨entry base pc + 1, σ₁⟩
        (RAM.bitLength (x.regs i) + RAM.bitLength (x.regs j)) := by
      simpa [compileInstr, RAM.Instr.exec, RAM.logCost, hσ.regs, σ₁]
        using Reaches.step (s := ⟨entry base pc, σ⟩) hcode.first
    have hsecond := Reaches.step (s := ⟨entry base pc + 1, σ₁⟩) (hcode 1 (by decide))
    by_cases hji : x.regs j < x.regs i
    · have hsecond' : Reaches q ⟨entry base pc + 1, σ₁⟩ ⟨entry base (pc + 1), σ₁⟩
          (RAM.bitLength (x.regs i - x.regs j)) := by
        simpa [compileInstr, RAM.Instr.exec, RAM.logCost, σ₁, Nat.sub_pos_iff_lt, hji] using hsecond
      refine ⟨_, ?_, hσ₁⟩
      simpa only [Cond.holds_eq, ite_eq_right (by lia : x.regs i ≠ x.regs j)] using
        (hfirst.trans hsecond').mono (by have := hr i; have := hr j; have := hd i j; lia)
    · have hsecond' : Reaches q ⟨entry base pc + 1, σ₁⟩ ⟨entry base pc + 2, σ₁⟩
          (RAM.bitLength (x.regs i - x.regs j)) := by
        simpa [compileInstr, RAM.Instr.exec, RAM.logCost, σ₁, Nat.sub_pos_iff_lt, hji,
          Nat.add_assoc] using hsecond
      let σ₂ := σ₁.write (test r) (x.regs j - x.regs i)
      have hσ₂ : Represents x σ₂ := hσ₁.scratch (Or.inr rfl) _
      have hthird : Reaches q ⟨entry base pc + 2, σ₁⟩ ⟨entry base pc + 3, σ₂⟩
          (RAM.bitLength (x.regs j) + RAM.bitLength (x.regs i)) := by
        simpa [compileInstr, RAM.Instr.exec, RAM.logCost, hσ₁.regs, σ₂, Nat.add_assoc]
          using Reaches.step (s := ⟨entry base pc + 2, σ₁⟩) (hcode 2 (by decide))
      have hfourth := Reaches.step (s := ⟨entry base pc + 3, σ₂⟩) (hcode 3 (by decide))
      by_cases hij : x.regs i < x.regs j
      · have hfourth' : Reaches q ⟨entry base pc + 3, σ₂⟩ ⟨entry base (pc + 1), σ₂⟩
            (RAM.bitLength (x.regs j - x.regs i)) := by
          simpa [compileInstr, RAM.Instr.exec, RAM.logCost, σ₂, Nat.sub_pos_iff_lt, hij]
            using hfourth
        refine ⟨_, ?_, hσ₂⟩
        simpa only [Cond.holds_eq, ite_eq_right (by lia : x.regs i ≠ x.regs j)] using
          (((hfirst.trans hsecond').trans hthird).trans hfourth').mono (by
            have := hr i; have := hr j; have := hd i j; have := hd j i; lia)
      · have heq : x.regs i = x.regs j := by lia
        have hfourth' : Reaches q ⟨entry base pc + 3, σ₂⟩ ⟨entry base pc + 4, σ₂⟩
            (RAM.bitLength (x.regs j - x.regs i)) := by
          simpa [compileInstr, RAM.Instr.exec, RAM.logCost, σ₂, Nat.sub_pos_iff_lt, hij,
            Nat.add_assoc] using hfourth
        refine ⟨_, ?_, hσ₂⟩
        simpa only [Cond.holds_eq, ite_eq_left heq] using
          ((((hfirst.trans hsecond').trans hthird).trans hfourth').trans
            (reaches_jump (hcode 4 (by decide)) hσ₂.one)).mono (by
              have := hr i; have := hr j; have := hd i j; have := hd j i; lia)

private theorem halt_simulation {q : RAM.Program} {base length pc w : ℕ} {i : Fin r}
    {x : Data r} {σ : URM.Regs} (hcode : BlockAt q base length pc (.halt i))
    (hσ : Represents x σ) (hx : x.Bounded w) :
    ∃ τ, Reaches q ⟨entry base pc, σ⟩ ⟨entry base length, τ⟩
      (8 * (RAM.bitLength (memoryBase r) + w + 1)) ∧ τ.output = x.regs i := by
  let τ := σ.write 0 (x.regs i)
  have hfirst : Reaches q ⟨entry base pc, σ⟩ ⟨entry base pc + 1, τ⟩
      (RAM.bitLength (x.regs i) + 1) := by
    simpa [compileInstr, RAM.Instr.exec, RAM.logCost, hσ.regs, hσ.zero, τ]
      using Reaches.step (s := ⟨entry base pc, σ⟩) hcode.first
  have hone : τ.read (one r) = 1 := by
    rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [one]; lia), hσ.one]
  refine ⟨τ, (hfirst.trans (reaches_jump (hcode 1 (by decide)) hone)).mono ?_, ?_⟩
  · have := (hx.1 i).bitLength_le
    lia
  · exact URM.Regs.write_read_self _ _ _

private theorem next_simulation {p : Program .standard r} {q : RAM.Program} {base w : ℕ}
    {s t : State r} {σ : URM.Regs}
    (hcode : ∀ pc i, p[pc]? = some i → BlockAt q base p.length pc i)
    (hp : p.IsAdditive) (hσ : Represents s.data σ) (hs : s.data.Bounded w)
    (h : Next w p s t) :
    ∃ τ, Reaches q ⟨entry base s.pc, σ⟩ ⟨entry base t.pc, τ⟩
      (8 * (RAM.bitLength (memoryBase r) + w + 1)) ∧ Represents t.data τ := by
  cases hi : p[s.pc]? with
  | none => simp [Next, WordRAM.step, hi] at h
  | some i =>
    have hc := hcode s.pc i hi
    have ha := hp i (List.mem_of_getElem? hi)
    cases i with
    | op o =>
      cases he : o.eval w s.data with
      | none => simp [Next, WordRAM.step, hi, he] at h
      | some y =>
        have ht : t = ⟨s.pc + 1, y⟩ := by simpa [Next, WordRAM.step, hi, he] using h.symm
        subst t
        exact op_simulation hc ha hσ hs he
    | jump target =>
      have ht : t = ⟨target, s.data⟩ := by simpa [Next, WordRAM.step, hi] using h.symm
      subst t
      exact ⟨σ, (reaches_jump hc.first hσ.one).mono (by lia), hσ⟩
    | branch c target =>
      have ht : t = ⟨if c.Holds s.data then target else s.pc + 1, s.data⟩ := by
        simpa [Next, WordRAM.step, hi] using h.symm
      subst t
      exact branch_simulation hc hσ hs
    | halt i => simp [Next, WordRAM.step, hi] at h

private theorem runs_simulation {p : Program .standard r} {q : RAM.Program} {base w n : ℕ}
    {s t : State r} {σ : URM.Regs}
    (hcode : ∀ pc i, p[pc]? = some i → BlockAt q base p.length pc i)
    (hp : p.IsAdditive) (hσ : Represents s.data σ) (hs : s.data.Bounded w)
    (h : Runs w p s t n) :
    ∃ τ, Reaches q ⟨entry base s.pc, σ⟩ ⟨entry base t.pc, τ⟩
      (n * (8 * (RAM.bitLength (memoryBase r) + w + 1))) ∧ Represents t.data τ := by
  induction h with
  | refl => exact ⟨σ, ⟨0, rfl, by simp⟩, hσ⟩
  | tail t u n hst htu ih =>
    obtain ⟨τ, hr, hτ⟩ := ih
    obtain ⟨υ, hr', hυ⟩ := next_simulation hcode hp hτ (Runs.bounded hst hs) htu
    exact ⟨υ, by simpa only [Nat.add_mul, Nat.one_mul] using hr.trans hr', hυ⟩

private theorem blockAt_append (pre : RAM.Program) {p : Program .standard r} {pc : ℕ}
    {i : Instr .standard r} (hi : p[pc]? = some i) :
    BlockAt (pre ++ compile pre.length p) pre.length p.length pc i := by
  intro k hk
  rw [List.getElem?_append_right (by dsimp [entry]; lia)]
  simpa only [entry, Nat.add_sub_cancel_left, Nat.add_assoc] using
    getElem?_compile (base := pre.length) hi hk

/-- Successful bounded-word execution is simulated by the compiled code, wherever it is
placed after `pre`. The initial target state represents the source state and starts at its
compiled instruction; execution of `pre` is not included in this statement. The final
output copy and jump past the end of the target program are included in the cost. -/
theorem executes_compile {p : Program .standard r} (hp : p.IsAdditive) (pre : RAM.Program)
    {w v n : ℕ} {s : State r} {σ : URM.Regs} (hσ : Represents s.data σ)
    (hs : s.data.Bounded w) (h : Executes w p s v n) :
    ∃ k, (RAM.run (pre ++ compile pre.length p) k ⟨entry pre.length s.pc, σ⟩).isHalted
        (pre ++ compile pre.length p) ∧
      (RAM.run (pre ++ compile pre.length p) k ⟨entry pre.length s.pc, σ⟩).regs.output = v ∧
      RAM.time RAM.logCost (pre ++ compile pre.length p) k ⟨entry pre.length s.pc, σ⟩ ≤
        n * (8 * (RAM.bitLength (memoryBase r) + w + 1)) := by
  obtain ⟨t, m, hr, ht, rfl⟩ := h
  have hc := fun pc i hi => blockAt_append (p := p) (pc := pc) (i := i) pre hi
  obtain ⟨τ, hrun, hτ⟩ := runs_simulation hc hp hσ hs hr
  cases hi : p[t.pc]? with
  | none => simp [WordRAM.step, hi] at ht
  | some i =>
    cases i with
    | halt i =>
      have hv : t.data.regs i = v := by simpa [WordRAM.step, hi] using ht
      obtain ⟨υ, hhalt, hυ⟩ := halt_simulation (hc t.pc (.halt i) hi) hτ (hr.bounded hs)
      obtain ⟨k, hk, hcost⟩ := hrun.trans hhalt
      refine ⟨k, ?_, ?_, ?_⟩
      · rw [hk]
        simp [RAM.State.isHalted, entry]
      · rw [hk, hυ, hv]
      · simpa only [Nat.add_mul, Nat.one_mul] using hcost
    | op o =>
      simp only [WordRAM.step, hi] at ht
      split at ht <;> cases ht
    | jump | branch => simp [WordRAM.step, hi] at ht

/-- The padded target input convention: zero working registers, followed by the source input
length and words. Installing this list is uncharged; the compiler's two initialization
instructions and all subsequent instructions are charged. -/
def paddedInput (r : ℕ) (input : List ℕ) : List ℕ :=
  List.replicate (memoryBase r) 0 ++ input.length :: input

/-- Initialize the two permanent compiler registers. -/
def prologue (r : ℕ) : RAM.Program := [.const (one r) 1, .const (offset r) (memoryBase r)]

/-- A complete compiled program using `paddedInput`. -/
def paddedProgram (p : Program .standard r) : RAM.Program := prologue r ++ compile 2 p

private theorem paddedInput_read_workspace (input : List ℕ) {a : ℕ} (ha : a < memoryBase r) :
    (URM.Regs.ofInputs (paddedInput r input)).read a = 0 := by
  dsimp only [URM.Regs.ofInputs, URM.Regs.read, paddedInput]
  rw [List.getD_append _ _ _ _ (by simpa using ha)]
  exact List.getD_replicate _ ha

private theorem paddedInput_read_memory (input : List ℕ) (a : ℕ) :
    (URM.Regs.ofInputs (paddedInput r input)).read (memoryBase r + a) =
      (Data.init input : Data r).mem a := by
  dsimp only [URM.Regs.ofInputs, URM.Regs.read, paddedInput]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left]
  cases a <;> rfl

private theorem represents_prologued (input : List ℕ) :
    Represents (Data.init input : Data r)
      (((URM.Regs.ofInputs (paddedInput r input)).write (one r) 1).write
        (offset r) (memoryBase r)) := by
  have read_other (a : ℕ) (h₁ : a ≠ one r) (h₂ : a ≠ offset r) :
      (((URM.Regs.ofInputs (paddedInput r input)).write (one r) 1).write
        (offset r) (memoryBase r)).read a =
          (URM.Regs.ofInputs (paddedInput r input)).read a := by
    rw [URM.Regs.write_read_of_ne _ _ _ _ h₂, URM.Regs.write_read_of_ne _ _ _ _ h₁]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [read_other _ (by dsimp [one]; lia) (by dsimp [offset]; lia)]
    exact paddedInput_read_workspace input (by dsimp [memoryBase]; lia)
  · rw [URM.Regs.write_read_of_ne _ _ _ _ (by dsimp [one, offset]; lia),
      URM.Regs.write_read_self]
  · exact URM.Regs.write_read_self _ _ _
  · intro i
    rw [read_other _ (by dsimp [one]; have := i.isLt; lia)
      (by dsimp [offset]; have := i.isLt; lia)]
    exact paddedInput_read_workspace input (by dsimp [memoryBase]; have := i.isLt; lia)
  · intro a
    rw [read_other _ (by dsimp [memoryBase, one]; lia) (by dsimp [memoryBase, offset]; lia)]
    exact paddedInput_read_memory input a

/-- Start the compiled simulation after an arbitrary already-executed prefix, from the
supplied padded register layout. The prefix itself is not charged by this theorem; the
two-instruction prologue, compiled source execution and final output are charged. This is
the composition interface for a separately certified input-preparation program. -/
theorem executes_compile_from_paddedInput {p : Program .standard r} (hp : p.IsAdditive)
    (pre : RAM.Program) {input : List ℕ} {w v n : ℕ} (hi : InputFits w input)
    (h : Executes w p (State.init input) v n) :
    let q := (pre ++ prologue r) ++ compile (pre.length + 2) p
    let s := RAM.State.mk pre.length (URM.Regs.ofInputs (paddedInput r input))
    ∃ k, (RAM.run q k s).isHalted q ∧ (RAM.run q k s).regs.output = v ∧
      RAM.time RAM.logCost q k s ≤
        8 * (RAM.bitLength (memoryBase r) + 1) * (n + 1) * (w + 1) := by
  let q := (pre ++ prologue r) ++ compile (pre.length + 2) p
  let σ := ((URM.Regs.ofInputs (paddedInput r input)).write (one r) 1).write
    (offset r) (memoryBase r)
  have h0 : q[pre.length]? = some (.const (one r) 1) := by
    dsimp only [q]
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp [prologue]
  have h1 : q[pre.length + 1]? = some (.const (offset r) (memoryBase r)) := by
    dsimp only [q]
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _)]
    simp [prologue]
  have hfirst := Reaches.step (p := q)
    (s := ⟨pre.length, URM.Regs.ofInputs (paddedInput r input)⟩) h0
  have hsecond := Reaches.step (p := q)
    (s := ⟨pre.length + 1, (URM.Regs.ofInputs (paddedInput r input)).write (one r) 1⟩) h1
  have hstart : Reaches q ⟨pre.length, URM.Regs.ofInputs (paddedInput r input)⟩ ⟨pre.length + 2, σ⟩
      (1 + RAM.bitLength (memoryBase r)) := by
    simpa [RAM.Instr.exec, RAM.logCost, RAM.bitLength, σ, Nat.add_assoc]
      using hfirst.trans hsecond
  have hc := executes_compile hp (pre ++ prologue r) (represents_prologued input)
    (Data.Bounded.init hi) h
  simp only [List.length_append, prologue, List.length_cons, List.length_nil] at hc
  obtain ⟨k, hk, hv, ht⟩ := hc
  change (RAM.run q k ⟨pre.length + 2, σ⟩).isHalted q at hk
  change (RAM.run q k ⟨pre.length + 2, σ⟩).regs.output = v at hv
  change RAM.time RAM.logCost q k ⟨pre.length + 2, σ⟩ ≤
    n * (8 * (RAM.bitLength (memoryBase r) + w + 1)) at ht
  obtain ⟨m, hm, hcost⟩ := hstart
  refine ⟨m + k, by rwa [RAM.run_add, hm], by rwa [RAM.run_add, hm], ?_⟩
  rw [RAM.time_add, hm]
  have hB : RAM.bitLength (memoryBase r) + w + 1 ≤
      (RAM.bitLength (memoryBase r) + 1) * (w + 1) := by nlinarith
  calc
    _ ≤ (n + 1) * (8 * (RAM.bitLength (memoryBase r) + w + 1)) := by
      have := Nat.add_le_add hcost ht
      nlinarith
    _ ≤ (n + 1) * (8 * ((RAM.bitLength (memoryBase r) + 1) * (w + 1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hB)
    _ = _ := by ring

/-- The padded-input logarithmic-cost simulation. The compiler and constant depend only on
the source program (in fact, the constant depends only on its number of named registers).
The input convention explicitly supplies the length and zero workspace; construction of
that convention is not a reduction certified by this theorem. -/
theorem haltsWithResultInTime_padded {p : Program .standard r} (hp : p.IsAdditive)
    {input : List ℕ} {w v n : ℕ} (hi : InputFits w input)
    (h : Executes w p (State.init input) v n) :
    RAM.HaltsWithResultInTime RAM.logCost (paddedProgram p) (paddedInput r input) v
      (8 * (RAM.bitLength (memoryBase r) + 1) * (n + 1) * (w + 1)) := by
  simpa [RAM.HaltsWithResultInTime, paddedProgram, RAM.State.init] using
    executes_compile_from_paddedInput hp [] hi h

/-- Compile a program over `Basis.additive` directly to `RAM.Program`. -/
def compileAdditive (base : ℕ) (p : Program .additive r) : RAM.Program :=
  compile base (p.mapOp Basis.additiveHomStandard)

/-- Compiling a `Basis.additive` program produces eight target instructions per source
instruction. -/
@[simp]
theorem length_compileAdditive (base : ℕ) (p : Program .additive r) :
    (compileAdditive base p).length = 8 * p.length := by
  simp [compileAdditive]

/-- Successful bounded-word execution of a program over `Basis.additive` is simulated by
`compileAdditive`, without a separate `IsAdditive` side condition. -/
theorem executes_compileAdditive {p : Program .additive r} (pre : RAM.Program)
    {w v n : ℕ} {s : State r} {σ : URM.Regs} (hσ : Represents s.data σ)
    (hs : s.data.Bounded w) (h : Executes w p s v n) :
    ∃ k, (RAM.run (pre ++ compileAdditive pre.length p) k ⟨entry pre.length s.pc, σ⟩).isHalted
        (pre ++ compileAdditive pre.length p) ∧
      (RAM.run (pre ++ compileAdditive pre.length p) k ⟨entry pre.length s.pc, σ⟩).regs.output = v ∧
      RAM.time RAM.logCost (pre ++ compileAdditive pre.length p) k ⟨entry pre.length s.pc, σ⟩ ≤
        n * (8 * (RAM.bitLength (memoryBase r) + w + 1)) :=
  executes_compile p.mapOp_additiveHomStandard_isAdditive pre hσ hs
    ((executes_mapOp_iff Basis.additiveHomStandard).mpr h)

/-- A complete compiled program over `Basis.additive` using `paddedInput`. -/
def paddedProgramAdditive (p : Program .additive r) : RAM.Program :=
  paddedProgram (p.mapOp Basis.additiveHomStandard)

/-- Start the compiled simulation of a `Basis.additive` program after an arbitrary
already-executed prefix, from the supplied padded register layout. -/
theorem executes_compile_from_paddedInput_additive {p : Program .additive r}
    (pre : RAM.Program) {input : List ℕ} {w v n : ℕ} (hi : InputFits w input)
    (h : Executes w p (State.init input) v n) :
    let q := (pre ++ prologue r) ++ compileAdditive (pre.length + 2) p
    let s := RAM.State.mk pre.length (URM.Regs.ofInputs (paddedInput r input))
    ∃ k, (RAM.run q k s).isHalted q ∧ (RAM.run q k s).regs.output = v ∧
      RAM.time RAM.logCost q k s ≤
        8 * (RAM.bitLength (memoryBase r) + 1) * (n + 1) * (w + 1) :=
  executes_compile_from_paddedInput p.mapOp_additiveHomStandard_isAdditive pre hi
    ((executes_mapOp_iff Basis.additiveHomStandard).mpr h)

/-- The padded-input logarithmic-cost simulation for programs over `Basis.additive`. -/
theorem haltsWithResultInTime_padded_additive {p : Program .additive r}
    {input : List ℕ} {w v n : ℕ} (hi : InputFits w input)
    (h : Executes w p (State.init input) v n) :
    RAM.HaltsWithResultInTime RAM.logCost (paddedProgramAdditive p) (paddedInput r input) v
      (8 * (RAM.bitLength (memoryBase r) + 1) * (n + 1) * (w + 1)) :=
  haltsWithResultInTime_padded p.mapOp_additiveHomStandard_isAdditive hi
    ((executes_mapOp_iff Basis.additiveHomStandard).mpr h)

end ToRAM
end Cslib.WordRAM

end
