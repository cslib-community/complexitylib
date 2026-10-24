/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (based on edemaine/lean-trominoes @6d5b36c1)

public import Complexity.Computability.WordRAM.Notation

/-!
# Memory allocation and arrays on the word RAM

Algorithms on the word RAM keep their arrays in memory. This file provides, as ordinary
structured programs with exact instruction counts:

* `Cslib.WordRAM.zeroFill`: zeroing a range of cells, in `4 k + 2` instructions for `k` cells;
* `Cslib.WordRAM.alloc`: allocating a zeroed block of `k` cells at a *frontier* that only grows,
  in `4 k + 7` instructions. Addresses are never reused, so blocks allocated at different times
  are disjoint (`Cslib.WordRAM.Block.disjoint_of_le`); the frontier is the high-water mark of the
  memory used;
* `Cslib.WordRAM.readAt`, `Cslib.WordRAM.writeAt`: reading and writing the cell at a pointer plus
  an index, in two instructions each.

None of them adds an instruction to the machine: allocation is a loop of stores, and an indexed
access is an addition followed by a load or a store. The registers they use are parameters, and
`Cslib.WordRAM.Block.Realizes` relates the contents of a block to a function on its indices.

## Main definitions

* `Cslib.WordRAM.Block`, `Cslib.WordRAM.Block.Owns`, `Cslib.WordRAM.Block.read`,
  `Cslib.WordRAM.Block.Realizes`: a block of consecutive cells, address ownership, indexed read,
  and array realization.
* `Cslib.WordRAM.clear`: memory with a range of cells set to `0`.
* `Cslib.WordRAM.zeroFill`, `Cslib.WordRAM.alloc`, `Cslib.WordRAM.readAt`,
  `Cslib.WordRAM.writeAt`: the standard-basis programs.
* `Cslib.WordRAM.Op.addAdditive`, `Cslib.WordRAM.zeroFillAdditive`,
  `Cslib.WordRAM.allocAdditive`, `Cslib.WordRAM.readAtAdditive`,
  `Cslib.WordRAM.writeAtAdditive`: the additive-basis counterparts.

## Main results

* `Cslib.WordRAM.zeroFill_exec`, `Cslib.WordRAM.alloc_exec`, `Cslib.WordRAM.readAt_exec`,
  `Cslib.WordRAM.writeAt_exec`: their executions, with exact instruction counts.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; allocation by
  a frontier, the zeroing loop and indexed access are adapted from its accompanying Lean
  formalization.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {r : ℕ}

/-! ## Blocks of memory -/

/-- A block of `length` consecutive memory cells starting at address `base`. -/
@[ext]
structure Block where
  /-- The address of the first cell. -/
  base : ℕ
  /-- The number of cells. -/
  length : ℕ
  deriving DecidableEq, Repr

namespace Block

/-- The block contains the cell at address `a`. -/
def Owns (b : Block) (a : ℕ) : Prop := b.base ≤ a ∧ a < b.base + b.length

/-- The contents of the block's cells in memory `m`, indexed from `0`. -/
def read (b : Block) (m : ℕ → ℕ) (i : Fin b.length) : ℕ := m (b.base + i)

/-- The block holds the values `vs` in memory `m`. -/
def Realizes (b : Block) (m : ℕ → ℕ) (vs : Fin b.length → ℕ) : Prop := ∀ i, b.read m i = vs i

/-- A block below the frontier is disjoint from any block allocated at the frontier. -/
theorem disjoint_of_le {b : Block} {frontier k : ℕ} (hb : b.base + b.length ≤ frontier) {a : ℕ}
    (ha : b.Owns a) : ¬(Block.mk frontier k).Owns a := by
  simp only [Owns] at ha ⊢
  omega

/-- Writing a cell of the block updates the value at its index. -/
theorem Realizes.update {b : Block} {m : ℕ → ℕ} {vs : Fin b.length → ℕ} (h : b.Realizes m vs)
    (i : Fin b.length) (v : ℕ) :
    b.Realizes (Function.update m (b.base + i) v) (Function.update vs i v) := by
  intro j
  by_cases hji : j = i
  · subst hji
    simp [read]
  · have : b.base + j ≠ b.base + i := fun h => hji (Fin.ext (by omega))
    simpa [read, Function.update_of_ne this, Function.update_of_ne hji] using h j

/-- Writing a cell outside the block leaves its contents unchanged. -/
theorem Realizes.update_of_not_owns {b : Block} {m : ℕ → ℕ} {vs : Fin b.length → ℕ}
    (h : b.Realizes m vs) {a : ℕ} (ha : ¬b.Owns a) (v : ℕ) :
    b.Realizes (Function.update m a v) vs := by
  intro j
  have : b.base + j ≠ a := fun h => ha ⟨by omega, by omega⟩
  simpa [read, Function.update_of_ne this] using h j

end Block

/-- Memory `m` with the `k` cells from address `base` set to `0`. -/
def clear (m : ℕ → ℕ) (base k : ℕ) : ℕ → ℕ :=
  fun a => if base ≤ a ∧ a < base + k then 0 else m a

/-- Clearing `k` cells from `base` sets every cell in the block to `0`. -/
theorem clear_of_owns {m : ℕ → ℕ} {base k a : ℕ} (h : (Block.mk base k).Owns a) :
    clear m base k a = 0 := by
  simp [clear, show base ≤ a ∧ a < base + k from h]

/-- Clearing `k` cells from `base` leaves every cell outside the block unchanged. -/
theorem clear_of_not_owns {m : ℕ → ℕ} {base k a : ℕ} (h : ¬(Block.mk base k).Owns a) :
    clear m base k a = m a := by
  simp only [clear, ite_eq_right_iff]
  exact fun h' => absurd h' h

/-- Clearing zero cells leaves memory unchanged. -/
@[simp]
theorem clear_zero (m : ℕ → ℕ) (base : ℕ) : clear m base 0 = m := by
  funext a
  simp [clear]

private theorem clear_succ (m : ℕ → ℕ) (base k : ℕ) :
    clear m base (k + 1) = Function.update (clear m base k) (base + k) 0 := by
  funext a
  simp only [clear, Function.update_apply]
  split_ifs <;> omega

/-- A cleared block holds zeros. -/
theorem Block.realizes_clear (m : ℕ → ℕ) (base k : ℕ) :
    (Block.mk base k).Realizes (clear m base k) fun _ => 0 :=
  fun i => clear_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _⟩

/-! ## Zeroing a range of cells -/

/-- Zero the cells from the address in register `cur` up to the address in register `stop`,
counting `cur` up to `stop`; registers `zero` and `one` hold `0` and `1`. -/
def zeroFill (cur stop zero one : Fin r) : Code .standard r :=
  ram[ while cur < stop do [ *cur ← zero; cur ← cur + one ] ]

/-- Zeroing `k` cells takes `4 k + 2` instructions: a store, an addition, a branch and a jump per
cell, and a branch and a jump to leave the loop. -/
theorem zeroFill_exec {w : ℕ} {cur stop zero one : Fin r} {x : Data r} (hcs : cur ≠ stop)
    (hcz : cur ≠ zero) (hco : cur ≠ one) (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hle : x.regs cur ≤ x.regs stop) (hw : Fits w (x.regs stop)) :
    Exec w (zeroFill cur stop zero one) x
      ⟨Function.update x.regs cur (x.regs stop),
        clear x.mem (x.regs cur) (x.regs stop - x.regs cur)⟩
      (4 * (x.regs stop - x.regs cur) + 2) := by
  set b := x.regs cur with hb
  set k := x.regs stop - b
  let xs : ℕ → Data r := fun i => ⟨Function.update x.regs cur (b + i), clear x.mem b i⟩
  have hstop (i : ℕ) : (xs i).regs stop = x.regs stop := by
    simp [xs, Function.update_of_ne hcs.symm]
  have hcur (i : ℕ) : (xs i).regs cur = b + i := by simp [xs]
  have hbody (i : ℕ) (hi : i < k) :
      Exec w (ram[*cur ← zero; cur ← cur + one]) (xs i) (xs (i + 1)) 2 := by
    have hz : (xs i).regs zero = 0 := by simp [xs, Function.update_of_ne hcz.symm, h0]
    have ho : (xs i).regs one = 1 := by simp [xs, Function.update_of_ne hco.symm, h1]
    have e := Exec.store.seq (Exec.bin (f := .add) (d := cur) (i := cur) (j := one)
      (x := (xs i).write ((xs i).regs cur) ((xs i).regs zero))
      (by simpa [hcur, ho] using hw.of_le (by omega : b + i + 1 ≤ x.regs stop)))
    convert e using 1
    ext a
    · simp [xs, Function.update_of_ne hco.symm, h1, Nat.add_assoc]
    · simp [xs, Function.update_of_ne hcz.symm, h0, clear_succ]
  have h := Exec.loop (cond := .lt cur stop) xs k 2
    (fun i hi => by simp only [Cond.holds_lt, hcur, hstop]; omega)
    (by simp only [Cond.holds_lt, hcur, hstop]; omega) hbody
  have hx : xs 0 = x := by
    ext a
    · simp [xs, hb]
    · simp [xs]
  have hk : xs k = ⟨Function.update x.regs cur (x.regs stop), clear x.mem b k⟩ := by
    simp only [xs]
    congr 2
    omega
  rw [hx, hk, show k * (2 + 2) + 2 = 4 * k + 2 by omega] at h
  exact h

/-! ## Allocation -/

/-- Allocate a zeroed block of as many cells as register `count` holds, at the address in
register `frontier`: the address of the block is left in register `result`, and `frontier`
advances past the block. Registers `cur`, `zero` and `one` are scratch. -/
def alloc (frontier count result cur zero one : Fin r) : Code .standard r := ram[
  zero ← #0; one ← #1; result ← frontier; cur ← frontier; frontier ← frontier + count;
  ⟪zeroFill cur frontier zero one⟫ ]

/-- **Allocation.** Allocating a zeroed block of `k` cells at frontier `f` takes `4 k + 7`
instructions. It sets `result` to `f` and `frontier` and `cur` to `f + k`, `zero` and `one` to
`0` and `1`, zeroes the cells `f, …, f + k - 1`, and leaves all other registers and cells
unchanged. -/
theorem alloc_exec {w : ℕ} {frontier count result cur zero one : Fin r} {x : Data r}
    (hd : [frontier, count, result, cur, zero, one].Nodup) (h1 : Fits w 1)
    (hw : Fits w (x.regs frontier + x.regs count)) :
    Exec w (alloc frontier count result cur zero one) x
      ⟨Function.update (Function.update (Function.update (Function.update (Function.update
          x.regs zero 0) one 1) result (x.regs frontier)) frontier
            (x.regs frontier + x.regs count)) cur (x.regs frontier + x.regs count),
        clear x.mem (x.regs frontier) (x.regs count)⟩
      (4 * x.regs count + 7) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hfc, hfr, hfu, hfz, hfo⟩, ⟨hcr, hcu, hcz, hco⟩, ⟨hru, hrz, hro⟩, ⟨huz, huo⟩,
    hzo, -⟩ := hd
  set f := x.regs frontier
  set k := x.regs count
  -- The data after each of the five instructions before the zeroing loop.
  set x₁ := x.set zero 0
  set x₂ := x₁.set one 1
  set x₃ := x₂.set result f
  set x₄ := x₃.set cur f
  set x₅ := x₄.set frontier (f + k)
  have h₂f : x₂.regs frontier = f := by simp [x₂, x₁, hfo, hfz, f]
  have h₃f : x₃.regs frontier = f := by simp [x₃, hfr, h₂f]
  have h₄f : x₄.regs frontier = f := by simp [x₄, hfu, h₃f]
  have h₄k : x₄.regs count = k := by
    simp [x₄, x₃, x₂, x₁, hcu, hcr, hco, hcz, k]
  have h₅z : x₅.regs zero = 0 := by
    simp [x₅, x₄, x₃, x₂, x₁, Ne.symm hfz, Ne.symm huz, Ne.symm hrz, hzo]
  have h₅o : x₅.regs one = 1 := by
    simp [x₅, x₄, x₃, x₂, Ne.symm hfo, Ne.symm huo, Ne.symm hro]
  have h₅u : x₅.regs cur = f := by simp [x₅, x₄, Ne.symm hfu]
  have h₅f : x₅.regs frontier = f + k := by simp [x₅]
  have e₃ : Exec (B := .standard) w (.op (.copy result frontier)) x₂ x₃ 1 := by
    rw [show x₃ = x₂.set result (x₂.regs frontier) by rw [h₂f]]
    exact Exec.copy
  have e₄ : Exec (B := .standard) w (.op (.copy cur frontier)) x₃ x₄ 1 := by
    rw [show x₄ = x₃.set cur (x₃.regs frontier) by rw [h₃f]]
    exact Exec.copy
  have e₅ : Exec w (.op (.bin .add frontier frontier count)) x₄ x₅ 1 := by
    rw [show x₅ = x₄.set frontier (BinOp.add.eval (x₄.regs frontier) (x₄.regs count)) by
      rw [h₄f, h₄k]; rfl]
    exact Exec.bin (by simpa [h₄f, h₄k] using hw)
  have e := (Exec.const (w := w) (d := zero) (x := x) (fits_zero w)).seq <|
    (Exec.const (d := one) (x := x₁) h1).seq <| e₃.seq <| e₄.seq <| e₅.seq <|
    zeroFill_exec (w := w) (x := x₅) (stop := frontier) (Ne.symm hfu) huz huo h₅z h₅o
      (by omega) (by rwa [h₅f])
  unfold alloc
  convert e using 1
  · ext a
    · simp only [h₅f, x₅, x₄, x₃, x₂, x₁, Data.set_regs, Function.update_apply]
      split_ifs <;> simp_all
    · simp [h₅u, h₅f, x₅, x₄, x₃, x₂, x₁]
  · rw [h₅f, h₅u]
    omega

/-! ## Arrays -/

/-- `dst ← (ptr)[idx]`: load the cell at the address in `ptr` plus the index in `idx`, through the
scratch register `tmp`. -/
def readAt (tmp dst ptr idx : Fin r) : Code .standard r := ram[ tmp ← ptr + idx; dst ← *tmp ]

/-- `(ptr)[idx] ← src`: store register `src` to the cell at the address in `ptr` plus the index in
`idx`, through the scratch register `tmp`. -/
def writeAt (tmp ptr idx src : Fin r) : Code .standard r := ram[ tmp ← ptr + idx; *tmp ← src ]

/-- An indexed read takes two instructions. -/
theorem readAt_exec {w : ℕ} {tmp dst ptr idx : Fin r} {x : Data r}
    (h : Fits w (x.regs ptr + x.regs idx)) :
    Exec w (readAt tmp dst ptr idx) x
      ((x.set tmp (x.regs ptr + x.regs idx)).set dst (x.mem (x.regs ptr + x.regs idx))) 2 := by
  simpa [readAt] using (Exec.bin (f := .add) (d := tmp) h).seq (Exec.load (d := dst) (a := tmp))

/-- An indexed write takes two instructions; the stored register must differ from the scratch
register. -/
theorem writeAt_exec {w : ℕ} {tmp ptr idx src : Fin r} {x : Data r} (hs : src ≠ tmp)
    (h : Fits w (x.regs ptr + x.regs idx)) :
    Exec w (writeAt tmp ptr idx src) x
      ((x.set tmp (x.regs ptr + x.regs idx)).write (x.regs ptr + x.regs idx) (x.regs src)) 2 := by
  simpa [writeAt, Function.update_of_ne hs] using
    (Exec.bin (f := .add) (d := tmp) h).seq (Exec.store (a := tmp) (s := src))

/-! ## Additive-basis primitives -/

/-- `addAdditive d i j` sets register `d` to register `i` plus register `j` over
`Basis.additive`. -/
def Op.addAdditive (d i j : Fin r) : Op .additive r :=
  .alu ⟨.bin .add, by decide⟩ d ![i, j]

/-- Zero the cells from the address in register `cur` up to the address in register `stop` over
`Basis.additive`. -/
def zeroFillAdditive (cur stop zero one : Fin r) : Code .additive r :=
  .loop (.lt cur stop) (.seq (.op (.store cur zero)) (.op (.addAdditive cur cur one)))

/-- Allocate a zeroed block of `count` cells at `frontier` over `Basis.additive`. -/
def allocAdditive (frontier count result cur zero one : Fin r) : Code .additive r :=
  .seq (.op (.const zero 0)) <|
  .seq (.op (.const one 1)) <|
  .seq (.op (.copy result frontier)) <|
  .seq (.op (.copy cur frontier)) <|
  .seq (.op (.addAdditive frontier frontier count)) <|
  zeroFillAdditive cur frontier zero one

/-- `dst ← (ptr)[idx]` over `Basis.additive`. -/
def readAtAdditive (tmp dst ptr idx : Fin r) : Code .additive r :=
  .seq (.op (.addAdditive tmp ptr idx)) (.op (.load dst tmp))

/-- `(ptr)[idx] ← src` over `Basis.additive`. -/
def writeAtAdditive (tmp ptr idx src : Fin r) : Code .additive r :=
  .seq (.op (.addAdditive tmp ptr idx)) (.op (.store tmp src))

end Cslib.WordRAM

end
