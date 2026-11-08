/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured
import Complexity.Computability.WordRAM.SymbolicExec

/-!
# Native programs in a caller-owned memory window

`MemoryWindow.compile` translates standard native code to use a runtime memory base. Three
additional registers hold the base, the source word modulus and an address temporary. A load
executes an addition, a load and a remainder; a store executes an addition and a store. Other
instructions and all branch decisions retain the source register values.

`MemoryWindow.view` clips memory words to the source width. Consequently arbitrary dirty memory
in the caller's window is allowed: no bulk initialization or copying of that window is implicit
in the translation. The view is only a relation between ordinary native data, not a new machine
or execution semantics. Source executions must still be established using `WordRAM.Exec`.

This compiler is original native program work. It does not supply an algorithm, an execution
certificate or a bound for any source program.
-/

public section

namespace Cslib.WordRAM.MemoryWindow

variable {r : ℕ}

namespace Reg

/-- Runtime address of source memory cell zero. -/
@[expose] def base : Fin (r + 3) := ⟨r, by omega⟩

/-- Runtime value `2^w` for the source word width `w`. -/
@[expose] def modulus : Fin (r + 3) := ⟨r + 1, by omega⟩

/-- Temporary absolute address used by translated loads and stores. -/
@[expose] def address : Fin (r + 3) := ⟨r + 2, by omega⟩

end Reg

/-- One source instruction with actual address additions and load normalization. -/
@[expose] def compileOp : Op .standard r → Code .standard (r + 3)
  | .load d a =>
      .seq (.op (.bin .add Reg.address Reg.base (a.castAdd 3)))
        (.seq (.op (.load (d.castAdd 3) Reg.address))
          (.op (.bin .mod (d.castAdd 3) (d.castAdd 3) Reg.modulus)))
  | .store a s =>
      .seq (.op (.bin .add Reg.address Reg.base (a.castAdd 3)))
        (.op (.store Reg.address (s.castAdd 3)))
  | o => .op (o.rename (Fin.castAdd 3))

/-- Rebase all memory accesses, retaining ordinary native branching and loop control. -/
@[expose] def compile : Code .standard r → Code .standard (r + 3)
  | .op o => compileOp o
  | .seq a b => .seq (compile a) (compile b)
  | .branch c a b => .branch (c.rename (Fin.castAdd 3)) (compile a) (compile b)
  | .loop c a => .loop (c.rename (Fin.castAdd 3)) (compile a)
  | .rand d s => .rand (d.castAdd 3) (s.castAdd 3)

/-- Source data represented by a target register bank and clipped, shifted memory. -/
@[expose] def view (w b : ℕ) (x : Data (r + 3)) : Data r :=
  ⟨fun i => x.regs (i.castAdd 3), fun a => x.mem (b + a) % 2 ^ w⟩

/-- Ordinary value equalities relating source and target native data. -/
structure Matches (w b : ℕ) (x : Data r) (y : Data (r + 3)) : Prop where
  /-- The source register bank and clipped memory agree. -/
  view_eq : view w b y = x
  /-- The base register has the chosen runtime address. -/
  base_eq : y.regs Reg.base = b
  /-- The modulus register has the source word modulus. -/
  modulus_eq : y.regs Reg.modulus = 2 ^ w

/-- The compiler expands a flat instruction into at most three instructions. -/
theorem size_compileOp (o : Op .standard r) : (compileOp o).size ≤ 3 := by
  cases o <;> simp [compileOp]

/-- Branches and loop overhead also satisfy the factor-three code-size bound. -/
theorem size_compile (c : Code .standard r) : (compile c).size ≤ 3 * c.size := by
  induction c with
  | op o => exact size_compileOp o
  | seq a b ha hb | branch c a b ha hb => simp only [compile, Code.size]; omega
  | loop c a ha => simp only [compile, Code.size]; omega
  | rand => simp [compile]

/-- Memory rebasing introduces no reads of the physical word width. -/
theorem readsWidth_compileOp (o : Op .standard r) : (compileOp o).ReadsWidth ↔ o.ReadsWidth := by
  cases o <;> simp [compileOp, Code.ReadsWidth, Op.rename, Op.ReadsWidth, Op.bin]

/-- The compiled code reads the word width exactly when the source does. -/
theorem readsWidth_compile (c : Code .standard r) : (compile c).ReadsWidth ↔ c.ReadsWidth := by
  induction c <;> simp_all [compile, Code.ReadsWidth, readsWidth_compileOp]

private theorem view_set (w b : ℕ) (x : Data (r + 3)) (i : Fin r) (v : ℕ) :
    view w b (x.set (i.castAdd 3) v) = (view w b x).set i v := by
  ext j
  · change (x.set (i.castAdd 3) v).regs (j.castAdd 3) = ((view w b x).set i v).regs j
    by_cases h : j = i
    · subst j; wram_simp
    · wram_simp
      rfl
  · rfl

private theorem view_address (w b : ℕ) (x : Data (r + 3)) (v : ℕ) :
    view w b (x.set Reg.address v) = view w b x := by
  ext j
  · change (x.set Reg.address v).regs (j.castAdd 3) = x.regs (j.castAdd 3)
    wram_simp
  · rfl

private theorem view_write (w b : ℕ) (x : Data (r + 3)) (a v : ℕ) (hv : Fits w v) :
    view w b (x.write (b + a) v) = (view w b x).write a v := by
  ext j
  · rfl
  · change Function.update x.mem (b + a) v (b + j) % 2 ^ w =
      Function.update (fun k => x.mem (b + k) % 2 ^ w) a v j
    by_cases h : j = a
    · subst j; simp [Nat.mod_eq_of_lt hv]
    · have h' : b + j ≠ b + a := by omega
      simp [Function.update_of_ne h, Function.update_of_ne h']

/-- Matching source registers have their exact target-bank values. -/
theorem Matches.regs {w b : ℕ} {x : Data r} {y : Data (r + 3)}
    (h : Matches w b x y) (i : Fin r) : y.regs (i.castAdd 3) = x.regs i :=
  congrArg (fun z : Data r => z.regs i) h.view_eq

/-- Matching source memory has the clipped target word at its shifted address. -/
theorem Matches.mem {w b : ℕ} {x : Data r} {y : Data (r + 3)}
    (h : Matches w b x y) (a : ℕ) : y.mem (b + a) % 2 ^ w = x.mem a :=
  congrArg (fun z : Data r => z.mem a) h.view_eq

private theorem Matches.set {w b : ℕ} {x : Data r} {y : Data (r + 3)}
    (h : Matches w b x y) (i : Fin r) (v : ℕ) :
    Matches w b (x.set i v) (y.set (i.castAdd 3) v) := by
  exact ⟨by rw [view_set, h.view_eq], by wram_simp [h.base_eq], by wram_simp [h.modulus_eq]⟩

private theorem Matches.address {w b : ℕ} {x : Data r} {y : Data (r + 3)}
    (h : Matches w b x y) (v : ℕ) : Matches w b x (y.set Reg.address v) := by
  exact ⟨by rw [view_address, h.view_eq], by wram_simp [h.base_eq], by wram_simp [h.modulus_eq]⟩

private theorem Matches.write {w b : ℕ} {x : Data r} {y : Data (r + 3)}
    (h : Matches w b x y) (a v : ℕ) (hv : Fits w v) :
    Matches w b (x.write a v) (y.write (b + a) v) :=
  ⟨by rw [view_write _ _ _ _ _ hv, h.view_eq], h.base_eq, h.modulus_eq⟩

/-- A translated source instruction has actual native execution within three instructions.
All source addresses fit the bounded source word, so the only writes are inside the runtime
window. Dirty words are normalized by the translated load itself. -/
theorem exec_compileOp {w W b : ℕ} {o : Op .standard r} {x x' : Data r}
    {y : Data (r + 3)} (ho : ¬o.ReadsWidth) (he : o.eval w x = some x')
    (hx : x.Bounded w) (hxy : Matches w b x y) (hw : w ≤ W)
    (hfit : Fits W (b + 2 ^ w)) :
    ∃ y', ExecWithin W (compileOp o) y y' 3 ∧ Matches w b x' y' ∧
      ∀ a, a < b ∨ b + 2 ^ w ≤ a → y'.mem a = y.mem a := by
  cases o with
  | const d v =>
    obtain ⟨hv, rfl⟩ := Data.put_eq_some.1 he
    refine ⟨y.set (d.castAdd 3) v, (ExecWithin.const (hv.mono hw)).mono (by omega),
      hxy.set d v, fun _ _ => rfl⟩
  | copy d s =>
    simp only [Op.eval, Option.some.injEq] at he
    subst x'
    refine ⟨y.set (d.castAdd 3) (x.regs s), ?_, hxy.set d _, fun _ _ => rfl⟩
    simpa only [compileOp, Op.rename, hxy.regs s] using
      (ExecWithin.copy (w := W) (B := .standard) (d := d.castAdd 3)
        (s := s.castAdd 3) (x := y)).mono (by omega : 1 ≤ 3)
  | alu f d args =>
    obtain ⟨v, hf, hv, rfl⟩ := Op.eval_alu_eq_some.1 he
    have hargs : y.regs ∘ (Fin.castAdd 3 ∘ args) = x.regs ∘ args := by
      funext i
      exact hxy.regs (args i)
    have hf' := Basis.standard.interp_mono_of_not_readsWidth f ho hw hf hv
    refine ⟨y.set (d.castAdd 3) v, ?_, hxy.set d v, fun _ _ => rfl⟩
    exact (ExecWithin.alu (by rw [hargs]; exact hf') (hv.mono hw)).mono (by omega)
  | load d a =>
    simp only [Op.eval, Option.some.injEq] at he
    subst x'
    have ha : Fits W (b + x.regs a) := hfit.of_le (by have := hx.1 a; unfold Fits at this; omega)
    have hz : Matches w b x (y.set Reg.address (b + x.regs a)) := hxy.address _
    have hfm : Fits W (x.mem (x.regs a)) := (hx.2 (x.regs a)).mono hw
    unfold compileOp
    wram_exec [hxy.base_eq, hxy.regs, hxy.modulus_eq, hxy.mem, ha, hfm]
    refine ⟨?_, fun _ _ => rfl⟩
    rw [Data.set_set]
    exact hz.set d _
  | store a s =>
    simp only [Op.eval, Option.some.injEq] at he
    subst x'
    have ha : Fits W (b + x.regs a) := hfit.of_le (by have := hx.1 a; unfold Fits at this; omega)
    have hz : Matches w b x (y.set Reg.address (b + x.regs a)) := hxy.address _
    unfold compileOp
    wram_exec [hxy.base_eq, hxy.regs, ha]
    refine ⟨hz.write _ _ (hx.1 s), ?_⟩
    intro j hj
    have hja : j ≠ b + x.regs a := by
      have := hx.1 a
      unfold Fits at this
      omega
    exact Function.update_of_ne hja _ _

private theorem Matches.holds {w b : ℕ} {x : Data r} {y : Data (r + 3)}
    (h : Matches w b x y) (c : Cond r) : (c.rename (Fin.castAdd 3)).Holds y ↔ c.Holds x := by
  cases c <;> simp only [Cond.rename, Cond.Holds, h.regs]

/-- Clipped memory is source-word bounded whenever the represented register bank is bounded.
No condition is imposed on the unnormalized physical memory words. -/
theorem view_bounded (w b : ℕ) (y : Data (r + 3))
    (hregs : ∀ i : Fin r, Fits w (y.regs (i.castAdd 3))) : (view w b y).Bounded w :=
  ⟨hregs, fun _ => Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Every actual bounded deterministic source execution gives an actual target execution with
at most three times its charged instructions. The base and modulus survive, source registers
and clipped memory agree, and the entire caller memory outside the reserved window survives.
This is a compiler correctness rule over the existing native `Exec`, not an assumed execution
contract for an algorithm. -/
theorem exec {w W b : ℕ} {c : Code .standard r} {x x' : Data r} {n : ℕ}
    (he : Exec w c x x' n) (hc : ¬c.ReadsWidth) (hx : x.Bounded w)
    {y : Data (r + 3)} (hxy : Matches w b x y) (hw : w ≤ W)
    (hfit : Fits W (b + 2 ^ w)) :
    ∃ y', ExecWithin W (compile c) y y' (3 * n) ∧ Matches w b x' y' ∧
      ∀ a, a < b ∨ b + 2 ^ w ≤ a → y'.mem a = y.mem a := by
  induction he generalizing y with
  | op ho => exact exec_compileOp hc ho hx hxy hw hfit
  | seq h₁ h₂ ih₁ ih₂ =>
    obtain ⟨z, hz, hzm, hzf⟩ := ih₁ (fun h => hc (Or.inl h)) hx hxy
    obtain ⟨z', hz', hz'm, hz'f⟩ := ih₂ (fun h => hc (Or.inr h)) (h₁.bounded hx) hzm
    refine ⟨z', (hz.seq hz').mono (by omega), hz'm, ?_⟩
    intro a ha
    exact (hz'f a ha).trans (hzf a ha)
  | branch_pos hp h ih =>
    obtain ⟨z, hz, hzm, hzf⟩ := ih (fun h => hc (Or.inl h)) hx hxy
    refine ⟨z, ?_, hzm, hzf⟩
    exact (ExecWithin.branch_pos ((hxy.holds _).2 hp) hz).mono (by omega)
  | branch_neg hp h ih =>
    obtain ⟨z, hz, hzm, hzf⟩ := ih (fun h => hc (Or.inr h)) hx hxy
    refine ⟨z, ?_, hzm, hzf⟩
    exact (ExecWithin.branch_neg (fun h => hp ((hxy.holds _).1 h)) hz).mono (by omega)
  | loop_exit hp =>
    refine ⟨y, ?_, hxy, fun _ _ => rfl⟩
    exact (Exec.loop_exit (fun h => hp ((hxy.holds _).1 h))).within.mono (by omega)
  | loop_iter hp h₁ h₂ ih₁ ih₂ =>
    obtain ⟨z, hz, hzm, hzf⟩ := ih₁ hc hx hxy
    obtain ⟨z', hz', hz'm, hz'f⟩ := ih₂ hc (h₁.bounded hx) hzm
    refine ⟨z', ?_, hz'm, ?_⟩
    · exact (ExecWithin.loop_iter ((hxy.holds _).2 hp) hz hz').mono (by omega)
    · intro a ha
      exact (hz'f a ha).trans (hzf a ha)

/-- The bounded-time form of memory-window compiler correctness. -/
theorem execWithin {w W b T : ℕ} {c : Code .standard r} {x x' : Data r}
    (he : ExecWithin w c x x' T) (hc : ¬c.ReadsWidth) (hx : x.Bounded w)
    {y : Data (r + 3)} (hxy : Matches w b x y) (hw : w ≤ W)
    (hfit : Fits W (b + 2 ^ w)) :
    ∃ y', ExecWithin W (compile c) y y' (3 * T) ∧ Matches w b x' y' ∧
      ∀ a, a < b ∨ b + 2 ^ w ≤ a → y'.mem a = y.mem a := by
  obtain ⟨n, hn, he⟩ := he
  obtain ⟨z, hz, hzm, hzf⟩ := exec he hc hx hxy hw hfit
  exact ⟨z, hz.mono (by omega), hzm, hzf⟩

/-- Normalize a static list of source registers, retaining the runtime base and modulus. -/
@[expose] def normalizeBankList : List (Fin r) → Code .standard (r + 3)
  | [] => .op (.copy Reg.address Reg.address)
  | i :: is => .seq (.op (.bin .mod (i.castAdd 3) (i.castAdd 3) Reg.modulus))
      (normalizeBankList is)

/-- A fixed instruction sequence normalizing each source register once. The final self-copy
also makes the zero-register case an ordinary nonempty native program. -/
@[expose] def normalizeRegisters (r : ℕ) : Code .standard (r + 3) :=
  normalizeBankList (List.finRange r)

private theorem exec_normalizeBankList {w W : ℕ} (is : List (Fin r)) (x : Data (r + 3))
    (hm : x.regs Reg.modulus = 2 ^ w) (hw : w ≤ W) :
    ∃ y, ExecWithin W (normalizeBankList is) x y (is.length + 1) ∧ y.mem = x.mem ∧
      y.regs Reg.base = x.regs Reg.base ∧ y.regs Reg.modulus = 2 ^ w ∧
      (∀ j : Fin r, y.regs (j.castAdd 3) =
        if j ∈ is then x.regs (j.castAdd 3) % 2 ^ w else x.regs (j.castAdd 3)) := by
  induction is generalizing x with
  | nil =>
    exact ⟨x.set Reg.address (x.regs Reg.address), ExecWithin.copy, rfl, by wram_simp,
      by wram_simp [hm], fun j => by wram_simp [List.not_mem_nil]⟩
  | cons i is ih =>
    let z := x.set (i.castAdd 3) (x.regs (i.castAdd 3) % 2 ^ w)
    have hfit : Fits W (x.regs (i.castAdd 3) % 2 ^ w) :=
      (show Fits w (x.regs (i.castAdd 3) % 2 ^ w) from Nat.mod_lt _ (Nat.two_pow_pos _)).mono hw
    have h1 : ExecWithin W (.op (.bin .mod (i.castAdd 3) (i.castAdd 3) Reg.modulus)) x z 1 := by
      wram_exec [hm, hfit]
    obtain ⟨y, he, hmem, hbase, hmod, hregs⟩ := ih z (by wram_simp [z, hm])
    refine ⟨y, ?_, hmem, by wram_simp [hbase, z], hmod, fun j => ?_⟩
    · simpa only [normalizeBankList, List.length_cons, Nat.add_left_comm] using h1.seq he
    · rw [hregs]
      by_cases hji : j = i
      · subst j
        simp [z]
      · wram_simp [z, List.mem_cons, hji, false_or]

/-- Actual register normalization supplies a bounded source view without clearing any memory.
The base, modulus and every caller memory cell are preserved. -/
theorem exec_normalizeRegisters {w W b : ℕ} (x : Data (r + 3))
    (hb : x.regs Reg.base = b) (hm : x.regs Reg.modulus = 2 ^ w) (hw : w ≤ W) :
    ∃ y, ExecWithin W (normalizeRegisters r) x y (r + 1) ∧ y.mem = x.mem ∧
      Matches w b (view w b y) y ∧ (view w b y).Bounded w ∧
      ∀ j : Fin r, y.regs (j.castAdd 3) = x.regs (j.castAdd 3) % 2 ^ w := by
  obtain ⟨y, he, hmem, hbase, hmod, hregs⟩ := exec_normalizeBankList (List.finRange r) x hm hw
  have hr (j : Fin r) : y.regs (j.castAdd 3) = x.regs (j.castAdd 3) % 2 ^ w := by
    simpa only [List.mem_finRange, ↓reduceIte] using hregs j
  refine ⟨y, ?_, hmem, ⟨rfl, hbase.trans hb, hmod⟩, ?_, hr⟩
  · simpa only [normalizeRegisters, List.length_finRange] using he
  · exact view_bounded w b y (fun j => by rw [hr]; exact Nat.mod_lt _ (Nat.two_pow_pos _))

end Cslib.WordRAM.MemoryWindow
