/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Program

/-! Nonvacuous flat-program projections with uniform code and clock constants, for both
already installed arguments and an actually charged native list-input prefix. The former
includes width zero; the latter explicitly checks frontier overflow and the empty-input case. -/

namespace ComplexityTests.WordRAMRealizationProgram

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure

private def word : ℕ ↪ (Fin 1 → ℕ) :=
  ⟨fun d _ => d, fun _ _ h => congrFun h 0⟩

private theorem copy_realizes :
    Realizes .exact (fun d : ℕ => (pure d : Memory.Prog ℕ)) word word
      (fun _ _ _ => True) (fun _ _ => 0) := by
  refine ⟨0, 1, fun _ src tmp => .op (.copy (tmp 0) (src 0)), ?_⟩
  intro r frontier src tmp _ _ hf _
  refine ⟨by simp [Code.ReadsWidth, Op.ReadsWidth], ?_⟩
  intro w d x _ hin _ _
  have harg : x.regs (src 0) = d := congrFun hin 0
  refine ⟨x.set (tmp 0) d, ?_, ?_, ?_, ?_⟩
  · change ExecWithin _ _ _ _ 1
    simpa [harg] using
      (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := tmp 0) (s := src 0))
  · apply Memory.State.ext
    · rfl
    · exact Function.update_of_ne (hf 0).symm _ _
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change (x.set (tmp 0) d).regs (tmp 0) = d
    simp [Data.set]
  · intro i _ htmp
    exact Function.update_of_ne (htmp 0).symm _ _

private def entry (r d : ℕ) : Data r :=
  ⟨fun i => if i.val = 0 then d else 0, fun _ => 0⟩

-- The register count, program and exchange constant precede every width and argument.
example : ∃ (r C : ℕ) (p : Program .exact r),
    ∀ w d, Fits w d →
      ∃ t, Executes w p ⟨0, entry r d⟩ d t ∧ t ≤ C + 1 := by
  obtain ⟨n, C, emit, he⟩ := copy_realizes.exists_program
  let m := 1 + n + 1
  let r := m + 2
  let frontier : Fin r := ⟨1, by dsimp [r, m]; omega⟩
  let src : Fin 1 → Fin r := fun _ => ⟨0, by dsimp [r, m]; omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun j => ⟨j.val + 2, by dsimp [r, m]; omega⟩
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [tmp] at this
    omega
  have hd : ∀ i j, src i ≠ tmp j := by
    intro i j h
    have := congrArg Fin.val h
    change 0 = j.val + 2 at this
    omega
  have hf : ∀ j, tmp j ≠ frontier := by
    intro j h
    have := congrArg Fin.val h
    change j.val + 2 = 1 at this
    omega
  have hs : ∀ i, src i ≠ frontier := by
    intro i h
    have := congrArg Fin.val h
    change 0 = 1 at this
    omega
  refine ⟨r, C, (emit frontier src tmp).program (tmp (Fin.castAdd (n + 1) (0 : Fin 1))), ?_⟩
  intro w d hfit
  have hx : (entry r d).Bounded w := by
    constructor
    · intro i
      by_cases h : i.val = 0
      · change Fits w (if i.val = 0 then d else 0)
        rwa [ite_eq_left h]
      · change Fits w (if i.val = 0 then d else 0)
        rw [ite_eq_right h]
        exact fits_zero w
    · intro a
      exact fits_zero w
  have hin : (entry r d).regs ∘ src = word d := by
    funext i
    rfl
  obtain ⟨t, ht, htime⟩ := he frontier src tmp hi hd hf hs 0 w d (entry r d) hx hin
    trivial (by trivial)
  change t ≤ C * (0 + 0 + 1) + 1 at htime
  exact ⟨t, ht, by simpa using htime⟩

-- One fixed flat program now includes actual argument and frontier installation.
example : ∃ (r C : ℕ) (p : Program .exact r),
    ∀ w d, Fits w 2 → Fits w d →
      ∃ t, Executes w p (State.init [d]) d t ∧ t ≤ C + 1 := by
  obtain ⟨n, C, emit, he⟩ := copy_realizes.exists_init_program (fun d => [d]) (by
    intro d i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl)
  let m := 1 + n + 1
  let r := m + 2
  let frontier : Fin r := ⟨1, by dsimp [r, m]; omega⟩
  let src : Fin 1 → Fin r := fun _ => ⟨0, by dsimp [r, m]; omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun j => ⟨j.val + 2, by dsimp [r, m]; omega⟩
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [tmp] at this
    omega
  have hd : ∀ i j, src i ≠ tmp j := by
    intro i j h
    have := congrArg Fin.val h
    change 0 = j.val + 2 at this
    omega
  have hf : ∀ j, tmp j ≠ frontier := by
    intro j h
    have := congrArg Fin.val h
    change j.val + 2 = 1 at this
    omega
  have hs : ∀ i, src i ≠ frontier := by
    intro i h
    have := congrArg Fin.val h
    change 0 = 1 at this
    omega
  refine ⟨r, C, (Code.seq (inputPrefix frontier (tmp (Fin.last (1 + n))) src)
    (emit frontier src tmp)).program (tmp (Fin.castAdd (n + 1) (0 : Fin 1))), ?_⟩
  intro w d h2 hfit
  have hin : InputFits w [d] := by
    refine ⟨h2.of_le (by simp), ?_⟩
    intro v hv
    simp only [List.mem_singleton] at hv
    exact hv.symm ▸ hfit
  obtain ⟨t, ht, htime⟩ := he frontier src tmp (fun _ _ _ => Subsingleton.elim _ _) hi
    hd hf hs 0 w d (by simp) h2 hin trivial (by trivial)
  change t ≤ C * (0 + 0 + 1) + 1 at htime
  exact ⟨t, ht, by simpa using htime⟩

private def unitWords : Unit ↪ (Fin 0 → ℕ) :=
  (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

private def storeZero {r : ℕ} (src ptr : Fin r) : Code .exact r :=
  .seq (.op (.const ptr 0)) (.op (.store ptr src))

-- The client really writes a cell and returns Unit with zero output coordinates.
private theorem write_realizes :
    Realizes .exact (fun d : ℕ => Memory.write 0 d) word unitWords
      (fun _ _ _ => True) (fun _ _ => 0) := by
  refine ⟨0, 1, fun _ src tmp => storeZero (src 0) (tmp 0), ?_⟩
  intro r frontier src tmp _ hd hf _
  refine ⟨by simp [storeZero, Code.ReadsWidth, Op.ReadsWidth], ?_⟩
  intro w d x _ hin _ _
  have harg : x.regs (src 0) = d := congrFun hin 0
  let y := (x.set (tmp 0) 0).write 0 d
  refine ⟨y, ?_, ?_, (fun i => Fin.elim0 i), ?_⟩
  · have e₁ := ExecWithin.const (B := .exact) (x := x) (d := tmp 0) (fits_zero w)
    have e₂ := ExecWithin.store (B := .exact) (w := w) (x := x.set (tmp 0) 0)
      (a := tmp 0) (s := src 0)
    have hs : (x.set (tmp 0) 0).regs (src 0) = d := by
      simpa [hd 0 0] using harg
    rw [hs] at e₂
    change ExecWithin w (storeZero (src 0) (tmp 0)) x y (1 * (1 + 0 + 1))
    simpa [storeZero] using e₁.seq e₂
  · apply Memory.State.ext
    · rfl
    · exact Function.update_of_ne (hf 0).symm _ _
  · intro j _ htmp
    exact Function.update_of_ne (htmp 0).symm _ _

-- The flat Unit write starts at Data.init, not a preinstalled register environment.
example : ∃ (r C : ℕ) (p : Program .exact r),
    ∀ w d, Fits w 2 → Fits w d →
      ∃ t, Executes w p (State.init [d]) 0 t ∧ t ≤ C * 2 + 2 := by
  obtain ⟨n, C, emit, he⟩ := write_realizes.exists_init_unit_program (fun d => [d]) (by
    intro d i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl)
  let r := (0 + n + 1) + 2
  let frontier : Fin r := ⟨1, by dsimp [r]; omega⟩
  let src : Fin 1 → Fin r := fun _ => ⟨0, by dsimp [r]; omega⟩
  let tmp : Fin (0 + n + 1) → Fin r := fun j => ⟨j.val + 2, by dsimp [r]; omega⟩
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [tmp] at this
    omega
  have hd : ∀ i j, src i ≠ tmp j := by
    intro i j h
    have := congrArg Fin.val h
    change 0 = j.val + 2 at this
    omega
  have hf : ∀ j, tmp j ≠ frontier := by
    intro j h
    have := congrArg Fin.val h
    change j.val + 2 = 1 at this
    omega
  have hs : ∀ i, src i ≠ frontier := by
    intro i h
    have := congrArg Fin.val h
    change 0 = 1 at this
    omega
  refine ⟨r, C, (Code.seq (inputPrefix frontier (tmp (Fin.last (0 + n))) src)
    (.seq (emit frontier src tmp) (.op (.const (tmp 0) 0)))).program (tmp 0), ?_⟩
  intro w d h2 hfit
  have hin : InputFits w [d] := by
    refine ⟨h2.of_le (by simp), ?_⟩
    intro v hv
    simp only [List.mem_singleton] at hv
    exact hv.symm ▸ hfit
  have hv : (Memory.spec w).ValidHistory (inputState [d])
      ((Memory.spec w).clientHistory (inputState [d]) (Memory.write 0 d)) := by
    exact ⟨⟨by simp [inputState], hfit⟩, trivial⟩
  obtain ⟨t, ht, htime⟩ := he frontier src tmp (fun _ _ _ => Subsingleton.elim _ _) hi
    hd hf hs w d (by simp) h2 hin trivial hv
  change t ≤ C * (1 + 0 + 1) + 2 at htime
  exact ⟨t, ht, by simpa using htime⟩

-- The same Unit observation supports all widths, including zero, for a pure Unit client.
private theorem pure_unit_realizes :
    Realizes .exact (fun _ : Unit => (pure () : Memory.Prog Unit)) unitWords unitWords
      (fun _ _ _ => True) (fun _ _ => 0) := by
  refine ⟨0, 1, fun _ _ tmp => .op (.copy (tmp 0) (tmp 0)), ?_⟩
  intro r frontier src tmp _ _ _ _
  refine ⟨by simp [Code.ReadsWidth, Op.ReadsWidth], ?_⟩
  intro w d x _ _ _ _
  refine ⟨x, ?_, rfl, (fun i => Fin.elim0 i), fun _ _ _ => rfl⟩
  change ExecWithin w (.op (.copy (tmp 0) (tmp 0))) x x 1
  simpa [Data.set] using
    (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := tmp 0) (s := tmp 0))

example : ∃ (r C : ℕ) (p : Program .exact r),
    ∀ w, ∃ t, Executes w p (State.init []) 0 t ∧ t ≤ C + 2 := by
  obtain ⟨n, C, emit, he⟩ := pure_unit_realizes.exists_unit_program
  let r := (0 + n + 1) + 1
  let frontier : Fin r := ⟨0, by dsimp [r]; omega⟩
  let src : Fin 0 → Fin r := Fin.elim0
  let tmp : Fin (0 + n + 1) → Fin r := fun j => ⟨j.val + 1, by dsimp [r]; omega⟩
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [tmp] at this
    omega
  have hf : ∀ j, tmp j ≠ frontier := by
    intro j h
    have := congrArg Fin.val h
    change j.val + 1 = 0 at this
    omega
  refine ⟨r, C, (Code.seq (emit frontier src tmp) (.op (.const (tmp 0) 0))).program
    (tmp 0), ?_⟩
  intro w
  have hx : (Data.init [] : Data r).Bounded w :=
    Data.Bounded.init ⟨fits_zero w, by simp⟩
  obtain ⟨t, ht, htime⟩ := he frontier src tmp hi (fun i => Fin.elim0 i) hf
    (fun i => Fin.elim0 i) w () (Data.init []) hx (by funext i; exact Fin.elim0 i)
    trivial (by trivial)
  change t ≤ C * (0 + 0 + 1) + 2 at htime
  exact ⟨t, ht, by simpa [State.init] using htime⟩

-- The actual prefix, Unit store and scalar-observation instruction preserve the write.
example : ((Code.seq (inputPrefix (r := 4) 1 2 (fun _ : Fin 1 => 0))
    (.seq (storeZero 0 2) (.op (.const 2 0)))).eval 2 30 (Data.init [3])).map
    (fun z => (z.1.mem 0, z.1.regs 1, z.1.regs 2, z.2)) = some (3, 2, 0, 10) := by
  decide

-- The charged prefix really reads memory and installs the frontier before its body.
example : ((inputPrefix (r := 4) 1 2 (fun _ : Fin 1 => 0)).eval 2 20 (Data.init [3])).map
    (fun z => (z.1.regs 0, z.1.regs 1, z.2)) = some (3, 2, 7) := by
  decide

-- With no arguments the real empty-case copy still costs one instruction.
example : ((inputPrefix (r := 2) 0 1 (Fin.elim0 : Fin 0 → Fin 2)).eval 1 20
    (Data.init [])).map (fun z => (z.1.regs 0, z.2)) = some (1, 5) := by
  decide

-- A fitting input word alone is insufficient: the next free address must also fit.
example : (inputPrefix (r := 4) 1 2 (fun _ : Fin 1 => 0)).eval 1 20 (Data.init [1]) = none := by
  decide

-- The frontier cannot fit at width zero, even for empty input.
example : (inputPrefix (r := 2) 0 1 (Fin.elim0 : Fin 0 → Fin 2)).eval 0 20
    (Data.init []) = none := by
  decide

end ComplexityTests.WordRAMRealizationProgram
