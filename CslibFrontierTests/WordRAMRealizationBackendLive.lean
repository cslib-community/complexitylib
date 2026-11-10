/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (live-input Backend and register-frame regressions)

public import CslibFrontier.Computability.WordRAM.Realization.Backend
public import CslibFrontier.Computability.WordRAM.Realization.Client.MemoryStack
public import CslibFrontier.Tactic.Realize

/-!
# Already resident arguments and the common Backend register banks

The two tags have the same five-word input and different result widths, as the queue's count
and count/optional-answer methods do. These query-free fixtures check that native execution
still has its positive per-call allowance, starts from the actual live input, and preserves the
other registers and complete dirty memory. They add no queue dispatcher or initialization claim.
-/

public section

namespace Cslib.WordRAM.Realization.Tests.BackendLive

open Cslib.DataStructure

abbrev Input := Fin 5 → ℕ
abbrev counts : ℕ × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode
abbrev answer : (ℕ × ℕ) × Option ℕ ↪ (Fin 4 → ℕ) := WordEncoding.encode

private theorem pure_counts : Realizes .exact
    (fun d : Input => (pure (d 0, d 1) : Memory.Prog (ℕ × ℕ))) (.refl (Fin 5 → ℕ)) counts
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private theorem pure_answer : Realizes .exact
    (fun d : Input => (pure ((d 0, d 1), none) : Memory.Prog ((ℕ × ℕ) × Option ℕ)))
    (.refl (Fin 5 → ℕ)) answer (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- A fixed finite family; the second tag has a larger output bank. -/
noncomputable def certificates : Bool → Certificate .exact
  | false => Certificate.ofRealizes pure_counts
  | true => Certificate.ofRealizes pure_answer

-- Constructor tags use the same resident count/layout coordinates.
example (i : Fin 5) : Backend.src certificates false i = Backend.src certificates true i :=
  Backend.src_eq_of_val_eq certificates false true rfl

-- The dispatcher may consume the first two shared scratch words before the body reclaims them.
example (i : Fin 2) :
    Backend.tmp certificates false ⟨i.val, by
      change i.val < 2 + pure_counts.scratchSize + 1
      have := i.isLt
      omega⟩ =
      Backend.tmp certificates true ⟨i.val, by
        change i.val < 4 + pure_answer.scratchSize + 1
        have := i.isLt
        omega⟩ :=
  Backend.tmp_eq_of_val_eq certificates false true rfl

-- Materializing zero cannot overwrite the delivered constructor tag.
example : Backend.tmp certificates false ⟨0, by
      change 0 < 2 + pure_counts.scratchSize + 1
      omega⟩ ≠
    Backend.tmp certificates false ⟨1, by
      change 1 < 2 + pure_counts.scratchSize + 1
      omega⟩ := by
  intro h
  have h' := Backend.tmp_injective certificates false h
  have := congrArg Fin.val h'
  change 0 = 1 at this
  omega

example (i : Fin 5) (j : Fin (4 + pure_answer.scratchSize + 1)) :
    Backend.src certificates false i ≠ Backend.tmp certificates true j :=
  Backend.src_ne_tmp certificates false true i j

/-- One actual constructor-tag coordinate, shared with the other tag's scratch prefix. -/
noncomputable def tagSlot : Fin (Backend.registers certificates) :=
  Backend.tmp certificates false ⟨0, by
    change 0 < 2 + pure_counts.scratchSize + 1
    omega⟩

/-- A different shared coordinate used for the paid zero materialization. -/
noncomputable def zeroSlot : Fin (Backend.registers certificates) :=
  Backend.tmp certificates true ⟨1, by
    change 1 < 4 + pure_answer.scratchSize + 1
    omega⟩

private theorem tag_ne_zero : tagSlot ≠ zeroSlot := by
  have hz : zeroSlot = Backend.tmp certificates false ⟨1, by
      change 1 < 2 + pure_counts.scratchSize + 1
      omega⟩ := Backend.tmp_eq_of_val_eq certificates true false rfl
  intro h
  have h' := h.trans hz
  have hh := Backend.tmp_injective certificates false h'
  have := congrArg Fin.val hh
  change 0 = 1 at this
  omega

-- The real paid zero instruction retains the delivered tag, resident arguments and memory.
example {w : ℕ} {x : Data (Backend.registers certificates)} (hx : x.Bounded w) :
    ∃ y, Exec (B := .exact) w (.op (.const zeroSlot 0)) x y 1 ∧ y.Bounded w ∧
      y.regs tagSlot = x.regs tagSlot ∧
      (∀ j : Fin 5, y.regs (Backend.src certificates false j) =
        x.regs (Backend.src certificates false j)) ∧
      memoryState (Backend.frontier certificates) y =
        memoryState (Backend.frontier certificates) x := by
  let y := x.set zeroSlot 0
  have he : Exec (B := .exact) w (.op (.const zeroSlot 0)) x y 1 := Exec.const (fits_zero w)
  refine ⟨y, he, he.bounded hx, ?_, ?_, ?_⟩
  · exact Function.update_of_ne tag_ne_zero 0 x.regs
  · intro j
    change Function.update x.regs zeroSlot 0 _ = _
    apply Function.update_of_ne
    exact Backend.src_ne_tmp certificates false true j _
  · apply Memory.State.ext
    · exact Data.set_mem x zeroSlot 0
    · have hf : Backend.frontier certificates ≠ zeroSlot := by
        unfold zeroSlot
        exact (Backend.tmp_ne_frontier certificates true _).symm
      simpa only [memoryState, y, Data.set] using Function.update_of_ne hf 0 x.regs

-- The identity is conditional on the supplied words actually occupying the input bank.
example (x : Data (Backend.registers certificates)) (d : Input)
    (hin : x.regs ∘ Backend.src certificates false = d) :
    Backend.install certificates false d x = x :=
  Backend.install_eq_self certificates false d x hin

-- Raw data with different input words does not meet that entry condition.
example : ¬(fun _ : Fin 5 => 0) = (fun _ : Fin 5 => 1) := by
  intro h
  have := congrFun h 0
  omega

/-- The same fixed body runs at zero width and on maximum three-bit input words. Neither
query-free execution is assigned zero native charge; both use the common exchange factor. -/
theorem live_zero_and_max : ∃ r, ∃ code : Code .exact r, ∃ C, ∃ out : Fin 2 → Fin r,
    ∃ x₀ y₀ x₇ y₇ : Data r,
      x₀.Bounded 0 ∧ x₇.Bounded 3 ∧
      ExecWithin 0 code x₀ y₀ C ∧ (∀ j, y₀.regs (out j) = 0) ∧ y₀.mem = x₀.mem ∧
      ExecWithin 3 code x₇ y₇ C ∧ (∀ j, y₇.regs (out j) = 7) ∧ y₇.mem = x₇.mem := by
  let x₀ : Data (Backend.registers certificates) := ⟨fun _ => 0, fun _ => 0⟩
  let x₇ : Data (Backend.registers certificates) := ⟨fun _ => 7, fun _ => 7⟩
  let d₀ : Input := fun _ => 0
  let d₇ : Input := fun _ => 7
  have hx₀ : x₀.Bounded 0 := ⟨fun _ => fits_zero _, fun _ => fits_zero _⟩
  have hx₇ : x₇.Bounded 3 :=
    ⟨fun _ => by change Fits 3 7; decide, fun _ => by change Fits 3 7; decide⟩
  obtain ⟨y₀, n₀, he₀, hn₀, hm₀, ho₀, -, hf₀⟩ :=
    Backend.exists_exec_live certificates false d₀ hx₀ rfl trivial (by trivial)
  obtain ⟨y₇, n₇, he₇, hn₇, hm₇, ho₇, -, hf₇⟩ :=
    Backend.exists_exec_live certificates false d₇ hx₇ rfl trivial (by trivial)
  have hc₀ : memoryCost ((certificates false).prog d₀)
      (memoryState (Backend.frontier certificates) x₀) = 0 := rfl
  have hc₇ : memoryCost ((certificates false).prog d₇)
      (memoryState (Backend.frontier certificates) x₇) = 0 := rfl
  have hw₀ : (certificates false).work d₀
      (memoryState (Backend.frontier certificates) x₀) = 0 := rfl
  have hw₇ : (certificates false).work d₇
      (memoryState (Backend.frontier certificates) x₇) = 0 := rfl
  have hn₀' : n₀ ≤ Backend.factor certificates := by
    simpa only [hc₀, hw₀, Nat.zero_add, Nat.mul_one] using hn₀
  have hn₇' : n₇ ≤ Backend.factor certificates := by
    simpa only [hc₇, hw₇, Nat.zero_add, Nat.mul_one] using hn₇
  refine ⟨Backend.registers certificates, Backend.code certificates false,
    Backend.factor certificates,
    (fun j => Backend.tmp certificates false
      (Fin.castAdd ((certificates false).realizes.scratchSize + 1) j)),
    x₀, y₀, x₇, y₇, hx₀, hx₇, ⟨n₀, hn₀', he₀⟩, ?_,
    congrArg Memory.State.mem hm₀, ⟨n₇, hn₇', he₇⟩, ?_, congrArg Memory.State.mem hm₇⟩
  · intro j
    have h := ho₀ j
    change _ = counts (0, 0) j at h
    fin_cases j <;> exact h
  · intro j
    have h := ho₇ j
    change _ = counts (7, 7) j at h
    fin_cases j <;> exact h

-- The full frame recovers every live source coordinate, including resident layout words.
example {w : ℕ} (d : Input) {x : Data (Backend.registers certificates)} (hx : x.Bounded w)
    (hin : x.regs ∘ Backend.src certificates false = d) :
    ∃ y n, Exec w (Backend.code certificates false) x y n ∧
      (∀ j : Fin 5, y.regs (Backend.src certificates false j) =
        x.regs (Backend.src certificates false j)) := by
  obtain ⟨y, n, he, -, -, -, -, hf⟩ :=
    Backend.exists_exec_live certificates false d hx hin trivial (by trivial)
  refine ⟨y, n, he, fun j => hf _ (Backend.src_ne_frontier certificates false j) ?_⟩
  intro a
  exact (Backend.src_ne_tmp certificates false false j a).symm

-- The larger result retains the same frame; its absent answer is represented by two zero words.
example {w : ℕ} (d : Input) {x : Data (Backend.registers certificates)} (hx : x.Bounded w)
    (hin : x.regs ∘ Backend.src certificates true = d) :
    ∃ y n, Exec w (Backend.code certificates true) x y n ∧ y.mem = x.mem := by
  obtain ⟨y, n, he, -, hm, -, -, -⟩ :=
    Backend.exists_exec_live certificates true d hx hin trivial (by trivial)
  exact ⟨y, n, he, congrArg Memory.State.mem hm⟩

/-- A genuine memory-reading provider, as used by raw-entry layout/counter consumers. -/
noncomputable def sizeCertificate (_ : Unit) : Certificate .exact :=
  Certificate.ofRealizes MemoryStack.realizes_size

-- The live rule also runs a real query and retains all resident layout words.
example {w : ℕ} (L : Stack.Memory.Layout)
    {x : Data (Backend.registers sizeCertificate)} (hx : x.Bounded w)
    (hin : x.regs ∘ Backend.src sizeCertificate () = MemoryStack.layoutWords L)
    (haddr : L.count.base < x.regs (Backend.frontier sizeCertificate)) :
    ∃ y n, Exec w (Backend.code sizeCertificate ()) x y n ∧ y.mem = x.mem ∧
      ∀ j : Fin 4, y.regs (Backend.src sizeCertificate () j) =
        x.regs (Backend.src sizeCertificate () j) := by
  have hv : (Memory.spec w).ValidHistory (memoryState (Backend.frontier sizeCertificate) x)
      ((Memory.spec w).clientHistory (memoryState (Backend.frontier sizeCertificate) x)
        ((sizeCertificate ()).prog L)) := by
    exact ⟨haddr, trivial⟩
  obtain ⟨y, n, he, -, hm, -, -, hf⟩ :=
    Backend.exists_exec_live sizeCertificate () L hx hin trivial hv
  refine ⟨y, n, he, congrArg Memory.State.mem hm, fun j =>
    hf _ (Backend.src_ne_frontier sizeCertificate () j) ?_⟩
  intro a
  exact (Backend.src_ne_tmp sizeCertificate () () j a).symm

section Metadata

variable {B : Basis} {ι ι' : Type} [Fintype ι] [Fintype ι']
  {D : StateTransitionSpec.{0, 0, 0}} {C : ι → Certificate B}

-- Adding a fixed family preserves dependent method arguments, results and observations.
example (S : Backend D C) (extra : ι' → Certificate B) (o : D.Op)
    (a : (C (S.tag o)).Res) : (S.extend extra).answer o a = S.answer o a := rfl

-- This is the extended-bank bound pattern needed by the heap's actual bound_extend caller.
example {w : ℕ} (S : Backend D C) (extra : ι' → Certificate B)
    {R : Refinement D (Memory.spec w)} (hS : S.Implements R)
    {upper : D.State → D.Op → ℕ} (A : R.Amortized Memory.charge upper (fun _ => 0))
    (c : ℕ) (hw : ∀ {e} o, R.inv e → D.valid (R.abs e) o →
      (C (S.tag o)).work (S.arg o) e ≤ c) :
    Bound (Backend.implementation (hS.extend extra)) id
      (fun s o => Backend.factor (Sum.elim C extra) * (upper s o + c + 1)) :=
  Backend.bound (hS.extend extra) A c (fun o hi hv => hw o hi hv)

-- Preparation is the identity only when the selected method's actual words are live.
example (S : Backend D C) (o : D.Op) (x : Data (Backend.registers C))
    (hin : x.regs ∘ Backend.src C (S.tag o) = (C (S.tag o)).input (S.arg o)) :
    S.prepare o x = x :=
  Backend.install_eq_self C (S.tag o) (S.arg o) x hin

-- A real live-input body execution enters the existing operation relation with its decoder.
example (S : Backend D C) (w : ℕ) (o : D.Op) (a : D.Result o)
    (x y : Data (Backend.registers C)) (n : ℕ)
    (hin : x.regs ∘ Backend.src C (S.tag o) = (C (S.tag o)).input (S.arg o))
    (he : Exec w (Backend.code C (S.tag o)) x y n)
    (hout : ∃ b, a = S.answer o b ∧ ∀ j,
      y.regs (Backend.tmp C (S.tag o)
        (Fin.castAdd ((C (S.tag o)).realizes.scratchSize + 1) j)) =
          (C (S.tag o)).output b j) :
    S.exec w x o a y n := by
  have hp : S.prepare o x = x := Backend.install_eq_self C (S.tag o) (S.arg o) x hin
  exact (S.exec_iff w x y o a n).mpr ⟨by simpa only [hp] using he, hout⟩

end Metadata

end Cslib.WordRAM.Realization.Tests.BackendLive
