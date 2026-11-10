/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.DataStructure.StateTransition.Refinement
public import CslibFrontier.DataStructure.StateTransition.Resource

/-!
# Native implementations of refinements, one realized body per operation constructor

`MemoryBackend` runs each memory operation as the static body of a primitive realization, chosen
by the operation's constructor. `Backend` does the same for any specification `D` refined to the
memory oracle by a `Refinement D (Memory.spec w)`. One supplied realization witness per
constructor tag supplies the body; the refinement supplies correctness and memory charges.

A `Certificate` bundles a `Realizes.Witness` with its program, encodings, domain and local work.
Resource and code projections retain those supplied data. `Certificate.ofRealizes` supports
existing existential clients using classical choice; it does not identify the chosen resources
with a particular realization derivation. A
family `C : ι → Certificate B` over a finite type of tags fixes one register file, one body per
tag and one exchange factor (`Backend.registers`, `Backend.code`, `Backend.factor`), before every
width, refinement, runtime layout and argument. A `Backend D C` says which tag each operation of
`D` selects (`tag`), which arguments the tag's program receives (`arg`, which may include the
structure's runtime layout), and how the program's result gives the specified answer (`answer`).
The result encoding belongs to the tag, so an operation's arguments are never encoded in its
result; the native code never dispatches on the operation.

`Backend.Implements` connects a backend to a refinement: each method runs the selected program
and maps its result by `answer`, and from an admissible state the arguments are words and the
program's domain holds. Then `Backend.implementation` is a `StateTransitionImpl D` with a
functional representation: the memory satisfies the refinement's invariant and abstracts to the
state, and every register and cell holds a word. Instruction counts follow from the refinement's
amortized memory charges (`Backend.amortized`), and are constant per operation when those charges
are constant and need no potential (`Backend.bound`). Backends of two specifications run their
product side by side (`Backend.sum`), with tags in a sum type: the operation's `Sum` constructor
selects the family, and no native code dispatches on it.

As in `MemoryBackend`, the selected tag's arguments are installed in registers before its body
runs, uncharged, as a calling convention; decoding the answer executes no instruction. Bounds
count the body's instructions only. The fields `arg` and `answer` are unrestricted: `arg` is any
function of the operation and `answer` any function of the operation and the program's result.
Nothing requires them to be computable or charges for evaluating them, and the answer need not be
held in a register: `Backend.exec` requires it to be `answer` applied to a result whose encoding
the result registers hold.

Memory charges do not depend on the word width (`totalCost_width`, `memoryCost_eq_totalCost`),
so `memoryCost`, which is taken at width zero, is the charge that refinements state at width `w`.

## Main definitions

* `Certificate`: a realization certificate with its program, encodings, domain and work.
* `Backend.registers`, `Backend.frontier`, `Backend.code`, `Backend.factor`: the register file,
  the body of each tag and one exchange factor.
* `Backend.data`: the native data holding a memory state.
* `Backend.install`: a tag's arguments installed in its argument registers.
* `Backend`: the tag, arguments and answer of each operation.
* `Backend.Implements`: a backend runs the methods of a refinement.
* `Backend.sum`: two backends side by side, for a product specification.
* `Backend.extend`: a backend with further tags, such as an allocation's.
* `Backend.exec`, `Backend.implementation`: native execution, and the native implementation.

## Main results

* `totalCost_width`, `clientHistory_width`, `memoryCost_eq_totalCost`: memory charges do not
  depend on the word width.
* `fits_appendWords`: appended argument words fit when both parts do.
* `Backend.exists_exec`: the body of one tag runs its program on installed arguments.
* `Backend.exists_exec_frame`, `Backend.exists_exec_live`: retain the register frame and run
  directly from arguments already live in the source bank.
* `Backend.install_eq_self`: installation is the identity on actual live arguments.
* `Backend.Implements.prod`: side-by-side backends run a product of refinements.
* `Backend.exec_iff`, `Backend.rep_iff`: the execution relation and representation, unfolded.
* `Backend.rep_data`: the data holding an invariant state represents its abstraction.
* `Backend.exec_memoryState`: an operation leaves its method's final memory.
* `Backend.amortized`, `Backend.bound`: amortized and worst-case instruction bounds.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-! ## Memory charges and the word width -/

/-- Memory charges along a history do not depend on the word width. -/
theorem totalCost_width (w : ℕ) (s : Memory.State) (os : List Memory.Op) :
    (Memory.spec w).totalCost Memory.charge s os =
      (Memory.spec 0).totalCost Memory.charge s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact congrArg (Memory.charge s o + ·) (ih _)

/-- The memory history of a client does not depend on the word width. -/
theorem clientHistory_width {α : Type} (w : ℕ) (p : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).clientHistory s p = (Memory.spec 0).clientHistory s p :=
  congrArg (fun t => t.2.2) (runClient_width w p s)

/-- `memoryCost` is the memory charge of the client's history at every word width. -/
theorem memoryCost_eq_totalCost {α : Type} (w : ℕ) (p : Memory.Prog α) (s : Memory.State) :
    memoryCost p s =
      (Memory.spec w).totalCost Memory.charge s ((Memory.spec w).clientHistory s p) := by
  rw [totalCost_width, clientHistory_width]
  rfl

/-- Appended argument words fit when both parts do. -/
theorem fits_appendWords {δ α : Type} {k l w : ℕ} (input : δ ↪ (Fin k → ℕ))
    (output : α ↪ (Fin l → ℕ)) {d : δ} {a : α} (h₁ : ∀ i, Fits w (input d i))
    (h₂ : ∀ i, Fits w (output a i)) : ∀ i, Fits w (appendWords input output (d, a) i) :=
  Fin.addCases (fun i => by simpa [appendWords, Fin.appendEquiv] using h₁ i)
    (fun i => by simpa [appendWords, Fin.appendEquiv] using h₂ i)

/-! ## Certificates and backends -/

/-- A uniform realization certificate, bundled with the program it realizes, its argument and
result encodings, its entry domain and its local work. -/
structure Certificate (B : Basis) where
  /-- The argument type. -/
  {Arg : Type}
  /-- The result type. -/
  {Res : Type}
  /-- The number of argument words. -/
  {k : ℕ}
  /-- The number of result words. -/
  {l : ℕ}
  /-- The realized memory program. -/
  {prog : Arg → Memory.Prog Res}
  /-- The faithful argument encoding. -/
  {input : Arg ↪ (Fin k → ℕ)}
  /-- The faithful result encoding. -/
  {output : Res ↪ (Fin l → ℕ)}
  /-- The entry domain. -/
  {safe : ℕ → Arg → Memory.State → Prop}
  /-- The certified local work. -/
  {work : Arg → Memory.State → ℕ}
  /-- The supplied witness. Resource and code projections retain these data directly. -/
  realizes : Realizes.Witness B prog input output safe work

/-- Package an existential realization using its classically selected witness. This fallback
retains correctness, but supplies no concrete bounds on its selected scratch or factor. -/
noncomputable abbrev Certificate.ofRealizes {B : Basis} {δ α : Type} {k l : ℕ}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}
    (h : Realizes B p input output safe work) : Certificate B :=
  ⟨Realizes.Witness.ofRealizes h⟩

variable {B : Basis} {ι : Type}

/-- How the operations of `D` run on the bodies of `C`: each operation selects a tag, passes
arguments to the tag's program and reads its answer from that program's result. Only the tag
selects code. The maps `arg` and `answer` are unrestricted: they need not be computable, and
evaluating them is not charged. -/
structure Backend (D : StateTransitionSpec.{0, 0, 0}) (C : ι → Certificate B) where
  /-- The tag of each operation, typically its constructor. -/
  tag : D.Op → ι
  /-- The arguments of the selected program, including any runtime layout. -/
  arg : ∀ o, (C (tag o)).Arg
  /-- The specified answer, read off the selected program's result. -/
  answer : ∀ o, (C (tag o)).Res → D.Result o

namespace Backend

section Registers

variable [Fintype ι] (C : ι → Certificate B)

/-- Registers for the longest argument vector. -/
@[expose] noncomputable def argWords : ℕ := Finset.univ.sup fun i => (C i).k

/-- Registers for the largest result and scratch bank. -/
@[expose] noncomputable def scratchWords : ℕ :=
  Finset.univ.sup fun i => (C i).l + (C i).realizes.scratchSize + 1

/-- One register count, chosen before every width, refinement, layout and argument. -/
@[expose] noncomputable def registers : ℕ := argWords C + scratchWords C + 1

/-- Register zero holds the allocation frontier. -/
@[expose] def frontier : Fin (registers C) := ⟨0, by unfold registers; omega⟩

/-- The argument registers of tag `i`, from register one. -/
@[expose] def src (i : ι) (j : Fin (C i).k) : Fin (registers C) :=
  ⟨j.val + 1, by
    have := Finset.le_sup (f := fun i => (C i).k) (Finset.mem_univ i)
    have := j.isLt
    unfold registers argWords at *
    omega⟩

/-- The result and scratch registers of tag `i`, after all argument registers. -/
@[expose] noncomputable def tmp (i : ι) (j : Fin ((C i).l + (C i).realizes.scratchSize + 1)) :
    Fin (registers C) :=
  ⟨argWords C + 1 + j.val, by
    have := Finset.le_sup (f := fun i => (C i).l + (C i).realizes.scratchSize + 1)
      (Finset.mem_univ i)
    have := j.isLt
    unfold registers scratchWords at *
    omega⟩

/-- Distinct argument coordinates use distinct source registers. -/
theorem src_injective (i : ι) : Function.Injective (src C i) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [src] at this
  omega

/-- Distinct result/scratch coordinates use distinct registers. -/
theorem tmp_injective (i : ι) : Function.Injective (tmp C i) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [tmp] at this
  omega

/-- Source coordinates at the same position agree across tags. -/
theorem src_eq_of_val_eq (i i' : ι) {a : Fin (C i).k} {b : Fin (C i').k}
    (h : a.val = b.val) : src C i a = src C i' b := by
  apply Fin.ext
  simp only [src, h]

/-- Result/scratch coordinates at the same position agree across tags. -/
theorem tmp_eq_of_val_eq (i i' : ι)
    {a : Fin ((C i).l + (C i).realizes.scratchSize + 1)}
    {b : Fin ((C i').l + (C i').realizes.scratchSize + 1)}
    (h : a.val = b.val) : tmp C i a = tmp C i' b := by
  apply Fin.ext
  simp only [tmp, h]

/-- No tag's argument register is used by any tag's result/scratch bank. -/
theorem src_ne_tmp (i i' : ι) (a : Fin (C i).k)
    (b : Fin ((C i').l + (C i').realizes.scratchSize + 1)) : src C i a ≠ tmp C i' b := by
  intro h
  have hk := Finset.le_sup (f := fun i => (C i).k) (Finset.mem_univ i)
  have ha := a.isLt
  have := congrArg Fin.val h
  simp only [src, tmp, argWords] at this
  omega

/-- Argument installation never uses the frontier register. -/
theorem src_ne_frontier (i : ι) (a : Fin (C i).k) : src C i a ≠ frontier C := by
  intro h
  have := congrArg Fin.val h
  simp only [src, frontier] at this
  omega

/-- Native result/scratch writes never use the frontier register. -/
theorem tmp_ne_frontier (i : ι) (a : Fin ((C i).l + (C i).realizes.scratchSize + 1)) :
    tmp C i a ≠ frontier C := by
  intro h
  have := congrArg Fin.val h
  simp only [tmp, frontier] at this
  omega

/-- The static body of tag `i`. -/
@[expose] noncomputable def code (i : ι) : Code B (registers C) :=
  (C i).realizes.code (frontier C) (src C i) (tmp C i)

/-- One exchange factor for every tag. -/
@[expose] noncomputable def factor : ℕ := Finset.univ.sup fun i => (C i).realizes.factor

/-- Each tag's exchange factor is at most the common one. -/
theorem factor_le (i : ι) : (C i).realizes.factor ≤ factor C :=
  Finset.le_sup (f := fun i => (C i).realizes.factor) (Finset.mem_univ i)

/-- The native data holding the memory state `s`: its cells, the frontier in its register, and
zero in every other register. A calling-convention state, not an allocation. -/
noncomputable def data (s : Memory.State) : Data (registers C) where
  regs i := if i = frontier C then s.frontier else 0
  mem := s.mem

/-- The data holding `s` abstracts to `s`. -/
@[simp] theorem memoryState_data (s : Memory.State) : memoryState (frontier C) (data C s) = s :=
  Memory.State.ext rfl (by simp [memoryState, data])

/-- The data holding a well-formed memory state is word-bounded. -/
theorem bounded_data {w : ℕ} {s : Memory.State} (hs : Memory.WellFormed w s) :
    (data C s).Bounded w := by
  refine ⟨fun i => ?_, hs.mem_fits⟩
  simp only [data]
  split
  · exact hs.frontier_fits
  · exact fits_zero w

private theorem layout (i : ι) :
    Function.Injective (tmp C i) ∧ (∀ a b, src C i a ≠ tmp C i b) ∧
      (∀ b, tmp C i b ≠ frontier C) ∧ ∀ a, src C i a ≠ frontier C := by
  have hk := Finset.le_sup (f := fun i => (C i).k) (Finset.mem_univ i)
  refine ⟨fun a b h => Fin.ext ?_, fun a b h => ?_, fun b h => ?_, fun a h => ?_⟩ <;>
    have := congrArg Fin.val h <;> simp only [src, tmp, frontier, argWords] at * <;> omega

/-- Install arguments `d` of tag `i` in its argument registers. Installation is uncharged and
leaves memory and the frontier unchanged. -/
def install (i : ι) (d : (C i).Arg) (x : Data (registers C)) : Data (registers C) where
  regs j := if h : 0 < j.val ∧ j.val ≤ (C i).k then (C i).input d ⟨j.val - 1, by omega⟩
    else x.regs j
  mem := x.mem

/-- Installation leaves the memory and the frontier. -/
@[simp] theorem memoryState_install (i : ι) (d : (C i).Arg) (x : Data (registers C)) :
    memoryState (frontier C) (install C i d x) = memoryState (frontier C) x := by
  apply Memory.State.ext rfl
  simp [memoryState, install, frontier]

/-- Installed arguments occupy the selected tag's actual source registers. -/
theorem install_src (i : ι) (d : (C i).Arg) (x : Data (registers C)) :
    (install C i d x).regs ∘ src C i = (C i).input d := by
  funext j
  simp [install, src]

/-- Installing arguments already present in their source registers changes nothing.
This identity requires actual live words; it supplies no native argument-staging code. -/
theorem install_eq_self (i : ι) (d : (C i).Arg) (x : Data (registers C))
    (hin : x.regs ∘ src C i = (C i).input d) : install C i d x = x := by
  apply Data.ext
  · funext j
    by_cases hj : 0 < j.val ∧ j.val ≤ (C i).k
    · let a : Fin (C i).k := ⟨j.val - 1, by omega⟩
      have hsrc : src C i a = j := by
        apply Fin.ext
        simp only [src, a]
        omega
      change (if h : 0 < j.val ∧ j.val ≤ (C i).k then
        (C i).input d ⟨j.val - 1, by omega⟩ else x.regs j) = _
      rw [dite_eq_left hj]
      have h := congrFun hin a
      change x.regs (src C i a) = (C i).input d a at h
      exact h.symm.trans (congrArg x.regs hsrc)
    · change (if h : 0 < j.val ∧ j.val ≤ (C i).k then
        (C i).input d ⟨j.val - 1, by omega⟩ else x.regs j) = _
      rw [dite_eq_right hj]
  · rfl

/-- Installing fitted argument words preserves bounded data. -/
theorem install_bounded {w : ℕ} (i : ι) (d : (C i).Arg) {x : Data (registers C)}
    (hx : x.Bounded w) (hin : ∀ j, Fits w ((C i).input d j)) : (install C i d x).Bounded w := by
  refine ⟨fun j => ?_, hx.2⟩
  simp only [install]
  split
  · exact hin _
  · exact hx.1 j

/-- The selected body's complete execution guarantee, including its register frame.
Only the frontier and its result/scratch bank may change relative to installed arguments. -/
theorem exists_exec_frame {w : ℕ} (i : ι) (d : (C i).Arg) {x : Data (registers C)}
    (hx : x.Bounded w)
    (hin : ∀ j, Fits w ((C i).input d j)) (hsafe : (C i).safe w d (memoryState (frontier C) x))
    (hv : (Memory.spec w).ValidHistory (memoryState (frontier C) x)
      ((Memory.spec w).clientHistory (memoryState (frontier C) x) ((C i).prog d))) :
    ∃ y n, Exec w (code C i) (install C i d x) y n ∧
      n ≤ factor C * (memoryCost ((C i).prog d) (memoryState (frontier C) x) +
        (C i).work d (memoryState (frontier C) x) + 1) ∧
      memoryState (frontier C) y =
        (Memory.spec w).clientState (memoryState (frontier C) x) ((C i).prog d) ∧
      (∀ j, y.regs (tmp C i (Fin.castAdd ((C i).realizes.scratchSize + 1) j)) =
        (C i).output ((Memory.spec w).clientResult (memoryState (frontier C) x) ((C i).prog d))
          j) ∧
      y.Bounded w ∧
      ∀ j, j ≠ frontier C → (∀ a, tmp C i a ≠ j) →
        y.regs j = (install C i d x).regs j := by
  have hb := install_bounded C i d hx hin
  have hm := memoryState_install C i d x
  obtain ⟨hi', hd, hf, hs⟩ := layout C i
  obtain ⟨y, ⟨n, hn, he⟩, hm', hout, hframe⟩ :=
    ((C i).realizes.code_spec (frontier C) (src C i) (tmp C i) hi' hd hf hs).2 w d _ hb
      (install_src C i d x) (hm ▸ hsafe) (hm ▸ hv)
  rw [hm] at hn hm' hout
  exact ⟨y, n, he, hn.trans (Nat.mul_le_mul_right _ (factor_le C i)), hm', hout,
    he.bounded hb, hframe⟩

/-- **The body of one tag.** From bounded data, with arguments that fit words, inside the tag's
domain and with an admissible memory history, the body of tag `i` runs its program on the
installed arguments within the certified bound at the common exchange factor. It leaves the
program's final memory and encoded result, and every register and cell a word. -/
theorem exists_exec {w : ℕ} (i : ι) (d : (C i).Arg) {x : Data (registers C)} (hx : x.Bounded w)
    (hin : ∀ j, Fits w ((C i).input d j)) (hsafe : (C i).safe w d (memoryState (frontier C) x))
    (hv : (Memory.spec w).ValidHistory (memoryState (frontier C) x)
      ((Memory.spec w).clientHistory (memoryState (frontier C) x) ((C i).prog d))) :
    ∃ y n, Exec w (code C i) (install C i d x) y n ∧
      n ≤ factor C * (memoryCost ((C i).prog d) (memoryState (frontier C) x) +
        (C i).work d (memoryState (frontier C) x) + 1) ∧
      memoryState (frontier C) y =
        (Memory.spec w).clientState (memoryState (frontier C) x) ((C i).prog d) ∧
      (∀ j, y.regs (tmp C i (Fin.castAdd ((C i).realizes.scratchSize + 1) j)) =
        (C i).output ((Memory.spec w).clientResult (memoryState (frontier C) x) ((C i).prog d))
          j) ∧
      y.Bounded w := by
  obtain ⟨y, n, he, hn, hm, hout, hb, -⟩ := exists_exec_frame C i d hx hin hsafe hv
  exact ⟨y, n, he, hn, hm, hout, hb⟩

/-- Run the same fixed body directly from bounded data whose input words are already live.
No installation or loader is executed. Safety and valid history remain explicit, and the
register frame is relative to the actual initial data. -/
theorem exists_exec_live {w : ℕ} (i : ι) (d : (C i).Arg) {x : Data (registers C)} (hx : x.Bounded w)
    (hin : x.regs ∘ src C i = (C i).input d) (hsafe : (C i).safe w d (memoryState (frontier C) x))
    (hv : (Memory.spec w).ValidHistory (memoryState (frontier C) x)
      ((Memory.spec w).clientHistory (memoryState (frontier C) x) ((C i).prog d))) :
    ∃ y n, Exec w (code C i) x y n ∧
      n ≤ factor C * (memoryCost ((C i).prog d) (memoryState (frontier C) x) +
        (C i).work d (memoryState (frontier C) x) + 1) ∧
      memoryState (frontier C) y =
        (Memory.spec w).clientState (memoryState (frontier C) x) ((C i).prog d) ∧
      (∀ j, y.regs (tmp C i (Fin.castAdd ((C i).realizes.scratchSize + 1) j)) =
        (C i).output ((Memory.spec w).clientResult (memoryState (frontier C) x) ((C i).prog d))
          j) ∧
      y.Bounded w ∧
      ∀ j, j ≠ frontier C → (∀ a, tmp C i a ≠ j) →
        y.regs j = x.regs j := by
  have hfit j : Fits w ((C i).input d j) := congrFun hin j ▸ hx.1 (src C i j)
  simpa only [install_eq_self C i d x hin] using
    exists_exec_frame C i d hx hfit hsafe hv

end Registers

variable {C : ι → Certificate B} {D : StateTransitionSpec.{0, 0, 0}} (S : Backend D C)

/-- A backend runs the methods of `R`: each method is the selected program with its result
mapped by `answer`, and from an admissible state the arguments are words and the program's
domain holds. -/
structure Implements {w : ℕ} (R : Refinement D (Memory.spec w)) : Prop where
  /-- Each method runs the selected program and answers through `answer`. -/
  run : ∀ o s, (Memory.spec w).runClient s (R.methods o) =
    Prod.map (S.answer o) id ((Memory.spec w).runClient s ((C (S.tag o)).prog (S.arg o)))
  /-- From an admissible state, the arguments fit words and the program's domain holds. -/
  entry : ∀ {e} o, Memory.WellFormed w e → R.inv e → D.valid (R.abs e) o →
    (∀ j, Fits w ((C (S.tag o)).input (S.arg o) j)) ∧ (C (S.tag o)).safe w (S.arg o) e

/-! ### Products -/

section Sum

variable {ι' : Type} {C' : ι' → Certificate B} {D' : StateTransitionSpec.{0, 0, 0}}

/-- Two backends side by side run the product specification: a left operation selects a left
tag and a right operation a right tag. -/
def sum (S' : Backend D' C') : Backend (product D D') (Sum.elim C C') where
  tag := Sum.map S.tag S'.tag
  arg
    | .inl o => S.arg o
    | .inr o => S'.arg o
  answer
    | .inl o => S.answer o
    | .inr o => S'.answer o

/-- Side-by-side backends run the product of two non-interfering refinements, whatever their
joint invariant `J`. -/
theorem Implements.prod {w : ℕ} {S : Backend D C} {S' : Backend D' C'}
    {R : Refinement D (Memory.spec w)} {R' : Refinement D' (Memory.spec w)}
    {J : Memory.State → Prop}
    {frame₁ : ∀ {e} o {a e' tr}, R.inv e → R'.inv e → J e → D.valid (R.abs e) o →
      (Memory.spec w).ClientRun e (R.methods o) a e' tr → R'.abs e' = R'.abs e ∧ R'.inv e' ∧ J e'}
    {frame₂ : ∀ {e} o {a e' tr}, R.inv e → R'.inv e → J e → D'.valid (R'.abs e) o →
      (Memory.spec w).ClientRun e (R'.methods o) a e' tr → R.abs e' = R.abs e ∧ R.inv e' ∧ J e'}
    (hS : S.Implements R) (hS' : S'.Implements R') :
    (S.sum S').Implements (R.prod R' J frame₁ frame₂) where
  run
    | .inl o, s => hS.run o s
    | .inr o, s => hS'.run o s
  entry
    | .inl o, hw, hi, hv => hS.entry o hw hi.1 hv
    | .inr o, hw, hi, hv => hS'.entry o hw hi.2.1 hv

/-- The backend with the tags of a second family added, such as a realized allocation's
(`Backend.Allocation`). Every operation selects the body it selects in `S`. -/
@[expose] def extend (C' : ι' → Certificate B) : Backend D (Sum.elim C C') where
  tag o := .inl (S.tag o)
  arg := S.arg
  answer := S.answer

/-- An extended backend runs the methods its original runs. -/
theorem Implements.extend {w : ℕ} {S : Backend D C} {R : Refinement D (Memory.spec w)}
    (hS : S.Implements R) (C' : ι' → Certificate B) : (S.extend C').Implements R where
  run := hS.run
  entry := hS.entry

end Sum

/-! ### Native execution -/

variable [Fintype ι]

/-- Install the selected program's arguments in its argument registers. Installation is
uncharged and leaves memory and the frontier unchanged. -/
@[expose] def prepare (o : D.Op) (x : Data (registers C)) : Data (registers C) :=
  install C (S.tag o) (S.arg o) x

/-- An operation runs the body of its tag from the prepared data, in the counted number of
instructions, and its answer is read off the encoded result. -/
def exec (w : ℕ) : Execution D (Data (registers C)) ℕ :=
  fun x o a y n => Exec w (code C (S.tag o)) (S.prepare o x) y n ∧
    ∃ b, a = S.answer o b ∧ ∀ j, y.regs (tmp C (S.tag o)
      (Fin.castAdd ((C (S.tag o)).realizes.scratchSize + 1) j)) = (C (S.tag o)).output b j

/-- The execution relation, unfolded. -/
theorem exec_iff (w : ℕ) (x y : Data (registers C)) (o : D.Op) (a : D.Result o) (n : ℕ) :
    S.exec w x o a y n ↔ Exec w (code C (S.tag o)) (S.prepare o x) y n ∧
      ∃ b, a = S.answer o b ∧ ∀ j, y.regs (tmp C (S.tag o)
        (Fin.castAdd ((C (S.tag o)).realizes.scratchSize + 1) j)) =
          (C (S.tag o)).output b j := Iff.rfl

variable {S} {w : ℕ} {R : Refinement D (Memory.spec w)}

/-- One operation from represented data: its body's execution, instruction count, memory,
encoded result and answer. -/
private theorem exists_body (hS : S.Implements R) (o : D.Op) {x : Data (registers C)}
    (hi : R.inv (memoryState (frontier C) x)) (hx : x.Bounded w)
    (hv : D.valid (R.abs (memoryState (frontier C) x)) o) :
    ∃ y n, Exec w (code C (S.tag o)) (S.prepare o x) y n ∧
      n ≤ factor C * ((Memory.spec w).totalCost Memory.charge (memoryState (frontier C) x)
          ((Memory.spec w).clientHistory (memoryState (frontier C) x) (R.methods o)) +
        (C (S.tag o)).work (S.arg o) (memoryState (frontier C) x) + 1) ∧
      memoryState (frontier C) y =
        (Memory.spec w).clientState (memoryState (frontier C) x) (R.methods o) ∧
      (∀ j, y.regs (tmp C (S.tag o) (Fin.castAdd ((C (S.tag o)).realizes.scratchSize + 1) j)) =
        (C (S.tag o)).output
          ((Memory.spec w).clientResult (memoryState (frontier C) x)
            ((C (S.tag o)).prog (S.arg o))) j) ∧
      S.answer o ((Memory.spec w).clientResult (memoryState (frontier C) x)
          ((C (S.tag o)).prog (S.arg o))) =
        (Memory.spec w).clientResult (memoryState (frontier C) x) (R.methods o) ∧
      y.Bounded w ∧
      (Memory.spec w).ValidHistory (memoryState (frontier C) x)
        ((Memory.spec w).clientHistory (memoryState (frontier C) x) (R.methods o)) := by
  have hrun := hS.run o (memoryState (frontier C) x)
  have hvalid := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
    (R.valid o hi hv)
  obtain ⟨hin, hsafe⟩ := hS.entry o (wellFormed_memoryState hx) hi hv
  have hhist : (Memory.spec w).clientHistory (memoryState (frontier C) x) (R.methods o) =
      (Memory.spec w).clientHistory (memoryState (frontier C) x)
        ((C (S.tag o)).prog (S.arg o)) := congrArg (fun t => t.2.2) hrun
  obtain ⟨y, n, he, hn, hm, hout, hb⟩ :=
    exists_exec C (S.tag o) (S.arg o) hx hin hsafe (hhist ▸ hvalid)
  refine ⟨y, n, he, hn.trans_eq ?_, hm.trans (congrArg (fun t => t.2.1) hrun).symm, hout,
    (congrArg Prod.fst hrun).symm, hb, hvalid⟩
  rw [memoryCost_eq_totalCost w, ← hhist]

/-- The answer of an execution is the method's result. -/
private theorem answer_eq (hS : S.Implements R) {o : D.Op} {x y : Data (registers C)}
    {a : D.Result o} {n : ℕ} (he : S.exec w x o a y n)
    (hout : ∀ j, y.regs (tmp C (S.tag o) (Fin.castAdd ((C (S.tag o)).realizes.scratchSize + 1) j)) =
      (C (S.tag o)).output
        ((Memory.spec w).clientResult (memoryState (frontier C) x)
          ((C (S.tag o)).prog (S.arg o))) j) :
    a = (Memory.spec w).clientResult (memoryState (frontier C) x) (R.methods o) := by
  obtain ⟨-, b, rfl, hb⟩ := he
  rw [(C (S.tag o)).output.injective (funext fun j => (hb j).symm.trans (hout j))]
  exact (congrArg Prod.fst (hS.run o _)).symm

/-- The native implementation: represented data holds a memory that satisfies the refinement's
invariant and abstracts to the state, and every register and cell holds a word. -/
noncomputable def implementation (hS : S.Implements R) : StateTransitionImpl D (S.exec w) where
  rep s x := R.inv (memoryState (frontier C) x) ∧ R.abs (memoryState (frontier C) x) = s ∧
    x.Bounded w
  total o hr hv := by
    obtain ⟨hi, rfl, hx⟩ := hr
    obtain ⟨y, n, he, -, -, hout, -⟩ := exists_body hS o hi hx hv
    exact ⟨_, y, n, he, _, rfl, hout⟩
  correct {s x o a y n} hr hv he := by
    obtain ⟨hi, rfl, hx⟩ := hr
    obtain ⟨y', n', he', -, hm, hout, -, hb, hvalid⟩ := exists_body hS o hi hx hv
    obtain ⟨rfl, rfl⟩ := he.1.unique he'
    have ha := answer_eq hS he hout
    obtain ⟨hstep, hi'⟩ := R.correct o hi hv ((Memory.spec w).clientRun_canonical _ _ hvalid)
    exact ⟨_, ha ▸ hstep, hm ▸ hi', by rw [hm], hb⟩

/-- The representation, unfolded. -/
theorem rep_iff (hS : S.Implements R) (s : D.State) (x : Data (registers C)) :
    (implementation hS).rep s x ↔ R.inv (memoryState (frontier C) x) ∧
      R.abs (memoryState (frontier C) x) = s ∧ x.Bounded w := Iff.rfl

/-- The data holding a well-formed memory state that satisfies the invariant represents its
abstraction. -/
theorem rep_data (hS : S.Implements R) {e : Memory.State} {s : D.State}
    (hw : Memory.WellFormed w e) (hi : R.inv e) (ha : R.abs e = s) :
    (implementation hS).rep s (data C e) := by
  refine (rep_iff hS s _).mpr ⟨?_, ?_, bounded_data C hw⟩ <;> rw [memoryState_data] <;> assumption

/-- An operation leaves the memory and frontier of its method. -/
theorem exec_memoryState (hS : S.Implements R) {s : D.State} {x y : Data (registers C)}
    {o : D.Op} {a : D.Result o} {n : ℕ} (hr : (implementation hS).rep s x) (hv : D.valid s o)
    (he : S.exec w x o a y n) :
    memoryState (frontier C) y =
      (Memory.spec w).clientState (memoryState (frontier C) x) (R.methods o) := by
  obtain ⟨hi, rfl, hx⟩ := hr
  obtain ⟨y', n', he', -, hm, -⟩ := exists_body hS o hi hx hv
  obtain ⟨rfl, -⟩ := he.1.unique he'
  exact hm

/-- **Amortized instructions.** Memory charges with a potential, plus local work at most `c`,
give native instruction counts with the potential scaled by the exchange factor. -/
theorem amortized (hS : S.Implements R) {upper : D.State → D.Op → ℕ}
    {Φ : Memory.State → ℕ} (A : R.Amortized Memory.charge upper Φ) (c : ℕ)
    (hwork : ∀ {e} o, R.inv e → D.valid (R.abs e) o → (C (S.tag o)).work (S.arg o) e ≤ c) :
    DataStructure.Amortized (implementation hS) id
      (fun _ x => factor C * Φ (memoryState (frontier C) x))
      (fun s o => factor C * (upper s o + c + 1)) where
  step {s x o a y n} hr hv he := by
    obtain ⟨hi, rfl, hx⟩ := hr
    obtain ⟨y', n', he', hn, hm, hout, -, hb, hvalid⟩ := exists_body hS o hi hx hv
    obtain ⟨rfl, rfl⟩ := he.1.unique he'
    have ha := answer_eq hS he hout
    have hrun := (Memory.spec w).clientRun_canonical _ _ hvalid
    obtain ⟨hstep, hi'⟩ := R.correct o hi hv hrun
    have hA := A.step o hi hv hrun
    rw [StateTransitionSpec.totalCostTranscript_canonicalTranscript, ← hm] at hA
    have hw := hwork o hi hv
    refine ⟨_, ha ▸ hstep, ⟨hm ▸ hi', by rw [hm], hb⟩, ?_⟩
    change n + _ ≤ _
    calc n + factor C * Φ (memoryState (frontier C) y)
        ≤ factor C * ((Memory.spec w).totalCost Memory.charge (memoryState (frontier C) x)
            ((Memory.spec w).clientHistory (memoryState (frontier C) x) (R.methods o)) +
          (C (S.tag o)).work (S.arg o) (memoryState (frontier C) x) + 1) +
          factor C * Φ (memoryState (frontier C) y) := Nat.add_le_add_right hn _
      _ = factor C * ((Memory.spec w).totalCost Memory.charge (memoryState (frontier C) x)
            ((Memory.spec w).clientHistory (memoryState (frontier C) x) (R.methods o)) +
          Φ (memoryState (frontier C) y) +
          (C (S.tag o)).work (S.arg o) (memoryState (frontier C) x) + 1) := by ring
      _ ≤ factor C * (upper (R.abs (memoryState (frontier C) x)) o +
          Φ (memoryState (frontier C) x) + c + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = factor C * (upper (R.abs (memoryState (frontier C) x)) o + c + 1) +
          factor C * Φ (memoryState (frontier C) x) := by ring

/-- **Worst-case instructions.** Memory charges at most `upper` without a potential, plus local
work at most `c`, bound every operation's instructions by `factor C * (upper + c + 1)`. With a
constant `upper` this is one constant for every width and refinement. -/
theorem bound (hS : S.Implements R) {upper : D.State → D.Op → ℕ}
    (A : R.Amortized Memory.charge upper fun _ => 0) (c : ℕ)
    (hwork : ∀ {e} o, R.inv e → D.valid (R.abs e) o → (C (S.tag o)).work (S.arg o) e ≤ c) :
    Bound (implementation hS) id fun s o => factor C * (upper s o + c + 1) := by
  intro s x o a y n hr hv he
  obtain ⟨-, -, -, hcost⟩ := (amortized hS A c hwork).step hr hv he
  simpa only [id, Nat.mul_zero, Nat.add_zero] using hcost

end Backend

end Cslib.WordRAM.Realization
