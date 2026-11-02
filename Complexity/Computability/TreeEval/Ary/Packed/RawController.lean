/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Iterative
public import Complexity.Computability.TreeEval.Reader.Arith
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Uniform raw control for packed Cook–Mertz

Runtime naturals hold the field modulus, fan-in and register width. One flat list holds the
register bank; continuation frames retain only round, child, phase, coefficient and target.
A stored scalar is offset by the modulus, so even a zero residue retains the field's bit width.
The offset disappears when the cell is read in `ZMod p`.

Unit rounds are numbered by naturals: round `j` uses `j + 1`, and its inverse uses the existing
modular inverse loop. No list of all field units is part of the machine state. Node values and
gate-extension values arrive as explicit replies; the raw controller stores no tree or gate.
-/

@[expose] public section

namespace Cslib.TreeEval.Ary.Packed.RawController

open Reader

/-- Runtime modulus, fan-in and register width. -/
abbrev Params := ℕ × ℕ × ℕ

/-- Round, child, undo phase, coefficient and target, with binary natural indices. -/
abbrev Frame := ℕ × ℕ × Bool × ℕ × ℕ

/-- One global bank, its continuation stack and a call coefficient/target or return. -/
abbrev State := List ℕ × List Frame × Option (ℕ × ℕ)

/-- Row-major bank position, matching the existing finite-product equivalence. -/
def index (r t i : ℕ) : ℕ := i + r * t

/-- The child register modulo the number of available registers. -/
def reg (d t j : ℕ) : ℕ := (t + (j + 1)) % (d + 1)

/-- Read the raw bank as the existing finite field register bank. -/
def toRegs (p d r : ℕ) (bank : List ℕ) : Ary.State (ZMod p) d r :=
  fun t i => (bank.getD (index r t i) 0 : ZMod p)

/-- Canonical padded cells for the existing register bank, flattened once. -/
noncomputable def ofRegs {p d r : ℕ} (S : Ary.State (ZMod p) d r) : List ℕ :=
  List.ofFn fun k : Fin ((d + 1) * r) =>
    let ti := finProdFinEquiv.symm k
    p + (S ti.1 ti.2).val

/-- Scale one register, retaining the global bank and all other cells. -/
def scaleBank (p r t a : ℕ) (bank : List ℕ) : List ℕ :=
  bank.mapIdx fun k v => if k / r = t then p + mulMod p a v else v

/-- Add a supplied vector times a coefficient into one register. -/
def addBank (p r t c : ℕ) (values bank : List ℕ) : List ℕ :=
  bank.mapIdx fun k v => if k / r = t then
    p + addMod p v (mulMod p c (values.getD (k % r) 0)) else v

/-- Subtract a supplied gate-extension vector times a coefficient from one register. -/
def subBank (p r t c : ℕ) (values bank : List ℕ) : List ℕ :=
  bank.mapIdx fun k v => if k / r = t then
    p + addMod p v (negMod p (mulMod p c (values.getD (k % r) 0))) else v

@[simp] theorem length_ofRegs {p d r : ℕ} (S : Ary.State (ZMod p) d r) :
    (ofRegs S).length = (d + 1) * r := by simp [ofRegs]

@[simp] theorem length_scaleBank (p r t a : ℕ) (bank : List ℕ) :
    (scaleBank p r t a bank).length = bank.length := by simp [scaleBank]

@[simp] theorem length_addBank (p r t c : ℕ) (values bank : List ℕ) :
    (addBank p r t c values bank).length = bank.length := by simp [addBank]

@[simp] theorem length_subBank (p r t c : ℕ) (values bank : List ℕ) :
    (subBank p r t c values bank).length = bank.length := by simp [subBank]

private theorem index_lt {d r : ℕ} (t : Fin (d + 1)) (i : Fin r) :
    index r t i < (d + 1) * r :=
  (finProdFinEquiv (t, i)).isLt

private theorem index_div {d r : ℕ} (t : Fin (d + 1)) (i : Fin r) :
    index r t i / r = t := by
  have hr : 0 < r := Nat.pos_of_ne_zero fun h => by simpa [h] using i.isLt
  simp [index, Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt i.isLt]

private theorem index_mod {d r : ℕ} (t : Fin (d + 1)) (i : Fin r) :
    index r t i % r = i := by
  simp [index, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

/-- Reading the canonical flat bank recovers the existing register representation. -/
theorem toRegs_ofRegs {p d r : ℕ} [NeZero p] (S : Ary.State (ZMod p) d r) :
    toRegs p d r (ofRegs S) = S := by
  funext t i
  have hk := index_lt t i
  have hnat : (ofRegs S).getD (index r t i) 0 = p + (S t i).val := by
    simp only [ofRegs, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk,
      ↓reduceDIte, Option.getD_some]
    have hfin : (⟨index r t i, hk⟩ : Fin ((d + 1) * r)) = finProdFinEquiv (t, i) := rfl
    rw [hfin, Equiv.symm_apply_apply]
  change ((ofRegs S).getD (index r t i) 0 : ZMod p) = S t i
  rw [hnat]
  simp

/-- Raw child-register arithmetic agrees with the existing finite register API. -/
theorem reg_eq {d : ℕ} (t : Fin (d + 1)) (j : Fin d) :
    reg d t j = (Ary.reg t j).val := by
  simp [reg, Ary.reg, Fin.val_add]

/-- Scaling the flat bank is exactly scaling one existing typed register. -/
theorem toRegs_scaleBank {p d r : ℕ} [Fact p.Prime] (bank : List ℕ)
    (hlen : bank.length = (d + 1) * r) (t : Fin (d + 1)) (a : ℕ) :
    toRegs p d r (scaleBank p r t a bank) =
      Ary.scale t (a : ZMod p) (toRegs p d r bank) := by
  funext t' i
  have hk : index r t' i < bank.length := hlen ▸ index_lt t' i
  have hd := index_div t' i
  by_cases ht : t' = t
  · subst t'
    simp [toRegs, scaleBank, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      hd, Ary.scale]
  · have htn : t'.val ≠ t.val := fun h => ht (Fin.ext h)
    simp [toRegs, scaleBank, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      hd, htn, Ary.scale, ht]

/-- Adding a returned leaf vector is the existing typed leaf update. -/
theorem toRegs_addBank {p d r : ℕ} (bank values : List ℕ)
    (hlen : bank.length = (d + 1) * r) (t : Fin (d + 1)) (c : ℕ) :
    toRegs p d r (addBank p r t c values bank) =
      Function.update (toRegs p d r bank) t
        (toRegs p d r bank t + (c : ZMod p) • fun i : Fin r => (values.getD i 0 : ZMod p)) := by
  funext t' i
  have hk : index r t' i < bank.length := hlen ▸ index_lt t' i
  have hd := index_div t' i
  have hm := index_mod t' i
  by_cases ht : t' = t
  · subst t'
    simp [toRegs, addBank, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      hd, hm]
  · have htn : t'.val ≠ t.val := fun h => ht (Fin.ext h)
    simp [toRegs, addBank, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      hd, htn, ht]

/-- Subtracting returned packed gate values is the existing typed gate update. -/
theorem toRegs_subBank {p d r : ℕ} [NeZero p] (bank values : List ℕ)
    (hlen : bank.length = (d + 1) * r) (t : Fin (d + 1)) (c : ℕ) :
    toRegs p d r (subBank p r t c values bank) =
      Function.update (toRegs p d r bank) t
        (fun i => toRegs p d r bank t i - (c : ZMod p) * (values.getD i 0 : ZMod p)) := by
  funext t' i
  have hk : index r t' i < bank.length := hlen ▸ index_lt t' i
  have hd := index_div t' i
  have hm := index_mod t' i
  by_cases ht : t' = t
  · subst t'
    simp [toRegs, subBank, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      hd, hm, sub_eq_add_neg]
  · have htn : t'.val ≠ t.val := fun h => ht (Fin.ext h)
    simp [toRegs, subBank, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      hd, htn, ht]

/-- Recover the path from child indices; it is not duplicated in continuation frames. -/
def path (stack : List Frame) : List ℕ := stack.reverse.map (fun fr => fr.2.1)

/-- The child-register point is the cyclic bank with its target register omitted. It uses
only two slices, including when the register width or fan-in is zero. -/
def point (d r t : ℕ) (bank : List ℕ) : List ℕ :=
  let target := t % (d + 1)
  bank.drop ((target + 1) * r) ++ bank.take (target * r)

/-- Node requests use tag zero; gate-extension requests use tag one and carry one point.
The final natural is the requested output chunk; zero begins a vector-reading subroutine. -/
abbrev Need := ℕ × List ℕ × List ℕ × ℕ

/-- Request only the external data needed by the current control step. -/
def needCore (d r : ℕ) (q : State) : Option Need :=
  match q.2.2 with
  | some _ => some (0, path q.2.1, [], 0)
  | none => match q.2.1 with
    | [] => none
    | fr :: st =>
      if fr.2.2.1 || decide (fr.2.1 + 1 < d) then none
      else some (1, path st, point d r fr.2.2.2.2 q.1, 0)

/-- A node reply has tag zero for invalid, one for a leaf, or two for a gate. The payload is
one packed value or one gate-extension value, never a table of assignments. -/
abbrev Reply := ℕ × List ℕ

/-- Check the padding needed by native register transformations. Malformed states can be
rejected before a transformation expands a short list of zeros into full-width residues. -/
def validBank (p d r : ℕ) (bank : List ℕ) : Bool :=
  decide (2 ≤ p) && decide (bank.length = (d + 1) * r) &&
    bank.all (fun v => decide (p ≤ v))

/-- Reject malformed storage before constructing a request point. -/
def need (p d r : ℕ) (q : State) : Option Need :=
  if validBank p d r q.1 then needCore d r q else none

/-- The executable guard states the bank shape and per-cell padding explicitly. -/
theorem validBank_eq_true (p d r : ℕ) (bank : List ℕ) :
    validBank p d r bank = true ↔
      2 ≤ p ∧ bank.length = (d + 1) * r ∧ ∀ v ∈ bank, p ≤ v := by
  simp [validBank, Bool.and_eq_true, List.all_eq_true, and_assoc]

private theorem padding_mapIdx {p : ℕ} {bank : List ℕ} {f : ℕ → ℕ → ℕ}
    (hbank : ∀ v ∈ bank, p ≤ v) (hf : ∀ i v, p ≤ v → p ≤ f i v) :
    ∀ v ∈ bank.mapIdx f, p ≤ v := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hv
  exact hf i bank[i] (hbank _ (List.getElem_mem hi))

/-- Scaling preserves the encoded-width padding invariant. -/
theorem validBank_scaleBank (p d r t a : ℕ) (bank : List ℕ)
    (hbank : validBank p d r bank = true) :
    validBank p d r (scaleBank p r t a bank) = true := by
  obtain ⟨hp, hlen, hpad⟩ := (validBank_eq_true p d r bank).mp hbank
  apply (validBank_eq_true p d r _).mpr
  refine ⟨hp, by simpa only [length_scaleBank] using hlen, ?_⟩
  apply padding_mapIdx hpad
  intro i v hv
  split_ifs <;> omega

/-- A returned value preserves the padding even when some supplied coordinates are missing. -/
theorem validBank_addBank (p d r t c : ℕ) (values bank : List ℕ)
    (hbank : validBank p d r bank = true) :
    validBank p d r (addBank p r t c values bank) = true := by
  obtain ⟨hp, hlen, hpad⟩ := (validBank_eq_true p d r bank).mp hbank
  apply (validBank_eq_true p d r _).mpr
  refine ⟨hp, by simpa only [length_addBank] using hlen, ?_⟩
  apply padding_mapIdx hpad
  intro i v hv
  split_ifs <;> omega

/-- A returned extension preserves the padding through a subtractive update. -/
theorem validBank_subBank (p d r t c : ℕ) (values bank : List ℕ)
    (hbank : validBank p d r bank = true) :
    validBank p d r (subBank p r t c values bank) = true := by
  obtain ⟨hp, hlen, hpad⟩ := (validBank_eq_true p d r bank).mp hbank
  apply (validBank_eq_true p d r _).mpr
  refine ⟨hp, by simpa only [length_subBank] using hlen, ?_⟩
  apply padding_mapIdx hpad
  intro i v hv
  split_ifs <;> omega

/-- Start one round using the counter's unit, without retaining an enumeration of units. -/
def beginRound (p d r round c t : ℕ) (bank : List ℕ) (stack : List Frame) : State :=
  (scaleBank p r (reg d t 0) (round + 1) bank,
    (round, 0, false, c, t) :: stack, some (1, reg d t 0))

/-- The arithmetic/control step, after any required reply has returned. -/
def stepCore (p d r : ℕ) (reply : Reply) (q : State) : State :=
  match q.2.2 with
  | some (c, t) =>
    if reply.1 = 1 then (addBank p r t c reply.2 q.1, q.2.1, none)
    else if reply.1 = 2 then
      if p - 1 = 0 then (q.1, q.2.1, none)
      else beginRound p d r 0 c t q.1 q.2.1
    else (q.1, q.2.1, none)
  | none => match q.2.1 with
    | [] => q
    | (round, child, undo, c, t) :: st =>
      if undo then
        let bank := scaleBank p r (reg d t child) (unitInv p round) q.1
        if child + 1 < d then
          (bank, (round, child + 1, true, c, t) :: st,
            some (p - 1, reg d t (child + 1)))
        else if round + 1 < p - 1 then beginRound p d r (round + 1) c t bank st
        else (bank, st, none)
      else
        if child + 1 < d then
          (scaleBank p r (reg d t (child + 1)) (round + 1) q.1,
            (round, child + 1, false, c, t) :: st, some (1, reg d t (child + 1)))
        else
          (subBank p r t c reply.2 q.1, (round, 0, true, c, t) :: st,
            some (p - 1, reg d t 0))

/-- Reject malformed storage without transforming it. -/
def step (p d r : ℕ) (reply : Reply) (q : State) : State :=
  if validBank p d r q.1 then stepCore p d r reply q else q

/-- Typed continuation frames are represented by their five small control fields. -/
def ofFrame {p d : ℕ} (fr : Ary.Iter.Frame (ZMod p) d) : Frame :=
  (fr.round, fr.child.val, fr.undo, fr.coeff.val, fr.target.val)

/-- The raw mode uses the same return/call convention as the existing controller. -/
def ofMode {p d : ℕ} (mode : Ary.Iter.Mode (ZMod p) d) : Option (ℕ × ℕ) :=
  match mode with
  | .call c t => some (c.val, t.val)
  | .ret => none

/-- The canonical raw representation has one bank and no saved banks in its frames. -/
noncomputable def ofCfg {p d r : ℕ} (q : Ary.Iter.Cfg (ZMod p) d r) : State :=
  (ofRegs q.regs, q.stack.map ofFrame, ofMode q.mode)

/-- Reading an individual raw frame uses the existing finite index types. -/
def toFrame {p d : ℕ} (hd : 0 < d) (fr : Frame) : Ary.Iter.Frame (ZMod p) d :=
  ⟨fr.1, ⟨fr.2.1 % d, Nat.mod_lt _ hd⟩, fr.2.2.1, (fr.2.2.2.1 : ZMod p),
    ⟨fr.2.2.2.2 % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩⟩

/-- Decode only the control fields and scalar values; no tree or table is reconstructed. -/
def toMode (p d : ℕ) (mode : Option (ℕ × ℕ)) : Ary.Iter.Mode (ZMod p) d :=
  match mode with
  | some (c, t) => .call (c : ZMod p) ⟨t % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩
  | none => .ret

/-- Read a raw configuration in the existing iterative semantics. -/
def toCfg (p d r : ℕ) (hd : 0 < d) (q : State) : Ary.Iter.Cfg (ZMod p) d r :=
  ⟨toRegs p d r q.1, q.2.1.map (toFrame hd), toMode p d q.2.2⟩

@[simp] theorem toFrame_ofFrame {p d : ℕ} [NeZero p] (hd : 0 < d)
    (fr : Ary.Iter.Frame (ZMod p) d) : toFrame hd (ofFrame fr) = fr := by
  cases fr with
  | mk round child undo coeff target =>
    simp only [toFrame, ofFrame, Nat.mod_eq_of_lt child.isLt,
      Nat.mod_eq_of_lt target.isLt, ZMod.natCast_zmod_val]

@[simp] theorem toMode_ofMode {p d : ℕ} [NeZero p] (mode : Ary.Iter.Mode (ZMod p) d) :
    toMode p d (ofMode mode) = mode := by
  cases mode with
  | ret => rfl
  | call c t =>
    simp only [toMode, ofMode, Nat.mod_eq_of_lt t.isLt, ZMod.natCast_zmod_val]

/-- The raw representation faithfully exposes the existing controller's configurations. -/
theorem toCfg_ofCfg {p d r : ℕ} [NeZero p] (hd : 0 < d)
    (q : Ary.Iter.Cfg (ZMod p) d r) : toCfg p d r hd (ofCfg q) = q := by
  cases q
  simp [toCfg, ofCfg, toRegs_ofRegs, List.map_map, Function.comp_def]

/-- The stack-derived request path is the existing controller's path. -/
theorem path_ofFrame {p d : ℕ} (st : List (Ary.Iter.Frame (ZMod p) d)) :
    path (st.map ofFrame) = (Ary.Iter.path st).map Fin.val := by
  simp [path, Ary.Iter.path, List.map_reverse, List.map_map, ofFrame]

/-- Canonical field banks satisfy the executable padding guard. -/
theorem validBank_ofRegs {p d r : ℕ} (hp : 2 ≤ p)
    (S : Ary.State (ZMod p) d r) : validBank p d r (ofRegs S) = true := by
  simp only [validBank, hp, decide_true, length_ofRegs, Bool.true_and]
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hv
  simp

/-- A returned leaf changes only its target bank and returns to its continuation. -/
theorem step_call_leaf (p d r c t : ℕ) (values bank : List ℕ) (stack : List Frame)
    (hvalid : validBank p d r bank = true) :
    step p d r (1, values) (bank, stack, some (c, t)) =
      (addBank p r t c values bank, stack, none) := by
  simp [step, hvalid, stepCore]

/-- The concrete raw leaf transition implements the existing iterative controller's leaf step. -/
theorem toCfg_step_call_leaf {p d r b : ℕ} [Fact p.Prime] (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (us : List (ZMod p)ˣ) (read : List (Fin d) → Tree.Node d b)
    (S : Ary.State (ZMod p) d r) (st : List (Ary.Iter.Frame (ZMod p) d))
    (c : ZMod p) (t : Fin (d + 1)) (v : Fin b → Bool) (values : List ℕ)
    (hread : read (Ary.Iter.path st) = .leaf v)
    (hvalues : ∀ i : Fin r, (values.getD i 0 : ZMod p) = e v i) :
    toCfg p d r hd
      (step p d r (1, values) (ofCfg (⟨S, st, .call c t⟩ : Ary.Iter.Cfg (ZMod p) d r))) =
      Ary.Iter.step hd e E us read ⟨S, st, .call c t⟩ := by
  rw [Ary.Iter.step_call_leaf hd e E us read S st c t v hread]
  change toCfg p d r hd
    (step p d r (1, values) (ofRegs S, st.map ofFrame, some (c.val, t.val))) = _
  rw [step_call_leaf p d r c.val t.val values (ofRegs S) (st.map ofFrame)
    (validBank_ofRegs (Fact.out : p.Prime).two_le S)]
  have hregs := toRegs_addBank (p := p) (d := d) (r := r)
    (ofRegs S) values (length_ofRegs S) t c.val
  rw [toRegs_ofRegs, ZMod.natCast_zmod_val] at hregs
  have hvec : (fun i : Fin r => (values.getD i 0 : ZMod p)) = e v := funext hvalues
  rw [hvec] at hregs
  simp only [toCfg, toMode, List.map_map]
  rw [hregs]
  congr 1
  simp only [Function.comp_def, toFrame_ofFrame, List.map_id_fun', id_eq]

/-- A counter-numbered raw round starts the same typed round when its unit is the supplied
list's unit. The list belongs only to the comparison theorem, not to the raw configuration. -/
theorem toCfg_beginRound {p d r : ℕ} [Fact p.Prime] (hd : 0 < d)
    (us : List (ZMod p)ˣ) (round : ℕ) (c : ZMod p) (t : Fin (d + 1))
    (bank : List ℕ) (hlen : bank.length = (d + 1) * r)
    (st : List (Ary.Iter.Frame (ZMod p) d))
    (hunit : ((round + 1 : ℕ) : ZMod p) = (Ary.Iter.unitAt us round : ZMod p)) :
    toCfg p d r hd (beginRound p d r round c.val t.val bank (st.map ofFrame)) =
      Ary.Iter.beginRound hd us round c t (toRegs p d r bank) st := by
  let child : Fin d := ⟨0, hd⟩
  have hreg : reg d t.val 0 = (Ary.reg t child).val := reg_eq t child
  have hscale := toRegs_scaleBank (p := p) (d := d) (r := r)
    bank hlen (Ary.reg t child) (round + 1)
  rw [hunit] at hscale
  have hstack : (st.map ofFrame).map (toFrame hd) = st := by
    simp only [List.map_map, Function.comp_def, toFrame_ofFrame,
      List.map_id_fun', id_eq]
  simp only [beginRound, toCfg, List.map_cons, hstack]
  simp only [toFrame, toMode, Nat.zero_mod, Nat.mod_eq_of_lt t.isLt,
    ZMod.natCast_zmod_val, Nat.cast_one]
  rw [hreg, hscale]
  simp only [Ary.Iter.beginRound, child, Nat.mod_eq_of_lt (Ary.reg t child).isLt]

/-- The comparison enumeration's unit is obtained directly from its round index. -/
theorem unitAt_zmodUnits {p : ℕ} [Fact p.Prime] {j : ℕ} (hj : j < p - 1) :
    Ary.Iter.unitAt ((List.range (p - 1)).map (TreeEval.Iter.zmodUnit p)) j =
      TreeEval.Iter.zmodUnit p j := by
  simp [Ary.Iter.unitAt, List.getD_eq_getElem?_getD, hj]

/-- In the canonical prime-field enumeration, the raw round counter implements the existing
round initializer without ever constructing the comparison enumeration at runtime. -/
theorem toCfg_beginRound_zmodUnits {p d r : ℕ} [Fact p.Prime] (hd : 0 < d)
    (round : ℕ) (hround : round < p - 1) (c : ZMod p) (t : Fin (d + 1))
    (bank : List ℕ) (hlen : bank.length = (d + 1) * r)
    (st : List (Ary.Iter.Frame (ZMod p) d)) :
    toCfg p d r hd (beginRound p d r round c.val t.val bank (st.map ofFrame)) =
      Ary.Iter.beginRound hd ((List.range (p - 1)).map (TreeEval.Iter.zmodUnit p))
        round c t (toRegs p d r bank) st := by
  apply toCfg_beginRound hd _ round c t bank hlen st
  rw [unitAt_zmodUnits hround, TreeEval.Iter.zmodUnit_val hround]

end Cslib.TreeEval.Ary.Packed.RawController
