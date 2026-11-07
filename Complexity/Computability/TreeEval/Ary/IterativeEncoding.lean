/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.IterativeBounds
public import Complexity.Computability.TreeEval.Ary.PackingParameters
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Binary encodings for iterative Cook–Mertz

The register bank is stored once as a flat finite table. A continuation frame contains binary
round and register indices, a phase bit and one coefficient. No register bank, tree or path is
stored in a frame. The final bound charges list and pair framing, including the current mode.

These are bounds on an actual injective representation. Native computation of the controller's
components and implicit node queries remain separate obligations.

## Main definitions

* `Cslib.TreeEval.Ary.Iter.encCfg`: compact state encoding, parameterized by a scalar encoding.
* `Cslib.TreeEval.Ary.Iter.encField`: binary residues in a nonzero modular field.

## Main results

* `Cslib.TreeEval.Ary.Iter.length_encCfg_le`: one bank plus a linear number of small frames.
* `Cslib.TreeEval.Ary.Iter.length_encCfg_runFrom_le`: every clocked prefix has that bound.
* `Cslib.TreeEval.Ary.Iter.length_encCfg_packed_runFrom_le_of_rounds_le`: the selected packed
  parameters give linear bank size plus logarithmic control per level at every clock.
-/

public section

namespace Cslib.TreeEval.Ary.Iter

open Turing.MultiTapeTM

variable {K : Type} {d r b H : ℕ}

/-- Finite indices use binary values, rather than unary enumeration ranks. -/
@[expose] def encIndex (n : ℕ) : Fin n ↪ List Bool where
  toFun i := encNat i.val
  inj' := by
    intro i j h
    exact Fin.val_injective (encNat.injective h)

@[simp] theorem length_encIndex (n : ℕ) (i : Fin n) :
    (encIndex n i).length = i.val.size := by
  change i.val.bits.length = i.val.size
  exact Nat.size_eq_bits_len _

/-- Flatten the two register indices before storing the bank, avoiding nested list framing. -/
@[expose] noncomputable def encRegs (encK : K ↪ List Bool) : Ary.State K d r ↪ List Bool where
  toFun S := encPi (Index := Fin (d + 1) × Fin r) encK (fun i => S i.1 i.2)
  inj' := by
    intro S S' h
    have heq := (encPi encK).injective h
    funext i j
    exact congrFun heq (i, j)

/-- Frames contain only their five control fields, with binary indices. -/
@[expose] def encFrame (encK : K ↪ List Bool) : Frame K d ↪ List Bool where
  toFun fr := encPair encNat (encPair (encIndex d)
    (encPair encBool (encPair encK (encIndex (d + 1)))))
      (fr.round, fr.child, fr.undo, fr.coeff, fr.target)
  inj' := by
    intro fr fr' h
    have heq := (encPair encNat (encPair (encIndex d)
      (encPair encBool (encPair encK (encIndex (d + 1)))))).injective h
    cases fr
    cases fr'
    simpa only [Prod.mk.injEq, Frame.mk.injEq] using heq

/-- Return is empty; call stores its coefficient and binary target after a tag. -/
@[expose] def encMode (encK : K ↪ List Bool) : Mode K d ↪ List Bool where
  toFun mode := encOption (encPair encK (encIndex (d + 1))) (match mode with
    | .call c t => some (c, t)
    | .ret => none)
  inj' := by
    intro a b h
    have heq := (encOption (encPair encK (encIndex (d + 1)))).injective h
    cases a <;> cases b <;> simp_all

/-- The bank is global; the stack and current mode are stored beside it. -/
@[expose] noncomputable def encCfg (encK : K ↪ List Bool) : Cfg K d r ↪ List Bool where
  toFun q := encPair (encRegs encK) (encPair (encList (encFrame encK)) (encMode encK))
    (q.regs, q.stack, q.mode)
  inj' := by
    intro q q' h
    have heq := (encPair (encRegs encK)
      (encPair (encList (encFrame encK)) (encMode encK))).injective h
    cases q
    cases q'
    simpa only [Prod.mk.injEq, Cfg.mk.injEq] using heq

/-- Binary residues give logarithmic scalar storage, including the zero residue. -/
@[expose] def encField (p : ℕ) [NeZero p] : ZMod p ↪ List Bool where
  toFun x := encNat x.val
  inj' := by
    intro x y h
    exact ZMod.val_injective p (encNat.injective h)

theorem length_encField_le (p : ℕ) [NeZero p] (x : ZMod p) :
    (encField p x).length ≤ p.size := by
  change (encNat x.val).length ≤ p.size
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le_size (ZMod.val_lt x).le

/-- The flattened bank charges each scalar and its list framing once. -/
theorem length_encRegs_le (encK : K ↪ List Bool) (S : Ary.State K d r) {L : ℕ}
    (hK : ∀ x, (encK x).length ≤ L) :
    (encRegs encK S).length ≤ (d + 1) * r * (2 * L + 1) := by
  change (encPi encK (fun i : Fin (d + 1) × Fin r => S i.1 i.2)).length ≤ _
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    length_encPi_le encK (fun i : Fin (d + 1) × Fin r => S i.1 i.2) (fun _ => hK _)

/-- The exact linear allowance for one bounded continuation frame. -/
@[expose] def frameBits (d rounds L : ℕ) : ℕ :=
  2 * rounds.size + 2 * d.size + 2 * L + (d + 1).size + 6

theorem length_encFrame_le (encK : K ↪ List Bool) (fr : Frame K d) {rounds L : ℕ}
    (hK : ∀ x, (encK x).length ≤ L) (hround : fr.round < rounds) :
    (encFrame encK fr).length ≤ frameBits d rounds L := by
  have hr := Nat.size_le_size hround.le
  have hc := Nat.size_le_size fr.child.isLt.le
  have ht := Nat.size_le_size fr.target.isLt.le
  have hk := hK fr.coeff
  change (encPair encNat (encPair (encIndex d)
    (encPair encBool (encPair encK (encIndex (d + 1)))))
      (fr.round, fr.child, fr.undo, fr.coeff, fr.target)).length ≤ _
  simp only [length_encPair, length_encIndex,
    encBool_apply, List.length_singleton, encNat_apply, Nat.size_eq_bits_len]
  unfold frameBits
  omega

theorem length_encMode_le (encK : K ↪ List Bool) (mode : Mode K d) {L : ℕ}
    (hK : ∀ x, (encK x).length ≤ L) :
    (encMode encK mode).length ≤ 2 * L + (d + 1).size + 2 := by
  cases mode with
  | ret => simp [encMode]
  | call c t =>
    have hk := hK c
    have ht := Nat.size_le_size t.isLt.le
    change (encOption (encPair encK (encIndex (d + 1))) (some (c, t))).length ≤ _
    simp only [encOption_some, List.length_cons, length_encPair, length_encIndex]
    omega

/-- Every frame and every separator is charged; the register bank is charged only once. -/
theorem length_encCfg_le (encK : K ↪ List Bool) (q : Cfg K d r) {rounds L : ℕ}
    (hK : ∀ x, (encK x).length ≤ L) (hq : ControlBounds H rounds q) :
    (encCfg encK q).length ≤
      2 * ((d + 1) * r * (2 * L + 1)) +
        2 * (H * (2 * frameBits d rounds L + 1)) + 2 * L + (d + 1).size + 4 := by
  have hregs := length_encRegs_le encK q.regs hK
  have hmode := length_encMode_le encK q.mode hK
  have hstack := length_encList_le (encFrame encK) q.stack
    (fun fr hfr => length_encFrame_le encK fr hK (hq.2 fr hfr))
  have hmul := Nat.mul_le_mul_right (2 * frameBits d rounds L + 1) hq.1
  change (encPair (encRegs encK)
    (encPair (encList (encFrame encK)) (encMode encK)) (q.regs, q.stack, q.mode)).length ≤ _
  simp only [length_encPair]
  omega

/-- The compact representation bound holds at every clock of a root call. -/
theorem length_encCfg_runFrom_le [Field K] (encK : K ↪ List Bool) {L : ℕ}
    (hK : ∀ x, (encK x).length ≤ L) (T : Tree d b H) (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ)
    (S : Ary.State K d r) (c : K) (t : Fin (d + 1)) (n : ℕ) :
    (encCfg encK (runFrom hd e E us T.nodeAt (initialCfg S c t) n)).length ≤
      2 * ((d + 1) * r * (2 * L + 1)) +
        2 * (H * (2 * frameBits d us.length L + 1)) + 2 * L + (d + 1).size + 4 :=
  length_encCfg_le encK _ hK (runFrom_initial_bounds T hd e E us S c t n)

/-- Binary encoding in the modulus selected by the packed parameter construction. -/
@[expose] def encPackedField (d b : ℕ) : ZMod (Packed.fieldModulus d b) ↪ List Bool :=
  letI : NeZero (Packed.fieldModulus d b) := ⟨(Packed.fieldModulus_prime d b).ne_zero⟩
  encField (Packed.fieldModulus d b)

theorem length_encPackedField_le (d b : ℕ) (x : ZMod (Packed.fieldModulus d b)) :
    (encPackedField d b x).length ≤ (Packed.fieldModulus d b).size := by
  let : NeZero (Packed.fieldModulus d b) := ⟨(Packed.fieldModulus_prime d b).ne_zero⟩
  exact length_encField_le _ x

/-- The actual flat bank encoding has linear payload size for the selected parameters. -/
theorem length_encRegs_packed_le (hd : 0 < d) (hb : 0 < b)
    (S : Ary.State (ZMod (Packed.fieldModulus d b)) d (Packed.chunkCount d b)) :
    (encRegs (encPackedField d b) S).length ≤
      9 * (d + 1) * (b + Packed.chunkWidth d b) := by
  have hbank := length_encRegs_le (encPackedField d b) S (length_encPackedField_le d b)
  have hmul := Packed.chunkCount_mul_fieldModulus_size_le hd hb
  have hr := Packed.chunkCount_le hd hb
  have hscalar : Packed.chunkCount d b * (2 * (Packed.fieldModulus d b).size + 1) ≤
      9 * (b + Packed.chunkWidth d b) := by nlinarith
  calc
    _ ≤ (d + 1) * Packed.chunkCount d b * (2 * (Packed.fieldModulus d b).size + 1) :=
      hbank
    _ = (d + 1) * (Packed.chunkCount d b * (2 * (Packed.fieldModulus d b).size + 1)) :=
      Nat.mul_assoc ..
    _ ≤ (d + 1) * (9 * (b + Packed.chunkWidth d b)) := Nat.mul_le_mul_left _ hscalar
    _ = _ := by ring

/-- The concrete packed representation has linear bank cost and small per-level control cost.
For fixed fan-in, `chunkWidth d b = (d*b).size`, so the first term is linear in `b` and each
frame uses logarithmically many bits in `b` and the round count. -/
theorem length_encCfg_packed_le (hd : 0 < d) (hb : 0 < b)
    (q : Cfg (ZMod (Packed.fieldModulus d b)) d (Packed.chunkCount d b)) {rounds : ℕ}
    (hq : ControlBounds H rounds q) :
    (encCfg (encPackedField d b) q).length ≤
      18 * (d + 1) * (b + Packed.chunkWidth d b) +
        2 * (H * (2 * frameBits d rounds (2 * Packed.chunkWidth d b + 2) + 1)) +
        4 * Packed.chunkWidth d b + (d + 1).size + 8 := by
  have hp := Packed.fieldModulus_size_le hd hb
  have hK : ∀ x, (encPackedField d b x).length ≤ 2 * Packed.chunkWidth d b + 2 :=
    fun x => (length_encPackedField_le d b x).trans hp
  have hregs := length_encRegs_packed_le hd hb q.regs
  have hmode := length_encMode_le (encPackedField d b) q.mode hK
  have hstack := length_encList_le (encFrame (encPackedField d b)) q.stack
    (fun fr hfr => length_encFrame_le (encPackedField d b) fr hK (hq.2 fr hfr))
  have hmul := Nat.mul_le_mul_right
    (2 * frameBits d rounds (2 * Packed.chunkWidth d b + 2) + 1) hq.1
  change (encPair (encRegs (encPackedField d b))
    (encPair (encList (encFrame (encPackedField d b))) (encMode (encPackedField d b)))
      (q.regs, q.stack, q.mode)).length ≤ _
  simp only [length_encPair]
  calc
    _ ≤ 2 * (9 * (d + 1) * (b + Packed.chunkWidth d b)) +
        2 * (H * (2 * frameBits d rounds (2 * Packed.chunkWidth d b + 2) + 1)) +
        (2 * (2 * Packed.chunkWidth d b + 2) + (d + 1).size + 2) + 2 := by omega
    _ = _ := by ring

/-- The selected packed representation satisfies the bound at every root-call clock. -/
theorem length_encCfg_packed_runFrom_le [Fact (Packed.fieldModulus d b).Prime]
    (hd : 0 < d) (hb : 0 < b) (T : Tree d b H)
    (e : (Fin b → Bool) → Fin (Packed.chunkCount d b) → ZMod (Packed.fieldModulus d b))
    (E : Gate d b → (Fin d → Fin (Packed.chunkCount d b) → ZMod (Packed.fieldModulus d b)) →
      Fin (Packed.chunkCount d b) → ZMod (Packed.fieldModulus d b))
    (us : List (ZMod (Packed.fieldModulus d b))ˣ)
    (S : Ary.State (ZMod (Packed.fieldModulus d b)) d (Packed.chunkCount d b))
    (c : ZMod (Packed.fieldModulus d b)) (t : Fin (d + 1)) (n : ℕ) :
    (encCfg (encPackedField d b)
      (runFrom hd e E us T.nodeAt (initialCfg S c t) n)).length ≤
      18 * (d + 1) * (b + Packed.chunkWidth d b) +
        2 * (H * (2 * frameBits d us.length (2 * Packed.chunkWidth d b + 2) + 1)) +
        4 * Packed.chunkWidth d b + (d + 1).size + 8 :=
  length_encCfg_packed_le hd hb _ (runFrom_initial_bounds T hd e E us S c t n)

/-- At most one round per field element keeps each frame logarithmic in the value width. -/
theorem frameBits_packed_le (hd : 0 < d) (hb : 0 < b) {rounds : ℕ}
    (hrounds : rounds ≤ Packed.fieldModulus d b) :
    frameBits d rounds (2 * Packed.chunkWidth d b + 2) ≤
      8 * Packed.chunkWidth d b + 2 * d.size + (d + 1).size + 14 := by
  have hsize := (Nat.size_le_size hrounds).trans (Packed.fieldModulus_size_le hd hb)
  unfold frameBits
  omega

/-- The complete packed state has linear bank size plus logarithmic control per tree level.
The explicit round-count premise holds for an enumeration without repeated field units. -/
theorem length_encCfg_packed_le_of_rounds_le (hd : 0 < d) (hb : 0 < b)
    (q : Cfg (ZMod (Packed.fieldModulus d b)) d (Packed.chunkCount d b)) {rounds : ℕ}
    (hq : ControlBounds H rounds q) (hrounds : rounds ≤ Packed.fieldModulus d b) :
    (encCfg (encPackedField d b) q).length ≤
      18 * (d + 1) * (b + Packed.chunkWidth d b) +
        2 * (H * (16 * Packed.chunkWidth d b + 4 * d.size + 2 * (d + 1).size + 29)) +
        4 * Packed.chunkWidth d b + (d + 1).size + 8 := by
  have hqsize := length_encCfg_packed_le hd hb q hq
  have hframe := frameBits_packed_le hd hb hrounds
  have hfactor : 2 * frameBits d rounds (2 * Packed.chunkWidth d b + 2) + 1 ≤
      16 * Packed.chunkWidth d b + 4 * d.size + 2 * (d + 1).size + 29 := by omega
  have hmul := Nat.mul_le_mul_left H hfactor
  omega

/-- The sharp representation bound holds at every clock when the rounds fit the field. -/
theorem length_encCfg_packed_runFrom_le_of_rounds_le [Fact (Packed.fieldModulus d b).Prime]
    (hd : 0 < d) (hb : 0 < b) (T : Tree d b H)
    (e : (Fin b → Bool) → Fin (Packed.chunkCount d b) → ZMod (Packed.fieldModulus d b))
    (E : Gate d b → (Fin d → Fin (Packed.chunkCount d b) → ZMod (Packed.fieldModulus d b)) →
      Fin (Packed.chunkCount d b) → ZMod (Packed.fieldModulus d b))
    (us : List (ZMod (Packed.fieldModulus d b))ˣ)
    (hus : us.length ≤ Packed.fieldModulus d b)
    (S : Ary.State (ZMod (Packed.fieldModulus d b)) d (Packed.chunkCount d b))
    (c : ZMod (Packed.fieldModulus d b)) (t : Fin (d + 1)) (n : ℕ) :
    (encCfg (encPackedField d b)
      (runFrom hd e E us T.nodeAt (initialCfg S c t) n)).length ≤
      18 * (d + 1) * (b + Packed.chunkWidth d b) +
        2 * (H * (16 * Packed.chunkWidth d b + 4 * d.size + 2 * (d + 1).size + 29)) +
        4 * Packed.chunkWidth d b + (d + 1).size + 8 :=
  length_encCfg_packed_le_of_rounds_le hd hb _
    (runFrom_initial_bounds T hd e E us S c t n) hus

end Cslib.TreeEval.Ary.Iter
