/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tableau.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# The gates of the uniform tableau within linear work space

The gate with number `g` of the tableau of a multi-tape machine for `T` steps on inputs of length
`n` (`Cslib.Circuits.Boolean.Tableau.gateCode`) is computable within work space linear in
the binary lengths of `n`, `T` and `g` (`Cslib.Circuits.Boolean.Tableau.gateCode_inSpace`): its
position is found by divisions with remainder, its operation and its references by tables of
constant size, and its wires by additions and multiplications. This is the uniformity of the
tableau, used to write the circuit down in logarithmic space.

## Main results

* `Cslib.Circuits.Boolean.Tableau.gateCode_inSpace`: the gate with a given number, within a budget
  covering the binary lengths of `n`, `T` and `g`.

## References

* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.7][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Tableau

open Turing MultiTapeTM ComputableTidilyInSpace

/-! ### The layout in normal form -/

section Layout

variable {k : ℕ} {State : Type} [Fintype State]

/-- The region of a position: the scan, the global gates, the global features, the column
features. -/
private def Loc.region : Loc k State → Fin 4
  | .scan _ => 0
  | .glob _ => 1
  | .gf .. => 2
  | .col .. => 3

/-- The number of gates of a column in the region of a position, `0` for the global regions. -/
private def Loc.mult : Loc k State → ℕ
  | .scan _ => scanWidth k
  | .col .. => colWidth k
  | _ => 0

/-- The position of a gate within its column or its region. -/
private noncomputable def Loc.lidx : Loc k State → ℕ
  | .scan l => l.idx
  | .glob l => l.idx
  | .gf f b j => gadgetIdx f.idx b j
  | .col f b j => gadgetIdx f.idx b j

variable (k State) in
/-- The start of a region within a block. -/
private def regionStart (T : ℕ) (i : Fin 4) : ℕ :=
  if i = 0 then 0 else if i = 1 then globStart k T else if i = 2 then gfStart k State T
  else colStart k State T

private theorem Loc.offset_eq (T c : ℕ) (l : Loc k State) :
    l.offset T c = regionStart k State T l.region + c * l.mult + l.lidx := by
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩ <;>
    simp [Loc.offset, Loc.region, Loc.mult, Loc.lidx, regionStart]

/-- The kind of a reference: the constants, the input bit, a position. -/
private def Ref.kind : Ref k State → Fin 4
  | .fls => 0
  | .tru => 1
  | .inp => 2
  | .node .. => 3

/-- Whether a reference reads the previous block. -/
private def Ref.prevOf : Ref k State → Bool
  | .node p _ _ _ => p
  | _ => false

/-- The position read by a reference. -/
private def Ref.locOf : Ref k State → Loc k State
  | .node _ l _ _ => l
  | _ => .scan .nx

/-- The column selection of a reference. -/
private def Ref.csOf : Ref k State → ColSel
  | .node _ _ cs _ => cs
  | _ => .same

/-- The guard of a reference. -/
private def Ref.guardOf : Ref k State → Guard
  | .node _ _ _ g => g
  | _ => .always

/-- A guard from the comparisons `1 ≤ c`, `c + 1 < 2 T + 1`, `c ≤ n`, `c = 0`, `c = n + 1` and
`c ≤ n + 1` of the column. -/
private def Guard.ofTests : Guard × Bool × Bool × Bool × Bool × Bool × Bool → Bool
  | (.always, _) => true
  | (.pos, b₁, _) => b₁
  | (.ltLast, _, b₂, _) => b₂
  | (.inRange, b₁, _, b₃, _) => b₁ && b₃
  | (.outRange, b₁, _, b₃, _) => !(b₁ && b₃)
  | (.isZero, _, _, _, b₄, _) => b₄
  | (.isEnd, _, _, _, _, b₅, _) => b₅
  | (.leEnd, b₁, _, _, _, _, b₆) => b₁ && b₆

private theorem Guard.test_eq (g : Guard) (n T c : ℕ) :
    g.test n T c = Guard.ofTests (g, decide (0 < c), decide (c + 1 < 2 * T + 1),
      decide (c < n + 1), decide (c = 0), decide (c = n + 1), decide (c < n + 2)) := by
  rcases g <;> simp [Guard.test, Guard.ofTests, numCols, Nat.lt_succ_iff, Nat.one_le_iff_ne_zero,
    Nat.pos_iff_ne_zero]

private theorem ColSel.apply_eq (cs : ColSel) (T c : ℕ) :
    cs.apply T c = if cs = .same then c else if cs = .prev then c - 1 else if cs = .next then c + 1
      else 2 * T := by
  rcases cs <;> rfl

/-- The wire of a reference, in normal form. -/
private theorem Ref.resolve_eq (r : Ref k State) (n T t c : ℕ) :
    r.resolve n T t c =
      if r.kind = 0 then n else if r.kind = 1 then n + 1
      else if r.kind = 2 then (if decide (0 < c) && decide (c < n + 1) then c - 1 else n)
      else if Guard.ofTests (r.guardOf, decide (0 < c), decide (c + 1 < 2 * T + 1),
          decide (c < n + 1), decide (c = 0), decide (c = n + 1), decide (c < n + 2)) then
        n + 2 + (if r.prevOf then t - 1 else t) * blockSize k State T +
          (regionStart k State T r.locOf.region + r.csOf.apply T c * r.locOf.mult + r.locOf.lidx)
      else n := by
  rcases r with _ | _ | _ | ⟨p, l, cs, g⟩
  · rfl
  · rfl
  · simp only [Ref.resolve, Ref.kind]
    by_cases h : 1 ≤ c ∧ c ≤ n
    · simp [h, Nat.one_le_iff_ne_zero.mp h.1, Nat.pos_iff_ne_zero]
    · have : ¬(0 < c ∧ c < n + 1) := by omega
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, h, Bool.and_eq_true, decide_eq_true_eq,
        this]
  · simp only [Ref.resolve, Ref.kind, Ref.guardOf, Ref.prevOf, Ref.locOf, Ref.csOf, wire,
      Loc.offset_eq, ← Guard.test_eq, Fin.isValue, Fin.reduceEq, ↓reduceIte]
    cases p <;> rfl

end Layout

/-! ### The gates within a budget -/

section Budget

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State)
variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}

omit [DecidableEq State] in
private theorem globWidth_pos : 0 < globWidth k State := by
  have : 0 < Fintype.card (Attr k State) := Fintype.card_pos_iff.2 ⟨.inMove 0⟩
  simp only [globWidth]
  have := Nat.mul_le_mul_right (numSit k State + 1) (Nat.one_le_iff_ne_zero.2 this.ne')
  omega

omit [DecidableEq State] in
private theorem gfWidth_pos : 0 < gfWidth State := by simp only [gfWidth]; omega

omit [DecidableEq State] in
private theorem colWidth_pos : 0 < colWidth k := by simp only [colWidth]; omega

section Layout

variable {T : α → ℕ} (hT : ComputableTidilyInSpace T encIn encNat Bs)
  (hin : (fun x => (encIn x).length) ≼ Bs)
include hT hin

omit [DecidableEq State] in
private theorem numCols_inSpace :
    ComputableTidilyInSpace (fun x => numCols (T x)) encIn encNat Bs :=
  budget_natAdd (budget_natMul (budget_const 2 hin) hT) (budget_const 1 hin)

omit [DecidableEq State] in
private theorem globStart_inSpace :
    ComputableTidilyInSpace (fun x => globStart k (T x)) encIn encNat Bs :=
  budget_natMul (numCols_inSpace hT hin) (budget_const (scanWidth k) hin)

omit [DecidableEq State] in
omit hT hin in
/-- Computing `gfStart k State (T x)` within space budget `Bs`. -/
theorem gfStart_inSpace (hT : ComputableInSpace T encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableInSpace (fun x => gfStart k State (T x)) encIn encNat Bs := by
  have hT := hT.tidy
  refine .of_tidy ?_
  exact budget_natAdd (globStart_inSpace (k := k) hT hin) (budget_const _ hin)

omit [DecidableEq State] in
private theorem colStart_inSpace :
    ComputableTidilyInSpace (fun x => colStart k State (T x)) encIn encNat Bs :=
  budget_natAdd (gfStart_inSpace (k := k) (State := State) (.of_tidy hT) hin).tidy (budget_const
    _ hin)

omit [DecidableEq State] in
omit hT hin in
/-- Computing `blockSize k State (T x)` within space budget `Bs`. -/
theorem blockSize_inSpace (hT : ComputableInSpace T encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableInSpace (fun x => blockSize k State (T x)) encIn encNat Bs := by
  have hT := hT.tidy
  refine .of_tidy ?_
  exact budget_natAdd (colStart_inSpace (k := k) (State := State) hT hin)
    (budget_natMul (numCols_inSpace hT hin) (budget_const _ hin))

/-- Explicit finite enumeration of `ColSel`. -/
instance : FinEnum ColSel :=
  FinEnum.ofList [.same, .prev, .next, .last] fun x => by cases x <;> decide

/-- Explicit finite enumeration of `Guard`. -/
instance : FinEnum Guard :=
  FinEnum.ofList [.always, .pos, .ltLast, .inRange, .outRange, .isZero, .isEnd, .leEnd]
    fun x => by cases x <;> decide

omit [DecidableEq State] in
private theorem regionStart_inSpace {i : α → Fin 4}
    (hi : ComputableTidilyInSpace i encIn (encFinEnum (Fin 4)) Bs) :
    ComputableTidilyInSpace (fun x => regionStart k State (T x) (i x)) encIn encNat Bs := by
  have h₀ := budget_finite (encC := encBool) (fun j : Fin 4 => decide (j = 0)) hi
  have h₁ := budget_finite (encC := encBool) (fun j : Fin 4 => decide (j = 1)) hi
  have h₂ := budget_finite (encC := encBool) (fun j : Fin 4 => decide (j = 2)) hi
  refine (budget_ite h₀ (budget_const (encB := encNat) 0 hin)
    (budget_ite h₁ (globStart_inSpace (k := k) hT hin)
      (budget_ite h₂ (gfStart_inSpace (k := k) (State := State) (.of_tidy hT) hin).tidy
      (colStart_inSpace (k := k) (State := State) hT hin)))).of_enc_eq fun x => ?_
  simp only [regionStart, decide_eq_true_eq]

end Layout

section Resolve

variable {n T t c : α → ℕ} (hn : ComputableTidilyInSpace n encIn encNat Bs)
  (hT : ComputableTidilyInSpace T encIn encNat Bs)
  (ht : ComputableTidilyInSpace t encIn encNat Bs)
  (hc : ComputableTidilyInSpace c encIn encNat Bs)
  (hin : (fun x => (encIn x).length) ≼ Bs)
include hn hT ht hc hin

omit [DecidableEq State] in
/-- **The wire of a reference**, within a budget. -/
private theorem resolve_inSpace {r : α → Ref k State}
    (hr : ComputableTidilyInSpace r encIn (encFinite (Ref k State)) Bs) :
    ComputableTidilyInSpace (fun x => (r x).resolve (n x) (T x) (t x) (c x)) encIn encNat Bs := by
  have hk (i : Fin 4) :=
    budget_finite (encC := encBool) (fun r : Ref k State => decide (r.kind = i)) hr
  have hc0 := budget_natLt (budget_const (encB := encNat) 0 hin) hc
  have hcn := budget_natLt hc (budget_natAdd hn (budget_const 1 hin))
  have hcT := budget_natLt (budget_natAdd hc (budget_const 1 hin))
    (budget_natAdd (budget_natMul (budget_const 2 hin) hT) (budget_const 1 hin))
  have hcz := budget_natEq hc (budget_const (encB := encNat) 0 hin)
  have hce := budget_natEq hc (budget_natAdd hn (budget_const 1 hin))
  have hcn2 := budget_natLt hc (budget_natAdd hn (budget_const 2 hin))
  -- the input bit
  have hinpc := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hc0 hcn)
  have hinp := budget_ite hinpc (budget_natSub hc (budget_const 1 hin)) hn
  -- the guard
  have hg := budget_finite (encC := encBool) Guard.ofTests
    (budget_prod (budget_finite (encC := encFinEnum Guard) Ref.guardOf hr)
      (budget_prod hc0 (budget_prod hcT (budget_prod hcn (budget_prod hcz
        (budget_prod hce hcn2))))))
  -- the position
  have hloc := budget_finite (encC := encFinite (Loc k State)) Ref.locOf hr
  have hprev := budget_finite (encC := encBool) Ref.prevOf hr
  have ht' := budget_ite hprev (budget_natSub ht (budget_const 1 hin)) ht
  have hreg := regionStart_inSpace (k := k) (State := State) hT hin
    (budget_finite (encC := encFinEnum (Fin 4)) Loc.region hloc)
  have hcs := budget_finite (encC := encFinEnum ColSel) Ref.csOf hr
  have hcs₀ := budget_finite (encC := encBool) (fun cs : ColSel => decide (cs = .same)) hcs
  have hcs₁ := budget_finite (encC := encBool) (fun cs : ColSel => decide (cs = .prev)) hcs
  have hcs₂ := budget_finite (encC := encBool) (fun cs : ColSel => decide (cs = .next)) hcs
  have hcol := budget_ite hcs₀ hc (budget_ite hcs₁ (budget_natSub hc (budget_const 1 hin))
    (budget_ite hcs₂ (budget_natAdd hc (budget_const 1 hin))
      (budget_natMul (budget_const 2 hin) hT)))
  have hmult := budget_finite (encC := encNat) Loc.mult hloc
  have hlidx := budget_finite (encC := encNat) Loc.lidx hloc
  have hwire := budget_natAdd (budget_natAdd (budget_natAdd hn (budget_const 2 hin))
    (budget_natMul ht' (blockSize_inSpace (k := k) (State := State) (.of_tidy hT) hin).tidy))
    (budget_natAdd (budget_natAdd hreg (budget_natMul hcol hmult)) hlidx)
  refine (budget_ite (hk 0) hn (budget_ite (hk 1) (budget_natAdd hn (budget_const 1 hin))
    (budget_ite (hk 2) hinp (budget_ite hg hwire hn)))).of_enc_eq fun x => ?_
  rw [Ref.resolve_eq, ColSel.apply_eq]
  simp only [decide_eq_true_eq]

end Resolve

/-- Whether an operation is a constant. -/
private def opIsConst : Op → Bool
  | .const _ => true
  | _ => false

private theorem argsOf_eq (op : Op) (a b : ℕ) :
    argsOf op a b = if opIsConst op then [] else if decide (op = .not) then [a] else [a, b] := by
  cases op <;> rfl

/-- The initial value of a column feature from the comparisons `c = 1` and `c = T`. -/
private def colInitOf : ColFeat k × Bool × Bool → Bool
  | (.inPos, b₁, _) => b₁
  | (.head _, _, bT) => bT
  | (.cell _ s, _, _) => decide (s = none)

/-- The initial constant of a position from the comparisons `c = 1` and `c = T`. -/
private def initBitOf : Loc k State × Bool × Bool → Bool
  | (.gf f true j, _, _) => decide (j = 7) && gfInit tm f
  | (.col f true j, b₁, bT) => decide (j = 7) && colInitOf (f, b₁, bT)
  | _ => false

private theorem initBit_eq (T c : ℕ) (l : Loc k State) :
    initBit tm T c l = initBitOf tm (l, decide (c = 1), decide (c = T)) := by
  rcases l with l | l | ⟨f, (_ | _), j⟩ | ⟨f, (_ | _), j⟩ <;> try rfl
  rcases f with _ | i | ⟨i, s⟩ <;> rfl

section Gate

variable {n T t c : α → ℕ} (hn : ComputableTidilyInSpace n encIn encNat Bs)
  (hT : ComputableTidilyInSpace T encIn encNat Bs)
  (hin : (fun x => (encIn x).length) ≼ Bs)
include hn hT hin

/-- **The gate at a position**, within a budget. -/
private theorem gateAt_inSpace (ht : ComputableTidilyInSpace t encIn encNat Bs)
    (hc : ComputableTidilyInSpace c encIn encNat Bs) {l : α → Loc k State}
    (hl : ComputableTidilyInSpace l encIn (encFinite (Loc k State)) Bs) :
    ComputableTidilyInSpace (fun x => gateAt tm (n x) (T x) (t x) (c x) (l x)) encIn encGate
      Bs := by
  have ht0 := budget_natEq ht (budget_const (encB := encNat) 0 hin)
  have hc1 := budget_natEq hc (budget_const (encB := encNat) 1 hin)
  have hcT := budget_natEq hc hT
  have hinit := budget_finite (encC := encOp)
    (fun p : Loc k State × Bool × Bool => Op.const (initBitOf tm p))
    (budget_prod hl (budget_prod hc1 hcT))
  have hop := budget_finite (encC := encOp) (fun l => (table tm l).1) hl
  have hr₁ := resolve_inSpace hn hT ht hc hin
    (budget_finite (encC := encFinite (Ref k State)) (fun l => (table tm l).2.1) hl)
  have hr₂ := resolve_inSpace hn hT ht hc hin
    (budget_finite (encC := encFinite (Ref k State)) (fun l => (table tm l).2.2) hl)
  have hk₀ := budget_finite (encC := encBool) (fun l => opIsConst (table tm l).1) hl
  have hk₁ := budget_finite (encC := encBool) (fun l => decide ((table tm l).1 = .not)) hl
  have hnil := budget_const (encB := encList encNat) ([] : List ℕ) hin
  have hargs := budget_ite hk₀ hnil (budget_ite hk₁ (budget_cons hr₁ hnil)
    (budget_cons hr₁ (budget_cons hr₂ hnil)))
  refine (budget_prod (budget_ite ht0 hinit hop) (budget_ite ht0 hnil hargs)).of_enc_eq
    fun x => ?_
  congr 1
  by_cases h : t x = 0
  · simp [gateAt, h, initBit_eq]
  · simp [gateAt, h, argsOf_eq]

omit hn hT hin in
/-- **The gate with a given number**, within a budget covering `n`, `T` and the number. -/
theorem gateCode_inSpace (hn : ComputableInSpace n encIn encNat Bs) (hT : ComputableInSpace T
    encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs) {g : α → ℕ} (hg : ComputableInSpace g encIn encNat
      Bs) :
    ComputableInSpace (fun x => gateCode tm (n x) (T x) (g x)) encIn encGate Bs := by
  have hT := hT.tidy
  have hn := hn.tidy
  have hg := hg.tidy
  refine .of_tidy ?_
  have hB := (blockSize_inSpace (k := k) (State := State) (.of_tidy hT) hin).tidy
  have hgm := budget_natSub hg (budget_const (encB := encNat) 2 hin)
  have ht := budget_natDiv hgm hB
  have hr := budget_natMod hgm hB
  have hgs := globStart_inSpace (k := k) hT hin
  have hgf := (gfStart_inSpace (k := k) (State := State) (.of_tidy hT) hin).tidy
  have hcs := colStart_inSpace (k := k) (State := State) hT hin
  have hr₁ := budget_natLt hr hgs
  have hr₂ := budget_natLt hr hgf
  have hr₃ := budget_natLt hr hcs
  have hcol := budget_ite hr₁ (budget_natDiv hr (budget_const (encB := encNat) (scanWidth k) hin))
    (budget_ite hr₃ (budget_const (encB := encNat) 0 hin)
      (budget_natDiv (budget_natSub hr hcs) (budget_const (encB := encNat) (colWidth k) hin)))
  have hlS := budget_finite (encC := encFinite (Loc k State))
    (fun i : Fin (scanWidth k) => Loc.scan (ScanLoc.ofIdx i.val))
    (budget_finMod scanWidth_pos hr hin)
  have hlG := budget_finite (encC := encFinite (Loc k State))
    (fun i : Fin (globWidth k State) => Loc.glob (GlobLoc.ofIdx i.val))
    (budget_finMod globWidth_pos (budget_natSub hr hgs) hin)
  have hlF := budget_finite (encC := encFinite (Loc k State))
    (fun i : Fin (gfWidth State) =>
      (Loc.gf (GFeat.ofIdx (i.val / 16)) (gadgetB i.val) (gadgetJ i.val) : Loc k State))
    (budget_finMod gfWidth_pos (budget_natSub hr hgf) hin)
  have hlC := budget_finite (encC := encFinite (Loc k State))
    (fun i : Fin (colWidth k) =>
      (Loc.col (ColFeat.ofIdx (i.val / 16)) (gadgetB i.val) (gadgetJ i.val) : Loc k State))
    (budget_finMod colWidth_pos (budget_natSub hr hcs) hin)
  have hloc := budget_ite hr₁ hlS (budget_ite hr₂ hlG (budget_ite hr₃ hlF hlC))
  have hgate := gateAt_inSpace tm hn hT hin ht hcol hloc
  have hsmall := budget_natLt hg (budget_const (encB := encNat) 2 hin)
  have hone := budget_finite (encC := encOp) (fun b : Bool => Op.const b)
    (budget_natEq hg (budget_const (encB := encNat) 1 hin))
  refine (budget_ite hsmall (budget_prod hone (budget_const (encB := encList encNat) [] hin))
    hgate).of_enc_eq fun x => ?_
  congr 1
  have hgs' : globStart k (T x) ≤ gfStart k State (T x) := Nat.le_add_right _ _
  have hgc' : gfStart k State (T x) ≤ colStart k State (T x) := Nat.le_add_right _ _
  simp only [gateCode, decide_eq_true_eq]
  have hgw : gfStart k State (T x) = globStart k (T x) + globWidth k State := rfl
  have hcw : colStart k State (T x) = gfStart k State (T x) + gfWidth State := rfl
  split_ifs with h₀ h₁ h₂ h₃ h₄
  all_goals first
    | rfl
    | (exfalso; omega)
    | rw [Nat.mod_eq_of_lt (a := (g x - 2) % blockSize k State (T x) - globStart k (T x))
        (by omega)]
    | rw [Nat.mod_eq_of_lt (a := (g x - 2) % blockSize k State (T x) - gfStart k State (T x))
        (by omega)]

end Gate

end Budget

end Cslib.Circuits.Boolean.Tableau
