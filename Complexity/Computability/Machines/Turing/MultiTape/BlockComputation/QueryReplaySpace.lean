/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplay
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
import Complexity.Foundations.Data.List.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Binary storage for the local replay query machine

Only the fixed control and output tags use finite encodings. Runtime window widths, counters,
input positions and head positions use binary encodings, and every window cell is stored
explicitly. No original input word occurs in the storage encoding.

`length_encConfig_le` bounds this representation by the local window width and the logarithm of
the original input length. All five native query-machine component certificates use the same
representation, including the step that updates each explicit local tape.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay

open MultiTapeTM MultiTapeTM.ComputableInSpace MultiTapeNTM.ChoiceTable
open MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {Q : Type}

/-- The replay storage as a tuple of runtime fields. -/
@[expose] def Config.equivProd : Config k Q ≃
    ℕ × ℕ × ℕ × ℕ × Option Q × (Fin k → ℕ) × (Fin k → List ℕ) × OutputTrack where
  toFun s := (s.inputLength, s.width, s.remaining, s.inputPos, s.control, s.heads, s.cells, s.track)
  invFun := fun (inputLength, width, remaining, inputPos, control, heads, cells, track) =>
    ⟨inputLength, width, remaining, inputPos, control, heads, cells, track⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite Q]

/-- Binary numeric fields and explicit fixed families of local work cells. -/
noncomputable def encConfig : Config k Q ↪ List Bool :=
  encOfEquiv Config.equivProd (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair (encFinite (Option Q)) (encPair (encPi encNat)
      (encPair (encPi (encList encNat)) (encFinite OutputTrack))))))))

private theorem config_parts : ComputableInSpace (Config.equivProd (k := k) (Q := Q))
    encConfig (encPair encNat (encPair encNat (encPair encNat
      (encPair encNat (encPair (encFinite (Option Q)) (encPair (encPi encNat)
        (encPair (encPi (encList encNat)) (encFinite OutputTrack))))))))
    (fun s => (encConfig s).length) :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

/-- The runtime input length can be read in linear encoded-state space. -/
theorem inputLength_inSpace : ComputableInSpace (Config.inputLength (k := k) (Q := Q))
    encConfig encNat (fun s => (encConfig s).length) := config_parts.fst'

/-- The runtime block width can be read in linear encoded-state space. -/
theorem width_inSpace : ComputableInSpace (Config.width (k := k) (Q := Q))
    encConfig encNat (fun s => (encConfig s).length) := config_parts.snd'.fst'

/-- The remaining replay duration can be read in linear encoded-state space. -/
theorem remaining_inSpace : ComputableInSpace (Config.remaining (k := k) (Q := Q))
    encConfig encNat (fun s => (encConfig s).length) := config_parts.snd'.snd'.fst'

/-- The original input pointer can be read in linear encoded-state space. -/
theorem inputPos_inSpace : ComputableInSpace (Config.inputPos (k := k) (Q := Q))
    encConfig encNat (fun s => (encConfig s).length) := config_parts.snd'.snd'.snd'.fst'

/-- Native original-input query component. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) :
    ComputableInSpace (machine M).query encConfig encNat (fun s => (encConfig s).length) :=
  budget_natPred inputPos_inSpace

/-- Native duration-zero stopping test. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) :
    ComputableInSpace (machine M).halted encConfig encBool (fun s => (encConfig s).length) :=
  budget_natIsZero remaining_inSpace

/-- Native silent emission component; accumulated output is never copied into storage. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) :
    ComputableInSpace (machine M).emit (encPair encConfig (encOption encBool)) encBits
      (fun p => (encPair encConfig (encOption encBool) p).length) :=
  budget_const [] (.refl _)

/-- Native silent final-output component. The caller reads the returned state separately. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) :
    ComputableInSpace (machine M).finish encConfig encBits (fun s => (encConfig s).length) :=
  budget_const [] (.refl _)

/-- Explicit storage bound for valid local replay data. The coefficient depends only on the
fixed tape count and finite tags; the original input contributes only its logarithm. -/
theorem length_encConfig_le (s : Config k Q)
    (hremaining : s.remaining ≤ s.width) (hinput : s.inputPos ≤ s.inputLength + 1)
    (hheads : ∀ h, s.heads h ≤ 3 * s.width)
    (hcells : ∀ h, (s.cells h).length ≤ 3 * s.width)
    (hcodes : ∀ h n, n ∈ s.cells h → n ≤ 2) :
    (encConfig s).length ≤ 1024 * (k + 1) *
      (s.width + Nat.log2 s.inputLength + Nat.card (Option Q) + Nat.card OutputTrack + 1) := by
  have hnat (n : ℕ) : (encNat n).length ≤ n := by
    rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
    exact Nat.lt_two_pow_self
  have hN := length_encNat_le_log2 (j := s.inputLength) le_rfl
  have hb := hnat s.width
  have hr := (hnat s.remaining).trans hremaining
  have hi := length_encNat_le_log2_add_two hinput
  have hq := (length_encFinite_lt s.control).le
  have ht := (length_encFinite_lt s.track).le
  have hh : (encPi encNat s.heads).length ≤ k * (6 * s.width + 1) := by
    simpa only [Fintype.card_fin, ← Nat.mul_assoc] using length_encPi_le encNat s.heads
      (fun h => (hnat (s.heads h)).trans (hheads h))
  have hw : (encPi (encList encNat) s.cells).length ≤ k * (30 * s.width + 1) := by
    have hl (h : Fin k) : (encList encNat (s.cells h)).length ≤ 15 * s.width := by
      have hl' := length_encList_le encNat (s.cells h)
        (fun n hn => (hnat n).trans (hcodes h n hn))
      nlinarith [hcells h]
    simpa only [Fintype.card_fin, ← Nat.mul_assoc] using length_encPi_le (encList encNat) s.cells hl
  change (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair (encFinite (Option Q)) (encPair (encPi encNat)
      (encPair (encPi (encList encNat)) (encFinite OutputTrack)))))))
      (Config.equivProd s)).length ≤ _
  simp only [length_encPair, Config.equivProd, Equiv.coe_fn_mk]
  nlinarith

private theorem finiteCases {α β Tag : Type} [Finite Tag]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {tagEncoding : Tag ↪ List Bool}
    {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableInSpace tag input tagEncoding (fun a => (input a).length))
    (hbranch : ∀ choice, ComputableInSpace (branch choice) input output
      (fun a => (input a).length)) :
    ComputableInSpace (fun a => branch (tag a) a) input output
      (fun a => (input a).length) := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    exact of_finite _
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableInSpace (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) input output (fun a => (input a).length) := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih =>
        have htest := budget_finite (encC := encBool) (fun t : Tag => decide (t = choice)) htag
        simpa only [List.foldr_cons, Bool.decide_iff] using
          (budget_ite htest (hbranch choice) ih)
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

private theorem piLinear {α Index Value : Type} [Fintype Index]
    {input : α ↪ List Bool} {enc : Value ↪ List Bool} {values : α → Index → Value}
    (hvalues : ∀ i, ComputableInSpace (fun a => values a i) input enc
      (fun a => (input a).length)) :
    ComputableInSpace values input (encPi enc) (fun a => (input a).length) := by
  classical
  choose T hT using fun i => (hvalues i).exists_inO
  refine (of_inO (ComputableInO.pi hT)).weaken ?_
  exact ⟨Fintype.card Index + 1, fun a => by simp; nlinarith⟩

private theorem piApplyLinear {Index Value : Type} [Fintype Index]
    (enc : Value ↪ List Bool) (i : Index) :
    ComputableInSpace (fun q : Index → Value => q i) (encPi enc) enc
      (fun q => (encPi enc q).length) :=
  of_inO (ComputableInO.pi_apply enc i)

private theorem control_inSpace : ComputableInSpace (Config.control (k := k) (Q := Q))
    encConfig (encFinite (Option Q)) (fun s => (encConfig s).length) :=
  config_parts.snd'.snd'.snd'.snd'.fst'

private theorem heads_inSpace : ComputableInSpace (Config.heads (k := k) (Q := Q))
    encConfig (encPi encNat) (fun s => (encConfig s).length) :=
  config_parts.snd'.snd'.snd'.snd'.snd'.fst'

private theorem cells_inSpace : ComputableInSpace (Config.cells (k := k) (Q := Q))
    encConfig (encPi (encList encNat)) (fun s => (encConfig s).length) :=
  config_parts.snd'.snd'.snd'.snd'.snd'.snd'.fst'

private theorem track_inSpace : ComputableInSpace (Config.track (k := k) (Q := Q))
    encConfig (encFinite OutputTrack) (fun s => (encConfig s).length) :=
  config_parts.snd'.snd'.snd'.snd'.snd'.snd'.snd'

private theorem cellOfCode_inSpace : ComputableInSpace cellOfCode encNat
    (encFinite (Option Bool)) (fun n => (encNat n).length) := by
  have hid : ComputableInSpace (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) := of_inO ComputableInDegree.id'.inO_one
  refine (budget_ite (budget_natEq hid (budget_const 1 (.refl _)))
    (budget_const (encB := encFinite (Option Bool)) (some false) (.refl _))
    (budget_ite (budget_natEq hid (budget_const 2 (.refl _)))
      (budget_const (encB := encFinite (Option Bool)) (some true) (.refl _))
      (budget_const (encB := encFinite (Option Bool)) none (.refl _)))).of_enc_eq ?_
  intro n
  simp only [cellOfCode, Bool.decide_iff]

/-- Reading the symbols uses finite tuples only for the fixed number of tapes. -/
theorem symbols_inSpace : ComputableInSpace (symbols (k := k) (Q := Q)) encConfig
    (encPi (encFinite (Option Bool))) (fun s => (encConfig s).length) := by
  refine piLinear fun h => ?_
  have hh := budget_comp_linear (piApplyLinear encNat h) (heads_inSpace (k := k) (Q := Q))
  have hc := budget_comp_linear (piApplyLinear (encList encNat) h) (cells_inSpace (k := k) (Q := Q))
  have hread := budget_comp_lin getD (linear_mul 8) (budget_prod hc hh)
  exact budget_comp_linear cellOfCode_inSpace hread

private theorem configMk {α : Type} {input : α ↪ List Bool} {S : α → ℕ}
    {N b r p : α → ℕ} {q : α → Option Q} {heads : α → Fin k → ℕ}
    {cells : α → Fin k → List ℕ} {track : α → OutputTrack}
    (hN : ComputableInSpace N input encNat S)
    (hb : ComputableInSpace b input encNat S)
    (hr : ComputableInSpace r input encNat S)
    (hp : ComputableInSpace p input encNat S)
    (hq : ComputableInSpace q input (encFinite (Option Q)) S)
    (hh : ComputableInSpace heads input (encPi encNat) S)
    (hc : ComputableInSpace cells input (encPi (encList encNat)) S)
    (ht : ComputableInSpace track input (encFinite OutputTrack) S) :
    ComputableInSpace (fun a => (⟨N a, b a, r a, p a, q a, heads a, cells a, track a⟩ :
      Config k Q)) input encConfig S :=
  (budget_prod hN (budget_prod hb (budget_prod hr (budget_prod hp
    (budget_prod hq (budget_prod hh (budget_prod hc ht))))))).of_enc_eq fun _ => rfl

private theorem fixedActionTick_inSpace (a : Option (Action k Bool Q)) :
    ComputableInSpace (fun s : Config k Q =>
      { a.elim s (applyAction s) with remaining := s.remaining - 1 })
      encConfig encConfig (fun s => (encConfig s).length) := by
  cases a with
  | none =>
    exact configMk inputLength_inSpace width_inSpace (budget_natPred remaining_inSpace)
      inputPos_inSpace control_inSpace heads_inSpace cells_inSpace track_inSpace
  | some a =>
    have hp : ComputableInSpace (fun s : Config k Q =>
        MultiTapeNTM.ConfigurationGraph.inputMove s.inputLength s.inputPos a.inputTape)
        encConfig encNat (fun s => (encConfig s).length) := by
      cases hd : a.inputTape with
      | neg => exact budget_natPred inputPos_inSpace
      | zero => exact inputPos_inSpace
      | pos =>
        have hpos := budget_natSucc (inputPos_inSpace (k := k) (Q := Q))
        have hN := budget_natSucc (inputLength_inSpace (k := k) (Q := Q))
        refine (budget_ite (budget_natLt hpos hN) hpos hN).of_enc_eq ?_
        intro s
        simp only [MultiTapeNTM.ConfigurationGraph.inputMove, Bool.decide_iff]
        congr 1
        split <;> omega
    have hh : ComputableInSpace (fun s : Config k Q =>
        fun h => move (s.heads h) (a.workTapes h).2) encConfig (encPi encNat)
        (fun s => (encConfig s).length) := by
      refine piLinear fun h => ?_
      have hhead := budget_comp_linear (piApplyLinear encNat h)
        (heads_inSpace (k := k) (Q := Q))
      cases (a.workTapes h).2 with
      | neg => exact budget_natPred hhead
      | zero => exact hhead
      | pos => exact budget_natSucc hhead
    have hc : ComputableInSpace (fun s : Config k Q => fun h =>
        match (a.workTapes h).1 with
        | none => s.cells h
        | some b => (s.cells h).set (s.heads h) (symbolCode b))
        encConfig (encPi (encList encNat)) (fun s => (encConfig s).length) := by
      refine piLinear fun h => ?_
      have hcell := budget_comp_linear (piApplyLinear (encList encNat) h)
        (cells_inSpace (k := k) (Q := Q))
      have hhead := budget_comp_linear (piApplyLinear encNat h)
        (heads_inSpace (k := k) (Q := Q))
      cases hw : (a.workTapes h).1 with
      | none => exact hcell
      | some b =>
        exact budget_comp_lin set (linear_mul 128)
          (budget_prod hcell (budget_prod hhead (budget_const (symbolCode b) (.refl _))))
    have ht := budget_finite (encC := encFinite OutputTrack) (fun t : OutputTrack =>
      t.emit a.output) (track_inSpace (k := k) (Q := Q))
    exact configMk inputLength_inSpace width_inSpace (budget_natPred remaining_inSpace)
      hp (budget_const a.state (.refl _)) hh hc ht

/-- Native step component. Transition lookup ranges only over fixed finite control, input
symbols and the fixed tuple of work symbols; the windows themselves remain explicit lists. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) :
    ComputableInSpace (machine M).next (encPair encConfig (encOption encBool)) encConfig
      (fun p => (encPair encConfig (encOption encBool) p).length) := by
  classical
  have hs := fst (encConfig (k := k) (Q := Q)) (encOption encBool)
  have hsymbol := snd (encConfig (k := k) (Q := Q)) (encOption encBool)
  have hN := budget_comp_linear inputLength_inSpace hs
  have hp := budget_comp_linear inputPos_inSpace hs
  have hcontrol := budget_comp_linear control_inSpace hs
  have hsymbols := budget_comp_linear symbols_inSpace hs
  have hsymbols' := budget_finite (encC := encFinite (Fin k → Option Bool))
    (fun x : Fin k → Option Bool => x) hsymbols
  have hsymbol' := budget_finite (encC := encFinite (Option Bool))
    (fun x : Option Bool => x) hsymbol
  have hleft := budget_natIsZero hp
  have hright := budget_natEq hp (budget_natSucc hN)
  have hboundary := budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 || q.2)
    (budget_prod hleft hright)
  have hread := budget_ite hboundary (budget_const none (.refl _)) hsymbol'
  have ha := budget_finite (encC := encFinite (Option (Action k Bool Q)))
    (fun q : Option Q × Option Bool × (Fin k → Option Bool) =>
      q.1.map (fun c => M.tr c q.2.1 q.2.2))
    (budget_prod hcontrol (budget_prod hread hsymbols'))
  have hbranches (a : Option (Action k Bool Q)) :=
    budget_comp_linear (fixedActionTick_inSpace a) hs
  refine (finiteCases ha hbranches).of_enc_eq ?_
  intro p
  simp only [machine, tick]
  have hread_eq : (if (decide (p.1.inputPos = 0) ||
      decide (p.1.inputPos = p.1.inputLength + 1)) then none else p.2) =
      MultiTapeNTM.ConfigurationGraph.inputSymbol p.1.inputLength p.1.inputPos p.2 := by
    simp only [MultiTapeNTM.ConfigurationGraph.inputSymbol, Bool.or_eq_true,
      Bool.decide_iff]
  rw [hread_eq]
  cases p.1.control <;> rfl

end Turing.MultiTapePTM.BlockComputation.QueryReplay
