/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORGuard

/-!
# Recovering subset choices from unrestricted guard chains

The inductive soundness argument of [WangLvShenZhang2027], Theorem 1
(PDF pp. 10–11). Guards are actual alternating operands, not constrained
operators. `recover_guarded_chain` recovers a subsequence of the actual block
weights from an arbitrary successful operator word. Its field hypotheses are
local arithmetic conditions; no hardness, reduction or recovery conclusion is
a hypothesis. The construction of the numerical fields and its resource bounds
are separate obligations.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR
open scoped List

/-- An alternating four-operand block and the position of its guard. -/
structure GuardBlock (m : ℕ) where
  /-- Lowest bit of the four-bit guard. -/
  position : ℕ
  /-- First and third operand. -/
  first : BitVec m
  /-- Second and fourth operand. -/
  second : BitVec m

namespace GuardBlock

/-- All four operands, with no restriction on their operators. -/
@[expose] def operands {m : ℕ} (g : GuardBlock m) : List (BitVec m) :=
  [g.first, g.second, g.first, g.second]

/-- The increment when all four operators are additions. -/
@[expose] def weight {m : ℕ} (g : GuardBlock m) : BitVec m :=
  (g.first + g.second) + (g.first + g.second)

end GuardBlock

/-- Concatenate the operands of a list of guard blocks. -/
@[expose] def guardedOperands {m : ℕ} (gs : List (GuardBlock m)) : List (BitVec m) :=
  gs.flatMap GuardBlock.operands

/-- Equal low fields remain equal under a further downward projection. -/
theorem project_eq_of_low_eq {m K p : ℕ} (hp : p ≤ K)
    {s t : BitVec m} (h : s.setWidth K = t.setWidth K) :
    s.setWidth p = t.setWidth p := by
  have hh := congrArg (fun x : BitVec K => x.setWidth p) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hp] using hh

/-- Zipping arbitrary operators with low-zero operands preserves that property. -/
theorem operands_zero_of_project {m p : ℕ} (bs : List Bool)
    (as : List (BitVec m)) (h : ∀ a ∈ as, a.setWidth p = 0) :
    ∀ x ∈ bs.zip as, x.2.setWidth p = 0 := by
  induction bs generalizing as with
  | nil => simp
  | cons b bs ih =>
    cases as with
    | nil => simp
    | cons a as =>
      intro x hx
      simp only [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h a (by simp)
      · exact ih as (fun a ha => h a (by simp [ha])) x hx

/-- Inductive guard recovery. Every operator is unrestricted. If the normalized
final low `K` bits return to their initial value, the actual final state differs
from the initial state by a sublist sum of the block weights after normalization.
Later zero padding may be included in `padding`; its parity is
retained in the statement rather than silently discarded. -/
theorem recover_guarded_chain {m K : ℕ} (hK : K ≤ m)
    (gs : List (GuardBlock m)) (padding : List (BitVec m))
    (hpadding : ∀ a ∈ padding, a = 0)
    (s : BitVec m)
    (hguards : ∀ g ∈ gs, 4 + g.position ≤ K ∧
      s.setWidth (4 + g.position) = 1#4 ++ s.setWidth g.position ∧
      g.first.setWidth (4 + g.position) = 3#4 ++ 0#g.position ∧
      g.second.setWidth (4 + g.position) = 13#4 ++ 0#g.position ∧
      g.weight.setWidth K = 0)
    (hseparated : gs.Pairwise fun g g' =>
      g'.first.setWidth (4 + g.position) = 0 ∧
      g'.second.setWidth (4 + g.position) = 0)
    (bs : List Bool) (hlen : bs.length = (guardedOperands gs ++ padding).length)
    (hfinal : (normalize (xnorParity (bs.zip (guardedOperands gs ++ padding)))
      (eval (bs.zip (guardedOperands gs ++ padding)) s)).setWidth K = s.setWidth K) :
    ∃ chosen : List (GuardBlock m), chosen <+ gs ∧
      normalize (xnorParity (bs.zip (guardedOperands gs ++ padding)))
        (eval (bs.zip (guardedOperands gs ++ padding)) s) =
          s + (chosen.map GuardBlock.weight).sum := by
  induction gs generalizing bs s with
  | nil =>
    refine ⟨[], .slnil, ?_⟩
    have hz := operands_zero_of_project bs padding
      (p := m) (fun a ha => by rw [hpadding a ha]; simp)
    have he := normalized_low_invariant (le_refl m) (bs.zip padding) hz s false
    simpa [guardedOperands, normalize] using he
  | cons g gs ih =>
    have hg := hguards g (by simp)
    have hsep := List.pairwise_cons.1 hseparated
    have hglen : (guardedOperands (g :: gs) ++ padding).length =
        4 + (guardedOperands gs ++ padding).length := by
      simp [guardedOperands, GuardBlock.operands]
      omega
    rw [hglen] at hlen
    rcases bs with _ | ⟨b, bs⟩
    · simp only [List.length_nil] at hlen; omega
    rcases bs with _ | ⟨c, bs⟩
    · simp only [List.length_cons, List.length_nil] at hlen; omega
    rcases bs with _ | ⟨d, bs⟩
    · simp only [List.length_cons, List.length_nil] at hlen; omega
    rcases bs with _ | ⟨e, bs⟩
    · simp only [List.length_cons, List.length_nil] at hlen; omega
    have hbs : bs.length = (guardedOperands gs ++ padding).length := by
      simp only [List.length_cons] at hlen
      omega
    let tail := bs.zip (guardedOperands gs ++ padding)
    let head := fourSteps b c d e g.first g.second
    have hzip : (b :: c :: d :: e :: bs).zip (guardedOperands (g :: gs) ++ padding) =
        head ++ tail := rfl
    rw [hzip] at hfinal
    have ht : ∀ x ∈ tail, x.2.setWidth (4 + g.position) = 0 := by
      apply operands_zero_of_project
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨g', hg', ha⟩ := List.mem_flatMap.1 ha
        have hx := hsep.1 g' hg'
        simp only [GuardBlock.operands, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        all_goals first | exact hx.1 | exact hx.2
      · rw [hpadding a ha]; simp
    have hf := project_eq_of_low_eq hg.1 hfinal
    have hfield := congrArg (fun w : BitVec (4 + g.position) =>
      w.extractLsb' g.position 4) hf
    rw [hg.2.1, BitVec.extractLsb'_append_eq_left] at hfield
    have hfield' : (normalize (xnorParity (head ++ tail))
        (eval (head ++ tail) s)).extractLsb' g.position 4 = 1#4 := by
      have he : ∀ w : BitVec m,
          (w.setWidth (4 + g.position)).extractLsb' g.position 4 =
            w.extractLsb' g.position 4 := by
        intro w
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [hi, show g.position + i < 4 + g.position by omega]
      rwa [he] at hfield
    have hpat := guard_forces_pattern (show g.position + 4 ≤ m by omega)
      b c d e s g.first g.second (s.setWidth g.position)
      hg.2.1 hg.2.2.1 hg.2.2.2.1 tail ht hfield'
    have hrest (s' : BitVec m) (hs' : s'.setWidth K = s.setWidth K) :
        ∀ g' ∈ gs, 4 + g'.position ≤ K ∧
          s'.setWidth (4 + g'.position) = 1#4 ++ s'.setWidth g'.position ∧
          g'.first.setWidth (4 + g'.position) = 3#4 ++ 0#g'.position ∧
          g'.second.setWidth (4 + g'.position) = 13#4 ++ 0#g'.position ∧
          g'.weight.setWidth K = 0 := by
      intro g' hg'
      have hh := hguards g' (by simp [hg'])
      refine ⟨hh.1, ?_, hh.2.2⟩
      rw [project_eq_of_low_eq hh.1 hs',
        project_eq_of_low_eq (show g'.position ≤ K by omega) hs']
      exact hh.2.1
    rcases hpat with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have he : eval head s = s + g.weight := by
        dsimp [head]
        rw [fourSteps_add]
        simp only [GuardBlock.weight, BitVec.add_assoc]
      have hp : xnorParity head = false := fourSteps_parity_of_uniform _ _ _
      rw [eval_append, xnorParity_append, hp, Bool.false_xor, he] at hfinal
      have hs' : (s + g.weight).setWidth K = s.setWidth K := by
        rw [BitVec.setWidth_add _ _ hK, hg.2.2.2.2, add_zero]
      have hfinal' : (normalize (xnorParity tail) (eval tail (s + g.weight))).setWidth K =
          (s + g.weight).setWidth K := hfinal.trans hs'.symm
      obtain ⟨chosen, hchosen, hc⟩ := ih (s + g.weight) (hrest _ hs') hsep.2 bs hbs hfinal'
      refine ⟨g :: chosen, hchosen.cons_cons g, ?_⟩
      rw [hzip, eval_append, xnorParity_append, hp, Bool.false_xor, he]
      rw [hc]
      simp [BitVec.add_assoc]
    · have he : eval head s = s := fourSteps_xnor _ _ _
      have hp : xnorParity head = false := fourSteps_parity_of_uniform _ _ _
      rw [eval_append, xnorParity_append, hp, Bool.false_xor, he] at hfinal
      obtain ⟨chosen, hchosen, hc⟩ := ih s (hrest _ rfl) hsep.2 bs hbs hfinal
      refine ⟨chosen, hchosen.cons g, ?_⟩
      rw [hzip, eval_append, xnorParity_append, hp, Bool.false_xor, he]
      exact hc

/-- Every sublist of blocks is realized by unrestricted operator choices:
selected blocks use four additions and omitted blocks use four XNORs. -/
theorem realize_guarded_sublist {m : ℕ} {chosen gs : List (GuardBlock m)}
    (h : chosen <+ gs) (s : BitVec m) :
    ∃ bs : List Bool, bs.length = (guardedOperands gs).length ∧
      eval (bs.zip (guardedOperands gs)) s = s + (chosen.map GuardBlock.weight).sum := by
  induction h generalizing s with
  | slnil => exact ⟨[], rfl, by simp [guardedOperands, eval]⟩
  | @cons chosen gs g h ih =>
    obtain ⟨bs, hlen, he⟩ := ih s
    refine ⟨true :: true :: true :: true :: bs, ?_, ?_⟩
    · simp [guardedOperands, GuardBlock.operands] at hlen ⊢
      omega
    · change eval (fourSteps true true true true g.first g.second ++
        bs.zip (guardedOperands gs)) s = _
      rw [eval_append, fourSteps_xnor, he]
  | @cons_cons chosen gs g h ih =>
    obtain ⟨bs, hlen, he⟩ := ih (s + g.weight)
    refine ⟨false :: false :: false :: false :: bs, ?_, ?_⟩
    · simp [guardedOperands, GuardBlock.operands] at hlen ⊢
      omega
    · change eval (fourSteps false false false false g.first g.second ++
        bs.zip (guardedOperands gs)) s = _
      rw [eval_append, fourSteps_add]
      rw [BitVec.add_assoc]
      change eval (bs.zip (guardedOperands gs)) (s + g.weight) = _
      rw [he]
      simp [BitVec.add_assoc]


end Cslib.Cryptanalysis.AddXNOR
