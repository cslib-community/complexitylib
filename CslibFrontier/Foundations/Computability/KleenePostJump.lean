/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate (Mathlib, `Mathlib/Computability/TuringDegree.lean`)

public import CslibFrontier.Foundations.Computability.KleenePost
public import CslibFrontier.Foundations.Computability.RecursiveInEvalnPrimrec
public import CslibFrontier.Foundations.Data.List.Primrec
public import Mathlib.Computability.PartrecCode

/-!
# Kleene–Post Theorem with Turing Jump

This module proves the upper bound on the Kleene–Post construction, showing that the constructed
incomparable sequences `limA` and `limB` from `CslibFrontier.Foundations.Computability.KleenePost`
are Turing reducible to the halting problem (`∅'`).

## Source correspondence and notation mapping

The Kleene–Post theorem [KleenePost1954] (see also [Soare1987]) constructs two Turing-incomparable
sets below `∅'` by finite extension. An inspected exposition is [Simpson2005], Theorem 2.6.4,
§2.6, pp. 30–31 (November 1, 2005 draft); the original-source locators remain unverified:

* **Constructed sets and characteristic functions**: the sets are
  `A = {n | limA n = true}` and `B = {n | limB n = true}`, where
  `limA n = (stage (2 * n + 2)).1.getD n false` and
  `limB n = (stage (2 * n + 2)).2.getD n false`. By `Nat.RecursiveIn.KleenePost.indicator_eq`,
  their `{0, 1}`-valued characteristic functions are `A.indicator 1 = fun n => (limA n).toNat`
  and `B.indicator 1 = fun n => (limB n).toNat`.
* **Diagonal halting set (`∅'`)**: `Nat.RecursiveIn.KleenePost.halting` is the diagonal halting set
  `{c : ℕ | (Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code c) c).Dom}` for Mathlib's acceptable
  numbering `Nat.Partrec.Code`, with characteristic function `halting.indicator 1 : ℕ → ℕ` and
  partial-function oracle wrapper `haltingOraclePart`.
* **Turing reducibility (`≤ᵀ`)**: `f ≤ᵀ g` is Mathlib's `TuringReducible f g`
  (`RecursiveIn {g} f`).
* **Model boundary**: at each stage `s`, the finite-extension step queries `halting` via the
  primitive-recursive many-one reduction `halts_reducibleTo_halting` to decide the `Σ⁰₁` question
  `Halts c τ σ.length`. Consequently `A` and `B` have total `Δ⁰₂` characteristic functions
  reducible to `∅'`. No c.e. property is proved; Friedberg–Muchnik remains separate.

Simpson's finite strings `σₙ, τₙ` and functions `χA, χB` correspond to the stage components and
limit indicators above. His extension test asks for output `1`; `Halts` accepts any output `y`
and `step` appends `decide (y = 0)`. His register-machine halting-on-input-`0` convention is
replaced by the diagonal ordinary-code set above. No register-machine simulation or equality
of numerical stage clocks is claimed.

## Main definitions

* `Nat.RecursiveIn.KleenePost.halting`: the diagonal halting set for partial recursive functions
  (`∅'`).
* `Nat.RecursiveIn.KleenePost.haltingOraclePart`: the characteristic function of `halting` as a
  total `ℕ →. ℕ` oracle.
* `Nat.RecursiveIn.KleenePost.O`: the singleton oracle set `{haltingOraclePart}`.
* `Nat.RecursiveIn.KleenePost.stageNat`: the encoded stage of the Kleene–Post construction.

## Main results

* `Nat.RecursiveIn.KleenePost.halts_reducibleTo_halting`: the single-step halting question `Halts`
  is many-one reducible to `halting` via a primitive recursive function.
* `Nat.RecursiveIn.KleenePost.rec_stageNat`: the encoded stage function `stageNat` is recursive in
  the halting oracle.
* `kleene_post_below_jump`: the Kleene–Post sequences `limA` and `limB` are Turing reducible to
  the characteristic function of `halting`.

## References

* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
* [S. G. Simpson, *Topics in Logic and Foundations: Spring 2004*][Simpson2005]
-/

public section

open Encodable Denumerable Nat.Partrec Primrec Nat.RecursiveIn.Code Nat.RecursiveIn.KleenePost
open Nat.RecursiveIn (comp pair prec rfind)
open scoped Computability

namespace Nat.RecursiveIn.KleenePost

/-- The Turing jump of the empty set, the diagonal halting set for partial recursive functions. -/
@[expose]
def halting : Set ℕ := { c | (Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code c) c).Dom }

/-- Boolean decision procedure for `haltsPred`. -/
private def haltsPredDecide (c : Nat.RecursiveIn.Code) (τ : List Bool) (x : ℕ) (e : ℕ) : Bool :=
  match Encodable.decode (α := List Bool × ℕ × ℕ) e with
  | Option.none => false
  | Option.some (σ, k, y) =>
    (τ <+: σ) && (Nat.RecursiveIn.Code.evaln (bits σ) k c x == Option.some y)

/-- Partial-search wrapper returning `some e` when `e` witnesses `haltsPredDecide c τ x e`. -/
private def haltsPredOpt (c : Nat.RecursiveIn.Code) (τ : List Bool) (x : ℕ) (e : ℕ) : Option ℕ :=
  bif haltsPredDecide c τ x e then Option.some e else Option.none

/-- Uncurried form of `haltsPredOpt` for primitive recursion combinators. -/
private def haltsPredOptAll (p : Nat.RecursiveIn.Code × List Bool × ℕ) (e : ℕ) : Option ℕ :=
  let (c, τ, x) := p
  haltsPredOpt c τ x e

private lemma primrec_bits : _root_.Primrec bits :=
  list_map _root_.Primrec.id ((_root_.Primrec.dom_bool Bool.toNat).comp snd).to₂

private lemma primrec_evaln_all :
    _root_.Primrec (fun (q : (Nat.RecursiveIn.Code × List Bool × ℕ) × List Bool × ℕ × ℕ) =>
      Nat.RecursiveIn.Code.evaln (bits q.2.1) q.2.2.1 q.1.1 q.1.2.2) := by
  have H : _root_.Primrec (fun q : (Nat.RecursiveIn.Code × List Bool × ℕ) × List Bool × ℕ × ℕ =>
      (bits q.2.1, (q.2.2.1, q.1.1), q.1.2.2)) :=
    (primrec_bits.comp (fst.comp snd)).pair
      (((fst.comp (snd.comp snd)).pair (fst.comp fst)).pair (snd.comp (snd.comp fst)))
  exact primrec_evaln.comp H

private lemma primrec_evaln_eq_all :
    _root_.Primrec (fun (q : (Nat.RecursiveIn.Code × List Bool × ℕ) × List Bool × ℕ × ℕ) =>
      Nat.RecursiveIn.Code.evaln (bits q.2.1) q.2.2.1 q.1.1 q.1.2.2 == Option.some q.2.2.2) := by
  have H : _root_.Primrec (fun (q : (Nat.RecursiveIn.Code × List Bool × ℕ) × List Bool × ℕ × ℕ) =>
      decide (Nat.RecursiveIn.Code.evaln (bits q.2.1) q.2.2.1 q.1.1 q.1.2.2 =
        Option.some q.2.2.2)) :=
    (PrimrecRel.comp _root_.Primrec.eq primrec_evaln_all
      (option_some.comp (snd.comp (snd.comp snd)))).decide
  exact H.of_eq fun q => by
    cases Nat.RecursiveIn.Code.evaln (bits q.2.1) q.2.2.1 q.1.1 q.1.2.2 <;>
      simp
    rfl

private lemma primrec_haltsPredOptAll : Primrec₂ haltsPredOptAll := by
  have hp1 : _root_.Primrec (fun (q : (Nat.RecursiveIn.Code × List Bool × ℕ) × List Bool × ℕ × ℕ) =>
      decide (q.1.2.1 <+: q.2.1)) :=
    (PrimrecRel.comp list_isPrefix (fst.comp (snd.comp fst)) (fst.comp snd)).decide
  have hs : _root_.Primrec (fun (q : (Nat.RecursiveIn.Code × List Bool × ℕ) × List Bool × ℕ × ℕ) =>
      decide (q.1.2.1 <+: q.2.1) &&
        (Nat.RecursiveIn.Code.evaln (bits q.2.1) q.2.2.1 q.1.1 q.1.2.2 ==
          Option.some q.2.2.2)) :=
    _root_.Primrec.and.comp hp1 primrec_evaln_eq_all
  have hs_to₂ : Primrec₂ (fun (arg : (Nat.RecursiveIn.Code × List Bool × ℕ) × ℕ)
      (p : List Bool × ℕ × ℕ) =>
      decide (arg.1.2.1 <+: p.1) &&
        (Nat.RecursiveIn.Code.evaln (bits p.1) p.2.1 arg.1.1 arg.1.2.2 == Option.some p.2.2)) :=
    hs.comp ((fst.comp fst).pair snd)
  have H_match : _root_.Primrec (fun arg : (Nat.RecursiveIn.Code × List Bool × ℕ) × ℕ =>
      haltsPredDecide arg.1.1 arg.1.2.1 arg.1.2.2 arg.2) :=
    (_root_.Primrec.option_casesOn (_root_.Primrec.decode.comp snd) (_root_.Primrec.const false)
      hs_to₂).of_eq fun arg => by
      dsimp [haltsPredDecide]
      cases Encodable.decode (α := List Bool × ℕ × ℕ) arg.2 <;> rfl
  exact (_root_.Primrec.cond H_match (option_some.comp snd)
    (_root_.Primrec.const Option.none)).of_eq fun _ => rfl

private lemma haltsPred_iff_haltsPredDecide
    (c : Nat.RecursiveIn.Code) (τ : List Bool) (x : ℕ) (e : ℕ) :
    haltsPred c τ x e ↔ haltsPredDecide c τ x e = true := by
  dsimp [haltsPred, haltsPredDecide]
  cases Encodable.decode (α := List Bool × ℕ × ℕ) e <;> simp

private lemma halts_iff_haltsPredOpt_dom (c : Nat.RecursiveIn.Code) (τ : List Bool) (x : ℕ) :
    Halts c τ x ↔ (Nat.rfindOpt (haltsPredOpt c τ x)).Dom := by
  rw [Halts_iff_exists_haltsPred]
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, e, by dsimp [haltsPredOpt]; rw [(haltsPred_iff_haltsPredDecide c τ x e).mp he]; rfl⟩
  · rintro ⟨e, a, he⟩
    dsimp [haltsPredOpt] at he
    cases h : haltsPredDecide c τ x e
    · simp [h] at he
    · exact ⟨e, (haltsPred_iff_haltsPredDecide c τ x e).mpr h⟩

private lemma partrec_haltsPredOpt_rfindOpt :
    Partrec fun (p : Nat.RecursiveIn.Code × List Bool × ℕ) =>
      Nat.rfindOpt (haltsPredOptAll p) :=
  Partrec.rfindOpt (Primrec₂.to_comp primrec_haltsPredOptAll)

/-- The halting question `Halts c τ x` reduces primitive-recursively to `halting`. -/
lemma halts_reducibleTo_halting :
    ∃ K : (Nat.RecursiveIn.Code × List Bool × ℕ) → ℕ,
      _root_.Primrec K ∧ ∀ c τ x, Halts c τ x ↔ K (c, τ, x) ∈ halting := by
  have H : Partrec fun (p : Nat.RecursiveIn.Code × List Bool × ℕ) =>
      Nat.rfindOpt (haltsPredOpt p.1 p.2.1 p.2.2) :=
    partrec_haltsPredOpt_rfindOpt
  obtain ⟨c_G, hc_G⟩ := Nat.Partrec.Code.exists_code.mp H
  have hc_G' : Nat.Partrec.Code.eval c_G = fun n =>
      (Encodable.decode (α := Nat.RecursiveIn.Code × List Bool × ℕ) n : Part _).bind
        fun (a : Nat.RecursiveIn.Code × List Bool × ℕ) =>
          Part.map (Encodable.encode : ℕ → ℕ) (Nat.rfindOpt (haltsPredOpt a.1 a.2.1 a.2.2)) :=
    hc_G
  let K := fun (p : Nat.RecursiveIn.Code × List Bool × ℕ) =>
    Encodable.encode (Nat.Partrec.Code.comp c_G (Nat.Partrec.Code.const (Encodable.encode p)))
  have hK : _root_.Primrec K :=
    _root_.Primrec.encode.comp
      (Nat.Partrec.Code.primrec₂_comp.comp (_root_.Primrec.const c_G)
        (Nat.Partrec.Code.primrec_const.comp _root_.Primrec.encode))
  use K, hK
  intro c τ x
  have h_eval : ∀ p,
      Nat.Partrec.Code.eval
        (Nat.Partrec.Code.comp c_G (Nat.Partrec.Code.const (Encodable.encode p))) (K p) =
        Part.map (Encodable.encode : ℕ → ℕ) (Nat.rfindOpt (haltsPredOpt p.1 p.2.1 p.2.2)) := by
    intro p
    change ((Nat.Partrec.Code.const (Encodable.encode p)).eval (K p)).bind
      (fun m => Nat.Partrec.Code.eval c_G m) = _
    rw [Nat.Partrec.Code.eval_const, Part.bind_some, hc_G']
    dsimp
    rw [Encodable.encodek]
    change (Part.some p).bind _ = _
    rw [Part.bind_some]
  change Halts c τ x ↔
    (Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code (K (c, τ, x))) (K (c, τ, x))).Dom
  constructor
  · intro h
    rw [ofNat_encode]
    have he := h_eval (c, τ, x)
    rw [he]
    exact (halts_iff_haltsPredOpt_dom c τ x).mp h
  · intro h
    rw [ofNat_encode] at h
    have he := h_eval (c, τ, x)
    rw [he] at h
    exact (halts_iff_haltsPredOpt_dom c τ x).mpr h

private lemma rfindOpt_const_some (a : ℕ) :
    Nat.rfindOpt (fun _ : ℕ => Option.some a) = Part.some a := by
  ext x
  simp only [Nat.rfindOpt, Part.mem_bind_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨_, _, hx⟩
    exact Part.mem_some_iff.mp hx
  · rintro rfl
    refine ⟨0, ?_, Part.mem_some x⟩
    exact Nat.mem_rfind.mpr ⟨Part.mem_some true, fun {m} hm => (Nat.not_lt_zero m hm).elim⟩

private lemma rfindOpt_haltsPredOpt_eq_some_find {c : Code} {τ : List Bool} {x : ℕ}
    (h : Halts c τ x) :
    Nat.rfindOpt (haltsPredOpt c τ x) =
      Part.some (Nat.find (p := haltsPred c τ x) ((Halts_iff_exists_haltsPred c τ x).mp h)) := by
  set h_ex := (Halts_iff_exists_haltsPred c τ x).mp h
  set e₀ := Nat.find h_ex
  have he₀ : haltsPredDecide c τ x e₀ = true :=
    (haltsPred_iff_haltsPredDecide c τ x e₀).mp (Nat.find_spec h_ex)
  have hmin : ∀ m < e₀, haltsPredDecide c τ x m = false := by
    intro m hm
    have hm' := Nat.find_min h_ex hm
    cases h_dec : haltsPredDecide c τ x m
    · rfl
    · exact (hm' ((haltsPred_iff_haltsPredDecide c τ x m).mpr h_dec)).elim
  ext a
  simp only [Nat.rfindOpt, Part.mem_bind_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨n, hn, ha⟩
    obtain ⟨hn_true, hn_min⟩ := Nat.mem_rfind.mp hn
    have hn_eq : n = e₀ := by
      rcases lt_trichotomy n e₀ with hlt | rfl | hgt
      · have h_false := hmin n hlt
        simp [haltsPredOpt, h_false] at hn_true
      · rfl
      · have h_false := hn_min hgt
        simp [haltsPredOpt, he₀] at h_false
    subst hn_eq
    simpa [haltsPredOpt, he₀] using ha
  · rintro rfl
    refine ⟨e₀, Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩, ?_⟩
    · simp [haltsPredOpt, he₀]
    · simp [haltsPredOpt, hmin m hm]
    · simp [haltsPredOpt, he₀]

/-- The characteristic function of `halting` as a total partial function `ℕ →. ℕ`. -/
noncomputable def haltingOraclePart (n : ℕ) : Part ℕ :=
  Part.some ((halting.indicator 1 : ℕ → ℕ) n)

/-- The singleton oracle set `{haltingOraclePart}`. -/
noncomputable def O : Set (ℕ →. ℕ) := {haltingOraclePart}

/-- `haltingOraclePart` is recursive in `O`. -/
lemma haltingOraclePart_rec : Nat.RecursiveIn O haltingOraclePart :=
  Nat.RecursiveIn.oracle haltingOraclePart (Set.mem_singleton _)

/-- The encoded stage pair `stage s` of the Kleene–Post construction. -/
noncomputable def stageNat (s : ℕ) : ℕ := encode (stage s)

private def emptyStage : List Bool × List Bool := ([], [])

private def stepStage (p : ℕ) : List Bool × List Bool :=
  match decode (α := List Bool × List Bool) p.unpair.2.unpair.2 with
  | Option.some st => st
  | Option.none => emptyStage

private lemma primrec_stepStage : _root_.Primrec stepStage := by
  have hprev : _root_.Primrec (fun p : ℕ => p.unpair.2.unpair.2) :=
    snd.comp (_root_.Primrec.unpair.comp (snd.comp _root_.Primrec.unpair))
  exact (_root_.Primrec.option_casesOn (_root_.Primrec.decode.comp hprev)
    (_root_.Primrec.const emptyStage) snd.to₂).of_eq fun p => by
    dsimp [stepStage]
    cases decode (α := List Bool × List Bool) p.unpair.2.unpair.2 <;> rfl

private lemma primrec_s_mod2_eq_zero :
    _root_.Primrec (fun p : ℕ => decide (p.unpair.2.unpair.1 % 2 = 0)) := by
  have hs : _root_.Primrec (fun p : ℕ => p.unpair.2.unpair.1) :=
    fst.comp (_root_.Primrec.unpair.comp (snd.comp _root_.Primrec.unpair))
  have hmod : _root_.Primrec (fun p : ℕ => p.unpair.2.unpair.1 % 2) :=
    nat_mod.comp hs (_root_.Primrec.const 2)
  exact (PrimrecRel.comp _root_.Primrec.eq hmod (_root_.Primrec.const 0)).decide

private def stepSigma (p : ℕ) : List Bool :=
  if p.unpair.2.unpair.1 % 2 = 0 then (stepStage p).1 else (stepStage p).2

private def stepTau (p : ℕ) : List Bool :=
  if p.unpair.2.unpair.1 % 2 = 0 then (stepStage p).2 else (stepStage p).1

private lemma primrec_stepSigma : _root_.Primrec stepSigma :=
  (_root_.Primrec.cond primrec_s_mod2_eq_zero
    (fst.comp primrec_stepStage) (snd.comp primrec_stepStage)).of_eq fun p => by
    dsimp [stepSigma]
    by_cases h : p.unpair.2.unpair.1 % 2 = 0 <;> simp [h]

private lemma primrec_stepTau : _root_.Primrec stepTau :=
  (_root_.Primrec.cond primrec_s_mod2_eq_zero
    (snd.comp primrec_stepStage) (fst.comp primrec_stepStage)).of_eq fun p => by
    dsimp [stepTau]
    by_cases h : p.unpair.2.unpair.1 % 2 = 0 <;> simp [h]

private def stepArgs (p : ℕ) : Code × List Bool × ℕ :=
  (ofNat Code (p.unpair.2.unpair.1 / 2), stepTau p, (stepSigma p).length)

private lemma primrec_stepArgs : _root_.Primrec stepArgs := by
  have hs : _root_.Primrec (fun p : ℕ => p.unpair.2.unpair.1) :=
    fst.comp (_root_.Primrec.unpair.comp (snd.comp _root_.Primrec.unpair))
  have hc : _root_.Primrec (fun p : ℕ => ofNat Code (p.unpair.2.unpair.1 / 2)) :=
    (_root_.Primrec.ofNat Code).comp (nat_div.comp hs (_root_.Primrec.const 2))
  exact hc.pair (primrec_stepTau.pair (list_length.comp primrec_stepSigma))

private noncomputable def stepPrep (p : ℕ) : ℕ :=
  let s := p.unpair.2.unpair.1
  let prev := p.unpair.2.unpair.2
  let stage_s : List Bool × List Bool :=
    match decode prev with
    | Option.some p => p
    | Option.none => ([], [])
  let c := ofNat Nat.RecursiveIn.Code (s / 2)
  let σ := if s % 2 = 0 then stage_s.1 else stage_s.2
  let τ := if s % 2 = 0 then stage_s.2 else stage_s.1
  let K := Classical.choose halts_reducibleTo_halting
  K (c, τ, σ.length)

private lemma primrec_stepPrep : _root_.Primrec stepPrep := by
  have hK : _root_.Primrec (Classical.choose halts_reducibleTo_halting) :=
    (Classical.choose_spec halts_reducibleTo_halting).1
  exact (hK.comp primrec_stepArgs).of_eq fun _ => rfl

private lemma primrec_halts_eq_one :
    _root_.Primrec (fun p : ℕ => decide (p.unpair.1 = 1)) :=
  (PrimrecRel.comp _root_.Primrec.eq (fst.comp _root_.Primrec.unpair)
    (_root_.Primrec.const 1)).decide

private def stepSearchOpt (p e : ℕ) : Option ℕ :=
  if p.unpair.1 = 1 then
    haltsPredOpt (stepArgs p).1 (stepArgs p).2.1 (stepArgs p).2.2 e
  else
    Option.some 0

private lemma primrec_stepSearchOpt : Primrec₂ stepSearchOpt := by
  have h_halts : _root_.Primrec (fun q : ℕ × ℕ => decide (q.1.unpair.1 = 1)) :=
    primrec_halts_eq_one.comp fst
  have h_pred : _root_.Primrec (fun q : ℕ × ℕ =>
      haltsPredOpt (stepArgs q.1).1 (stepArgs q.1).2.1 (stepArgs q.1).2.2 q.2) :=
    primrec_haltsPredOptAll.comp (primrec_stepArgs.comp fst) snd
  exact (_root_.Primrec.cond h_halts h_pred (_root_.Primrec.const (Option.some 0))).of_eq
    fun ⟨p, e⟩ => by
      dsimp [stepSearchOpt]
      by_cases h : p.unpair.1 = 1 <;> simp [h]

private def stepFallback (p : ℕ) : ℕ :=
  encode (if p.unpair.2.unpair.1 % 2 = 0 then (stepSigma p ++ [false], stepTau p)
    else (stepTau p, stepSigma p ++ [false]))

private lemma primrec_stepFallback : _root_.Primrec stepFallback := by
  have h_app : _root_.Primrec (fun p : ℕ => stepSigma p ++ [false]) :=
    list_append.comp primrec_stepSigma (_root_.Primrec.const ([false] : List Bool))
  have h_pair : _root_.Primrec (fun p : ℕ =>
      if p.unpair.2.unpair.1 % 2 = 0 then (stepSigma p ++ [false], stepTau p)
      else (stepTau p, stepSigma p ++ [false])) :=
    (_root_.Primrec.cond primrec_s_mod2_eq_zero
      (h_app.pair primrec_stepTau) (primrec_stepTau.pair h_app)).of_eq fun p => by
      by_cases h : p.unpair.2.unpair.1 % 2 = 0 <;> simp [h]
  exact _root_.Primrec.encode.comp h_pair

private def stepFound (p : ℕ) (w : List Bool × ℕ × ℕ) : ℕ :=
  encode (if p.unpair.2.unpair.1 % 2 = 0 then (stepSigma p ++ [decide (w.2.2 = 0)], w.1)
    else (w.1, stepSigma p ++ [decide (w.2.2 = 0)]))

private lemma primrec_stepFound : Primrec₂ stepFound := by
  have h_w0 : _root_.Primrec (fun q : ℕ × (List Bool × ℕ × ℕ) => decide (q.2.2.2 = 0)) :=
    (PrimrecRel.comp _root_.Primrec.eq (snd.comp (snd.comp snd)) (_root_.Primrec.const 0)).decide
  have h_sing : _root_.Primrec (fun q : ℕ × (List Bool × ℕ × ℕ) => [decide (q.2.2.2 = 0)]) :=
    list_cons.comp h_w0 (_root_.Primrec.const [])
  have h_app : _root_.Primrec (fun q : ℕ × (List Bool × ℕ × ℕ) =>
      stepSigma q.1 ++ [decide (q.2.2.2 = 0)]) :=
    list_append.comp (primrec_stepSigma.comp fst) h_sing
  have h_w1 : _root_.Primrec (fun q : ℕ × (List Bool × ℕ × ℕ) => q.2.1) :=
    fst.comp snd
  have h_pair : _root_.Primrec (fun q : ℕ × (List Bool × ℕ × ℕ) =>
      if q.1.unpair.2.unpair.1 % 2 = 0 then
        (stepSigma q.1 ++ [decide (q.2.2.2 = 0)], q.2.1)
      else (q.2.1, stepSigma q.1 ++ [decide (q.2.2.2 = 0)])) :=
    (_root_.Primrec.cond (primrec_s_mod2_eq_zero.comp fst)
      (h_app.pair h_w1) (h_w1.pair h_app)).of_eq fun q => by
      by_cases h : q.1.unpair.2.unpair.1 % 2 = 0 <;> simp [h]
  exact _root_.Primrec.encode.comp h_pair

private def stepPost (p e : ℕ) : ℕ :=
  if p.unpair.1 = 1 then
    match decode (α := List Bool × ℕ × ℕ) e with
    | Option.some w => stepFound p w
    | Option.none => stepFallback p
  else
    stepFallback p

private lemma primrec_stepPost : Primrec₂ stepPost := by
  have h_match : _root_.Primrec (fun q : ℕ × ℕ =>
      match decode (α := List Bool × ℕ × ℕ) q.2 with
      | Option.some w => stepFound q.1 w
      | Option.none => stepFallback q.1) :=
    (_root_.Primrec.option_casesOn (_root_.Primrec.decode.comp snd)
      (primrec_stepFallback.comp fst)
      (primrec_stepFound.comp (fst.comp fst) snd).to₂).of_eq fun ⟨p, e⟩ => by
      cases decode (α := List Bool × ℕ × ℕ) e <;> rfl
  exact (_root_.Primrec.cond (primrec_halts_eq_one.comp fst)
    h_match (primrec_stepFallback.comp fst)).of_eq fun ⟨p, e⟩ => by
    dsimp [stepPost]
    by_cases h : p.unpair.1 = 1 <;> simp [h]

private noncomputable def stepCore (p : ℕ) : Part ℕ :=
  let halts := p.unpair.1
  let s := p.unpair.2.unpair.1
  let prev := p.unpair.2.unpair.2
  let stage_s : List Bool × List Bool :=
    match decode prev with
    | Option.some p => p
    | Option.none => ([], [])
  let c := ofNat Nat.RecursiveIn.Code (s / 2)
  let σ := if s % 2 = 0 then stage_s.1 else stage_s.2
  let τ := if s % 2 = 0 then stage_s.2 else stage_s.1
  if halts = 1 then
    (Nat.rfindOpt (haltsPredOpt c τ σ.length)).map fun e =>
      match decode (α := List Bool × ℕ × ℕ) e with
      | Option.some p =>
        let r := p.2
        encode (if s % 2 = 0 then (σ ++ [decide (r.2 = 0)], p.1)
          else (p.1, σ ++ [decide (r.2 = 0)]))
      | Option.none =>
        encode (if s % 2 = 0 then (σ ++ [false], τ) else (τ, σ ++ [false]))
  else
    Part.some <| encode (if s % 2 = 0 then (σ ++ [false], τ) else (τ, σ ++ [false]))

private lemma partrec_stepCore : Partrec stepCore := by
  have h_rfind : Partrec (fun p : ℕ => Nat.rfindOpt (stepSearchOpt p)) :=
    Partrec.rfindOpt primrec_stepSearchOpt.to_comp
  have h_map : Partrec (fun p : ℕ => (Nat.rfindOpt (stepSearchOpt p)).map (stepPost p)) :=
    Partrec.map h_rfind primrec_stepPost.to_comp
  refine h_map.of_eq fun p => ?_
  have h_search : stepSearchOpt p = fun e =>
      if p.unpair.1 = 1 then haltsPredOpt (stepArgs p).1 (stepArgs p).2.1 (stepArgs p).2.2 e
      else Option.some 0 := rfl
  have h_post : stepPost p = fun e =>
      if p.unpair.1 = 1 then
        match decode (α := List Bool × ℕ × ℕ) e with
        | Option.some w => stepFound p w
        | Option.none => stepFallback p
      else stepFallback p := rfl
  rw [h_search, h_post]
  dsimp [stepCore, stepArgs, stepFound, stepFallback, stepSigma, stepTau, stepStage, emptyStage]
  by_cases h : p.unpair.1 = 1
  · simp [h]
  · simp [h, rfindOpt_const_some]

private def stageNatBase (_p : ℕ) : Part ℕ := Part.some (encode (([], []) : List Bool × List Bool))

private lemma primrec_stageNatBase : _root_.Primrec (fun _ : ℕ => encode emptyStage) :=
  _root_.Primrec.const (encode emptyStage)

open Classical in
private lemma stage_succ_eq (s : ℕ) :
    let c := ofNat Code (s / 2)
    let σ := if s % 2 = 0 then (stage s).1 else (stage s).2
    let τ := if s % 2 = 0 then (stage s).2 else (stage s).1
    stage (s + 1) =
      if h : Halts c τ σ.length then
        let e := Nat.find (p := haltsPred c τ σ.length)
          ((Halts_iff_exists_haltsPred c τ σ.length).mp h)
        match decode (α := List Bool × ℕ × ℕ) e with
        | Option.some w =>
          if s % 2 = 0 then (σ ++ [decide (w.2.2 = 0)], w.1)
          else (w.1, σ ++ [decide (w.2.2 = 0)])
        | Option.none =>
          if s % 2 = 0 then (σ ++ [false], τ) else (τ, σ ++ [false])
      else
        if s % 2 = 0 then (σ ++ [false], τ) else (τ, σ ++ [false]) := by
  intro c σ τ
  dsimp only [stage, step, c, σ, τ]
  by_cases hs : s % 2 = 0 <;> simp only [hs, ↓reduceIte]
  · split_ifs with h
    · generalize Nat.find (p := haltsPred _ _ _) _ = e
      cases decode (α := List Bool × ℕ × ℕ) e <;> rfl
    · rfl
  · split_ifs with h
    · generalize Nat.find (p := haltsPred _ _ _) _ = e
      cases decode (α := List Bool × ℕ × ℕ) e <;> rfl
    · rfl

private noncomputable def stepFull (p : ℕ) : Part ℕ :=
  (Nat.pair <$> (Part.some (stepPrep p)).bind haltingOraclePart <*> Part.some p.unpair.2) >>=
    stepCore

open Classical in
private lemma stepFull_spec (a s : ℕ) :
    stepFull (Nat.pair a (Nat.pair s (stageNat s))) = Part.some (stageNat (s + 1)) := by
  set p := Nat.pair a (Nat.pair s (stageNat s))
  have hp2 : p.unpair.2 = Nat.pair s (stageNat s) := by simp [p]
  have h_dec : decode (α := List Bool × List Bool) (stageNat s) = Option.some (stage s) :=
    Encodable.encodek (stage s)
  let c := ofNat Code (s / 2)
  let σ := if s % 2 = 0 then (stage s).1 else (stage s).2
  let τ := if s % 2 = 0 then (stage s).2 else (stage s).1
  have hprep : stepPrep p = Classical.choose halts_reducibleTo_halting (c, τ, σ.length) := by
    dsimp [stepPrep, c, σ, τ]
    rw [hp2, Nat.unpair_pair, h_dec]
  have hK := (Classical.choose_spec halts_reducibleTo_halting).2 c τ σ.length
  rw [← hprep] at hK
  have h_full : stepFull p =
      stepCore
        (Nat.pair ((halting.indicator 1 : ℕ → ℕ) (stepPrep p)) (Nat.pair s (stageNat s))) := by
    simp [stepFull, haltingOraclePart, Seq.seq, hp2]
  rw [h_full]
  dsimp [stepCore]
  rw [Nat.unpair_pair, Nat.unpair_pair, h_dec]
  have h_rhs : stageNat (s + 1) =
      encode (if h : Halts c τ σ.length then
        let e := Nat.find (p := haltsPred c τ σ.length)
          ((Halts_iff_exists_haltsPred c τ σ.length).mp h)
        match decode (α := List Bool × ℕ × ℕ) e with
        | Option.some w =>
          if s % 2 = 0 then (σ ++ [decide (w.2.2 = 0)], w.1)
          else (w.1, σ ++ [decide (w.2.2 = 0)])
        | Option.none =>
          if s % 2 = 0 then (σ ++ [false], τ) else (τ, σ ++ [false])
      else
        if s % 2 = 0 then (σ ++ [false], τ) else (τ, σ ++ [false])) :=
    congrArg encode (stage_succ_eq s)
  rw [h_rhs]
  change (if (halting.indicator 1 : ℕ → ℕ) (stepPrep p) = 1 then
      Part.map (fun e =>
        match decode (α := List Bool × ℕ × ℕ) e with
        | Option.some w =>
          encode (if s % 2 = 0 then (σ ++ [decide (w.2.2 = 0)], w.1)
            else (w.1, σ ++ [decide (w.2.2 = 0)]))
        | Option.none =>
          encode (if s % 2 = 0 then (σ ++ [false], τ) else (τ, σ ++ [false])))
        (Nat.rfindOpt (haltsPredOpt c τ σ.length))
    else
      Part.some (encode (if s % 2 = 0 then (σ ++ [false], τ) else (τ, σ ++ [false])))) = _
  by_cases h : Halts c τ σ.length
  · have h_mem : stepPrep p ∈ halting := hK.mp h
    have h_ind : (halting.indicator 1 : ℕ → ℕ) (stepPrep p) = 1 := Set.indicator_of_mem h_mem _
    simp only [h_ind, ↓reduceIte, h, ↓reduceDIte, rfindOpt_haltsPredOpt_eq_some_find h,
      Part.map_some]
    generalize Nat.find (p := haltsPred c τ σ.length)
      ((Halts_iff_exists_haltsPred c τ σ.length).mp h) = e₀
    cases decode (α := List Bool × ℕ × ℕ) e₀ <;> rfl
  · have h_nmem : stepPrep p ∉ halting := fun hm => h (hK.mpr hm)
    have h_ind : (halting.indicator 1 : ℕ → ℕ) (stepPrep p) = 0 := Set.indicator_of_notMem h_nmem _
    have h_ne : (halting.indicator 1 : ℕ → ℕ) (stepPrep p) ≠ 1 := by omega
    simp only [h_ne, ↓reduceIte, h, ↓reduceDIte]

/-- The encoded stage sequence `stageNat` is recursive in `O`. -/
lemma rec_stageNat : Nat.RecursiveIn O (fun n => Part.some (stageNat n)) := by
  have h_base : Nat.RecursiveIn O stageNatBase :=
    (Primrec.nat_iff.mp primrec_stageNatBase).recursiveIn
  have h_step : Nat.RecursiveIn O stepCore :=
    (Partrec.nat_iff.mp partrec_stepCore).recursiveIn
  have h_prep : Nat.RecursiveIn O (fun p => Part.some (stepPrep p)) :=
    (Primrec.nat_iff.mp primrec_stepPrep).recursiveIn
  have h_halts : Nat.RecursiveIn O (fun p => (Part.some (stepPrep p)).bind haltingOraclePart) :=
    comp haltingOraclePart_rec h_prep
  have h_id : Nat.RecursiveIn O (fun p : ℕ => Part.some p.unpair.2) :=
    (Primrec.nat_iff.mp (snd.comp _root_.Primrec.unpair)).recursiveIn
  have h_pair : Nat.RecursiveIn O
      (fun p =>
        Nat.pair <$> (Part.some (stepPrep p)).bind haltingOraclePart <*> Part.some p.unpair.2) :=
    pair h_halts h_id
  have h_step2 : Nat.RecursiveIn O stepFull := comp h_step h_pair
  have h_prec := prec h_base h_step2
  have h_zero_pair : Nat.RecursiveIn O (fun n : ℕ => Part.some (Nat.pair 0 n)) :=
    (Primrec.nat_iff.mp
      (Primrec₂.natPair.comp (_root_.Primrec.const 0) _root_.Primrec.id)).recursiveIn
  have h_comp := comp h_prec h_zero_pair
  refine h_comp.of_eq fun n => ?_
  simp only [Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ s ih =>
    change (Nat.rec (motive := fun _ => Part ℕ) (stageNatBase 0)
        (fun y IH => IH.bind fun i => stepFull (Nat.pair 0 (Nat.pair y i))) s).bind
      (fun i => stepFull (Nat.pair 0 (Nat.pair s i))) = Part.some (stageNat (s + 1))
    rw [ih, Part.bind_some]
    exact stepFull_spec 0 s

private def decodeStagePair (p : ℕ) : List Bool × List Bool :=
  match decode (α := List Bool × List Bool) p.unpair.2 with
  | Option.some st => st
  | Option.none => emptyStage

private lemma primrec_decodeStagePair : _root_.Primrec decodeStagePair :=
  (_root_.Primrec.option_casesOn (_root_.Primrec.decode.comp (snd.comp _root_.Primrec.unpair))
    (_root_.Primrec.const emptyStage) snd.to₂).of_eq fun p => by
    dsimp [decodeStagePair]
    cases decode (α := List Bool × List Bool) p.unpair.2 <;> rfl

private lemma primrec_two_mul_add_two : _root_.Primrec (fun n : ℕ => 2 * n + 2) :=
  (_root_.Primrec.succ.comp
    (_root_.Primrec.succ.comp (nat_add.comp _root_.Primrec.id _root_.Primrec.id))).of_eq
    fun n => by dsimp; omega

end Nat.RecursiveIn.KleenePost

/-- **Kleene–Post upper bound**: the constructed incomparable sequences `limA` and `limB` are
Turing reducible to the halting problem (`∅'`). -/
theorem kleene_post_below_jump :
    (fun n => (limA n).toNat : ℕ → ℕ) ≤ᵀ (fun n => (halting.indicator 1 n) : ℕ → ℕ) ∧
    (fun n => (limB n).toNat : ℕ → ℕ) ≤ᵀ (fun n => (halting.indicator 1 n) : ℕ → ℕ) := by
  have h_idx : Nat.RecursiveIn O (fun n => Part.some (2 * n + 2)) :=
    (Primrec.nat_iff.mp primrec_two_mul_add_two).recursiveIn
  have h_stage_idx : Nat.RecursiveIn O (fun n => Part.some (stageNat (2 * n + 2))) :=
    (comp rec_stageNat h_idx).of_eq fun n => by simp
  have h_id : Nat.RecursiveIn O (fun n => Part.some n) := Nat.Primrec.id.recursiveIn
  have h_arg : Nat.RecursiveIn O (fun n => Part.some (Nat.pair n (stageNat (2 * n + 2)))) :=
    (pair h_id h_stage_idx).of_eq fun n => by simp [Seq.seq]
  have h_extA : _root_.Primrec (fun p : ℕ =>
      ((decodeStagePair p).1.getD p.unpair.1 false).toNat) :=
    (_root_.Primrec.dom_bool Bool.toNat).comp
      ((_root_.Primrec.list_getD false).comp
        (fst.comp primrec_decodeStagePair) (fst.comp _root_.Primrec.unpair))
  have h_extB : _root_.Primrec (fun p : ℕ =>
      ((decodeStagePair p).2.getD p.unpair.1 false).toNat) :=
    (_root_.Primrec.dom_bool Bool.toNat).comp
      ((_root_.Primrec.list_getD false).comp
        (snd.comp primrec_decodeStagePair) (fst.comp _root_.Primrec.unpair))
  have h_recA : Nat.RecursiveIn O (fun n => Part.some (limA n).toNat) := by
    refine (comp (Primrec.nat_iff.mp h_extA).recursiveIn h_arg).of_eq fun n => ?_
    simp only [Part.bind_eq_bind, Part.bind_some, Part.coe_some,
      decodeStagePair, Nat.unpair_pair, stageNat, Encodable.encodek, limA]
  have h_recB : Nat.RecursiveIn O (fun n => Part.some (limB n).toNat) := by
    refine (comp (Primrec.nat_iff.mp h_extB).recursiveIn h_arg).of_eq fun n => ?_
    simp only [Part.bind_eq_bind, Part.bind_some, Part.coe_some,
      decodeStagePair, Nat.unpair_pair, stageNat, Encodable.encodek, limB]
  exact ⟨RecursiveIn.iff_nat.mpr h_recA, RecursiveIn.iff_nat.mpr h_recB⟩
