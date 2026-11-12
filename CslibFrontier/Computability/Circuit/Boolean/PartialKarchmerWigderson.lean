/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.KarchmerWigderson

/-!
# Formula depth of partial functions

A *partial* Boolean function `f : BitString n → Option Bool` is `none` outside its domain. A De
Morgan formula computes it (`Formula.ComputesPartial`) when it agrees with `f` wherever `f` is
defined, and `partialFormulaDepth f` is the least depth of such a formula, with negations and
constants free. For a total function this is `formulaDepth` (`partialFormulaDepth_some`).

The Karchmer–Wigderson game of `f` (`kwRelation f`) gives Alice an input in `f⁻¹(1)` and Bob one
in `f⁻¹(0)`, as elements of the subtypes, and asks for a coordinate where they differ. The
Karchmer–Wigderson theorem holds for partial functions as well
(`natCast_partialFormulaDepth_eq_ecomplexity`) [KarchmerWigderson1990]; this is the form used by
[ChukhinKulikovMihajlinSmal2026], Definition 3.1 and Theorem 3.2 (printed p. 7; PDF p. 8), whose
`KW_f` gives Alice the input in `f⁻¹(0)` instead; the two games differ by exchanging the players.

## Main definitions

* `Cslib.Circuits.Formula.ComputesPartial`: a formula agrees with a partial function on its
  domain.
* `Cslib.Circuits.Boolean.partialFormulaDepth`: the formula depth of a partial function.
* `Cslib.Circuits.Boolean.kwRelation`: the Karchmer–Wigderson game of a partial function.

## Main results

* `Cslib.Circuits.Boolean.partialFormulaDepth_some`: on total functions it is `formulaDepth`.
* `Cslib.Circuits.Boolean.exists_computesPartial_const_of_isEmpty`: a constant formula computes a
  function that is nowhere `true` or nowhere `false`.
* `Cslib.Circuits.Boolean.natCast_partialFormulaDepth_eq_ecomplexity`: the Karchmer–Wigderson
  theorem for partial functions.

## References

* [M. Karchmer and A. Wigderson, *Monotone circuits for connectivity require super-logarithmic
  depth*][KarchmerWigderson1990]
* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
-/

public section

namespace Cslib.Circuits

open Boolean Cslib.Communication

variable {n : ℕ}

/-- A De Morgan formula computes the partial function `f` when it agrees with `f` wherever `f` is
defined. -/
@[expose] def Formula.ComputesPartial (F : Formula signature n) (f : BitString n → Option Bool) :
    Prop :=
  ∀ x b, f x = some b → F.eval interpretation x = b

namespace Boolean

variable {f : BitString n → Option Bool}

/-- A formula computing a total function computes it as a partial function. -/
theorem _root_.Cslib.Circuits.Formula.Computes.computesPartial {F : Formula signature n}
    {g : BooleanFunction n} (hF : F.Computes interpretation g) :
    F.ComputesPartial fun x => some (g x) :=
  fun x _ h => (hF x).trans (Option.some_injective _ h)

/-- Every partial function has a De Morgan formula: one for any total extension. -/
theorem exists_computesPartial (f : BitString n → Option Bool) :
    ∃ F : Formula signature n, F.ComputesPartial f := by
  obtain ⟨F, hF⟩ := Formula.exists_computes fun x => (f x).getD false
  exact ⟨F, fun x b h => by simp [hF x, h]⟩

/-- The least depth of a De Morgan formula computing the partial function `f`, with negations and
constants free. -/
noncomputable def partialFormulaDepth (f : BitString n → Option Bool) : ℕ :=
  sInf {d | ∃ F : Formula signature n, F.ComputesPartial f ∧ F.depthWith binaryCost = d}

/-- The partial formula depth is at most the depth of every formula computing the function. -/
theorem partialFormulaDepth_le {F : Formula signature n} (hF : F.ComputesPartial f) :
    partialFormulaDepth f ≤ F.depthWith binaryCost :=
  Nat.sInf_le ⟨F, hF, rfl⟩

/-- Some formula attains the partial formula depth. -/
theorem exists_computesPartial_depthWith_eq (f : BitString n → Option Bool) :
    ∃ F : Formula signature n, F.ComputesPartial f ∧
      F.depthWith binaryCost = partialFormulaDepth f :=
  Nat.sInf_mem (s := {d | ∃ F : Formula signature n, F.ComputesPartial f ∧
    F.depthWith binaryCost = d}) <|
    let ⟨F, hF⟩ := exists_computesPartial f
    ⟨_, F, hF, rfl⟩

/-- On a total function, the partial formula depth is the formula depth. -/
theorem partialFormulaDepth_some (g : BooleanFunction n) :
    partialFormulaDepth (fun x => some (g x)) = formulaDepth g := by
  refine le_antisymm ?_ ?_
  · obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth g
    exact (partialFormulaDepth_le hF.computesPartial).trans hd.le
  · obtain ⟨F, hF, hd⟩ := exists_computesPartial_depthWith_eq fun x => some (g x)
    exact (formulaDepth_le fun x => hF x _ rfl).trans hd.le

/-- The Karchmer–Wigderson game of a partial function: Alice holds an input in `f⁻¹(1)`, Bob one
in `f⁻¹(0)`, and they must name a coordinate where the two differ. -/
@[expose] def kwRelation (f : BitString n → Option Bool) :
    {x // f x = some true} → {y // f y = some false} → Fin n → Prop :=
  fun x y i => DiffersAt x.1 y.1 i

/-- A formula computing `f` gives a protocol for its Karchmer–Wigderson game with at most as many
bits as the formula has AND and OR gates on a path. -/
theorem exists_kwProtocol_of_computesPartial [NeZero n] {F : Formula signature n}
    (hF : F.ComputesPartial f) :
    ∃ p : Communication.Protocol {x // f x = some true} {y // f y = some false} (Fin n),
      p.Solves (kwRelation f) Set.univ Set.univ ∧ p.depth ≤ F.depthWith binaryCost :=
  ⟨(F.kwProtocol true).comap Subtype.val Subtype.val, fun x _ y _ => by
    simpa [kwRelation] using F.differsAt_run_kwProtocol true (hF _ _ x.2) (hF _ _ y.2),
    by simpa using F.depth_kwProtocol_le true⟩

/-- If `f` is nowhere `true`, or nowhere `false`, a constant formula computes it. -/
theorem exists_computesPartial_const_of_isEmpty
    (h : IsEmpty {x // f x = some true} ∨ IsEmpty {y // f y = some false}) :
    ∃ F : Formula signature n, F.ComputesPartial f ∧ F.depthWith binaryCost = 0 := by
  rcases h with h | h
  · refine ⟨.const false, fun x b hx => ?_, by simp⟩
    cases b
    · simp
    · exact (h.false ⟨x, hx⟩).elim
  · refine ⟨.const true, fun x b hx => ?_, by simp⟩
    cases b
    · exact (h.false ⟨x, hx⟩).elim
    · simp

/-- If `f` is nowhere `true`, or nowhere `false`, its partial formula depth is zero. -/
theorem partialFormulaDepth_eq_zero_of_isEmpty
    (h : IsEmpty {x // f x = some true} ∨ IsEmpty {y // f y = some false}) :
    partialFormulaDepth f = 0 :=
  let ⟨_, hF, hd⟩ := exists_computesPartial_const_of_isEmpty h
  Nat.eq_zero_of_le_zero ((partialFormulaDepth_le hF).trans hd.le)

open scoped Classical in
/-- A protocol for the Karchmer–Wigderson game of `f` gives a formula computing `f` with at most
as many AND and OR gates on a path as the protocol sends bits: `Protocol.kwFormula` of the
protocol run on `f⁻¹(1) × f⁻¹(0)`, or a constant when one side is empty. -/
theorem exists_computesPartial_of_solves
    {p : Communication.Protocol {x // f x = some true} {y // f y = some false} (Fin n)}
    (hp : p.Solves (kwRelation f) Set.univ Set.univ) :
    ∃ F : Formula signature n, F.ComputesPartial f ∧ F.depthWith binaryCost ≤ p.depth := by
  by_cases h : IsEmpty {x // f x = some true} ∨ IsEmpty {y // f y = some false}
  · obtain ⟨F, hF, hd⟩ := exists_computesPartial_const_of_isEmpty h
    exact ⟨F, hF, hd.trans_le (Nat.zero_le _)⟩
  simp only [not_or, not_isEmpty_iff] at h
  obtain ⟨hA, hB⟩ := h
  obtain ⟨x₀⟩ := hA
  obtain ⟨y₀⟩ := hB
  let a : BitString n → {x // f x = some true} := fun x => if h : f x = some true then ⟨x, h⟩
    else x₀
  let b : BitString n → {y // f y = some false} := fun y => if h : f y = some false then ⟨y, h⟩
    else y₀
  set q : KWProtocol (Fin n) := p.comap a b
  have hq : q.Solves DiffersAt {x | f x = some true} {y | f y = some false} := by
    intro x hx y hy
    have := hp (a x) trivial (b y) trivial
    simp only [Set.mem_ofPred_eq] at hx hy
    simpa [q, a, b, hx, hy, kwRelation] using this
  refine ⟨q.kwFormula {x | f x = some true} {y | f y = some false}, fun x c h => ?_,
    by simpa [q] using q.depthWith_kwFormula_le _ _⟩
  cases c
  · exact Communication.Protocol.eval_kwFormula_of_mem_right hq h
  · exact Communication.Protocol.eval_kwFormula_of_mem_left hq h

/-- **The Karchmer–Wigderson theorem for partial functions.** The least depth of a De Morgan
formula computing a partial function of at least one bit, with negations free, is the
communication complexity of its Karchmer–Wigderson game. -/
theorem natCast_partialFormulaDepth_eq_ecomplexity [NeZero n] (f : BitString n → Option Bool) :
    (partialFormulaDepth f : ℕ∞) =
      Communication.Protocol.ecomplexity (kwRelation f) Set.univ Set.univ := by
  refine le_antisymm (Communication.Protocol.le_ecomplexity_iff.2 fun p hp => ?_) ?_
  · obtain ⟨F, hF, hd⟩ := exists_computesPartial_of_solves hp
    exact_mod_cast (partialFormulaDepth_le hF).trans hd
  · obtain ⟨F, hF, hd⟩ := exists_computesPartial_depthWith_eq f
    obtain ⟨p, hp, hpd⟩ := exists_kwProtocol_of_computesPartial hF
    exact (Communication.Protocol.ecomplexity_le_depth hp).trans (by exact_mod_cast hpd.trans hd.le)

end Boolean

end Cslib.Circuits
