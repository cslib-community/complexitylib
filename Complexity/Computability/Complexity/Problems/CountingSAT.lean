/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ModP
public import Complexity.Computability.Complexity.Classes.US
public import Complexity.Computability.Complexity.Problems.SharpSAT
public import Complexity.Computability.Complexity.Problems.USAT
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Complexity.CookLevin.Counting
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Logics.Propositional.CNF.ModelCount.Relabel

/-!
# Complete problems for the counting classes

Since the Cook–Levin reduction is parsimonious (`CookLevin.SharpSAT_sharpPHard`), each counting
class defined by a condition on a function in `#P` has a complete problem defined by the same
condition on the number of satisfying assignments of a formula (`SharpSAT`), under
polynomial-time many-one reductions [Valiant][Valiant1979]. The classes are the verifier-based
ones of this library, following [Fortnow, Section 4][Fortnow1997].

* `ParitySAT`, an odd number of satisfying assignments, is `⊕P`-complete
  [Papadimitriou and Zachos][PapadimitriouZachos1983];
* `USAT`, exactly one satisfying assignment (`SharpSAT.mem_USAT_iff`), is `US`-complete
  [Blass and Gurevich][BlassGurevich1982];
* `ModSAT k`, a number of satisfying assignments not divisible by `k`, is `ModP k`-complete, and
  its complement is `coModP k`-complete, for every modulus `k`; the modular classes are those of
  [Cai and Hemachandra][CaiHemachandra1990] and
  [Beigel, Gill and Hertrampf][BeigelGillHertrampf1990];
* `SharpSATAtLeast`, the pairs `(φ, m)` of a formula and a number in binary such that `φ` has at
  least `m` satisfying assignments, is `PP`-complete; it is a threshold variant of the majority
  problem `MAJSAT`, the formulas satisfied by strictly more than half of the truth assignments to
  their occurring variables, which is also `PP`-complete [Gill][Gill1977],
  [Simon][Simon1975], [Papadimitriou, Chapter 11][Papadimitriou94];
* `SharpSATExact`, the pairs `(φ, m)` such that `φ` has exactly `m` satisfying assignments, is
  `C=P`-complete, and its complement is `coC=P`-complete; `C=P` and complete problems for it
  were introduced by [Wagner][Wagner1986].

The first four follow one pattern (`polyTimeComplete_sharpSAT`): a problem in the class is
`{a | Q (f a)}` for some `f ∈ #P`, and the parsimonious reduction `r` for `f` reduces it to
`{φ | Q (SharpSAT φ)}`. For `PP`, the characterization of `PP` through `#P`
(`mem_PP_iff_exists_SharpP`) gives `a ∈ A ↔ 2 ^ q(n) < 2 f(a)`; the reduction to
`SharpSATAtLeast` maps `a` to the formula for `2 f` with the threshold `2 ^ q(n) + 1`, and the
reduction to `MAJSAT` pads that formula (`padMajority`) with `q(n)` even-numbered dummy variables
and a selector variable `0` so that the padded formula has `1 + q(n) + k` occurring variables and
`2 f(a) + 2 ^ (q(n) + k) - 2 ^ q(n)` satisfying assignments. For `C=P`, a problem in the class is
`{a | f₁ a = f₂ a}` for `f₁, f₂ ∈ #P`, with `f₂ ≤ 2 ^ p(n)` and `2 ^ p(n) - f₂ ∈ #P`
(`SharpP.exists_two_pow_sub_mem`); the reduction maps `a` to the formula for `f₁ + (2 ^ p(n) - f₂)`
with the count `2 ^ p(n)`. In the pair problems the number `m` is computed in polynomial time in
binary.

## Main definitions

* `Cslib.Complexity.ParitySAT`, `Cslib.Complexity.ModSAT`, `Cslib.Complexity.MAJSAT`,
  `Cslib.Complexity.SharpSATAtLeast`, `Cslib.Complexity.SharpSATExact`.
* `Cslib.Complexity.shiftOdd`, `Cslib.Complexity.dummyClauses`,
  `Cslib.Complexity.padMajority`: padding a formula to a majority instance.

## Main results

* `Cslib.Complexity.ParitySAT_parityPComplete`: `⊕SAT` is `⊕P`-complete.
* `Cslib.Complexity.USAT_usComplete`: `USAT` is `US`-complete.
* `Cslib.Complexity.ModSAT_modPComplete`, `Cslib.Complexity.compl_ModSAT_coModPComplete`.
* `Cslib.Complexity.ModSAT_two`, `Cslib.Complexity.ModSAT_zero`: `ModSAT 2` is `ParitySAT` and
  `ModSAT 0` is `SAT`.
* `Cslib.Complexity.SharpSATAtLeast_ppComplete`: counting threshold is `PP`-complete.
* `Cslib.Complexity.card_vars_padMajority`, `Cslib.Complexity.sharpSAT_padMajority`,
  `Cslib.Complexity.padMajority_mem_MAJSAT_iff`: variable count and model count of a padded
  majority formula.
* `Cslib.Complexity.MAJSAT_mem_PP`, `Cslib.Complexity.MAJSAT_ppHard`,
  `Cslib.Complexity.MAJSAT_ppComplete`: majority satisfiability is `PP`-complete.
* `Cslib.Complexity.SharpSATExact_ceqPComplete`,
  `Cslib.Complexity.compl_SharpSATExact_coCeqPComplete`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [C. H. Papadimitriou, S. Zachos, *Two remarks on the power of counting*][PapadimitriouZachos1983]
* [A. Blass, Y. Gurevich, *On the unique satisfiability problem*][BlassGurevich1982]
* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [J. Simon, *On Some Central Problems in Computational Complexity*][Simon1975]
* [J.-Y. Cai, L. A. Hemachandra, *On the power of parity polynomial time*][CaiHemachandra1990]
* [R. Beigel, J. Gill, U. Hertrampf, *Counting classes: thresholds, parity, mods, and
  fewness*][BeigelGillHertrampf1990]
* [K. W. Wagner, *The complexity of combinatorial problems with succinct input
  representation*][Wagner1986]
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The problems -/

/-- **⊕SAT**: the formulas with an odd number of satisfying assignments. -/
def ParitySAT : Set (CNF ℕ) := {φ | Odd (SharpSAT φ)}

/-- **Mod_k SAT**: the formulas whose number of satisfying assignments is not divisible by `k`. -/
def ModSAT (k : ℕ) : Set (CNF ℕ) := {φ | SharpSAT φ % k ≠ 0}

/-- **MAJSAT**: the formulas satisfied by strictly more than half of the truth assignments to their
occurring variables (`2 ^ φ.vars.toFinset.card < 2 * SharpSAT φ`) [Gill][Gill1977],
[Simon][Simon1975]. -/
def MAJSAT : Set (CNF ℕ) := {φ | 2 ^ φ.vars.toFinset.card < 2 * SharpSAT φ}

/-- The pairs `(φ, m)` such that `φ` has at least `m` satisfying assignments. Instances are
encoded with `m` in binary (`encPair encCNF encNat`). -/
def SharpSATAtLeast : Set (CNF ℕ × ℕ) := {x | x.2 ≤ SharpSAT x.1}

/-- The pairs `(φ, m)` such that `φ` has exactly `m` satisfying assignments. Instances are
encoded with `m` in binary (`encPair encCNF encNat`). -/
def SharpSATExact : Set (CNF ℕ × ℕ) := {x | SharpSAT x.1 = x.2}

/-- Modulo two, a nonzero residue is oddness. -/
theorem ModSAT_two : ModSAT 2 = ParitySAT := by
  ext φ
  simp [ModSAT, ParitySAT, Nat.odd_iff]

/-- Modulo zero, a nonzero residue is a positive count: `ModSAT 0` is satisfiability. -/
theorem ModSAT_zero : ModSAT 0 = SAT := by
  ext φ
  simp [ModSAT, SharpSAT.mem_SAT_iff, Nat.pos_iff_ne_zero]

/-! ### Completeness through the parsimonious reduction -/

/-- **Complete problems from conditions on counts.** If the problems of a class `C` are, for
every encoding, the sets `{a | Q (f a)}` for functions `f` in `#P`, then
`{φ | Q (SharpSAT φ)}` is `C`-complete. -/
theorem polyTimeComplete_sharpSAT {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (Q : ℕ → Prop) (hC : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α),
      A ∈ C enc ↔ ∃ f ∈ SharpP enc, ∀ a, a ∈ A ↔ Q (f a)) :
    PolyTimeComplete C encCNF {φ | Q (SharpSAT φ)} := by
  refine ⟨(hC encCNF _).2 ⟨SharpSAT, SharpSAT.mem_SharpP, fun _ => Iff.rfl⟩,
    fun _ enc A hA => ?_⟩
  obtain ⟨f, hf, hA⟩ := (hC enc A).1 hA
  obtain ⟨r, hr, hfr⟩ := CookLevin.SharpSAT_sharpPHard enc f hf
  exact ⟨r, hr, fun a => (hA a).trans (by rw [hfr a]; rfl)⟩

/-- **`⊕SAT` is `⊕P`-complete.** -/
theorem ParitySAT_parityPComplete : PolyTimeComplete ParityP encCNF ParitySAT :=
  polyTimeComplete_sharpSAT Odd fun _ _ => mem_ParityP_iff_exists_SharpP

/-- **`USAT` is `US`-complete**: unique satisfiability is complete for the class of problems
defined by a function in `#P` equal to one. -/
theorem USAT_usComplete : PolyTimeComplete US encCNF USAT := by
  have h := polyTimeComplete_sharpSAT (C := US) (· = 1) fun _ _ => Iff.rfl
  rwa [show {φ | SharpSAT φ = 1} = USAT from Set.ext fun _ => SharpSAT.mem_USAT_iff.symm] at h

/-- **`Mod_k SAT` is `ModP k`-complete**, for every modulus `k`. -/
theorem ModSAT_modPComplete (k : ℕ) : PolyTimeComplete (ModP k) encCNF (ModSAT k) :=
  polyTimeComplete_sharpSAT (· % k ≠ 0) fun _ _ => Iff.rfl

/-- **The complement of `Mod_k SAT` is `coModP k`-complete**, for every modulus `k`. -/
theorem compl_ModSAT_coModPComplete (k : ℕ) : PolyTimeComplete (coModP k) encCNF (ModSAT k)ᶜ :=
  (ModSAT_modPComplete k).compl fun _ _ => Iff.rfl

/-! ### Thresholds and exact counts -/

/-- The polynomial-time threshold `2 ^ q(n) + j`, in binary, for instances of encoded length
`n`. -/
private theorem computableInPolyTime_two_pow_add {α : Type} (enc : α ↪ List Bool)
    (q : Polynomial ℕ) (j : ℕ) :
    ComputableInPolyTime (fun a => 2 ^ q.eval (enc a).length + j) enc encNat :=
  ComputableInPolyTime.binary_add.comp ((ComputableInPolyTime.binary_two_pow.comp
    ((ComputableInPolyTime.unary_eval q).comp
      (ComputableInPolyTime.encoding_length enc))).prod (.const j))

/-- The number given with a formula, as a function in `#P`. -/
private theorem snd_mem_SharpP : (Prod.snd : CNF ℕ × ℕ → ℕ) ∈ SharpP (encPair encCNF encNat) :=
  mem_SharpP_of_polyTime (.snd encCNF encNat)

/-- The number of satisfying assignments of the formula of a pair, as a function in `#P`. -/
private theorem sharpSAT_fst_mem_SharpP :
    (fun x : CNF ℕ × ℕ => SharpSAT x.1) ∈ SharpP (encPair encCNF encNat) :=
  SharpP.comp_mem SharpSAT.mem_SharpP (.fst encCNF encNat)

/-- **Counting threshold is `PP`-complete**: whether a formula has at least `m` satisfying
assignments, for `m` given in binary. -/
theorem SharpSATAtLeast_ppComplete :
    PolyTimeComplete PP (encPair encCNF encNat) SharpSATAtLeast := by
  refine ⟨mem_PP_iff_exists_GapP.2 ⟨_, GapP.natCast_sub_natCast_mem
    (SharpP.add_one_mem sharpSAT_fst_mem_SharpP) snd_mem_SharpP, fun x => ?_⟩,
    fun _ enc A hA => ?_⟩
  · simp only [SharpSATAtLeast, Set.mem_ofPred_eq, Pi.add_apply, Pi.one_apply]
    omega
  · obtain ⟨f, hf, q, hA⟩ := mem_PP_iff_exists_SharpP.1 hA
    obtain ⟨r, hr, hfr⟩ := CookLevin.SharpSAT_sharpPHard enc _ (SharpP.add_mem hf hf)
    refine ⟨fun a => (r a, 2 ^ q.eval (enc a).length + 1),
      hr.prod (computableInPolyTime_two_pow_add enc q 1), fun a => ?_⟩
    have := hfr a
    simp only [Pi.add_apply] at this
    simp only [SharpSATAtLeast, Set.mem_ofPred_eq, hA a, ← this]
    omega

/-- **Exact counting is `C=P`-complete**: whether a formula has exactly `m` satisfying
assignments, for `m` given in binary. -/
theorem SharpSATExact_ceqPComplete :
    PolyTimeComplete CeqP (encPair encCNF encNat) SharpSATExact := by
  refine ⟨mem_CeqP_iff_exists_SharpP.2 ⟨_, sharpSAT_fst_mem_SharpP, _, snd_mem_SharpP,
    fun _ => Iff.rfl⟩, fun _ enc A hA => ?_⟩
  obtain ⟨f₁, hf₁, f₂, hf₂, hA⟩ := mem_CeqP_iff_exists_SharpP.1 hA
  obtain ⟨p, hle, hsub⟩ := SharpP.exists_two_pow_sub_mem hf₂
  obtain ⟨r, hr, hfr⟩ := CookLevin.SharpSAT_sharpPHard enc _ (SharpP.add_mem hf₁ hsub)
  refine ⟨fun a => (r a, 2 ^ p.eval (enc a).length),
    by simpa using hr.prod (computableInPolyTime_two_pow_add enc p 0),
    fun a => ?_⟩
  have h₁ := hfr a
  have h₂ := hle a
  simp only [Pi.add_apply] at h₁
  simp only [SharpSATExact, Set.mem_ofPred_eq, hA a, ← h₁]
  omega

/-- **The complement of exact counting is `coC=P`-complete.** -/
theorem compl_SharpSATExact_coCeqPComplete :
    PolyTimeComplete coCeqP (encPair encCNF encNat) SharpSATExactᶜ :=
  SharpSATExact_ceqPComplete.compl fun _ _ => Iff.rfl

/-! ### Majority satisfiability -/

/-- The number of assignments to the occurring variables of a formula, as a function in `#P`. -/
private theorem two_pow_card_vars_mem_SharpP :
    (fun φ : CNF ℕ => 2 ^ φ.vars.toFinset.card) ∈ SharpP encCNF :=
  mem_SharpP_of_polyTime (ComputableInPolyTime.binary_two_pow.comp
    SharpSAT.computableInPolyTime_card_vars)

/-- **`MAJSAT` belongs to `PP`.** -/
theorem MAJSAT_mem_PP : MAJSAT ∈ PP encCNF := by
  refine mem_PP_iff_exists_GapP.2 ⟨_, GapP.natCast_sub_natCast_mem
    (SharpP.add_mem SharpSAT.mem_SharpP SharpSAT.mem_SharpP) two_pow_card_vars_mem_SharpP,
    fun φ => ?_⟩
  simp only [MAJSAT, Set.mem_ofPred_eq, Pi.add_apply]
  omega

/-- Relabel the variables of `φ` to the odd numbers `2 v + 1`. -/
def shiftOdd (φ : CNF ℕ) : CNF ℕ :=
  φ.relabel (fun v => v + v + 1)

/-- Clauses forcing the `Q` positive even dummy variables `2, 4, …, 2 Q` to `false` when the
selector variable `0` is `false`. -/
def dummyClauses (Q : ℕ) : CNF ℕ :=
  (List.range Q).map (fun j => [(0, true), (j + j + 2, false)])

/-- Pad `φ` with `Q` even dummy variables `2, 4, …, 2 Q` and a selector variable `0` so that the
resulting formula has `1 + Q + φ.vars.toFinset.card` occurring variables and
`SharpSAT φ + (2 ^ (Q + φ.vars.toFinset.card) - 2 ^ Q)` satisfying assignments. -/
def padMajority (φ : CNF ℕ) (Q : ℕ) : CNF ℕ :=
  (shiftOdd φ).map ((0, true) :: ·) ++
    dummyClauses Q ++
    [(0, false) :: (shiftOdd φ).vars.map (·, true)]

@[local fun_prop]
private theorem computableInPolyTime_shiftOdd :
    ComputableInPolyTime shiftOdd encCNF encCNF := by
  unfold shiftOdd encCNF
  exact CNF.computableInPolyTime_relabel (f := fun v : ℕ => v + v + 1) (by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_dummyClauses :
    ComputableInPolyTime dummyClauses encUnary encCNF := by
  have hj : ComputableInPolyTime (fun j : ℕ => j + j + 2) encUnary encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  unfold dummyClauses encCNF
  exact (ComputableInPolyTime.map (encA := encUnary)
    (encB := encList (encPair encNat encBool)) (by fun_prop)).comp
    ComputableInPolyTime.range

/-- Padding a formula to a majority instance is computable in polynomial time, with `Q` in unary. -/
@[fun_prop]
theorem computableInPolyTime_padMajority :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => padMajority p.1 p.2)
      (encPair encCNF encUnary) encCNF := by
  have hshift : ComputableInPolyTime (fun p : CNF ℕ × ℕ => shiftOdd p.1)
      (encPair encCNF encUnary) (encList (encList (encPair encNat encBool))) :=
    computableInPolyTime_shiftOdd.comp (.fst encCNF encUnary)
  have hdummy : ComputableInPolyTime (fun p : CNF ℕ × ℕ => dummyClauses p.2)
      (encPair encCNF encUnary) (encList (encList (encPair encNat encBool))) :=
    computableInPolyTime_dummyClauses.comp (.snd encCNF encUnary)
  unfold padMajority encCNF
  refine ComputableInPolyTime.listAppend'
    (ComputableInPolyTime.listAppend' ?_ hdummy) ?_
  · exact (ComputableInPolyTime.map
      (encA := encList (encPair encNat encBool))
      (encB := encList (encPair encNat encBool)) (by fun_prop)).comp hshift
  · refine ComputableInPolyTime.cons' ?_ (.const [])
    refine ComputableInPolyTime.cons' (.const (0, false)) ?_
    exact (ComputableInPolyTime.map (encA := encNat)
      (encB := encPair encNat encBool) (by fun_prop)).comp
      ((CNF.computableInPolyTime_vars encNat).comp hshift)

private theorem injective_shiftOdd_fn : Function.Injective (fun v : ℕ => v + v + 1) := by
  intro a b h
  dsimp only at h
  omega

private theorem odd_of_mem_vars_shiftOdd {φ : CNF ℕ} {v : ℕ} (hv : v ∈ (shiftOdd φ).vars) :
    v % 2 = 1 := by
  rw [shiftOdd, CNF.vars_relabel, List.mem_map] at hv
  rcases hv with ⟨w, -, rfl⟩
  omega

private theorem card_vars_shiftOdd (φ : CNF ℕ) :
    (shiftOdd φ).vars.toFinset.card = φ.vars.toFinset.card := by
  have heq : (shiftOdd φ).vars.toFinset = φ.vars.toFinset.image (fun v => v + v + 1) := by
    ext v
    simp [shiftOdd, CNF.vars_relabel]
  rw [heq, Finset.card_image_of_injective _ injective_shiftOdd_fn]

private theorem mem_vars_padMajority {φ : CNF ℕ} {Q v : ℕ} :
    v ∈ (padMajority φ Q).vars ↔
      v = 0 ∨ (∃ j < Q, v = j + j + 2) ∨ v ∈ (shiftOdd φ).vars := by
  simp only [padMajority, dummyClauses, CNF.mem_vars, List.mem_append, List.mem_map,
    List.mem_range, List.mem_singleton]
  constructor
  · rintro ⟨c, (⟨c₀, hc₀, rfl⟩ | ⟨j, hj, rfl⟩) | rfl, b, hlit⟩
    · rcases List.mem_cons.1 hlit with ⟨rfl, rfl⟩ | hlit
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨c₀, hc₀, b, hlit⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hlit
      rcases hlit with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
    · simp only [List.mem_cons, List.mem_map, Prod.mk.injEq] at hlit
      rcases hlit with ⟨rfl, -⟩ | ⟨w, hw, rfl, -⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (CNF.mem_vars.1 hw))
  · rintro (rfl | ⟨j, hj, rfl⟩ | hv)
    · exact ⟨_, Or.inr rfl, false, List.mem_cons_self ..⟩
    · exact ⟨_, Or.inl (Or.inr ⟨j, hj, rfl⟩), false,
        List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩
    · exact ⟨_, Or.inr rfl, true,
        List.mem_cons_of_mem _ (List.mem_map.2 ⟨v, CNF.mem_vars.2 hv, rfl⟩)⟩

/-- **Variable count of `padMajority`**: the padded formula has `1 + Q + φ.vars.toFinset.card`
distinct occurring variables. -/
theorem card_vars_padMajority (φ : CNF ℕ) (Q : ℕ) :
    (padMajority φ Q).vars.toFinset.card = 1 + Q + φ.vars.toFinset.card := by
  let S₀ : Finset ℕ := {0}
  let S₁ : Finset ℕ := (Finset.range Q).image (fun j => j + j + 2)
  let S₂ : Finset ℕ := (shiftOdd φ).vars.toFinset
  have heq : (padMajority φ Q).vars.toFinset = (S₀ ∪ S₁) ∪ S₂ := by
    ext v
    simp only [S₀, S₁, S₂, List.mem_toFinset, mem_vars_padMajority, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩ | hv)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
      · exact Or.inr hv
    · rintro ((rfl | ⟨j, hj, rfl⟩) | hv)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
      · exact Or.inr (Or.inr hv)
  have hd₀₁ : Disjoint S₀ S₁ := by
    rw [Finset.disjoint_left]
    intro v hv₀ hv₁
    simp only [S₀, S₁, Finset.mem_singleton, Finset.mem_image, Finset.mem_range] at hv₀ hv₁
    rcases hv₁ with ⟨j, -, hj⟩
    omega
  have hd₀₁₂ : Disjoint (S₀ ∪ S₁) S₂ := by
    rw [Finset.disjoint_left]
    intro v hv₀₁ hv₂
    have hodd := odd_of_mem_vars_shiftOdd (List.mem_toFinset.1 hv₂)
    simp only [S₀, S₁, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_range] at hv₀₁
    rcases hv₀₁ with rfl | ⟨j, -, rfl⟩ <;> omega
  have hcard₁ : S₁.card = Q := by
    dsimp [S₁]
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  rw [heq, Finset.card_union_of_disjoint hd₀₁₂, Finset.card_union_of_disjoint hd₀₁,
    Finset.card_singleton, hcard₁, card_vars_shiftOdd]

private theorem eval_padMajority_eq_true_iff (σ : ℕ → Bool) (φ : CNF ℕ) (Q : ℕ) :
    (padMajority φ Q).eval σ = true ↔
      if σ 0 = false then
        (shiftOdd φ).eval σ = true ∧ ∀ j < Q, σ (j + j + 2) = false
      else
        ∃ v ∈ (shiftOdd φ).vars, σ v = true := by
  have h1 : CNF.eval σ ((shiftOdd φ).map ((0, true) :: ·)) = true ↔
      (σ 0 = true ∨ (shiftOdd φ).eval σ = true) := by
    simp only [CNF.eval_eq_true_iff, List.mem_map, Clause.eval_cons, Literal.eval_eq_true_iff,
      Bool.or_eq_true, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    cases σ 0 <;> simp
  have h2 : (dummyClauses Q).eval σ = true ↔
      (σ 0 = true ∨ ∀ j < Q, σ (j + j + 2) = false) := by
    simp only [dummyClauses, CNF.eval_map_eq_true_iff, List.mem_range, Clause.eval_cons,
      Clause.eval_nil, Bool.or_false, Literal.eval_eq_true_iff, Bool.or_eq_true]
    cases σ 0 <;> simp
  have h3 : Clause.eval σ ((0, false) :: (shiftOdd φ).vars.map (·, true)) = true ↔
      (σ 0 = false ∨ ∃ v ∈ (shiftOdd φ).vars, σ v = true) := by
    simp [Clause.eval_eq_true_iff]
  simp only [padMajority, CNF.eval_append, CNF.eval_cons, CNF.eval_nil, Bool.and_true,
    Bool.and_eq_true, h1, h2, h3]
  cases σ 0 <;> simp

/-- The coordinates of an assignment that matter for `padMajority φ Q`: the selector variable `0`,
the dummy variables `2, 4, …, 2 Q`, and the variables of `shiftOdd φ`. -/
private def padSplit (φ : CNF ℕ) (Q : ℕ) (σ : ℕ → Bool) :
    Bool × (Fin Q → Bool) × ((shiftOdd φ).vars.toFinset → Bool) :=
  (σ 0, fun j => σ (j.1 + j.1 + 2), fun v => σ v.1)

/-- Two assignments have the same coordinates exactly when they agree on the variables of
`padMajority φ Q`. -/
private theorem padSplit_eq_iff {φ : CNF ℕ} {Q : ℕ} {σ τ : ℕ → Bool} :
    padSplit φ Q σ = padSplit φ Q τ ↔ ∀ v ∈ (padMajority φ Q).vars, σ v = τ v := by
  simp only [padSplit, Prod.mk.injEq, funext_iff, Fin.forall_iff, Subtype.forall,
    List.mem_toFinset]
  constructor
  · rintro ⟨h0, heven, hodd⟩ v hv
    rcases mem_vars_padMajority.1 hv with rfl | ⟨j, hj, rfl⟩ | hv'
    · exact h0
    · exact heven j hj
    · exact hodd v hv'
  · intro h
    exact ⟨h 0 (mem_vars_padMajority.2 (Or.inl rfl)),
      fun j hj => h _ (mem_vars_padMajority.2 (Or.inr (Or.inl ⟨j, hj, rfl⟩))),
      fun v hv => h v (mem_vars_padMajority.2 (Or.inr (Or.inr hv)))⟩

/-- Every choice of coordinates comes from an assignment: the selector at `0`, the dummy values
at the even variables and an extension of the values on the odd variables of `shiftOdd φ`. -/
private theorem padSplit_surjective (φ : CNF ℕ) (Q : ℕ) : Function.Surjective (padSplit φ Q) := by
  rintro ⟨b, δ, τ⟩
  refine ⟨fun v => if v = 0 then b
    else if v % 2 = 0 then (if h : v / 2 - 1 < Q then δ ⟨v / 2 - 1, h⟩ else false)
    else (shiftOdd φ).extendAssignment τ v, ?_⟩
  refine Prod.ext rfl (Prod.ext (funext fun j => ?_) (funext fun ⟨v, hv⟩ => ?_))
  · -- The dummy variable `2 j + 2` is even and nonzero.
    have h1 : j.1 + j.1 + 2 ≠ 0 := by omega
    have h2 : (j.1 + j.1 + 2) % 2 = 0 := by omega
    have h3 : (j.1 + j.1 + 2) / 2 - 1 = j.1 := by omega
    simp only [padSplit, h1, h2, h3, j.2, ↓reduceIte, ↓reduceDIte, Fin.eta]
  · -- The variables of `shiftOdd φ` are odd.
    have hv' := List.mem_toFinset.1 hv
    have hmod := odd_of_mem_vars_shiftOdd hv'
    have h1 : v ≠ 0 := by omega
    have h2 : ¬v % 2 = 0 := by omega
    simp only [padSplit, h1, h2, ↓reduceIte, CNF.extendAssignment_of_mem _ hv']

/-- The coordinates of the satisfying assignments of `padMajority φ Q`: with selector `false`, a
model of `shiftOdd φ` and all dummy variables `false`; with selector `true`, any dummy values and
values on the variables of `shiftOdd φ` that are not all `false`. -/
private def padModels (φ : CNF ℕ) (Q : ℕ) :
    Bool × (Fin Q → Bool) × ((shiftOdd φ).vars.toFinset → Bool) → Prop
  | (false, δ, τ) =>
    δ = (fun _ => false) ∧ (shiftOdd φ).eval ((shiftOdd φ).extendAssignment τ) = true
  | (true, _, τ) => τ ≠ fun _ => false

/-- `padModels` is decidable, case by case on the selector. -/
private instance (φ : CNF ℕ) (Q : ℕ) : DecidablePred (padModels φ Q)
  | (false, _, _) => inferInstanceAs (Decidable (_ ∧ _))
  | (true, _, _) => inferInstanceAs (Decidable (¬_))

/-- An assignment satisfies `padMajority φ Q` exactly when its coordinates are those of a
satisfying assignment. -/
private theorem padModels_padSplit_iff (σ : ℕ → Bool) (φ : CNF ℕ) (Q : ℕ) :
    padModels φ Q (padSplit φ Q σ) ↔ (padMajority φ Q).eval σ = true := by
  rw [eval_padMajority_eq_true_iff, padSplit]
  cases σ 0 <;>
    simp [padModels, CNF.eval_extendAssignment_restrict, funext_iff, Fin.forall_iff, and_comm]

/-- **Counting the coordinates of satisfying assignments.** Selector `false` contributes the models
of `φ`, and selector `true` all `2 ^ Q * (2 ^ |vars φ| - 1)` other choices. -/
private theorem card_filter_padModels (φ : CNF ℕ) (Q : ℕ) :
    (Finset.univ.filter (padModels φ Q)).card =
      SharpSAT φ + (2 ^ (Q + φ.vars.toFinset.card) - 2 ^ Q) := by
  let S_false : Finset (Bool × (Fin Q → Bool) × ((shiftOdd φ).vars.toFinset → Bool)) :=
    {false} ×ˢ (({fun _ : Fin Q => false} : Finset (Fin Q → Bool)) ×ˢ
      (Finset.univ.filter fun τ : (shiftOdd φ).vars.toFinset → Bool =>
        (shiftOdd φ).eval ((shiftOdd φ).extendAssignment τ) = true))
  let S_true : Finset (Bool × (Fin Q → Bool) × ((shiftOdd φ).vars.toFinset → Bool)) :=
    {true} ×ˢ ((Finset.univ : Finset (Fin Q → Bool)) ×ˢ
      (Finset.univ.erase (fun _ : (shiftOdd φ).vars.toFinset => false)))
  have hfilter : Finset.univ.filter (padModels φ Q) = S_false ∪ S_true := by
    ext ⟨b, δ, τ⟩
    cases b <;> simp only [padModels, S_false, S_true, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union, Finset.mem_product, Finset.mem_singleton, Finset.mem_erase,
      Bool.false_eq_true, Bool.true_eq_false, false_and, or_false, false_or, ne_eq, and_true]
  have hdisj : Disjoint S_false S_true :=
    Finset.disjoint_product.2 (Or.inl (Finset.disjoint_singleton.2 Bool.false_ne_true))
  have hS_false : S_false.card = SharpSAT φ := by
    simp only [S_false, Finset.card_product, Finset.card_singleton, one_mul]
    rw [← CNF.modelCount, shiftOdd, CNF.modelCount_relabel injective_shiftOdd_fn, ← SharpSAT]
  have hS_true : S_true.card = 2 ^ (Q + φ.vars.toFinset.card) - 2 ^ Q := by
    simp only [S_true, Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Finset.card_erase_of_mem (Finset.mem_univ _), Fintype.card_coe,
      card_vars_shiftOdd, Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add]
  rw [hfilter, Finset.card_union_of_disjoint hdisj, hS_false, hS_true]

/-- **Model count of `padMajority`**: the padded formula has
`SharpSAT φ + (2 ^ (Q + φ.vars.toFinset.card) - 2 ^ Q)` satisfying assignments. -/
theorem sharpSAT_padMajority (φ : CNF ℕ) (Q : ℕ) :
    SharpSAT (padMajority φ Q) = SharpSAT φ + (2 ^ (Q + φ.vars.toFinset.card) - 2 ^ Q) := by
  rw [SharpSAT, CNF.modelCount_eq_card_filter (padSplit φ Q) (padModels φ Q)
    (fun σ τ _ _ => padSplit_eq_iff) fun x => ?_, card_filter_padModels]
  obtain ⟨σ, rfl⟩ := padSplit_surjective φ Q x
  constructor
  · exact fun h => ⟨σ, (padModels_padSplit_iff σ φ Q).1 h, rfl⟩
  · rintro ⟨τ, hτ, h⟩
    exact h ▸ (padModels_padSplit_iff τ φ Q).2 hτ

/-- **Threshold equivalence of `padMajority`**: the padded formula belongs to `MAJSAT` if and only
if `φ` has strictly more than `2 ^ Q` satisfying assignments. -/
theorem padMajority_mem_MAJSAT_iff {φ : CNF ℕ} {Q : ℕ} :
    padMajority φ Q ∈ MAJSAT ↔ 2 ^ Q < SharpSAT φ := by
  simp only [MAJSAT, Set.mem_ofPred_eq, card_vars_padMajority, sharpSAT_padMajority]
  have hle : 2 ^ Q ≤ 2 ^ (Q + φ.vars.toFinset.card) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hpow : 2 ^ (1 + Q + φ.vars.toFinset.card) = 2 * 2 ^ (Q + φ.vars.toFinset.card) := by
    rw [Nat.add_assoc, Nat.pow_add, pow_one]
  omega

/-- **`MAJSAT` is `PP`-hard.** -/
theorem MAJSAT_ppHard : PolyTimeHard PP encCNF MAJSAT := by
  intro α enc A hA
  obtain ⟨f, hf, q, hA⟩ := mem_PP_iff_exists_SharpP.1 hA
  obtain ⟨r, hr, hfr⟩ := CookLevin.SharpSAT_sharpPHard enc _ (SharpP.add_mem hf hf)
  have hq : ComputableInPolyTime (fun a => q.eval (enc a).length) enc encUnary :=
    (ComputableInPolyTime.unary_eval q).comp
      (ComputableInPolyTime.encoding_length enc)
  refine ⟨fun a => padMajority (r a) (q.eval (enc a).length),
    computableInPolyTime_padMajority.comp (hr.prod hq), fun a => ?_⟩
  have h := hfr a
  simp only [Pi.add_apply] at h
  rw [hA a, padMajority_mem_MAJSAT_iff, ← h]
  omega

/-- **`MAJSAT` is `PP`-complete** [Gill][Gill1977], [Simon][Simon1975]. -/
theorem MAJSAT_ppComplete : PolyTimeComplete PP encCNF MAJSAT :=
  ⟨MAJSAT_mem_PP, MAJSAT_ppHard⟩

end Cslib.Complexity
