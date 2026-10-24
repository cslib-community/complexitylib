/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Formula
public import Cslib.Computability.Circuit.Boolean.Basic
public import Complexity.Computability.Circuit.Boolean.BinaryCost
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Fin

/-!
# De Morgan formulas

A *De Morgan formula* is a formula over the De Morgan signature, `Formula Boolean.signature n`,
evaluated under `Boolean.interpretation`. Negations may appear anywhere. Pushing them to the
leaves by De Morgan's laws does not change the leaf size, so lower bounds on the leaf size of these
formulas are at least as strong as for formulas whose negations sit at the leaves
[Jukna, Chapter 6][Jukna2012].

## Main definitions

* `Cslib.Circuits.Formula.const`, `Cslib.Circuits.Formula.not`, `Cslib.Circuits.Formula.and`,
  `Cslib.Circuits.Formula.or`: De Morgan formulas built from constants and smaller formulas.
* `Cslib.Circuits.Formula.xor`: the exclusive or `(F ∧ ¬G) ∨ (¬F ∧ G)`.
* `Cslib.Circuits.Formula.orList`, `Cslib.Circuits.Formula.andList`: the disjunction and the
  conjunction of a list of formulas as balanced trees of binary gates (`Formula.balanced`).
* `Cslib.Circuits.Formula.literal`: the literal of bit `i` that is true at `z`.
* `Cslib.Circuits.Boolean.formulaDepth`: the least depth of a De Morgan formula for a function,
  with negations and constants free.

## Main results

* `Cslib.Circuits.Formula.size_orList_add_one`, `Cslib.Circuits.Formula.depthWith_orList_le`,
  `Cslib.Circuits.Formula.size_andList_add_one`, `Cslib.Circuits.Formula.depthWith_andList_le`: a
  balanced tree of `k ≥ 1` formulas adds `k - 1` nodes and `⌈log₂ k⌉` levels.
* `Cslib.Circuits.Formula.exists_computes`: every Boolean function has a De Morgan formula.
* `Cslib.Circuits.Boolean.exists_computes_depthWith_eq_formulaDepth`: some formula attains the
  formula depth.
* `Cslib.Circuits.Boolean.arity_le_two`: the De Morgan basis has fan-in at most two.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Formula

open Boolean

variable {n : ℕ} (F G : Formula signature n) (x : BitString n)

/-- The constant De Morgan formula. -/
def const (c : Bool) : Formula signature n :=
  gate (.const c) Fin.elim0

/-- The negation of a De Morgan formula. -/
def not : Formula signature n :=
  gate .not ![F]

/-- The conjunction of two De Morgan formulas. -/
def and : Formula signature n :=
  gate .and ![F, G]

/-- The disjunction of two De Morgan formulas. -/
def or : Formula signature n :=
  gate .or ![F, G]

/-- The exclusive or of two De Morgan formulas, `(F ∧ ¬G) ∨ (¬F ∧ G)`. -/
def xor : Formula signature n :=
  (F.and G.not).or (F.not.and G)

/-- Evaluating `const c` returns `c`. -/
@[simp] theorem eval_const (c : Bool) : (const c : Formula signature n).eval interpretation x = c :=
  rfl

/-- Evaluating `F.not` negates the value of `F`. -/
@[simp] theorem eval_not : F.not.eval interpretation x = !F.eval interpretation x :=
  rfl

/-- Evaluating `F.and G` takes the conjunction of the values of `F` and `G`. -/
@[simp] theorem eval_and :
    (F.and G).eval interpretation x = (F.eval interpretation x && G.eval interpretation x) :=
  rfl

/-- Evaluating `F.or G` takes the disjunction of the values of `F` and `G`. -/
@[simp] theorem eval_or :
    (F.or G).eval interpretation x = (F.eval interpretation x || G.eval interpretation x) :=
  rfl

/-- Evaluating `F.xor G` takes the exclusive or of the values of `F` and `G`. -/
@[simp] theorem eval_xor :
    (F.xor G).eval interpretation x = (F.eval interpretation x ^^ G.eval interpretation x) := by
  simp only [xor, eval_or, eval_and, eval_not]
  cases F.eval interpretation x <;> cases G.eval interpretation x <;> rfl

/-- Negation preserves the leaf size of a formula. -/
@[simp] theorem leafSize_not : F.not.leafSize = F.leafSize :=
  Fin.sum_univ_one _

/-- The leaf size of a conjunction is the sum of the leaf sizes of its conjuncts. -/
@[simp] theorem leafSize_and : (F.and G).leafSize = F.leafSize + G.leafSize :=
  Fin.sum_univ_two _

/-- The leaf size of a disjunction is the sum of the leaf sizes of its disjuncts. -/
@[simp] theorem leafSize_or : (F.or G).leafSize = F.leafSize + G.leafSize :=
  Fin.sum_univ_two _

/-- The leaf size of `F.xor G` is twice the sum of the leaf sizes of `F` and `G`. -/
@[simp] theorem leafSize_xor : (F.xor G).leafSize = 2 * F.leafSize + 2 * G.leafSize := by
  simp only [xor, leafSize_or, leafSize_and, leafSize_not]
  omega

/-- A constant formula has no input leaves. -/
@[simp] theorem leafSize_const (c : Bool) : (const c : Formula signature n).leafSize = 0 :=
  rfl

/-- A constant formula has no leaves in `Y`. -/
@[simp] theorem leafSizeIn_const (Y : Finset (Fin n)) (c : Bool) :
    (const c : Formula signature n).leafSizeIn Y = 0 :=
  rfl

/-- Negation preserves the number of leaves in `Y`. -/
@[simp] theorem leafSizeIn_not (Y : Finset (Fin n)) :
    F.not.leafSizeIn Y = F.leafSizeIn Y :=
  Fin.sum_univ_one _

/-- The number of leaves in `Y` of a conjunction is the sum of those of its conjuncts. -/
@[simp] theorem leafSizeIn_and (Y : Finset (Fin n)) :
    (F.and G).leafSizeIn Y = F.leafSizeIn Y + G.leafSizeIn Y :=
  Fin.sum_univ_two _

/-- The number of leaves in `Y` of a disjunction is the sum of those of its disjuncts. -/
@[simp] theorem leafSizeIn_or (Y : Finset (Fin n)) :
    (F.or G).leafSizeIn Y = F.leafSizeIn Y + G.leafSizeIn Y :=
  Fin.sum_univ_two _

/-- A constant is one operation node. -/
@[simp] theorem size_const (c : Bool) : (const c : Formula signature n).size = 1 :=
  rfl

/-- A negation adds one operation node. -/
@[simp] theorem size_not : F.not.size = F.size + 1 := by
  simp [not]

/-- A conjunction adds one operation node. -/
@[simp] theorem size_and : (F.and G).size = F.size + G.size + 1 := by
  simp [and, Fin.sum_univ_two]

/-- A disjunction adds one operation node. -/
@[simp] theorem size_or : (F.or G).size = F.size + G.size + 1 := by
  simp [or, Fin.sum_univ_two]

/-- Exclusive or uses two copies of each argument and five operation nodes. -/
@[simp] theorem size_xor : (F.xor G).size = 2 * F.size + 2 * G.size + 5 := by
  simp only [xor, size_or, size_and, size_not]
  omega

/-- A constant has depth one. -/
@[simp] theorem depth_const (c : Bool) : (const c : Formula signature n).depth = 1 :=
  rfl

/-- A negation is one deeper than its argument. -/
@[simp] theorem depth_not : F.not.depth = F.depth + 1 := by
  simp [not]

/-- A conjunction is one deeper than the deeper conjunct. -/
@[simp] theorem depth_and : (F.and G).depth = max F.depth G.depth + 1 := by
  simp [and, Fin.univ_succ]

/-- A disjunction is one deeper than the deeper disjunct. -/
@[simp] theorem depth_or : (F.or G).depth = max F.depth G.depth + 1 := by
  simp [or, Fin.univ_succ]

/-- Exclusive or adds at most three levels beyond its deeper argument. -/
theorem depth_xor_le : (F.xor G).depth ≤ max F.depth G.depth + 3 := by
  simp only [xor, depth_or, depth_and, depth_not]
  omega

/-- The weighted depth of `const c` is `cost (.const c)`. -/
@[simp] theorem depthWith_const (cost : Op → ℕ) (c : Bool) :
    (const c : Formula signature n).depthWith cost = cost (.const c) := by
  simp [const]

/-- The weighted depth of `F.not` adds `cost .not` to the weighted depth of `F`. -/
@[simp] theorem depthWith_not (cost : Op → ℕ) :
    F.not.depthWith cost = F.depthWith cost + cost .not := by
  simp [not]

/-- The weighted depth of `F.and G` adds `cost .and` to the maximum weighted depth of `F` and
`G`. -/
@[simp] theorem depthWith_and (cost : Op → ℕ) :
    (F.and G).depthWith cost = max (F.depthWith cost) (G.depthWith cost) + cost .and := by
  simp [and, Fin.univ_succ]

/-- The weighted depth of `F.or G` adds `cost .or` to the maximum weighted depth of `F` and `G`. -/
@[simp] theorem depthWith_or (cost : Op → ℕ) :
    (F.or G).depthWith cost = max (F.depthWith cost) (G.depthWith cost) + cost .or := by
  simp [or, Fin.univ_succ]

/-- A conjunction is the binary node of `.and`. -/
@[simp] theorem gate₂_and : gate₂ (σ := signature) .and rfl F G = F.and G :=
  rfl

/-- A disjunction is the binary node of `.or`. -/
@[simp] theorem gate₂_or : gate₂ (σ := signature) .or rfl F G = F.or G :=
  rfl

/-- The disjunction of a list of De Morgan formulas, as a balanced tree (`Formula.balanced`); the
constant `false` for no formulas. -/
def orList (l : List (Formula signature n)) : Formula signature n :=
  balanced .or rfl (const false) l

/-- The conjunction of a list of De Morgan formulas, as a balanced tree (`Formula.balanced`); the
constant `true` for no formulas. -/
def andList (l : List (Formula signature n)) : Formula signature n :=
  balanced .and rfl (const true) l

/-- Evaluating `orList l` tests whether any formula in `l` evaluates to `true`. -/
@[simp] theorem eval_orList (l : List (Formula signature n)) :
    (orList l).eval interpretation x = l.any fun F => F.eval interpretation x := by
  rw [orList, eval_balanced]
  change l.balancedFold (· || ·) false _ = _
  rw [List.balancedFold_eq_foldr]
  induction l <;> simp_all

/-- Evaluating `andList l` tests whether every formula in `l` evaluates to `true`. -/
@[simp] theorem eval_andList (l : List (Formula signature n)) :
    (andList l).eval interpretation x = l.all fun F => F.eval interpretation x := by
  rw [andList, eval_balanced]
  change l.balancedFold (· && ·) true _ = _
  rw [List.balancedFold_eq_foldr]
  induction l <;> simp_all

/-- The disjunction of no formulas is the constant `false`. -/
@[simp] theorem orList_nil : orList ([] : List (Formula signature n)) = const false :=
  balanced_nil _

/-- The disjunction of one formula is that formula. -/
@[simp] theorem orList_singleton : orList [F] = F :=
  balanced_singleton _ F

/-- The conjunction of no formulas is the constant `true`. -/
@[simp] theorem andList_nil : andList ([] : List (Formula signature n)) = const true :=
  balanced_nil _

/-- The conjunction of one formula is that formula. -/
@[simp] theorem andList_singleton : andList [F] = F :=
  balanced_singleton _ F

/-- A balanced disjunction of `k ≥ 1` formulas has `k - 1` operation nodes besides theirs. -/
theorem size_orList_add_one {l : List (Formula signature n)} (hl : l ≠ []) :
    (orList l).size + 1 = (l.map size).sum + l.length :=
  size_balanced_add_one _ hl

/-- A balanced conjunction of `k ≥ 1` formulas has `k - 1` operation nodes besides theirs. -/
theorem size_andList_add_one {l : List (Formula signature n)} (hl : l ≠ []) :
    (andList l).size + 1 = (l.map size).sum + l.length :=
  size_balanced_add_one _ hl

/-- A balanced disjunction is deeper than its disjuncts by `⌈log₂⌉` of their number times the
cost of a disjunction; the disjunction of no formulas is a constant. -/
theorem depthWith_orList_le {cost : Op → ℕ} {l : List (Formula signature n)} {d : ℕ}
    (hl : ∀ F ∈ l, F.depthWith cost ≤ d) (hnil : l = [] → cost (.const false) ≤ d) :
    (orList l).depthWith cost ≤ d + cost .or * Nat.clog 2 l.length :=
  depthWith_balanced_le _ hl fun h => (depthWith_const cost false).trans_le (hnil h)

/-- A balanced conjunction is deeper than its conjuncts by `⌈log₂⌉` of their number times the
cost of a conjunction; the conjunction of no formulas is a constant. -/
theorem depthWith_andList_le {cost : Op → ℕ} {l : List (Formula signature n)} {d : ℕ}
    (hl : ∀ F ∈ l, F.depthWith cost ≤ d) (hnil : l = [] → cost (.const true) ≤ d) :
    (andList l).depthWith cost ≤ d + cost .and * Nat.clog 2 l.length :=
  depthWith_balanced_le _ hl fun h => (depthWith_const cost true).trans_le (hnil h)

/-- With negations and constants free, a balanced disjunction is deeper than its disjuncts by
`⌈log₂⌉` of their number. -/
theorem depthWith_binaryCost_orList_le {l : List (Formula signature n)} {d : ℕ}
    (hl : ∀ F ∈ l, F.depthWith binaryCost ≤ d) :
    (orList l).depthWith binaryCost ≤ d + Nat.clog 2 l.length := by
  simpa using depthWith_orList_le hl fun _ => (binaryCost_const false).trans_le (Nat.zero_le d)

/-- With negations and constants free, a balanced conjunction is deeper than its conjuncts by
`⌈log₂⌉` of their number. -/
theorem depthWith_binaryCost_andList_le {l : List (Formula signature n)} {d : ℕ}
    (hl : ∀ F ∈ l, F.depthWith binaryCost ≤ d) :
    (andList l).depthWith binaryCost ≤ d + Nat.clog 2 l.length := by
  simpa using depthWith_andList_le hl fun _ => (binaryCost_const true).trans_le (Nat.zero_le d)

/-- The literal of bit `i` that is true at `z`. -/
def literal (z : BitString n) (i : Fin n) : Formula signature n :=
  if z i then input i else (input i).not

/-- Evaluating `literal z i` at `x` tests whether `x i` equals `z i`. -/
@[simp] theorem eval_literal (z : BitString n) (i : Fin n) :
    (literal z i).eval interpretation x = (x i == z i) := by
  unfold literal
  cases z i <;> cases hx : x i <;> simp [hx]

/-- A literal has binary-gate depth zero. -/
@[simp] theorem depthWith_literal (z : BitString n) (i : Fin n) :
    (literal z i).depthWith binaryCost = 0 := by
  unfold literal
  split <;> simp

/-- Every Boolean function has a De Morgan formula: its disjunctive normal form. -/
theorem exists_computes (f : BooleanFunction n) :
    ∃ F : Formula signature n, F.Computes interpretation f := by
  classical
  refine ⟨orList ((Finset.univ.filter fun z => f z = true).toList.map fun z =>
    andList ((List.finRange n).map (literal z))), fun x => ?_⟩
  rw [eval_orList, Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
    have : x = z := funext (by simpa [List.all_eq_true] using h)
    rwa [this]
  · intro hx
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [List.all_eq_true]⟩

end Formula

namespace Boolean

/-- The De Morgan basis has fan-in at most two. -/
theorem arity_le_two (op : Op) : signature.Arity op ≤ 2 := by
  cases op <;> simp

variable {n : ℕ} {f : BooleanFunction n}

/-- The least depth of a De Morgan formula computing `f`, with negations and constants free: the
least depth with costs `binaryCost` (`Formula.minDepthWith`), which is finite because every
function has a formula (`Formula.exists_computes`). -/
noncomputable def formulaDepth (f : BooleanFunction n) : ℕ :=
  (Formula.minDepthWith interpretation binaryCost f).toNat

/-- The formula depth is the least depth with costs `binaryCost`. -/
@[simp]
theorem natCast_formulaDepth (f : BooleanFunction n) :
    (formulaDepth f : ℕ∞) = Formula.minDepthWith interpretation binaryCost f :=
  ENat.natCast_toNat (Formula.minDepthWith_ne_top_iff.2 (Formula.exists_computes f))

/-- The formula depth is at most the depth of every formula computing the function. -/
theorem formulaDepth_le {F : Formula signature n} (hF : F.Computes interpretation f) :
    formulaDepth f ≤ F.depthWith binaryCost := by
  exact_mod_cast (natCast_formulaDepth f).trans_le (Formula.minDepthWith_le hF)

/-- Some formula attains the formula depth. -/
theorem exists_computes_depthWith_eq_formulaDepth (f : BooleanFunction n) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧
      F.depthWith binaryCost = formulaDepth f := by
  obtain ⟨F, hF, hd⟩ := Formula.exists_depthWith_eq_minDepthWith (cost := binaryCost)
    (Formula.exists_computes f)
  exact ⟨F, hF, by exact_mod_cast hd.trans (natCast_formulaDepth f).symm⟩

end Boolean

end Cslib.Circuits
