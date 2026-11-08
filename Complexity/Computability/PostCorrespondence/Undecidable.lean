/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PostCorrespondence.Modified
public import Complexity.Computability.PostCorrespondence.OfTM0
public import Complexity.Computability.PostCorrespondence.Substitution
public import Mathlib.Computability.Halting
public import Mathlib.Computability.TuringMachine.Config
public import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Undecidability of Post's correspondence problem

**Post's correspondence problem is undecidable** [Post1946]; [Sipser2013, Theorem 5.15]: no
computable predicate decides whether a list of dominoes over `Bool`, or over any alphabet with two
distinct letters, has a match (`not_computablePred_solvable_bool`, `not_computablePred_solvable`).
The modified problem MPCP is undecidable too (`not_computablePred_mSolvable_bool`,
`not_computablePred_mSolvable`).

The reduction is from the halting problem for Mathlib's partial recursive codes,
`ComputablePred.halting_problem`. Fix a `ToPartrec` code `univ` that, on input `[n]`, evaluates
the `n`-th code at `0` (`Turing.ToPartrec.Code.exists_code`). Mathlib's compilers `PartrecToTM2`,
`TM2to1` and `TM1to0` turn `univ` into one fixed `TM0` machine `M₀`, supported on a finite set of
states; `M₀'` is its restriction to that set, so it has finitely many states and symbols. A code
`c` halts on `0` iff `M₀'` halts on the tape holding `encode c`, iff the MPCP instance
`OfTM0.mInstance M₀' (input (encode c))` is solvable. The binary code `boolCode` takes the instance
to `Bool`, and `toPCP` from MPCP to PCP; every step is primitive recursive.

**Scope.** Sipser reduces from the acceptance problem of Turing machines, building the instance
from the machine and its input. Here the machine is fixed: the instance is built from the input
of one universal `TM0` machine, which is how the reduction is computable for Mathlib's codes.

## Main definitions

* `Cslib.PostCorrespondence.Universal.M₀'`: the universal `TM0` machine with finitely many states.
* `Cslib.PostCorrespondence.Universal.mReduction`: the reduction from halting to MPCP over `Bool`.

## Main results

* `Cslib.PostCorrespondence.halting_manyOneReducible_mSolvable`,
  `Cslib.PostCorrespondence.halting_manyOneReducible_solvable`: the halting problem many-one
  reduces to MPCP and to PCP over `Bool`.
* `Cslib.PostCorrespondence.not_computablePred_solvable_bool`,
  `Cslib.PostCorrespondence.not_computablePred_solvable`: **PCP is undecidable**.
* `Cslib.PostCorrespondence.not_computablePred_mSolvable_bool`,
  `Cslib.PostCorrespondence.not_computablePred_mSolvable`: MPCP is undecidable.

## References

* [E. L. Post, *A variant of a recursively unsolvable problem*][Post1946]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.PostCorrespondence

open Relation Turing StateTransition

/-! ### The universal machine -/

namespace Universal

open ToPartrec PartrecToTM2

/-- The four stacks of `PartrecToTM2` form a finite type. -/
local instance : Fintype K' :=
  ⟨⟨{K'.main, K'.rev, K'.aux, K'.stack}, by decide⟩, fun k => by cases k <;> decide⟩

theorem exists_univ : ∃ u : Code, ∀ n : ℕ,
    (u.eval [n]).Dom ↔ ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom := by
  have hf : Partrec fun n : ℕ => (Denumerable.ofNat Nat.Partrec.Code n).eval 0 :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)
  obtain ⟨u, hu⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨u, fun n => ?_⟩
  have h : u.eval [n] = pure <$> (Denumerable.ofNat Nat.Partrec.Code n).eval 0 := hu ⟨[n], rfl⟩
  rw [h]
  rfl

/-- A `ToPartrec` code evaluating, on input `[n]`, the `n`-th partial recursive function at
`0`. -/
noncomputable def univ : Code := Classical.choose exists_univ

theorem univ_spec (n : ℕ) :
    (univ.eval [n]).Dom ↔ ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom :=
  Classical.choose_spec exists_univ n

/-- The labels of the `TM2` machine compiled from `univ`, with initial label the compiled
program. -/
@[expose] def UΛ : Type := Λ'

noncomputable instance : Inhabited UΛ := ⟨trNormal univ Cont'.halt⟩

/-- The `TM2` machine compiled from `univ`. -/
def M₂ : UΛ → TM2.Stmt (fun _ : K' => Γ') UΛ (Option Γ') := tr

/-- The `TM1` machine simulating `M₂`. -/
noncomputable def M₁ := TM2to1.tr M₂

/-- The `TM0` machine simulating `M₁`. -/
noncomputable def M₀ := TM1to0.tr M₁

theorem supports₂ : TM2.Supports M₂ (codeSupp univ Cont'.halt : Finset UΛ) :=
  tr_supports univ Cont'.halt

/-- The finite set of `TM1` labels used by `M₁`. -/
noncomputable def S₁ := TM2to1.trSupp M₂ (codeSupp univ Cont'.halt : Finset UΛ)

theorem supports₁ : TM1.Supports M₁ S₁ := TM2to1.tr_supports M₂ supports₂

/-- The finite set of `TM0` states used by `M₀`. -/
noncomputable def S₀ := TM1to0.trStmts M₁ S₁

theorem supports₀ : TM0.Supports M₀ (S₀ : Set (TM1to0.Λ' M₁)) := TM1to0.tr_supports M₁ supports₁

noncomputable instance : Inhabited (S₀ : Set (TM1to0.Λ' M₁)) := ⟨⟨default, supports₀.1⟩⟩

theorem closed₀ {q a q' s} (h : (q', s) ∈ M₀ q a) (hq : q ∈ (S₀ : Set (TM1to0.Λ' M₁))) :
    q' ∈ (S₀ : Set (TM1to0.Λ' M₁)) :=
  supports₀.2 h hq

/-- The restriction of `M₀` to its finitely many reachable states. -/
noncomputable def M₀' : TM0.Machine (TM2to1.Γ' K' fun _ => Γ') (S₀ : Set (TM1to0.Λ' M₁)) :=
  OfTM0.restrict M₀ closed₀

theorem tm2_init_eq (v : List ℕ) :
    (TM2.init K'.main (trList v) : TM2.Cfg (fun _ : K' => Γ') UΛ (Option Γ')) = init univ v := by
  simp only [TM2.init, init]
  congr 1
  funext k
  cases k <;> rfl

theorem dom_M₂ (n : ℕ) :
    (TM2.eval M₂ K'.main (trList [n])).Dom ↔ (univ.eval [n]).Dom := by
  rw [TM2.eval, Part.map_Dom, tm2_init_eq]
  have := tr_eval univ [n]
  change StateTransition.eval (TM2.step M₂) _ = _ at this
  rw [this]
  rfl

theorem dom_M₀' (n : ℕ) :
    (TM0.eval M₀' (TM2to1.trInit K'.main (trList [n]))).Dom ↔ (univ.eval [n]).Dom := by
  rw [M₀', OfTM0.eval_restrict_dom M₀ closed₀ rfl, M₀, TM1to0.tr_eval, M₁,
    TM2to1.tr_eval_dom, dom_M₂]

/-! ### Computability of the reduction -/

theorem trNat_eq (n : ℕ) :
    trNat n = if n = 0 then [] else (if n.bodd then Γ'.bit1 else Γ'.bit0) :: trNat n.div2 := by
  split_ifs with hn hb
  · rw [hn, trNat_zero]
  · have key : trNat n = trNum (Num.bit1 (Num.ofNat' n.div2)) := by
      conv_lhs => rw [← Nat.bit_bodd_div2 n, hb]
      rw [trNat, ← Num.ofNat'_eq, Num.ofNat'_bit]
      rfl
    rw [key, trNat, ← Num.ofNat'_eq]
    cases Num.ofNat' n.div2 <;> rfl
  · have hb' : n.bodd = false := by simpa using hb
    have hd : n.div2 ≠ 0 := by
      intro hd
      apply hn
      rw [← Nat.bit_bodd_div2 n, hb', hd]
      rfl
    have key : trNat n = trNum (Num.bit0 (Num.ofNat' n.div2)) := by
      conv_lhs => rw [← Nat.bit_bodd_div2 n, hb']
      rw [trNat, ← Num.ofNat'_eq, Num.ofNat'_bit]
      rfl
    rw [key, trNat, ← Num.ofNat'_eq]
    rcases h : Num.ofNat' n.div2 with _ | p
    · exact absurd (by rw [← Num.to_of_nat n.div2, ← Num.ofNat'_eq, h]; rfl) hd
    · rfl

/-! The finite alphabets and state set are primcodable through enumerations. -/

noncomputable local instance : Primcodable Γ' := Primcodable.ofEquiv _ (Fintype.equivFin Γ')

noncomputable local instance : Primcodable (TM2to1.Γ' K' fun _ : K' => Γ') :=
  letI := Classical.decEq (TM2to1.Γ' K' fun _ : K' => Γ')
  Primcodable.ofEquiv _ (Fintype.equivFin _)

noncomputable local instance : Primcodable (S₀ : Set (TM1to0.Λ' M₁)) :=
  letI := Classical.decEq (S₀ : Set (TM1to0.Λ' M₁))
  Primcodable.ofEquiv _ (Fintype.equivFin _)

theorem primrec_trNat : Primrec trNat := by
  have hdig : Primrec fun b : Bool => if b then Γ'.bit1 else Γ'.bit0 := Primrec.dom_finite _
  have hl : Primrec fun p : Unit × List (List Γ') => p.2 := Primrec.snd
  have hlen : Primrec fun p : Unit × List (List Γ') => p.2.length := Primrec.list_length.comp hl
  have hget : Primrec fun p : Unit × List (List Γ') => p.2[p.2.length.div2]? :=
    Primrec.list_getElem?.comp hl (Primrec.nat_div2.comp hlen)
  have hcons : Primrec₂ fun (p : Unit × List (List Γ')) (t : List Γ') =>
      (if p.2.length.bodd then Γ'.bit1 else Γ'.bit0) :: t :=
    Primrec.list_cons.comp₂ (hdig.comp (Primrec.nat_bodd.comp (hlen.comp Primrec.fst))).to₂
      Primrec₂.right
  have hg : Primrec₂ fun (_ : Unit) (l : List (List Γ')) =>
      some (((l[l.length.div2]?).map fun t =>
        (if l.length.bodd then Γ'.bit1 else Γ'.bit0) :: t).getD []) :=
    (Primrec.option_some.comp (Primrec.option_getD.comp (Primrec.option_map hget hcons)
      (Primrec.const ([] : List Γ')))).to₂
  have := Primrec.nat_strong_rec (fun (_ : Unit) n => trNat n) hg fun _ n => by
    change some ((((List.range n).map trNat)[(((List.range n).map trNat).length).div2]?).map
      (fun t => (if (((List.range n).map trNat).length).bodd then Γ'.bit1 else Γ'.bit0) :: t)
        |>.getD []) = some (trNat n)
    rw [List.length_map, List.length_range]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · have hlt : n.div2 < n := by rw [Nat.div2_val]; omega
      rw [List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.map_some,
        Option.getD_some, trNat_eq n, ite_eq_right (Nat.pos_iff_ne_zero.mp hn)]
  exact (this.comp (Primrec.const ()) Primrec.id).of_eq fun _ => rfl

theorem primrec_trInit :
    Primrec (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main) := by
  let G := TM2to1.Γ' K' fun _ : K' => Γ'
  let f : Γ' → G := fun a => (false, Function.update (fun _ => none) K'.main (some a))
  let g : G → G := fun x => (true, x.2)
  have hf : Primrec f := Primrec.dom_finite _
  have hL : Primrec fun L : List Γ' => L.reverse.map f :=
    Primrec.list_map Primrec.list_reverse (hf.comp Primrec.snd).to₂
  have hg : Primrec g := Primrec.dom_finite _
  exact (Primrec.list_cons.comp (hg.comp (Primrec.list_headI.comp hL))
    (Primrec.list_tail.comp hL)).of_eq fun _ => rfl

/-- The input tape of `M₀'` holding the number `n`. -/
noncomputable def input (n : ℕ) : List (TM2to1.Γ' K' fun _ : K' => Γ') :=
  TM2to1.trInit K'.main (trList [n])

theorem primrec_input : Primrec input := by
  have : Primrec fun n : ℕ => trList [n] :=
    (Primrec.list_append.comp primrec_trNat (Primrec.const [Γ'.cons])).of_eq fun _ => rfl
  exact (primrec_trInit.comp this).of_eq fun _ => rfl

/-- The many-one reduction from the halting problem to MPCP over `Bool`: simulate `univ` on the
code as an MPCP instance, then code the instance in binary. -/
noncomputable def mReduction (c : Nat.Partrec.Code) : MInstance Bool :=
  (OfTM0.mInstance M₀' (input (Encodable.encode c))).subst boolCode

theorem eval_dom_iff_solvable (c : Nat.Partrec.Code) :
    (c.eval 0).Dom ↔ (mReduction c).Solvable := by
  rw [mReduction, MInstance.solvable_subst_iff flatMap_boolCode_injective,
    ← OfTM0.eval_dom_iff_solvable, input, dom_M₀', univ_spec, Denumerable.ofNat_encode]

theorem primrec_mReduction : Primrec mReduction :=
  ((MInstance.primrec_subst primrec_boolCode).comp
    ((OfTM0.primrec_mInstance M₀').comp (primrec_input.comp Primrec.encode))).of_eq fun _ => rfl

end Universal

/-! ### Undecidability -/

/-- The halting problem reduces to MPCP over `Bool`. -/
theorem halting_manyOneReducible_mSolvable :
    (fun c : Nat.Partrec.Code => (c.eval 0).Dom) ≤₀ (MInstance.Solvable : MInstance Bool → Prop) :=
  ⟨Universal.mReduction, Universal.primrec_mReduction.to_comp, Universal.eval_dom_iff_solvable⟩

/-- **MPCP is undecidable** over the binary alphabet. -/
theorem not_computablePred_mSolvable_bool :
    ¬ComputablePred (MInstance.Solvable : MInstance Bool → Prop) := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_mSolvable h)

/-- **MPCP is undecidable** over every alphabet with two distinct letters. -/
theorem not_computablePred_mSolvable {α : Type*} [Primcodable α] {a b : α} (hab : a ≠ b) :
    ¬ComputablePred (MInstance.Solvable : MInstance α → Prop) := fun h =>
  not_computablePred_mSolvable_bool
    (ComputablePred.computable_of_manyOneReducible (mSolvable_bool_manyOneReducible hab) h)

/-- The halting problem reduces to PCP over `Bool`: through MPCP over `Bool`, Sipser's reduction
to PCP over `Marked Bool`, and the binary code. -/
theorem halting_manyOneReducible_solvable :
    (fun c : Nat.Partrec.Code => (c.eval 0).Dom) ≤₀ (Solvable : List (Domino Bool) → Prop) :=
  halting_manyOneReducible_mSolvable.trans
    (mSolvable_manyOneReducible.trans solvable_manyOneReducible_bool)

/-- **Post's correspondence problem is undecidable** over the binary alphabet
[Sipser2013, Theorem 5.15]. -/
theorem not_computablePred_solvable_bool :
    ¬ComputablePred (Solvable : List (Domino Bool) → Prop) := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_solvable h)

/-- **Post's correspondence problem is undecidable** over every alphabet with two distinct
letters. -/
theorem not_computablePred_solvable {α : Type*} [Primcodable α] {a b : α} (hab : a ≠ b) :
    ¬ComputablePred (Solvable : List (Domino α) → Prop) := fun h =>
  not_computablePred_solvable_bool
    (ComputablePred.computable_of_manyOneReducible (solvable_bool_manyOneReducible hab) h)

end Cslib.PostCorrespondence
