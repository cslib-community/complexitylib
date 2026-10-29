/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount
public import Complexity.Computability.Complexity.FineGrained.CountingEndpoint
public import Complexity.Logics.Propositional.CSP.ToCNF
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Exact subexponential counting and decision for bounded-arity Boolean `#CSP`

When the arity bound `k` is fixed and the relation semantics `sem : Rel → List Bool → Bool` is
computable in polynomial time on patterns of length at most `k` (in particular whenever
`fun p : Rel × List Bool => sem p.1 p.2` is computable in polynomial time or `Rel` is finite),
the width-guarded forbidden-pattern compiler `CSP.toCNFBounded k sem` runs in polynomial time.
Composing with `CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared` yields:
1. Exact declared-variable counting (`CSP.exists_declaredCounter`) in time
   `O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial space;
2. Exact occurring-variable counting (`CSP.exists_modelCounter`) in time
   `O(2 ^ (A * interpolationScale F.numVars) * (|F| + 1) ^ e)` and polynomial space via dense
   variable relabeling;
3. Subexponential-time decision (`CSP.decidableInSubexpTime_KCSP`) for `CSP.KCSP k sem` with respect
   to `CSP.numVars`.

### Source relation and library adaptations

* **Generalizing the forbidden-assignment encoding of Corollary C.2 (`7ef5c0cc`, p. 52):**
  In [OpenAI2026ETH] (Appendix C, p. 52), the proof of Corollary C.2 encodes each local output test
  $G_i(x_{S_i}) = b_i$ of arity $|S_i| \le d$ as at most $2^d$ width-$d$ clauses forbidding the
  assignments to $x_{S_i}$ on which $G_i$ disagrees with $b_i$, producing an equivalent $d$-CNF
  formula on the same $n$ variables with no auxiliary variables (so $|G^{-1}(\vec{b})|$ equals the
  model count of the compiled $d$-CNF formula). This module and `Cslib.Logic.PL.CSP.ToCNF` abstract
  and generalize that proof pattern to arbitrary polynomial-time computable (or finite) Boolean
  constraint languages of arity at most `k`.
* **Runtime scale:** As in `CountingNativeEndpoint`, the sublinear exponent $\rho(n)$ of
  Proposition 6.4 (pp. 43–44) is formalized as `interpolationScale`.

## Main definitions

* `Cslib.Complexity.encConstraint`, `Cslib.Complexity.encCSP`: standard binary encodings for
  constraints and CSP instances.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded`,
  `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded_of_forall`,
  `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded_of_finite`: polynomial-time compilation
  to `k`-CNF.
* `Cslib.Complexity.CSP.exists_declaredCounter`,
  `Cslib.Complexity.CSP.exists_declaredCounter_of_forall`,
  `Cslib.Complexity.CSP.exists_declaredCounter_of_finite`: exact subexponential declared-variable
  counting.
* `Cslib.Complexity.CSP.exists_modelCounter`,
  `Cslib.Complexity.CSP.exists_modelCounter_of_forall`,
  `Cslib.Complexity.CSP.exists_modelCounter_of_finite`: exact subexponential occurring-variable
  counting.
* `Cslib.Complexity.CSP.decidableInSubexpTime_KCSP`,
  `Cslib.Complexity.CSP.decidableInSubexpTime_KCSP_of_forall`,
  `Cslib.Complexity.CSP.decidableInSubexpTime_KCSP_of_finite`: subexponential-time decision for
  bounded-arity Boolean CSP.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 6.4 and Appendix C.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- Binary encoding of a constraint `(R, vs) : Constraint Rel V`. -/
abbrev encConstraint {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    Constraint Rel V ↪ List Bool :=
  encPair encRel (encList encV)

/-- Binary encoding of a CSP instance `F : CSP Rel V`. -/
abbrev encCSP {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    CSP Rel V ↪ List Bool :=
  encList (encConstraint encRel encV)

namespace CSP

variable {Rel V : Type}

open Cslib.Logic.PL.CSP ComputableInPolyTime

@[local fun_prop]
private theorem computableInPolyTime_zip {α β : Type}
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List β => p.1.zip p.2)
      (encPair (encList encA) (encList encB)) (encList (encPair encA encB)) := by
  rcases isEmpty_or_nonempty α with h | h
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.1 with
      | nil => rfl
      | cons a _ => exact isEmptyElim a
    rw [heq]
    exact const []
  rcases isEmpty_or_nonempty β with h' | h'
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.2 with
      | nil => simp
      | cons b _ => exact isEmptyElim b
    rw [heq]
    exact const []
  obtain ⟨a⟩ := h
  obtain ⟨b⟩ := h'
  have heq (p : List α × List β) : p.1.zip p.2 =
      (List.range (p.1.length - (p.1.length - p.2.length))).map
        (fun i => (p.1.getD i a, p.2.getD i b)) := by
    have hmin : p.1.length - (p.1.length - p.2.length) = min p.1.length p.2.length := by omega
    rw [hmin]
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have hleft : i < p.1.length := (Nat.lt_min.mp (by simpa only [List.length_zip] using hi)).1
    have hright : i < p.2.length := (Nat.lt_min.mp (by simpa only [List.length_zip] using hi)).2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hleft,
      List.getElem?_eq_getElem hright, Option.getD_some]
  simp_rw [heq]
  fun_prop

private theorem computableInPolyTime_mapFilterConst {α ι γ : Type} {encIn : α ↪ List Bool}
    {encC : γ ↪ List Bool} (items : List ι) {test : α → ι → Bool} {f : α → ι → γ}
    (htest : ∀ i ∈ items, ComputableInPolyTime (fun a => test a i) encIn encBool)
    (hf : ∀ i ∈ items, ComputableInPolyTime (fun a => f a i) encIn encC) :
    ComputableInPolyTime (fun a => (items.filter (test a)).map (f a)) encIn (encList encC) := by
  induction items with
  | nil => exact const []
  | cons item rest ih =>
    have hrest := ih (fun i hi => htest i (List.mem_cons_of_mem _ hi))
      (fun i hi => hf i (List.mem_cons_of_mem _ hi))
    have hhead := hf item List.mem_cons_self
    have hkeep := htest item List.mem_cons_self
    refine (hkeep.ite (cons' hhead hrest) hrest).of_enc_eq fun a => ?_
    simp only [List.filter_cons]
    cases test a item <;> simp

private theorem computableInPolyTime_forbidClause (encV : V ↪ List Bool) :
    ComputableInPolyTime
      (fun p : List V × List Bool => Constraint.forbidClause p.1 p.2)
      (encPair (encList encV) (encList encBool))
      (encList (encPair encV encBool)) := by
  unfold Constraint.forbidClause
  fun_prop

private theorem computableInPolyTime_toCNFAt (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (sem : Rel → List Bool → Bool) (r : ℕ)
    (hsem : ∀ w ∈ BitString.enumList r,
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ComputableInPolyTime
      (fun c : Constraint Rel V =>
        ((BitString.enumList r).filter fun w => !sem c.1 w).map (Constraint.forbidClause c.2))
      (encConstraint encRel encV)
      (encList (encList (encPair encV encBool))) := by
  refine computableInPolyTime_mapFilterConst (BitString.enumList r)
    (test := fun (c : Constraint Rel V) (w : List Bool) => !sem c.1 w)
    (f := fun (c : Constraint Rel V) (w : List Bool) => Constraint.forbidClause c.2 w)
    (fun w hw => ?_) (fun w _ => ?_)
  · have hsemw := hsem w hw
    fun_prop
  · exact (computableInPolyTime_forbidClause encV).comp
      ((snd encRel (encList encV)).prod (const w))

private theorem computableInPolyTime_constraintToCNFBounded
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ComputableInPolyTime (Constraint.toCNFBounded k sem)
      (encConstraint encRel encV)
      (encList (encList (encPair encV encBool))) := by
  induction k with
  | zero =>
    have htest : ComputableInPolyTime
        (fun c : Constraint Rel V => decide (c.2.length = 0))
        (encConstraint encRel encV) encBool := by
      fun_prop
    refine (htest.ite (computableInPolyTime_toCNFAt encRel encV sem 0
        fun w hw => hsem w (by simp [BitString.length_of_mem_enumList hw]))
      (const [])).of_enc_eq fun c => ?_
    simp only [Constraint.toCNFBounded, Constraint.toCNF, Nat.le_zero]
    by_cases h : c.2.length = 0 <;> simp [h]
  | succ k ih =>
    have htest : ComputableInPolyTime
        (fun c : Constraint Rel V => decide (c.2.length = k + 1))
        (encConstraint encRel encV) encBool := by
      fun_prop
    refine (htest.ite (computableInPolyTime_toCNFAt encRel encV sem (k + 1)
        fun w hw => hsem w (by simp [BitString.length_of_mem_enumList hw]))
      (ih fun w hw => hsem w (hw.trans (Nat.le_succ k)))).of_enc_eq fun c => ?_
    simp only [Constraint.toCNFBounded, Constraint.toCNF]
    by_cases h1 : c.2.length = k + 1
    · simp [h1]
    · have hle : (c.2.length ≤ k + 1) ↔ (c.2.length ≤ k) := by omega
      simp [h1, hle]

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time whenever `fun R => sem R w` is computable in polynomial time for each bit pattern
`w` of length at most `k`. -/
theorem computableInPolyTime_toCNFBounded_of_forall (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV)
      (encList (encList (encPair encV encBool))) := by
  have hc := computableInPolyTime_constraintToCNFBounded encRel encV k sem hsem
  exact flatMapWithInput (id' (encIn := encCSP encRel encV))
    (hc.comp (snd (encCSP encRel encV) (encConstraint encRel encV)))

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time whenever `sem` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toCNFBounded (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ComputableInPolyTime (fun p : Rel × List Bool => sem p.1 p.2)
      (encPair encRel encBits) encBool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV)
      (encList (encList (encPair encV encBool))) :=
  computableInPolyTime_toCNFBounded_of_forall encRel encV k sem fun w _ =>
    hsem.comp (id'.prod (const w))

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time for any finite relation alphabet `Rel`. -/
theorem computableInPolyTime_toCNFBounded_of_finite [Finite Rel] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV)
      (encList (encList (encPair encV encBool))) :=
  computableInPolyTime_toCNFBounded_of_forall encRel encV k sem fun _ _ => of_finite _

/-- Extracting the variable-occurrence list `CSP.vars` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_vars (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.vars (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList encV) := by
  unfold CSP.vars
  fun_prop

/-- Constructing the auxiliary positive-clause CNF `CSP.varCNF` is computable in polynomial
time. -/
@[fun_prop]
theorem computableInPolyTime_varCNF (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.varCNF (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList (encList (encPair encV encBool))) := by
  unfold CSP.varCNF
  fun_prop

/-- Listing the distinct occurring variables `CSP.distinctVars` in order of first occurrence is
computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_distinctVars [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.distinctVars (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList encV) := by
  have heq : (CSP.distinctVars (Rel := Rel) (V := V)) = fun F => F.varCNF.distinctVars := by
    funext F
    exact (distinctVars_varCNF F).symm
  rw [heq]
  exact (CNF.computableInPolyTime_distinctVars encV).comp
    (computableInPolyTime_varCNF encRel encV)

/-- Computing the number of distinct occurring variables `CSP.numVars` in unary is computable in
polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_numVars [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.numVars (Rel := Rel) (V := V))
      (encCSP encRel encV) encUnary := by
  have heq : (CSP.numVars (Rel := Rel) (V := V)) = fun F => F.varCNF.numVars := by
    funext F
    exact (numVars_varCNF F).symm
  rw [heq]
  exact (CNF.computableInPolyTime_numVars encV).comp
    (computableInPolyTime_varCNF encRel encV)

/-- Dense variable relabeling `CSP.denseRelabel` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_denseRelabel [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.denseRelabel (Rel := Rel) (V := V))
      (encCSP encRel encV) (encCSP encRel encNat) := by
  have hunary : ComputableInPolyTime (CSP.denseRelabel (Rel := Rel) (V := V))
      (encCSP encRel encV) (encCSP encRel encUnary) := by
    unfold CSP.denseRelabel CSP.relabel Constraint.relabel
    fun_prop
  have hbin : ComputableInPolyTime
      (CSP.relabel (Rel := Rel) (V := ℕ) (W := ℕ) (fun n => n))
      (encCSP encRel encUnary) (encCSP encRel encNat) := by
    unfold CSP.relabel Constraint.relabel
    fun_prop
  have heq : (CSP.denseRelabel (Rel := Rel) (V := V)) =
      fun F => (CSP.denseRelabel F).relabel (fun n => n) := by
    have hid : ∀ G : CSP Rel ℕ, G.relabel (fun n => n) = G := by
      intro G
      induction G with
      | nil => rfl
      | cons c G ih =>
        rcases c with ⟨r, vs⟩
        simp only [CSP.relabel, List.map_cons, Constraint.relabel, List.map_id']
        exact congrArg ((r, vs) :: ·) ih
    funext F
    exact (hid F.denseRelabel).symm
  rw [heq]
  exact hbin.comp hunary

private theorem computableInPolyTime_validDeclaredCSP (encRel : Rel ↪ List Bool) (k : ℕ) :
    ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => validDeclaredCSP k x.1 x.2)
      (encPair encUnary (encCSP encRel encNat)) encBool := by
  have hN := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.fst encUnary (encCSP encRel encNat))
  have hlt : ComputableInPolyTime
      (fun p : (ℕ × CSP Rel ℕ) × ℕ => decide (p.2 < p.1.1))
      (encPair (encPair encUnary (encCSP encRel encNat)) encNat) encBool :=
    ComputableInPolyTime.binary_lt.comp
      ((ComputableInPolyTime.snd _ _).prod (hN.comp (ComputableInPolyTime.fst _ _)))
  have hvars : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => x.2.vars.all fun v => decide (v < x.1))
      (encPair encUnary (encCSP encRel encNat)) encBool :=
    ComputableInPolyTime.allWithInput
      ((computableInPolyTime_vars encRel encNat).comp (ComputableInPolyTime.snd _ _)) hlt
  have hwidth : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => x.2.all fun c => decide (c.2.length ≤ k))
      (encPair encUnary (encCSP encRel encNat)) encBool := by
    fun_prop
  unfold validDeclaredCSP
  fun_prop

/-- **Declared-variable exact counting for bounded-arity Boolean `#CSP` (pattern-wise hypothesis).**
Whenever `fun R => sem R w` is polynomial-time computable for each pattern `w` of length `≤ k`, one
machine computes the exact guarded declared-variable model count
`F.modelCountOn sem (Finset.range N)` on every input `(N, F) : ℕ × CSP Rel ℕ` in time
`O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial space. -/
theorem exists_declaredCounter_of_forall (encRel : Rel ↪ List Bool) (k : ℕ)
    (sem : Rel → List Bool → Bool)
    (hsem : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ∃ (count : ℕ × CSP Rel ℕ → ℕ) (T S : ℕ × CSP Rel ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encPair encUnary (encCSP encRel encNat)) encNat T S ∧
      (∀ x, count x = if validDeclaredCSP k x.1 x.2 then
        x.2.modelCountOn sem (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encRel encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encRel encNat) x).length + 1) ^ b) := by
  let g (x : ℕ × CSP Rel ℕ) : ℕ × CNF ℕ := (x.1, x.2.toCNFBounded k sem)
  have hg : ComputableInPolyTime g
      (encPair encUnary (encCSP encRel encNat)) (encPair encUnary encCNF) := by
    have h1 := ComputableInPolyTime.fst encUnary (encCSP encRel encNat)
    have h2 := (computableInPolyTime_toCNFBounded_of_forall encRel encNat k sem hsem).comp
      (ComputableInPolyTime.snd encUnary (encCSP encRel encNat))
    exact h1.prod h2
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ :=
    CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared k hg
      (computableInPolyTime_validDeclaredCSP encRel k)
      (fun x hx => validDeclaredInput_toCNFBounded sem hx)
  refine ⟨count, T, S, A, c, e, a, b, hcount, fun x => ?_, hT, hS⟩
  rw [hspec x]
  split_ifs with hx
  · obtain ⟨hw, _⟩ := validDeclaredCSP_eq_true_iff.mp hx
    simp only [g, toCNFBounded_eq_toCNF hw, modelCountOn_toCNF]
  · rfl

/-- **Declared-variable exact counting for bounded-arity Boolean `#CSP`.** For any polynomial-time
computable relation semantics `sem` and arity bound `k`, one machine computes the exact guarded
declared-variable model count `F.modelCountOn sem (Finset.range N)` on every input
`(N, F) : ℕ × CSP Rel ℕ` in time `O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial
space. -/
theorem exists_declaredCounter (encRel : Rel ↪ List Bool) (k : ℕ)
    (sem : Rel → List Bool → Bool)
    (hsem : ComputableInPolyTime (fun p : Rel × List Bool => sem p.1 p.2)
      (encPair encRel encBits) encBool) :
    ∃ (count : ℕ × CSP Rel ℕ → ℕ) (T S : ℕ × CSP Rel ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encPair encUnary (encCSP encRel encNat)) encNat T S ∧
      (∀ x, count x = if validDeclaredCSP k x.1 x.2 then
        x.2.modelCountOn sem (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encRel encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encRel encNat) x).length + 1) ^ b) :=
  exists_declaredCounter_of_forall encRel k sem fun w _ =>
    hsem.comp (id'.prod (const w))

/-- **Declared-variable exact counting for bounded-arity Boolean `#CSP` over a finite relation
alphabet.** -/
theorem exists_declaredCounter_of_finite [Finite Rel] (encRel : Rel ↪ List Bool) (k : ℕ)
    (sem : Rel → List Bool → Bool) :
    ∃ (count : ℕ × CSP Rel ℕ → ℕ) (T S : ℕ × CSP Rel ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encPair encUnary (encCSP encRel encNat)) encNat T S ∧
      (∀ x, count x = if validDeclaredCSP k x.1 x.2 then
        x.2.modelCountOn sem (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encRel encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encRel encNat) x).length + 1) ^ b) :=
  exists_declaredCounter_of_forall encRel k sem fun _ _ => of_finite _

/-- **Occurring-variable exact counting for bounded-arity Boolean `#CSP` (pattern-wise
hypothesis).** -/
theorem exists_modelCounter_of_forall [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ∃ (count : CSP Rel V → ℕ) (T S : CSP Rel V → ℕ) (A c e a b : ℕ),
      ComputableInO count (encCSP encRel encV) encNat T S ∧
      (∀ F : CSP Rel V, (∀ c ∈ F, c.2.length ≤ k) → count F = F.modelCount sem) ∧
      (∀ F : CSP Rel V, (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
        (((encCSP encRel encV F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP Rel V, S F ≤ a * ((encCSP encRel encV F).length + 1) ^ b) := by
  let g (F : CSP Rel V) : ℕ × CNF ℕ :=
    (F.numVars, F.denseRelabel.toCNFBounded k sem)
  have hg : ComputableInPolyTime g (encCSP encRel encV) (encPair encUnary encCNF) :=
    (computableInPolyTime_numVars encRel encV).prod
      ((computableInPolyTime_toCNFBounded_of_forall encRel encNat k sem hsem).comp
        (computableInPolyTime_denseRelabel encRel encV))
  let valid (F : CSP Rel V) : Bool := F.all fun c => decide (c.2.length ≤ k)
  have hvalid : ComputableInPolyTime valid (encCSP encRel encV) encBool := by
    unfold valid
    fun_prop
  have hvalid_imp (F : CSP Rel V) (hF : valid F = true) :
      CNF.validDeclaredInput k (g F).1 (g F).2 = true := by
    apply validDeclaredInput_toCNFBounded sem
    rw [validDeclaredCSP_eq_true_iff]
    simp only [valid, List.all_eq_true, decide_eq_true_eq] at hF
    exact ⟨(all_length_le_denseRelabel F).mpr hF, by rw [vars_denseRelabel_toFinset]⟩
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ :=
    CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared k hg hvalid hvalid_imp
  refine ⟨count, T, S, A, c, e, a, b, hcount, fun F hF => ?_, hT, hS⟩
  have hv : valid F = true := by
    simp only [valid, List.all_eq_true, decide_eq_true_eq]
    exact hF
  have hd : ∀ c ∈ F.denseRelabel, c.2.length ≤ k := (all_length_le_denseRelabel F).mpr hF
  simp only [hspec F, hv, ite_true, g, toCNFBounded_eq_toCNF hd, modelCountOn_toCNF,
    modelCountOn_denseRelabel]

/-- **Occurring-variable exact counting for bounded-arity Boolean `#CSP`.** For any polynomial-time
computable relation semantics `sem`, variable encoding `encV`, and arity bound `k`, one machine
computes `F.modelCount sem` on every instance `F : CSP Rel V` of constraint arity `≤ k` in time
`O(2 ^ (A * interpolationScale F.numVars) * (|F| + 1) ^ e)` and polynomial space. -/
theorem exists_modelCounter [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ComputableInPolyTime (fun p : Rel × List Bool => sem p.1 p.2)
      (encPair encRel encBits) encBool) :
    ∃ (count : CSP Rel V → ℕ) (T S : CSP Rel V → ℕ) (A c e a b : ℕ),
      ComputableInO count (encCSP encRel encV) encNat T S ∧
      (∀ F : CSP Rel V, (∀ c ∈ F, c.2.length ≤ k) → count F = F.modelCount sem) ∧
      (∀ F : CSP Rel V, (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
        (((encCSP encRel encV F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP Rel V, S F ≤ a * ((encCSP encRel encV F).length + 1) ^ b) :=
  exists_modelCounter_of_forall encRel encV k sem fun w _ =>
    hsem.comp (id'.prod (const w))

/-- **Occurring-variable exact counting for bounded-arity Boolean `#CSP` over a finite relation
alphabet.** -/
theorem exists_modelCounter_of_finite [Finite Rel] [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    ∃ (count : CSP Rel V → ℕ) (T S : CSP Rel V → ℕ) (A c e a b : ℕ),
      ComputableInO count (encCSP encRel encV) encNat T S ∧
      (∀ F : CSP Rel V, (∀ c ∈ F, c.2.length ≤ k) → count F = F.modelCount sem) ∧
      (∀ F : CSP Rel V, (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
        (((encCSP encRel encV F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP Rel V, S F ≤ a * ((encCSP encRel encV F).length + 1) ^ b) :=
  exists_modelCounter_of_forall encRel encV k sem fun _ _ => of_finite _

/-- **Subexponential-time decision for bounded-arity Boolean `CSP` (pattern-wise hypothesis).** -/
theorem decidableInSubexpTime_KCSP_of_forall [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    DecidableInSubexpTime (KCSP k sem) (encCSP encRel encV) CSP.numVars := by
  let f (F : CSP Rel V) : CNF ℕ := (F.toCNFBounded k sem).denseRelabel
  have hf : ComputableInPolyTime f (encCSP encRel encV) encCNF :=
    (CNF.computableInPolyTime_denseRelabel encV).comp
      (computableInPolyTime_toCNFBounded_of_forall encRel encV k sem hsem)
  have hB : DecidableInSubexpTime {F : CSP Rel V | f F ∈ KSAT k}
      (encCSP encRel encV) CSP.numVars :=
    (CountingNativeEndpoint.decidableInSubexpTime_KSAT k).of_reduction hf (fun _ => Iff.rfl)
      (c := 1) fun F => by
        have hsub : (F.toCNFBounded k sem).vars.toFinset ⊆ F.vars.toFinset := by
          intro v hv
          exact List.mem_toFinset.mpr (mem_vars_toCNFBounded (List.mem_toFinset.mp hv))
        have hle : (F.toCNFBounded k sem).numVars ≤ F.numVars := Finset.card_le_card hsub
        simp only [f, CNF.numVars_denseRelabel]
        omega
  have hwidth : ComputableInPolyTime
      (fun F : CSP Rel V => F.all fun c => decide (c.2.length ≤ k))
      (encCSP encRel encV) encBool := by
    fun_prop
  intro δ hδ
  have hKCSP_eq : KCSP k sem =
      {F : CSP Rel V | (F.all fun c => decide (c.2.length ≤ k)) = true} ∩
      {F : CSP Rel V | f F ∈ KSAT k} := by
    ext F
    simp only [KCSP, f, KSAT, Set.mem_inter_iff, Set.mem_ofPred_eq,
      CNF.all_length_le_denseRelabel, CNF.satisfiable_denseRelabel,
      List.all_eq_true, decide_eq_true_eq]
    refine and_congr_right fun hF => ?_
    rw [toCNFBounded_eq_toCNF hF, satisfiable_toCNF]
    exact ⟨fun hsat => ⟨fun cl hcl => length_clause_mem_toCNF hF hcl, hsat⟩, And.right⟩
  rw [hKCSP_eq]
  exact (hB δ hδ).inter hwidth hδ.le

/-- **Subexponential-time decision for bounded-arity Boolean `CSP`.** For any polynomial-time
computable relation semantics `sem`, variable encoding `encV`, and arity bound `k`,
`CSP.KCSP k sem` is decidable in subexponential time in the number of occurring variables
`CSP.numVars`. -/
theorem decidableInSubexpTime_KCSP [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool)
    (hsem : ComputableInPolyTime (fun p : Rel × List Bool => sem p.1 p.2)
      (encPair encRel encBits) encBool) :
    DecidableInSubexpTime (KCSP k sem) (encCSP encRel encV) CSP.numVars :=
  decidableInSubexpTime_KCSP_of_forall encRel encV k sem fun w _ =>
    hsem.comp (id'.prod (const w))

/-- **Subexponential-time decision for bounded-arity Boolean `CSP` over a finite relation
alphabet.** -/
theorem decidableInSubexpTime_KCSP_of_finite [Finite Rel] [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    DecidableInSubexpTime (KCSP k sem) (encCSP encRel encV) CSP.numVars :=
  decidableInSubexpTime_KCSP_of_forall encRel encV k sem fun _ _ => of_finite _

end CSP

end Cslib.Complexity
