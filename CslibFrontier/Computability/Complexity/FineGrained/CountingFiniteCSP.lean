/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.CSP.Declared
public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.CSP.ToBoolean
public import CslibFrontier.Computability.Complexity.FineGrained.CountingCSP
import CslibFrontier.Computability.Complexity.FineGrained.CountingScaleBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Fine-grained complexity of finite-domain `#CSP` and `k-CSP`

This module proves that the binary-encoding compilation `Cslib.Logic.PL.CSP.toBoolean` from
finite-domain CSPs over `Fin q` to Boolean CSPs runs in polynomial time on the native encoding
`encDeclaredCSP encRel` (with compiled encoding length polynomially bounded in
the native input encoding length), and composes it with the subexponential bounded-arity Boolean
`#CSP` and `k-CSP` endpoints (`Cslib.Complexity.CSP`) to obtain native subexponential counting and
decision over any fixed finite domain size `q` and arity bound `k`:

1. **Polynomial-time compilation (`CSP.computableInPolyTime_toBoolean`,
   `CSP.computableInPolyTime_toBooleanDeclared`, `CSP.polyBounded_length_toBooleanDeclared`):**
   compiling `(N, F) : DeclaredCSP Rel` to `(N * CSP.bitWidth q, F.toBoolean q N)` is computable in
   polynomial time from `encDeclaredCSP encRel` to
   `encDeclaredCSP (encOption encRel)`.
2. **Native declared-variable counting (`CSP.exists_declaredCounter_finiteDomain_of_forall`,
   `CSP.exists_declaredCounter_finiteDomain`):** one machine on
   `encDeclaredCSP encRel` computes the exact guarded declared-variable model
   count `F.modelCountOn sem (Finset.range N)` in time
   `O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial space in the native
   finite-domain input length `|x|`.
3. **Native occurring-variable counting (`CSP.exists_modelCounter_finiteDomain_of_forall`,
   `CSP.exists_modelCounter_finiteDomain`):** one machine on `encCSP encRel encV` computes
   `F.modelCount sem` for every instance `F : CSP Rel V` of constraint arity `≤ k` in time
   `O(2 ^ (A * interpolationScale F.numVars) * (|F| + 1) ^ e)` and polynomial space via dense
   variable relabeling.
4. **Subexponential decision (`CSP.decidableInSubexpTime_finiteDomainKCSP_of_forall`,
   `CSP.decidableInSubexpTime_finiteDomainKCSP`):** `CSP.KCSP k sem` over `Fin q` is decidable in
   subexponential time with respect to `CSP.numVars`.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_bitScope`,
  `Cslib.Complexity.CSP.computableInPolyTime_toBoolean`,
  `Cslib.Complexity.CSP.computableInPolyTime_toBooleanDeclared`,
  `Cslib.Complexity.CSP.polyBounded_length_toBooleanDeclared`: polynomial-time compilation and
  output-length bound for `CSP.toBoolean`.
* `Cslib.Complexity.CSP.exists_declaredCounter_toBoolean`: transfer lemma on the compiled Boolean
  encoding.
* `Cslib.Complexity.CSP.exists_counter_of_polyTime_toFiniteDeclaredCSP`,
  `Cslib.Complexity.CSP.exists_declaredCounter_finiteDomain_of_forall`,
  `Cslib.Complexity.CSP.exists_declaredCounter_finiteDomain`: native declared-variable exact
  counting and polynomial-time reduction interface for finite-domain `#CSP`.
* `Cslib.Complexity.CSP.exists_modelCounter_finiteDomain_of_forall`,
  `Cslib.Complexity.CSP.exists_modelCounter_finiteDomain`: native occurring-variable exact counting
  for finite-domain `#CSP`.
* `Cslib.Complexity.CSP.decidableInSubexpTime_finiteDomainKCSP_of_forall`,
  `Cslib.Complexity.CSP.decidableInSubexpTime_finiteDomainKCSP`: subexponential-time decision for
  bounded-arity finite-domain `CSP`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2.
-/

public section

namespace Cslib.Complexity.CSP

variable {Rel V : Type}

open Cslib.Logic.PL
open Cslib.Logic.PL.CSP
open Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal
open SubexponentialSAT

/-! ### Polynomial-time compilation to Boolean CSP -/

/-- Expanding a variable index `v` into its `b`-bit variable block `CSP.bitScope b v` is
computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_bitScope (b : ℕ) :
    ComputableInPolyTime (CSP.bitScope b) encNat (encList encNat) := by
  unfold CSP.bitScope
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.const (List.range b))
    (ComputableInPolyTime.binary_add.comp
      ((ComputableInPolyTime.binary_mul' (ComputableInPolyTime.fst encNat encNat)
          (ComputableInPolyTime.const b)).prod
        (ComputableInPolyTime.snd encNat encNat)))

/-- Compiling a finite-domain CSP on declared variables `0, …, N - 1` into its equivalent Boolean
CSP `x.formula.toBoolean q x.numVars` is computable in polynomial time from the native encoding
`encDeclaredCSP encRel`. -/
@[fun_prop]
theorem computableInPolyTime_toBoolean (encRel : Rel ↪ List Bool) (q : ℕ) :
    ComputableInPolyTime (fun x : DeclaredCSP Rel => x.formula.toBoolean q x.numVars)
      (encDeclaredCSP encRel)
      (encCSP (encOption encRel) encNat) := by
  let b := CSP.bitWidth q
  let encIn := encDeclaredCSP encRel
  let encOutElem := encConstraint (encOption encRel) encNat
  have hnone : ComputableInPolyTime
      (fun x : DeclaredCSP Rel =>
        (List.range x.numVars).map fun v => ((none : Option Rel), CSP.bitScope b v))
      encIn (encList encOutElem) := by fun_prop
  have hsome : ComputableInPolyTime
      (fun x : DeclaredCSP Rel => x.2.map fun c => (some c.1, c.2.flatMap (CSP.bitScope b)))
      encIn (encList encOutElem) := by fun_prop
  exact ComputableInPolyTime.listAppend' hnone hsome

/-- Compiling a declared finite-domain CSP `(N, F)` into the declared Boolean CSP
`(N * CSP.bitWidth q, F.toBoolean q N)` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toBooleanDeclared (encRel : Rel ↪ List Bool) (q : ℕ) :
    ComputableInPolyTime
      (fun x : DeclaredCSP Rel => { numVars := x.numVars * CSP.bitWidth q, formula := x.formula.toBoolean q x.numVars : DeclaredCSP (Option Rel) })
      (encDeclaredCSP encRel)
      (encDeclaredCSP (encOption encRel)) :=
  encDeclaredCSP_mk_polyTime
    (ComputableInPolyTime.unary_mul' (encDeclaredCSP_numVars_polyTime ComputableInPolyTime.id')
      (ComputableInPolyTime.const (CSP.bitWidth q)))
    (computableInPolyTime_toBoolean encRel q)

/-- The compiled Boolean CSP encoding length is polynomially bounded in the native finite-domain
input encoding length. -/
theorem polyBounded_length_toBooleanDeclared (encRel : Rel ↪ List Bool) (q : ℕ) :
    PolyBounded
      (fun x : DeclaredCSP Rel => (encDeclaredCSP encRel x).length)
      (fun x : DeclaredCSP Rel =>
        (encDeclaredCSP (encOption encRel)
          (x.numVars * CSP.bitWidth q, x.formula.toBoolean q x.numVars)).length) :=
  (computableInPolyTime_toBooleanDeclared encRel q).polyBounded_length

/-- Pattern-wise polynomial-time computability of the compiled Boolean semantics
`CSP.semBoolean q sem`. Whenever `fun R => sem R w` is computable in polynomial time for each
domain tuple `w : List (Fin q)` of length at most `max 1 k`, `fun oR => CSP.semBoolean q sem oR bw`
is computable in polynomial time for every bit pattern `bw` of length at most
`max 1 k * CSP.bitWidth q`. -/
theorem computableInPolyTime_semBoolean_of_forall (encRel : Rel ↪ List Bool) (q k : ℕ)
    (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ w : List (Fin q), w.length ≤ max 1 k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ∀ bw : List Bool, bw.length ≤ max 1 k * CSP.bitWidth q →
      ComputableInPolyTime (fun oR : Option Rel => CSP.semBoolean q sem oR bw)
        (encOption encRel) encBool := by
  intro bw hbw
  let b := CSP.bitWidth q
  have hb : 0 < b := CSP.one_le_bitWidth q
  have hsome : ComputableInPolyTime (fun R : Rel => CSP.semBoolean q sem (some R) bw)
      encRel encBool := by
    by_cases hq : 0 < q
    · let r := bw.length / b
      let vals := CSP.decodeChunks b r bw
      let ok : Bool := (bw.length % b == 0) && vals.all (decide <| · < q)
      by_cases hok : ok = true
      · have hw_len : (vals.map (CSP.toFin q hq)).length ≤ max 1 k := by
          rw [List.length_map, CSP.decodeChunks_length]
          exact (Nat.div_le_div_right hbw).trans (by rw [Nat.mul_div_cancel _ hb])
        refine (hsem (vals.map (CSP.toFin q hq)) hw_len).of_enc_eq fun R => ?_
        dsimp only [CSP.semBoolean]
        simp only [hq, ↓reduceDIte]
        change encBool ((ok && sem R (vals.map (CSP.toFin q hq)))) = _
        rw [hok, Bool.true_and]
      · refine (ComputableInPolyTime.const (encOut := encBool) false).of_enc_eq fun R => ?_
        dsimp only [CSP.semBoolean]
        simp only [hq, ↓reduceDIte]
        change encBool ((ok && sem R (vals.map (CSP.toFin q hq)))) = encBool false
        have hok_false : ok = false := Bool.eq_false_iff.mpr hok
        rw [hok_false, Bool.false_and]
    · refine (ComputableInPolyTime.const (encOut := encBool) false).of_enc_eq fun R => ?_
      dsimp only [CSP.semBoolean]
      simp only [hq, ↓reduceDIte]
  refine (ComputableInPolyTime.optionElimWithInput
    (body := fun _ R => CSP.semBoolean q sem (some R) bw)
    (ComputableInPolyTime.id' (encIn := encOption encRel))
    (ComputableInPolyTime.const (CSP.semBoolean q sem none bw))
    (hsome.comp (ComputableInPolyTime.snd (encOption encRel) encRel))).of_enc_eq fun oR => ?_
  cases oR <;> rfl

/-! ### Exact counting and decision endpoints -/

/-- **Declared-variable model counting transfer via Boolean compilation.**
For any fixed domain size `q`, arity bound `k`, and finite relation alphabet `Rel` with semantics
`sem : Rel → List (Fin q) → Bool`, evaluating the bounded-arity Boolean CSP counter on the
compiled Boolean instance `(x.numVars * CSP.bitWidth q, x.formula.toBoolean q x.numVars)` computes the exact
declared-variable model count `x.formula.modelCountOn sem (Finset.range x.numVars)` for every valid
finite-domain instance `x` of constraint width at most `k`. -/
theorem exists_declaredCounter_toBoolean [Finite Rel]
    (encRel : Rel ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool) :
    let b := CSP.bitWidth q
    let enc := encDeclaredCSP (encOption encRel)
    ∃ (count : DeclaredCSP (Option Rel) → ℕ) (T S : DeclaredCSP (Option Rel) → ℕ)
      (A c e a b_space : ℕ),
      ComputableInO count enc encNat T S ∧
      (∀ x : DeclaredCSP Rel,
        (∀ c ∈ x.2, c.2.length ≤ k) →
        (∀ v ∈ x.formula.vars, v < x.numVars) →
        count { numVars := x.numVars * b, formula := x.formula.toBoolean q x.numVars } =
          x.formula.modelCountOn sem (Finset.range x.numVars)) ∧
      (∀ x : DeclaredCSP Rel,
        (T { numVars := x.numVars * b, formula := x.formula.toBoolean q x.numVars } : ℝ) ≤
          c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (x.numVars * b)) *
            (((enc { numVars := x.numVars * b, formula := x.formula.toBoolean q x.numVars }).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x : DeclaredCSP Rel,
        S { numVars := x.numVars * b, formula := x.formula.toBoolean q x.numVars } ≤
          a * ((enc { numVars := x.numVars * b, formula := x.formula.toBoolean q x.numVars }).length + 1) ^ b_space) := by
  let b := CSP.bitWidth q
  let k' := max 1 k * b
  let sem' := CSP.semBoolean q sem
  let enc := encDeclaredCSP (encOption encRel)
  obtain ⟨count, T, S, A, c, e, a, b_space, hcount, hspec, hT, hS⟩ :=
    CSP.exists_declaredCounter_of_finite (encOption encRel) k' sem'
  refine ⟨count, T, S, A, c, e, a, b_space, hcount, fun x hw hvars => ?_,
    fun x => hT { numVars := x.numVars * b, formula := x.formula.toBoolean q x.numVars },
    fun x => hS { numVars := x.numVars * b, formula := x.formula.toBoolean q x.numVars }⟩
  rw [hspec { numVars := x.numVars * b, formula := x.formula.toBoolean q x.numVars }]
  dsimp only [Prod.fst, Prod.snd]
  have hvalid := CSP.validDeclaredCSP_toBoolean (q := q) hw hvars
  rw [hvalid]
  simp only [eq_self, ↓reduceIte]
  exact CSP.modelCountOn_toBoolean q x.numVars sem x.2 hvars

/-- **General polynomial-time reduction to declared-variable finite-domain `#CSP`:**
Composing any polynomial-time reduction `f : α → DeclaredCSP Rel` and polynomial-time validity guard
`valid : α → Bool` (implying `validDeclaredCSP k (f x).numVars (f x).formula = true`) with
`CSP.computableInPolyTime_toBooleanDeclared` and `CSP.exists_counter_of_polyTime_toDeclaredCSP`,
and rescaling `interpolationScale ((f x).numVars * bitWidth q)` via `interpolationScale_mul_le`, yields
an exact guarded model counter in time
`O(2 ^ (A * interpolationScale (f x).numVars) * (|x| + 1) ^ e)` and polynomial space. -/
theorem exists_counter_of_polyTime_toFiniteDeclaredCSP {α : Type} {encA : α ↪ List Bool}
    (encRel : Rel ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ w : List (Fin q), w.length ≤ max 1 k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool)
    {f : α → DeclaredCSP Rel}
    (hf : ComputableInPolyTime f encA (encDeclaredCSP encRel))
    {valid : α → Bool} (hvalid : ComputableInPolyTime valid encA encBool)
    (hvalid_imp : ∀ x, valid x = true → validDeclaredCSP k (f x).numVars (f x).formula = true) :
    ∃ (count : α → ℕ) (T S : α → ℕ) (A c e a b_space : ℕ),
      ComputableInO count encA encNat T S ∧
      (∀ x, count x = if valid x then
        (f x).formula.modelCountOn sem (Finset.range (f x).numVars) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (f x).numVars) *
        (((encA x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encA x).length + 1) ^ b_space) := by
  let b := CSP.bitWidth q
  let k' := max 1 k * b
  let sem' := CSP.semBoolean q sem
  have hg : ComputableInPolyTime
      (fun x : α => { numVars := (f x).numVars * b, formula := (f x).formula.toBoolean q (f x).numVars })
      encA (encDeclaredCSP (encOption encRel)) :=
    (computableInPolyTime_toBooleanDeclared encRel q).comp hf
  have hvalid_bool (x : α) (hx : valid x = true) :
      validDeclaredCSP k' ((f x).numVars * b) ((f x).formula.toBoolean q (f x).numVars) = true := by
    obtain ⟨hw, hsub⟩ := validDeclaredCSP_eq_true_iff.mp (hvalid_imp x hx)
    exact CSP.validDeclaredCSP_toBoolean hw fun v hv =>
      Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv))
  obtain ⟨count, T, S, A₀, c, e, a, b_space, hcount, hspec, hT₀, hS⟩ :=
    exists_counter_of_polyTime_toDeclaredCSP (encOption encRel) k' sem'
      (computableInPolyTime_semBoolean_of_forall encRel q k sem hsem) hg hvalid hvalid_bool
  refine ⟨count, T, S, A₀ * 8 ^ b, c, e, a, b_space, hcount, fun x => ?_, fun x => ?_, hS⟩
  · rw [hspec x]
    split_ifs with hx
    · obtain ⟨_, hsub⟩ := validDeclaredCSP_eq_true_iff.mp (hvalid_imp x hx)
      exact CSP.modelCountOn_toBoolean q (f x).numVars sem (f x).formula fun v hv =>
        Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv))
    · rfl
  · refine (hT₀ x).trans ?_
    have hscale : interpolationScale ((f x).numVars * b) ≤ (8 ^ b : ℕ) * interpolationScale (f x).numVars := by
      rw [Nat.mul_comm]
      exact interpolationScale_mul_le b (f x).numVars
    have hexp : (A₀ : ℝ) * interpolationScale ((f x).numVars * b) ≤
        ((A₀ * 8 ^ b : ℕ) : ℝ) * interpolationScale (f x).numVars := by
      have hmul := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg A₀)
      push_cast at hmul ⊢
      linarith
    have hrpow : (2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale ((f x).numVars * b)) ≤
        (2 : ℝ) ^ (((A₀ * 8 ^ b : ℕ) : ℝ) * interpolationScale (f x).numVars) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have h1 := mul_le_mul_of_nonneg_right hrpow
      (by positivity : (0 : ℝ) ≤ (((encA x).length : ℝ) + 1) ^ e)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
    linarith

/-- **Declared-variable exact counting for bounded-arity finite-domain `#CSP` (pattern-wise
hypothesis).** Whenever `fun R => sem R w` is computable in polynomial time for each domain tuple
`w : List (Fin q)` of length at most `max 1 k`, one native machine on
`encDeclaredCSP encRel` computes the exact guarded declared-variable model count
`F.modelCountOn sem (Finset.range N)` on every input `x = (N, F) : DeclaredCSP Rel` in time
`O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial space in the native finite-domain
input length `|x|`. -/
theorem exists_declaredCounter_finiteDomain_of_forall (encRel : Rel ↪ List Bool)
    (q : ℕ) [Inhabited (Fin q)] (k : ℕ) (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ w : List (Fin q), w.length ≤ max 1 k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ∃ (count : DeclaredCSP Rel → ℕ) (T S : DeclaredCSP Rel → ℕ) (A c e a b_space : ℕ),
      ComputableInO count (encDeclaredCSP encRel) encNat T S ∧
      (∀ x, count x = if validDeclaredCSP k x.1 x.2 then
        x.formula.modelCountOn sem (Finset.range x.numVars) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.numVars) *
        (((encDeclaredCSP encRel x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encDeclaredCSP encRel x).length + 1) ^ b_space) :=
  exists_counter_of_polyTime_toFiniteDeclaredCSP encRel q k sem hsem
    (ComputableInPolyTime.id' (encIn := encDeclaredCSP encRel))
    (computableInPolyTime_validDeclaredCSP encRel k) (fun _ hx => hx)

/-- **Declared-variable exact counting for bounded-arity finite-domain `#CSP` over a finite relation
alphabet.** For any fixed domain size `q`, arity bound `k`, and finite relation alphabet `Rel`, one
native machine on `encDeclaredCSP encRel` computes the exact guarded
declared-variable model count `F.modelCountOn sem (Finset.range N)` on every input `x = (N, F)` in
time `O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial space. -/
theorem exists_declaredCounter_finiteDomain [Finite Rel] (encRel : Rel ↪ List Bool)
    (q : ℕ) [Inhabited (Fin q)] (k : ℕ) (sem : Rel → List (Fin q) → Bool) :
    ∃ (count : DeclaredCSP Rel → ℕ) (T S : DeclaredCSP Rel → ℕ) (A c e a b_space : ℕ),
      ComputableInO count (encDeclaredCSP encRel) encNat T S ∧
      (∀ x, count x = if validDeclaredCSP k x.1 x.2 then
        x.formula.modelCountOn sem (Finset.range x.numVars) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.numVars) *
        (((encDeclaredCSP encRel x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encDeclaredCSP encRel x).length + 1) ^ b_space) :=
  exists_declaredCounter_finiteDomain_of_forall encRel q k sem fun _ _ =>
    ComputableInPolyTime.of_finite _

/-- **Occurring-variable exact counting for bounded-arity finite-domain `#CSP` (pattern-wise
hypothesis).** -/
theorem exists_modelCounter_finiteDomain_of_forall [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ w : List (Fin q), w.length ≤ max 1 k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ∃ (count : CSP Rel V → ℕ) (T S : CSP Rel V → ℕ) (A c e a b_space : ℕ),
      ComputableInO count (encCSP encRel encV) encNat T S ∧
      (∀ F : CSP Rel V, (∀ c ∈ F, c.2.length ≤ k) → count F = F.modelCount sem) ∧
      (∀ F : CSP Rel V, (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
        (((encCSP encRel encV F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP Rel V, S F ≤ a * ((encCSP encRel encV F).length + 1) ^ b_space) := by
  have hf : ComputableInPolyTime (fun F : CSP Rel V => { numVars := F.numVars, formula := F.denseRelabel : DeclaredCSP Rel })
      (encCSP encRel encV) (encDeclaredCSP encRel) := by
    exact encDeclaredCSP_mk_polyTime (by fun_prop) (by fun_prop)
  have hvalid : ComputableInPolyTime
      (fun F : CSP Rel V => F.all fun c => decide (c.2.length ≤ k))
      (encCSP encRel encV) encBool := by fun_prop
  obtain ⟨count, T, S, A, c, e, a, b_space, hcount, hspec, hT, hS⟩ :=
    exists_counter_of_polyTime_toFiniteDeclaredCSP encRel q k sem hsem hf hvalid fun F hF =>
      validDeclaredCSP_denseRelabel (by simpa only [List.all_eq_true, decide_eq_true_eq] using hF)
  refine ⟨count, T, S, A, c, e, a, b_space, hcount, fun F hF => ?_, hT, hS⟩
  have hv : (F.all fun c => decide (c.2.length ≤ k)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hF
  simp only [hspec F, hv, ↓reduceIte, modelCountOn_denseRelabel]

/-- **Occurring-variable exact counting for bounded-arity finite-domain `#CSP` over a finite
relation alphabet.** -/
theorem exists_modelCounter_finiteDomain [Finite Rel] [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool) :
    ∃ (count : CSP Rel V → ℕ) (T S : CSP Rel V → ℕ) (A c e a b_space : ℕ),
      ComputableInO count (encCSP encRel encV) encNat T S ∧
      (∀ F : CSP Rel V, (∀ c ∈ F, c.2.length ≤ k) → count F = F.modelCount sem) ∧
      (∀ F : CSP Rel V, (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
        (((encCSP encRel encV F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP Rel V, S F ≤ a * ((encCSP encRel encV F).length + 1) ^ b_space) :=
  exists_modelCounter_finiteDomain_of_forall encRel encV q k sem fun _ _ =>
    ComputableInPolyTime.of_finite _

private theorem satisfiable_denseRelabel [DecidableEq V] {q : ℕ} [Inhabited (Fin q)]
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) :
    F.denseRelabel.Satisfiable sem ↔ F.Satisfiable sem := by
  rw [← modelCount_pos_iff, modelCount_denseRelabel, modelCount_pos_iff]

/-- **Subexponential-time decision for bounded-arity finite-domain `CSP` (pattern-wise
hypothesis).** -/
theorem decidableInSubexpTime_finiteDomainKCSP_of_forall [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ w : List (Fin q), w.length ≤ max 1 k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    DecidableInSubexpTime (KCSP k sem) (encCSP encRel encV) CSP.numVars := by
  let b := CSP.bitWidth q
  let k' := max 1 k * b
  let sem' := CSP.semBoolean q sem
  let f (F : CSP Rel V) : CSP (Option Rel) ℕ := { numVars := F.numVars, formula := F.denseRelabel : DeclaredCSP Rel }.formula.toBoolean q { numVars := F.numVars, formula := F.denseRelabel : DeclaredCSP Rel }.numVars
  have hf : ComputableInPolyTime f (encCSP encRel encV) (encCSP (encOption encRel) encNat) := by
    fun_prop
  refine decidableInSubexpTime_KCSP_of_reduction encRel encV k sem hf
    (decidableInSubexpTime_KCSP_of_forall (encOption encRel) encNat k' sem'
      (computableInPolyTime_semBoolean_of_forall encRel q k sem hsem))
    (c := b) (fun F => ?_) (fun F hF => ?_)
  · simpa only [f, b, Nat.mul_comm] using
      CSP.numVars_toBoolean_le (q := q) (fun _ hv => mem_vars_denseRelabel_lt_numVars F hv)
  · dsimp only [f, sem', KCSP]
    rw [Set.mem_ofPred_eq,
      CSP.satisfiable_toBoolean q F.numVars sem F.denseRelabel
        (fun _ hv => mem_vars_denseRelabel_lt_numVars F hv),
      satisfiable_denseRelabel sem F]
    exact ⟨fun hsat => ⟨CSP.all_length_le_toBoolean ((all_length_le_denseRelabel F).mpr hF), hsat⟩,
      And.right⟩

/-- **Subexponential-time decision for bounded-arity finite-domain `CSP` over a finite relation
alphabet.** -/
theorem decidableInSubexpTime_finiteDomainKCSP [Finite Rel] [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool) :
    DecidableInSubexpTime (KCSP k sem) (encCSP encRel encV) CSP.numVars :=
  decidableInSubexpTime_finiteDomainKCSP_of_forall encRel encV q k sem fun _ _ =>
    ComputableInPolyTime.of_finite _

end Cslib.Complexity.CSP
