/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.CSP.ToBoolean
public import Complexity.Computability.Complexity.FineGrained.CountingCSP
import Complexity.Computability.Complexity.FineGrained.CountingScaleBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Fine-grained complexity of finite-domain `#CSP` and `k-CSP`

This module proves that the binary-encoding compilation `Cslib.Logic.PL.CSP.toBoolean` from
finite-domain CSPs over `Fin q` to Boolean CSPs runs in polynomial time on the native encoding
`encPair encUnary (encCSP encRel encNat)` (with compiled encoding length polynomially bounded in
the native input encoding length), and composes it with the subexponential bounded-arity Boolean
`#CSP` and `k-CSP` endpoints (`Cslib.Complexity.CSP`) to obtain native subexponential counting and
decision over any fixed finite domain size `q` and arity bound `k`:

1. **Polynomial-time compilation (`CSP.computableInPolyTime_toBoolean`,
   `CSP.computableInPolyTime_toBooleanDeclared`, `CSP.polyBounded_length_toBooleanDeclared`):**
   compiling `(N, F) : ℕ × CSP Rel ℕ` to `(N * CSP.bitWidth q, F.toBoolean q N)` is computable in
   polynomial time from `encPair encUnary (encCSP encRel encNat)` to
   `encPair encUnary (encCSP (encOption encRel) encNat)`.
2. **Native declared-variable counting (`CSP.exists_declaredCounter_finiteDomain_of_forall`,
   `CSP.exists_declaredCounter_finiteDomain`):** one machine on
   `encPair encUnary (encCSP encRel encNat)` computes the exact guarded declared-variable model
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
* `Cslib.Complexity.CSP.exists_declaredCounter_finiteDomain_of_forall`,
  `Cslib.Complexity.CSP.exists_declaredCounter_finiteDomain`: native declared-variable exact
  counting for finite-domain `#CSP`.
* `Cslib.Complexity.CSP.exists_modelCounter_finiteDomain_of_forall`,
  `Cslib.Complexity.CSP.exists_modelCounter_finiteDomain`: native occurring-variable exact counting
  for finite-domain `#CSP`.
* `Cslib.Complexity.CSP.decidableInSubexpTime_finiteDomainKCSP_of_forall`,
  `Cslib.Complexity.CSP.decidableInSubexpTime_finiteDomainKCSP`: subexponential-time decision for
  bounded-arity finite-domain `CSP`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2.
-/

@[expose] public section

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
CSP `x.2.toBoolean q x.1` is computable in polynomial time from the native encoding
`encPair encUnary (encCSP encRel encNat)`. -/
@[fun_prop]
theorem computableInPolyTime_toBoolean (encRel : Rel ↪ List Bool) (q : ℕ) :
    ComputableInPolyTime (fun x : ℕ × CSP Rel ℕ => x.2.toBoolean q x.1)
      (encPair encUnary (encCSP encRel encNat))
      (encCSP (encOption encRel) encNat) := by
  let b := CSP.bitWidth q
  let encIn := encPair encUnary (encCSP encRel encNat)
  let encOutElem := encConstraint (encOption encRel) encNat
  have hnone : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ =>
        (List.range x.1).map fun v => ((none : Option Rel), CSP.bitScope b v))
      encIn (encList encOutElem) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.unary_range' (ComputableInPolyTime.fst encUnary (encCSP encRel encNat)))
      ((ComputableInPolyTime.const (encOut := encOption encRel) none).prod
        ((computableInPolyTime_bitScope b).comp
          (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd encIn encUnary))))
  have hsome : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => x.2.map fun c => (some c.1, c.2.flatMap (CSP.bitScope b)))
      encIn (encList encOutElem) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.snd encUnary (encCSP encRel encNat))
      (((ComputableInPolyTime.optionSome encRel).comp
          ((ComputableInPolyTime.fst encRel (encList encNat)).comp
            (ComputableInPolyTime.snd encIn (encConstraint encRel encNat)))).prod
        (ComputableInPolyTime.flatMapWithInput
          ((ComputableInPolyTime.snd encRel (encList encNat)).comp
            (ComputableInPolyTime.snd encIn (encConstraint encRel encNat)))
          ((computableInPolyTime_bitScope b).comp
            (ComputableInPolyTime.snd (encPair encIn (encConstraint encRel encNat)) encNat))))
  exact ComputableInPolyTime.listAppend' hnone hsome

/-- Compiling a declared finite-domain CSP `(N, F)` into the declared Boolean CSP
`(N * CSP.bitWidth q, F.toBoolean q N)` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toBooleanDeclared (encRel : Rel ↪ List Bool) (q : ℕ) :
    ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => (x.1 * CSP.bitWidth q, x.2.toBoolean q x.1))
      (encPair encUnary (encCSP encRel encNat))
      (encPair encUnary (encCSP (encOption encRel) encNat)) :=
  (ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.fst encUnary (encCSP encRel encNat))
    (ComputableInPolyTime.const (CSP.bitWidth q))).prod
    (computableInPolyTime_toBoolean encRel q)

/-- The compiled Boolean CSP encoding length is polynomially bounded in the native finite-domain
input encoding length. -/
theorem polyBounded_length_toBooleanDeclared (encRel : Rel ↪ List Bool) (q : ℕ) :
    PolyBounded
      (fun x : ℕ × CSP Rel ℕ => (encPair encUnary (encCSP encRel encNat) x).length)
      (fun x : ℕ × CSP Rel ℕ =>
        (encPair encUnary (encCSP (encOption encRel) encNat)
          (x.1 * CSP.bitWidth q, x.2.toBoolean q x.1)).length) :=
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

private theorem computableInPolyTime_validDeclaredCSP_plain (encRel : Rel ↪ List Bool) (k : ℕ) :
    ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => validDeclaredCSP k x.1 x.2)
      (encPair encUnary (encCSP encRel encNat)) encBool := by
  let encIn := encPair encUnary (encCSP encRel encNat)
  have hN := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.fst encUnary (encCSP encRel encNat))
  have hlt : ComputableInPolyTime
      (fun p : (ℕ × CSP Rel ℕ) × ℕ => decide (p.2 < p.1.1))
      (encPair encIn encNat) encBool :=
    ComputableInPolyTime.binary_lt'
      (ComputableInPolyTime.snd encIn encNat)
      (hN.comp (ComputableInPolyTime.fst encIn encNat))
  have hvars : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => x.2.vars.all fun v => decide (v < x.1))
      encIn encBool :=
    ComputableInPolyTime.allWithInput
      ((computableInPolyTime_vars encRel encNat).comp
        (ComputableInPolyTime.snd encUnary (encCSP encRel encNat))) hlt
  have hwidth : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => x.2.all fun c => decide (c.2.length ≤ k))
      encIn encBool :=
    ComputableInPolyTime.allWithInput
      (ComputableInPolyTime.snd encUnary (encCSP encRel encNat))
      (ComputableInPolyTime.unary_le'
        ((ComputableInPolyTime.length_list encNat).comp
          ((ComputableInPolyTime.snd encRel (encList encNat)).comp
            (ComputableInPolyTime.snd encIn (encConstraint encRel encNat))))
        (ComputableInPolyTime.const k))
  unfold validDeclaredCSP
  exact ComputableInPolyTime.bool_and.comp (hwidth.prod hvars)

/-! ### Exact counting and decision endpoints -/

/-- **Declared-variable model counting transfer via Boolean compilation.**
For any fixed domain size `q`, arity bound `k`, and finite relation alphabet `Rel` with semantics
`sem : Rel → List (Fin q) → Bool`, evaluating the bounded-arity Boolean CSP counter on the
compiled Boolean instance `(x.1 * CSP.bitWidth q, x.2.toBoolean q x.1)` computes the exact
declared-variable model count `x.2.modelCountOn sem (Finset.range x.1)` for every valid
finite-domain instance `x` of constraint width at most `k`. -/
theorem exists_declaredCounter_toBoolean [Finite Rel]
    (encRel : Rel ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool) :
    let b := CSP.bitWidth q
    let enc := encPair encUnary (encCSP (encOption encRel) encNat)
    ∃ (count : ℕ × CSP (Option Rel) ℕ → ℕ) (T S : ℕ × CSP (Option Rel) ℕ → ℕ)
      (A c e a b_space : ℕ),
      ComputableInO count enc encNat T S ∧
      (∀ x : ℕ × CSP Rel ℕ,
        (∀ c ∈ x.2, c.2.length ≤ k) →
        (∀ v ∈ x.2.vars, v < x.1) →
        count (x.1 * b, x.2.toBoolean q x.1) =
          x.2.modelCountOn sem (Finset.range x.1)) ∧
      (∀ x : ℕ × CSP Rel ℕ,
        (T (x.1 * b, x.2.toBoolean q x.1) : ℝ) ≤
          c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (x.1 * b)) *
            (((enc (x.1 * b, x.2.toBoolean q x.1)).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x : ℕ × CSP Rel ℕ,
        S (x.1 * b, x.2.toBoolean q x.1) ≤
          a * ((enc (x.1 * b, x.2.toBoolean q x.1)).length + 1) ^ b_space) := by
  let b := CSP.bitWidth q
  let k' := max 1 k * b
  let sem' := CSP.semBoolean q sem
  let enc := encPair encUnary (encCSP (encOption encRel) encNat)
  obtain ⟨count, T, S, A, c, e, a, b_space, hcount, hspec, hT, hS⟩ :=
    CSP.exists_declaredCounter_of_finite (encOption encRel) k' sem'
  refine ⟨count, T, S, A, c, e, a, b_space, hcount, fun x hw hvars => ?_,
    fun x => hT (x.1 * b, x.2.toBoolean q x.1),
    fun x => hS (x.1 * b, x.2.toBoolean q x.1)⟩
  rw [hspec (x.1 * b, x.2.toBoolean q x.1)]
  dsimp only [Prod.fst, Prod.snd]
  have hvalid := CSP.validDeclaredCSP_toBoolean (q := q) hw hvars
  rw [hvalid]
  simp only [eq_self, ↓reduceIte]
  exact CSP.modelCountOn_toBoolean q x.1 sem x.2 hvars

/-- **Declared-variable exact counting for bounded-arity finite-domain `#CSP` (pattern-wise
hypothesis).** Whenever `fun R => sem R w` is computable in polynomial time for each domain tuple
`w : List (Fin q)` of length at most `max 1 k`, one native machine on
`encPair encUnary (encCSP encRel encNat)` computes the exact guarded declared-variable model count
`F.modelCountOn sem (Finset.range N)` on every input `x = (N, F) : ℕ × CSP Rel ℕ` in time
`O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial space in the native finite-domain
input length `|x|`. -/
theorem exists_declaredCounter_finiteDomain_of_forall (encRel : Rel ↪ List Bool)
    (q : ℕ) [Inhabited (Fin q)] (k : ℕ) (sem : Rel → List (Fin q) → Bool)
    (hsem : ∀ w : List (Fin q), w.length ≤ max 1 k →
      ComputableInPolyTime (fun R : Rel => sem R w) encRel encBool) :
    ∃ (count : ℕ × CSP Rel ℕ → ℕ) (T S : ℕ × CSP Rel ℕ → ℕ) (A c e a b_space : ℕ),
      ComputableInO count (encPair encUnary (encCSP encRel encNat)) encNat T S ∧
      (∀ x, count x = if validDeclaredCSP k x.1 x.2 then
        x.2.modelCountOn sem (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encRel encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encRel encNat) x).length + 1) ^ b_space) := by
  let b := CSP.bitWidth q
  let k' := max 1 k * b
  let sem' := CSP.semBoolean q sem
  let encB := encPair encUnary (encCSP (encOption encRel) encNat)
  let g (x : ℕ × CSP Rel ℕ) : ℕ × CNF ℕ :=
    (x.1 * b, (x.2.toBoolean q x.1).toCNFBounded k' sem')
  have htoCNF : ComputableInPolyTime
      (fun y : ℕ × CSP (Option Rel) ℕ => (y.1, y.2.toCNFBounded k' sem'))
      encB (encPair encUnary encCNF) :=
    (ComputableInPolyTime.fst encUnary (encCSP (encOption encRel) encNat)).prod
      ((computableInPolyTime_toCNFBounded_of_forall (encOption encRel) encNat k' sem'
          (computableInPolyTime_semBoolean_of_forall encRel q k sem hsem)).comp
        (ComputableInPolyTime.snd encUnary (encCSP (encOption encRel) encNat)))
  have hg : ComputableInPolyTime g
      (encPair encUnary (encCSP encRel encNat)) (encPair encUnary encCNF) :=
    htoCNF.comp (computableInPolyTime_toBooleanDeclared encRel q)
  have hvalid_imp (x : ℕ × CSP Rel ℕ) (hx : validDeclaredCSP k x.1 x.2 = true) :
      CNF.validDeclaredInput k' (g x).1 (g x).2 = true := by
    obtain ⟨hw, hsub⟩ := validDeclaredCSP_eq_true_iff.mp hx
    have hvars : ∀ v ∈ x.2.vars, v < x.1 := fun v hv =>
      Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv))
    exact validDeclaredInput_toCNFBounded sem' (CSP.validDeclaredCSP_toBoolean hw hvars)
  obtain ⟨count, T, S, A₀, c, e, a, b_space, hcount, hspec, hT₀, hS⟩ :=
    CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared k' hg
      (computableInPolyTime_validDeclaredCSP_plain encRel k) hvalid_imp
  refine ⟨count, T, S, A₀ * 8 ^ b, c, e, a, b_space, hcount, fun x => ?_, fun x => ?_, hS⟩
  · rw [hspec x]
    split_ifs with hx
    · obtain ⟨hw, hsub⟩ := validDeclaredCSP_eq_true_iff.mp hx
      have hvars : ∀ v ∈ x.2.vars, v < x.1 := fun v hv =>
        Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv))
      have hwB : ∀ c ∈ x.2.toBoolean q x.1, c.2.length ≤ k' := CSP.all_length_le_toBoolean hw
      simp only [g, toCNFBounded_eq_toCNF hwB, modelCountOn_toCNF]
      exact CSP.modelCountOn_toBoolean q x.1 sem x.2 hvars
    · rfl
  · refine (hT₀ x).trans ?_
    have hscale : interpolationScale (x.1 * b) ≤ (8 ^ b : ℕ) * interpolationScale x.1 := by
      rw [Nat.mul_comm]
      exact interpolationScale_mul_le b x.1
    have hexp : (A₀ : ℝ) * interpolationScale (x.1 * b) ≤
        ((A₀ * 8 ^ b : ℕ) : ℝ) * interpolationScale x.1 := by
      have hmul := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg A₀)
      push_cast at hmul ⊢
      linarith
    have hrpow : (2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale (x.1 * b)) ≤
        (2 : ℝ) ^ (((A₀ * 8 ^ b : ℕ) : ℝ) * interpolationScale x.1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hlen_nonneg :
        (0 : ℝ) ≤ (((encPair encUnary (encCSP encRel encNat) x).length : ℝ) + 1) ^ e := by
      positivity
    have h1 := mul_le_mul_of_nonneg_right hrpow hlen_nonneg
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
    linarith

/-- **Declared-variable exact counting for bounded-arity finite-domain `#CSP` over a finite relation
alphabet.** For any fixed domain size `q`, arity bound `k`, and finite relation alphabet `Rel`, one
native machine on `encPair encUnary (encCSP encRel encNat)` computes the exact guarded
declared-variable model count `F.modelCountOn sem (Finset.range N)` on every input `x = (N, F)` in
time `O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial space. -/
theorem exists_declaredCounter_finiteDomain [Finite Rel] (encRel : Rel ↪ List Bool)
    (q : ℕ) [Inhabited (Fin q)] (k : ℕ) (sem : Rel → List (Fin q) → Bool) :
    ∃ (count : ℕ × CSP Rel ℕ → ℕ) (T S : ℕ × CSP Rel ℕ → ℕ) (A c e a b_space : ℕ),
      ComputableInO count (encPair encUnary (encCSP encRel encNat)) encNat T S ∧
      (∀ x, count x = if validDeclaredCSP k x.1 x.2 then
        x.2.modelCountOn sem (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encRel encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encRel encNat) x).length + 1) ^ b_space) :=
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
  let b := CSP.bitWidth q
  let k' := max 1 k * b
  let sem' := CSP.semBoolean q sem
  let encB := encPair encUnary (encCSP (encOption encRel) encNat)
  let g (F : CSP Rel V) : ℕ × CNF ℕ :=
    (F.numVars * b, (F.denseRelabel.toBoolean q F.numVars).toCNFBounded k' sem')
  have hrel : ComputableInPolyTime (fun F : CSP Rel V => (F.numVars, F.denseRelabel))
      (encCSP encRel encV) (encPair encUnary (encCSP encRel encNat)) :=
    (computableInPolyTime_numVars encRel encV).prod (computableInPolyTime_denseRelabel encRel encV)
  have htoCNF : ComputableInPolyTime
      (fun y : ℕ × CSP (Option Rel) ℕ => (y.1, y.2.toCNFBounded k' sem'))
      encB (encPair encUnary encCNF) :=
    (ComputableInPolyTime.fst encUnary (encCSP (encOption encRel) encNat)).prod
      ((computableInPolyTime_toCNFBounded_of_forall (encOption encRel) encNat k' sem'
          (computableInPolyTime_semBoolean_of_forall encRel q k sem hsem)).comp
        (ComputableInPolyTime.snd encUnary (encCSP (encOption encRel) encNat)))
  have hg : ComputableInPolyTime g (encCSP encRel encV) (encPair encUnary encCNF) :=
    htoCNF.comp ((computableInPolyTime_toBooleanDeclared encRel q).comp hrel)
  let valid (F : CSP Rel V) : Bool := F.all fun c => decide (c.2.length ≤ k)
  have hvalid : ComputableInPolyTime valid (encCSP encRel encV) encBool :=
    ComputableInPolyTime.allWithInput
      (ComputableInPolyTime.id' (encIn := encCSP encRel encV))
      (ComputableInPolyTime.unary_le'
        ((ComputableInPolyTime.length_list encV).comp
          ((ComputableInPolyTime.snd encRel (encList encV)).comp
            (ComputableInPolyTime.snd (encCSP encRel encV) (encConstraint encRel encV))))
        (ComputableInPolyTime.const k))
  have hvalid_imp (F : CSP Rel V) (hF : valid F = true) :
      CNF.validDeclaredInput k' (g F).1 (g F).2 = true := by
    simp only [valid, List.all_eq_true, decide_eq_true_eq] at hF
    have hd : ∀ c ∈ F.denseRelabel, c.2.length ≤ k := (all_length_le_denseRelabel F).mpr hF
    have hvars : ∀ v ∈ F.denseRelabel.vars, v < F.numVars := fun v hv => by
      have hv' : v ∈ F.denseRelabel.vars.toFinset := List.mem_toFinset.mpr hv
      rw [vars_denseRelabel_toFinset] at hv'
      exact Finset.mem_range.mp hv'
    exact validDeclaredInput_toCNFBounded sem' (CSP.validDeclaredCSP_toBoolean hd hvars)
  obtain ⟨count, T, S, A₀, c, e, a, b_space, hcount, hspec, hT₀, hS⟩ :=
    CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared k' hg hvalid hvalid_imp
  refine ⟨count, T, S, A₀ * 8 ^ b, c, e, a, b_space, hcount, fun F hF => ?_, fun F => ?_, hS⟩
  · have hv : valid F = true := by
      simp only [valid, List.all_eq_true, decide_eq_true_eq]
      exact hF
    have hd : ∀ c ∈ F.denseRelabel, c.2.length ≤ k := (all_length_le_denseRelabel F).mpr hF
    have hvars : ∀ v ∈ F.denseRelabel.vars, v < F.numVars := fun v hv => by
      have hv' : v ∈ F.denseRelabel.vars.toFinset := List.mem_toFinset.mpr hv
      rw [vars_denseRelabel_toFinset] at hv'
      exact Finset.mem_range.mp hv'
    have hwB : ∀ c ∈ F.denseRelabel.toBoolean q F.numVars, c.2.length ≤ k' :=
      CSP.all_length_le_toBoolean hd
    simp only [hspec F, hv, ↓reduceIte, g, toCNFBounded_eq_toCNF hwB, modelCountOn_toCNF]
    exact (CSP.modelCountOn_toBoolean q F.numVars sem F.denseRelabel hvars).trans
      (modelCountOn_denseRelabel sem F)
  · refine (hT₀ F).trans ?_
    have hscale :
        interpolationScale (F.numVars * b) ≤ (8 ^ b : ℕ) * interpolationScale F.numVars := by
      rw [Nat.mul_comm]
      exact interpolationScale_mul_le b F.numVars
    have hexp : (A₀ : ℝ) * interpolationScale (F.numVars * b) ≤
        ((A₀ * 8 ^ b : ℕ) : ℝ) * interpolationScale F.numVars := by
      have hmul := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg A₀)
      push_cast at hmul ⊢
      linarith
    have hrpow : (2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale (F.numVars * b)) ≤
        (2 : ℝ) ^ (((A₀ * 8 ^ b : ℕ) : ℝ) * interpolationScale F.numVars) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hlen_nonneg : (0 : ℝ) ≤ (((encCSP encRel encV F).length : ℝ) + 1) ^ e := by positivity
    have h1 := mul_le_mul_of_nonneg_right hrpow hlen_nonneg
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
    linarith

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
  let f (F : CSP Rel V) : CSP (Option Rel) ℕ := F.denseRelabel.toBoolean q F.numVars
  have hf : ComputableInPolyTime f (encCSP encRel encV) (encCSP (encOption encRel) encNat) :=
    (computableInPolyTime_toBoolean encRel q).comp
      ((computableInPolyTime_numVars encRel encV).prod
        (computableInPolyTime_denseRelabel encRel encV))
  have hB : DecidableInSubexpTime {F : CSP Rel V | f F ∈ KCSP k' sem'}
      (encCSP encRel encV) CSP.numVars :=
    (decidableInSubexpTime_KCSP_of_forall (encOption encRel) encNat k' sem'
        (computableInPolyTime_semBoolean_of_forall encRel q k sem hsem)).of_reduction
      hf (fun _ => Iff.rfl) (c := b) fun F => by
        have hvars : ∀ v ∈ F.denseRelabel.vars, v < F.numVars := fun v hv => by
          have hv' : v ∈ F.denseRelabel.vars.toFinset := List.mem_toFinset.mpr hv
          rw [vars_denseRelabel_toFinset] at hv'
          exact Finset.mem_range.mp hv'
        have hle := CSP.numVars_toBoolean_le (q := q) hvars
        rw [Nat.mul_comm] at hle
        dsimp only [f, b] at hle ⊢
        omega
  have hwidth : ComputableInPolyTime
      (fun F : CSP Rel V => F.all fun c => decide (c.2.length ≤ k))
      (encCSP encRel encV) encBool :=
    ComputableInPolyTime.allWithInput
      (ComputableInPolyTime.id' (encIn := encCSP encRel encV))
      (ComputableInPolyTime.unary_le'
        ((ComputableInPolyTime.length_list encV).comp
          ((ComputableInPolyTime.snd encRel (encList encV)).comp
            (ComputableInPolyTime.snd (encCSP encRel encV) (encConstraint encRel encV))))
        (ComputableInPolyTime.const k))
  intro δ hδ
  have hKCSP_eq : KCSP k sem =
      {F : CSP Rel V | (F.all fun c => decide (c.2.length ≤ k)) = true} ∩
      {F : CSP Rel V | f F ∈ KCSP k' sem'} := by
    ext F
    simp only [KCSP, f, Set.mem_inter_iff, Set.mem_ofPred_eq, List.all_eq_true, decide_eq_true_eq]
    refine and_congr_right fun hF => ?_
    have hd : ∀ c ∈ F.denseRelabel, c.2.length ≤ k := (all_length_le_denseRelabel F).mpr hF
    have hvars : ∀ v ∈ F.denseRelabel.vars, v < F.numVars := fun v hv => by
      have hv' : v ∈ F.denseRelabel.vars.toFinset := List.mem_toFinset.mpr hv
      rw [vars_denseRelabel_toFinset] at hv'
      exact Finset.mem_range.mp hv'
    rw [CSP.satisfiable_toBoolean q F.numVars sem F.denseRelabel hvars,
      satisfiable_denseRelabel sem F]
    exact ⟨fun hsat => ⟨CSP.all_length_le_toBoolean hd, hsat⟩, And.right⟩
  rw [hKCSP_eq]
  exact (hB δ hδ).inter hwidth hδ.le

/-- **Subexponential-time decision for bounded-arity finite-domain `CSP` over a finite relation
alphabet.** -/
theorem decidableInSubexpTime_finiteDomainKCSP [Finite Rel] [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool) :
    DecidableInSubexpTime (KCSP k sem) (encCSP encRel encV) CSP.numVars :=
  decidableInSubexpTime_finiteDomainKCSP_of_forall encRel encV q k sem fun _ _ =>
    ComputableInPolyTime.of_finite _

end Cslib.Complexity.CSP
