/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Computability.Complexity.Problems.USAT
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Binary
public import Complexity.Foundations.Data.BitString.WordCount
public import Complexity.Languages.Probabilistic.Iteration
public import Complexity.Probability.BitString.AffineHash
public import Complexity.Probability.UniformNat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Complexity.Foundations.Data.Finset.Sampling
import Complexity.Foundations.Data.List.Lookup
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Probability.PairwiseIndependentHash.Shift
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.List.GetD

/-!
# The Valiant–Vazirani randomized isolation reduction

`ValiantVazirani.reduce (φ, r)` adds to `φ` some number `k` of random parity equations
`A x + b = 0` over the `n = φ.vars.length` occurrences `x` of its variables [Valiant and Vazirani]
[ValiantVazirani1986], [Arora and Barak, Section 17.4][AroraBarak09]. The number `k` is
read in binary from the first `hashBits φ` bits of `r`, so that every `k ≤ n + 2` has probability
`2 ^ (-hashBits φ) ≥ 1 / (2 (n + 3))`; the rows of `A` and the offsets `b` are read from the
remaining bits, missing bits being `false`. Each equation is written in conjunctive normal form
with auxiliary variables carrying its prefix parities, with two or four clauses per term, so the
auxiliary variables are determined by the original ones. The variables are then renumbered by the
injective `Cslib.Complexity.splitVarToNat`.

## Main definitions

* `Cslib.Complexity.ValiantVazirani.hashCNF`: random parity equations in conjunctive normal form.
* `Cslib.Complexity.ValiantVazirani.reduce`: the Valiant–Vazirani reduction.
* `Cslib.Complexity.ValiantVazirani.randomBits`: the number of random bits it reads.

## Main results

* `Cslib.Complexity.ValiantVazirani.computableInPolyTime_reduce`: polynomial time.
* `Cslib.Complexity.ValiantVazirani.reduce_mem_UNSAT`: soundness.
* `Cslib.Complexity.ValiantVazirani.three_mul_two_pow_le_card_reduce_mem_USAT`,
  `Cslib.Complexity.ValiantVazirani.three_div_le_dens_reduce_mem_USAT`: success probability
  `Ω(1 / n)`.
* `Cslib.Complexity.ValiantVazirani.two_pow_le_two_mul_card_exists_row`: amplification by
  independent rows.

## References

* [L. G. Valiant, V. V. Vazirani, *NP is as easy as detecting unique
  solutions*][ValiantVazirani1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.ValiantVazirani

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Parity equations in conjunctive normal form -/

/-- The variables of the reduced formula before renumbering: `inl v` is a variable of the original
formula, and `inr (i, j)` carries the parity of the first `j` terms of the `i`-th equation. -/
abbrev Var := ℕ ⊕ (ℕ × ℕ)

/-- The encoding of the variables of the reduced formula: original variables in binary, auxiliary
indices in unary. -/
def encVar : Var ↪ List Bool := encSum encNat (encPair encUnary encUnary)

/-- Clauses forcing `next = prev ^^ (bit && x)`. -/
def stepClauses (bit : Bool) (next prev x : Var) : CNF Var :=
  if bit then
    [[(next, false), (prev, true), (x, true)], [(next, false), (prev, false), (x, false)],
      [(next, true), (prev, false), (x, true)], [(next, true), (prev, true), (x, false)]]
  else [[(next, false), (prev, true)], [(next, true), (prev, false)]]

/-- Clauses forcing the `i`-th parity equation: the auxiliary variables `inr (i, j)` start at
`offset`, the `j`-th one adds `row[j] && vars[j]`, and the last one is false. Together they force
`offset ^^ ⨁ j, (row[j] && vars[j]) = false`. -/
def rowClauses (vars : List ℕ) (i : ℕ) (row : List Bool) (offset : Bool) : CNF Var :=
  [(.inr (i, 0), offset)] :: [(.inr (i, vars.length), false)] ::
    vars.zipIdx.flatMap fun p =>
      stepClauses (row.getD p.2 false) (.inr (i, p.2 + 1)) (.inr (i, p.2)) (.inl p.1)

/-- The `k` parity equations read from the word `w`: the `i`-th equation has the `i`-th row of
`vars.length` bits of `w` as coefficients, and offset bit `k * vars.length + i` of `w`. Missing
bits are `false`. -/
def hashCNF (vars : List ℕ) (k : ℕ) (w : List Bool) : CNF Var :=
  (BitString.listRows k vars.length w).zipIdx.flatMap fun p =>
    rowClauses vars p.2 p.1 ((w.drop (k * vars.length)).getD p.2 false)

/-- The number of random bits selecting the number of equations. -/
def hashBits (φ : CNF ℕ) : ℕ := Nat.log 2 (φ.vars.length + 2) + 1

/-- `φ` together with `k` random parity equations read from `w`, renumbered into `ℕ`. -/
def reduceWith (φ : CNF ℕ) (k : ℕ) (w : List Bool) : CNF ℕ :=
  (φ.relabel Sum.inl ++ hashCNF φ.vars k w).relabel splitVarToNat

/-- **The Valiant–Vazirani reduction.** The first `hashBits φ` random bits, read in binary, give
the number `k` of parity equations; the remaining bits give their coefficients and offsets. -/
def reduce (x : CNF ℕ × List Bool) : CNF ℕ :=
  reduceWith x.1 (BitString.binaryValue (x.2.take (hashBits x.1))) (x.2.drop (hashBits x.1))

/-! ### Polynomial time -/

/-- Building the clauses of one step is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_stepClauses :
    ComputableInPolyTime (fun p : Bool × Var × Var × Var =>
      stepClauses p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encBool (encPair encVar (encPair encVar encVar)))
      (encList (encList (encPair encVar encBool))) := by
  unfold stepClauses encVar
  fun_prop

/-- Building the clauses of one equation is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_rowClauses :
    ComputableInPolyTime (fun p : List ℕ × ℕ × List Bool × Bool =>
      rowClauses p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encList encNat) (encPair encUnary (encPair encBits encBool)))
      (encList (encList (encPair encVar encBool))) := by
  unfold rowClauses encVar
  fun_prop

/-- Building all equations is polynomial-time, with the number of equations in unary. -/
@[fun_prop]
theorem computableInPolyTime_hashCNF :
    ComputableInPolyTime (fun p : List ℕ × ℕ × List Bool => hashCNF p.1 p.2.1 p.2.2)
      (encPair (encList encNat) (encPair encUnary encBits))
      (encList (encList (encPair encVar encBool))) := by
  unfold hashCNF
  fun_prop

/-- The selector ranges over the dyadic range of `φ.vars.length + 2`: the least power of two
above it. -/
private theorem two_pow_hashBits (φ : CNF ℕ) :
    2 ^ hashBits φ = Probability.dyadicSize (φ.vars.length + 2) :=
  rfl

/-- `2 ^ hashBits φ` is at most twice `φ.vars.length + 3`. -/
private theorem two_pow_hashBits_le (φ : CNF ℕ) : 2 ^ hashBits φ ≤ 2 * (φ.vars.length + 3) :=
  (two_pow_hashBits φ).trans_le (Probability.dyadicSize_le _)

/-- Every number of equations up to `φ.vars.length + 2` can be selected. -/
private theorem lt_two_pow_hashBits (φ : CNF ℕ) : φ.vars.length + 2 < 2 ^ hashBits φ :=
  (two_pow_hashBits φ).symm ▸ Probability.lt_dyadicSize _

private theorem binaryValue_take_hashBits (φ : CNF ℕ) (r : List Bool) :
    BitString.binaryValue (r.take (hashBits φ)) =
      BitString.boundedBinaryValue (2 * φ.vars.length + 5) (r.take (hashBits φ)) := by
  rw [BitString.boundedBinaryValue_eq, Nat.min_eq_right]
  have h1 := BitString.binaryValue_lt_two_pow (r.take (hashBits φ))
  have h2 : 2 ^ (r.take (hashBits φ)).length ≤ 2 ^ hashBits φ :=
    Nat.pow_le_pow_right (by norm_num) (by simp)
  have h3 := two_pow_hashBits_le φ
  omega

/-- **The Valiant–Vazirani reduction is polynomial-time**, on the framed encoding of the formula
followed by the raw random bits. -/
@[fun_prop]
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce (encPair encCNF encBits) encCNF := by
  have h : reduce = fun x : CNF ℕ × List Bool =>
      reduceWith x.1 (BitString.boundedBinaryValue (2 * x.1.vars.length + 5)
        (x.2.take (Nat.log 2 (x.1.vars.length + 2) + 1)))
        (x.2.drop (Nat.log 2 (x.1.vars.length + 2) + 1)) := by
    funext x
    rw [reduce, binaryValue_take_hashBits]
    rfl
  have hvars : ComputableInPolyTime (fun x : CNF ℕ × List Bool => x.1.vars)
      (encPair (encList (encList (encPair encNat encBool))) encBits) (encList encNat) :=
    (CNF.computableInPolyTime_vars encNat).comp (by fun_prop)
  have hinl : ComputableInPolyTime
      (fun x : CNF ℕ × List Bool => CNF.relabel (Sum.inl : ℕ → ℕ ⊕ ℕ × ℕ) x.1)
      (encPair (encList (encList (encPair encNat encBool))) encBits)
      (encList (encList (encPair (encSum encNat (encPair encUnary encUnary)) encBool))) :=
    (CNF.computableInPolyTime_relabel (by fun_prop)).comp (by fun_prop)
  have hsplit : ComputableInPolyTime (CNF.relabel splitVarToNat)
      (encList (encList (encPair (encSum encNat (encPair encUnary encUnary)) encBool)))
      (encList (encList (encPair encNat encBool))) :=
    CNF.computableInPolyTime_relabel computableInPolyTime_splitVarToNat
  rw [h]
  unfold reduceWith encCNF
  fun_prop

/-! ### Semantics of the parity equations -/

/-- The clauses of a step hold exactly when `next = prev ^^ (bit && x)`. -/
theorem eval_stepClauses (σ : Var → Bool) (bit : Bool) (next prev x : Var) :
    (stepClauses bit next prev x).eval σ = true ↔ σ next = (σ prev ^^ (bit && σ x)) := by
  cases bit <;> cases hn : σ next <;> cases hp : σ prev <;> cases hx : σ x <;>
    simp [stepClauses, CNF.eval, Clause.eval, Literal.eval, hn, hp, hx]

/-- The clauses of one equation hold exactly when the auxiliary variables start at the offset,
follow the steps, and end at `false`. -/
private theorem eval_rowClauses (σ : Var → Bool) (vars : List ℕ) (i : ℕ) (row : List Bool)
    (offset : Bool) :
    (rowClauses vars i row offset).eval σ = true ↔
      σ (.inr (i, 0)) = offset ∧ σ (.inr (i, vars.length)) = false ∧
        ∀ (j : ℕ) (hj : j < vars.length), σ (.inr (i, j + 1)) =
          (σ (.inr (i, j)) ^^ (row.getD j false && σ (.inl vars[j]))) := by
  simp only [rowClauses, CNF.eval_cons, Clause.eval_cons, Clause.eval_nil, Bool.or_false,
    Bool.and_eq_true, Literal.eval_eq_true_iff, CNF.eval_flatMap_eq_true_iff,
    eval_stepClauses, Prod.forall, List.mem_zipIdx_iff_getElem?]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h j hj => h _ _ (List.getElem?_eq_getElem hj),
    fun h v j hv => ?_⟩)
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hv
  exact h j hj

/-- The `i`-th row read by `hashCNF`, for `i < k`, is the `i`-th block of the padded word. -/
private theorem mem_zipIdx_listRows {k width : ℕ} {w row : List Bool} {i : ℕ} :
    (row, i) ∈ (BitString.listRows k width w).zipIdx ↔
      ∃ hi : i < k,
        row = List.ofFn (BitString.block (BitString.ofList (k * width) w) ⟨i, hi⟩) := by
  rw [List.mem_zipIdx_iff_getElem?, BitString.listRows_eq_ofFn, List.getElem?_ofFn]
  simp only
  split
  · rename_i hi
    exact ⟨fun h => ⟨hi, (Option.some.inj h).symm⟩, fun ⟨_, h⟩ => congrArg some h.symm⟩
  · rename_i hi
    exact ⟨fun h => (nomatch h), fun ⟨h, _⟩ => absurd h hi⟩

/-- The coefficient matrix read from `w` by `hashCNF`: `k` rows of `width` bits. Missing bits are
`false`. -/
def matrix (k width : ℕ) (w : List Bool) : Fin k → BitString width :=
  BitString.block (BitString.ofList (k * width) w)

/-- The offsets read from `w` by `hashCNF`, after the coefficient matrix. Missing bits are
`false`. -/
def offset (k width : ℕ) (w : List Bool) : BitString k :=
  BitString.ofList k (w.drop (k * width))

/-- The equations hold exactly when, for each `i < k`, the auxiliary variables of the `i`-th
equation start at its offset, follow its coefficients, and end at `false`. -/
private theorem eval_hashCNF (σ : Var → Bool) (vars : List ℕ) (k : ℕ) (w : List Bool) :
    (hashCNF vars k w).eval σ = true ↔ ∀ i : Fin k,
      σ (.inr (i, 0)) = offset k vars.length w i ∧ σ (.inr (i, vars.length)) = false ∧
        ∀ (j : ℕ) (hj : j < vars.length), σ (.inr (i, j + 1)) =
          (σ (.inr (i, j)) ^^ (matrix k vars.length w i ⟨j, hj⟩ && σ (.inl vars[j]))) := by
  have hrow (i : Fin k) {j : ℕ} (hj : j < vars.length) :
      (List.ofFn (BitString.block (BitString.ofList (k * vars.length) w) i)).getD j false =
        matrix k vars.length w i ⟨j, hj⟩ := by
    rw [List.getD_ofFn_of_lt _ hj]
    rfl
  have hoff (i : Fin k) : (w.drop (k * vars.length)).getD i false = offset k vars.length w i := rfl
  simp only [hashCNF, CNF.eval_flatMap_eq_true_iff, Prod.forall, mem_zipIdx_listRows,
    forall_exists_index, eval_rowClauses]
  constructor
  · intro h i
    obtain ⟨h0, hL, hs⟩ := h _ i i.2 rfl
    exact ⟨h0.trans (hoff i), hL, fun j hj => (hs j hj).trans (by rw [hrow i hj])⟩
  · rintro h row i hi rfl
    obtain ⟨h0, hL, hs⟩ := h ⟨i, hi⟩
    exact ⟨h0.trans (hoff ⟨i, hi⟩).symm, hL,
      fun j hj => (hs j hj).trans (by rw [hrow ⟨i, hi⟩ hj])⟩

/-- A sequence that starts at `c` and adds `f j` at each step `j < n` holds `c + ∑ j' < j, f j'`
up to step `n`. -/
theorem eq_add_sum_of_step {z f : ℕ → Bool} {c : Bool} {n : ℕ} (h0 : z 0 = c)
    (hstep : ∀ j < n, z (j + 1) = (z j ^^ f j)) :
    ∀ j ≤ n, z j = c + ∑ j' ∈ Finset.range j, f j' := by
  intro j hj
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [hstep j (by omega), ih (by omega), Finset.sum_range_succ, ← add_assoc]
    rfl

open BitString.LinearHash (affineHash isPairwiseIndependentHash_affineHash)

/-- The variables `vars` read off an assignment of the original variables. -/
def point (vars : List ℕ) (σ : ℕ → Bool) : BitString vars.length := fun j => σ vars[j]

/-- The value of the auxiliary variable `inr (i, j)` forced by an assignment `σ` of the original
variables: the offset plus the first `j` terms of the `i`-th equation. -/
def auxValue (vars : List ℕ) (k : ℕ) (w : List Bool) (σ : ℕ → Bool) (i : Fin k) (j : ℕ) :
    Bool :=
  offset k vars.length w i + ∑ j' ∈ Finset.range j,
    if h : j' < vars.length then matrix k vars.length w i ⟨j', h⟩ && σ vars[j'] else false

/-- After all terms, the auxiliary value is the `i`-th coordinate of the hash. -/
private theorem auxValue_length (vars : List ℕ) (k : ℕ) (w : List Bool) (σ : ℕ → Bool)
    (i : Fin k) :
    auxValue vars k w σ i vars.length =
      affineHash (matrix k vars.length w, offset k vars.length w) (point vars σ) i := by
  rw [auxValue, affineHash, Pi.add_apply, add_comm, ← Fin.sum_univ_eq_sum_range]
  simp only [Fin.is_lt, dite_true, Fin.eta]
  rfl

/-- In a satisfying assignment of the equations, the auxiliary variables hold the forced
values. -/
private theorem eq_auxValue_of_eval {σ : Var → Bool} {vars : List ℕ} {k : ℕ} {w : List Bool}
    (h : (hashCNF vars k w).eval σ = true) (i : Fin k) {j : ℕ} (hj : j ≤ vars.length) :
    σ (.inr (i, j)) = auxValue vars k w (σ ∘ .inl) i j := by
  obtain ⟨h0, -, hs⟩ := (eval_hashCNF σ vars k w).1 h i
  refine eq_add_sum_of_step (z := fun j => σ (.inr (i, j))) h0 (fun j hj => ?_) j hj
  simp only [hs j hj, hj, dite_true, Function.comp_apply]

/-- A satisfying assignment of the equations hashes its point to zero. -/
private theorem hash_point_eq_zero_of_eval {σ : Var → Bool} {vars : List ℕ} {k : ℕ} {w : List Bool}
    (h : (hashCNF vars k w).eval σ = true) :
    affineHash (matrix k vars.length w, offset k vars.length w) (point vars (σ ∘ .inl)) = 0 := by
  funext i
  rw [← auxValue_length, ← eq_auxValue_of_eval h i le_rfl]
  exact ((eval_hashCNF σ vars k w).1 h i).2.1

/-- An assignment of the original variables whose point hashes to zero extends, by the forced
auxiliary values, to a satisfying assignment of the equations. -/
private theorem eval_hashCNF_extend {vars : List ℕ} {k : ℕ} {w : List Bool} {σ : ℕ → Bool}
    (h : affineHash (matrix k vars.length w, offset k vars.length w) (point vars σ) = 0) :
    (hashCNF vars k w).eval (Sum.elim σ fun p =>
      if hp : p.1 < k then auxValue vars k w σ ⟨p.1, hp⟩ p.2 else false) = true := by
  refine (eval_hashCNF _ vars k w).2 fun i => ⟨?_, ?_, fun j hj => ?_⟩
  · simp [auxValue]
  · simp only [Sum.elim_inr, i.2, dite_true, Fin.eta]
    rw [auxValue_length, h]
    rfl
  · simp only [Sum.elim_inr, Sum.elim_inl, i.2, dite_true, Fin.eta, auxValue,
      Finset.sum_range_succ, hj]
    rw [← add_assoc]
    rfl

/-! ### Variables of the reduced formula -/

/-- The clauses of a step only mention its three variables. -/
private theorem mem_vars_stepClauses {bit : Bool} {next prev x u : Var}
    (h : u ∈ (stepClauses bit next prev x).vars) : u = next ∨ u = prev ∨ u = x := by
  cases bit <;> simp only [stepClauses, CNF.vars, Bool.false_eq_true, ite_false, ite_true,
    List.flatten_cons, List.flatten_nil, List.map_append, List.map_cons, List.map_nil,
    List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h <;> tauto

/-- Every variable of the `i`-th equation is an original variable among `vars`, or an auxiliary
variable `inr (i, j)` with `j ≤ vars.length`. -/
private theorem mem_vars_rowClauses {vars : List ℕ} {i : ℕ} {row : List Bool} {c : Bool} {u : Var}
    (h : u ∈ (rowClauses vars i row c).vars) :
    (∃ v ∈ vars, u = .inl v) ∨ ∃ j ≤ vars.length, u = .inr (i, j) := by
  simp only [rowClauses, CNF.mem_vars, List.mem_cons, List.mem_flatMap] at h
  obtain ⟨cl, hcl, b, hb⟩ := h
  rcases hcl with rfl | rfl | ⟨⟨v, j⟩, hp, hcl⟩
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb
    exact .inr ⟨0, Nat.zero_le _, hb.1⟩
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hb
    exact .inr ⟨_, le_rfl, hb.1⟩
  · obtain ⟨hj, hvj⟩ := List.mem_zipIdx' hp
    have hv : v ∈ vars := hvj ▸ List.getElem_mem hj
    rcases mem_vars_stepClauses (CNF.mem_vars.2 ⟨cl, hcl, b, hb⟩) with rfl | rfl | rfl
    · exact .inr ⟨j + 1, hj, rfl⟩
    · exact .inr ⟨j, hj.le, rfl⟩
    · exact .inl ⟨_, hv, rfl⟩

/-- Every variable of the equations is an original variable among `vars`, or an auxiliary
variable `inr (i, j)` with `i < k` and `j ≤ vars.length`. -/
private theorem mem_vars_hashCNF {vars : List ℕ} {k : ℕ} {w : List Bool} {u : Var}
    (h : u ∈ (hashCNF vars k w).vars) :
    (∃ v ∈ vars, u = .inl v) ∨ ∃ i < k, ∃ j ≤ vars.length, u = .inr (i, j) := by
  simp only [hashCNF, CNF.mem_vars, List.mem_flatMap] at h
  obtain ⟨cl, ⟨⟨row, i⟩, hp, hcl⟩, b, hb⟩ := h
  obtain ⟨hi, -⟩ := mem_zipIdx_listRows.1 hp
  rcases mem_vars_rowClauses (CNF.mem_vars.2 ⟨cl, hcl, b, hb⟩) with h | ⟨j, hj, rfl⟩
  · exact .inl h
  · exact .inr ⟨i, hi, j, hj, rfl⟩

/-! ### Soundness and isolation -/

/-- **Soundness.** A satisfying assignment of the reduced formula restricts to one of `φ`: the
equations only add constraints. -/
theorem satisfiable_of_satisfiable_reduceWith {φ : CNF ℕ} {k : ℕ} {w : List Bool}
    (h : (reduceWith φ k w).Satisfiable) : φ.Satisfiable := by
  obtain ⟨τ, hτ⟩ := h
  simp only [reduceWith, CNF.eval_relabel, CNF.eval_append, Bool.and_eq_true] at hτ
  exact ⟨_, hτ.1⟩

/-- **Soundness of the reduction**: if `φ` is unsatisfiable, then so is the reduced formula, for
every random word. -/
theorem reduce_mem_UNSAT {φ : CNF ℕ} (hφ : φ ∈ UNSAT) (r : List Bool) :
    reduce (φ, r) ∈ UNSAT :=
  fun h => hφ (satisfiable_of_satisfiable_reduceWith h)

open Classical in
/-- The satisfying assignments of `φ`, read off at the occurrences of its variables. -/
noncomputable def solutions (φ : CNF ℕ) : Finset (BitString φ.vars.length) :=
  Finset.univ.filter fun x => ∃ σ : ℕ → Bool, φ.eval σ = true ∧ point φ.vars σ = x

theorem mem_solutions {φ : CNF ℕ} {x : BitString φ.vars.length} :
    x ∈ solutions φ ↔ ∃ σ : ℕ → Bool, φ.eval σ = true ∧ point φ.vars σ = x := by
  simp [solutions]

/-- The forced auxiliary values only depend on the original variables among `vars`. -/
theorem auxValue_congr {vars : List ℕ} {k : ℕ} {w : List Bool} {σ τ : ℕ → Bool}
    (h : point vars σ = point vars τ) (i : Fin k) (j : ℕ) :
    auxValue vars k w σ i j = auxValue vars k w τ i j := by
  unfold auxValue
  congr 1
  refine Finset.sum_congr rfl fun j' _ => ?_
  split
  · rename_i hj'
    rw [show σ vars[j'] = τ vars[j'] from congrFun h ⟨j', hj'⟩]
  · rfl

open Classical in
/-- The equations with seed `p` isolate a solution of `φ`: exactly one solution hashes to
zero. -/
def Isolates (φ : CNF ℕ) {k : ℕ} (p : (Fin k → BitString φ.vars.length) × BitString k) :
    Prop :=
  ((solutions φ).filter fun x => affineHash p x = 0).card = 1

/-- **Isolation gives unique satisfiability.** If exactly one satisfying assignment of `φ` hashes
to zero under the equations read from `w`, then `φ` with these equations is uniquely
satisfiable: the auxiliary variables are determined by the original ones. -/
theorem reduceWith_mem_USAT {φ : CNF ℕ} {k : ℕ} {w : List Bool}
    (h : Isolates φ (matrix k φ.vars.length w, offset k φ.vars.length w)) :
    reduceWith φ k w ∈ USAT := by
  classical
  obtain ⟨x₀, hx₀⟩ := Finset.card_eq_one.1 h
  have hmem : x₀ ∈ (solutions φ).filter fun x =>
      affineHash (matrix k φ.vars.length w, offset k φ.vars.length w) x = 0 :=
    hx₀ ▸ Finset.mem_singleton_self x₀
  obtain ⟨hsol, hhash⟩ := Finset.mem_filter.1 hmem
  obtain ⟨σ, hσ, rfl⟩ := mem_solutions.1 hsol
  set σ' : Var → Bool := Sum.elim σ fun p =>
    if hp : p.1 < k then auxValue φ.vars k w σ ⟨p.1, hp⟩ p.2 else false with hσ'
  have hsat : (φ.relabel Sum.inl ++ hashCNF φ.vars k w).eval σ' = true := by
    simp only [CNF.eval_append, CNF.eval_relabel, Bool.and_eq_true]
    exact ⟨hσ, eval_hashCNF_extend hhash⟩
  refine ⟨Function.extend splitVarToNat σ' fun _ => false, ?_, fun τ hτ v hvψ => ?_⟩
  · rw [reduceWith, CNF.eval_relabel, Function.extend_comp splitVarToNat_injective]
    exact hsat
  rw [reduceWith, CNF.eval_relabel] at hτ
  simp only [CNF.eval_append, CNF.eval_relabel, Bool.and_eq_true] at hτ
  obtain ⟨hφ, hH⟩ := hτ
  -- the point of `τ` is a solution hashing to zero, hence it is the point of `σ`
  have hpoint : point φ.vars ((τ ∘ splitVarToNat) ∘ Sum.inl) = point φ.vars σ := by
    have : point φ.vars ((τ ∘ splitVarToNat) ∘ Sum.inl) ∈ (solutions φ).filter fun x =>
        affineHash (matrix k φ.vars.length w, offset k φ.vars.length w) x = 0 :=
      Finset.mem_filter.2 ⟨mem_solutions.2 ⟨_, hφ, rfl⟩, hash_point_eq_zero_of_eval hH⟩
    rw [hx₀] at this
    exact Finset.mem_singleton.1 this
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ((CNF.vars_relabel _ _) ▸ hvψ)
  rw [splitVarToNat_injective.extend_apply]
  change (τ ∘ splitVarToNat) u = σ' u
  rw [CNF.vars, List.flatten_append, List.map_append, List.mem_append] at hu
  rcases hu with hu | hu
  · rw [← CNF.vars, CNF.vars_relabel] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    exact congrFun hpoint ⟨j, hj⟩
  · rcases mem_vars_hashCNF hu with ⟨v, hv, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      exact congrFun hpoint ⟨j, hj⟩
    · rw [eq_auxValue_of_eval hH ⟨i, hi⟩ hj, auxValue_congr hpoint]
      simp [hσ', hi]

/-! ### The success probability -/

/-- The number of equations isolating a solution with probability at least `3 / 16`: with `s`
solutions, `2 ^ (log₂ s + 2)` lies between `2 s` and `4 s`. -/
private noncomputable def goodRows (φ : CNF ℕ) : ℕ := Nat.log 2 (solutions φ).card + 2

/-- A satisfiable formula has a solution. -/
theorem solutions_nonempty {φ : CNF ℕ} (hφ : φ.Satisfiable) : (solutions φ).Nonempty :=
  let ⟨σ, hσ⟩ := hφ
  ⟨_, mem_solutions.2 ⟨σ, hσ, rfl⟩⟩

/-- `2 ^ goodRows φ` is at most four times the number of solutions. -/
private theorem two_pow_goodRows_le {φ : CNF ℕ} (hφ : φ.Satisfiable) :
    2 ^ goodRows φ ≤ 4 * (solutions φ).card := by
  have := Nat.pow_log_le_self 2 (solutions_nonempty hφ).card_pos.ne'
  rw [goodRows, pow_add]
  omega

/-- `2 ^ goodRows φ` is at least twice the number of solutions. -/
private theorem two_mul_card_solutions_le (φ : CNF ℕ) : 2 *
    (solutions φ).card ≤ 2 ^ goodRows φ := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (solutions φ).card
  rw [goodRows, pow_add, pow_succ] at *
  omega

/-- At most `2 ^ φ.vars.length` solutions need at most `φ.vars.length + 2` equations. -/
private theorem goodRows_le (φ : CNF ℕ) : goodRows φ ≤ φ.vars.length + 2 := by
  have hcard : (solutions φ).card ≤ 2 ^ φ.vars.length :=
    (Finset.card_le_univ _).trans_eq (by simp)
  have := Nat.log_mono_right (b := 2) hcard
  rw [Nat.log_pow (by decide)] at this
  rw [goodRows]
  omega

/-- The selector bits can select `goodRows φ` equations. -/
private theorem goodRows_lt_two_pow_hashBits (φ : CNF ℕ) : goodRows φ < 2 ^ hashBits φ :=
  (goodRows_le φ).trans_lt (lt_two_pow_hashBits φ)

open Classical in
/-- **The Valiant–Vazirani lemma for the formula**: with `goodRows φ` random equations, exactly
one solution of a satisfiable `φ` satisfies them with probability at least `3 / 16`. -/
private theorem three_sixteenths_le_dens {φ : CNF ℕ} (hφ : φ.Satisfiable) :
    3 / 16 ≤ Finset.dens (Finset.univ.filter
      fun p : (Fin (goodRows φ) → BitString φ.vars.length) × BitString (goodRows φ) =>
        Isolates φ p) := by
  classical
  have hY : Fintype.card (BitString (goodRows φ)) = 2 ^ goodRows φ := by simp
  have hpi := isPairwiseIndependentHash_affineHash (goodRows φ) φ.vars.length
  convert hpi.three_sixteenths_le_dens_filter_card_filter_eq_one 0
    (hY ▸ two_pow_goodRows_le hφ) (hY ▸ two_mul_card_solutions_le φ) using 3
  exact Iff.rfl

open Classical in
/-- The density bound in integers: at least `3 / 16` of the `2 ^ (k * n + k)` seeds isolate a
solution. -/
private theorem three_mul_two_pow_le_card_isolates {φ : CNF ℕ} (hφ : φ.Satisfiable) :
    3 * 2 ^ (goodRows φ * φ.vars.length + goodRows φ) ≤
      16 * (Finset.univ.filter fun p :
        (Fin (goodRows φ) → BitString φ.vars.length) × BitString (goodRows φ) =>
          Isolates φ p).card := by
  classical
  have hdens := three_sixteenths_le_dens hφ
  rw [Finset.dens, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, le_div_iff₀ (by positivity)] at hdens
  have h : (3 * 2 ^ (goodRows φ * φ.vars.length + goodRows φ) : ℚ≥0) ≤
      16 * (Finset.univ.filter fun p :
        (Fin (goodRows φ) → BitString φ.vars.length) × BitString (goodRows φ) =>
          Isolates φ p).card := by
    rw [pow_add, pow_mul', ← mul_assoc]
    have := mul_le_mul_of_nonneg_left hdens (by norm_num : (0 : ℚ≥0) ≤ 16)
    convert this using 1
    push_cast
    ring
  exact_mod_cast h

/-! ### Counting random words -/

/-- A prefix of a word given by its bits. -/
theorem take_ofFn {m a : ℕ} (h : a ≤ m) (r : Fin m → Bool) :
    (List.ofFn r).take a = List.ofFn fun i : Fin a => r (Fin.castLE h i) :=
  (Fin.ofFn_take_eq_take_ofFn h r).symm

/-- A suffix of a word given by its bits. -/
theorem drop_ofFn {m a : ℕ} (h : a ≤ m) (r : Fin m → Bool) :
    (List.ofFn r).drop a = List.ofFn fun j : Fin (m - a) => r ⟨a + j, by omega⟩ :=
  List.ext_getElem (by simp) fun i _ _ => by simp

/-- The coefficients only read the first `k * width + k` bits. -/
theorem matrix_take (k width : ℕ) (w : List Bool) :
    matrix k width (w.take (k * width + k)) = matrix k width w := by
  funext i j
  simp only [matrix, BitString.block_apply, BitString.ofList, List.getD_eq_getElem?_getD,
    List.getElem?_take]
  rw [ite_eq_left (by have := (finProdFinEquiv (i, j)).2; omega)]

/-- The offsets only read the first `k * width + k` bits. -/
theorem offset_take (k width : ℕ) (w : List Bool) :
    offset k width (w.take (k * width + k)) = offset k width w := by
  funext i
  simp only [offset, BitString.ofList, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_take]
  rw [ite_eq_left (by omega)]

/-- The coefficients of a word of exactly `k * width + k` bits are its first blocks. -/
private theorem matrix_ofFn_append {k width : ℕ} (a : BitString (k * width)) (b : BitString k) :
    matrix k width (List.ofFn (Fin.append a b)) = BitString.blocksEquiv a := by
  rw [matrix, List.ofFn_fin_append, BitString.ofList_ofFn_append]
  rfl

/-- The offsets of a word of exactly `k * width + k` bits are its last `k` bits. -/
private theorem offset_ofFn_append {k width : ℕ} (a : BitString (k * width)) (b : BitString k) :
    offset k width (List.ofFn (Fin.append a b)) = b := by
  rw [offset, List.ofFn_fin_append, List.drop_left' (by simp), BitString.ofList_ofFn]

/-- Reading the coefficients and offsets is a bijection from words of exactly
`k * width + k` bits. -/
theorem card_filter_seed {k width : ℕ}
    (U : (Fin k → BitString width) × BitString k → Prop) [DecidablePred U] :
    (Finset.univ.filter fun v : Fin (k * width + k) → Bool =>
      U (matrix k width (List.ofFn v), offset k width (List.ofFn v))).card =
      (Finset.univ.filter U).card := by
  refine Finset.card_nbij' (fun v => (matrix k width (List.ofFn v), offset k width (List.ofFn v)))
    (fun p => Fin.append (BitString.blocksEquiv.symm p.1) p.2)
    (fun v hv => by simpa using hv) (fun p hp => ?_) (fun v _ => ?_) (fun p _ => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rwa [matrix_ofFn_append, offset_ofFn_append, Equiv.apply_symm_apply]
  · conv_rhs => rw [← Fin.append_castAdd_natAdd (f := v)]
    conv_lhs => rw [← Fin.append_castAdd_natAdd (f := v)]
    simp only [matrix_ofFn_append, offset_ofFn_append, Equiv.symm_apply_apply]
  · simp only
    rw [matrix_ofFn_append, offset_ofFn_append, Equiv.apply_symm_apply]

open Classical in
/-- The random words of length `m` for which the reduction outputs a uniquely satisfiable formula
are at least `3 / (16 * 2 ^ hashBits φ)` of all words, once `m` covers the selector bits and
the coefficients and offsets of `goodRows φ` equations. -/
private theorem three_mul_two_pow_le_card {φ : CNF ℕ} (hφ : φ.Satisfiable) {m : ℕ}
    (hm : hashBits φ + (goodRows φ * φ.vars.length + goodRows φ) ≤ m) :
    3 * 2 ^ m ≤ 16 * 2 ^ hashBits φ *
      (Finset.univ.filter fun r : Fin m → Bool => reduce (φ, List.ofFn r) ∈ USAT).card := by
  set t := hashBits φ
  set k := goodRows φ
  set n := φ.vars.length
  -- the event: the selector bits read `k`, and the equations isolate a solution
  have hsub : (Finset.univ.filter fun r : Fin m → Bool =>
      BitString.binaryValue ((List.ofFn r).take t) = k ∧
        Isolates φ (matrix k n ((List.ofFn r).drop t), offset k n ((List.ofFn r).drop t))) ⊆
      Finset.univ.filter fun r : Fin m → Bool => reduce (φ, List.ofFn r) ∈ USAT := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [reduce]
    simp only
    rw [hr.1]
    exact reduceWith_mem_USAT hr.2
  have hsplit := BitString.card_filter_take_drop (show t ≤ m by omega)
    (fun w => BitString.binaryValue w = k) (fun w => Isolates φ (matrix k n w, offset k n w))
  have hrest := BitString.card_filter_take_drop (show k * n + k ≤ m - t by omega)
    (fun w => Isolates φ (matrix k n w, offset k n w)) (fun _ => True)
  simp only [and_true, Finset.filter_true, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, matrix_take, offset_take] at hrest
  rw [card_filter_seed (fun p => Isolates φ p)] at hrest
  obtain ⟨u, hu⟩ := BitString.exists_binaryValue_eq (goodRows_lt_two_pow_hashBits φ)
  have hone : 1 ≤ (Finset.univ.filter fun u : Fin t → Bool =>
      BitString.binaryValue (List.ofFn u) = k).card :=
    Finset.card_pos.2 ⟨u, by simpa using hu⟩
  have hU := three_mul_two_pow_le_card_isolates hφ
  have hm' : m = t + (k * n + k) + (m - t - (k * n + k)) := by omega
  calc 3 * 2 ^ m = 3 * 2 ^ (k * n + k) * 2 ^ t * 2 ^ (m - t - (k * n + k)) := by
        conv_lhs => rw [hm']
        rw [pow_add, pow_add]
        ring
    _ ≤ 16 * (Finset.univ.filter fun p => Isolates φ p).card * 2 ^ t *
          2 ^ (m - t - (k * n + k)) := by gcongr
    _ = 16 * 2 ^ t * (1 * ((Finset.univ.filter fun p => Isolates φ p).card *
          2 ^ (m - t - (k * n + k)))) := by ring
    _ ≤ 16 * 2 ^ t * ((Finset.univ.filter fun u : Fin t → Bool =>
          BitString.binaryValue (List.ofFn u) = k).card *
          ((Finset.univ.filter fun p => Isolates φ p).card * 2 ^ (m - t - (k * n + k)))) := by
        gcongr
    _ = 16 * 2 ^ t * (Finset.univ.filter fun r : Fin m → Bool =>
          BitString.binaryValue ((List.ofFn r).take t) = k ∧
            Isolates φ (matrix k n ((List.ofFn r).drop t),
              offset k n ((List.ofFn r).drop t))).card := by
        rw [hsplit, hrest]
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)

/-- The number of random bits the reduction reads on `φ`: `hashBits φ` selector bits, then the
coefficients and offsets of up to `φ.vars.length + 2` equations of `φ.vars.length` terms. -/
def randomBits (φ : CNF ℕ) : ℕ := hashBits φ + (φ.vars.length + 2) * (φ.vars.length + 1)

/-- The selector reads at most `φ.vars.length + 2` bits. -/
private theorem hashBits_le (φ : CNF ℕ) : hashBits φ ≤ φ.vars.length + 2 :=
  Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega))

/-- The reduction reads at most `(φ.vars.length + 2) ^ 2` random bits. -/
theorem randomBits_le (φ : CNF ℕ) : randomBits φ ≤ (φ.vars.length + 2) ^ 2 := by
  have := hashBits_le φ
  rw [randomBits, sq]
  nlinarith

open Classical in
/-- **The Valiant–Vazirani reduction succeeds with probability `Ω(1 / n)`.** For a satisfiable
formula `φ` with `n = φ.vars.length` variable occurrences and any number `m ≥ randomBits φ` of
random bits, the reduced formula is uniquely satisfiable for at least a `3 / (32 (n + 3))`
fraction of the random words of length `m`. Since `n` counts occurrences, not variables, this is
`Ω(1 / |φ|)` in the length of the formula, weaker than the textbook bound `1 / (8 v)` in the
number `v` of variables. -/
theorem three_mul_two_pow_le_card_reduce_mem_USAT {φ : CNF ℕ} (hφ : φ ∈ SAT) {m : ℕ}
    (hm : randomBits φ ≤ m) :
    3 * 2 ^ m ≤ 32 * (φ.vars.length + 3) *
      (Finset.univ.filter fun r : Fin m → Bool => reduce (φ, List.ofFn r) ∈ USAT).card := by
  have hk := goodRows_le φ
  have h := three_mul_two_pow_le_card hφ (m := m) (by
    rw [randomBits] at hm
    have : goodRows φ * φ.vars.length + goodRows φ ≤
        (φ.vars.length + 2) * (φ.vars.length + 1) := by nlinarith
    omega)
  refine h.trans (Nat.mul_le_mul_right _ ?_)
  have := two_pow_hashBits_le φ
  omega

open Classical in
/-- **The Valiant–Vazirani success probability as a density**: for a satisfiable formula `φ` with
`n = φ.vars.length` variable occurrences and `m ≥ randomBits φ`, a uniformly random word of
length `m` makes the reduced formula uniquely satisfiable with probability at least
`3 / (32 (n + 3))`. -/
theorem three_div_le_dens_reduce_mem_USAT {φ : CNF ℕ} (hφ : φ ∈ SAT) {m : ℕ}
    (hm : randomBits φ ≤ m) :
    3 / (32 * (φ.vars.length + 3)) ≤ Finset.dens
      (Finset.univ.filter fun r : Fin m → Bool => reduce (φ, List.ofFn r) ∈ USAT) := by
  have h := three_mul_two_pow_le_card_reduce_mem_USAT hφ hm
  rw [Finset.dens, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    div_le_div_iff₀ (by positivity) (by positivity), mul_comm (Finset.card _ : ℚ≥0)]
  exact_mod_cast h

/-! ### Amplification -/

open Classical in
/-- **Amplification by independent rows.** If at least a `3 / (32 M)` fraction of the words of
length `W` are good, then among the words of `11 M` rows of `W` bits, at least half have a good
row: the repeated-trials bound `Fintype.half_le_dens_filter_exists_apply_mem`, transferred along
the block decomposition. -/
theorem two_pow_le_two_mul_card_exists_row {M W : ℕ} (hM : 0 < M) (good : List Bool → Prop)
    [DecidablePred good]
    (hgood : 3 * 2 ^ W ≤
      32 * M * (Finset.univ.filter fun b : Fin W → Bool => good (List.ofFn b)).card) :
    2 ^ (11 * M * W) ≤ 2 * (Finset.univ.filter fun r : Fin (11 * M * W) → Bool =>
      ∃ b ∈ BitString.listRows (11 * M) W (List.ofFn r), good b).card := by
  set s := Finset.univ.filter fun b : Fin W → Bool => good (List.ofFn b) with hs
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hq : (3 / (32 * M) : ℚ) ≤ (s.dens : ℚ) := by
    rw [Finset.dens, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (3 * 2 ^ W : ℚ) ≤ 32 * M * s.card := by exact_mod_cast hgood
    linarith
  have h := Fintype.half_le_dens_filter_exists_apply_mem (ι := Fin (11 * M)) (s := s) (𝕜 := ℚ)
    (by positivity) hq (by rw [Fintype.card_fin]; push_cast; field_simp; norm_num)
  have hcard : (Finset.univ.filter fun r : Fin (11 * M * W) → Bool =>
      ∃ b ∈ BitString.listRows (11 * M) W (List.ofFn r), good b).card =
      (Finset.univ.filter fun ω : Fin (11 * M) → BitString W => ∃ j, ω j ∈ s).card := by
    refine Finset.card_equiv BitString.blocksEquiv fun r => ?_
    simp [BitString.listRows_eq_ofFn, hs]
  rw [Finset.dens, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_fin, ← hcard] at h
  push_cast at h
  rw [le_div_iff₀ (by positivity), ← pow_mul, mul_comm W] at h
  exact_mod_cast (by push_cast; linarith : ((2 ^ (11 * M * W) : ℕ) : ℚ) ≤
    ((2 * (Finset.univ.filter fun r : Fin (11 * M * W) → Bool =>
      ∃ b ∈ BitString.listRows (11 * M) W (List.ofFn r), good b).card : ℕ) : ℚ))

end Cslib.Complexity.ValiantVazirani
