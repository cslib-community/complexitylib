/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Encoding
public import Complexity.Logics.SecondOrder.Existential
public import Complexity.Computability.Complexity.Classes.NP
public import Mathlib.SetTheory.Cardinal.NatCard
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Existential second-order definable classes are in NP

The easy direction of Fagin's theorem [Fagin, Theorem 6][Fagin1974],
[Immerman, Proposition 7.6][Immerman1999]: for a fixed existential second-order sentence
`Φ = ∃ R₁ … Rₖ, φ` over a vocabulary, the inputs encoding the finite structures satisfying `Φ`
form a problem in `NP`. The certificate for an input of encoded length `N` is a bit string of
length `blocks * N ^ degree`, where a layout (`Cslib.Logic.ESO.Sentence.Layout`) gives each
relation variable its own block of `N ^ degree` bits and `degree` bounds the arities. The block
of a relation variable is its truth table, indexed like the tables of the input by
`Cslib.Logic.tupleIndex`; since the cardinality `n` of the structure is at most `N`, every tuple
has a bit, and the unused bits of a block are ignored. Reading the blocks as relations
(`Cslib.Logic.ESO.Sentence.Layout.certRel`) expands the decoded structure by the relation
variables, and the verifier (`Cslib.Logic.ESO.Sentence.Layout.verifier`) checks that the input is
well formed and evaluates the first-order part in the expansion. The evaluator
(`Cslib.Logic.ESO.Sentence.Layout.eval`) recurses on the fixed formula and ranges over the `n`
elements at each quantifier, so it is a polynomial-time program for each fixed sentence;
`fun_prop` certifies it with the closure rules of `Turing.MultiTapeTM.ComputableInPolyTime`.

The sentence and the vocabulary are fixed parameters: the degree of the polynomial time bound
depends on the quantifier depth and the arities of the sentence, and the number of relation symbols
enters the length of the input. Malformed inputs are rejected by the verifier and are not in the
problem. Which certificates are accepted depends on the layout; the problem does not. The converse
direction, that every isomorphism-closed problem in `NP` is existential second-order definable,
is not proved here.

## Main definitions

* `Cslib.Logic.ESO.Sentence.Layout`: a certificate layout for a sentence, with its polynomial
  `Layout.polynomial` of certificate lengths.
* `Cslib.Logic.ESO.Sentence.Layout.eval`: the evaluator of the first-order part on an input and a
  certificate.
* `Cslib.Logic.ESO.Sentence.Layout.verifier`: the verifier.

## Main results

* `Cslib.Logic.ESO.Sentence.Layout.eval_eq_true_iff`: the evaluator decides truth in the expansion
  of the decoded structure by the certificate relations.
* `Cslib.Logic.ESO.Sentence.Layout.realize_iff_exists_certificate`: a decoded structure satisfies
  the sentence exactly when some certificate is accepted.
* `Cslib.Logic.ESO.Sentence.Layout.computableInPolyTime_verifier`: the verifier is
  polynomial-time.
* `Cslib.Logic.ESO.Sentence.queryLanguage_mem_NP`,
  `Cslib.Logic.ESO.Definable.queryLanguage_mem_NP`: the problem of a sentence, and the query
  language of a definable class, are in `NP`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v

open FirstOrder Language Structure CategoryTheory Turing.MultiTapeTM Cslib.Complexity

namespace Cslib.Logic.ESO.Sentence

variable {L : Language.{u, v}} (Φ : Sentence L)

/-! ### Layouts -/

/-- A **certificate layout** for `Φ`: a block number for each relation variable, and a bound on
their arities. A certificate for an input of encoded length `N` has `blocks * N ^ degree` bits,
block `i` holding the truth table of relation variable `i`. -/
structure Layout where
  /-- The number of blocks. -/
  blocks : ℕ
  /-- The block of each relation variable. -/
  block : Φ.Var ↪ Fin blocks
  /-- A bound on the arities of the relation variables. -/
  degree : ℕ
  arity_le : ∀ i, Φ.arity i ≤ degree

/-- Every sentence has a layout, numbering its finitely many relation variables. -/
private noncomputable def Layout.ofFinite : Layout Φ where
  blocks := Nat.card Φ.Var
  block := (Finite.equivFin Φ.Var).toEmbedding
  degree := ⨆ i, Φ.arity i
  arity_le i := le_ciSup (Set.finite_range Φ.arity).bddAbove i

instance : Nonempty (Layout Φ) :=
  ⟨Layout.ofFinite Φ⟩

namespace Layout

variable {Φ} (ℓ : Layout Φ)

/-- The polynomial giving the length of certificates in the encoded length of the input. -/
noncomputable def polynomial : Polynomial ℕ :=
  Polynomial.C ℓ.blocks * Polynomial.X ^ ℓ.degree

theorem eval_polynomial (N : ℕ) : ℓ.polynomial.eval N = ℓ.blocks * N ^ ℓ.degree := by
  simp [polynomial]

/-- The position of the bit of relation variable `i` at the tuple of index `idx`, in a certificate
for an input of encoded length `N`. -/
def position (N : ℕ) (i : Φ.Var) (idx : ℕ) : ℕ :=
  ℓ.block i * N ^ ℓ.degree + idx

private theorem position_lt (N : ℕ) (i : Φ.Var) {idx : ℕ} (h : idx < N ^ ℓ.degree) :
    ℓ.position N i idx < ℓ.blocks * N ^ ℓ.degree := by
  unfold position
  calc ℓ.block i * N ^ ℓ.degree + idx < (ℓ.block i + 1) * N ^ ℓ.degree := by
        rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ ℓ.blocks * N ^ ℓ.degree := Nat.mul_le_mul_right _ (ℓ.block i).2

/-- Positions determine the relation variable and the index of the tuple. -/
theorem position_injective (N : ℕ) {i j : Φ.Var} {idx idx' : ℕ} (h : idx < N ^ ℓ.degree)
    (h' : idx' < N ^ ℓ.degree) (he : ℓ.position N i idx = ℓ.position N j idx') :
    i = j ∧ idx = idx' := by
  have hB : 0 < N ^ ℓ.degree := by omega
  have hdiv : ∀ (b idx : ℕ), idx < N ^ ℓ.degree → (b * N ^ ℓ.degree + idx) / N ^ ℓ.degree = b :=
    fun b idx h => by rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt h, Nat.add_zero]
  have hmod : ∀ (b idx : ℕ), idx < N ^ ℓ.degree → (b * N ^ ℓ.degree + idx) % N ^ ℓ.degree = idx :=
    fun b idx h => by rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h]
  unfold position at he
  have h₁ := congrArg (· / N ^ ℓ.degree) he
  have h₂ := congrArg (· % N ^ ℓ.degree) he
  simp only [hdiv _ _ h, hdiv _ _ h', hmod _ _ h, hmod _ _ h'] at h₁ h₂
  exact ⟨ℓ.block.injective (Fin.ext h₁), h₂⟩

/-- The number of tuples of the arity of a relation variable is at most the block size, for inputs
of cardinality at most `N`. -/
private theorem pow_arity_le {n N : ℕ} (hn : n ≤ N) (hN : 0 < N) (i : Φ.Var) :
    n ^ Φ.arity i ≤ N ^ ℓ.degree :=
  (Nat.pow_le_pow_left hn _).trans (Nat.pow_le_pow_right hN (ℓ.arity_le i))

/-- The relations read from a certificate: relation variable `i` holds of a tuple when the bit at
its position is set; missing bits read as false. -/
def certRel (n N : ℕ) (w : List Bool) (i : Φ.Var) : Set (Fin (Φ.arity i) → Fin n) :=
  {x | w.getD (ℓ.position N i (tupleIndex x)) false = true}

open scoped Classical in
/-- The certificate encoding relations `R` on `Fin n`, for inputs of encoded length `N`: the bit
at the position of a tuple is its membership in the relation, and the other bits are clear. -/
private noncomputable def certificate (n N : ℕ) (R : ∀ i, Set (Fin (Φ.arity i) → Fin n))
    : List Bool :=
  (List.range (ℓ.blocks * N ^ ℓ.degree)).map fun pos =>
    decide (∃ (i : Φ.Var) (x : Fin (Φ.arity i) → Fin n),
      pos = ℓ.position N i (tupleIndex x) ∧ x ∈ R i)

private theorem length_certificate (n N : ℕ) (R : ∀ i, Set (Fin (Φ.arity i) → Fin n)) :
    (ℓ.certificate n N R).length = ℓ.blocks * N ^ ℓ.degree := by
  simp [certificate]

/-- Reading the certificate of `R` gives back `R`, when every tuple has a bit. -/
private theorem certRel_certificate {n N : ℕ} (hn : n ≤ N) (hN : 0 < N)
    (R : ∀ i, Set (Fin (Φ.arity i) → Fin n)) : ℓ.certRel n N (ℓ.certificate n N R) = R := by
  funext i
  ext x
  have hx : tupleIndex x < N ^ ℓ.degree := (tupleIndex_lt x).trans_le (ℓ.pow_arity_le hn hN i)
  simp only [certRel, Set.mem_ofPred_eq]
  rw [List.getD_eq_getElem (ℓ.certificate n N R) false
    (by rw [length_certificate]; exact ℓ.position_lt N i hx)]
  simp only [certificate, List.getElem_map, List.getElem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨j, y, he, hy⟩
    have hy' : tupleIndex y < N ^ ℓ.degree := (tupleIndex_lt y).trans_le (ℓ.pow_arity_le hn hN j)
    obtain ⟨rfl, hxy⟩ := ℓ.position_injective N hx hy' he
    rwa [tupleIndex_injective hxy]
  · exact fun hx => ⟨i, x, rfl, hx⟩

/-! ### The evaluator -/

variable [L.IsRelational] (v : Vocabulary L)

/-- The expansion of the decoded structure by the relations read from a certificate. -/
@[instance_reducible]
def expansion (a : EncodedStructure) (N : ℕ) (w : List Bool) :
    (L.sum (varLanguage Φ.arity)).Structure (Fin a.1) :=
  @sumStructure _ _ _ (v.decode a) (varLanguage.structure (ℓ.certRel a.1 N w))

/-- The position of a variable in the environment: bound variables are numbered, and a sentence
has no free variables. -/
def varPos {k : ℕ} : Empty ⊕ Fin k → ℕ
  | .inl e => e.elim
  | .inr i => i

/-- The value of a term in an environment of bound variables; in a relational language, a term
is a variable. -/
def termValue {k : ℕ} (σ : List ℕ) (t : (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)) :
    ℕ :=
  σ.getD (varPos (FO.termVar t)) 0

/-- The index of the tuple of values of a sequence of terms, by recursion on its length. -/
def termsIndex (n : ℕ) {k : ℕ} (σ : List ℕ) :
    ∀ {l : ℕ}, (Fin l → (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)) → ℕ
  | 0, _ => 0
  | _ + 1, ts => termValue σ (ts 0) + n * termsIndex n σ fun j => ts j.succ

/-- The bit of a relation symbol at a tuple index: read from the input for a symbol of the
vocabulary, from the certificate for a relation variable. -/
def relBit (a : EncodedStructure) (N : ℕ) (w : List Bool) {l : ℕ}
    (R : (L.sum (varLanguage Φ.arity)).Relations l) (idx : ℕ) : Bool :=
  match R with
  | .inl r => (v.table a ⟨_, r⟩).getD idx false
  | .inr r => w.getD (ℓ.position N r.1 idx) false

/-- The evaluator of the first-order part on an input `a` of encoded length `N`, a certificate
`w`, and an environment of bound variables: quantifiers range over the `a.1` elements. -/
def eval (a : EncodedStructure) (N : ℕ) (w : List Bool) :
    ∀ {k : ℕ}, (L.sum (varLanguage Φ.arity)).BoundedFormula Empty k → List ℕ → Bool
  | _, .falsum, _ => false
  | _, .equal t₁ t₂, σ => termValue σ t₁ == termValue σ t₂
  | _, .rel R ts, σ => ℓ.relBit v a N w R (termsIndex a.1 σ ts)
  | _, .imp φ ψ, σ => !eval a N w φ σ || eval a N w ψ σ
  | _, .all φ, σ => (List.range a.1).all fun x => eval a N w φ (σ ++ [x])

/-- The verifier: the input is well formed and the first-order part holds in the expansion of the
decoded structure by the certificate relations. -/
def verifier (p : EncodedStructure × List Bool) : Bool :=
  v.checkShape p.1 && ℓ.eval v p.1 (encStructure p.1).length p.2 Φ.matrix []

/-! ### Correctness -/

section Correctness

variable {v} {a : EncodedStructure} {N : ℕ} {w : List Bool}

private theorem termValue_ofFn {k : ℕ} (xs : Fin k → Fin a.1)
    (t : (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)) :
    termValue (Φ := Φ) (List.ofFn fun j => (xs j : ℕ)) t =
      Fin.val (Sum.elim (default : Empty → Fin a.1) xs (FO.termVar t)) := by
  unfold termValue
  rcases FO.termVar t with e | i
  · exact e.elim
  · simp [varPos]

private theorem termsIndex_ofFn {k : ℕ} (xs : Fin k → Fin a.1) :
    ∀ {l : ℕ} (ts : Fin l → (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)),
      termsIndex (Φ := Φ) a.1 (List.ofFn fun j => (xs j : ℕ)) ts =
        tupleIndex fun j => Sum.elim (default : Empty → Fin a.1) xs (FO.termVar (ts j))
  | 0, _ => by simp [termsIndex, tupleIndex_apply]
  | l + 1, ts => by
    rw [termsIndex, termsIndex_ofFn xs, termValue_ofFn, tupleIndex_apply, tupleIndex_apply,
      Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.val_succ, pow_succ]
    ring

theorem relBit_eq_true_iff {l : ℕ} (R : (L.sum (varLanguage Φ.arity)).Relations l)
    (y : Fin l → Fin a.1) :
    ℓ.relBit v a N w R (tupleIndex y) = true ↔ (ℓ.expansion v a N w).RelMap R y := by
  rcases R with r | r
  · exact Iff.rfl
  · change _ ↔ y ∘ Fin.cast r.2 ∈ ℓ.certRel a.1 N w r.1
    simp only [certRel, Set.mem_ofPred_eq, relBit, tupleIndex_comp_cast]

private theorem ofFn_val_snoc {k : ℕ} (xs : Fin k → Fin a.1) (x : Fin a.1) :
    (List.ofFn fun j => ((Fin.snoc xs x : Fin (k + 1) → Fin a.1) j : ℕ)) =
      (List.ofFn fun j => (xs j : ℕ)) ++ [(x : ℕ)] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

/-- **The evaluator decides truth** of the first-order part in the expansion of the decoded
structure by the certificate relations. -/
theorem eval_eq_true_iff :
    ∀ {k : ℕ} (φ : (L.sum (varLanguage Φ.arity)).BoundedFormula Empty k) (xs : Fin k → Fin a.1),
      ℓ.eval v a N w φ (List.ofFn fun j => (xs j : ℕ)) = true ↔
        (letI := ℓ.expansion v a N w; φ.Realize default xs)
  | _, .falsum, _ => by simp [eval, BoundedFormula.Realize]
  | _, .equal t₁ t₂, xs => by
    let _ := ℓ.expansion v a N w
    simp only [eval, beq_iff_eq, termValue_ofFn, Fin.val_inj]
    change _ ↔ t₁.realize (Sum.elim default xs) = t₂.realize (Sum.elim default xs)
    rw [FO.realize_termVar, FO.realize_termVar]
  | _, .rel R ts, xs => by
    let _ := ℓ.expansion v a N w
    change ℓ.relBit v a N w R _ = true ↔ RelMap R fun j => (ts j).realize (Sum.elim default xs)
    rw [termsIndex_ofFn, relBit_eq_true_iff]
    simp only [FO.realize_termVar]
  | _, .imp φ ψ, xs => by
    let _ := ℓ.expansion v a N w
    rw [BoundedFormula.realize_imp, ← eval_eq_true_iff φ xs, ← eval_eq_true_iff ψ xs]
    simp only [eval, Bool.or_eq_true, Bool.not_eq_true']
    cases ℓ.eval v a N w φ (List.ofFn fun j => (xs j : ℕ)) <;> simp
  | _, .all φ, xs => by
    let _ := ℓ.expansion v a N w
    rw [BoundedFormula.realize_all]
    simp only [eval, List.all_eq_true, List.mem_range]
    constructor
    · intro h x
      rw [← eval_eq_true_iff φ, ofFn_val_snoc]
      exact h x x.2
    · intro h x hx
      have := (eval_eq_true_iff φ (Fin.snoc xs ⟨x, hx⟩)).2 (h ⟨x, hx⟩)
      rwa [ofFn_val_snoc] at this

/-- The first-order part holds in the expansion by the certificate relations exactly when the
evaluator accepts. -/
theorem eval_matrix_eq_true_iff :
    ℓ.eval v a N w Φ.matrix [] = true ↔
      (letI := ℓ.expansion v a N w; Fin a.1 ⊨ Φ.matrix) := by
  have := ℓ.eval_eq_true_iff (v := v) (a := a) (N := N) (w := w) Φ.matrix default
  rwa [List.ofFn_zero] at this

/-- **A decoded structure satisfies the sentence exactly when some certificate is accepted**, for
certificate lengths computed from any `N` at least the cardinality. -/
theorem realize_iff_exists_certificate (hn : a.1 ≤ N) (hN : 0 < N) :
    (letI := v.decode a; Φ.Realize (Fin a.1)) ↔
      ∃ w : List Bool, w.length = ℓ.blocks * N ^ ℓ.degree ∧ ℓ.eval v a N w Φ.matrix [] = true := by
  let _ := v.decode a
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨ℓ.certificate a.1 N R, ℓ.length_certificate a.1 N R, ?_⟩
    rw [eval_matrix_eq_true_iff]
    have hw := ℓ.certRel_certificate hn hN R
    revert hR
    unfold expansion
    rw [hw]
    exact id
  · rintro ⟨w, -, hw⟩
    exact ⟨ℓ.certRel a.1 N w, (eval_matrix_eq_true_iff ℓ).1 hw⟩

/-- The verifier accepts an input with some certificate of the prescribed length exactly when the
input is well formed and its decoded structure satisfies the sentence. -/
theorem exists_verifier_eq_true_iff (a : EncodedStructure) :
    (∃ w : List Bool, w.length = ℓ.polynomial.eval (encStructure a).length ∧
        ℓ.verifier v (a, w) = true) ↔
      v.WellFormed a ∧ (letI := v.decode a; Φ.Realize (Fin a.1)) := by
  have hN : 0 < (encStructure a).length := by
    simp only [encStructure, length_encPair]; omega
  rw [realize_iff_exists_certificate ℓ (card_le_length_encStructure a) hN]
  simp only [verifier, Bool.and_eq_true, v.checkShape_eq_true_iff, eval_polynomial]
  constructor
  · rintro ⟨w, hw, hshape, heval⟩
    exact ⟨hshape, w, hw, heval⟩
  · rintro ⟨hshape, w, hw, heval⟩
    exact ⟨w, hw, hshape, heval⟩

/-- The verifier, with the certificate lengths of the layout, verifies the query language of a
class defined by the sentence. -/
theorem isVerifier {K : Set (Bundled.{0} L.Structure)}
    (hK : ∀ (M : Bundled.{0} L.Structure) [Finite M], M ∈ K ↔ Φ.Realize M) :
    IsVerifier encStructure ℓ.polynomial (ℓ.verifier v) (v.queryLanguage K) := by
  intro a
  have : Finite (v.decoded a) := inferInstanceAs (Finite (Fin a.1))
  rw [exists_verifier_eq_true_iff, Vocabulary.mem_queryLanguage, hK (v.decoded a)]
  rfl

end Correctness

/-! ### Polynomial time -/

section PolyTime

open ComputableInPolyTime

variable {v} {γ : Type} {encIn : γ ↪ List Bool}

private theorem unary_beq_plain {left right : γ → ℕ}
    (hleft : ComputableInPolyTime left encIn encUnary)
    (hright : ComputableInPolyTime right encIn encUnary) :
    ComputableInPolyTime (fun a => left a == right a) encIn encBool :=
  (bool_and' (unary_le' hleft hright) (unary_le' hright hleft)).of_enc_eq fun _ => by
    rw [encBool.injective.eq_iff, Bool.eq_iff_iff]
    simp [Nat.le_antisymm_iff]

omit [L.IsRelational] in
/-- Reading a table of the input is polynomial-time. -/
@[fun_prop]
theorem _root_.Cslib.Logic.Vocabulary.computableInPolyTime_table (r : Σ n, L.Relations n)
    {a : γ → EncodedStructure} (ha : ComputableInPolyTime a encIn encStructure) :
    ComputableInPolyTime (fun x => v.table (a x) r) encIn encBits :=
  listGetDWithInput ((snd encUnary (encList encBits)).comp ha) (const (v.index r)) []

/-- The cardinality of the input, in unary. -/
private theorem computableInPolyTime_card {a : γ → EncodedStructure}
    (ha : ComputableInPolyTime a encIn encStructure) :
    ComputableInPolyTime (fun x => (a x).1) encIn encUnary :=
  (fst encUnary (encList encBits)).comp ha

omit [L.IsRelational] in
/-- Checking well-formedness is polynomial-time. -/
@[fun_prop]
theorem _root_.Cslib.Logic.Vocabulary.computableInPolyTime_checkShape :
    ComputableInPolyTime v.checkShape encStructure encBool := by
  unfold Vocabulary.checkShape
  refine bool_and' (unary_beq_plain ((length_list encBits).comp (snd encUnary (encList encBits)))
    (const v.count)) (allConst _ fun i _ => unary_beq_plain ?_ ?_)
  · exact length_bits_comp (listGetDWithInput (snd encUnary (encList encBits))
      (const (i : ℕ)) [])
  · exact (unary_pow _).comp (computableInPolyTime_card id')

@[fun_prop]
theorem computableInPolyTime_termValue {k : ℕ} {σ : γ → List ℕ}
    (hσ : ComputableInPolyTime σ encIn (encList encUnary))
    (t : (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)) :
    ComputableInPolyTime (fun x => termValue (Φ := Φ) (σ x) t) encIn encUnary :=
  listGetDWithInput hσ (const (varPos (FO.termVar t))) 0

@[fun_prop]
theorem computableInPolyTime_termsIndex {k : ℕ} {n : γ → ℕ} {σ : γ → List ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hσ : ComputableInPolyTime σ encIn (encList encUnary)) :
    ∀ {l : ℕ} (ts : Fin l → (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)),
      ComputableInPolyTime (fun x => termsIndex (Φ := Φ) (n x) (σ x) ts) encIn encUnary
  | 0, _ => const 0
  | _ + 1, ts =>
    unary_add' (computableInPolyTime_termValue hσ (ts 0))
      (unary_mul' hn (computableInPolyTime_termsIndex hn hσ fun j => ts j.succ))

omit [L.IsRelational] in
@[fun_prop]
theorem computableInPolyTime_relBit {l : ℕ}
    (R : (L.sum (varLanguage Φ.arity)).Relations l) {a : γ → EncodedStructure} {N : γ → ℕ}
    {w : γ → List Bool} {idx : γ → ℕ} (ha : ComputableInPolyTime a encIn encStructure)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (hidx : ComputableInPolyTime idx encIn encUnary) :
    ComputableInPolyTime (fun x => ℓ.relBit v (a x) (N x) (w x) R (idx x)) encIn encBool :=
  match R with
  | .inl r => bitsGetDWithInput (v.computableInPolyTime_table ⟨_, r⟩ ha) hidx false
  | .inr r => bitsGetDWithInput hw (unary_add'
      (unary_mul' (const (ℓ.block r.1 : ℕ)) ((unary_pow _).comp hN)) hidx) false

/-- **The evaluator is polynomial-time** for each fixed formula, by induction on the formula. The
input type is generalized, as the body of a quantifier takes the current element as well. -/
@[fun_prop]
theorem computableInPolyTime_eval {k : ℕ}
    (φ : (L.sum (varLanguage Φ.arity)).BoundedFormula Empty k) {γ : Type}
    {encIn : γ ↪ List Bool} {a : γ → EncodedStructure} {N : γ → ℕ} {w : γ → List Bool}
    {σ : γ → List ℕ} (ha : ComputableInPolyTime a encIn encStructure)
    (hN : ComputableInPolyTime N encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (hσ : ComputableInPolyTime σ encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => ℓ.eval v (a x) (N x) (w x) φ (σ x)) encIn encBool := by
  induction φ generalizing γ with
  | falsum => exact const false
  | equal t₁ t₂ =>
    exact unary_beq_plain (computableInPolyTime_termValue hσ t₁)
      (computableInPolyTime_termValue hσ t₂)
  | rel R ts =>
    exact ℓ.computableInPolyTime_relBit R ha hN hw
      (computableInPolyTime_termsIndex (computableInPolyTime_card ha) hσ ts)
  | imp φ ψ ih₁ ih₂ =>
    exact bool_or.comp ((bool_not.comp (ih₁ ha hN hw hσ)).prod (ih₂ ha hN hw hσ))
  | all φ ih =>
    exact allWithInput (range.comp (computableInPolyTime_card ha))
      (ih (ha.comp (fst encIn encUnary))
        (hN.comp (fst encIn encUnary))
        (hw.comp (fst encIn encUnary))
        (listAppend' (hσ.comp (fst encIn encUnary))
          (cons' (snd encIn encUnary) (const []))))

/-- **The verifier is polynomial-time.** -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime (ℓ.verifier v) (encPair encStructure encBits) encBool :=
  bool_and' (v.computableInPolyTime_checkShape.comp (fst encStructure encBits))
    (ℓ.computableInPolyTime_eval Φ.matrix (fst encStructure encBits)
      ((encoding_length encStructure).comp (fst encStructure encBits))
      (snd encStructure encBits) (const []))

end PolyTime

end Layout

/-! ### Membership in NP -/

variable [L.IsRelational] (v : Vocabulary L)

/-- **The problem of a fixed existential second-order sentence is in NP**: the inputs encoding
the finite structures satisfying `Φ`, with respect to the encoding of structures of the
vocabulary. -/
theorem queryLanguage_mem_NP : v.queryLanguage {M | Φ.Realize M} ∈ NP encStructure :=
  let ℓ := Layout.ofFinite Φ
  ⟨ℓ.polynomial, ℓ.verifier v, ℓ.computableInPolyTime_verifier,
    ℓ.isVerifier fun _ _ => Iff.rfl⟩

end Sentence

/-- **Existential second-order definable classes are in NP** (the easy direction of Fagin's
theorem): the query language of a definable class of finite structures is in `NP`, with respect
to the encoding of structures of any vocabulary of the language
[Fagin, Theorem 6][Fagin1974], [Immerman, Proposition 7.6][Immerman1999]. -/
theorem Definable.queryLanguage_mem_NP {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)
    {K : Set (Bundled.{0} L.Structure)} (hK : Definable K) :
    v.queryLanguage K ∈ NP encStructure :=
  let ⟨Φ, hΦ⟩ := hK
  let ℓ := Sentence.Layout.ofFinite Φ
  ⟨ℓ.polynomial, ℓ.verifier v, ℓ.computableInPolyTime_verifier, ℓ.isVerifier hΦ⟩

end Cslib.Logic.ESO
