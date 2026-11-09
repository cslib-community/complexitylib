/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter
import Mathlib.Data.List.GetD

/-!
# Actual unit-clause self-reduction for the explicit DNF frontend

Fix the declared bits in order while retaining an actual satisfying extension. The runtime formula
is unchanged apart from appended unit clauses; no assignment family is enumerated. This is the
self-reduction in [ChenJiangZhu2027], Corollary 7.4 / Appendix D.5 (PDF pp.26,37).

## Main definitions

* `fix`, `query`: actual bounded unit-clause writing on retained original formulas.
* `run`: original declared-word recovery, without assignment enumeration.

## Main results

* `run_recovers`: the returned word itself satisfies the original formula.
* `exists_recovery_sharp_certificate`: actual sharp time and polynomial peak workspace.
-/

public section

namespace Cslib.Logic.PL.TwoBoundary.BinaryFrontend.Witness

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Retained original formula and already fixed prefix of its declared assignment. -/
abbrev State := Input × List Bool
/-- Retained original input, never replaced by an unrelated graph restriction. -/
@[expose] def original (s : State) : Input := s.1
/-- Actual fixed assignment prefix. -/
@[expose] def fixedBits (s : State) : List Bool := s.2
/-- Charge the complete original formula and live Boolean prefix. -/
@[expose] def encState : State ↪ List Bool := encPair encInput encBits
/-- Actual unit clauses fixing the prefix at its original declared indices. -/
@[expose] def units (p : List Bool) : CNF ℕ :=
  (List.range p.length).map fun j => [(j, p.getD j false)]
/-- Append actual unit clauses without introducing variables or conditions. -/
@[expose] def fix (s : State) : Input :=
  (declared (original s), side (original s) ++ units (fixedBits s), conditions (original s))
/-- Query a false extension of the retained prefix. -/
@[expose] def query (s : State) : Input :=
  fix (original s, (fixedBits s ++ [false]).take (declared (original s)))
/-- Append the selected next bit while retaining the original formula. -/
@[expose] def advance (b : Bool) (s : State) : State := (original s, fixedBits s ++ [b])
/-- One actual feasibility call and one Boolean prefix update. -/
@[expose] def step (test : Input → Bool) (s : State) : State :=
  if test (query s) then advance false s else advance true s
/-- Start with no fixed assignment bits. -/
@[expose] def initial (x : Input) : State := (x, [])
/-- Return the actual declared word after exactly one iteration per variable. -/
@[expose] def run (test : Input → Bool) (x : Input) : List Bool :=
  fixedBits ((step test)^[declared x] (initial x))

/-- Finite unit clauses with the very same original variable labels. -/
@[expose] def finiteUnits {n : ℕ} (p : List Bool) (hp : p.length ≤ n) : CNF (Fin n) :=
  List.ofFn fun j : Fin p.length => [(⟨j.val, Nat.lt_of_lt_of_le j.isLt hp⟩, p.getD j.val false)]

/-- Erasing bounded indices recovers the actually written unit clauses. -/
theorem finiteUnits_relabel {n : ℕ} (p : List Bool) (hp : p.length ≤ n) :
    (finiteUnits p hp).relabel Fin.val = units p := by
  simp only [finiteUnits, CNF.relabel, List.map_ofFn, Clause.relabel, List.map_cons,
    List.map_nil, Prod.map, id_eq, units, ← List.map_coe_finRange_eq_range, Function.comp_def,
    List.finRange, List.map_ofFn]

/-- Actual unit evaluation fixes precisely the stored prefix. -/
theorem finiteUnits_eval {n : ℕ} (p : List Bool) (hp : p.length ≤ n) (σ : Fin n → Bool) :
    (finiteUnits p hp).eval σ = true ↔
      ∀ i : Fin n, i.val < p.length → σ i = p.getD i.val false := by
  simp only [finiteUnits, CNF.eval_eq_true_iff, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
    Literal.eval_eq_true_iff]
  constructor
  · intro h i hi; exact h ⟨i.val, hi⟩
  · intro h j; exact h ⟨j.val, Nat.lt_of_lt_of_le j.isLt hp⟩ j.isLt

/-- Actual fixedBits writing preserves the finite representation, declaration and conditions. -/
theorem fix_ofFinite {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (p : List Bool) (hp : p.length ≤ n) :
    fix (ofFinite B P, p) = ofFinite (B ++ finiteUnits p hp) P := by
  simp only [fix, original, fixedBits, ofFinite, declared, side, conditions]
  rw [show CNF.relabel Fin.val (B ++ finiteUnits p hp) =
    B.relabel Fin.val ++ (finiteUnits p hp).relabel Fin.val from List.map_append ..,
    finiteUnits_relabel]

/-- A surviving satisfying extension of the original formula and current fixed prefix. -/
@[expose] def Admits {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n))) (p : List Bool) : Prop :=
  ∃ σ : Fin n → Bool, (B.eval σ = true ∧ ∀ q ∈ P, DNF.eval σ q = true) ∧
    ∀ i : Fin n, i.val < p.length → σ i = p.getD i.val false

private theorem trajectory (test : Input → Bool) (x : Input) (j : ℕ) :
    original ((step test)^[j] (initial x)) = x ∧
      (fixedBits ((step test)^[j] (initial x))).length = j := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    simp only [original, fixedBits] at ih
    rw [Function.iterate_succ_apply']
    simp only [step]
    split_ifs <;> simp only [advance, original, fixedBits, List.length_append,
      List.length_cons, List.length_nil] <;> exact ⟨ih.1, by omega⟩

private theorem append_fixed {n : ℕ} (p : List Bool) (b : Bool) (σ : Fin n → Bool)
    (hj : p.length < n) (h : ∀ i : Fin n, i.val < p.length → σ i = p.getD i.val false)
    (hb : σ ⟨p.length, hj⟩ = b) :
    ∀ i : Fin n, i.val < (p ++ [b]).length → σ i = (p ++ [b]).getD i.val false := by
  intro i hi
  by_cases hlt : i.val < p.length
  · rw [List.getD_append _ _ _ _ hlt]; exact h i hlt
  · have he : i.val = p.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      omega
    have heq : i = ⟨p.length, hj⟩ := Fin.ext he
    subst i
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simpa using hb

open Classical in
private theorem extend {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (p : List Bool) (hj : p.length < n) (h : Admits B P p) :
    Admits B P (p ++ [false]) ∨ Admits B P (p ++ [true]) := by
  obtain ⟨σ, hs, hf⟩ := h
  cases hb : σ ⟨p.length, hj⟩
  · exact Or.inl ⟨σ, hs, append_fixed p false σ hj hf hb⟩
  · exact Or.inr ⟨σ, hs, append_fixed p true σ hj hf hb⟩

open Classical in
/-- The actual bounded loop returns a satisfying declared word, not an existential extension.
The generic test premise is discharged by the actual sharp counter below. -/
theorem run_recovers (test : Input → Bool) {n : ℕ} (B : CNF (Fin n))
    (P : List (DNF (Fin n)))
    (ht : ∀ p : List Bool, p.length ≤ n →
      (test (fix (ofFinite B P, p)) = true ↔ Admits B P p))
    (hbase : ∃ σ : Fin n → Bool, B.eval σ = true ∧ ∀ q ∈ P, DNF.eval σ q = true) :
    let bits := run test (ofFinite B P)
    bits.length = n ∧ B.eval (fun i => bits.getD i.val false) = true ∧
      ∀ q ∈ P, DNF.eval (fun i => bits.getD i.val false) q = true := by
  have hi : ∀ j ≤ n,
      Admits B P (fixedBits ((step test)^[j] (initial (ofFinite B P)))) := by
    intro j hj
    induction j with
    | zero => obtain ⟨σ, hs⟩ := hbase; exact ⟨σ, hs, by simp [initial, fixedBits]⟩
    | succ j ih =>
      have ih := ih (by omega)
      let s := (step test)^[j] (initial (ofFinite B P))
      have ho : original s = ofFinite B P := (trajectory test _ j).1
      have hl : (fixedBits s).length = j := (trajectory test _ j).2
      have he := extend B P (fixedBits s) (by omega) ih
      have hQ : test (query s) = true ↔ Admits B P (fixedBits s ++ [false]) := by
        unfold query; rw [ho]
        have hlen : (fixedBits s ++ [false]).length ≤ n := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [show declared (ofFinite B P) = n from rfl, List.take_of_length_le hlen]
        exact ht _ hlen
      rw [Function.iterate_succ_apply']
      change Admits B P (fixedBits (step test s))
      by_cases hy : test (query s) = true
      · simpa only [step, hy, ↓reduceIte, advance, fixedBits] using hQ.mp hy
      · have hn : Admits B P (fixedBits s ++ [true]) := he.resolve_left (fun h => hy (hQ.mpr h))
        simpa only [step, hy, Bool.false_eq_true, ↓reduceIte, advance, fixedBits] using hn
  obtain ⟨σ, hs, hf⟩ := hi n (Nat.le_refl _)
  have hl : (run test (ofFinite B P)).length = n := (trajectory test _ n).2
  have heq : σ = fun i => (run test (ofFinite B P)).getD i.val false := by
    funext i; exact hf i (by change i.val < (run test (ofFinite B P)).length; omega)
  rw [heq] at hs
  exact ⟨hl, hs⟩

open Classical in
private theorem exists_test_sharp_certificate (b d : ℕ) :
    ∃ test : Input → Bool, ∃ cs : NativeCertificate test encInput encBool, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
        (_hb : ∀ c ∈ B, c.length ≤ b) (_hp : ∀ q ∈ P, ∀ t ∈ q, t.length ≤ d),
        (test (ofFinite B P) = true ↔
          ∃ σ : Fin n → Bool, B.eval σ = true ∧ ∀ q ∈ P, DNF.eval σ q = true) ∧
        cs.time (ofFinite B P) ≤ C * ((encInput (ofFinite B P)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by
  obtain ⟨count, cp, C, e, A, hs, h⟩ := BinaryFrontend.exists_count_sharp_certificate b d
  have hpos : ComputableInPolyTime (fun z : ℕ => decide (0 < z)) encNat encBool := by fun_prop
  let post := NativeCertificate.ofPolyTime hpos
  have hp := NativeCertificate.ofPolyTime_isPolynomial hpos
  let cs : NativeCertificate ((fun x => decide (0 < count x))) encInput encBool :=
    (post.comp cp).congr fun _ => rfl
  have hspace : PolyBounded (fun x => (encInput x).length) cp.space :=
    PolyBounded.of_forall_le C e hs
  obtain ⟨k, _, hlen⟩ := cp.computes
  have hlength : PolyBounded (fun x => (encInput x).length)
      (fun x => (encNat (count x)).length) :=
    ((PolyBounded.const k).mul (hspace.add (.const 1))).mono hlen
  have hpostT := hp.1.comp hlength
  have hpostS := hp.2.comp hlength
  have hcsS : PolyBounded (fun x => (encInput x).length) cs.space := hspace.add hpostS
  let W (x : Input) := C * ((encInput x).length + 1) ^ e + post.time (count x) + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (((PolyBounded.const C).mul ((PolyBounded.self.add (.const 1)).pow e)).add hpostT).add hcsS
  obtain ⟨D, f, hDf⟩ := hW.exists_le
  refine ⟨(fun x => decide (0 < count x)), cs, D, f, A,
    fun x => (Nat.le_add_left _ _).trans (hDf x), ?_⟩
  intro n B P hb hp
  obtain ⟨hc, ht⟩ := h B P hb hp
  constructor
  · simp only [hc, decide_eq_true_eq]
    simp only [Fintype.card_pos_iff, nonempty_subtype]
  · let E := 2 ^ (A * Nat.logLogSqrtLogScale (n + P.length))
    have hE : 0 < E := Nat.two_pow_pos _
    change cp.time (ofFinite B P) + post.time (count (ofFinite B P)) ≤ _
    calc
      _ ≤ (C * ((encInput (ofFinite B P)).length + 1) ^ e +
          post.time (count (ofFinite B P))) * E := by
        rw [Nat.add_mul]
        exact Nat.add_le_add ht (Nat.le_mul_of_pos_right _ hE)
      _ ≤ W (ofFinite B P) * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hDf _)


private theorem units_polytime : ComputableInPolyTime units encBits VCOne.encSignedCNF := by
  have hj := ComputableInPolyTime.snd encBits encUnary
  have hb := ComputableInPolyTime.bitsGetDWithInput
    (ComputableInPolyTime.fst encBits encUnary) hj false
  have hi := ComputableInPolyTime.unary_to_binary.comp hj
  have hc : ComputableInPolyTime (fun p : List Bool × ℕ => [(p.2, p.1.getD p.2 false)])
      (encPair encBits encUnary) (encList (encPair encNat encBool)) := by fun_prop
  unfold units VCOne.encSignedCNF
  exact ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp ComputableInPolyTime.length_bits) hc

private theorem fix_polytime : ComputableInPolyTime fix encState encInput := by
  have hu := units_polytime.comp (show ComputableInPolyTime fixedBits encState encBits from by
    unfold fixedBits encState; fun_prop)
  unfold fix original declared side conditions encState encInput
  fun_prop

private theorem advance_polytime (b : Bool) : ComputableInPolyTime (advance b) encState
    encState := by
  have hs : ComputableInPolyTime fixedBits encState encBits := by
    unfold fixedBits encState; fun_prop
  have ha := ComputableInPolyTime.bitsAppend hs (ComputableInPolyTime.const [b])
  unfold advance original encState
  fun_prop

private theorem query_polytime : ComputableInPolyTime query encState encInput := by
  have ho : ComputableInPolyTime original encState encInput := by
    unfold original encState; fun_prop
  have hn : ComputableInPolyTime (fun s => declared (original s)) encState encUnary := by
    unfold original declared encState encInput; fun_prop
  have hb : ComputableInPolyTime fixedBits encState encBits := by
    unfold fixedBits encState; fun_prop
  have ht := ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsAppend hb (ComputableInPolyTime.const [false])) hn
  exact fix_polytime.comp (ho.prod ht)

private theorem initial_polytime : ComputableInPolyTime initial encInput encState := by
  unfold initial encState; fun_prop

private theorem rounds_polytime : ComputableInPolyTime declared encInput encNat :=
  ComputableInPolyTime.unary_to_binary.comp (by unfold encInput; fun_prop)

private theorem output_polytime : ComputableInPolyTime fixedBits encState encBits := by
  unfold fixedBits encState; fun_prop

private theorem declared_le_length (x : Input) : declared x ≤ (encInput x).length := by
  rcases x with ⟨n, B, P⟩
  simp only [declared, encInput, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem trajectory_length (test : Input → Bool) (x : Input) {j : ℕ}
    (hj : j ≤ declared x) : (encState ((step test)^[j] (initial x))).length ≤
      4 * ((encInput x).length + 1) := by
  have ho := (trajectory test x j).1
  have hl := (trajectory test x j).2
  have h := declared_le_length x
  simp only [encState, length_encPair, encBits_apply]
  change 2 * (encInput (original ((step test)^[j] (initial x)))).length + 1 +
    (fixedBits ((step test)^[j] (initial x))).length ≤ _
  rw [ho, hl]
  omega

private theorem fixed_width {n b : ℕ} (B : CNF (Fin n)) (p : List Bool) (h : p.length ≤ n)
    (hb : ∀ c ∈ B, c.length ≤ b) (hb0 : 1 ≤ b) :
    ∀ c ∈ B ++ finiteUnits p h, c.length ≤ b := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hb c hc
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    simpa using hb0

open Classical in
/-- Actual declared-word recovery by at most one sharp feasibility call per declared wire.
The complete native certificate charges unit writing, every loop prefix and final output. -/
theorem exists_recovery_sharp_certificate (b d : ℕ) (hb0 : 1 ≤ b) :
    ∃ recover : Input → List Bool, ∃ cs : NativeCertificate recover encInput encBits,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
        (_hb : ∀ c ∈ B, c.length ≤ b) (_hp : ∀ q ∈ P, ∀ t ∈ q, t.length ≤ d),
        ((∃ σ : Fin n → Bool, B.eval σ = true ∧ ∀ q ∈ P, DNF.eval σ q = true) →
          let bits := recover (ofFinite B P)
          bits.length = n ∧ B.eval (fun i => bits.getD i.val false) = true ∧
            ∀ q ∈ P, DNF.eval (fun i => bits.getD i.val false) q = true) ∧
        cs.time (ofFinite B P) ≤ C * ((encInput (ofFinite B P)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by
  obtain ⟨test, cp, D, f, A, hs, ht⟩ := exists_test_sharp_certificate b d
  let cq := NativeCertificate.ofPolyTime query_polytime
  let cy := NativeCertificate.ofPolyTime (advance_polytime false)
  let cz := NativeCertificate.ofPolyTime (advance_polytime true)
  let ct := cp.comp cq
  let cb : NativeCertificate (step test) encState encState :=
    (NativeCertificate.branch ct cy cz).congr fun _ => rfl
  have hq := NativeCertificate.ofPolyTime_isPolynomial query_polytime
  have hy := NativeCertificate.ofPolyTime_isPolynomial (advance_polytime false)
  have hz := NativeCertificate.ofPolyTime_isPolynomial (advance_polytime true)
  have hctS := SparseCNFLeafCounter.polyBounded_comp_space cp cq
    (PolyBounded.of_forall_le D f hs) hq.2
  have hcbS : PolyBounded (fun s => (encState s).length) cb.space :=
    ((hctS.add hy.2).add hz.2).mono fun s => by
      change ct.space s + (if test (query s) then cy.space s else cz.space s) ≤
        ct.space s + cy.space s + cz.space s
      split_ifs <;> omega
  let H (s : State) := cq.time s + cy.time s + cz.time s +
    D * ((encInput (query s)).length + 1) ^ f
  have hH : PolyBounded (fun s => (encState s).length) H :=
    ((hq.1.add hy.1).add hz.1).add ((PolyBounded.const D).mul
      ((query_polytime.polyBounded_length.add (.const 1)).pow f))
  obtain ⟨cR, eR, hR⟩ := hH.exists_le
  obtain ⟨cS, eS, hS⟩ := hcbS.exists_le
  let Bound (g : Input) := 4 * ((encInput g).length + 1)
  let R (g : Input) := cR * (Bound g + 1) ^ eR
  let Q (g : Input) := cS * (Bound g + 1) ^ eS
  have hB : PolyBounded (fun g => (encInput g).length) Bound :=
    (PolyBounded.const 4).mul (PolyBounded.self.add (.const 1))
  have hRP : PolyBounded (fun g => (encInput g).length) R :=
    (PolyBounded.const cR).mul ((hB.add (.const 1)).pow eR)
  have hQP : PolyBounded (fun g => (encInput g).length) Q :=
    (PolyBounded.const cS).mul ((hB.add (.const 1)).pow eS)
  let cn := NativeCertificate.ofPolyTime rounds_polytime
  let ci := NativeCertificate.ofPolyTime initial_polytime
  let loop := NativeCertificate.iterate cn ci cb
  have hn := NativeCertificate.ofPolyTime_isPolynomial rounds_polytime
  have hi := NativeCertificate.ofPolyTime_isPolynomial initial_polytime
  have hN : PolyBounded (fun g => (encInput g).length) declared :=
    PolyBounded.of_forall_le 1 1 fun g => by
      have := declared_le_length g
      simp only [pow_one, one_mul]; omega
  have hLN := rounds_polytime.polyBounded_length
  have hmaxB (g : Input) :
      NativeCertificate.maxStateLength encState (step test) (declared g) (initial g) ≤ Bound g :=
    NativeCertificate.maxStateLength_le _ _ _ _ fun j hj => trajectory_length test g hj
  have hmaxQ (g : Input) :
      NativeCertificate.maxRoundSpace cb (declared g) (initial g) ≤ Q g :=
    NativeCertificate.maxRoundSpace_le _ _ _ fun j hj =>
      (hS _).trans (Nat.mul_le_mul_left cS
        (Nat.pow_le_pow_left (Nat.add_le_add_right (trajectory_length test g hj) 1) eS))
  have hloopS : PolyBounded (fun g => (encInput g).length) loop.space :=
    ((((hn.2.add hi.2).add hQP).add hB).add hLN).mono fun g => by
      change cn.space g + ci.space g +
        NativeCertificate.maxRoundSpace cb (declared g) (initial g) +
        NativeCertificate.maxStateLength encState (step test) (declared g) (initial g) +
        (encNat (declared g)).length ≤
          cn.space g + ci.space g + Q g + Bound g + (encNat (declared g)).length
      have := hmaxQ g
      have := hmaxB g
      omega
  have hfinalL : PolyBounded (fun g => (encInput g).length)
      (fun g => (encState ((step test)^[declared g] (initial g))).length) :=
    hB.mono fun g => trajectory_length test g (Nat.le_refl _)
  let post := NativeCertificate.ofPolyTime output_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial output_polytime
  have hpostT := hp.1.comp hfinalL
  have hpostS := hp.2.comp hfinalL
  let cs : NativeCertificate (run test) encInput encBits :=
    (post.comp loop).congr fun _ => rfl
  have hcsS : PolyBounded (fun g => (encInput g).length) cs.space :=
    hloopS.add hpostS
  let W (g : Input) := cn.time g + ci.time g +
    (declared g + 1) * (R g + Bound g + ((encNat (declared g)).length + 1) ^ 2) +
    post.time ((step test)^[declared g] (initial g)) + cs.space g
  have hW : PolyBounded (fun g => (encInput g).length) W :=
    (((hn.1.add hi.1).add ((hN.add (.const 1)).mul
      ((hRP.add hB).add ((hLN.add (.const 1)).pow 2)))).add hpostT).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨run test, cs, C, e, A, fun g => (Nat.le_add_left _ _).trans (hCe g), ?_⟩
  intro n B P hb hp
  refine ⟨?_, ?_⟩
  · apply run_recovers test B P
    intro p hlen
    rw [fix_ofFinite B P p hlen]
    have hc := (ht (B ++ finiteUnits p hlen) P (fixed_width B p hlen hb hb0) hp).1
    simpa only [CNF.eval_append, Bool.and_eq_true, finiteUnits_eval, Admits,
      and_assoc, and_left_comm, and_comm] using hc
  let g := ofFinite B P
  let E := 2 ^ (A * Nat.logLogSqrtLogScale (n + P.length))
  have hE : 0 < E := Nat.two_pow_pos _
  have hmaxT : NativeCertificate.maxRoundTime cb (declared g) (initial g) ≤ R g * E := by
    apply NativeCertificate.maxRoundTime_le
    intro j hj
    let s := (step test)^[j] (initial g)
    have hg : original s = g := (trajectory test g j).1
    let p := (fixedBits s ++ [false]).take n
    have hl : p.length ≤ n := List.length_take_le _ _
    have hquery : query s = ofFinite (B ++ finiteUnits p hl) P := by
      unfold query
      rw [hg]
      exact fix_ofFinite B P _ hl
    have htime := (ht (B ++ finiteUnits p hl) P (fixed_width B p hl hb hb0) hp).2
    rw [← hquery] at htime
    change cp.time (query s) ≤ D * ((encInput (query s)).length + 1) ^ f * E at htime
    have hlocal : cb.time s ≤ H s * E := by
      change cq.time s + cp.time (query s) +
        (if test (query s) then cy.time s else cz.time s) ≤ _
      have hsmall : cq.time s + (if test (query s) then cy.time s else cz.time s) ≤
          cq.time s + cy.time s + cz.time s := by split_ifs <;> omega
      have hm := Nat.le_mul_of_pos_right (cq.time s + cy.time s + cz.time s) hE
      have hh := Nat.add_le_add hm htime
      dsimp only [H]
      rw [Nat.add_mul]
      omega
    exact hlocal.trans (Nat.mul_le_mul_right E ((hR s).trans
      (Nat.mul_le_mul_left cR (Nat.pow_le_pow_left
        (Nat.add_le_add_right (trajectory_length test g hj) 1) eR))))
  change cn.time g + ci.time g + (declared g + 1) *
    (NativeCertificate.maxRoundTime cb (declared g) (initial g) +
      NativeCertificate.maxStateLength encState (step test) (declared g) (initial g) +
      ((encNat (declared g)).length + 1) ^ 2) +
    post.time ((step test)^[declared g] (initial g)) ≤ _
  have hmb := hmaxB g
  have ht0 := Nat.le_mul_of_pos_right
    (cn.time g + ci.time g + post.time ((step test)^[declared g] (initial g))) hE
  have ht1 := Nat.le_mul_of_pos_right
    (Bound g + ((encNat (declared g)).length + 1) ^ 2) hE
  have ht2 := Nat.mul_le_mul_left (declared g + 1) (Nat.add_le_add hmaxT ht1)
  have hfinal : cs.time g ≤ W g * E := by
    change cn.time g + ci.time g + (declared g + 1) *
      (NativeCertificate.maxRoundTime cb (declared g) (initial g) +
        NativeCertificate.maxStateLength encState (step test) (declared g) (initial g) +
        ((encNat (declared g)).length + 1) ^ 2) +
      post.time ((step test)^[declared g] (initial g)) ≤ _
    have hm := Nat.mul_le_mul_left (declared g + 1) (Nat.add_le_add_right
      (Nat.add_le_add_left hmb (NativeCertificate.maxRoundTime cb (declared g) (initial g)))
      (((encNat (declared g)).length + 1) ^ 2))
    dsimp only [W]
    nlinarith
  exact hfinal.trans (Nat.mul_le_mul_right E (hCe g))

end Cslib.Logic.PL.TwoBoundary.BinaryFrontend.Witness
