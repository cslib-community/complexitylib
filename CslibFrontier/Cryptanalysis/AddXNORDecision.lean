/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORChain
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Polynomial-time verification of Add/XNOR

The NP-membership part of [WangLvShenZhang2027], Theorem 1 (PDF p. 9).
Instances contain a unary word width and a framed list of binary natural
operands. The balanced language checks that the list length is the width,
that the width is at least two, and that all operands fit. The independent
two-parameter language allows width one and requires at least two operands. Leading zeroes
are implicit. The semantic predicate uses actual `BitVec` operations.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

open Turing.MultiTapeTM Cslib.Complexity

/-- Unary width followed by the framed binary operands. -/
@[expose] def encInstance : ℕ × List ℕ ↪ List Bool := encPair encUnary (encList encNat)

/-- One natural-number implementation of modular addition or width-limited XNOR. -/
@[expose] def natStep (m : ℕ) (s : ℕ) (op : Bool × ℕ) : ℕ :=
  let (b, a) := op
  if b then 2 ^ m - 1 - (s ^^^ a) else (s + a) % 2 ^ m

/-- Execute the selected operators on binary operands. -/
@[expose] def natEval (m : ℕ) (xs : List (Bool × ℕ)) (s : ℕ) : ℕ :=
  xs.foldl (natStep m) s

/-- The implementation agrees with actual full-width words on fitting inputs. -/
theorem natStep_toNat {m : ℕ} (b : Bool) (s a : BitVec m) :
    natStep m s.toNat (b, a.toNat) = (step b s a).toNat := by
  cases b <;> simp [natStep, step, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_xor]

/-- Execution agrees with actual word evaluation for every operator word. -/
theorem natEval_toNat {m : ℕ} (xs : List (Bool × BitVec m)) (s : BitVec m) :
    natEval m (xs.map fun (b, a) => (b, a.toNat)) s.toNat = (eval xs s).toNat := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b, a⟩
    simp only [natEval, List.map_cons, List.foldl_cons, natStep_toNat, eval] at *
    exact ih (step b s a)

/-- Every step's result fits the width, even on malformed natural inputs. -/
theorem natStep_lt (m s : ℕ) (op : Bool × ℕ) : natStep m s op < 2 ^ m := by
  rcases op with ⟨b, a⟩
  unfold natStep
  dsimp only
  split
  · have := Nat.two_pow_pos m
    omega
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Joint polynomial-time computation of one natural-number step. -/
@[fun_prop] theorem natStep_polyTime :
    ComputableInPolyTime (fun (((m, s), op) : (ℕ × ℕ) × (Bool × ℕ)) => natStep m s op)
      (encPair (encPair encUnary encNat) (encPair encBool encNat)) encNat := by
  let input := encPair (encPair encUnary encNat) (encPair encBool encNat)
  have hm : ComputableInPolyTime (fun p : (ℕ × ℕ) × (Bool × ℕ) => p.1.1) input encUnary := by
    fun_prop
  have hs : ComputableInPolyTime (fun p : (ℕ × ℕ) × (Bool × ℕ) => p.1.2) input encNat := by
    fun_prop
  have ha : ComputableInPolyTime (fun p : (ℕ × ℕ) × (Bool × ℕ) => p.2.2) input encNat := by
    fun_prop
  have hb : ComputableInPolyTime (fun p : (ℕ × ℕ) × (Bool × ℕ) => p.2.1) input encBool := by
    fun_prop
  have hp : ComputableInPolyTime (fun p : (ℕ × ℕ) × (Bool × ℕ) => 2 ^ p.1.1) input encNat := by
    fun_prop
  have hxor := ComputableInPolyTime.binary_xor' hs ha
  have hsub := ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.binary_sub' hp (.const 1)) hxor
  have hadd := ComputableInPolyTime.binary_add.comp (hs.prod ha)
  exact hb.ite hsub (ComputableInPolyTime.binary_mod.comp (hadd.prod hp))

/-- A whole chain is polynomial-time. The fold state has at most `m` binary
bits after every step; the captured width is unary. -/
@[fun_prop] theorem natEval_polyTime :
    ComputableInPolyTime (fun (((m, s), xs) : (ℕ × ℕ) × List (Bool × ℕ)) => natEval m xs s)
      (encPair (encPair encUnary encNat) (encList (encPair encBool encNat))) encNat := by
  apply ComputableInPolyTime.of_tidy
  unfold natEval
  apply ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (encP := encUnary) (encA := encPair encBool encNat) (encL := encList (encPair encBool encNat))
    (show ComputableInPolyTime (fun p : (ℕ × ℕ) × List (Bool × ℕ) => p.1.1) _ encUnary
      by fun_prop).tidy
    (show ComputableInPolyTime (fun p : (ℕ × ℕ) × List (Bool × ℕ) => p.2) _
      (encList (encPair encBool encNat)) by fun_prop).tidy
    (show ComputableInPolyTime (fun p : (ℕ × ℕ) × List (Bool × ℕ) => p.1.2) _ encNat
      by fun_prop).tidy
    natStep_polyTime.tidy
    (growth := fun p => p.1.1)
  · have h := (show ComputableInPolyTime
        (fun p : (ℕ × ℕ) × List (Bool × ℕ) => p.1.1)
        (encPair (encPair encUnary encNat) (encList (encPair encBool encNat)))
          encUnary by fun_prop).polyBounded_length
    simpa using h
  · intro p state value _
    have hsize := Nat.size_le.2 (natStep_lt p.1.1 state value)
    change (natStep p.1.1 state value).bits.length ≤ state.bits.length + p.1.1
    rw [Nat.size_eq_bits_len]
    omega

/-- Balanced, fitting Add/XNOR instances with unrestricted operators. -/
@[expose] def Decision : Set (ℕ × List ℕ) := {p |
  2 ≤ p.1 ∧ p.2.length = p.1 ∧ (∀ a ∈ p.2, a < 2 ^ p.1) ∧
    Solvable (p.2.tail.map (BitVec.ofNat p.1)) (BitVec.ofNat p.1 (p.2.headD 0)) 0}

private theorem natEval_zip {m : ℕ} (bs : List Bool) (as : List ℕ)
    (hfit : ∀ a ∈ as, a < 2 ^ m) (s : BitVec m) :
    natEval m (bs.zip as) s.toNat =
      (eval (bs.zip (as.map (BitVec.ofNat m))) s).toNat := by
  induction bs generalizing as s with
  | nil => rfl
  | cons b bs ih =>
    cases as with
    | nil => rfl
    | cons a as =>
      have ha : (BitVec.ofNat m a).toNat = a := Nat.mod_eq_of_lt (hfit a (by simp))
      have ht : ∀ a ∈ as, a < 2 ^ m := fun a ha => hfit a (by simp [ha])
      simp only [List.zip_cons_cons, List.map_cons, natEval, List.foldl_cons, eval] at *
      conv_lhs => rw [← ha, natStep_toNat]
      exact ih as ht (step b s (BitVec.ofNat m a))

/-- The two-parameter problem, with the number of operands independent of width. -/
@[expose] def WordDecision : Set (ℕ × List ℕ) := {p |
  1 ≤ p.1 ∧ 2 ≤ p.2.length ∧ (∀ a ∈ p.2, a < 2 ^ p.1) ∧
    Solvable (p.2.tail.map (BitVec.ofNat p.1)) (BitVec.ofNat p.1 (p.2.headD 0)) 0}

/-- Check the instance shape, range, and the actual chain selected by the
certificate. Extra certificate bits past the operand list are ignored. -/
@[expose] def wordVerifier (p : (ℕ × List ℕ) × List Bool) : Bool :=
  let ((m, as), bs) := p
  decide (1 ≤ m) && decide (2 ≤ as.length) &&
    as.all (fun a => decide (a < 2 ^ m)) &&
    decide (natEval m (bs.zip as.tail) (as.headD 0) = 0)

private theorem evaluator_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × List Bool =>
      natEval p.1.1 (p.2.zip p.1.2.tail) (p.1.2.headD 0))
      (encPair encInstance encBits) encNat := by
  have hinst := ComputableInPolyTime.fst encInstance encBits
  have hlist := (ComputableInPolyTime.snd encUnary (encList encNat)).comp hinst
  have hwidth := (ComputableInPolyTime.fst encUnary (encList encNat)).comp hinst
  have hbits := (bits_encList_polyTime encBool).1.comp
    (ComputableInPolyTime.snd encInstance encBits)
  have htail := (ComputableInPolyTime.tail (encA := encNat) (encL := encList encNat)).comp hlist
  have hz := (ComputableInPolyTime.zip encBool encNat).comp (hbits.prod htail)
  have hhead := (ComputableInPolyTime.headD (encA := encNat) (encL := encList encNat) 0).comp hlist
  have harg : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × List Bool => ((p.1.1, p.1.2.headD 0), p.2.zip p.1.2.tail))
      (encPair encInstance encBits)
      (encPair (encPair encUnary encNat) (encList (encPair encBool encNat))) :=
    (hwidth.prod hhead).prod hz
  have h := natEval_polyTime.comp harg
  dsimp only [Function.comp_def] at h
  exact h

private theorem verifier_zero_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × List Bool => decide
      (natEval p.1.1 (p.2.zip p.1.2.tail) (p.1.2.headD 0) = 0))
      (encPair encInstance encBits) encBool :=
  .of_tidy (ComputableTidilyInPolyTime.decide_eq' evaluator_polyTime.tidy (.const 0))

/-- Polynomial-time verifier, using the certified fold rather than assuming
that a machine implements the word recurrence. -/
@[fun_prop] theorem wordVerifier_polyTime :
    ComputableInPolyTime wordVerifier (encPair encInstance encBits) encBool := by
  have hwidth : ComputableInPolyTime (fun p : (ℕ × List ℕ) × List Bool => p.1.1)
      (encPair encInstance encBits) encUnary := by fun_prop
  have hlist : ComputableInPolyTime (fun p : (ℕ × List ℕ) × List Bool => p.1.2)
      (encPair encInstance encBits) (encList encNat) := by fun_prop
  have hshape₁ : ComputableInPolyTime (fun p : (ℕ × List ℕ) × List Bool => decide (1 ≤ p.1.1))
      (encPair encInstance encBits) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.unary_le' (.const 1) hwidth.tidy)
  have hfits : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × List Bool => p.1.2.all (fun a => decide (a < 2 ^ p.1.1)))
      (encPair encInstance encBits) encBool := by
    apply ComputableInPolyTime.allWithInput hlist
    have hp : ComputableInPolyTime
        (fun p : ((ℕ × List ℕ) × List Bool) × ℕ => 2 ^ p.1.1.1)
        (encPair (encPair encInstance encBits) encNat) encNat := by fun_prop
    exact ComputableInPolyTime.binary_lt' (by fun_prop) hp
  have hlen := (ComputableTidilyInPolyTime.length encNat).comp hlist.tidy
  have hcount := ComputableTidilyInPolyTime.unary_le' (.const 2) hlen
  exact .of_tidy (ComputableTidilyInPolyTime.bool_and'
    (ComputableTidilyInPolyTime.bool_and'
      (ComputableTidilyInPolyTime.bool_and' hshape₁.tidy hcount) hfits.tidy)
        verifier_zero_polyTime.tidy)


private theorem zip_take_length {α β : Type} (as : List α) (bs : List β) :
    (as.take bs.length).zip bs = as.zip bs := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    cases bs with
    | nil => simp
    | cons b bs => simp [ih]

private theorem zip_padding {α : Type} (bs : List Bool) (as : List α)
    (hlen : bs.length = as.length) (k : ℕ) :
    (bs ++ List.replicate k false).zip as = bs.zip as := by
  have h : bs.zip as ++ (List.replicate k false).zip [] =
      (bs ++ List.replicate k false).zip (as ++ []) := (List.zip_append hlen).symm
  simpa using h.symm

/-- The verifier characterizes the semantic language with certificates of the
encoded instance length. The certificate bound counts every free operator. -/
theorem wordVerifier_isVerifier : IsVerifier encInstance Polynomial.X wordVerifier WordDecision :=
  by
  apply IsVerifier.of_padding
  · rintro ⟨m, as⟩ w hw hV
    simp only [wordVerifier, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hV
    obtain ⟨⟨⟨hm, hcount⟩, hfit⟩, he⟩ := hV
    have hhead : as.headD 0 < 2 ^ m := by
      cases as with
      | nil => simp
      | cons a as => exact hfit a (by simp)
    have htail : ∀ a ∈ as.tail, a < 2 ^ m := fun a ha => hfit a (List.mem_of_mem_tail ha)
    have heq := natEval_zip w as.tail htail (BitVec.ofNat m (as.headD 0))
    rw [show (BitVec.ofNat m (as.headD 0)).toNat = as.headD 0 from Nat.mod_eq_of_lt hhead
      , he] at heq
    refine ⟨hm, hcount, hfit, w.take as.tail.length, ?_, ?_⟩
    · have hbound : as.length ≤ (encInstance (m, as)).length := by
        have := length_le_length_encList encNat as
        simp only [encInstance, length_encPair]
        omega
      simp only [Polynomial.eval_X] at hw
      simp only [List.length_take, List.length_map, List.length_tail]
      omega
    · have hzip : (w.take as.tail.length).zip (as.tail.map (BitVec.ofNat m)) =
          w.zip (as.tail.map (BitVec.ofNat m)) := by
        have h := zip_take_length w (as.tail.map (BitVec.ofNat m))
        simpa only [List.length_map] using h
      rw [hzip]
      exact BitVec.eq_of_toNat_eq heq.symm
  · rintro ⟨m, as⟩ ⟨hm, hcount, hfit, bs, hbs, he⟩
    refine ⟨bs, ?_, fun k => ?_⟩
    · have := length_le_length_encList encNat as
      simp only [encInstance, length_encPair, Polynomial.eval_X, List.length_map] at *
      simp only [List.length_tail] at hbs
      omega
    · have hhead : as.headD 0 < 2 ^ m := by
        cases as with
        | nil => simp
        | cons a as => exact hfit a (by simp)
      have htail : ∀ a ∈ as.tail, a < 2 ^ m := fun a ha => hfit a (List.mem_of_mem_tail ha)
      have heq := natEval_zip bs as.tail htail (BitVec.ofNat m (as.headD 0))
      rw [show (BitVec.ofNat m (as.headD 0)).toNat = as.headD 0 from Nat.mod_eq_of_lt hhead
        , he] at heq
      have hz : natEval m (bs.zip as.tail) (as.headD 0) = 0 := heq
      simp only [List.length_map] at hbs
      simp only [wordVerifier, decide_eq_true hm, decide_eq_true hcount, Bool.true_and,
        List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true, zip_padding bs as.tail hbs k]
      exact ⟨hfit, hz⟩

/-- The unrestricted two-parameter language belongs to NP. -/
theorem WordDecision_mem_NP : WordDecision ∈ NP encInstance :=
  ⟨Polynomial.X, wordVerifier, wordVerifier_polyTime, wordVerifier_isVerifier⟩

/-- The balanced verifier adds the operand-count check to the common verifier. -/
@[expose] def verifier (p : (ℕ × List ℕ) × List Bool) : Bool :=
  let ((m, as), _) := p
  decide (as.length = m) && wordVerifier p

/-- The balanced verifier is polynomial-time. -/
@[fun_prop] theorem verifier_polyTime :
    ComputableInPolyTime verifier (encPair encInstance encBits) encBool := by
  have hwidth : ComputableInPolyTime (fun p : (ℕ × List ℕ) × List Bool => p.1.1)
      (encPair encInstance encBits) encUnary := by fun_prop
  have hlist : ComputableInPolyTime (fun p : (ℕ × List ℕ) × List Bool => p.1.2)
      (encPair encInstance encBits) (encList encNat) := by fun_prop
  have hlen := (ComputableTidilyInPolyTime.length encNat).comp hlist.tidy
  exact .of_tidy (ComputableTidilyInPolyTime.bool_and'
    (ComputableTidilyInPolyTime.decide_eq' hlen hwidth.tidy) wordVerifier_polyTime.tidy)

/-- The balanced guard preserves the semantic verifier characterization. -/
theorem verifier_isVerifier : IsVerifier encInstance Polynomial.X verifier Decision := by
  have h := wordVerifier_isVerifier.guard (c := fun p => decide (p.2.length = p.1))
  have he : {p : ℕ × List ℕ | decide (p.2.length = p.1) = true ∧ p ∈ WordDecision} = Decision := by
    ext p
    simp only [WordDecision, Decision, Set.mem_ofPred_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨hlen, hm, hcount, hfit, hs⟩
      exact ⟨by omega, hlen, hfit, hs⟩
    · rintro ⟨hm, hlen, hfit, hs⟩
      exact ⟨hlen, by omega, by omega, hfit, hs⟩
  rw [he] at h
  exact h

/-- The balanced Add/XNOR decision language belongs to NP. -/
theorem Decision_mem_NP : Decision ∈ NP encInstance :=
  ⟨Polynomial.X, verifier, verifier_polyTime, verifier_isVerifier⟩

end Cslib.Cryptanalysis.AddXNOR
