/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Loop
public import Complexity.Logics.FirstOrder.Ordered.TransitiveClosure
public import Complexity.Computability.Complexity.Classes.LogSpace
import Complexity.Foundations.Data.List.Lookup

/-!
# FO(positive TC) model checking in nondeterministic logarithmic space

For each fixed sentence of FO(TC) over a finite relational vocabulary expanded by the canonical
numeric symbols, whose closures all occur positively, the encoded query language belongs to the
native class `NL`. The input uses `encStructure`, as for ordered first-order model checking in
`L`; malformed table shapes and cardinalities below two are rejected.

The decider is one nondeterministic counter program: it validates the input tables, rejects
cardinalities below two, and runs the compiled code of the sentence at polarity `true`. Every
branch halts with every register at most `(N + 1) ^ (d + w)` for input length `N`, maximal input
arity `d` and closure width `w`, so the program runs in logarithmic space.

This is the inclusion of FO(positive TC) in NL from [Immerman1987], Theorem 3.1, proved by
evaluating closures with bounded guessed paths. Closures under negation and the converse
inclusion remain open.

## Main definitions

* `Cslib.Logic.FO.Ordered.TCModelChecker.decider`: the nondeterministic decider.

## Main results

* `Cslib.Logic.FO.Ordered.TCModelChecker.correct`: compiler correctness for every formula.
* `Cslib.Logic.FO.Ordered.TCModelChecker.encodedLanguage_mem_NL`: a query defined by a sentence
  with positive closures is in native `NL`.
* `Cslib.Logic.FO.Ordered.PosTCDefinable.encodedLanguage_mem_NL`: FO(positive TC) ⊆ NL on
  canonically ordered structures.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 3.1][Immerman1987]
-/

public section

universe u v w

open FirstOrder Language
namespace Cslib.Logic.FO.Ordered.TCModelChecker

open Turing Turing.CounterProgram Turing.CounterProgram.Block Expr Vocabulary.ModelChecker
open Operator (Formula RelEnv)

variable {L : Language.{u, v}} [L.IsRelational] {v : Vocabulary L}

section Correct

variable {a : EncodedStructure} [L.Structure (Fin a.1)] [Fact (2 ≤ a.1)]
  {P : CounterProgram} {B : ℕ} {Post : Config → Prop} {R : ℕ}

theorem correct_op (hE : Env v a P B Post R) {Γ : List ℕ} {α : Type} (k : ℕ)
    (body : (i : Fin (TC.shape k).slots) → Formula (language L) TC.shape
      (((TC.shape k).binder i).relations ++ Γ) (α ⊕ Fin ((TC.shape k).binder i).vars))
    (args : Fin (TC.shape k).arity → (language L).Term α)
    (ih : Correct v a P B Post R (body ⟨0, Nat.one_pos⟩)) :
    Correct v a P B Post R (Formula.op k body args) := by
  intro hΓ s hpos hW fv base val ρ b T regs hP hbase hfv hd h0 hv hregs
  cases s with
  | false => exact absurd hpos.1 Bool.false_ne_true
  | true =>
  have hn : 0 < a.1 := by have := (Fact.out : 2 ≤ a.1); omega
  have hNB : a.1 ^ k ≤ B := (Nat.pow_le_pow_right hn (le_max_left _ _)).trans hW
  have hWb : a.1 ^ TC.width (body ⟨0, Nat.one_pos⟩) ≤ B :=
    (Nat.pow_le_pow_right hn (le_max_right _ _)).trans hW
  have hdb : base + 2 * k + 2 + scratch (body ⟨0, Nat.one_pos⟩) ≤ regs.length := by
    have : scratch (Formula.op (L := language L) (shape := TC.shape) (Γ := Γ) k body args) =
      2 * k + 2 + scratch (body ⟨0, Nat.one_pos⟩) := rfl
    omega
  -- the endpoint tuples and the edge relation
  let s₀ : Fin k → Fin a.1 := fun i => (TC.left args i).realize val
  let z₀ : Fin k → Fin a.1 := fun i => (TC.right args i).realize val
  let E : (Fin k → Fin a.1) → (Fin k → Fin a.1) → Prop := fun us ws =>
    (body ⟨0, Nat.one_pos⟩).Realize TC.interpretation (RelEnv.empty.append ρ)
      (Sum.elim val (TC.pair us ws))
  have hreal : (Formula.op k body args).Realize TC.interpretation ρ val ↔
      Relation.ReflTransGen E s₀ z₀ := Iff.rfl
  have hsrc : ∀ regs' : List ℕ, (∀ j < base, regs'.getD j 0 = regs.getD j 0) →
      ∀ i, (termE fv (TC.left args i)).eval regs' = s₀ i := fun regs' h i =>
    eval_termE hE fv val ((h 0 hbase).trans h0) (fun x => (h _ (hfv x)).trans (hv x)) _
  have hdst : ∀ regs' : List ℕ, (∀ j < base, regs'.getD j 0 = regs.getD j 0) →
      ∀ i, (termE fv (TC.right args i)).eval regs' = z₀ i := fun regs' h i =>
    eval_termE hE fv val ((h 0 hbase).trans h0) (fun x => (h _ (hfv x)).trans (hv x)) _
  -- the body block
  let code := compile v (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
    (Sum.elim fv fun i => base + i.val) (base + 2 * k + 2) (body ⟨0, Nat.one_pos⟩) true
    (b + 2 * k + 7) (b + 2 * k + 7 + len (body ⟨0, Nat.one_pos⟩) true) R
  have hP' : P.CodeAt b (tcCode b base k (fun i => termE fv (TC.left args i))
      (fun i => termE fv (TC.right args i)) code T R) := hP
  have hcl : code.length = len (body ⟨0, Nat.one_pos⟩) true := length_compile ..
  have hbody : ∀ us ws t regs₃, LoopMid a.1 B base k regs us ws t regs₃ →
      Sound P (encStructure a) B Post (b + 2 * k + 7) regs₃ (b + 2 * k + 7 + code.length)
        (fun regs' => Kept B (base + 2 * k + 2) regs₃ regs' ∧ E us ws) ∧
      (E us ws → Complete P (encStructure a) (b + 2 * k + 7) regs₃
        (b + 2 * k + 7 + code.length) (Kept B (base + 2 * k + 2) regs₃)) := by
    intro us ws t regs₃ hmid
    obtain ⟨⟨hk, hlen, hu, -⟩, hw⟩ := hmid
    rw [hcl]
    exact ih (by rw [hΓ]; rfl) true hpos.2 hWb _ _ (Sum.elim val (TC.pair us ws))
      (RelEnv.empty.append ρ) _ _ regs₃ (tcCode_parts hP').2.2.2.2.2.2.1 (by omega)
      (fun x => by
        cases x with
        | inl x => have := hfv x; simp only [Sum.elim_inl]; omega
        | inr i => have : (i : ℕ) < 2 * k := i.isLt; simp only [Sum.elim_inr]; omega)
      (by rw [hk.1]; omega) ((hk.2.1 0 hbase).trans h0)
      (fun x => by
        cases x with
        | inl x => simp only [Sum.elim_inl]; exact (hk.2.1 _ (hfv x)).trans (hv x)
        | inr i => exact getD_pair hu hw i)
      hk.2.2
  obtain ⟨regsI, hrI, hinvI⟩ := loop_init (w := encStructure a) hP' (by omega)
    hE.card_le hregs hsrc
  refine ⟨Sound.of_oblivious hE.one_le hrI ?_, fun hsat => Complete.of_oblivious hrI ?_⟩
  · refine (loop_sound (s₀ := s₀) hP' hbase hE.one_le hE.card_le hNB h0 hE.halts hE.post hdst
      (fun us ws t regs₃ hmid => (hbody us ws t regs₃ hmid).1) _ 0 s₀ regsI rfl hinvI
      Relation.ReflTransGen.refl).mono fun regs' h => ⟨h.1, h.2⟩
  · have hcard : Nat.card (Fin k → Fin a.1) ≤ a.1 ^ k - 1 + 1 := by
      have : 0 < a.1 ^ k := pow_pos hn k
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      omega
    obtain ⟨m, hm, hsteps⟩ := (Relation.reflTransGen_iff_relatesWithinSteps hcard).mp hsat
    have : 0 < a.1 ^ k := pow_pos hn k
    exact loop_complete hP' hbase hE.card_le hNB h0 hdst
      (fun us ws t regs₃ hmid => (hbody us ws t regs₃ hmid).2) m 0 s₀ regsI hsteps (by omega)
      hinvI

/-- **Compiler correctness** for every formula without free relation variables. -/
theorem correct (hE : Env v a P B Post R) :
    ∀ {Γ : List ℕ} {α : Type} (φ : Formula (language L) TC.shape Γ α),
      Correct v a P B Post R φ
  | _, _, .ofFO φ => correct_ofFO hE φ
  | _, _, .rel r _ => fun hΓ => by subst hΓ; cases r
  | _, _, .neg φ => correct_neg (correct hE φ)
  | _, _, .conj φ ψ => correct_conj hE (correct hE φ) (correct hE ψ)
  | _, _, .ex φ => correct_ex hE (correct hE φ)
  | _, _, .op k body args => correct_op hE k body args (correct hE (body ⟨0, Nat.one_pos⟩))

end Correct

variable (v)

/-- The decider's code: the shape check, the size guard, the compiled sentence, accept, reject. -/
def deciderCode (φ : Formula (language L) TC.shape [] Empty) : List Instr :=
  (shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + len φ true)).map Instr.shift ++
    [(Instr.lt (reg 0) (const 2) (6 + 6 * v.count + len φ true) (5 + 6 * v.count)).shift] ++
    compile v (fun e : Empty => e.elim) 3 φ true (5 + 6 * v.count) (5 + 6 * v.count + len φ true)
      (6 + 6 * v.count + len φ true) ++ [.accept, .reject]

/-- The nondeterministic decider of a sentence with positive closures. -/
def decider (φ : Formula (language L) TC.shape [] Empty) : CounterProgram where
  code := deciderCode v φ
  registers := 4 + scratch φ

variable {v}

private theorem decider_layout (φ : Formula (language L) TC.shape [] Empty) :
    (decider v φ).CodeAt 0
      ((shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + len φ true)).map Instr.shift) ∧
    (decider v φ).instr (4 + 6 * v.count) =
      (Instr.lt (reg 0) (const 2) (6 + 6 * v.count + len φ true) (5 + 6 * v.count)).shift ∧
    (decider v φ).CodeAt (5 + 6 * v.count) (compile v (fun e : Empty => e.elim) 3 φ true
      (5 + 6 * v.count) (5 + 6 * v.count + len φ true) (6 + 6 * v.count + len φ true)) ∧
    (decider v φ).instr (5 + 6 * v.count + len φ true) = .accept ∧
    (decider v φ).instr (6 + 6 * v.count + len φ true) = .reject := by
  have hcode : (decider v φ).CodeAt 0 (decider v φ).code :=
    codeAt_of_code_eq (pre := []) (post := []) (by simp)
  change (decider v φ).CodeAt 0 (deciderCode v φ) at hcode
  rw [deciderCode, codeAt_append, codeAt_append, codeAt_append] at hcode
  obtain ⟨⟨⟨hshape, hguard⟩, hcomp⟩, hhalt⟩ := hcode
  simp only [List.length_append, List.length_map, length_shapeCode, length_compile,
    List.length_singleton, Nat.zero_add] at hguard hcomp hhalt
  obtain ⟨hacc, hrest⟩ := codeAt_cons.mp hhalt
  refine ⟨hshape, (codeAt_cons.mp hguard).1, ?_, ?_, ?_⟩
  · rwa [show 4 + 6 * v.count + 1 = 5 + 6 * v.count by omega] at hcomp
  · rwa [show 4 + 6 * v.count + 1 + len φ true = 5 + 6 * v.count + len φ true by omega] at hacc
  · have := (codeAt_cons.mp hrest).1
    rwa [show 4 + 6 * v.count + 1 + len φ true + 1 = 6 + 6 * v.count + len φ true by omega]
      at this

variable (v) in
omit [L.IsRelational] in
private theorem bounds (a : EncodedStructure) (k : ℕ) :
    1 ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) ∧
    a.1 ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) ∧
    a.1 ^ k ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) ∧
    (encStructure a).length ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) ∧
    ∀ i, a.1 ^ arityAt v i ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) := by
  have hm0 : v.maxArity ≠ 0 := by simp [Vocabulary.maxArity]
  have hN : 1 ≤ (encStructure a).length + 1 := Nat.le_add_left 1 _
  have hmono : ((encStructure a).length + 1) ^ v.maxArity ≤
      ((encStructure a).length + 1) ^ (v.maxArity + k) := Nat.pow_le_pow_right hN (by omega)
  have hn : a.1 ≤ (encStructure a).length + 1 :=
    (card_le_length_encStructure a).trans (Nat.le_succ _)
  refine ⟨Nat.one_le_pow _ _ hN, ?_, ?_, (length_le_pow_maxArity v a).trans hmono,
    fun i => (pow_arityAt_le v a i).trans hmono⟩
  · exact hn.trans ((Nat.le_self_pow hm0 _).trans hmono)
  · exact (Nat.pow_le_pow_left hn k).trans (Nat.pow_le_pow_right hN (by omega))

private theorem init_decider (φ : Formula (language L) TC.shape [] Empty) :
    (decider v φ).init = (0, (false : Bool).toNat :: List.replicate (3 + scratch φ) 0) := by
  simp only [init, decider, Bool.toNat_false]
  rw [show 4 + scratch φ = (3 + scratch φ) + 1 by omega, List.replicate_succ]

variable (v) in
/-- **Soundness**: every branch of the decider halts within the space bound, and accepts only
encodings of structures in the query. -/
theorem allBranches_decider {φ : Formula (language L) TC.shape [] Empty}
    (hpos : TC.Positive φ true) {K : Query L}
    (hφ : ∀ M : Ordered.Structure L,
      M ∈ K ↔ φ.Realize (M := M) TC.interpretation RelEnv.empty Empty.elim)
    (a : EncodedStructure) :
    (decider v φ).AllBranches (encStructure a)
      (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ))
      (fun s => (decider v φ).instr s.1 = .accept → a ∈ K.encodedLanguage v) (fun _ => False)
      (decider v φ).init := by
  obtain ⟨hshape, hguard, hcomp, hacc, hrej⟩ := decider_layout (v := v) φ
  obtain ⟨hB1, hnB, hwidth, hwB, hLB⟩ := bounds v a (TC.width φ)
  rw [init_decider]
  suffices h : Sound (decider v φ) (encStructure a)
      (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ))
      (fun s => (decider v φ).instr s.1 = .accept → a ∈ K.encodedLanguage v) 0
      (List.replicate (3 + scratch φ) 0) 0 (fun _ => False) from
    (h false).mono fun _ ⟨_, _, _, h⟩ => h
  obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
    reaches_shapeCode (P := padded 0 (shapeCode v 0 (4 + 6 * v.count)
      (6 + 6 * v.count + len φ true))) (codeAt_padded 0 _) hLB hwB
      (List.replicate (3 + scratch φ) 0) (by simp) (by simp) (by simp)
  refine Sound.of_reaches hB1 hshape hreach₁ ?_
  have hreject : ∀ regs : List ℕ, (∀ r ∈ regs, r ≤
      ((encStructure a).length + 1) ^ (v.maxArity + TC.width φ)) →
      Sound (decider v φ) (encStructure a)
        (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ))
        (fun s => (decider v φ).instr s.1 = .accept → a ∈ K.encodedLanguage v)
        (6 + 6 * v.count + len φ true) regs 0 (fun _ => False) := fun regs hregs =>
    Sound.halt hB1 (by rw [hrej]; rfl) (fun _ h => by simp [hrej] at h) hregs
  by_cases hwf : v.WellFormed a
  · rw [ite_eq_left hwf]
    by_cases hn : 2 ≤ a.1
    · let _ : Fact (2 ≤ a.1) := ⟨hn⟩
      let _ := v.decode a
      have hE : Env v a (decider v φ) (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ))
          (fun s => (decider v φ).instr s.1 = .accept → a ∈ K.encodedLanguage v)
          (6 + 6 * v.count + len φ true) :=
        ⟨fun fv base val => ModelChecker.atomicCompiler_correct hwf fv base val, hB1, hnB,
          by rw [hrej]; rfl, fun s hs h => by simp [hs, hrej] at h⟩
      refine Sound.of_oblivious hB1 (l' := 5 + 6 * v.count) (regs' := regs₁) ?_ ?_
      · refine Reaches.slt hguard (Nat.zero_le _) hB₁ ?_
        rw [ite_eq_right (by simp only [Expr.eval_reg, Expr.eval_const, h0₁ hwf]; omega)]
        exact Reaches.refl _
      have hC := correct hE φ rfl true hpos hwidth (fun e : Empty => e.elim) 3 Empty.elim
        RelEnv.empty (5 + 6 * v.count) (5 + 6 * v.count + len φ true) regs₁ hcomp (by decide)
        (fun e => e.elim) (by rw [hlen₁]; simp) (h0₁ hwf) (fun e => e.elim) hB₁
      refine hC.1.bind fun regs' ⟨hk, hsat⟩ => Sound.halt hB1 (by rw [hacc]; rfl)
        (fun _ _ => ?_) hk.2.2
      exact (show v.WellFormed a ∧ ∃ hn : 2 ≤ a.1, decoded v a hn ∈ K from
        ⟨hwf, hn, (hφ (decoded v a hn)).mpr hsat⟩)
    · refine Sound.of_oblivious hB1 (l' := 6 + 6 * v.count + len φ true) (regs' := regs₁) ?_
        (hreject regs₁ hB₁)
      refine Reaches.slt hguard (Nat.zero_le _) hB₁ ?_
      rw [ite_eq_left (by simp only [Expr.eval_reg, Expr.eval_const, h0₁ hwf]; omega)]
      exact Reaches.refl _
  · rw [ite_eq_right hwf]
    exact hreject regs₁ hB₁

variable (v) in
/-- **Completeness**: on every encoding of a structure in the query, some branch of the decider
accepts. -/
theorem accepts_decider {φ : Formula (language L) TC.shape [] Empty}
    (hpos : TC.Positive φ true) {K : Query L}
    (hφ : ∀ M : Ordered.Structure L,
      M ∈ K ↔ φ.Realize (M := M) TC.interpretation RelEnv.empty Empty.elim)
    (a : EncodedStructure) (ha : a ∈ K.encodedLanguage v) :
    ∃ s, Branches (P := decider v φ) (w := encStructure a) (decider v φ).init s ∧
      (decider v φ).instr s.1 = .accept := by
  obtain ⟨hwf, hn, hK⟩ := ha
  let _ : Fact (2 ≤ a.1) := ⟨hn⟩
  let _ := v.decode a
  obtain ⟨hshape, hguard, hcomp, hacc, hrej⟩ := decider_layout (v := v) φ
  obtain ⟨hB1, hnB, hwidth, hwB, hLB⟩ := bounds v a (TC.width φ)
  obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
    reaches_shapeCode (P := padded 0 (shapeCode v 0 (4 + 6 * v.count)
      (6 + 6 * v.count + len φ true))) (codeAt_padded 0 _) hLB hwB
      (List.replicate (3 + scratch φ) 0) (by simp) (by simp) (by simp)
  rw [ite_eq_left hwf] at hreach₁
  have hE : Env v a (decider v φ) (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ))
      (fun _ => True) (6 + 6 * v.count + len φ true) :=
    ⟨fun fv base val => ModelChecker.atomicCompiler_correct hwf fv base val, hB1, hnB,
      by rw [hrej]; rfl, fun _ _ => trivial⟩
  have hC := correct hE φ rfl true hpos hwidth (fun e : Empty => e.elim) 3 Empty.elim
    RelEnv.empty (5 + 6 * v.count) (5 + 6 * v.count + len φ true) regs₁ hcomp (by decide)
    (fun e => e.elim) (by rw [hlen₁]; simp) (h0₁ hwf) (fun e => e.elim) hB₁
  have hguardStep : (decider v φ).Reaches (encStructure a)
      ((decider v φ).Oblivious (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ)))
      (4 + 6 * v.count, 0 :: regs₁) (5 + 6 * v.count, 0 :: regs₁) := by
    refine Reaches.slt hguard (Nat.zero_le _) hB₁ ?_
    rw [ite_eq_right (by simp only [Expr.eval_reg, Expr.eval_const, h0₁ hwf]; omega)]
    exact Reaches.refl _
  obtain ⟨regs', -, hbr⟩ := Complete.of_reaches hshape hreach₁
    (Complete.of_oblivious hguardStep (hC.2 ((hφ (decoded v a hn)).mp hK)))
  obtain ⟨c', hc'⟩ := hbr false
  rw [init_decider]
  exact ⟨_, hc', hacc⟩

variable (v) in
/-- **A query defined by a sentence with positive closures is in native `NL`**: its source-only
encoded language is decided by one nondeterministic machine in logarithmic space. -/
theorem encodedLanguage_mem_NL {φ : Formula (language L) TC.shape [] Empty}
    (hpos : TC.Positive φ true) {K : Query L}
    (hφ : ∀ M : Ordered.Structure L,
      M ∈ K ↔ φ.Realize (M := M) TC.interpretation RelEnv.empty Empty.elim) :
    K.encodedLanguage v ∈ Complexity.NL encStructure :=
  exists_decidesInLogSpace_of_allBranches (decider v φ) (v.maxArity + TC.width φ)
    (allBranches_decider v hpos hφ) (accepts_decider v hpos hφ)

end Cslib.Logic.FO.Ordered.TCModelChecker

namespace Cslib.Logic.FO.Ordered

/-- **FO(positive TC) ⊆ NL** on canonically ordered structures: a query defined by one FO(TC)
sentence whose closures occur positively is in native nondeterministic logarithmic space, at the
source-only structure encoding. -/
theorem PosTCDefinable.encodedLanguage_mem_NL {L : Language} [L.IsRelational] {K : Query L}
    (hK : PosTCDefinable K) (v : Vocabulary L) :
    K.encodedLanguage v ∈ Complexity.NL encStructure :=
  let ⟨_, hpos, hφ⟩ := hK
  TCModelChecker.encodedLanguage_mem_NL v hpos hφ

end Cslib.Logic.FO.Ordered
