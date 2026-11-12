/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Counting
public import CslibFrontier.Logics.FirstOrder.Ordered.TransitiveClosure
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.NondeterministicDecider
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step

/-!
# FO(TC) model checking in nondeterministic logarithmic space

For each fixed sentence of FO(TC) over a finite relational vocabulary expanded by the canonical
numeric symbols, the encoded query language belongs to the native class `NL`. The input uses
`encStructure`, as for ordered first-order model checking in `L`; malformed table shapes and
cardinalities below two are rejected.

The decider is one nondeterministic counter program, `nblockDecider` around the compiled sentence
at polarity `true`: it validates the input tables, rejects cardinalities below two, and runs the
compiled code. Every branch halts with every register at most `(N + 1) ^ (d + w)` for input length
`N`, maximal input arity `d` and closure width `w`, so the program runs in logarithmic space.

[Immerman1987], Theorem 3.1, places FO(positive TC) in NL; closures under negation add nothing
because NL is closed under complementation ([Immerman1988], Corollary 3; [Szelepcsenyi1987]).
Here both polarities are compiled directly. A closure at polarity `true` is evaluated by a
bounded guessed path. A closure at polarity `false` (under an odd number of negations, counted
afresh inside each closure body) is evaluated by an inductive-counting block whose tests run the
compiled body at both polarities. The converse inclusion NL ⊆ FO(positive TC), and with it
FO(TC) = NL, is in `Classes.LogSpace.FirstOrder.TransitiveClosure.Converse`.

## Main results

* `Cslib.Logic.FO.Ordered.TCModelChecker.correct`: compiler correctness for every formula.
* `Cslib.Logic.FO.Ordered.TCModelChecker.encodedLanguage_mem_NL`: a query defined by an FO(TC)
  sentence is in native `NL`.
* `Cslib.Logic.FO.Ordered.TCDefinable.encodedLanguage_mem_NL`: FO(TC) ⊆ NL on canonically ordered
  structures.
* `Cslib.Logic.FO.Ordered.PosTCDefinable.encodedLanguage_mem_NL`: the positive fragment.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 3.1][Immerman1987]
* [N. Immerman, *Nondeterministic Space is Closed Under Complementation*, Corollary 3][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
-/

public section

universe u v w

open FirstOrder Language
namespace Cslib.Logic.FO.Ordered.TCModelChecker

open Turing Turing.CounterProgram Turing.CounterProgram.Block Expr Vocabulary.ModelChecker
open Operator (Formula RelEnv)
open ClosureKernel (termE getD_pair eval_pow_reg0)

variable {L : Language.{u, v}} [L.IsRelational] {v : Vocabulary L}

section Correct

variable {a : EncodedStructure} [L.Structure (Fin a.1)] [Fact (2 ≤ a.1)]
  {P : CounterProgram} {B : ℕ} {Post : Config → Prop} {R : ℕ}

private theorem sound_of_eq {w : List Bool} {l l' T T' : ℕ} {regs : List ℕ}
    {G : List ℕ → Prop} (h : Sound P w B Post l regs T G) (hl : l = l') (hT : T = T') :
    Sound P w B Post l' regs T' G := by
  subst hl hT; exact h

private theorem complete_of_eq {w : List Bool} {l l' T T' : ℕ} {regs : List ℕ}
    {G : List ℕ → Prop} (h : Complete P w l regs T G) (hl : l = l') (hT : T = T') :
    Complete P w l' regs T' G := by
  subst hl hT; exact h

/-- The compiled body of a closure, run with the outer free variables below `base` and a pair
`(us, ws)` from register `base'`, decides the edge relation `E` at polarity `s`. -/
private theorem body_correct {Γ : List ℕ} {α : Type} {k : ℕ}
    {body : (i : Fin (TC.shape k).slots) → Formula (language L) TC.shape
      (((TC.shape k).binder i).relations ++ Γ) (α ⊕ Fin ((TC.shape k).binder i).vars)}
    (ih : Correct v a P B Post R (body ⟨0, Nat.one_pos⟩)) (hΓ : Γ = [])
    (hWb : a.1 ^ TC.width (body ⟨0, Nat.one_pos⟩) ≤ B)
    {fv : α → ℕ} {base : ℕ} {val : α → Fin a.1} {ρ : RelEnv Γ (Fin a.1)} {regs₀ : List ℕ}
    (hbase : 0 < base) (hfv : ∀ x, fv x < base) (h0 : regs₀.getD 0 0 = a.1)
    (hv : ∀ x, regs₀.getD (fv x) 0 = val x)
    {E : (Fin k → Fin a.1) → (Fin k → Fin a.1) → Prop}
    (hEiff : ∀ us ws, E us ws ↔ (body ⟨0, Nat.one_pos⟩).Realize TC.interpretation
      (RelEnv.empty.append ρ) (Sum.elim val (TC.pair us ws)))
    {base' sb : ℕ} (hb' : base ≤ base') (hsb : base' + 2 * k ≤ sb) (s : Bool) {l T : ℕ}
    (hP : P.CodeAt l (compile v (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
      (Sum.elim fv fun i => base' + i.val) sb (body ⟨0, Nat.one_pos⟩) s l T R))
    {regs : List ℕ} (hk : Kept B base regs₀ regs)
    (hd : sb + scratch (body ⟨0, Nat.one_pos⟩) ≤ regs.length)
    {us ws : Fin k → Fin a.1} (hu : ∀ j : Fin k, regs.getD (base' + j) 0 = us j)
    (hw : ∀ j : Fin k, regs.getD (base' + k + j) 0 = ws j) :
    Sound P (encStructure a) B Post l regs T
      (fun regs' => Kept B sb regs regs' ∧ Sat s (E us ws)) ∧
    (Sat s (E us ws) → Complete P (encStructure a) l regs T (Kept B sb regs)) := by
  have hsat : Sat s (E us ws) ↔ Sat s ((body ⟨0, Nat.one_pos⟩).Realize TC.interpretation
      (RelEnv.empty.append ρ) (Sum.elim val (TC.pair us ws))) := by
    cases s
    · exact not_congr (hEiff us ws)
    · exact hEiff us ws
  obtain ⟨hs, hc⟩ := ih (by rw [hΓ]; rfl) s hWb _ sb (Sum.elim val (TC.pair us ws))
    (RelEnv.empty.append ρ) l T regs hP (by omega)
    (fun x => by
      cases x with
      | inl x => have := hfv x; simp only [Sum.elim_inl]; omega
      | inr i => have : (i : ℕ) < 2 * k := i.isLt; simp only [Sum.elim_inr]; omega)
    hd ((hk.getD_eq 0 hbase).trans h0)
    (fun x => by
      cases x with
      | inl x => simp only [Sum.elim_inl]; exact (hk.getD_eq _ (hfv x)).trans (hv x)
      | inr i => exact getD_pair hu hw i)
    hk.bounded
  exact ⟨hs.mono fun regs' h => ⟨h.1, hsat.mpr h.2⟩, fun h => hc (hsat.mp h)⟩

/-- One test of the counting block of a negated closure, with the compiled body as walk and
edge codes, is sound and complete. -/
private theorem test_correct (hE : Env v a P B Post R) {Γ : List ℕ} {α : Type} {k : ℕ}
    {body : (i : Fin (TC.shape k).slots) → Formula (language L) TC.shape
      (((TC.shape k).binder i).relations ++ Γ) (α ⊕ Fin ((TC.shape k).binder i).vars)}
    {args : Fin (TC.shape k).arity → (language L).Term α}
    (ih : Correct v a P B Post R (body ⟨0, Nat.one_pos⟩)) (hΓ : Γ = [])
    (hNB : a.1 ^ k ≤ B) (hWb : a.1 ^ TC.width (body ⟨0, Nat.one_pos⟩) ≤ B)
    {fv : α → ℕ} {base : ℕ} {val : α → Fin a.1} {ρ : RelEnv Γ (Fin a.1)} {regs₀ : List ℕ}
    (hbase : 0 < base) (hfv : ∀ x, fv x < base)
    (hd : base + 9 + 4 * k + scratch (body ⟨0, Nat.one_pos⟩) ≤ regs₀.length)
    (h0 : regs₀.getD 0 0 = a.1) (hv : ∀ x, regs₀.getD (fv x) 0 = val x)
    {s₀ : Fin k → Fin a.1}
    (hsrc : ∀ regs : List ℕ, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ j, (termE fv (TC.left args j)).eval regs = s₀ j)
    {E : (Fin k → Fin a.1) → (Fin k → Fin a.1) → Prop}
    (hEiff : ∀ us ws, E us ws ↔ (body ⟨0, Nat.one_pos⟩).Realize TC.interpretation
      (RelEnv.empty.append ρ) (Sum.elim val (TC.pair us ws)))
    {l l' T : ℕ}
    (hP : P.CodeAt l' (countTestCode l base k (fun i => termE fv (TC.left args i))
      (compile v (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
        (Sum.elim fv fun i => base + 7 + 2 * k + i.val) (base + 9 + 4 * k)
        (body ⟨0, Nat.one_pos⟩) true (l + 6 + 2 * k + 2 * k + 7)
        (l + 6 + 2 * k + 2 * k + 7 + len (body ⟨0, Nat.one_pos⟩) true) R)
      (compile v (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
        (Sum.elim fv fun i => base + 7 + i.val) (base + 7 + 2 * k)
        (body ⟨0, Nat.one_pos⟩) true (l + 22 + 5 * k + len (body ⟨0, Nat.one_pos⟩) true)
        (l + 21 + 5 * k + len (body ⟨0, Nat.one_pos⟩) true) R)
      (compile v (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
        (Sum.elim fv fun i => base + 7 + i.val) (base + 7 + 2 * k)
        (body ⟨0, Nat.one_pos⟩) false (l + 23 + 5 * k + 2 * len (body ⟨0, Nat.one_pos⟩) true)
        (l + 23 + 5 * k + 2 * len (body ⟨0, Nat.one_pos⟩) true +
          len (body ⟨0, Nat.one_pos⟩) false) R)
      T R))
    (hl : l' = l) {i y : ℕ} {regs : List ℕ} (hpre : TestPre B base E s₀ regs₀ i y regs) :
    Sound P (encStructure a) B Post l regs T (fun regs' => Kept B (base + 4) regs regs' ∧
      regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) ∧
    Complete P (encStructure a) l regs T (fun regs' => Kept B (base + 4) regs regs' ∧
      regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) := by
  replace hP := codeAt_of_eq hP hl
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, -, -, -, -, -, -, h18, -, h20, -⟩ :=
    countTestCode_parts (w₁ := l + 14 + 5 * k + len (body ⟨0, Nat.one_pos⟩) true)
      (by rw [length_compile]) hP
  have hwb := (tcCode_parts h9).2.2.2.2.2.2.1
  refine ⟨test_sound (w₁ := l + 14 + 5 * k + len (body ⟨0, Nat.one_pos⟩) true)
    (by rw [length_compile]) hP hE.one_le hE.card_le hNB hE.halts hE.post hsrc ?_ ?_ ?_ hpre,
    test_complete (w₁ := l + 14 + 5 * k + len (body ⟨0, Nat.one_pos⟩) true)
    (by rw [length_compile]) hP hE.one_le hE.card_le hNB hsrc ?_ ?_ ?_ hpre⟩
  · intro regsW us ws t regs₃ hkW hmid
    obtain ⟨⟨hk₃, -, hu, -⟩, hw⟩ := hmid
    rw [length_compile]
    exact ((body_correct ih hΓ hWb hbase hfv h0 hv hEiff (by omega) (by omega) true hwb
      (hkW.trans (hk₃.mono (by omega))) (by rw [hk₃.length_eq, hkW.length_eq]; omega) hu
      hw).1).mono
      fun regs' h => ⟨h.1.mono (by omega), h.2⟩
  · intro regs₂ xs ys hk₂ hx hy
    exact sound_of_eq ((body_correct ih hΓ hWb hbase hfv h0 hv hEiff (by omega) (by omega)
      true (codeAt_of_eq h18 (by omega)) hk₂ (by rw [hk₂.length_eq]; omega) hx hy).1.mono
      fun regs' h => ⟨h.1, h.2⟩) (by omega) (by omega)
  · intro regs₂ xs ys hk₂ hx hy
    exact sound_of_eq ((body_correct ih hΓ hWb hbase hfv h0 hv hEiff (by omega) (by omega)
      false (codeAt_of_eq h20 (by rw [length_compile]; omega)) hk₂ (by rw [hk₂.length_eq]; omega) hx
      hy).1.mono fun regs' h => ⟨h.1, h.2⟩) (by rw [length_compile]; omega)
      (by simp only [length_compile]; omega)
  · intro regsW us ws t regs₃ hkW hmid he
    obtain ⟨⟨hk₃, -, hu, -⟩, hw⟩ := hmid
    rw [length_compile]
    exact ((body_correct ih hΓ hWb hbase hfv h0 hv hEiff (by omega) (by omega) true hwb
      (hkW.trans (hk₃.mono (by omega))) (by rw [hk₃.length_eq, hkW.length_eq]; omega) hu
      hw).2 he).mono
      fun regs' h => h.mono (by omega)
  · intro regs₂ xs ys hk₂ hx hy he
    exact complete_of_eq ((body_correct ih hΓ hWb hbase hfv h0 hv hEiff (by omega)
      (by omega) true (codeAt_of_eq h18 (by omega)) hk₂ (by rw [hk₂.length_eq]; omega) hx hy).2 he)
      (by omega) (by omega)
  · intro regs₂ xs ys hk₂ hx hy he
    exact complete_of_eq ((body_correct ih hΓ hWb hbase hfv h0 hv hEiff (by omega)
      (by omega) false (codeAt_of_eq h20 (by rw [length_compile]; omega)) hk₂
      (by rw [hk₂.length_eq]; omega) hx hy).2 he) (by rw [length_compile]; omega)
      (by simp only [length_compile]; omega)

theorem correct_op (hE : Env v a P B Post R) {Γ : List ℕ} {α : Type} (k : ℕ)
    (body : (i : Fin (TC.shape k).slots) → Formula (language L) TC.shape
      (((TC.shape k).binder i).relations ++ Γ) (α ⊕ Fin ((TC.shape k).binder i).vars))
    (args : Fin (TC.shape k).arity → (language L).Term α)
    (ih : Correct v a P B Post R (body ⟨0, Nat.one_pos⟩)) :
    Correct v a P B Post R (Formula.op k body args) := by
  intro hΓ s hW fv base val ρ b T regs hP hbase hfv hd h0 hv hregs
  have hn : 0 < a.1 := by have := (Fact.out : 2 ≤ a.1); omega
  have hNB : a.1 ^ k ≤ B := (Nat.pow_le_pow_right hn (le_max_left _ _)).trans hW
  have hWb : a.1 ^ TC.width (body ⟨0, Nat.one_pos⟩) ≤ B :=
    (Nat.pow_le_pow_right hn (le_max_right _ _)).trans hW
  have hscratch : scratch (Formula.op (L := language L) (shape := TC.shape) (Γ := Γ) k body args) =
      4 * k + 9 + scratch (body ⟨0, Nat.one_pos⟩) := rfl
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
  cases s with
  | false =>
    -- inductive counting: one test per candidate per round, then a test of the target
    have hEiff : ∀ us ws, E us ws ↔ (body ⟨0, Nat.one_pos⟩).Realize TC.interpretation
        (RelEnv.empty.append ρ) (Sum.elim val (TC.pair us ws)) := fun _ _ => Iff.rfl
    have hd' : base + 9 + 4 * k + scratch (body ⟨0, Nat.one_pos⟩) ≤ regs.length := by omega
    obtain ⟨-, -, -, -, -, -, c7, -, -, -, -, -, c13, -⟩ := countCode_parts hP
    refine ⟨count_sound (E := E) (s₀ := s₀) (z₀ := z₀) hP hbase hE.one_le hNB hE.halts hE.post
      hdst ?_ ?_ (by omega) h0 hregs, fun hn => count_complete (E := E) (s₀ := s₀) (z₀ := z₀)
      hP hbase hE.one_le hNB hdst ?_ ?_ (by omega) h0 hregs hn⟩
    · intro i y regs' hpre
      exact sound_of_eq (test_correct hE ih hΓ hNB hWb hbase hfv hd' h0 hv hsrc hEiff c7 rfl
        hpre).1 rfl (by simp only [length_countTestCode, length_compile]; omega)
    · intro i y regs' hpre
      exact sound_of_eq (test_correct hE ih hΓ hNB hWb hbase hfv hd' h0 hv hsrc hEiff c13
        (by simp only [length_countTestCode, length_compile]; omega) hpre).1
        (by simp only [length_countTestCode, length_compile]; omega)
        (by simp only [length_countTestCode, length_compile]; omega)
    · intro i y regs' hpre
      exact complete_of_eq (test_correct hE ih hΓ hNB hWb hbase hfv hd' h0 hv hsrc hEiff c7 rfl
        hpre).2 rfl (by simp only [length_countTestCode, length_compile]; omega)
    · intro i y regs' hpre
      exact complete_of_eq (test_correct hE ih hΓ hNB hWb hbase hfv hd' h0 hv hsrc hEiff c13
        (by simp only [length_countTestCode, length_compile]; omega) hpre).2
        (by simp only [length_countTestCode, length_compile]; omega)
        (by simp only [length_countTestCode, length_compile]; omega)
  | true =>
  have hdb : base + 2 * k + 2 + scratch (body ⟨0, Nat.one_pos⟩) ≤ regs.length := by omega
  -- the body block
  let code := compile v (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
    (Sum.elim fv fun i => base + i.val) (base + 2 * k + 2) (body ⟨0, Nat.one_pos⟩) true
    (b + 2 * k + 7) (b + 2 * k + 7 + len (body ⟨0, Nat.one_pos⟩) true) R
  have hP' : P.CodeAt b (tcCode b base k (fun i => termE fv (TC.left args i))
      (fun i => termE fv (TC.right args i)) (pow (reg 0) k) code T R) := hP
  have hM : ∀ regs' : List ℕ, (∀ j < base, regs'.getD j 0 = regs.getD j 0) →
      (pow (reg 0) k).eval regs' = a.1 ^ k := fun _ h => eval_pow_reg0 ((h 0 hbase).trans h0)
  have hcl : code.length = len (body ⟨0, Nat.one_pos⟩) true := length_compile ..
  have hbody : ∀ us ws t regs₃, LoopMid a.1 B base k regs us ws t regs₃ →
      Sound P (encStructure a) B Post (b + 2 * k + 7) regs₃ (b + 2 * k + 7 + code.length)
        (fun regs' => Kept B (base + 2 * k + 2) regs₃ regs' ∧ E us ws) ∧
      (E us ws → Complete P (encStructure a) (b + 2 * k + 7) regs₃
        (b + 2 * k + 7 + code.length) (Kept B (base + 2 * k + 2) regs₃)) := by
    intro us ws t regs₃ hmid
    obtain ⟨⟨hk, hlen, hu, -⟩, hw⟩ := hmid
    rw [hcl]
    exact body_correct ih hΓ hWb hbase hfv h0 hv (fun _ _ => Iff.rfl) le_rfl (by omega) true
      (tcCode_parts hP').2.2.2.2.2.2.1 hk (by rw [hk.length_eq]; omega) hu hw
  obtain ⟨regsI, hrI, hinvI⟩ := loop_init (w := encStructure a) hP' (by omega)
    hE.card_le hregs hsrc
  refine ⟨Sound.of_oblivious hE.one_le hrI ?_, fun hsat => Complete.of_oblivious hrI ?_⟩
  · refine (loop_sound (s₀ := s₀) hP' hbase hE.one_le hE.card_le hNB hNB h0 hE.halts hE.post
      hdst hM (fun us ws t regs₃ hmid => (hbody us ws t regs₃ hmid).1) _ 0 s₀ regsI rfl
      (Nat.zero_le _) hinvI (Relation.RelatesWithinSteps.refl _)).mono
      fun regs' h => ⟨h.1, h.2.reflTransGen⟩
  · have hcard : Nat.card (Fin k → Fin a.1) ≤ a.1 ^ k - 1 + 1 := by
      have : 0 < a.1 ^ k := pow_pos hn k
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      omega
    obtain ⟨m, hm, hsteps⟩ := (Relation.reflTransGen_iff_relatesWithinSteps hcard).mp hsat
    have : 0 < a.1 ^ k := pow_pos hn k
    exact loop_complete hP' hbase hE.card_le hNB hNB h0 hdst hM
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

variable (v) in
/-- **A query defined by an FO(TC) sentence is in native `NL`**: its source-only encoded language
is decided by one nondeterministic machine, `nblockDecider` around the compiled sentence at
polarity `true`, in logarithmic space. -/
theorem encodedLanguage_mem_NL {φ : Formula (language L) TC.shape [] Empty}
    {K : Query L}
    (hφ : ∀ M : Ordered.Structure L,
      M ∈ K ↔ φ.Realize (M := M) TC.interpretation RelEnv.empty Empty.elim) :
    K.encodedLanguage v ∈ Complexity.NL encStructure :=
  mem_NL_of_soundCompleteBlock v (k := TC.width φ) (s := scratch φ)
    (C := fun b T F => compile v (fun e : Empty => e.elim) 3 φ true b T F)
    (fun b T F => length_compile v (fun e : Empty => e.elim) 3 φ true b T F)
    (fun _ h => ⟨h.1, h.2.1⟩)
    fun a hwf hn _ _ b T F regs hP hF hPost hlen h0 hB => by
      let _ : Fact (2 ≤ a.1) := ⟨hn⟩
      let _ := v.decode a
      obtain ⟨hB1, hnB, hwidth, -, -⟩ := decider_bounds v a (TC.width φ)
      have hE : Env v a _ (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ)) _ F :=
        ⟨fun fv base val => ModelChecker.atomicCompiler_correct hwf fv base val, hB1, hnB, hF,
          hPost⟩
      have hC := correct hE φ rfl true hwidth (fun e : Empty => e.elim) 3 Empty.elim
        RelEnv.empty b T regs hP (by decide) (fun e => e.elim) (by omega) h0 (fun e => e.elim) hB
      refine ⟨hC.1.mono fun regs' ⟨hk, hsat⟩ =>
        ⟨hk.bounded, hwf, hn, (hφ (decoded v a hn)).mpr hsat⟩, fun ⟨_, _, hK⟩ => ?_⟩
      exact (hC.2 ((hφ (decoded v a hn)).mp hK)).mono fun _ _ => trivial

end Cslib.Logic.FO.Ordered.TCModelChecker

namespace Cslib.Logic.FO.Ordered

/-- **FO(TC) ⊆ NL** on canonically ordered structures: a query defined by one FO(TC) sentence is
in native nondeterministic logarithmic space, at the source-only structure encoding. -/
theorem TCDefinable.encodedLanguage_mem_NL {L : Language} [L.IsRelational] {K : Query L}
    (hK : TCDefinable K) (v : Vocabulary L) :
    K.encodedLanguage v ∈ Complexity.NL encStructure :=
  let ⟨_, hφ⟩ := hK
  TCModelChecker.encodedLanguage_mem_NL v hφ

/-- **FO(positive TC) ⊆ NL** on canonically ordered structures: the positive fragment, as a
special case of `TCDefinable.encodedLanguage_mem_NL`. -/
theorem PosTCDefinable.encodedLanguage_mem_NL {L : Language} [L.IsRelational] {K : Query L}
    (hK : PosTCDefinable K) (v : Vocabulary L) :
    K.encodedLanguage v ∈ Complexity.NL encStructure :=
  hK.tcDefinable.encodedLanguage_mem_NL v

end Cslib.Logic.FO.Ordered
