/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Compile
public import CslibFrontier.Foundations.Relation.RelatesWithinSteps
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step

/-!
# The bounded closure loop

`tcCode` decides bounded reachability of a target tuple from a source tuple along the edges
computed by compiled body code, in a universe of size `n`. It keeps the current tuple and a step
counter, tests the current tuple against the target, guesses a successor below `n ^ k`, decodes its
base-`n` digits, runs the body, and counts the step; it rejects once the counter reaches the value
`M₀` of the step-bound expression. Every branch therefore halts, and the loop certifies exactly
the paths of at most `M₀` steps. Closures use `M₀ = n ^ k`; inductive counting uses smaller
bounds.

## Main results

* `Cslib.Logic.FO.Ordered.TCModelChecker.loop_sound`: every branch rejects or reaches the exit with
  the target reachable within `M₀` steps.
* `Cslib.Logic.FO.Ordered.TCModelChecker.loop_complete`: a path of at most `M₀` steps gives a
  branch reaching the exit.
-/

public section

namespace Cslib.Logic.FO.Ordered.TCModelChecker

open Turing Turing.CounterProgram Turing.CounterProgram.Block Expr Vocabulary.ModelChecker
open ClosureKernel

/-- Decoding register `r`, holding `g < n ^ k`, into registers `d + i` writes the tuple
`finFunctionFinEquiv.symm g`. -/
theorem reaches_digits {P : CounterProgram} {w : List Bool} {B b r d k n : ℕ}
    (hP : P.CodeAt b (assignChain b d k (digitE r))) (hrd : r < d ∨ d + k ≤ r) (hd : 0 < d)
    {regs : List ℕ} (hlen : d + k ≤ regs.length) (h0 : regs.getD 0 0 = n)
    (hnB : n ≤ B) (hB : ∀ x ∈ regs, x ≤ B) (g : Fin (n ^ k)) (hg : regs.getD r 0 = g) :
    ∃ regs', P.Reaches w (P.Oblivious B) (b, 0 :: regs) (b + k, 0 :: regs') ∧
      regs'.length = regs.length ∧
      (∀ j, (j < d ∨ d + k ≤ j) → regs'.getD j 0 = regs.getD j 0) ∧
      (∀ i : Fin k, regs'.getD (d + i) 0 = finFunctionFinEquiv.symm g i) ∧
      ∀ x ∈ regs', x ≤ B := by
  obtain ⟨regs', hr, hrest⟩ := reaches_digitsCode (w := w)
    (codeAt_padded b (assignsCode b d k (digitE r))) hrd hd hlen h0 hnB hB g hg
  exact ⟨regs', Reaches.unpad (Nat.zero_le B) (assignChain_eq b d k _ ▸ hP) hr, hrest⟩

theorem tcCode_parts {P : CounterProgram} {b base k : ℕ} {src dst : Fin k → Expr} {M : Expr}
    {body : List Instr} {T R : ℕ} (hP : P.CodeAt b (tcCode b base k src dst M body T R)) :
    P.CodeAt b (assignChain b base k (fun i => if h : i < k then src ⟨i, h⟩ else const 0)) ∧
    P.instr (b + k) = (Instr.assign (base + 2 * k + 1) (const 0) (b + k + 1)).shift ∧
    P.instr (b + k + 1) = (Instr.lt (const 0) (testExpr base k dst) (b + k + 2) T).shift ∧
    P.instr (b + k + 2) =
      (Instr.lt (reg (base + 2 * k + 1)) M (b + k + 3) R).shift ∧
    P.CodeAt (b + k + 3) (guessCode (b + k + 3) (base + 2 * k) (pow (reg 0) k) (b + k + 7) R) ∧
    P.CodeAt (b + k + 7) (assignChain (b + k + 7) (base + k) k (digitE (base + 2 * k))) ∧
    P.CodeAt (b + 2 * k + 7) body ∧
    P.CodeAt (b + 2 * k + 7 + body.length)
      (assignChain (b + 2 * k + 7 + body.length) base k (fun i => reg (base + k + i))) ∧
    P.instr (b + 3 * k + 7 + body.length) = (Instr.assign (base + 2 * k + 1)
      (add (reg (base + 2 * k + 1)) (const 1)) (b + k + 1)).shift := by
  simp only [tcCode, codeAt_append, codeAt_cons, List.length_append, length_assignChain,
    List.length_cons, List.length_nil, length_guessCode] at hP
  obtain ⟨⟨⟨⟨⟨⟨h1, h2, h3, h4, -⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9, -⟩ := hP
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_, ?_⟩
  · convert h5 using 2
  · convert h6 using 2
  · convert h7 using 1; omega
  · convert h8 using 1; omega
  · convert h9 using 2; omega

section Loop

variable {P : CounterProgram} {w : List Bool} {n B b base k T R : ℕ} {Post : Config → Prop}
  {src dst : Fin k → Expr} {M : Expr} {body : List Instr} {regs₀ : List ℕ}

variable (n B base k regs₀) in
/-- The loop invariant at the test label: registers below `base` and the length are kept, the
current tuple is in registers `base + i`, and the step counter is `t`. -/
structure LoopInv (us : Fin k → Fin n) (t : ℕ) (regs : List ℕ) : Prop where
  /-- The registers below `base` and the length are kept, and every register is bounded. -/
  kept : Kept B base regs₀ regs
  /-- The loop's registers exist. -/
  le_length : base + 2 * k + 2 ≤ regs.length
  /-- The current tuple is in registers `base + i`. -/
  cur : ∀ i : Fin k, regs.getD (base + i) 0 = us i
  /-- The step counter is in register `base + 2 * k + 1`. -/
  counter : regs.getD (base + 2 * k + 1) 0 = t

variable (n B base k regs₀) in
/-- The state after decoding a successor: the loop invariant, the decoded tuple in registers
`base + k + i`. -/
structure LoopMid (us ws : Fin k → Fin n) (t : ℕ) (regs : List ℕ) : Prop
    extends LoopInv n B base k regs₀ us t regs where
  /-- The decoded successor is in registers `base + k + i`. -/
  next : ∀ i : Fin k, regs.getD (base + k + i) 0 = ws i

/-- Initialization: copy the source tuple and reset the step counter. -/
theorem loop_init (hP : P.CodeAt b (tcCode b base k src dst M body T R))
    (hlen : base + 2 * k + 2 ≤ regs₀.length) (hnB : n ≤ B) (hB : ∀ r ∈ regs₀, r ≤ B)
    {s₀ : Fin k → Fin n}
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ i, (src i).eval regs = s₀ i) :
    ∃ regs, P.Reaches w (P.Oblivious B) (b, 0 :: regs₀) (b + k + 1, 0 :: regs) ∧
      LoopInv n B base k regs₀ s₀ 0 regs := by
  obtain ⟨hc, h2, -⟩ := tcCode_parts hP
  obtain ⟨regs₁, hr₁, hlen₁, hout₁, hin₁, hB₁⟩ := reaches_loadCode (w := w)
    (codeAt_padded b (assignsCode b base k (fun i => if h : i < k then src ⟨i, h⟩ else const 0)))
    (by omega) hnB hB hsrc
  have hr₁' : P.Reaches w (P.Oblivious B) (b, 0 :: regs₀) (b + k, 0 :: regs₁) :=
    Reaches.unpad (Nat.zero_le B) (assignChain_eq b base k _ ▸ hc) hr₁
  refine ⟨regs₁.set (base + 2 * k + 1) 0,
    hr₁'.trans (Reaches.sassign h2 (Nat.zero_le B) hB₁ (Reaches.refl _)), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [List.length_set, hlen₁]
  · intro j hj
    rw [List.getD_set_ne (by omega), hout₁ j (by omega)]
  · exact List.forall_mem_set_of_forall_mem hB₁ (Nat.zero_le B)
  · rw [List.length_set, hlen₁]; exact hlen
  · intro i
    rw [List.getD_set_ne (by omega), hin₁ i]
  · exact List.getD_set_self (by omega)

/-- Copy the decoded successor into the current tuple and count the step. -/
private theorem loop_copy (hP : P.CodeAt b (tcCode b base k src dst M body T R))
    {us ws : Fin k → Fin n} {t : ℕ} {regs₃ regs₄ : List ℕ}
    (hmid : LoopMid n B base k regs₀ us ws t regs₃)
    (hk : Kept B (base + 2 * k + 2) regs₃ regs₄) (htB : t < B) :
    ∃ regs, P.Reaches w (P.Oblivious B) (b + 2 * k + 7 + body.length, 0 :: regs₄)
      (b + k + 1, 0 :: regs) ∧ LoopInv n B base k regs₀ ws (t + 1) regs := by
  obtain ⟨-, -, -, -, -, -, -, hc, hinc⟩ := tcCode_parts hP
  obtain ⟨⟨hk₀, hlen₃, hu₃, ht₃⟩, hw₃⟩ := hmid
  have hlen₄ : base + 2 * k + 2 ≤ regs₄.length := by rw [hk.length_eq]; exact hlen₃
  have hw₄ : ∀ i : Fin k, regs₄.getD (base + k + i) 0 = ws i := fun i => by
    rw [hk.getD_eq _ (by omega), hw₃]
  obtain ⟨regs₅, hr₅, hlen₅, hout₅, hin₅, hB₅⟩ := reaches_assignChain (w := w) hc (by omega)
    (fun i hi regs' h => by
      simp only [eval_reg]
      exact h _ (by omega)) hk.bounded
    (fun i hi => by simp only [eval_reg]; exact List.getD_le_of_forall_le hk.bounded _)
  have ht₅ : regs₅.getD (base + 2 * k + 1) 0 = t := by
    rw [hout₅ _ (by omega), hk.getD_eq _ (by omega), ht₃]
  refine ⟨regs₅.set (base + 2 * k + 1) (t + 1), hr₅.trans ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [show b + 2 * k + 7 + body.length + k = b + 3 * k + 7 + body.length by omega]
    cp_step [ht₅]
  · rw [List.length_set, hlen₅, hk.length_eq, hk₀.length_eq]
  · intro j hj
    rw [List.getD_set_ne (by omega), hout₅ j (by omega), hk.getD_eq j (by omega), hk₀.getD_eq j hj]
  · exact List.forall_mem_set_of_forall_mem hB₅ (by omega)
  · rw [List.length_set, hlen₅]; exact hlen₄
  · intro i
    rw [List.getD_set_ne (by omega), hin₅ i i.isLt]
    simp only [eval_reg]
    exact hw₄ i
  · exact List.getD_set_self (by omega)

variable {us : Fin k → Fin n} {t M₀ : ℕ} {regs : List ℕ} {z₀ : Fin k → Fin n}

private theorem loop_test_eq (hP : P.CodeAt b (tcCode b base k src dst M body T R))
    (hinv : LoopInv n B base k regs₀ us t regs)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ i, (dst i).eval regs = z₀ i) (heq : us = z₀) :
    P.Reaches w (P.Oblivious B) (b + k + 1, 0 :: regs) (T, 0 :: regs) := by
  obtain ⟨-, -, h3, -⟩ := tcCode_parts hP
  have := hinv.kept.bounded
  cp_step [↓mt (lt_eval_testExpr hinv.cur (hdst regs hinv.kept.getD_eq)).mp (not_not.mpr heq)]

private theorem loop_test_ne (hP : P.CodeAt b (tcCode b base k src dst M body T R))
    (hinv : LoopInv n B base k regs₀ us t regs)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ i, (dst i).eval regs = z₀ i) (hne : us ≠ z₀) :
    P.Reaches w (P.Oblivious B) (b + k + 1, 0 :: regs) (b + k + 2, 0 :: regs) := by
  obtain ⟨-, -, h3, -⟩ := tcCode_parts hP
  have := hinv.kept.bounded
  cp_step [↓(lt_eval_testExpr hinv.cur (hdst regs hinv.kept.getD_eq)).mpr hne]

private theorem loop_bound_lt (hP : P.CodeAt b (tcCode b base k src dst M body T R))
    (hM : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → M.eval regs = M₀)
    (hinv : LoopInv n B base k regs₀ us t regs) (ht : t < M₀) :
    P.Reaches w (P.Oblivious B) (b + k + 2, 0 :: regs) (b + k + 3, 0 :: regs) := by
  obtain ⟨-, -, -, h4, -⟩ := tcCode_parts hP
  have := hinv.kept.bounded
  cp_step [hM regs hinv.kept.getD_eq, hinv.counter]

private theorem loop_bound_ge (hP : P.CodeAt b (tcCode b base k src dst M body T R))
    (hM : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → M.eval regs = M₀)
    (hinv : LoopInv n B base k regs₀ us t regs) (ht : M₀ ≤ t) :
    P.Reaches w (P.Oblivious B) (b + k + 2, 0 :: regs) (R, 0 :: regs) := by
  obtain ⟨-, -, -, h4, -⟩ := tcCode_parts hP
  have := hinv.kept.bounded
  cp_step [hM regs hinv.kept.getD_eq, hinv.counter]

private theorem loop_decode (hP : P.CodeAt b (tcCode b base k src dst M body T R))
    (hbase : 0 < base)
    (hnB : n ≤ B) (hNB : n ^ k ≤ B) (h0 : regs₀.getD 0 0 = n)
    (hinv : LoopInv n B base k regs₀ us t regs) (g : Fin (n ^ k)) :
    ∃ regs₃, P.Reaches w (P.Oblivious B) (b + k + 7, 0 :: regs.set (base + 2 * k) g)
      (b + 2 * k + 7, 0 :: regs₃) ∧
      LoopMid n B base k regs₀ us (finFunctionFinEquiv.symm g) t regs₃ := by
  obtain ⟨-, -, -, -, -, hc, -⟩ := tcCode_parts hP
  have hlen := hinv.le_length
  obtain ⟨regs₃, hr, hlen₃, hout, hin, hB₃⟩ := reaches_digits (w := w) hc (by omega)
    (by omega) (regs := regs.set (base + 2 * k) g) (by rw [List.length_set]; omega)
    (by rw [List.getD_set_ne (by omega)]; exact (hinv.kept.getD_eq 0 hbase).trans h0) hnB
    (List.forall_mem_set_of_forall_mem hinv.kept.bounded (g.isLt.le.trans hNB)) g
    (List.getD_set_self (by omega))
  refine ⟨regs₃, by rw [show b + 2 * k + 7 = b + k + 7 + k by omega]; exact hr,
    ⟨⟨?_, ?_, hB₃⟩, ?_, ?_, ?_⟩, hin⟩
  · rw [hlen₃, List.length_set, hinv.kept.length_eq]
  · intro j hj
    rw [hout j (by omega), List.getD_set_ne (by omega), hinv.kept.getD_eq j hj]
  · rw [hlen₃, List.length_set]; exact hlen
  · intro i
    rw [hout _ (by omega), List.getD_set_ne (by omega), hinv.cur i]
  · rw [hout _ (by omega), List.getD_set_ne (by omega), hinv.counter]

variable {E : (Fin k → Fin n) → (Fin k → Fin n) → Prop} {s₀ : Fin k → Fin n}

/-- **Soundness of the closure loop**: from a state with step counter `t ≤ M₀` and current tuple
reachable from `s₀` within `t` steps, every branch either rejects or reaches `T` with the target
`z₀` reachable from `s₀` within `M₀` steps. -/
theorem loop_sound (hP : P.CodeAt b (tcCode b base k src dst M body T R)) (hbase : 0 < base)
    (hB1 : 1 ≤ B) (hnB : n ≤ B) (hNB : n ^ k ≤ B) (hMB : M₀ ≤ B) (h0 : regs₀.getD 0 0 = n)
    (hR : (P.instr R).halts = true) (hPost : ∀ s : Config, s.1 = R → Post s)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ i, (dst i).eval regs = z₀ i)
    (hM : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → M.eval regs = M₀)
    (hbody : ∀ us ws t regs₃, LoopMid n B base k regs₀ us ws t regs₃ →
      Sound P w B Post (b + 2 * k + 7) regs₃ (b + 2 * k + 7 + body.length)
        (fun regs' => Kept B (base + 2 * k + 2) regs₃ regs' ∧ E us ws)) :
    ∀ e t us regs, M₀ - t = e → t ≤ M₀ → LoopInv n B base k regs₀ us t regs →
      Relation.RelatesWithinSteps E s₀ us t →
      Sound P w B Post (b + k + 1) regs T
        (fun regs' => Kept B base regs₀ regs' ∧ Relation.RelatesWithinSteps E s₀ z₀ M₀) := by
  obtain ⟨-, -, -, -, hguess, -⟩ := tcCode_parts hP
  intro e
  induction e with
  | zero =>
    intro t us regs he ht hinv hpath
    by_cases heq : us = z₀
    · exact Sound.of_oblivious hB1 (loop_test_eq hP hinv hdst heq)
        (Sound.exit ⟨hinv.kept, heq ▸ hpath.mono ht⟩)
    · refine Sound.of_oblivious hB1
        ((loop_test_ne hP hinv hdst heq).trans (loop_bound_ge hP hM hinv (by omega))) ?_
      exact Sound.halt hB1 hR (fun _ => hPost _ rfl) hinv.kept.bounded
  | succ e ih =>
    intro t us regs he ht hinv hpath
    by_cases heq : us = z₀
    · exact Sound.of_oblivious hB1 (loop_test_eq hP hinv hdst heq)
        (Sound.exit ⟨hinv.kept, heq ▸ hpath.mono ht⟩)
    refine Sound.of_oblivious hB1
      ((loop_test_ne hP hinv hdst heq).trans (loop_bound_lt hP hM hinv (by omega))) ?_
    have hNe := eval_pow_reg0 (k := k) ((hinv.kept.getD_eq 0 hbase).trans h0)
    refine (Sound.guess hB1 hguess hR hPost (by have := hinv.le_length; omega)
      (fun y => by simp only [eval_pow, eval_reg]; rw [List.getD_set_ne (by omega)])
      (hNe ▸ hNB) hinv.kept.bounded).bind ?_
    rintro _ ⟨m, hm, rfl⟩
    rw [hNe] at hm
    obtain ⟨regs₃, hr₃, hmid⟩ := loop_decode hP hbase hnB hNB h0 hinv ⟨m, hm⟩
    refine Sound.of_oblivious hB1 hr₃ ((hbody us _ t regs₃ hmid).bind fun regs₄ ⟨hk₄, hE⟩ => ?_)
    obtain ⟨regs₅, hr₅, hinv₅⟩ := loop_copy (w := w) hP hmid hk₄ (by omega)
    exact Sound.of_oblivious hB1 hr₅ (ih (t + 1) _ regs₅ (by omega) (by omega) hinv₅
      (hpath.trans (Relation.RelatesWithinSteps.single hE)))

/-- **Completeness of the closure loop**: from a state with step counter `t`, a path of `m` steps
to the target with `t + m ≤ M₀` gives a branch reaching `T`. -/
theorem loop_complete (hP : P.CodeAt b (tcCode b base k src dst M body T R)) (hbase : 0 < base)
    (hnB : n ≤ B) (hNB : n ^ k ≤ B) (hMB : M₀ ≤ B) (h0 : regs₀.getD 0 0 = n)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ i, (dst i).eval regs = z₀ i)
    (hM : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → M.eval regs = M₀)
    (hbody : ∀ us ws t regs₃, LoopMid n B base k regs₀ us ws t regs₃ → E us ws →
      Complete P w (b + 2 * k + 7) regs₃ (b + 2 * k + 7 + body.length)
        (Kept B (base + 2 * k + 2) regs₃)) :
    ∀ m t us regs, Relation.RelatesInSteps E us z₀ m → t + m ≤ M₀ →
      LoopInv n B base k regs₀ us t regs →
      Complete P w (b + k + 1) regs T (Kept B base regs₀) := by
  obtain ⟨-, -, -, -, hguess, -⟩ := tcCode_parts hP
  intro m
  induction m with
  | zero =>
    intro t us regs h ht hinv
    exact Complete.of_oblivious (loop_test_eq hP hinv hdst h.zero) (Complete.refl hinv.kept)
  | succ m ih =>
    intro t us regs h ht hinv
    by_cases heq : us = z₀
    · exact Complete.of_oblivious (loop_test_eq hP hinv hdst heq) (Complete.refl hinv.kept)
    obtain ⟨u₁, he, hrest⟩ := h.succ'
    refine Complete.of_oblivious
      ((loop_test_ne hP hinv hdst heq).trans (loop_bound_lt hP hM hinv (by omega))) ?_
    have hNe := eval_pow_reg0 (k := k) ((hinv.kept.getD_eq 0 hbase).trans h0)
    refine (Complete.guess hguess (by have := hinv.le_length; omega)
      (fun y => by simp only [eval_pow, eval_reg]; rw [List.getD_set_ne (by omega)])
      (hNe ▸ hNB) hinv.kept.bounded (m := finFunctionFinEquiv u₁)
      (by rw [hNe]; exact (finFunctionFinEquiv u₁).isLt)).bind ?_
    rintro _ rfl
    obtain ⟨regs₃, hr₃, hmid⟩ := loop_decode hP hbase hnB hNB h0 hinv (finFunctionFinEquiv u₁)
    rw [Equiv.symm_apply_apply] at hmid
    refine Complete.of_oblivious hr₃ ((hbody us u₁ t regs₃ hmid he).bind fun regs₄ hk₄ => ?_)
    obtain ⟨regs₅, hr₅, hinv₅⟩ := loop_copy (w := w) hP hmid hk₄ (by omega)
    exact Complete.of_oblivious hr₅ (ih (t + 1) u₁ regs₅ hrest (by omega) hinv₅)

end Loop

end Cslib.Logic.FO.Ordered.TCModelChecker
