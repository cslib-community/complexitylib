/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Shift
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Sound and complete blocks of nondeterministic counter code

Compositional reasoning for nondeterministic counter programs whose choice bit is register `0`.
`Block.Sound P w B Post l regs T G` says that every branch from label `l`, with registers `regs`
above the choice, halts in a configuration satisfying `Post` or reaches label `T` with registers
satisfying `G`, keeping all registers at most `B`. `Block.Complete P w l regs T G` says that,
whatever the current choice bit, some branch reaches `T` with registers satisfying `G`. Both
compose sequentially and absorb shifted deterministic code; `guessCode` guesses a register value
below a bound.

## Main definitions

* `Turing.CounterProgram.Block.Sound`, `Turing.CounterProgram.Block.Complete`: block contracts.
* `Turing.CounterProgram.Block.guessCode`: nondeterministically guess a bounded value.

## Main results

* `Turing.CounterProgram.Block.Sound.bind`, `Turing.CounterProgram.Block.Complete.bind`:
  sequential composition.
* `Turing.CounterProgram.Block.Sound.guess`, `Turing.CounterProgram.Block.Complete.guess`: the
  guessed value is any number below the bound.
-/

public section

namespace Turing

namespace CounterProgram

namespace Block

variable {P : CounterProgram} {w : List Bool} {B : ℕ} {Post : Config → Prop}

variable (P w B Post) in
/-- `Sound l regs T G`: from the label `l` with the registers `regs` above the choice, every
branch halts satisfying `Post` or reaches the label `T` with registers satisfying `G` above the
choice, keeping its registers at most `B`. -/
@[expose] def Sound (l : ℕ) (regs : List ℕ) (T : ℕ) (G : List ℕ → Prop) : Prop :=
  ∀ c : Bool, P.AllBranches w B Post
    (fun s => ∃ (c' : Bool) (regs' : List ℕ), s = (T, c'.toNat :: regs') ∧ G regs')
    (l, c.toNat :: regs)

variable (P w) in
/-- `Complete l regs T G`: from the label `l` with the registers `regs` above the choice, whatever
the choice, some branch reaches the label `T` with registers satisfying `G` above the choice. -/
@[expose] def Complete (l : ℕ) (regs : List ℕ) (T : ℕ) (G : List ℕ → Prop) : Prop :=
  ∃ regs', G regs' ∧ ∀ c : Bool, ∃ c' : Bool,
    Branches (P := P) (w := w) (l, c.toNat :: regs) (T, c'.toNat :: regs')

/-- Transport an instruction fact along an equality of labels, for labels computed by `omega`. -/
theorem instr_of_eq {l l' : ℕ} {i : Instr} (h : P.instr l = i) (hl : l = l') :
    P.instr l' = i := hl ▸ h

/-- Transport a code-placement fact along an equality of labels. -/
theorem codeAt_of_eq {l l' : ℕ} {c : List Instr} (h : P.CodeAt l c) (hl : l = l') :
    P.CodeAt l' c := hl ▸ h

private theorem forall_mem_cons_toNat {c : Bool} {regs : List ℕ} (hB : 1 ≤ B)
    (h : ∀ r ∈ regs, r ≤ B) :
    ∀ r ∈ c.toNat :: regs, r ≤ B := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | hr
  · cases c
    · exact Nat.zero_le B
    · exact hB
  · exact h r hr

theorem _root_.Turing.CounterProgram.Reaches.sassign {B c l i next : ℕ} {e : Expr}
    {regs : List ℕ} {s' : Config} (hl : P.instr l = (Instr.assign i e next).shift) (hc : c ≤ B)
    (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.Reaches w (P.Oblivious B) (next, c :: regs.set i (e.eval regs)) s') :
    P.Reaches w (P.Oblivious B) (l, c :: regs) s' :=
  Reaches.oassign hl (by omega) (Expr.readsChoice_shift e)
    (fun r hr => by
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hc
      · exact hB r hr)
    (by simpa using h)

theorem _root_.Turing.CounterProgram.Reaches.slt {B c l yes no : ℕ} {x y : Expr}
    {regs : List ℕ} {s' : Config} (hl : P.instr l = (Instr.lt x y yes no).shift) (hc : c ≤ B)
    (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.Reaches w (P.Oblivious B)
      (if x.eval regs < y.eval regs then yes else no, c :: regs) s') :
    P.Reaches w (P.Oblivious B) (l, c :: regs) s' :=
  Reaches.olt hl (Expr.readsChoice_shift x) (Expr.readsChoice_shift y)
    (fun r hr => by
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hc
      · exact hB r hr)
    (by simpa using h)

namespace Sound

variable {l T T' : ℕ} {regs : List ℕ} {G G' : List ℕ → Prop}

theorem bind (h : Sound P w B Post l regs T G)
    (h' : ∀ regs', G regs' → Sound P w B Post T regs' T' G') :
    Sound P w B Post l regs T' G' := fun c =>
  (h c).bind fun _ ⟨c', regs', hs, hG⟩ => hs ▸ h' regs' hG c'

theorem mono (h : Sound P w B Post l regs T G) (hG : ∀ regs', G regs' → G' regs') :
    Sound P w B Post l regs T G' := fun c =>
  (h c).mono fun _ ⟨c', regs', hs, hG'⟩ => ⟨c', regs', hs, hG regs' hG'⟩

theorem exit (hG : G regs) : Sound P w B Post l regs l G := fun c => .exit ⟨c, regs, rfl, hG⟩

/-- A halting label satisfying `Post`. -/
theorem halt (hB : 1 ≤ B) (hl : (P.instr l).halts = true)
    (hPost : ∀ c : Bool, Post (l, c.toNat :: regs)) (hregs : ∀ r ∈ regs, r ≤ B) :
    Sound P w B Post l regs T G := fun c =>
  .halt hl (hPost c) (forall_mem_cons_toNat hB hregs)

/-- Oblivious deterministic code, above the choice. -/
theorem of_oblivious (hB : 1 ≤ B) {l' : ℕ} {regs' : List ℕ}
    (hr' : P.Reaches w (P.Oblivious B) (l, 0 :: regs) (l', 0 :: regs'))
    (h : Sound P w B Post l' regs' T G) : Sound P w B Post l regs T G := by
  intro c
  have := allBranches_of_oblivious (Post := Post) hB hr'
    (Q := fun s => P.AllBranches w B Post
      (fun s => ∃ (c' : Bool) (regs' : List ℕ), s = (T, c'.toNat :: regs') ∧ G regs') s)
    (fun c' => h c') c
  exact this.bind fun _ h => h

/-- Deterministic code placed by `padded`, shifted above the choice. -/
theorem of_reaches (hB : 1 ≤ B) {b : ℕ} {code : List Instr}
    (hP : P.CodeAt b (code.map Instr.shift)) {l' : ℕ} {regs' : List ℕ}
    (hr : (padded b code).Reaches w ((padded b code).Running B) (l, regs) (l', regs'))
    (h : Sound P w B Post l' regs' T G) : Sound P w B Post l regs T G :=
  of_oblivious hB (Reaches.unpad (w := w) (c := 0) (Nat.zero_le B) hP hr) h

/-- A choice: the label `yes` on the choice `false`, and `no` on `true`. -/
theorem choice (hB : 1 ≤ B) {yes no : ℕ}
    (hl : P.instr l = .lt (.reg 0) (.const 1) yes no) (hregs : ∀ r ∈ regs, r ≤ B)
    (hyes : Sound P w B Post yes regs T G) (hno : Sound P w B Post no regs T G) :
    Sound P w B Post l regs T G := by
  intro c
  have hh : P.halted (l, c.toNat :: regs) = false := by simp [halted, hl, Instr.halts]
  refine .step hh (forall_mem_cons_toNat hB hregs) fun c' => ?_
  rw [P.step_lt w hl]
  cases c <;> simp only [Expr.eval_reg, Expr.eval_const, List.getD_cons_zero, Bool.toNat_false,
    Bool.toNat_true, Nat.lt_irrefl, zero_lt_one, ↓reduceIte, withChoice, List.set_cons_zero]
  · exact hyes c'
  · exact hno c'

end Sound

namespace Complete

variable {l T T' : ℕ} {regs : List ℕ} {G G' : List ℕ → Prop}

theorem refl (hG : G regs) : Complete P w l regs l G :=
  ⟨regs, hG, fun c => ⟨c, Branches.refl _⟩⟩

theorem mono (h : Complete P w l regs T G) (hG : ∀ regs', G regs' → G' regs') :
    Complete P w l regs T G' :=
  let ⟨regs', hG', h'⟩ := h
  ⟨regs', hG regs' hG', h'⟩

theorem bind (h : Complete P w l regs T G)
    (h' : ∀ regs', G regs' → Complete P w T regs' T' G') : Complete P w l regs T' G' := by
  obtain ⟨regs₁, hG₁, h₁⟩ := h
  obtain ⟨regs₂, hG₂, h₂⟩ := h' regs₁ hG₁
  refine ⟨regs₂, hG₂, fun c => ?_⟩
  obtain ⟨c₁, hc₁⟩ := h₁ c
  obtain ⟨c₂, hc₂⟩ := h₂ c₁
  exact ⟨c₂, hc₁.trans hc₂⟩

/-- Oblivious deterministic code, above the choice. -/
theorem of_oblivious {B : ℕ} {l' : ℕ} {regs' : List ℕ}
    (hr' : P.Reaches w (P.Oblivious B) (l, 0 :: regs) (l', 0 :: regs'))
    (h : Complete P w l' regs' T G) : Complete P w l regs T G := by
  obtain ⟨regs₂, hG, h₂⟩ := h
  refine ⟨regs₂, hG, fun c => ?_⟩
  obtain ⟨c₂, hc₂⟩ := h₂ c
  have := branches_of_oblivious hr' c c fun _ => rfl
  exact ⟨c₂, this.trans hc₂⟩

/-- Deterministic code placed by `padded`, shifted above the choice. -/
theorem of_reaches {B : ℕ} {b : ℕ} {code : List Instr}
    (hP : P.CodeAt b (code.map Instr.shift)) {l' : ℕ} {regs' : List ℕ}
    (hr : (padded b code).Reaches w ((padded b code).Running B) (l, regs) (l', regs'))
    (h : Complete P w l' regs' T G) : Complete P w l regs T G :=
  of_oblivious (Reaches.unpad (w := w) (c := 0) (Nat.zero_le B) hP hr) h

/-- A step of deterministic code into a choice, then the branch of either label. -/
theorem choice {B : ℕ} {l' : ℕ} {regs' : List ℕ}
    (hr' : P.Reaches w (P.Oblivious B) (l, 0 :: regs) (l', 0 :: regs'))
    (hne : l ≠ l') {yes no : ℕ} (hl : P.instr l' = .lt (.reg 0) (.const 1) yes no)
    (h : Complete P w yes regs' T G ∨ Complete P w no regs' T G) :
    Complete P w l regs T G := by
  have hh : ∀ c : Bool, P.halted (l', c.toNat :: regs') = false := fun c => by
    simp [halted, hl, Instr.halts]
  have hstep : ∀ c c' : Bool, Branches (P := P) (w := w) (l', c.toNat :: regs')
      (cond c no yes, c'.toNat :: regs') := fun c c' => by
    have := Branches.single (P := P) (w := w) (hh c) c'
    rw [P.step_lt w hl] at this
    cases c <;> simpa [withChoice] using this
  rcases h with ⟨regs₂, hG, h₂⟩ | ⟨regs₂, hG, h₂⟩
  · refine ⟨regs₂, hG, fun c => ?_⟩
    obtain ⟨c₂, hc₂⟩ := h₂ false
    have := branches_of_oblivious hr' c false fun h => absurd (congrArg Prod.fst h) hne
    exact ⟨c₂, (this.trans (hstep false false)).trans hc₂⟩
  · refine ⟨regs₂, hG, fun c => ?_⟩
    obtain ⟨c₂, hc₂⟩ := h₂ true
    have := branches_of_oblivious hr' c true fun h => absurd (congrArg Prod.fst h) hne
    exact ⟨c₂, (this.trans (hstep true true)).trans hc₂⟩

end Complete

/-- **A guess** of register `x` (above the choice) below the value of `N`: set it to `0`, then
while it is below `N`, either stop at `E` or increment it; reject at `R` when it reaches `N`. -/
@[expose] def guessCode (b x : ℕ) (N : Expr) (E R : ℕ) : List Instr :=
  [(Instr.assign x (.const 0) (b + 1)).shift,
   (Instr.lt (.reg x) N (b + 2) R).shift,
   .lt (.reg 0) (.const 1) E (b + 3),
   (Instr.assign x (.add (.reg x) (.const 1)) (b + 1)).shift]

theorem length_guessCode (b x : ℕ) (N : Expr) (E R : ℕ) : (guessCode b x N E R).length = 4 :=
  rfl

private theorem guessCode_instr {b x E R : ℕ} {N : Expr} (hP : P.CodeAt b (guessCode b x N E R)) :
    P.instr b = (Instr.assign x (.const 0) (b + 1)).shift ∧
    P.instr (b + 1) = (Instr.lt (.reg x) N (b + 2) R).shift ∧
    P.instr (b + 2) = .lt (.reg 0) (.const 1) E (b + 3) ∧
    P.instr (b + 3) = (Instr.assign x (.add (.reg x) (.const 1)) (b + 1)).shift :=
  ⟨hP 0 (by simp [guessCode]), hP 1 (by simp [guessCode]), hP 2 (by simp [guessCode]),
    hP 3 (by simp [guessCode])⟩

/-- Every branch of a guess reaches `E` with a value below `N`, or rejects. -/
theorem Sound.guess (hB : 1 ≤ B) {b x E R : ℕ} {N : Expr} (hP : P.CodeAt b (guessCode b x N E R))
    (hR : (P.instr R).halts = true) (hPost : ∀ s : Config, s.1 = R → Post s)
    {regs : List ℕ} (hx : x < regs.length)
    (hN : ∀ y, N.eval (regs.set x y) = N.eval regs)
    (hNB : N.eval regs ≤ B) (hregs : ∀ r ∈ regs, r ≤ B) :
    Sound P w B Post b regs E (fun regs' => ∃ m < N.eval regs, regs' = regs.set x m) := by
  obtain ⟨h0, h1, h2, h3⟩ := guessCode_instr hP
  have hset : ∀ m ≤ N.eval regs, ∀ r ∈ regs.set x m, r ≤ B := fun m hm =>
    List.forall_mem_set_of_forall_mem hregs (hm.trans hNB)
  have key : ∀ e m, N.eval regs - m = e → m ≤ N.eval regs →
      Sound P w B Post (b + 1) (regs.set x m) E
        (fun regs' => ∃ m < N.eval regs, regs' = regs.set x m) := by
    intro e
    induction e with
    | zero =>
      intro m he hm
      refine Sound.of_oblivious hB (Reaches.slt h1 (Nat.zero_le B) (hset m hm) (Reaches.refl _)) ?_
      have : ¬ (Expr.reg x).eval (regs.set x m) < N.eval (regs.set x m) := by
        rw [Expr.eval_reg, List.getD_set_self hx, hN]; omega
      simp only [this, ↓reduceIte]
      exact Sound.halt hB hR (fun c => hPost _ rfl) (hset m hm)
    | succ e ih =>
      intro m he hm
      have hmN : m < N.eval regs := by omega
      refine Sound.of_oblivious hB (Reaches.slt h1 (Nat.zero_le B) (hset m hm) (Reaches.refl _)) ?_
      have : (Expr.reg x).eval (regs.set x m) < N.eval (regs.set x m) := by
        rw [Expr.eval_reg, List.getD_set_self hx, hN]; exact hmN
      simp only [this, ↓reduceIte]
      refine Sound.choice hB h2 (hset m hm) (Sound.exit ⟨m, hmN, rfl⟩) ?_
      refine Sound.of_oblivious hB
        (Reaches.sassign h3 (Nat.zero_le B) (hset m hm) (Reaches.refl _)) ?_
      simp only [Expr.eval_add, Expr.eval_reg, Expr.eval_const, List.getD_set_self hx,
        List.set_set]
      exact ih (m + 1) (by omega) (by omega)
  refine Sound.of_oblivious hB (Reaches.sassign h0 (Nat.zero_le B) hregs (Reaches.refl _)) ?_
  exact key _ 0 rfl (Nat.zero_le _)

/-- Some branch of a guess reaches `E` with any value below `N`. -/
theorem Complete.guess {b x E R : ℕ} {N : Expr} (hP : P.CodeAt b (guessCode b x N E R))
    {regs : List ℕ} (hx : x < regs.length)
    (hN : ∀ y, N.eval (regs.set x y) = N.eval regs)
    (hNB : N.eval regs ≤ B) (hregs : ∀ r ∈ regs, r ≤ B) {m : ℕ} (hm : m < N.eval regs) :
    Complete P w b regs E (· = regs.set x m) := by
  obtain ⟨h0, h1, h2, h3⟩ := guessCode_instr hP
  have hset : ∀ j ≤ N.eval regs, ∀ r ∈ regs.set x j, r ≤ B := fun j hj =>
    List.forall_mem_set_of_forall_mem hregs (hj.trans hNB)
  have key : ∀ e j, m - j = e → j ≤ m →
      Complete P w (b + 1) (regs.set x j) E (· = regs.set x m) := by
    intro e
    induction e with
    | zero =>
      intro j he hj
      obtain rfl : j = m := by omega
      have : (Expr.reg x).eval (regs.set x j) < N.eval (regs.set x j) := by
        rw [Expr.eval_reg, List.getD_set_self hx, hN]; exact hm
      refine Complete.choice (B := B) (Reaches.slt h1 (Nat.zero_le B) (hset j hm.le)
        (by simp only [this, ↓reduceIte]; exact Reaches.refl _)) (by omega) h2
        (Or.inl (Complete.refl rfl))
    | succ e ih =>
      intro j he hj
      have : (Expr.reg x).eval (regs.set x j) < N.eval (regs.set x j) := by
        rw [Expr.eval_reg, List.getD_set_self hx, hN]; omega
      refine Complete.choice (B := B) (Reaches.slt h1 (Nat.zero_le B) (hset j (by omega))
        (by simp only [this, ↓reduceIte]; exact Reaches.refl _)) (by omega) h2 (Or.inr ?_)
      refine Complete.of_oblivious (B := B)
        (Reaches.sassign h3 (Nat.zero_le B) (hset j (by omega)) (Reaches.refl _)) ?_
      simp only [Expr.eval_add, Expr.eval_reg, Expr.eval_const, List.getD_set_self hx,
        List.set_set]
      exact ih (j + 1) (by omega) (by omega)
  refine Complete.of_oblivious (B := B)
    (Reaches.sassign h0 (Nat.zero_le B) hregs (Reaches.refl _)) ?_
  exact key _ 0 rfl (Nat.zero_le _)

end Block

end CounterProgram

end Turing
