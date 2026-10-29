/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate
-- Preserve the compiler and bounds from crei:crei/tidy-universal @9cce4cc7.
-- vendored: `spaceUsed` is `space` since cslib #1133; `transformsTapes_inputFromWord` is
-- `transformsTapes_inputFromWord_fun`, as the name is taken by a run-path lemma here; `flagWord`
-- is `stepFlagWord`, as `Encodings/MultiPass` declares the same function

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.StepMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OnWords
public import Complexity.Computability.Machines.Turing.MultiTape.StepMachine.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step machines with plain resource certificates

The halting test, step and initial state have charged plain resource certificates. Their
realizing machines are normalized only within this internal compiler proof. The input head stays
where the step machine has it between rounds, so each round pays for its callbacks and state,
not a new traversal of the whole input.

Whole-run conclusions use independent, uncharged `ComputableInBigO` bounds. An emitter may write
an unbounded output with constant workspace; no bound on the whole output is added.

## Main definitions

* `Turing.MultiTapeTM.encMove`, `.encPeek`: the unchanged encodings used by the compiler.
* `Turing.StepMachine.ResourceCertificate`: charged plain certificates for halt and step.

## Main results

* `Turing.StepMachine.ResourceCertificate.computableInBigO_of_init`: compile a computed initial
  state, retaining the original time/workspace formulas and halting/output hypotheses.
* `Turing.StepMachine.ResourceCertificate.computableInBigO`: the fixed-initial-state case.
-/

namespace Turing.MultiTapeTM

/-! ### A flag as a word -/

/-- A flag as a word: `[true]` if set, blank otherwise. -/
@[expose] public def stepFlagWord (b : Bool) : List Bool := if b then [true] else []

public lemma linear_stepFlagWord :
    ComputableInLinearTimeAndSpace stepFlagWord encBool encBits :=
  .of_finite stepFlagWord

/-- Moves of the input head: none, to the left, to the right. -/
@[expose] public def encMove : SignType ↪ List Bool :=
  ⟨fun m => match m with | .zero => [] | .neg => [false] | .pos => [true], by
    intro a b h
    cases a <;> cases b <;> simp_all⟩

@[simp] public lemma moveOfCell_encMove (m : SignType) : moveOfCell (encMove m).head? = m := by
  cases m <;> rfl

public lemma peekWord_injective : Function.Injective peekWord := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => simp [peekWord] at h
  | some a => cases b with
    | none => simp [peekWord] at h
    | some b => simp_all [peekWord]

/-- A value behind the symbol under the input head, recorded by `peekWord`. -/
@[expose] public def encPeek {τ : Type*} (enc : τ ↪ List Bool) : Option Bool × τ ↪ List Bool :=
  ⟨fun p => peekWord p.1 ++ enc p.2, fun p q h => by
    have h₂ := List.append_inj h rfl
    exact Prod.ext (peekWord_injective h₂.1) (enc.injective h₂.2)⟩

@[simp] public lemma encPeek_apply {τ : Type*} (enc : τ ↪ List Bool) (p : Option Bool × τ) :
    encPeek enc p = peekWord p.1 ++ enc p.2 := rfl

/-! ### Converting to and from `encPeek` -/

/-- Drops the first two symbols. -/
@[simps q₀ step final]
def dropTwoT : Transducer Bool (Fin 3) where
  q₀ := 0
  step q b := if q = 2 then (2, [b]) else (q + 1, [])
  final _ := []
  length_step_le q b := by split_ifs <;> simp
  length_final_le _ := by simp

lemma dropTwoT_run_two (w : List Bool) : dropTwoT.run 2 w = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]

/-- Reads the symbol recorded in the first two cells. -/
@[simps q₀ step final]
def peekSymT : Transducer Bool (Fin 4) where
  q₀ := 0
  step q b := match q, b with
    | 0, false => (1, [])
    | 0, true => (2, [])
    | 2, b => (3, [true, b])
    | _, _ => (3, [])
  final _ := []
  length_step_le q b := by split <;> simp
  length_final_le _ := by simp

lemma peekSymT_run_three (w : List Bool) : peekSymT.run 3 w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]

/-- Puts the two cells of `slot` in front, with one symbol of delay. -/
@[simps q₀ step final]
def slotT : Transducer Bool (Option Bool) where
  q₀ := none
  step q b := (some b, q.elim [false, false] fun c => [c])
  final q := q.elim [false, false] fun c => [c]
  length_step_le q b := by cases q <;> simp
  length_final_le q := by cases q <;> simp

lemma slotT_run_some (c : Bool) (w : List Bool) : slotT.run (some c) w = c :: w := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih => simp [ih]

open ComputableInO

variable {τ : Type} {enc : τ ↪ List Bool}

/-- The value behind the recorded symbol. -/
public lemma peek_snd : ComputableInO Prod.snd (encPeek enc) enc
    (fun p => (encPeek enc p).length) fun p => (encPeek enc p).length :=
  of_linear (ComputableInLinearTimeAndSpace.of_transducer dropTwoT fun p => by
    obtain ⟨_ | b, t⟩ := p <;> simp [peekWord, dropTwoT_run_two])

/-- The recorded symbol. -/
public lemma peek_fst : ComputableInO Prod.fst (encPeek enc) (encOption encBool)
    (fun p => (encPeek enc p).length) fun p => (encPeek enc p).length :=
  of_linear (ComputableInLinearTimeAndSpace.of_transducer peekSymT fun p => by
    obtain ⟨_ | b, t⟩ := p <;> simp [peekWord, peekSymT_run_three])

/-- No symbol recorded in front of a value. -/
public lemma peek_none : ComputableInO (fun t => ((none : Option Bool), t)) enc (encPeek enc)
    (fun t => (enc t).length) fun t => (enc t).length :=
  of_linear (ComputableInLinearTimeAndSpace.of_transducer slotT fun t => by
    cases h : enc t with
    | nil => simp [h, peekWord]
    | cons b w => simp [h, peekWord, slotT_run_some])

/-! ### The parts of a round -/

section Parts

variable {σ : Type} {encS : σ ↪ List Bool} {halt : σ → Bool}
  {step : σ → Option Bool → σ × SignType × List Bool} {TH SH : σ → ℕ}
  {TS SS : σ × Option Bool → ℕ}

/-- The state and its pending move. -/
public abbrev encAug (encS : σ ↪ List Bool) : σ × SignType ↪ List Bool := encPair encS encMove

/-- The step, read from the state behind the symbol under the input head. -/
lemma step_peek_inO
    (hstep : ComputableInO (fun p : σ × Option Bool => step p.1 p.2)
      (encPair encS (encOption encBool)) (encPair encS (encPair encMove encBits)) TS SS) :
    ComputableInO (fun p : Option Bool × (σ × SignType) => step p.2.1 p.1)
      (encPeek (encAug encS)) (encPair encS (encPair encMove encBits))
      (fun p => (encPeek (encAug encS) p).length + (encPeek (encAug encS) p).length +
        TS (p.2.1, p.1))
      fun p => (encPeek (encAug encS) p).length + (encPeek (encAug encS) p).length +
        SS (p.2.1, p.1) :=
  hstep.comp (peek_snd.fst'.prod peek_fst)

end Parts

/-- The time of a step machine, simplified. -/
lemma step_time_le (cI D TI w R Tm L P₁ P₂ S : ℕ) (hcI : cI ≤ D) (hD : 100 ≤ D)
    (hP₁ : P₁ ≤ 2 * L + 4) (hP₂ : P₂ ≤ 2 * L + 4) (hS : S ≤ R * (100 * (D * (Tm + L + 1)))) :
    cI * (TI + w + 1) + P₁ + 2 + (D * (Tm + 2 * L + 5) + 7) + (S + 1 + (3 * (P₂ + 1) + (w + 2)))
      ≤ 1000 * D * D * (TI + (R + 1) * (Tm + L + 1) + w) := by
  set Y := TI + (R + 1) * (Tm + L + 1) + w
  have hX : Tm + L + 1 ≤ Y := by
    have : Tm + L + 1 ≤ (R + 1) * (Tm + L + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hRX : R * (Tm + L + 1) ≤ Y := by
    have : R * (Tm + L + 1) ≤ (R + 1) * (Tm + L + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have h₁ : cI * (TI + w + 1) ≤ D * (2 * Y) := Nat.mul_le_mul hcI (by omega)
  have h₂ : D * (Tm + 2 * L + 5) ≤ D * (5 * Y) := Nat.mul_le_mul_left _ (by omega)
  have h₃ : S ≤ 100 * (D * Y) := hS.trans (by
    calc R * (100 * (D * (Tm + L + 1))) = 100 * (D * (R * (Tm + L + 1))) := by ring
      _ ≤ 100 * (D * Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hRX))
  have hY : 1 ≤ Y := by omega
  have h₄ : D * Y ≤ D * D * Y := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have h₅ : Y ≤ D * Y := Nat.le_mul_of_pos_left _ (by omega)
  have e : D * (2 * Y) = 2 * (D * Y) := by ring
  have e' : D * (5 * Y) = 5 * (D * Y) := by ring
  have e'' : 1000 * D * D * Y = 1000 * (D * D * Y) := by ring
  rw [e'']
  omega

/-- The space of a step machine, simplified. -/
lemma step_space_le (cI D SI Sm L K P P₂ sR : ℕ) (hcI : cI ≤ D) (hD : 100 ≤ D) (hK : K ≤ D)
    (hP : P ≤ 2 * L + 4) (hP₂ : P₂ ≤ 2 * L + 4) (hsR : sR ≤ 200 * (D * (Sm + L + 1))) :
    cI * (SI + 0 + 1) + 2 * P + 2 * K + 3 + (D * (Sm + 2 * L + 5) + 4 * L + 30 + 4 * K) +
      (2 * K * sR + K + (P₂ + 1 + K + K)) ≤ 1000 * D * D * (SI + Sm + L + 1) := by
  set Y := SI + Sm + L + 1
  have h₁ : cI * (SI + 0 + 1) ≤ D * Y := Nat.mul_le_mul hcI (by omega)
  have h₂ : D * (Sm + 2 * L + 5) ≤ D * (5 * Y) := Nat.mul_le_mul_left _ (by omega)
  have h₃ : 2 * K * sR ≤ 2 * D * (200 * (D * Y)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hK) (hsR.trans (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ (by omega))))
  have hY : 1 ≤ Y := by omega
  have h₅ : Y ≤ D * Y := Nat.le_mul_of_pos_left _ (by omega)
  have h₄ : D * Y ≤ D * D * Y := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have e : 2 * D * (200 * (D * Y)) = 400 * (D * D * Y) := by ring
  have e' : D * (5 * Y) = 5 * (D * Y) := by ring
  have e'' : 1000 * D * D * Y = 1000 * (D * D * Y) := by ring
  have h₆ : D ≤ D * Y := Nat.le_mul_of_pos_right _ hY
  rw [e] at h₃
  rw [e'] at h₂
  rw [e'']
  omega

/-! ### The theorem -/

/-- **Compile step machines with plain resource-certified components.** Let the step machine
`⟨init x, halt, step⟩` halt on the input `encIn x` after `rounds x` steps with the output
`encOut (g x)`. If `init`, `halt` and `step` have plain resource certificates, then `g` has a tidy
implementation, in time
`O(TI x + (rounds x + 1) * (tMax x + lMax x + 1) + n)` and space `O(SI x + sMax x + lMax x + 1)`,
where `tMax`, `sMax` bound the time and space of `halt` and `step` along the run and `lMax` the
size of the states. The input head is never rewound between steps. -/
private theorem Internal.compileStepMachine {σ γ ω : Type} {encS : σ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} (init : γ → σ) (halt : σ → Bool)
    (step : σ → Option Bool → σ × SignType × List Bool) (g : γ → ω) (rounds : γ → ℕ)
    {TI SI : γ → ℕ} {TH SH : σ → ℕ} {TS SS : σ × Option Bool → ℕ}
    (hinit : ComputableInO init encIn encS TI SI)
    (hhalt : ComputableInO halt encS encBool TH SH)
    (hstep : ComputableInO (fun p : σ × Option Bool => step p.1 p.2)
      (encPair encS (encOption encBool)) (encPair encS (encPair encMove encBits)) TS SS)
    (hrounds : ∀ x, (StepMachine.mk (init x) halt step).HaltsAt (encIn x) (rounds x))
    (hg : ∀ x, encOut (g x) =
      ((StepMachine.mk (init x) halt step).run (encIn x) (rounds x)).out)
    {tMax sMax lMax : γ → ℕ}
    (htMax : ∀ x, ∀ i ≤ rounds x,
      TS (((StepMachine.mk (init x) halt step).run (encIn x) i).state, inputSymbolAt (encIn x)
        ((StepMachine.mk (init x) halt step).run (encIn x) i).pos) +
      TH ((StepMachine.mk (init x) halt step).run (encIn x) i).state ≤ tMax x)
    (hsMax : ∀ x, ∀ i ≤ rounds x,
      SS (((StepMachine.mk (init x) halt step).run (encIn x) i).state, inputSymbolAt (encIn x)
        ((StepMachine.mk (init x) halt step).run (encIn x) i).pos) +
      SH ((StepMachine.mk (init x) halt step).run (encIn x) i).state ≤ sMax x)
    (hlMax : ∀ x, ∀ i ≤ rounds x,
      (encS ((StepMachine.mk (init x) halt step).run (encIn x) i).state).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (TI x + (rounds x + 1) * (tMax x + lMax x + 1) + (encIn x).length))
      (fun x => c * (SI x + sMax x + lMax x + 1)) := by
  -- the parts, on the state behind the symbol under the input head
  have hS := step_peek_inO (encS := encS) hstep
  have fE := hS.snd'.snd'
  have fN := peek_none.comp_linear (hS.fst'.prod hS.snd'.fst')
  have fM := (peek_snd (enc := encAug encS)).snd'
  have fC := (of_linear linear_stepFlagWord).comp_linear
    ((of_linear (ComputableInLinearTimeAndSpace.of_finite
      (encIn := encBool) (encMid := encBool) fun b : Bool => !b)).comp_linear
      (hhalt.comp (peek_snd (enc := encAug encS)).fst'))
  have fI := (peek_none (enc := encAug encS)).comp_linear
    (hinit.prod (ComputableInO.constZero (0 : SignType)))
  obtain ⟨cE, ⟨kE, SE, _, tmE, htmE⟩, -⟩ := Internal.NormalForm.inO fE
  obtain ⟨cN, ⟨kN, SN, _, tmN, htmN⟩, -⟩ := Internal.NormalForm.inO fN
  obtain ⟨cM, ⟨kM, SM, _, tmM, htmM⟩, -⟩ := Internal.NormalForm.inO fM
  obtain ⟨cC, ⟨kC, SC, _, tmC, htmC⟩, -⟩ := Internal.NormalForm.inO fC
  obtain ⟨cI, ⟨kI, SI', _, tmI, htmI⟩, -⟩ := Internal.NormalForm.inO fI
  -- the tapes: those of the machines, then the state `V`, the next state `N`, a flag `F` for
  -- copying, the flag `C` for another round and the move `Mv`
  obtain ⟨M, hM⟩ : ∃ M, M = kI + kE + kN + kM + kC + 8 := ⟨_, rfl⟩
  let V : Fin (M + 5) := ⟨M, by omega⟩
  let N : Fin (M + 5) := ⟨M + 1, by omega⟩
  let F : Fin (M + 5) := ⟨M + 2, by omega⟩
  let C : Fin (M + 5) := ⟨M + 3, by omega⟩
  let Mv : Fin (M + 5) := ⟨M + 4, by omega⟩
  have hVN : V ≠ N := by simp [V, N, Fin.ext_iff]
  have hVF : V ≠ F := by simp [V, F, Fin.ext_iff]
  have hNF : N ≠ F := by simp [N, F, Fin.ext_iff]
  have hVC : V ≠ C := by simp [V, C, Fin.ext_iff]
  have hVM : V ≠ Mv := by simp [V, Mv, Fin.ext_iff]
  obtain ⟨eI, heI⟩ := exists_embedding_eq (K := M + 5) (by omega) (Fin.last kI) V
  obtain ⟨eE, heE⟩ := exists_embedding_eq (K := M + 5) (by omega) (Fin.natAdd kE (0 : Fin 2)) V
  obtain ⟨eN, heN, heN'⟩ := exists_embedding_eq₂ (K := M + 5) (by omega)
    (i := Fin.natAdd (kN + 1) (0 : Fin 2)) (o := (Fin.last kN).castAdd 2)
    (by simp [Fin.ext_iff]) hVN
  obtain ⟨eM, heM, heM'⟩ := exists_embedding_eq₂ (K := M + 5) (by omega)
    (i := Fin.natAdd (kM + 1) (0 : Fin 2)) (o := (Fin.last kM).castAdd 2)
    (by simp [Fin.ext_iff]) hVM
  obtain ⟨eC, heC, heC'⟩ := exists_embedding_eq₂ (K := M + 5) (by omega)
    (i := Fin.natAdd (kC + 1) (0 : Fin 2)) (o := (Fin.last kC).castAdd 2)
    (by simp [Fin.ext_iff]) hVC
  have hI := transformsTapes_outputToWord htmI heI
  have hE := transformsTapes_inputFromWord_fun htmE heE
  have hN := transformsTapes_onWords htmN heN heN'
  have hMm := transformsTapes_onWords htmM heM heM'
  have hC := transformsTapes_onWords (encD := encBits) htmC heC heC'
  set D := cE + cN + cM + cC + cI + M + 100 with hD
  refine ⟨1000 * D * D, _, _, by set_option synthInstance.maxSize 1024 in infer_instance,
    stepTM (tmI.outputToWord.extendTapes eI) ((tmE.inputFromWord true).extendTapes eE)
      ((tmN.onWords true).extendTapes eN) ((tmM.onWords true).extendTapes eM)
      ((tmC.onWords true).extendTapes eC) V N F C Mv hVN hVF hNF, fun x => ?_⟩
  -- the run of the step machine on `x`
  set m := StepMachine.mk (init x) halt step with hm
  set R := rounds x
  set w := encIn x
  let q (i : ℕ) : σ := (m.run w i).state
  let a (i : ℕ) : Option Bool := inputSymbolAt w (m.run w i).pos
  let st (i : ℕ) : σ × SignType × List Bool := step (q i) (a i)
  let mv (i : ℕ) : SignType := if i = 0 then 0 else (st (i - 1)).2.1
  have hnh (i : ℕ) (hi : i < R) : halt (q i) = false := by
    simpa using (hrounds x).2 i hi
  have hrun (i : ℕ) (hi : i < R) : m.run w (i + 1) =
      ⟨(st i).1, moveInputPos (m.run w i).pos (st i).2.1, (m.run w i).out ++ (st i).2.2⟩ :=
    m.run_succ_of_not_halt (hnh i hi)
  have hq (i : ℕ) (hi : i < R) : q (i + 1) = (st i).1 := by simp only [q, hrun i hi]
  -- uniform bounds on the parts
  set L := lMax x
  set Tm := tMax x
  set Sm := sMax x
  have hDK : M + 5 ≤ D := by omega
  have hP (b : Option Bool) (n : ℕ) (hn : n ≤ R) (mm : SignType) :
      (encPeek (encAug encS) (b, (q n, mm))).length ≤ 2 * L + 4 := by
    have : (encS (q n)).length ≤ L := hlMax x n hn
    cases b <;> cases mm <;> simp [peekWord, encMove] <;> omega
  have hst (n : ℕ) (hn : n ≤ R) : TS (q n, a n) + TH (q n) ≤ Tm ∧ SS (q n, a n) + SH (q n) ≤ Sm :=
    ⟨htMax x n hn, hsMax x n hn⟩
  have hfl (n : ℕ) : (stepFlagWord (!halt (q n))).length ≤ 1 := by
    unfold stepFlagWord; split_ifs <;> simp
  have hmv (mm : SignType) : (encMove mm).length ≤ 1 := by cases mm <;> simp [encMove]
  have h := computesTidily_stepTM hVN hVF hNF hVC hVM w R (fun n => encAug encS (q n, mv n))
    (fun n => (st n).2.2) (fun n => encMove (st n).2.1) (fun n => stepFlagWord (!halt (q n)))
    (fun n => (m.run w n).pos) rfl
    (fun n hn => by simp only [hrun n hn, moveOfCell_encMove])
    (fun n hn => by simp [hnh n hn, stepFlagWord])
    (by simpa [stepFlagWord] using (hrounds x).1)
    ((hI x).imp (fun _ _ h => h) (fun _ _ _ _ _ ⟨h, he⟩ => ⟨h.trans rfl, he⟩) le_rfl le_rfl)
    (tE := fun _ => D * (Tm + 4 * L + 10) + 4)
    (sE := fun _ => D * (Sm + 4 * L + 10) + 8 * L + 30 + 3 * (M + 5))
    (tN := fun _ => D * (2 * Tm + 8 * L + 20) + 2 * L + 10)
    (sN := fun _ => D * (2 * Sm + 8 * L + 20) + 12 * L + 40 + 4 * (M + 5))
    (tM := fun _ => D * (2 * L + 5) + 7)
    (sM := fun _ => D * (2 * L + 5) + 4 * L + 30 + 4 * (M + 5))
    (tC := fun _ => D * (Tm + 2 * L + 5) + 7)
    (sC := fun _ => D * (Sm + 2 * L + 5) + 4 * L + 30 + 4 * (M + 5))
    (fun n hn => (hE (a n, (q n, mv n))).imp (fun _ _ h => h)
      (fun _ _ _ _ _ ⟨h, he⟩ => ⟨h, he.trans rfl⟩) (by
        have := hP (a n) n hn.le (mv n); have := (hst n hn.le).1
        exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by dsimp -zeta only; omega)) _) (by
        have := hP (a n) n hn.le (mv n); have := (hst n hn.le).2
        have := Nat.mul_le_mul (show cE ≤ D by omega)
          (show (encPeek (encAug encS) (a n, q n, mv n)).length +
            (encPeek (encAug encS) (a n, q n, mv n)).length + SS (q n, a n) + 1 ≤
              Sm + 4 * L + 10 by omega)
        dsimp -zeta only; omega))
    (fun n hn => (hN (a n, (q n, mv n))).imp (fun _ _ h => h)
      (fun _ _ _ _ _ ⟨h, he⟩ => ⟨by rw [h]; simp [hq n hn, mv, st, peekWord, slot], he⟩) (by
        have := hP (a n) n hn.le (mv n); have := (hst n hn.le).1
        have : (encPeek (encPair encS encMove) (none, (step (q n) (a n)).1,
            (step (q n) (a n)).2.1)).length ≤ 2 * L + 4 := by
          have := hP none (n + 1) hn (step (q n) (a n)).2.1
          rw [hq n hn] at this
          exact this
        have := Nat.mul_le_mul (show cN ≤ D by omega)
          (show (encPeek (encAug encS) (a n, q n, mv n)).length +
            (encPeek (encAug encS) (a n, q n, mv n)).length + TS (q n, a n) +
            ((encPeek (encAug encS) (a n, q n, mv n)).length +
            (encPeek (encAug encS) (a n, q n, mv n)).length + TS (q n, a n)) + 1 ≤
              2 * Tm + 8 * L + 20 by omega)
        dsimp -zeta only; simp only [Function.comp_apply]; omega) (by
        have := hP (a n) n hn.le (mv n); have := (hst n hn.le).2
        have : (encPeek (encPair encS encMove) (none, (step (q n) (a n)).1,
            (step (q n) (a n)).2.1)).length ≤ 2 * L + 4 := by
          have := hP none (n + 1) hn (step (q n) (a n)).2.1
          rw [hq n hn] at this
          exact this
        have := Nat.mul_le_mul (show cN ≤ D by omega)
          (show (encPeek (encAug encS) (a n, q n, mv n)).length +
            (encPeek (encAug encS) (a n, q n, mv n)).length + SS (q n, a n) +
            ((encPeek (encAug encS) (a n, q n, mv n)).length +
            (encPeek (encAug encS) (a n, q n, mv n)).length + SS (q n, a n)) + 1 ≤
              2 * Sm + 8 * L + 20 by omega)
        dsimp -zeta only; simp only [Function.comp_apply]; omega))
    (fun n hn => (hMm (none, (q (n + 1), mv (n + 1)))).imp (fun _ _ h => by rw [h]; rfl)
      (fun _ _ _ _ _ ⟨h, he⟩ => ⟨by rw [h]; simp [mv], he⟩) (by
        have := hP none (n + 1) hn (mv (n + 1)); have := hmv (mv (n + 1))
        have := Nat.mul_le_mul (show cM ≤ D by omega)
          (show (encPeek (encAug encS) (none, q (n + 1), mv (n + 1))).length + 1 ≤ 2 * L + 5 by
            omega)
        dsimp -zeta only; omega) (by
        have := hP none (n + 1) hn (mv (n + 1)); have := hmv (mv (n + 1))
        have := Nat.mul_le_mul (show cM ≤ D by omega)
          (show (encPeek (encAug encS) (none, q (n + 1), mv (n + 1))).length + 1 ≤ 2 * L + 5 by
            omega)
        dsimp -zeta only; omega))
    (fun n hn => (hC (none, (q n, mv n))).imp (fun _ _ h => by rw [h]; rfl)
      (fun _ _ _ _ _ ⟨h, he⟩ => ⟨by rw [h]; rfl, he⟩) (by
        have := hP none n hn (mv n); have := (hst n hn).1; have := hfl n
        have := Nat.mul_le_mul (show cC ≤ D by omega)
          (show (encPeek (encAug encS) (none, q n, mv n)).length + TH (q n) + 1 ≤
            Tm + 2 * L + 5 by omega)
        dsimp -zeta only; simp only [Function.comp_apply, encBits_apply]; omega) (by
        have := hP none n hn (mv n); have := (hst n hn).2; have := hfl n
        have := Nat.mul_le_mul (show cC ≤ D by omega)
          (show (encPeek (encAug encS) (none, q n, mv n)).length + SH (q n) + 1 ≤
            Sm + 2 * L + 5 by omega)
        dsimp -zeta only; simp only [Function.comp_apply, encBits_apply]; omega))
    (sR := stepRoundSpace (M + 5) 1 (2 * L + 4) (2 * L + 4) 1
      (D * (Sm + 4 * L + 10) + 8 * L + 30 + 3 * (M + 5))
      (D * (2 * Sm + 8 * L + 20) + 12 * L + 40 + 4 * (M + 5))
      (D * (2 * L + 5) + 4 * L + 30 + 4 * (M + 5))
      (D * (Sm + 2 * L + 5) + 4 * L + 30 + 4 * (M + 5))) (fun n hn => by
      have h₁ := hP (a n) n hn.le (mv n)
      have h₂ := hP none (n + 1) hn (mv (n + 1))
      have := hfl n
      have := hmv (st n).2.1
      simp only [encPeek_apply] at h₁ h₂
      simp only [stepRoundSpace, List.length_append, slot, peekWord, List.length_cons,
        List.length_nil] at h₁ h₂ ⊢
      omega)
  rw [hg x, m.out_run fun i hi => hnh i hi]
  -- the bounds
  have hround (n : ℕ) (hn : n < R) : stepRoundTime (stepFlagWord (!halt (q n))).length
      (peekWord (a n) ++ encAug encS (q n, mv n)).length
      (slot ++ encAug encS (q (n + 1), mv (n + 1))).length (encMove (st n).2.1).length
      (D * (Tm + 4 * L + 10) + 4) (D * (2 * Tm + 8 * L + 20) + 2 * L + 10) (D * (2 * L + 5) + 7)
      (D * (Tm + 2 * L + 5) + 7) + 1 ≤ 100 * (D * (Tm + L + 1)) := by
    have h₁ := hP (a n) n hn.le (mv n)
    have h₂ := hP none (n + 1) hn (mv (n + 1))
    have := hfl n
    have := hmv (st n).2.1
    simp only [encPeek_apply] at h₁ h₂
    simp only [stepRoundTime, List.length_append, slot, peekWord, List.length_cons,
      List.length_nil] at h₁ h₂ ⊢
    have e₁ : D * (Tm + 4 * L + 10) = D * Tm + 4 * (D * L) + 10 * D := by ring
    have e₂ : D * (2 * Tm + 8 * L + 20) = 2 * (D * Tm) + 8 * (D * L) + 20 * D := by ring
    have e₃ : D * (2 * L + 5) = 2 * (D * L) + 5 * D := by ring
    have e₄ : D * (Tm + 2 * L + 5) = D * Tm + 2 * (D * L) + 5 * D := by ring
    have e₅ : D * (Tm + L + 1) = D * Tm + D * L + D := by ring
    have : L ≤ D * L := Nat.le_mul_of_pos_left _ (by omega)
    rw [e₁, e₂, e₃, e₄, e₅]
    omega
  have hS : ∑ n ∈ Finset.range R, (stepRoundTime (stepFlagWord (!halt (q n))).length
      (peekWord (a n) ++ encAug encS (q n, mv n)).length
      (slot ++ encAug encS (q (n + 1), mv (n + 1))).length (encMove (st n).2.1).length
      (D * (Tm + 4 * L + 10) + 4) (D * (2 * Tm + 8 * L + 20) + 2 * L + 10) (D * (2 * L + 5) + 7)
      (D * (Tm + 2 * L + 5) + 7) + 1) ≤ R * (100 * (D * (Tm + L + 1))) :=
    (Finset.sum_le_sum fun n hn => hround n (Finset.mem_range.mp hn)).trans (by simp)
  have hP₁ : (encPeek (encAug encS) (none, (init x, 0))).length ≤ 2 * L + 4 :=
    hP none 0 (Nat.zero_le _) 0
  have hP₂ : (slot ++ encAug encS (q R, mv R)).length ≤ 2 * L + 4 := by
    simpa [slot, peekWord] using hP none R le_rfl (mv R)
  have hsR : stepRoundSpace (M + 5) 1 (2 * L + 4) (2 * L + 4) 1
      (D * (Sm + 4 * L + 10) + 8 * L + 30 + 3 * (M + 5))
      (D * (2 * Sm + 8 * L + 20) + 12 * L + 40 + 4 * (M + 5))
      (D * (2 * L + 5) + 4 * L + 30 + 4 * (M + 5))
      (D * (Sm + 2 * L + 5) + 4 * L + 30 + 4 * (M + 5)) ≤ 200 * (D * (Sm + L + 1)) := by
    simp only [stepRoundSpace]
    have e₁ : D * (Sm + 4 * L + 10) = D * Sm + 4 * (D * L) + 10 * D := by ring
    have e₂ : D * (2 * Sm + 8 * L + 20) = 2 * (D * Sm) + 8 * (D * L) + 20 * D := by ring
    have e₃ : D * (2 * L + 5) = 2 * (D * L) + 5 * D := by ring
    have e₄ : D * (Sm + 2 * L + 5) = D * Sm + 2 * (D * L) + 5 * D := by ring
    have e₅ : D * (Sm + L + 1) = D * Sm + D * L + D := by ring
    have : L ≤ D * L := Nat.le_mul_of_pos_left _ (by omega)
    rw [e₁, e₂, e₃, e₄, e₅]
    omega
  refine h.mono ?_ ?_
  · exact step_time_le cI D (TI x) w.length R Tm L _ _ _ (by omega) (by omega) hP₁ hP₂ hS
  · exact step_space_le cI D (SI x) Sm L (M + 5) _ _ _ (by omega) (by omega) hDK hP₁ hP₂ hsR

end Turing.MultiTapeTM

namespace Turing.StepMachine

open MultiTapeTM

/-- Plain certificates for the halting test and step. Each callback charges its encoded result
to `S`; the whole-run output is not charged to workspace. -/
public structure ResourceCertificate {σ : Type} (m : StepMachine σ Bool Bool) (encS : σ ↪ List Bool)
    (T S : σ → ℕ) : Prop where
  computable_halt : ComputableInO m.halt encS encBool T S
  computable_step : ComputableInO (fun p : σ × Option Bool => m.step p.1 p.2)
    (encPair encS (encOption encBool)) (encPair encS (encPair encMove encBits))
    (fun p => T p.1) fun p => S p.1

/-- The step machine `m` started in the state `s`. -/
@[expose] public def withInit {σ Γ Out : Type*} (m : StepMachine σ Γ Out) (s : σ) :
    StepMachine σ Γ Out :=
  { m with init := s }

/-- **Compile a resource-certified step machine.** If `m`, started in the state
`init x` computed within `TI x` and `SI x`, halts on `encIn x` after `rounds x` steps with the
output `encOut (g x)`, and its steps along the run take time `tMax x` and space `sMax x`, then `g`
is computable in time `O(TI x + (rounds x + 1) * (tMax x + sMax x + SI x + 1) + n)` and
space `O(SI x + sMax x)`: the initial state bounds the states along the run, besides the steps.
-/
public theorem ResourceCertificate.computableInBigO_of_init {σ γ ω : Type} {encS : σ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} {m : StepMachine σ Bool Bool} {T S : σ → ℕ}
    (hm : m.ResourceCertificate encS T S) {init : γ → σ} {TI SI : γ → ℕ}
    (hinit : ComputableInO init encIn encS TI SI) (g : γ → ω) (rounds : γ → ℕ)
    (hrounds : ∀ x, (m.withInit (init x)).HaltsAt (encIn x) (rounds x))
    (hg : ∀ x, encOut (g x) = ((m.withInit (init x)).run (encIn x) (rounds x)).out)
    {tMax sMax : γ → ℕ}
    (hmax : ∀ x, ∀ i ≤ rounds x, T ((m.withInit (init x)).run (encIn x) i).state ≤ tMax x ∧
      S ((m.withInit (init x)).run (encIn x) i).state ≤ sMax x) :
    ComputableInBigO g encIn encOut
      (fun x => TI x + (rounds x + 1) * (tMax x + sMax x + SI x + 1) + (encIn x).length)
      fun x => SI x + sMax x := by
  obtain ⟨cS, hcS⟩ := hm.computable_step.length_le
  obtain ⟨cI, hcI⟩ := hinit.length_le
  -- the states along the run are within the space of the steps before them
  have hlen : ∀ x, ∀ i ≤ rounds x, (encS ((m.withInit (init x)).run (encIn x) i).state).length ≤
      cS * (sMax x + 1) + cI * (SI x + 1) := by
    intro x i hi
    cases i with
    | zero => exact (hcI x).trans (Nat.le_add_left _ _)
    | succ i =>
      have hh : (m.withInit (init x)).halt ((m.withInit (init x)).run (encIn x) i).state =
          false := by simpa using (hrounds x).2 i (by omega)
      rw [(m.withInit (init x)).run_succ_of_not_halt hh]
      have h₁ := hcS (((m.withInit (init x)).run (encIn x) i).state,
        inputSymbolAt (encIn x) ((m.withInit (init x)).run (encIn x) i).pos)
      have h₂ := length_le_encPair_left encS (encPair encMove encBits)
        (m.step ((m.withInit (init x)).run (encIn x) i).state
          (inputSymbolAt (encIn x) ((m.withInit (init x)).run (encIn x) i).pos))
      have h₃ := Nat.mul_le_mul_left cS (Nat.add_le_add_right (hmax x i (by omega)).2 1)
      dsimp only [withInit, stepAt] at h₁ h₂ h₃ ⊢
      omega
  obtain ⟨c, hc⟩ := MultiTapeTM.Internal.compileStepMachine (encS := encS)
    init m.halt m.step g rounds hinit hm.computable_halt hm.computable_step hrounds hg
    (tMax := fun x => 2 * tMax x) (sMax := fun x => 2 * sMax x)
    (fun x i hi => (Nat.add_le_add (hmax x i hi).1 (hmax x i hi).1).trans_eq (two_mul _).symm)
    (fun x i hi => (Nat.add_le_add (hmax x i hi).2 (hmax x i hi).2).trans_eq (two_mul _).symm)
    hlen
  obtain ⟨k, State, hfinite, tm, htm⟩ := hc
  refine .of_bounds ⟨k, State, hfinite, tm, fun x => (htm x).computesInTimeAndSpace⟩ ?_
    (.const_mul c (.of_le_linear (cS + cI + 3) (cS + cI + 1) fun x => by nlinarith))
  have hR := BigOLe.mul_left (fun x => rounds x + 1)
    (v := fun x => 2 * tMax x + (cS * (sMax x + 1) + cI * (SI x + 1)) + 1)
    (w := fun x => tMax x + sMax x + SI x + 1)
    (.of_le_linear (cS + cI + 2) 0 fun x => by nlinarith) fun _ => by omega
  have hR' := hR.trans_le (w := fun x => TI x + (rounds x + 1) * (tMax x + sMax x + SI x + 1) +
    (encIn x).length) fun x => by omega
  have hTI : TI ≼ fun x => TI x + (rounds x + 1) * (tMax x + sMax x + SI x + 1) +
      (encIn x).length := .of_le fun x => by omega
  have hn : (fun x => (encIn x).length) ≼ fun x => TI x + (rounds x + 1) *
      (tMax x + sMax x + SI x + 1) + (encIn x).length := .of_le fun x => by omega
  bigO

/-- **Compile a resource-certified step machine**, from its initial state: as
`Turing.StepMachine.ResourceCertificate.computableInBigO_of_init`, in time
`O((rounds x + 1) * (tMax x + sMax x + 1) + n)` and space `O(sMax x)`. -/
public theorem ResourceCertificate.computableInBigO {σ γ ω : Type} {encS : σ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} {m : StepMachine σ Bool Bool} {T S : σ → ℕ}
    (hm : m.ResourceCertificate encS T S) (g : γ → ω) (rounds : γ → ℕ)
    (hrounds : ∀ x, m.HaltsAt (encIn x) (rounds x))
    (hg : ∀ x, encOut (g x) = (m.run (encIn x) (rounds x)).out) {tMax sMax : γ → ℕ}
    (hmax : ∀ x, ∀ i ≤ rounds x,
      T (m.run (encIn x) i).state ≤ tMax x ∧ S (m.run (encIn x) i).state ≤ sMax x) :
    ComputableInBigO g encIn encOut
      (fun x => (rounds x + 1) * (tMax x + sMax x + 1) + (encIn x).length) sMax :=
  (hm.computableInBigO_of_init (ComputableInO.constZero m.init) g rounds hrounds hg hmax).weaken
    (.of_le_linear 2 0 fun x => by simp only [Nat.add_zero]; omega) (.of_le fun x => by omega)

end Turing.StepMachine
