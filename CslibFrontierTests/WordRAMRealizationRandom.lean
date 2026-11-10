/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Realization.RandomLoop
import CslibFrontier.Tactic.Realize

/-! `RealizesRand` end to end: sample a uniformly random input word.

The client `sample` reads the input length, draws a uniform index below it, and reads that input
word. Its two memory reads are certified by `realize` and enter through `Realizes.toRand`; the
draw is `RealizesRand.coin`. On every path the flat program from the list input halts within a
fixed bound and makes at most one `rand` call. It chooses an input position uniformly, retaining
repeated values (`sample_program`). Repeated in a loop (`RealizesRand.iterate`), every path takes
`6` units of time and at most one `rand` call per iteration. -/

namespace CslibFrontierTests.WordRAMRealizationRandom

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-- One word. -/
abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- No words. -/
abbrev unitWords : Unit ↪ (Fin 0 → ℕ) := (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

/-- The largest input index: the input length, less one. -/
def lastIndex : Memory.Prog ℕ := do
  let n ← Memory.read 0
  pure (n - 1)

/-- A uniform index `c ≤ n`. -/
noncomputable abbrev index (n : ℕ) : ProbOracleComp Memory.Op.Result ℕ :=
  Fin.val <$> ProbOracleComp.sample (ProbComp.unifFin n)

/-- **Sample an input word**: draw a uniform index below the input length, and read that word. -/
noncomputable def sample : ProbOracleComp Memory.Op.Result ℕ := do
  let n ← OracleComp.liftRight lastIndex
  let c ← index n
  OracleComp.liftRight (Memory.read (c + 1))

/-! ## The law -/

/-- The law of `sample` from any memory: a uniform index `c` below the length cell, the cell
`c + 1`, and the memory unchanged. -/
theorem run_sample (w : ℕ) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run sample s =
      (Probability.PMF.uniformOfFintype (Fin (s.mem 0 - 1 + 1))).map
        fun c => (s.mem (c.val + 1), s) := by
  rw [sample, RandomizedSpec.run_bind, RandomizedSpec.withCoins_run_liftRight,
    StateTransitionSpec.run_toRandomized, PMF.pure_bind]
  change (Memory.spec w).toRandomized.withCoins.run
    (index (s.mem 0 - 1) >>= fun c => OracleComp.liftRight (Memory.read (c + 1))) s = _
  rw [RandomizedSpec.run_bind, RandomizedSpec.run_map, RandomizedSpec.withCoins_run_sample,
    ProbComp.eval_unifFin, PMF.map_comp, PMF.bind_map, ← PMF.bind_pure_comp]
  congr 1 with c : 1
  simp only [Function.comp_apply]
  rw [RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized]
  rfl

/-- On the list input, `sample` chooses a position uniformly, retaining repeated values. -/
theorem run_sample_inputState (w : ℕ) (xs : List ℕ) :
    ((Memory.spec w).toRandomized.withCoins.run sample (Memory.State.init xs)).map Prod.fst =
      (Probability.PMF.uniformOfFintype (Fin (xs.length - 1 + 1))).map
        fun c => xs.getD c.val 0 := by
  rw [run_sample, PMF.map_comp]
  rfl

/-- `sample` leaves the memory unchanged on every path. -/
theorem eq_of_mem_support_sample {w : ℕ} {s s' : Memory.State} {v : ℕ}
    (h : (v, s') ∈ ((Memory.spec w).toRandomized.withCoins.run sample s).support) : s' = s := by
  rw [run_sample, PMF.mem_support_map_iff] at h
  obtain ⟨c, -, hc⟩ := h
  exact (congrArg Prod.snd hc).symm

/-- Every call of `sample` is admissible when the length cell is positive and allocated. -/
theorem demonicValid_sample {w : ℕ} {s : Memory.State} (h0 : 1 ≤ s.mem 0)
    (hf : s.mem 0 < s.frontier) :
    (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s sample := by
  refine StateTransitionSpec.DemonicValid.bind (D := (Memory.spec w).toRandomized.withCoins.toSpec)
    (p := OracleComp.liftRight lastIndex)
    (RandomizedSpec.demonicValid_liftRight
      (StateTransitionSpec.toRandomized_demonicValid_of_validHistory (D := Memory.spec w)
        (p := lastIndex) (s := s) (And.intro (show 0 < s.frontier by omega) trivial)))
    fun n s' tr hrun => ?_
  have hmem := RandomizedSpec.mem_support_run_of_clientRun _ hrun
  rw [RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized,
    PMF.mem_support_pure_iff] at hmem
  obtain ⟨hn, hs'⟩ := Prod.mk.inj hmem
  subst n s'
  change (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s
    (index (s.mem 0 - 1) >>= fun c => OracleComp.liftRight (Memory.read (c + 1)))
  rw [bind_map_left]
  refine RandomizedSpec.demonicValid_sample_bind fun c => ?_
  have hc := c.isLt
  exact RandomizedSpec.demonicValid_liftRight
    (StateTransitionSpec.toRandomized_demonicValid_of_validHistory (D := Memory.spec w)
      (p := Memory.read (c.val + 1)) (s := s)
      (And.intro (show c.val + 1 < s.frontier by omega) trivial))

/-! ## The certificate -/

/-- The appended word of an environment. -/
theorem appendWords_last {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) (d : δ) (a : ℕ) :
    (appendWords input word) (d, a) (Fin.natAdd k 0) = a := by
  simp [appendWords, Fin.appendEquiv]

/-- `sample` in any environment of word encodings, from certificates of its two reads. -/
theorem realizesRand_sample {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ))
    (hlast : Realizes .exact (fun _ : δ => lastIndex) input word
      (fun _ _ s => 1 ≤ s.mem 0) (fun _ _ => 0))
    (hread : Realizes .exact (fun e : (δ × ℕ) × ℕ => Memory.read (e.2 + 1))
      (appendWords (appendWords input word) word) word (fun w e _ => Fits w (e.2 + 1))
      (fun _ _ => 0)) :
    RealizesRand .exact (fun _ => sample) input word (fun _ _ s => 1 ≤ s.mem 0)
      (fun _ _ => 5) (fun _ _ => 1) := by
  have hinner := (RealizesRand.coin (B := .exact) (appendWords input word) (Fin.natAdd k 0)).bind
    hread.toRand (fun _ _ => 1) (fun _ _ => 0)
  refine ((hlast.toRand.bind hinner (fun _ _ => 3) (fun _ _ => 1)).congr fun d => ?_).consequence
    ?_
  · unfold sample
    congr 1 with a : 1
    rw [appendWords_last]
  · intro w d s _ hs h0
    refine ⟨⟨h0, fun n s' hmem => ?_⟩, le_rfl, le_rfl⟩
    rw [RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized,
      PMF.mem_support_pure_iff] at hmem
    obtain ⟨hn, hs'⟩ := Prod.mk.inj hmem
    subst n s'
    refine ⟨⟨trivial, fun c s'' hc => ⟨?_, le_rfl, le_rfl⟩⟩, le_rfl, le_rfl⟩
    rw [RandomizedSpec.run_map, RandomizedSpec.withCoins_run_sample, ProbComp.eval_unifFin,
      PMF.map_comp, PMF.mem_support_map_iff] at hc
    obtain ⟨c', -, hc'⟩ := hc
    have hcv : c = c'.val := (congrArg Prod.fst hc').symm
    have hbound : (appendWords input word) (d, (Memory.spec w).clientResult s lastIndex)
        (Fin.natAdd k 0) + 1 = s.mem 0 - 1 + 1 := by
      rw [appendWords_last]
      rfl
    have hlt : c'.val < s.mem 0 - 1 + 1 := c'.isLt.trans_eq hbound
    exact (hs.mem_fits 0).of_le (by omega)

/-- `sample` with no environment: both reads by `realize`. -/
theorem realizesRand_sample_unit :
    RealizesRand .exact (fun _ : Unit => sample) unitWords word (fun _ _ s => 1 ≤ s.mem 0)
      (fun _ _ => 5) (fun _ _ => 1) :=
  realizesRand_sample unitWords (by realize; exact h) (by realize; exact h)

/-! ## The flat program -/

/-- The output word and the memory of a halting configuration. -/
def observe {r : ℕ} (frontier : Fin r) : RandCfg r → ℕ × Memory.State
  | .halted v y => (v, memoryState frontier y)
  | _ => (0, ⟨fun _ => 0, 0⟩)

/-- **End to end.** One flat word-RAM program samples a uniform input position: from every
nonempty input that fits, it halts within `T` steps on every path, makes at most one `rand`
call, and returns the word at the chosen position. Repeated values retain their multiplicity. -/
theorem sample_program : ∃ (r : ℕ) (prog : Program .exact r) (T : ℕ),
    ∀ (w : ℕ) (xs : List ℕ), xs ≠ [] → Fits w (xs.length + 1) → InputFits w xs →
      RandHaltsWithin w prog (State.init xs) T ∧ RandCallsBounded w prog (State.init xs) T 1 ∧
      ∃ out : RandCfg r → ℕ, (evalRand w prog T (State.init xs)).map out =
        (Probability.PMF.uniformOfFintype (Fin (xs.length - 1 + 1))).map
        fun c => xs.getD c.val 0 := by
  obtain ⟨n, C, emit, he⟩ := realizesRand_sample_unit.exists_init_program
  let frontier : Fin (1 + n + 1 + 1) := Fin.last _
  let tmp : Fin (1 + n + 1) → Fin (1 + n + 1 + 1) := Fin.castSucc
  have hrun := he frontier Fin.elim0 tmp (fun i => i.elim0) (Fin.castSucc_injective _)
    (fun i => i.elim0) (fun j => Fin.castSucc_ne_last j) (fun i => i.elim0)
  refine ⟨1 + n + 1 + 1, (Code.seq (inputPrefix frontier (tmp (Fin.last (1 + n))) Fin.elim0)
    (emit frontier Fin.elim0 tmp)).program (tmp (Fin.castAdd (n + 1) 0)), C * (5 + 1) + 1,
    fun w xs hxs hw hin => ?_⟩
  have hlen : 1 ≤ xs.length := List.length_pos_iff.mpr hxs
  obtain ⟨hhalt, hcalls, hlaw⟩ := hrun 0 w () xs (fun j => j.elim0) (Nat.zero_le _) hw hin hlen
    (demonicValid_sample hlen (by simp [Memory.State.init])) (observe frontier)
    fun _ _ => rfl
  refine ⟨hhalt, hcalls, fun cfg => (observe frontier cfg).1, ?_⟩
  rw [show (fun cfg => (observe frontier cfg).1) = Prod.fst ∘ observe frontier from rfl,
    ← PMF.map_comp, hlaw, PMF.map_comp, ← run_sample_inputState w xs]
  rfl

/-! ## A loop -/

/-- Sample `n` input words, keeping the last. -/
noncomputable def sampleTimes : ℕ → ℕ → ProbOracleComp Memory.Op.Result ℕ
  | 0, a => pure a
  | n + 1, _ => sample >>= sampleTimes n

/-- Every iteration samples once, so every path of `n` iterations takes `6 n` units of time and at
most `n` `rand` calls. -/
example : RealizesRand .exact (fun ((_, a), fuel) => sampleTimes fuel a)
    (((appendWords unitWords word).prodMap word).trans (Fin.appendEquiv (0 + 1) 1).toEmbedding)
    word (fun _ _ s => 1 ≤ s.mem 0) (fun ((_, _), fuel) _ => fuel * 6)
    (fun ((_, _), fuel) _ => fuel) := by
  have hbody := realizesRand_sample (appendWords unitWords word) (by realize; exact h)
    (by realize; exact h)
  refine (RealizesRand.iterate unitWords word (loop := fun _ n a => sampleTimes n a)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => 5) (fun _ _ => 1) hbody).consequence ?_
  rintro w ⟨⟨_, a⟩, fuel⟩ s - - h0
  refine ⟨fun j _ b s' hmem => ⟨?_, le_rfl, le_rfl⟩, le_rfl, by simp⟩
  suffices ∀ j a b s', (b, s') ∈ ((Memory.spec w).toRandomized.withCoins.run
      (sampleTimes j a) s).support → s' = s by
    rw [this j a b s' hmem]
    exact h0
  intro j
  induction j with
  | zero =>
    intro a b s' h
    rw [sampleTimes, RandomizedSpec.run_pure, PMF.mem_support_pure_iff] at h
    exact (congrArg Prod.snd h)
  | succ j ih =>
    intro a b s' h
    rw [sampleTimes, RandomizedSpec.run_bind, PMF.mem_support_bind_iff] at h
    obtain ⟨⟨v, s₁⟩, h₁, h₂⟩ := h
    obtain rfl := eq_of_mem_support_sample h₁
    exact ih v b s' h₂

/-! ## An adaptive write retains the joint result/memory law -/

/-- Sample an input word, then store the sampled value in the length cell. -/
noncomputable def storeSample : ProbOracleComp Memory.Op.Result ℕ := do
  let v ← sample
  OracleComp.liftRight (do
    Memory.write 0 v
    pure v)

/-- The returned value and the updated cell are correlated, while every other cell and the
frontier are unchanged. Separate result and memory marginals would not express this law. -/
theorem run_storeSample (w : ℕ) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run storeSample s =
      (Probability.PMF.uniformOfFintype (Fin (s.mem 0 - 1 + 1))).map fun c =>
        (s.mem (c.val + 1),
          (⟨Function.update s.mem 0 (s.mem (c.val + 1)), s.frontier⟩ : Memory.State)) := by
  rw [storeSample, RandomizedSpec.run_bind, run_sample, PMF.bind_map, ← PMF.bind_pure_comp]
  congr 1 with c : 1
  simp only [Function.comp_apply]
  rw [RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized]
  rfl

/-- Every supported joint outcome records the returned value in cell zero. -/
theorem storeSample_result_eq_cell {w : ℕ} {s s' : Memory.State} {v : ℕ}
    (h : (v, s') ∈ ((Memory.spec w).toRandomized.withCoins.run storeSample s).support) :
    s'.mem 0 = v := by
  rw [run_storeSample, PMF.mem_support_map_iff] at h
  obtain ⟨c, -, hc⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  simp only [Function.update_self]

/-- The adaptive write is admissible on the same nonempty allocated input as `sample`, when
the memory words fit. The stored value is a word read from that memory. -/
theorem demonicValid_storeSample {w : ℕ} {s : Memory.State} (hs : Memory.WellFormed w s)
    (h0 : 1 ≤ s.mem 0) (hf : s.mem 0 < s.frontier) :
    (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s storeSample := by
  refine StateTransitionSpec.DemonicValid.bind (demonicValid_sample h0 hf) fun v s' tr hrun => ?_
  have hmem := RandomizedSpec.mem_support_run_of_clientRun _ hrun
  rw [run_sample, PMF.mem_support_map_iff] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  apply RandomizedSpec.demonicValid_liftRight
  apply StateTransitionSpec.toRandomized_demonicValid_of_validHistory
  exact ⟨⟨by omega, hs.mem_fits _⟩, trivial⟩

/-- The adaptive store uses the same deterministic entry point and preserves a pathwise
single-call budget; its concrete memory write is included in the instruction currency. -/
theorem realizesRand_storeSample :
    RealizesRand .exact (fun _ : Unit => storeSample) unitWords word
      (fun _ _ s => 1 ≤ s.mem 0) (fun _ _ => 7) (fun _ _ => 1) := by
  have hwrite : Realizes .exact (fun e : Unit × ℕ => do
      Memory.write 0 e.2
      pure e.2) (appendWords unitWords word) word (fun _ _ _ => True) (fun _ _ => 0) := by
    realize
  refine ((realizesRand_sample_unit.bind hwrite.toRand (fun _ _ => 1) (fun _ _ => 0)).congr
    fun _ => rfl).consequence ?_
  intro w d s _ _ h
  exact ⟨⟨h, fun _ _ _ => ⟨trivial, le_rfl, le_rfl⟩⟩, le_rfl, le_rfl⟩

end CslibFrontierTests.WordRAMRealizationRandom
