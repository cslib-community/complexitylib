/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.CookLevinBridge
import ComplexityAbstracts.Randomized
import Complexity.Crypto.Computational.OneWayToPRG
import Complexity.Crypto.Computational.PRGToOneWay
import Complexity.Crypto.Computational.GoldreichLevin.HardCore
import Complexity.Crypto.Computational.Stretch
import Complexity.Crypto.Computational.OneWayToPRF
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Languages.Probabilistic.Oracle.Interaction
import Complexity.Tactic.PPT


import Diag1155.Measure
/-! # Bridge for uniform cryptographic constructions

The public abstract describes randomized algorithms by a deterministic polynomial-time
evaluator fed a polynomial-length uniform coin tape. The saved-coin theorem identifies this
semantic interface with the library's strict fair-coin Turing-machine certificates.
-/


diag1155_install
namespace ComplexityTests.Abstracts.CryptographyBridge

open Cslib Cslib.Probability Turing.MultiTapeTM
open ComplexityTests.Abstracts.Randomized
open scoped NNReal

def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

def encodePair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) (p : α × β) :
    List Bool := frame (a p.1) ++ b p.2

theorem encodePair_injective {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    Function.Injective (encodePair a b) := (Turing.MultiTapeTM.encPair a b).injective

def pairEncoding {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair a b, encodePair_injective a b⟩

def bitsEncoding : List Bool ↪ List Bool := Function.Embedding.refl _

def unaryEncoding : ℕ ↪ List Bool := ⟨fun n => List.replicate n true,
  fun _ _ h => by simpa only [List.length_replicate] using congrArg List.length h⟩

def boolEncoding : Bool ↪ List Bool := ⟨fun b => [b], fun _ _ h => by injection h⟩

def PolyTime {α β : Type} (f : α → β) (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f a b t s

theorem polyTime_iff {α β : Type} {f : α → β} {a : α ↪ List Bool} {b : β ↪ List Bool} :
    PolyTime f a b ↔ ComputableTidilyInPolyTime f a b :=
  Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength.symm

theorem strictPPT_iff {α β : Type} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {law : α → PMF β} :
    StrictPPT a b law ↔ ∃ program : α → ProbComp β,
      IsPPTOn a b program ∧ ∀ x, ProbComp.eval (program x) = law x := by
  constructor
  · rintro ⟨c, d, evaluate, hevaluate, hlaw⟩
    have he : ComputableTidilyInPolyTime (fun p : α × List Bool => evaluate p.1 p.2)
        (encPair a encBits) b := polyTime_iff.mp hevaluate
    let program (x : α) : ProbComp β := do
      let coins ← BitString.sampleList (c * ((a x).length + 1) ^ d)
      pure (evaluate x coins)
    refine ⟨program, ?_, fun x => ?_⟩
    · unfold program
      ppt
    · simpa only [program, ProbComp.eval_bind, BitString.eval_sampleList,
        ProbComp.eval_pure, PMF.map, Function.comp_def, uniformBits, BitString.uniformList]
        using (hlaw x).symm
  · rintro ⟨program, hp, hlaw⟩
    obtain ⟨c, d, evaluate, hevaluate, heq⟩ := hp.exists_seeded_evaluator
    exact ⟨c, d, evaluate, polyTime_iff.mpr hevaluate,
      fun x => (hlaw x).symm.trans (heq x)⟩

theorem indistinguishable_iff {X Y : ℕ → PMF (List Bool)} :
    Indistinguishable X Y ↔ Crypto.ComputationallyIndistinguishable X Y := by
  rw [Crypto.computationallyIndistinguishable_iff_tests]
  have hadmissible (test : ℕ → List Bool → PMF Bool) :
      StrictPPT (Encoding.encPair Encoding.encUnary Encoding.encBits) Encoding.encBool
        (fun p => test p.1 p.2) ↔ Crypto.IsPPTTest test := by
    rw [strictPPT_iff]
    constructor
    · rintro ⟨program, hp, heq⟩
      exact ⟨fun n word => program (n, word), hp, fun n word => heq (n, word)⟩
    · rintro ⟨program, hp, heq⟩
      exact ⟨fun p => program p.1 p.2, hp, fun p => heq p.1 p.2⟩
  simp only [Indistinguishable, hadmissible, Crypto.Game.Indistinguishable,
    Crypto.Game.advantage, Crypto.Game.succProbability, probability, PMF.monad_bind_eq_bind,
    Negligible, Crypto.Negligible, Asymptotics.SuperpolynomialDecay]

def OneWay (f : List Bool → List Bool) : Prop :=
  PolyTime f bitsEncoding bitsEncoding ∧
    ∀ inverter : ℕ → List Bool → PMF (List Bool),
      StrictPPT (pairEncoding unaryEncoding bitsEncoding) bitsEncoding
        (fun p => inverter p.1 p.2) →
      Negligible (fun n => probability ((uniformBits n).bind fun x =>
        (inverter n (f x)).map fun candidate => f candidate == f x))

theorem oneWay_iff {f : List Bool → List Bool} : OneWay f ↔ Crypto.OneWay f := by
  constructor
  · rintro ⟨hf, hsecure⟩
    apply Crypto.OneWay.of_inversion_negligible (.of_tidy (polyTime_iff.mp hf))
    intro adversary ha
    have h := hsecure (fun n word => ProbComp.eval (adversary n word))
      (strictPPT_iff.mpr ⟨fun p => adversary p.1 p.2, ha, fun _ => rfl⟩)
    simpa only [Crypto.inversionGame, ProbComp.eval_bind, BitString.eval_sampleList,
      ProbComp.eval_map, ProbComp.eval_pure, PMF.map, Function.comp_def,
      uniformBits, BitString.uniformList, Negligible, Crypto.Negligible,
      probability, Crypto.Game.succProbability, Asymptotics.SuperpolynomialDecay] using h
  · intro hf
    refine ⟨polyTime_iff.mpr hf.polyTime.tidy, fun inverter hinverter => ?_⟩
    obtain ⟨program, hp, heq⟩ := strictPPT_iff.mp hinverter
    have h := hf.inversion_negligible (fun n word => program (n, word)) hp
    simpa only [Crypto.inversionGame, ProbComp.eval_bind, BitString.eval_sampleList,
      ProbComp.eval_map, ProbComp.eval_pure, PMF.map, Function.comp_def, heq,
      uniformBits, BitString.uniformList, Negligible, Crypto.Negligible,
      probability, Crypto.Game.succProbability, Asymptotics.SuperpolynomialDecay] using h

def PseudorandomGenerator (g : List Bool → List Bool) (length : ℕ → ℕ) : Prop :=
  PolyTime g bitsEncoding bitsEncoding ∧
    (∀ seed, (g seed).length = length seed.length) ∧ (∀ n, n < length n) ∧
    Indistinguishable (fun n => (uniformBits n).map g) (fun n => uniformBits (length n))

theorem generator_iff {g : List Bool → List Bool} {length : ℕ → ℕ} :
    PseudorandomGenerator g length ↔ Crypto.PseudorandomGenerator g length := by
  constructor
  · rintro ⟨hg, hlength, hstretch, hsecure⟩
    exact Crypto.PseudorandomGenerator.of_indistinguishable (.of_tidy (polyTime_iff.mp hg)) hlength
      hstretch (indistinguishable_iff.mp hsecure)
  · intro hg
    exact ⟨polyTime_iff.mpr hg.polyTime.tidy, hg.length_eq, hg.stretch,
      indistinguishable_iff.mpr hg.indistinguishable⟩

theorem hill {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ g : List Bool → List Bool, PseudorandomGenerator g (fun n => n + 1) := by
  obtain ⟨g, hg⟩ := (oneWay_iff.mp hf).exists_pseudorandomGenerator
  exact ⟨g, generator_iff.mpr hg⟩

theorem existence_equivalence :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      ∃ (g : List Bool → List Bool) (length : ℕ → ℕ), PseudorandomGenerator g length := by
  simp only [oneWay_iff, generator_iff]
  exact Crypto.exists_oneWay_iff_exists_pseudorandomGenerator

theorem stretch {g : List Bool → List Bool}
    (hg : PseudorandomGenerator g (fun n => n + 1)) (target : ℕ → ℕ)
    (htarget : PolyTime target unaryEncoding unaryEncoding) (hgreater : ∀ n, n < target n) :
    ∃ g' : List Bool → List Bool, PseudorandomGenerator g' target :=
  ⟨_, generator_iff.mpr ((generator_iff.mp hg).amplify target
    (.of_tidy (polyTime_iff.mp htarget)) hgreater)⟩

abbrev OracleResponse : Sum ℕ (Unit × List Bool) → Type :=
  Cslib.probOracleSpec (fun _ : Unit × List Bool => List Bool)

abbrev OracleProgram (β : Type) :=
  Cslib.ProbOracleComp (fun _ : Unit × List Bool => List Bool) β

noncomputable def execute {State β : Type} (program : OracleProgram β)
    (oracle : Unit × List Bool → StateT State PMF (List Bool)) (s : State) : PMF (β × State) :=
  ProbOracleComp.runWith oracle program s

theorem execute_eq {State β : Type} (program : OracleProgram β)
    (oracle : Unit × List Bool → StateT State PMF (List Bool)) (s : State) :
    execute program oracle s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          program).run s := rfl

def OraclePPT (program : ℕ → List Bool → OracleProgram Bool) : Prop :=
  ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ),
    ∀ n aux (State : Type) (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      execute (boolEncoding <$> program n aux) oracle s =
        execute (machine.runOracle (c * ((encodePair unaryEncoding bitsEncoding (n, aux)).length
          + 1) ^ d) (encodePair unaryEncoding bitsEncoding (n, aux))) oracle s

theorem oraclePPT_iff {program : ℕ → List Bool → OracleProgram Bool} :
    OraclePPT program ↔ Cslib.Probability.IsOraclePPT encBool program := by
  constructor
  · rintro ⟨k, Control, hfinite, machine, c, d, h⟩
    refine ⟨inferInstance, k, Control, hfinite, machine, c, d, fun p State oracle s => ?_⟩
    simpa only [execute_eq, boolEncoding, encBool, encodePair, encPair, unaryEncoding, encUnary,
      bitsEncoding, encBits, frame, Turing.MultiTapeTM.frame, Function.Embedding.coeFn_mk,
      Function.Embedding.coe_refl] using h p.1 p.2 State oracle s
  · rintro ⟨_, k, Control, hfinite, machine, c, d, h⟩
    refine ⟨k, Control, hfinite, machine, c, d, fun n aux State oracle s => ?_⟩
    simpa only [execute_eq, boolEncoding, encBool, encodePair, encPair, unaryEncoding, encUnary,
      bitsEncoding, encBits, frame, Turing.MultiTapeTM.frame, Function.Embedding.coeFn_mk,
      Function.Embedding.coe_refl] using h (n, aux) State oracle s

noncomputable def evaluateOracle {β : Type} (program : OracleProgram β)
    (oracle : List Bool → List Bool) : PMF β :=
  (ProbOracleComp.runWith
    (fun request => StateT.lift (PMF.pure (oracle request.2))) program ()).map Prod.fst

theorem evaluateOracle_eq {β : Type} (program : OracleProgram β)
    (oracle : List Bool → List Bool) :
    evaluateOracle program oracle = OracleComp.interpret
      (ProbOracleComp.handler ProbComp.unifOracle (fun request => PMF.pure (oracle request.2)))
        program := by
  have hlift : ProbOracleComp.handler (fun n => StateT.lift (σ := Unit) (ProbComp.unifOracle n))
      (fun request : Unit × List Bool => StateT.lift (PMF.pure (oracle request.2))) =
      (fun q => StateT.lift
        (ProbOracleComp.handler ProbComp.unifOracle (fun request => PMF.pure (oracle request.2))
          q)) := by
    funext q
    cases q <;> rfl
  simp only [evaluateOracle, ProbOracleComp.runWith, hlift, OracleComp.run_interpret_lift]
  simp only [PMF.monad_map_eq_map, PMF.map_comp]
  exact PMF.map_id _

noncomputable def realPRF (family : List Bool → List Bool → List Bool)
    (adversary : ℕ → List Bool → OracleProgram Bool) (n : ℕ) : PMF Bool := do
  let key ← uniformBits n
  evaluateOracle (adversary n [])
    (fun query => if query.length = n then family key query else [])

noncomputable def idealPRF (adversary : ℕ → List Bool → OracleProgram Bool) (n : ℕ) : PMF Bool := do
  let table ← Cslib.Probability.PMF.uniformOfFintype ((Fin n → Bool) → Fin n → Bool)
  evaluateOracle (adversary n []) (fun query =>
    if query.length = n then List.ofFn (table fun i => query.getD i.val false) else [])

def PseudorandomFunction (family : List Bool → List Bool → List Bool) : Prop :=
  PolyTime (fun p : List Bool × List Bool => family p.1 p.2)
    (pairEncoding bitsEncoding bitsEncoding) bitsEncoding ∧
  (∀ key query, query.length = key.length → (family key query).length = key.length) ∧
  ∀ adversary : ℕ → List Bool → OracleProgram Bool, OraclePPT adversary →
    Negligible (fun n => nndist (probability (realPRF family adversary n))
      (probability (idealPRF adversary n)))

theorem realPRF_eq (family : List Bool → List Bool → List Bool)
    (adversary : ℕ → List Bool → OracleProgram Bool) (n : ℕ) :
    realPRF family adversary n = ProbComp.eval (Crypto.prfRealGame family adversary n) := by
  simp only [realPRF, Crypto.prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, evaluateOracle_eq]
  rfl

theorem idealPRF_eq (adversary : ℕ → List Bool → OracleProgram Bool) (n : ℕ) :
    idealPRF adversary n = ProbComp.eval (Crypto.prfIdealGame adversary n) := by
  simp only [idealPRF, Crypto.prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, evaluateOracle_eq]
  rfl

theorem function_iff {family : List Bool → List Bool → List Bool} :
    PseudorandomFunction family ↔ Crypto.PseudorandomFunction family := by
  constructor
  · rintro ⟨hefficient, hlength, hsecure⟩
    refine ⟨.of_tidy (polyTime_iff.mp hefficient), hlength, fun adversary ha => ?_⟩
    simpa only [realPRF_eq, idealPRF_eq, Negligible, Crypto.Negligible,
      Crypto.Game.advantage, Crypto.Game.succProbability, probability,
      Asymptotics.SuperpolynomialDecay] using hsecure adversary (oraclePPT_iff.mpr ha)
  · intro hf
    refine ⟨polyTime_iff.mpr hf.polyTime.tidy, hf.length_eq, fun adversary ha => ?_⟩
    simpa only [realPRF_eq, idealPRF_eq, Negligible, Crypto.Negligible,
      Crypto.Game.advantage, Crypto.Game.succProbability, probability,
      Asymptotics.SuperpolynomialDecay] using hf.secure adversary (oraclePPT_iff.mp ha)

theorem adaptive_functions {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ family : List Bool → List Bool → List Bool, PseudorandomFunction family := by
  obtain ⟨family, hfamily⟩ := (oneWay_iff.mp hf).exists_pseudorandomFunction
  exact ⟨family, function_iff.mpr hfamily⟩

/-! The admissible adversary classes are inhabited, and the security definition rejects
the simplest insecure function. These checks do not assume that one-way functions exist. -/

example : StrictPPT (pairEncoding unaryEncoding bitsEncoding) boolEncoding
    (fun _ => PMF.pure false) :=
  strictPPT_iff.mpr ⟨fun _ => pure false, by ppt, fun _ => rfl⟩

example : OraclePPT (fun _ _ => pure false) := by
  have h : ComputableTidilyInPolyTime (fun _ : ℕ × List Bool => false)
      (encPair encUnary encBits) encBool := .const false
  exact oraclePPT_iff.mpr h.isOraclePPTOn

example : ¬ OneWay (fun _ => []) :=
  fun h => Crypto.not_oneWay_const [] (oneWay_iff.mp h)

end ComplexityTests.Abstracts.CryptographyBridge
