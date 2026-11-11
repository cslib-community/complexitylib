/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Oracle.Selection
public import CslibFrontier.Computability.MCSP.AntiChecker.Oracle

/-!
# The anti-checker generator as an oracle circuit

`generator n s ℓ R` is an explicit oracle circuit that, given the truth table of a function `f`
on `n` inputs, runs `R` rounds of the threshold greedy (`Cslib.MCSP.AntiChecker.greedy`) and
appends the chosen samples. Each greedy round is one selection round
(`Cslib.Circuits.Boolean.selectionRound`): round `r` has one oracle gate for each of the `2 ^ n`
inputs `y`, in the order of `Cslib.BitString.enum`. The gate for `y` asks about the
exact query word `encQuery (Query.ofSamples n s ℓ (R - 1 - r) (P ++ [(y, f y)]))`, where `P` are
the samples chosen in the earlier rounds. Its bits are read from constants (the unary parameters,
the bits of `y` and the framing) and from wires (the earlier samples and the table entry of `y`).
The round appends the sample `(y, f y)` of the first accepted `y`, or `(default, f default)` when
none is accepted, as the greedy does.

So, under any oracle `O`, the samples in the output (`samplesOf`) are exactly those of the greedy
against `O`'s answers to the greedy's queries (`samplesOf_eval_generator`), and each is a correct
pair `(y, f y)` (`snd_eq_of_mem_samplesOf_eval_generator`). With power `ℓ = L + 200` and
`R = L (L + 200) + 1` rounds, where `L` is the certificate length, and any oracle that agrees with
`antiCheckerOracle` on query words, such as the `P/poly` language of
`exists_mem_PPoly_agrees_antiCheckerOracle`, the chosen inputs are an anti-checker for the circuits
with at most `s` gates against every `f` that needs more gates than `n` of them and their strict
majority (`isAntiChecker_samplesOf_generator`). A later query about the samples of an output can
read them from its blocks (`map_querySources_blockSources`).

The generator has `R (2 + 2 ^ n (3 n + 5))` gates, `R 2 ^ n` oracle gates and at most `R` oracle
gates on any path. Round `r` asks queries with `r + 1` samples, so query lengths differ between
rounds. They are not padded, so every query is an `encQuery` word, and `queryLength n s ℓ R R`
bounds the fan-in of every gate. For the anti-checker parameters, the number of rounds and the
query length are polynomial in `n + s`.

This is the library's deterministic greedy, not the proof of
[Oliveira, Pich and Santhanam, Lemma 4.1][OliveiraPichSanthanam2019]. Replacing the oracle gates by
circuits for the oracle, under `NP ⊆ P/poly`, is not done here.

## Main definitions

* `Cslib.MCSP.AntiChecker.querySources`: a query word read from constants and wires.
* `Cslib.MCSP.AntiChecker.queryLength`: the length of a greedy query
  (`Cslib.MCSP.AntiChecker.length_encQuery_ofSamples_eq_queryLength`).
* `Cslib.MCSP.AntiChecker.generator`: the greedy as an oracle circuit over the truth table.
* `Cslib.MCSP.AntiChecker.blockWire`: wire `b` of the block of round `j` in an output.
* `Cslib.MCSP.AntiChecker.samplesOf`, `Cslib.MCSP.AntiChecker.blockSources`: the samples in an
  output of the generator, and the wires that hold them.
* `Cslib.MCSP.AntiChecker.queryOracle`: a language's answers to the greedy's queries.
* `Cslib.MCSP.AntiChecker.antiCheckerPower`, `Cslib.MCSP.AntiChecker.antiCheckerRounds`: the power
  `L + 200` and the `L (L + 200) + 1` rounds of the anti-checker generator.

## Main results

* `Cslib.MCSP.AntiChecker.samplesOf_eval_generator`: the generator runs the greedy.
* `Cslib.MCSP.AntiChecker.snd_eq_of_mem_samplesOf_eval_generator`: every sample is `(y, f y)`.
* `Cslib.MCSP.AntiChecker.isAntiChecker_samplesOf_generator`: the anti-checker generator.
* `Cslib.MCSP.AntiChecker.map_querySources_blockSources`: a query about the samples of an output.
* `Cslib.MCSP.AntiChecker.size_generator`, `Cslib.MCSP.AntiChecker.cost_generator`,
  `Cslib.MCSP.AntiChecker.depthWith_generator_le`,
  `Cslib.MCSP.AntiChecker.fanInAtMost_generator`: the measures of the generator.
* `Cslib.MCSP.AntiChecker.antiCheckerRounds_le`,
  `Cslib.MCSP.AntiChecker.queryLength_antiChecker_le`: polynomial bounds on the parameters.

## References

* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
-/

public section

namespace Cslib.MCSP.AntiChecker

open Circuits Circuits.Boolean Turing.MultiTapeTM

/-! ### Query words read from sources -/

section Sources

variable {K : ℕ}

/-- `frame` on words of sources: each source preceded by the constant `true`, then the constant
`false`. -/
private def frameSrc (w : List (Source K)) : List (Source K) :=
  w.flatMap (fun a => [.inr true, a]) ++ [.inr false]

private theorem map_frameSrc (v : BitString K) (w : List (Source K)) :
    (frameSrc w).map (Sum.elim v id) = frame (w.map (Sum.elim v id)) := by
  simp [frameSrc, frame, List.map_flatMap, List.flatMap_map]

/-- An `encQuery` word is the word of its parameters followed by the frames of its samples. -/
private theorem encQuery_eq_append (n s ℓ u : ℕ) (P : List (List Bool × Bool)) :
    encQuery ⟨n, s, ℓ, u, P⟩ =
      encQuery ⟨n, s, ℓ, u, []⟩ ++ P.flatMap fun p => frame (frame p.1 ++ [p.2]) := by
  simp [encQuery_apply, encQueryFields, encList, Function.comp_def]

/-- The sources of the query with parameters `n`, `s`, `ℓ`, `u` and samples whose inputs and labels
are read from the sources `P`: the parameters as constants, then the frame of each sample. -/
def querySources (n s ℓ u : ℕ) (P : List (List (Source K) × Source K)) : List (Source K) :=
  (encQuery ⟨n, s, ℓ, u, []⟩).map .inr ++ P.flatMap fun p => frameSrc (frameSrc p.1 ++ [p.2])

/-- **Reading a query word from sources.** On the wires `v`, the sources of a query read the
`encQuery` word of the samples read from `v`. -/
theorem map_querySources (v : BitString K) (n s ℓ u : ℕ) (P : List (List (Source K) × Source K)) :
    (querySources n s ℓ u P).map (Sum.elim v id) =
      encQuery ⟨n, s, ℓ, u, P.map fun p => (p.1.map (Sum.elim v id), Sum.elim v id p.2)⟩ := by
  rw [querySources, encQuery_eq_append n s ℓ u (P.map _), List.map_append, List.map_map]
  simp [List.map_flatMap, List.flatMap_map, map_frameSrc, Function.comp_def]

/-- The length of a query word read from sources. -/
theorem length_querySources (n s ℓ u : ℕ) (P : List (List (Source K) × Source K)) :
    (querySources n s ℓ u P).length =
      2 * (n + s + ℓ + u) + 4 + (P.map fun p => 4 * p.1.length + 5).sum := by
  have h := congrArg List.length (map_querySources (fun _ => false) n s ℓ u P)
  rw [List.length_map, length_encQuery] at h
  rw [h]
  simp [Function.comp_def]

end Sources

/-! ### The generator -/

variable {n : ℕ}

/-- The length of a query with threshold `u` and `t` samples of inputs of `n` bits, for circuits
with at most `s` gates and power `ℓ`. -/
def queryLength (n s ℓ u t : ℕ) : ℕ :=
  2 * (n + s + ℓ + u) + 4 + t * (4 * n + 5)

/-- A greedy query with `t` samples has length `queryLength n s ℓ u t`. -/
theorem length_encQuery_ofSamples_eq_queryLength (n s ℓ u : ℕ) (P : List (BitString n × Bool)) :
    (encQuery (Query.ofSamples n s ℓ u P)).length = queryLength n s ℓ u P.length :=
  length_encQuery_ofSamples n s ℓ u P

/-- Wire `b` of block `j` among `r` blocks of `n + 1` wires after the truth table. -/
def blockWire {r : ℕ} (j : Fin r) (b : Fin (n + 1)) : Fin (2 ^ n + (n + 1) * r) :=
  ⟨2 ^ n + (n + 1) * j + b, by
    have := Nat.mul_le_mul_left (n + 1) (Nat.succ_le_of_lt j.isLt)
    rw [Nat.mul_succ] at this
    omega⟩

/-- The sources of the sample in block `j`: its `n` input wires and its label wire. -/
def blockSources {r : ℕ} (j : Fin r) :
    List (Source (2 ^ n + (n + 1) * r)) × Source (2 ^ n + (n + 1) * r) :=
  (List.ofFn fun b : Fin n => .inl (blockWire j b.castSucc), .inl (blockWire j (Fin.last n)))

/-- The sources of the sample `(y, T y)`: the bits of `y` as constants, then the table wire of
`y`. -/
private def inputSources (r : ℕ) (y : BitString n) :
    List (Source (2 ^ n + (n + 1) * r)) × Source (2 ^ n + (n + 1) * r) :=
  ((List.ofFn y).map .inr, .inl (Fin.castAdd _ (BitString.equivFin n y)))

/-- The sources of round `r`'s query about the input `y`: the samples of the `r` earlier blocks and
the sample `(y, T y)`, with threshold `R - 1 - r`. -/
private def roundSources (s ℓ R r : ℕ) (y : BitString n) :
    List (Source (2 ^ n + (n + 1) * r)) :=
  querySources n s ℓ (R - 1 - r) (List.ofFn (fun j : Fin r => blockSources j) ++ [inputSources r y])

/-- Round `r`'s queries have `r + 1` samples and threshold `R - 1 - r`. -/
private theorem length_roundSources (s ℓ R r : ℕ) (y : BitString n) :
    (roundSources s ℓ R r y).length = queryLength n s ℓ (R - 1 - r) (r + 1) := by
  simp [roundSources, length_querySources, blockSources, inputSources, queryLength, List.sum_ofFn]
  ring

/-- Round `r`'s query about the `i`-th input, read from sources. -/
private def roundSrc (s ℓ R r : ℕ) (i : Fin (2 ^ n))
    (a : Fin (queryLength n s ℓ (R - 1 - r) (r + 1))) :
    Source (2 ^ n + (n + 1) * r) :=
  (roundSources s ℓ R r ((BitString.equivFin n).symm i)).get
    (a.cast (length_roundSources s ℓ R r _).symm)

/-- The word of the sample `(y, T y)`: the bits of `y` as constants, then the table wire of `y`. -/
private def inputWord (r : ℕ) (y : BitString n) :
    Fin (n + 1) → Source (2 ^ n + (n + 1) * r) :=
  Fin.snoc (α := fun _ => Source (2 ^ n + (n + 1) * r)) (fun b => .inr (y b))
    (.inl (Fin.castAdd _ (BitString.equivFin n y)))

/-- Round `r` of `R`: the selection with threshold `R - 1 - r` over all `2 ^ n` inputs, with
default `(default, T default)`. -/
private def generatorRound (s ℓ R r : ℕ) :
    Circuit oracleSignature (2 ^ n + (n + 1) * r) (2 ^ n + (n + 1) * r + (n + 1)) :=
  selectionRound (roundSrc s ℓ R r) (fun i => inputWord r ((BitString.equivFin n).symm i))
    (inputWord r default)

/-- **The generator**: `R` rounds of the threshold greedy over the truth table of a function on
`n` inputs, for circuits with at most `s` gates and power `ℓ`. It keeps the table and appends one
block of `n + 1` wires per round, holding an input and its label. -/
def generator (n s ℓ R : ℕ) : Circuit oracleSignature (2 ^ n) (2 ^ n + (n + 1) * R) :=
  Circuit.accumulate (generatorRound (n := n) s ℓ R) R

/-- The samples in the blocks of an output of the generator: block `j` holds an input and its
label. -/
def samplesOf {R : ℕ} (z : BitString (2 ^ n + (n + 1) * R)) : List (BitString n × Bool) :=
  List.ofFn fun j : Fin R => (fun b => z (blockWire j b.castSucc), z (blockWire j (Fin.last n)))

/-- An output of `R` rounds holds `R` samples. -/
@[simp] theorem length_samplesOf {R : ℕ} (z : BitString (2 ^ n + (n + 1) * R)) :
    (samplesOf z).length = R := by
  simp [samplesOf]

/-- On an output `z`, the sources of the blocks read the samples of `z`. -/
theorem map_ofFn_blockSources {r : ℕ} (z : BitString (2 ^ n + (n + 1) * r)) :
    (List.ofFn fun j : Fin r => blockSources j).map
        (fun p => (p.1.map (Sum.elim z id), Sum.elim z id p.2)) =
      (samplesOf z).map fun p => (List.ofFn p.1, p.2) := by
  simp [samplesOf, blockSources, List.map_ofFn, Function.comp_def]

/-- **Reading the samples of an output as a query.** On an output `z`, the sources of the query
whose samples are the blocks read the `encQuery` word of the samples of `z`. -/
theorem map_querySources_blockSources {r : ℕ} (z : BitString (2 ^ n + (n + 1) * r)) (s ℓ u : ℕ) :
    (querySources n s ℓ u (List.ofFn fun j : Fin r => blockSources j)).map (Sum.elim z id) =
      encQuery (Query.ofSamples n s ℓ u (samplesOf z)) := by
  rw [map_querySources, map_ofFn_blockSources, Query.ofSamples]

/-- The answers of a language `O` to the greedy's queries `(P, u)` for circuits on `n` inputs with
at most `s` gates and power `ℓ`. -/
noncomputable def queryOracle (O : Language Bool) (n s ℓ : ℕ) (P : List (BitString n × Bool))
    (u : ℕ) : Bool :=
  @decide (encQuery (Query.ofSamples n s ℓ u P) ∈ O) (Classical.propDecidable _)

/-- `O` answers a greedy query yes exactly when its `encQuery` word is in `O`. -/
theorem queryOracle_eq_true_iff {O : Language Bool} {s ℓ u : ℕ} {P : List (BitString n × Bool)} :
    queryOracle O n s ℓ P u = true ↔ encQuery (Query.ofSamples n s ℓ u P) ∈ O :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-! ### The generator runs the greedy -/

section Run

variable {α : Type*} [Inhabited α] (O' : List (α × Bool) → ℕ → Bool) (f' : α → Bool)
  (cands : List α) (R : ℕ)

/-- The first `r` rounds of the greedy with `R` rounds. -/
private def run : ℕ → List (α × Bool)
  | 0 => []
  | r + 1 => step O' f' cands (R - 1 - r) (run r)

private theorem greedy_run : ∀ k j : ℕ, j + k = R →
    greedy O' f' cands k (run O' f' cands R j) = run O' f' cands R R
  | 0, j, h => by rw [greedy_zero, Nat.add_zero] at *; rw [h]
  | k + 1, j, h => by
    rw [greedy_succ, show k = R - 1 - j by omega, ← run, show R - 1 - j = k by omega]
    exact greedy_run k (j + 1) (by omega)

private theorem greedy_eq_run : greedy O' f' cands R [] = run O' f' cands R R :=
  greedy_run O' f' cands R R 0 (Nat.zero_add R)

end Run

/-- The word selected from candidates `g (e i)` accepted by `p (e i)`, with default `g default`, is
`g` of the first candidate in the list of the `e i` that `p` accepts. -/
private theorem eq_getD_find? {N : ℕ} {α β : Type*} [Inhabited α] {e : Fin N → α} {p : α → Bool}
    {g : α → β} {v : β}
    (h : (∃ i, p (e i) = true ∧ (∀ j < i, p (e j) = false) ∧ v = g (e i)) ∨
      ((∀ i, p (e i) = false) ∧ v = g default)) :
    v = g (((List.ofFn e).find? p).getD default) := by
  rcases h with ⟨i, hi, hlt, rfl⟩ | ⟨hnone, rfl⟩
  · have : (List.ofFn e).find? p = some (e i) := by
      rw [List.find?_eq_some_iff_getElem]
      refine ⟨hi, i, by simp, by simp, fun j hj => ?_⟩
      simp [hlt ⟨j, hj.trans i.isLt⟩ hj]
    rw [this, Option.getD_some]
  · have : (List.ofFn e).find? p = none := by
      rw [List.find?_eq_none]
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      simp [hnone i]
    rw [this, Option.getD_none]

private theorem substitute_inputWord (r : ℕ) (y : BitString n)
    (z : BitString (2 ^ n + (n + 1) * r)) :
    substitute (inputWord r y) z =
      Fin.snoc (α := fun _ => Bool) y (z (Fin.castAdd _ (BitString.equivFin n y))) := by
  funext b
  induction b using Fin.lastCases <;> simp [inputWord, substitute]

/-- **One round selects as the greedy does.** If the table wires carry the truth table of `f`,
round `r` appends the sample that the greedy selects after the samples already in the blocks. -/
private theorem selectedWord_generatorRound (O : Language Bool) (f : BooleanFunction n)
    (s ℓ R r : ℕ) (z : BitString (2 ^ n + (n + 1) * r))
    (hz : ∀ i : Fin (2 ^ n), z (Fin.castAdd _ i) = MCSP.truthTable n f i) :
    selectedWord O (roundSrc s ℓ R r) (fun i => inputWord r ((BitString.equivFin n).symm i))
        (inputWord r default) z =
      Fin.snoc (α := fun _ => Bool)
        (select (queryOracle O n s ℓ) f (BitString.enum n) (R - 1 - r) (samplesOf z))
        (f (select (queryOracle O n s ℓ) f (BitString.enum n) (R - 1 - r) (samplesOf z))) := by
  have hword (y : BitString n) :
      substitute (inputWord r y) z = Fin.snoc (α := fun _ => Bool) y (f y) := by
    rw [substitute_inputWord, hz]
    simp
  have hslice (i : Fin (2 ^ n)) :
      O.slice _ (substitute (roundSrc s ℓ R r i) z) =
        queryOracle O n s ℓ (samplesOf z ++
          [((BitString.equivFin n).symm i, f ((BitString.equivFin n).symm i))]) (R - 1 - r) := by
    have hofFn : List.ofFn (substitute (roundSrc s ℓ R r i) z) =
        (roundSources s ℓ R r ((BitString.equivFin n).symm i)).map (Sum.elim z id) := by
      apply List.ext_getElem
      · simp [length_roundSources]
      · intro a h₁ h₂
        simp [substitute, roundSrc]
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, queryOracle_eq_true_iff, hofFn, roundSources,
      map_querySources, List.map_append, map_ofFn_blockSources]
    simp [Query.ofSamples, inputSources, hz, Function.comp_def]
  have hspec := selectedWord_spec O (roundSrc s ℓ R r)
    (fun i => inputWord r ((BitString.equivFin n).symm i)) (inputWord r default) z
  simp only [hslice, hword] at hspec
  refine (eq_getD_find? (e := (BitString.equivFin n).symm)
    (p := fun y => queryOracle O n s ℓ (samplesOf z ++ [(y, f y)]) (R - 1 - r))
    (g := fun y => Fin.snoc (α := fun _ => Bool) y (f y)) hspec).trans ?_
  rw [select, BitString.enum_eq_ofFn]

private theorem eval_generatorRound (O : Language Bool) (s ℓ R r : ℕ)
    (y : BitString (2 ^ n + (n + 1) * r)) :
    (generatorRound s ℓ R r).eval (oracleInterpretation O) y =
      Fin.append y (selectedWord O (roundSrc s ℓ R r)
        (fun i => inputWord r ((BitString.equivFin n).symm i)) (inputWord r default) y) :=
  eval_selectionRound _ _ _ O y

/-- **The generator runs the greedy.** On the truth table of `f`, under any oracle `O`, the samples
in the output of `R` rounds are those of `R` rounds of the greedy against `O`'s answers, over the
inputs in the order of `Cslib.BitString.enum`. -/
theorem samplesOf_eval_generator (O : Language Bool) (n s ℓ R : ℕ) (f : BooleanFunction n) :
    samplesOf ((generator n s ℓ R).eval (oracleInterpretation O) (MCSP.truthTable n f)) =
      greedy (queryOracle O n s ℓ) f (BitString.enum n) R [] := by
  rw [greedy_eq_run]
  have hstep := eval_generatorRound (n := n) O s ℓ R
  suffices h : ∀ r, samplesOf ((Circuit.accumulate (generatorRound (n := n) s ℓ R) r).eval
      (oracleInterpretation O) (MCSP.truthTable n f)) =
        run (queryOracle O n s ℓ) f (BitString.enum n) R r from h R
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    have hz (i : Fin (2 ^ n)) :
        (Circuit.accumulate (generatorRound (n := n) s ℓ R) r).eval (oracleInterpretation O)
          (MCSP.truthTable n f) (Fin.castAdd _ i) = MCSP.truthTable n f i :=
      Circuit.eval_accumulate_input hstep _ r i
    have hsel := selectedWord_generatorRound O f s ℓ R r _ hz
    have hblock (b : Fin (n + 1)) :=
      Circuit.eval_accumulate_block hstep (MCSP.truthTable n f) (Nat.lt_succ_self r) b
    rw [run, step, ← ih]
    conv_lhs => rw [samplesOf, List.ofFn_succ', List.concat_eq_append]
    congr 1
    · unfold samplesOf
      refine List.ofFn_inj.2 (funext fun j => Prod.ext (funext fun b => ?_) ?_)
      · exact Circuit.eval_accumulate_prefix hstep _ (Nat.le_succ r) _ (blockWire j b.castSucc).2
      · exact Circuit.eval_accumulate_prefix hstep _ (Nat.le_succ r) _
          (blockWire j (Fin.last n)).2
    · refine congrArg (fun p => [p]) (Prod.ext (funext fun b => ?_) ?_)
      · exact (hblock b.castSucc).trans (by rw [hsel, Fin.snoc_castSucc])
      · exact (hblock (Fin.last n)).trans (by rw [hsel, Fin.snoc_last])

/-- **Every sample of the generator is a correct pair `(y, f y)`**, whatever the oracle. -/
theorem snd_eq_of_mem_samplesOf_eval_generator (O : Language Bool) (n s ℓ R : ℕ)
    (f : BooleanFunction n) {p : BitString n × Bool}
    (hp : p ∈ samplesOf ((generator n s ℓ R).eval (oracleInterpretation O)
      (MCSP.truthTable n f))) :
    p.2 = f p.1 := by
  rw [samplesOf_eval_generator] at hp
  exact forall_mem_greedy_snd_eq _ f _ (P := []) (by simp) R p hp

/-! ### The anti-checker generator -/

/-- The power of the anti-checker generator for circuits on `n` inputs with at most `s` gates:
`L + 200`, where `L` is the certificate length. -/
def antiCheckerPower (n s : ℕ) : ℕ :=
  certLength n s + 200

/-- The number of rounds of the anti-checker generator: `L (L + 200) + 1`, where `L` is the
certificate length. -/
def antiCheckerRounds (n s : ℕ) : ℕ :=
  certLength n s * (certLength n s + 200) + 1

/-- **The anti-checker generator.** Let `O` agree with the anti-checker oracle on query words, and
let `f` need more gates than `n` circuits with at most `s` gates and a circuit for their strict
majority. On the truth table of `f`, every circuit with at most `s` gates differs from `f` on one of
the inputs that the generator with the anti-checker parameters chooses. -/
theorem isAntiChecker_samplesOf_generator {n s : ℕ} (hn : 0 < n) {O : Language Bool}
    (hO : ∀ q : Query, encQuery q ∈ O ↔ encQuery q ∈ antiCheckerOracle) {f : BooleanFunction n}
    (hf : n * s + complexity interpretation (single (strictMajority n)) <
      complexity interpretation (single f)) :
    IsAntiChecker (computableFunctions n s) f
      {x | x ∈ (samplesOf ((generator n s (antiCheckerPower n s) (antiCheckerRounds n s)).eval
        (oracleInterpretation O) (MCSP.truthTable n f))).map Prod.fst} := by
  rw [samplesOf_eval_generator, antiCheckerRounds, antiCheckerPower]
  exact isAntiChecker_greedy hn hf (isThresholdOracle_of_eq_true_iff (Nat.succ_pos _)
    fun P u => by rw [queryOracle_eq_true_iff, hO])

/-! ### Measures -/

/-- The generator has `R (2 + 2 ^ n (3 n + 5))` gates. -/
theorem size_generator (n s ℓ R : ℕ) :
    (generator n s ℓ R).size = R * (2 + 2 ^ n * (3 * n + 5)) := by
  simp only [generator, Circuit.size_accumulate, generatorRound, size_selectionRound,
    Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- The generator has `R 2 ^ n` oracle gates. -/
theorem cost_generator (n s ℓ R : ℕ) :
    (generator n s ℓ R).program.cost OracleOp.queryWeight = R * 2 ^ n := by
  simp [generator, generatorRound, Circuit.cost_program_accumulate]

/-- The generator has at most `R` oracle gates on any path. -/
theorem depthWith_generator_le (n s ℓ R : ℕ) :
    (generator n s ℓ R).depthWith OracleOp.queryWeight ≤ R :=
  (Circuit.depthWith_accumulate_le (generatorRound (n := n) s ℓ R) OracleOp.queryWeight
    fun _ _ => depthWith_selectionRound_le _ _ _).trans (Nat.mul_one R).le

/-- Every gate of the generator reads at most `queryLength n s ℓ R R` wires. -/
theorem fanInAtMost_generator (n s ℓ R : ℕ) :
    (generator n s ℓ R).FanInAtMost (queryLength n s ℓ R R) :=
  Circuit.fanInAtMost_accumulate (generatorRound (n := n) s ℓ R) fun r hr =>
    (fanInAtMost_selectionRound _ _ _).mono <|
    max_le (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (by omega)) 4)
      (Nat.mul_le_mul_right _ hr)) (by unfold queryLength; omega)

/-- The certificate length is at most `3 (n + s + 1) ^ 2`. -/
private theorem certLength_le_three_mul_sq (n s : ℕ) :
    certLength n s ≤ 3 * (n + s + 1) ^ 2 := by
  have h : 3 * (n + s + 1) ^ 2 =
      certLength n s + (3 * n ^ 2 + s ^ 2 + 4 * n * s + 5 * n + s + 3) := by
    unfold certLength
    ring
  omega

/-- The anti-checker generator has at most `610 (n + s + 1) ^ 4` rounds. -/
theorem antiCheckerRounds_le (n s : ℕ) : antiCheckerRounds n s ≤ 610 * (n + s + 1) ^ 4 := by
  have hL := certLength_le_three_mul_sq n s
  have hm : 1 ≤ n + s + 1 := Nat.le_add_left 1 _
  set m := n + s + 1
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  calc antiCheckerRounds n s ≤ 3 * m ^ 2 * (3 * m ^ 2 + 200) + 1 := by
        unfold antiCheckerRounds
        gcongr
    _ ≤ 610 * m ^ 4 := by nlinarith

/-- The queries of the anti-checker generator have length at most `5000 (n + s + 1) ^ 5`. -/
theorem queryLength_antiChecker_le (n s : ℕ) :
    queryLength n s (antiCheckerPower n s) (antiCheckerRounds n s) (antiCheckerRounds n s) ≤
      5000 * (n + s + 1) ^ 5 := by
  have hL := certLength_le_three_mul_sq n s
  have hR := antiCheckerRounds_le n s
  have hm : 1 ≤ n + s + 1 := Nat.le_add_left 1 _
  set m := n + s + 1 with hmdef
  have hm2 : m ^ 2 ≤ m ^ 5 := Nat.pow_le_pow_right hm (by norm_num)
  have hm4 : m ^ 4 ≤ m ^ 5 := Nat.pow_le_pow_right hm (by norm_num)
  have hm1 : m ≤ m ^ 5 := by simpa using Nat.pow_le_pow_right hm (by norm_num : 1 ≤ 5)
  have hm0 : 1 ≤ m ^ 5 := Nat.one_le_pow _ _ hm
  have hn : 4 * n + 5 ≤ 5 * m := by omega
  have hRn : antiCheckerRounds n s * (4 * n + 5) ≤ 610 * m ^ 4 * (5 * m) :=
    Nat.mul_le_mul hR hn
  have h45 : m ^ 4 * m = m ^ 5 := by ring
  unfold queryLength antiCheckerPower
  nlinarith

end Cslib.MCSP.AntiChecker
