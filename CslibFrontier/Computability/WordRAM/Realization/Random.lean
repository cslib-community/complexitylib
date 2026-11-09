/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Bind
public import CslibFrontier.Computability.WordRAM.Realization.Branch
public import CslibFrontier.Computability.WordRAM.Realization.Program
public import CslibFrontier.Computability.WordRAM.Randomized.Law
public import CslibFrontier.DataStructure.StateTransition.Randomized

/-!
# Realizing memory clients with private coins

A memory client with private coins is a `ProbOracleComp Memory.Op.Result` program: it calls the
memory oracle and draws uniform coins. It runs against `(Memory.spec w).toRandomized.withCoins`,
the memory oracle beside uniform sampling. Linking a client of a randomized specification
through a memory refinement with its coins passed through (`RandomizedRefinement.withCoins`)
produces exactly such a program. `RealizesRand` certifies one uniform native emitter for a family
of them, as `Realizes` does for deterministic clients, with the same emitter, scratch bank,
frontier and register frame. The certificate gives the exact law instead of a single run. At
word size `w`, from native data whose memory abstraction is `s`, the emitted code's result words
and memory state have the law of `(Memory.spec w).toRandomized.withCoins.run (p d) s`, read
through the result encoding (`ExecRandLaw`). Every path runs within `C * (time d s + 1)`
instructions and makes at most `calls d s` `rand` calls. Both are worst-case bounds that hold on
every path, not expected ones.

Deterministic parts are certified by `Realizes`, including every certificate `realize` builds,
and enter unchanged (`Realizes.toRand`). A coin is one `rand` instruction (`RealizesRand.coin`).
Sequencing (`RealizesRand.bind`) needs the continuation's domain and budgets at every supported
intermediate state; these obligations become part of the visible domain. Branching on the live
words is `RealizesRand.branch`. A flat program from the native list-input convention halts within
its bound on every path, respects the `rand` budget and has the law of the client
(`RealizesRand.exists_init_program`). Runtime-bounded loops are in
`CslibFrontier.Computability.WordRAM.Realization.RandomLoop`.

## Main definitions

* `RealizesRand.Spec`, `RealizesRand.Witness`: the canonical contract and supplied data.
* `RealizesRand`: uniform native realization of a memory client with private coins, with its
  law, a worst-case instruction bound and a worst-case `rand` budget.

## Main results

* `Realizes.toRand`: deterministic certificates are randomized ones with no `rand` call.
* `Realizes.Witness.toRand`, `RealizesRand.coinWitness`, `RealizesRand.Witness.bind`: supplied
  deterministic entry, coin and shared-bank sequential data.
* `RealizesRand.coin`: a uniform draw from `[0, n]`, for a live word `n`.
* `RealizesRand.bind`, `RealizesRand.branch`: sequencing and branching.
* `RealizesRand.consequence`, `RealizesRand.congr`: weakening and transport along equal clients.
* `RealizesRand.exists_init_program`: a flat program with `RandHaltsWithin`, `RandCallsBounded` and
  the law of its halting configurations.

The randomized certificate is original infrastructure over the existing realization kernel, the
structured randomized semantics `ExecRandLaw` and the randomized specifications of
`DataStructure.StateTransition.Randomized`; no execution semantics or client language is added.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {B : Basis} {δ α β : Type} {k l m : ℕ}

/-- The existing pathwise execution, joint-law and register-frame contract for specified
resource parameters and a specified emitter. Both existential and supplied witnesses use it. -/
def RealizesRand.Spec (B : Basis) (p : δ → ProbOracleComp Memory.Op.Result α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (time calls : δ → Memory.State → ℕ) (n C : ℕ)
    (emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r) : Prop :=
  ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
    (tmp : Fin (l + n + 1) → Fin r),
    Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
    (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
    ¬(emit frontier src tmp).ReadsWidth ∧
    ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
      safe w d (memoryState frontier x) →
      (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid (memoryState frontier x)
        (p d) →
      ExecRandLaw w (emit frontier src tmp) x
        (fun y => ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i)
        (C * (time d (memoryState frontier x) + 1)) (calls d (memoryState frontier x))
        (fun y => (fun i : Fin l => y.regs (tmp (Fin.castAdd (n + 1) i)),
          memoryState frontier y))
        (((Memory.spec w).toRandomized.withCoins.run (p d) (memoryState frontier x)).map
          fun (a, s) => (output a, s))

/-- Uniform native realization of a family of memory clients with private coins. The emitter,
scratch size and exchange constant precede every runtime argument, word width and initial
memory, and the register conventions are those of `Realizes`. From admissible entry data, the
emitted code terminates on every path within `C * (time d s + 1)` instructions and `calls d s`
`rand` calls, keeps every register outside the scratch bank and the frontier, and the result words
together with the memory state have the law of the client's run, read through `output`. -/
def RealizesRand (B : Basis) (p : δ → ProbOracleComp Memory.Op.Result α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (time calls : δ → Memory.State → ℕ) : Prop :=
  ∃ n C : ℕ, ∃ emit, RealizesRand.Spec B p input output safe time calls n C emit

/-- Retain specified randomized realization data with the same existing law contract.
It changes neither the oracle model nor the observation or supported-path semantics. -/
structure RealizesRand.Witness (B : Basis) (p : δ → ProbOracleComp Memory.Op.Result α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (time calls : δ → Memory.State → ℕ) where
  /-- Auxiliary registers, excluding results and the reserved extra slot. -/
  scratchSize : ℕ
  /-- Exchange factor for the original visible time grade. -/
  factor : ℕ
  /-- One emitter, fixed before layout, width, memory and random outcomes. -/
  code : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
    (Fin (l + scratchSize + 1) → Fin r) → Code B r
  /-- The canonical original execution and law contract. -/
  code_spec : RealizesRand.Spec B p input output safe time calls scratchSize factor code

/-- Forget supplied resources and code while retaining the original randomized judgment. -/
theorem RealizesRand.Witness.toRealizesRand
    {p : δ → ProbOracleComp Memory.Op.Result α} {input : δ ↪ (Fin k → ℕ)}
    {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
    {time calls : δ → Memory.State → ℕ}
    (h : RealizesRand.Witness B p input output safe time calls) :
    RealizesRand B p input output safe time calls :=
  ⟨h.scratchSize, h.factor, h.code, h.code_spec⟩

namespace Realizes

variable {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

/-- **Deterministic parts.** A deterministic certificate, for instance one built by `realize`,
realizes the same client with coins available and unused: its law is the point mass at the
deterministic run, its time is the memory charge plus local work, and it makes no `rand` call. -/
def Witness.toRand (h : Witness B p input output safe work) :
    RealizesRand.Witness B (fun d => OracleComp.liftRight (p d)) input output safe
      (fun d s => memoryCost (p d) s + work d s) (fun _ _ => 0) where
  scratchSize := h.scratchSize
  factor := h.factor
  code := h.code
  code_spec := by
    intro r frontier src tmp hi hd hf hs
    obtain ⟨hnw, hrun⟩ := h.code_spec frontier src tmp hi hd hf hs
    refine ⟨hnw, fun w d x hx hin hsafe hv => ?_⟩
    have hv' := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ (p d)).mp
      (StateTransitionSpec.toRandomized_demonicValid_iff.mp
        (RandomizedSpec.demonicValid_liftRight_iff.mp hv))
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x hx hin hsafe hv'
    refine (ExecRandLaw.of_execWithin hy hframe).congr_law ?_
    rw [RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized, PMF.pure_map]
    exact congrArg PMF.pure (Prod.ext (funext hout) hm)

/-- The existential randomized entry supplied by the deterministic witness construction. -/
theorem toRand (h : Realizes B p input output safe work) :
    RealizesRand B (fun d => OracleComp.liftRight (p d)) input output safe
      (fun d s => memoryCost (p d) s + work d s) (fun _ _ => 0) := by
  obtain ⟨n, C, emit, he⟩ := h
  exact (Witness.toRand ⟨n, C, emit, he⟩).toRealizesRand

end Realizes

namespace RealizesRand

variable {p : δ → ProbOracleComp Memory.Op.Result α} {input : δ ↪ (Fin k → ℕ)}
  {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
  {time calls : δ → Memory.State → ℕ}

/-- Strengthen the visible domain, and enlarge the time and `rand` budgets on it. The entry word
and memory bounds may be used. -/
theorem consequence {safe' : ℕ → δ → Memory.State → Prop} {time' calls' : δ → Memory.State → ℕ}
    (h : RealizesRand B p input output safe time calls)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s → safe' w d s →
      safe w d s ∧ time d s ≤ time' d s ∧ calls d s ≤ calls' d s) :
    RealizesRand B p input output safe' time' calls' := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, emit, fun frontier src tmp hi hd hf hs => ?_⟩
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨hnw, fun w d x hx hin hsafe' hv => ?_⟩
  have hwords (i : Fin k) : Fits w (input d i) := congrFun hin i ▸ hx.1 (src i)
  obtain ⟨hsafe, htime, hcalls⟩ := hsafe w d _ hwords (wellFormed_memoryState hx) hsafe'
  exact (hrun w d x hx hin hsafe hv).mono (fun _ h => h)
    (Nat.mul_le_mul_left C (Nat.add_le_add_right htime 1)) hcalls

/-- Pointwise equal clients have the same certificates. -/
theorem congr {p' : δ → ProbOracleComp Memory.Op.Result α}
    (h : RealizesRand B p input output safe time calls) (hp : ∀ d, p d = p' d) :
    RealizesRand B p' input output safe time calls :=
  funext hp ▸ h

/-- **A coin.** Drawing uniformly from `[0, n]`, for a live word `n`, is one `rand` instruction
into the result slot. -/
def coinWitness (input : δ ↪ (Fin k → ℕ)) (i : Fin k) :
    Witness B (fun d => Fin.val <$> ProbOracleComp.sample (ProbComp.unifFin (input d i)))
      input (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (fun _ _ _ => True)
      (fun _ _ => 1) (fun _ _ => 1) where
  scratchSize := 0
  factor := 1
  code := fun _ src tmp => .rand (tmp 0) (src i)
  code_spec := by
    intro r frontier src tmp _ _ hf _
    refine ⟨fun h => h, fun w d x hx hin _ _ => ?_⟩
    have h := ExecRandLaw.rand (B := B) (w := w) (x := x) (dst := tmp 0) (src := src i)
      (P := fun y => ∀ j, j ≠ frontier → (∀ t, tmp t ≠ j) → y.regs j = x.regs j)
      (f := fun y => (fun j : Fin 1 => y.regs (tmp (Fin.castAdd (0 + 1) j)),
        memoryState frontier y))
      (hx.1 (src i)) fun c j _ hj => Function.update_of_ne (hj 0).symm _ _
    refine (h.mono (fun _ h => h) (by omega) le_rfl).congr_law ?_
    have hsrc : x.regs (src i) = input d i := congrFun hin i
    rw [RandomizedSpec.run_map, RandomizedSpec.withCoins_run_sample, ProbComp.eval_unifFin,
      PMF.map_comp, PMF.map_comp, ← hsrc]
    congr 1
    funext c
    refine Prod.ext (funext fun j => ?_) ?_
    · rw [Fin.fin_one_eq_zero j]
      simp [Data.set]
    · exact Memory.State.ext rfl (Function.update_of_ne (hf 0).symm _ _)

/-- The existential coin realization supplied by `coinWitness`. -/
theorem coin (input : δ ↪ (Fin k → ℕ)) (i : Fin k) :
    RealizesRand B (fun d => Fin.val <$> ProbOracleComp.sample (ProbComp.unifFin (input d i)))
      input (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (fun _ _ _ => True)
      (fun _ _ => 1) (fun _ _ => 1) :=
  (coinWitness input i).toRealizesRand

section Bind

variable {q : δ × α → ProbOracleComp Memory.Op.Result β} {answer : α ↪ (Fin l → ℕ)}
  {output : β ↪ (Fin m → ℕ)}
  {safeP : ℕ → δ → Memory.State → Prop} {safeQ : ℕ → δ × α → Memory.State → Prop}
  {timeP callsP : δ → Memory.State → ℕ} {timeQ callsQ : δ × α → Memory.State → ℕ}

/-- **Sequencing.** One uniform continuation emitter consumes the original environment and the
first computation's answer. Its domain and budgets must hold at every supported intermediate
answer and state, within the uniform budgets `T` and `R`; these obligations join the visible
domain. The laws compose by `PMF.bind`, the times and `rand` budgets add. -/
def Witness.bind (hP : Witness B p input answer safeP timeP callsP)
    (hQ : Witness B q (appendWords input answer) output safeQ timeQ callsQ)
    (T R : δ → Memory.State → ℕ) :
    Witness B (fun d => p d >>= fun a => q (d, a)) input output
      (fun w d s => safeP w d s ∧ ∀ a s',
        (a, s') ∈ ((Memory.spec w).toRandomized.withCoins.run (p d) s).support →
          safeQ w (d, a) s' ∧ timeQ (d, a) s' ≤ T d s ∧ callsQ (d, a) s' ≤ R d s)
      (fun d s => timeP d s + T d s + 1) (fun d s => callsP d s + R d s) :=
  let n₁ := hP.scratchSize
  let n₂ := hQ.scratchSize
  let C₁ := hP.factor
  let C₂ := hQ.factor
  let N := l + max n₁ n₂
  let left : Fin (m + n₂ + 1) → Fin (m + N + 1) := bindSharedLeft
  let right : Fin (l + n₁ + 1) → Fin (m + N + 1) := bindSharedRight
  let emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (m + N + 1) → Fin r) → Code B r := fun frontier src tmp =>
    .seq (hP.code frontier src (tmp ∘ right))
      (hQ.code frontier
        (Fin.append src (fun i => tmp (right (Fin.castAdd (n₁ + 1) i)))) (tmp ∘ left))
  ⟨N, max C₁ C₂, emit, by
    intro r frontier src tmp hi hd hf hs
    obtain ⟨hright, hleft, hnextDisjoint, hnextFrontier⟩ := bindShared_layout hi hd hf hs
    let nextSrc : Fin (k + l) → Fin r :=
      Fin.append src (fun i => tmp (right (Fin.castAdd (n₁ + 1) i)))
    obtain ⟨hnwP, hrunP⟩ := hP.code_spec frontier src (tmp ∘ right) hright
      (fun i j => hd i (right j)) (fun j => hf (right j)) hs
    obtain ⟨hnwQ, hrunQ⟩ := hQ.code_spec frontier nextSrc (tmp ∘ left) hleft hnextDisjoint
      (fun j => hf (left j)) hnextFrontier
    refine ⟨fun h => h.elim hnwP hnwQ, fun w d x hx hin hsafe hv => ?_⟩
    let s := memoryState frontier x
    let D := (Memory.spec w).toRandomized.withCoins
    have hv' : D.toSpec.DemonicValid s ((p d).bind fun a => q (d, a)) := hv
    obtain ⟨hvP, hvQ⟩ := StateTransitionSpec.DemonicValid.of_bind hv'
    obtain ⟨⟨a₀, -⟩, -⟩ := (D.run (p d) s).support_nonempty
    have : Nonempty α := ⟨a₀⟩
    have hdecode : ∀ a, Function.invFun answer (answer a) = a :=
      Function.leftInverse_invFun answer.injective
    let κ : (Fin l → ℕ) × Memory.State → PMF ((Fin m → ℕ) × Memory.State) := fun (v, s') =>
      (D.run (q (d, Function.invFun answer v)) s').map fun (b, s'') => (output b, s'')
    have h₁ := ((hrunP w d x hx hin hsafe.1 hvP).withBounded hx).withSupport
    have h := ExecRandLaw.seq (κ := κ)
      (Q := fun y => ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i)
      (T₂ := C₂ * (T d s + 1)) (R₂ := R d s)
      (f := fun y => (fun i : Fin m => y.regs (tmp (Fin.castAdd (N + 1) i)),
        memoryState frontier y)) h₁ fun z ⟨⟨hframe, hzb⟩, hzsup⟩ => by
      obtain ⟨⟨a, s'⟩, hmem, hz⟩ := (PMF.mem_support_map_iff _ _ _).mp hzsup
      have hzout : (fun i : Fin l => z.regs ((tmp ∘ right) (Fin.castAdd (n₁ + 1) i))) = answer a :=
        (congrArg Prod.fst hz).symm
      have hzs : memoryState frontier z = s' := (congrArg Prod.snd hz).symm
      have hinQ : z.regs ∘ nextSrc = (appendWords input answer) (d, a) := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · change z.regs (nextSrc (Fin.castAdd l j)) =
            Fin.append (input d) (answer a) (Fin.castAdd l j)
          simp only [nextSrc, Fin.append_left]
          exact (hframe (src j) (hs j) (fun t => (hd j (right t)).symm)).trans (congrFun hin j)
        · change z.regs (nextSrc (Fin.natAdd k j)) =
            Fin.append (input d) (answer a) (Fin.natAdd k j)
          simp only [nextSrc, Fin.append_right]
          exact congrFun hzout j
      obtain ⟨hsafeQ, htime, hcalls⟩ := hsafe.2 a s' hmem
      obtain ⟨tr, hrun⟩ := D.exists_clientRun_of_mem_support hvP hmem
      have hQ := hrunQ w (d, a) z hzb hinQ (hzs ▸ hsafeQ) (hzs ▸ hvQ a s' tr hrun)
      rw [hzs] at hQ
      have hκ : κ (answer a, s') = (D.run (q (d, a)) s').map fun (b, s'') => (output b, s'') := by
        simp only [κ, hdecode]
      change ExecRandLaw w _ z _ _ _ _
        (κ ((fun i : Fin l => z.regs ((tmp ∘ right) (Fin.castAdd (n₁ + 1) i))),
          memoryState frontier z))
      rw [hzout, hzs, hκ]
      exact hQ.mono (fun y hy i hif htmp => (hy i hif fun j => htmp (left j)).trans
        (hframe i hif fun j => htmp (right j)))
        (Nat.mul_le_mul_left C₂ (Nat.add_le_add_right htime 1)) hcalls
    refine (h.mono (fun _ h => h) ?_ le_rfl).congr_law ?_
    · change C₁ * (timeP d s + 1) + C₂ * (T d s + 1) ≤ max C₁ C₂ * (timeP d s + T d s + 1 + 1)
      calc
        _ ≤ max C₁ C₂ * (timeP d s + 1) + max C₁ C₂ * (T d s + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
            (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
        _ = _ := by ring
    · change ((D.run (p d) s).map fun (a, s') => (answer a, s')).bind κ =
        (D.run (p d >>= fun a => q (d, a)) s).map fun (b, s'') => (output b, s'')
      rw [PMF.bind_map, RandomizedSpec.run_bind, PMF.map_bind]
      congr 1
      funext ⟨a, s'⟩
      simp only [Function.comp_apply, κ, hdecode]⟩

/-- The existential sequential realization supplied by the shared-bank constructor. -/
theorem bind (hP : RealizesRand B p input answer safeP timeP callsP)
    (hQ : RealizesRand B q (appendWords input answer) output safeQ timeQ callsQ)
    (T R : δ → Memory.State → ℕ) :
    RealizesRand B (fun d => p d >>= fun a => q (d, a)) input output
      (fun w d s => safeP w d s ∧ ∀ a s',
        (a, s') ∈ ((Memory.spec w).toRandomized.withCoins.run (p d) s).support →
          safeQ w (d, a) s' ∧ timeQ (d, a) s' ≤ T d s ∧ callsQ (d, a) s' ≤ R d s)
      (fun d s => timeP d s + T d s + 1) (fun d s => callsP d s + R d s) := by
  obtain ⟨n₁, C₁, emitP, heP⟩ := hP
  obtain ⟨n₂, C₂, emitQ, heQ⟩ := hQ
  exact (Witness.bind ⟨n₁, C₁, emitP, heP⟩ ⟨n₂, C₂, emitQ, heQ⟩ T R).toRealizesRand

end Bind

section Branch

variable {pos neg : δ → ProbOracleComp Memory.Op.Result α}
  {safePos safeNeg : ℕ → δ → Memory.State → Prop}
  {timePos timeNeg callsPos callsNeg : δ → Memory.State → ℕ}

/-- **Branching** on a test of the live words. Only the selected alternative's domain and
budgets are required; the test and the jump are absorbed by the exchange constant. -/
theorem branch (c : Cond k) (hp : RealizesRand B pos input output safePos timePos callsPos)
    (hn : RealizesRand B neg input output safeNeg timeNeg callsNeg) :
    RealizesRand B (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun d s => if test c (input d) then timePos d s else timeNeg d s)
      (fun d s => if test c (input d) then callsPos d s else callsNeg d s) := by
  obtain ⟨np, Cp, ep, hep⟩ := hp
  obtain ⟨nn, Cn, en, hen⟩ := hn
  let ip : Fin (l + np + 1) → Fin (l + (np + nn) + 1) := Fin.castLE (by omega)
  let ineg : Fin (l + nn + 1) → Fin (l + (np + nn) + 1) := Fin.castLE (by omega)
  refine ⟨np + nn, max Cp Cn + 2, fun frontier src tmp =>
    .branch (c.rename src) (ep frontier src (tmp ∘ ip)) (en frontier src (tmp ∘ ineg)), ?_⟩
  intro r frontier src tmp hi hd hf hs
  have hip : Function.Injective (tmp ∘ ip) := fun a b hab =>
    Fin.ext (congrArg (fun z : Fin (l + (np + nn) + 1) => z.val) (hi hab))
  have hin : Function.Injective (tmp ∘ ineg) := fun a b hab =>
    Fin.ext (congrArg (fun z : Fin (l + (np + nn) + 1) => z.val) (hi hab))
  obtain ⟨hnp, hrp⟩ := hep frontier src (tmp ∘ ip) hip
    (fun i j => hd i (ip j)) (fun j => hf (ip j)) hs
  obtain ⟨hnn, hrn⟩ := hen frontier src (tmp ∘ ineg) hin
    (fun i j => hd i (ineg j)) (fun j => hf (ineg j)) hs
  refine ⟨fun h => h.elim hnp hnn, fun w d x hx hinput hsafe hv => ?_⟩
  have hc := test_rename c src x (input d) hinput
  have hle (C t : ℕ) (hC : C ≤ max Cp Cn) (e : ℕ) (he : e ≤ 2) :
      C * (t + 1) + e ≤ (max Cp Cn + 2) * (t + 1) := by
    have := Nat.mul_le_mul_right (t + 1) hC
    nlinarith
  by_cases ht : test c (input d)
  · simp only [ite_eq_left ht] at hsafe hv ⊢
    exact ((hrp w d x hx hinput hsafe hv).branch_pos (hc.mpr ht)).mono
      (fun y hy i hif htmp => hy i hif fun j => htmp (ip j))
      (hle Cp _ (Nat.le_max_left _ _) 1 (by omega)) le_rfl
  · simp only [ite_eq_right ht] at hsafe hv ⊢
    exact ((hrn w d x hx hinput hsafe hv).branch_neg (fun h => ht (hc.mp h))).mono
      (fun y hy i hif htmp => hy i hif fun j => htmp (ineg j))
      (hle Cn _ (Nat.le_max_right _ _) 2 le_rfl) le_rfl

end Branch

/-- **Flat programs.** Each static coordinate of the result has one flat exact-basis program from
the native list-input convention. On an input list whose first `k` words encode the environment,
it halts on every path within its bound, makes at most the budgeted `rand` calls, and the halting
output word together with the memory state has the law of the client's run from the whole input
memory, read at that coordinate. The rest of the input list is arbitrary memory content, such as
a graph the client reads. The argument installation is absorbed into the exchange constant; the
bound includes the trailing halt. -/
theorem exists_init_program (h : RealizesRand .exact p input output safe time calls) :
    ∃ n C : ℕ,
      ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
          (Fin (l + n + 1) → Fin r) → Code .exact r,
        ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
          (tmp : Fin (l + n + 1) → Fin r),
          Function.Injective src → Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
          (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
          ∀ (i : Fin l) (w : ℕ) (d : δ) (xs : List ℕ), (∀ j : Fin k, xs.getD j.val 0 = input d j) →
          k ≤ xs.length → Fits w (xs.length + 1) → InputFits w xs → safe w d (inputState xs) →
          (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid (inputState xs) (p d) →
          ∀ F : RandCfg r → ℕ × Memory.State,
          (∀ v y, F (.halted v y) = (v, memoryState frontier y)) →
          RandHaltsWithin w ((Code.seq (inputPrefix frontier (tmp (Fin.last (l + n))) src)
              (emit frontier src tmp)).program (tmp (Fin.castAdd (n + 1) i)))
            (State.init xs) (C * (time d (inputState xs) + 1) + 1) ∧
          RandCallsBounded w ((Code.seq (inputPrefix frontier (tmp (Fin.last (l + n))) src)
              (emit frontier src tmp)).program (tmp (Fin.castAdd (n + 1) i)))
            (State.init xs) (C * (time d (inputState xs) + 1) + 1) (calls d (inputState xs)) ∧
          (evalRand w ((Code.seq (inputPrefix frontier (tmp (Fin.last (l + n))) src)
              (emit frontier src tmp)).program (tmp (Fin.castAdd (n + 1) i)))
            (C * (time d (inputState xs) + 1) + 1) (State.init xs)).map F =
            ((Memory.spec w).toRandomized.withCoins.run (p d) (inputState xs)).map
              fun (a, s) => (output a i, s) := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C + (2 * k + 5), emit, ?_⟩
  intro r frontier src tmp hsrc htmp hd hf hs i w d xs hlayout hk hw hin hsafe hv F hF
  obtain ⟨x, ex, hx, hm, hwords, -⟩ :=
    inputPrefix_exec frontier (tmp (Fin.last (l + n))) src xs hsrc
      (hf _) (fun j => hd j _) hs hk hw hin
  have harg : x.regs ∘ src = input d := funext fun j => (hwords j).trans (hlayout j)
  have h₁ := (he frontier src tmp htmp hd hf hs).2 w d x hx harg (hm.symm ▸ hsafe)
    (hm.symm ▸ hv)
  rw [hm] at h₁
  have h₂ := ExecRandLaw.seq_det ex (h₁.map fun (v, s) => (v i, s))
  have hT : 2 * k + 5 + C * (time d (inputState xs) + 1) + 1 ≤
      (C + (2 * k + 5)) * (time d (inputState xs) + 1) + 1 := by
    rw [Nat.add_mul]
    have := Nat.mul_le_mul_left (2 * k + 5) (Nat.le_add_left 1 (time d (inputState xs)))
    omega
  obtain ⟨hhalt, hcalls, -, hlaw⟩ := h₂.program (tmp (Fin.castAdd (n + 1) i)) hT F
    fun y _ => hF _ y
  refine ⟨hhalt, hcalls, hlaw.trans ?_⟩
  rw [PMF.map_comp]
  rfl

end RealizesRand

end Cslib.WordRAM.Realization
