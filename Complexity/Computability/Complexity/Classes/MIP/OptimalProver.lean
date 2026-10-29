/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.MIP.Defs
public import Complexity.Computability.Complexity.Classes.IP.CoinFixing

/-!
# Deterministic prover optimality and history consistency for `MIP`

Fixing the private coins of a multi-channel probabilistic oracle Turing machine `M` running under
clock `t` yields a finite family of deterministic multi-channel query programs
`Cslib.Complexity.Interaction.coinProgram M t x r : WordQueryComp Oracle Bool`, and averaging over
uniform `t`-bit coin strings reproduces `M.runOracle t x` against any stateful multi-channel oracle
(`Cslib.Complexity.Interaction.acceptProb_eq_sum`), in particular against `Prover.independent P`.

For any bounded family of multi-channel query programs, any independent family of
stateful randomized provers `P : ι → Prover Unit` can be replaced by an independent family of
deterministic stateful provers `D : ι → DetProver` without decreasing the expected acceptance
probability (`Cslib.Complexity.MIP.exists_deterministic_prover_family`). We establish this by
presampling a finite-depth deterministic response tree (`Cslib.Complexity.MIP.TreeStrategy`,
`Cslib.Complexity.MIP.presampleTree`) independently for each prover channel before the protocol
starts, showing that the presampled tree family reproduces the exact output distribution on every
coin branch, and selecting a maximizing deterministic tree tuple over the finite support.

Finally, we formalize deterministic single-prover strategies (`Cslib.Complexity.MIP.DetProver`),
pairwise history consistency (`Cslib.Complexity.MIP.consistentHist`), and the candidate-filtering
prover (`Cslib.Complexity.MIP.candidateProver`), proving that a finite list of single-prover
histories is realizable by a deterministic prover if and only if it is pairwise consistent.

## Main definitions

* `Cslib.Complexity.MIP.IsBoundedComp`: depth and query/reply length bounds on a
  `WordQueryComp ι α`.
* `Cslib.Complexity.MIP.TreeStrategy`, `Cslib.Complexity.MIP.presampleTree`: finite-depth
  deterministic response trees and their presampling distribution from a randomized prover.
* `Cslib.Complexity.MIP.DetProver`, `Cslib.Complexity.MIP.consistentHist`,
  `Cslib.Complexity.MIP.candidateProver`: deterministic provers and history consistency.

## Main results

* `Cslib.Complexity.MIP.isBoundedComp_coinFamily`: fixed-coin verifier programs form a bounded
  multi-channel family.
* `Cslib.Complexity.MIP.exists_deterministic_prover_family`: deterministic provers are optimal for
  multiprover interactive proofs.
* `Cslib.Complexity.MIP.DetProver.ValidFrom.consistentHist`,
  `Cslib.Complexity.MIP.validFrom_candidateProver`: characterization of deterministic prover
  histories via `consistentHist`.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.5][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.MIP

open Cslib.Probability Cslib.Complexity.Interaction
open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
open scoped ENNReal

variable {k : ℕ} {Control Oracle ι α β : Type}

/-! ### Bounded multi-channel query programs -/

/-- `IsBoundedComp L k p` states that the deterministic multi-channel query program `p` makes at
most `k` queries along every execution path, every query word has length at most `L`, and every
continuation depends only on the first `L` bits of the reply. -/
inductive IsBoundedComp (L : ℕ) : ℕ → WordQueryComp ι α → Prop
  | pure (n : ℕ) (a : α) : IsBoundedComp L n (pure a)
  | liftBind {n : ℕ} (q : ι × List Bool) (next : List Bool → WordQueryComp ι α) :
      q.2.length ≤ L →
      (∀ y, next y = next (y.take L)) →
      (∀ y, IsBoundedComp L n (next y)) →
      IsBoundedComp L (n + 1) (.liftBind q next)

namespace IsBoundedComp

theorem mono {L m n : ℕ} {p : WordQueryComp ι α} (hp : IsBoundedComp L m p) (hmn : m ≤ n) :
    IsBoundedComp L n p := by
  induction hp generalizing n with
  | pure m a => exact .pure n a
  | @liftBind m₀ q next hq htake _ ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by lia⟩
    exact .liftBind q next hq htake fun y => ih y (by lia)

theorem bind {L m n : ℕ} {p : WordQueryComp ι α} {k : α → WordQueryComp ι β}
    (hp : IsBoundedComp L m p) (hk : ∀ a, IsBoundedComp L n (k a)) :
    IsBoundedComp L (m + n) (p >>= k) := by
  induction hp with
  | pure m a =>
    change IsBoundedComp L (m + n) (k a)
    exact (hk a).mono (Nat.le_add_left n m)
  | @liftBind m₀ q next hq htake _ ih =>
    rw [Nat.add_right_comm m₀ 1 n]
    refine .liftBind q (fun y => next y >>= k) hq (fun y => ?_) (fun y => ih y)
    rw [htake y]

theorem map {L m : ℕ} {p : WordQueryComp ι α} (f : α → β) (hp : IsBoundedComp L m p) :
    IsBoundedComp L m (f <$> p) := by
  rw [← bind_pure_comp]
  simpa using hp.bind fun a => .pure 0 (f a)

end IsBoundedComp

section CoinBounds

variable [DecidableEq Oracle] (M : MultiTapePTM k Bool Control Oracle)

/-- Every configuration reachable by `coinStep M t cfg b` from a configuration with query buffers
of length at most `i` has query buffers of length at most `i + 1`, and `coinStep M t cfg b` is a
1-query bounded program when `i ≤ t`. -/
private theorem isBoundedComp_coinStep_bind {t i n : ℕ} {cfg : FiniteConfig k Bool Control Oracle}
    (hbuf : ∀ op, (cfg.channels op).1.length ≤ i) (hit : i ≤ t) (b : Bool)
    {cont : FiniteConfig k Bool Control Oracle → WordQueryComp Oracle α}
    (hcont : ∀ cfg', (∀ op, (cfg'.channels op).1.length ≤ i + 1) → IsBoundedComp t n (cont cfg')) :
    IsBoundedComp t (n + 1) (coinStep M t cfg b >>= cont) := by
  unfold coinStep MultiTapeMachine.finiteStep
  cases cfg.tapes.state with
  | none =>
    simp only [pure_bind]
    exact (hcont cfg fun op => (hbuf op).trans (Nat.le_succ i)).mono (Nat.le_succ n)
  | some c =>
    simp only [map_pure, pure_bind]
    cases M.tr c cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols b with
    | step action symbol move =>
      simp only [pure_bind]
      refine (hcont _ fun op => ?_).mono (Nat.le_succ n)
      simp only [FiniteConfig.step, List.length_append]
      exact Nat.add_le_add (hbuf op) (symbol op).length_toList_le
    | query op next =>
      change IsBoundedComp t (n + 1)
        (.liftBind (op, (cfg.channels op).1) fun y => cont (cfg.receive op next (y.take t)))
      refine .liftBind (op, (cfg.channels op).1)
        (fun y => cont (cfg.receive op next (y.take t)))
        ((hbuf op).trans hit)
        (fun y => by simp only [List.take_take, min_self])
        (fun y => hcont _ fun op' => ?_)
      by_cases heq : op' = op
      · subst heq
        simp [FiniteConfig.receive]
      · simpa [FiniteConfig.receive, heq] using (hbuf op').trans (Nat.le_succ i)

/-- Folding `coinStep M t` over a list of coins `r` produces a bounded query program. -/
private theorem isBoundedComp_foldlM_coinStep (t : ℕ) (r : List Bool) :
    ∀ (i : ℕ) (cfg : FiniteConfig k Bool Control Oracle),
      (∀ op, (cfg.channels op).1.length ≤ i) → i + r.length ≤ t →
      IsBoundedComp t r.length (r.foldlM (coinStep M t) cfg) := by
  induction r with
  | nil =>
    intro i cfg _ _
    exact .pure 0 cfg
  | cons b r ih =>
    intro i cfg hbuf hit
    simp only [List.length_cons] at hit
    simp only [List.foldlM_cons, List.length_cons]
    exact isBoundedComp_coinStep_bind M hbuf (by lia) b fun cfg' hbuf' =>
      ih (i + 1) cfg' hbuf' (by lia)

/-- `coinProgram M t x r` is a `t`-bounded query program of depth `r.length` whenever
`r.length ≤ t`. -/
private theorem isBoundedComp_coinProgram (t : ℕ) (x r : List Bool) (hr : r.length ≤ t) :
    IsBoundedComp t r.length (coinProgram M t x r) := by
  unfold coinProgram
  refine IsBoundedComp.map _ (isBoundedComp_foldlM_coinStep M t r 0
    (FiniteConfig.init M.initial x) (fun _ => by simp [FiniteConfig.init]) (by lia))

/-- Every member of `coinFamily M t x` is a `t`-bounded query program of depth `t`. -/
theorem isBoundedComp_coinFamily (t : ℕ) (x : List Bool) (r : Fin t → Bool) :
    IsBoundedComp t t (coinFamily M t x r) := by
  simpa [coinFamily, List.length_ofFn] using
    isBoundedComp_coinProgram M t x (List.ofFn r) (by simp)

end CoinBounds

/-! ### Deterministic provers, tree strategies, and presampling -/

/-- A deterministic single-prover strategy with internal state `State`. -/
structure DetProver where
  /-- Internal memory across rounds. -/
  State : Type
  /-- Initial state before any query. -/
  init : State
  /-- Deterministic response `(reply, nextState)` to a query word in a given state. -/
  respond : List Bool → State → List Bool × State

/-- Embed a deterministic prover as a `Prover Unit`. -/
noncomputable abbrev DetProver.toProver (D : DetProver) : Prover Unit where
  State := D.State
  init := D.init
  respond q := StateT.mk fun s => PMF.pure (D.respond q.2 s)

/-- A finite-depth deterministic response tree for a single prover. At depth `d + 1`, the tree is an
association list mapping each query word `m` to a reply `y` and a continuation tree of depth `d`. -/
abbrev TreeStrategy : ℕ → Type
  | 0 => PUnit
  | d + 1 => List (List Bool × (List Bool × TreeStrategy d))

/-- Step a `TreeStrategy` on query `m`, returning the reply and the next `(depth, tree)` pair. -/
def TreeStrategy.step : {d : ℕ} → TreeStrategy d → List Bool → List Bool × Sigma TreeStrategy
  | 0, _, _ => ([], ⟨0, PUnit.unit⟩)
  | d + 1, table, m =>
    match table.lookup m with
    | some (y, child) => (y, ⟨d, child⟩)
    | none => ([], ⟨0, PUnit.unit⟩)

/-- Turn an initial `(depth, TreeStrategy)` pair into a `DetProver`. -/
private abbrev TreeStrategy.toDetProver (initTree : Sigma TreeStrategy) : DetProver where
  State := Sigma TreeStrategy
  init := initTree
  respond m s := s.2.step m

/-- Universal `Prover Unit` for tree strategies with initial state `⟨0, PUnit.unit⟩`; its `.respond`
operation depends only on the runtime `Sigma TreeStrategy` state. -/
private noncomputable abbrev treeProver : Prover Unit :=
  (TreeStrategy.toDetProver ⟨0, PUnit.unit⟩).toProver

/-- Presample a depth-`d` `TreeStrategy` from a stateful randomized prover `Q : Prover Unit`
starting at state `s`, over the candidate query list `queries`, truncating each reply to `L`
bits. -/
noncomputable def presampleTree (Q : Prover Unit) (L : ℕ) (queries : List (List Bool)) :
    (d : ℕ) → Q.State → PMF (TreeStrategy d)
  | 0, _ => PMF.pure PUnit.unit
  | d + 1, s =>
    queries.mapM fun m => do
      let ys ← (Q.respond ((), m)).run s
      (presampleTree Q L queries d ys.2).map fun child =>
        (m, (ys.1.take L, child))

/-- Looking up an element `m ∈ queries` in a table sampled via `queries.mapM` marginalizes all
other entries and returns the sample at `m`. -/
private theorem mapM_lookup_eq [BEq α] [LawfulBEq α] (f : α → PMF β) (queries : List α) {m : α}
    (hm : m ∈ queries) :
    (queries.mapM fun a => (f a).map fun b => (a, b)).map (List.lookup m) =
      (f m).map some := by
  induction queries with
  | nil => cases hm
  | cons a rest ih =>
    simp only [List.mapM_cons, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.bind_map, PMF.map_bind, PMF.pure_map,
      Function.comp_def]
    by_cases hma : m = a
    · subst hma
      have hhead (b : β) (tbl : List (α × β)) : List.lookup m ((m, b) :: tbl) = some b := by
        rw [List.lookup, beq_self_eq_true]
      simp only [hhead, PMF.bind_const]
      rfl
    · have htail (b : β) (tbl : List (α × β)) :
          List.lookup m ((a, b) :: tbl) = List.lookup m tbl := by
        rw [List.lookup, beq_false_of_ne hma]
      have hm' : m ∈ rest := List.mem_of_ne_of_mem hma hm
      simp only [htail, PMF.bind_const]
      exact ih hm'

/-- Stepping a presampled tree of depth `d + 1` on `m ∈ queries` has the exact same distribution
as running `Q.respond ((), m)` once, truncating the reply to `L` bits, and presampling a depth-`d`
continuation tree from the resulting prover state. -/
private theorem presampleTree_step (Q : Prover Unit) (L : ℕ) (queries : List (List Bool)) (d : ℕ)
    (s : Q.State) {m : List Bool} (hm : m ∈ queries) :
    (presampleTree Q L queries (d + 1) s).map (fun t => t.step m) =
      ((Q.respond ((), m)).run s).bind fun ys =>
        (presampleTree Q L queries d ys.2).map fun child => (ys.1.take L, ⟨d, child⟩) := by
  let f : List Bool → PMF (List Bool × TreeStrategy d) := fun m' =>
    ((Q.respond ((), m')).run s).bind fun ys =>
      (presampleTree Q L queries d ys.2).map fun child => (ys.1.take L, child)
  have h1 : presampleTree Q L queries (d + 1) s =
      queries.mapM fun m' => (f m').map fun p => (m', p) := by
    simp only [presampleTree, f, Probability.PMF.monad_bind_eq_bind, PMF.map_bind,
      PMF.map_comp, Function.comp_def]
  have h2 := congrArg (PMF.map fun o : Option (List Bool × TreeStrategy d) =>
      match o with
      | some (y, child) => (y, (⟨d, child⟩ : Sigma TreeStrategy))
      | none => ([], ⟨0, PUnit.unit⟩))
    (mapM_lookup_eq f queries hm)
  simp only [PMF.map_comp, Function.comp_def] at h2
  refine (congrArg (PMF.map (fun t : TreeStrategy (d + 1) => t.step m)) h1).trans ?_
  simpa only [TreeStrategy.step, f, PMF.map_bind, PMF.map_comp, Function.comp_def] using h2

/-! ### Independent product presampling across prover channels -/

/-- Sample an `ι`-indexed tuple independently on the coordinates in `l`, defaulting to `default`
outside `l`. -/
private noncomputable def listPiPMF [DecidableEq ι] (default : α) (μ : ι → PMF α) :
    List ι → PMF (ι → α)
  | [] => PMF.pure (fun _ => default)
  | i :: rest => do
    let a ← μ i
    (listPiPMF default μ rest).map fun f => Function.update f i a

private theorem listPiPMF_congr [DecidableEq ι] (default : α) {μ₁ μ₂ : ι → PMF α}
    (l : List ι) (h : ∀ i ∈ l, μ₁ i = μ₂ i) :
    listPiPMF default μ₁ l = listPiPMF default μ₂ l := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
    simp only [listPiPMF, h i List.mem_cons_self,
      ih fun j hj => h j (List.mem_cons_of_mem i hj)]

/-- Factor out coordinate `i₀ ∈ l` from `listPiPMF` when `l.Nodup`. -/
private theorem listPiPMF_extract [DecidableEq ι] (default : α) (μ : ι → PMF α)
    (l : List ι) (hl : l.Nodup) {i₀ : ι} (hi₀ : i₀ ∈ l) :
    listPiPMF default μ l =
      (μ i₀).bind fun a =>
        (listPiPMF default μ (l.erase i₀)).map fun f => Function.update f i₀ a := by
  induction l with
  | nil => cases hi₀
  | cons i rest ih =>
    obtain ⟨_, hl_rest⟩ := List.nodup_cons.mp hl
    by_cases h : i₀ = i
    · subst h
      simp [listPiPMF]
    · have hi₀_rest : i₀ ∈ rest := List.mem_of_ne_of_mem h hi₀
      have herase : (i :: rest).erase i₀ = i :: rest.erase i₀ := by
        simp [Ne.symm h]
      rw [herase, listPiPMF, ih hl_rest hi₀_rest]
      simp only [listPiPMF, Probability.PMF.monad_bind_eq_bind, PMF.map_bind, PMF.map_comp,
        Function.comp_def]
      rw [PMF.bind_comm]
      congr 1
      funext a₀
      congr 1
      funext a
      congr 1
      funext f
      exact Function.update_comm h a₀ a f

/-- Presample an independent tuple of `Sigma TreeStrategy` across all channels `i : ι`. -/
private noncomputable def piPresample [Fintype ι] [DecidableEq ι] (P : ι → Prover Unit) (L : ℕ)
    (queries : List (List Bool)) (d : ι → ℕ) (s : ∀ i, (P i).State) :
    PMF (ι → Sigma TreeStrategy) :=
  listPiPMF ⟨0, PUnit.unit⟩
    (fun i => (presampleTree (P i) L queries (d i) (s i)).map fun t => ⟨d i, t⟩)
    (Finset.univ : Finset ι).toList

/-- Stepping channel `i₀` in `piPresample` on query `m ∈ queries` when `d i₀ = d' + 1` matches
running `(P i₀).respond ((), m)` and presampling at the updated depth and state vectors. -/
private theorem piPresample_step [Fintype ι] [DecidableEq ι] (P : ι → Prover Unit) (L : ℕ)
    (queries : List (List Bool)) (d : ι → ℕ) (s : ∀ i, (P i).State)
    (i₀ : ι) (d' : ℕ) (hd : d i₀ = d' + 1) {m : List Bool} (hm : m ∈ queries) :
    (piPresample P L queries d s).map (fun f =>
        let res := (f i₀).2.step m
        (res.1, Function.update f i₀ res.2)) =
      (((P i₀).respond ((), m)).run (s i₀)).bind fun ys =>
        (piPresample P L queries (Function.update d i₀ d') (Function.update s i₀ ys.2)).map
          fun f' => (ys.1.take L, f') := by
  let defaultTree : Sigma TreeStrategy := ⟨0, PUnit.unit⟩
  let mkLayer (i : ι) (k : ℕ) (si : (P i).State) : PMF (Sigma TreeStrategy) :=
    (presampleTree (P i) L queries k si).map fun t => ⟨k, t⟩
  let μ (d₀ : ι → ℕ) (s₀ : ∀ i, (P i).State) (i : ι) : PMF (Sigma TreeStrategy) :=
    mkLayer i (d₀ i) (s₀ i)
  have hl : (Finset.univ : Finset ι).toList.Nodup := Finset.nodup_toList Finset.univ
  have hi₀ : i₀ ∈ (Finset.univ : Finset ι).toList := Finset.mem_toList.mpr (Finset.mem_univ i₀)
  change (listPiPMF defaultTree (μ d s) (Finset.univ : Finset ι).toList).map _ = _
  rw [listPiPMF_extract defaultTree (μ d s) (Finset.univ : Finset ι).toList hl hi₀]
  have hμi₀ : μ d s i₀ =
      (presampleTree (P i₀) L queries (d' + 1) (s i₀)).map fun t => ⟨d' + 1, t⟩ := by
    change mkLayer i₀ (d i₀) (s i₀) = mkLayer i₀ (d' + 1) (s i₀)
    rw [hd]
  rw [hμi₀]
  have hupd (x : ι → Sigma TreeStrategy) (a : TreeStrategy (d' + 1)) :
      (Function.update x i₀ (Sigma.mk (d' + 1) a) i₀).2.step m = a.step m := by
    rw [Function.update_self]
  simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
    hupd, Function.update_idem]
  have hstep := congrArg (PMF.bind · fun (res : List Bool × Sigma TreeStrategy) =>
      (listPiPMF defaultTree (μ d s) ((Finset.univ : Finset ι).toList.erase i₀)).map fun f =>
        (res.1, Function.update f i₀ res.2))
    (presampleTree_step (P i₀) L queries d' (s i₀) hm)
  simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def] at hstep
  rw [hstep]
  congr 1
  funext ys
  have hcongr : listPiPMF defaultTree (μ d s) ((Finset.univ : Finset ι).toList.erase i₀) =
      listPiPMF defaultTree (μ (Function.update d i₀ d') (Function.update s i₀ ys.2))
        ((Finset.univ : Finset ι).toList.erase i₀) := by
    refine listPiPMF_congr defaultTree _ fun j hj => ?_
    have hjne : j ≠ i₀ := (List.Nodup.mem_erase_iff hl).mp hj |>.1
    simp only [μ, Function.update_of_ne hjne]
  rw [hcongr]
  have hextract2 := listPiPMF_extract defaultTree
    (μ (Function.update d i₀ d') (Function.update s i₀ ys.2)) (Finset.univ : Finset ι).toList hl hi₀
  have hμ' : μ (Function.update d i₀ d') (Function.update s i₀ ys.2) i₀ =
      (presampleTree (P i₀) L queries d' ys.2).map fun child => ⟨d', child⟩ := by
    change mkLayer i₀ (Function.update d i₀ d' i₀) (Function.update s i₀ ys.2 i₀) =
      mkLayer i₀ d' ys.2
    rw [Function.update_self, Function.update_self]
  change _ = (listPiPMF defaultTree
    (μ (Function.update d i₀ d') (Function.update s i₀ ys.2)) (Finset.univ : Finset ι).toList).map
      fun f' => (ys.1.take L, f')
  rw [hextract2, hμ']
  simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

theorem independent_respond [DecidableEq ι] (P : ι → Prover Unit) (q : ι × List Bool)
    (s : ∀ i, (P i).State) :
    ((Prover.independent P).respond q).run s =
      (((P q.1).respond ((), q.2)).run (s q.1)).map fun x =>
        (x.1, Function.update s q.1 x.2) :=
  rfl

/-- **Presampled tree equivalence**: running any bounded query program `p` (`IsBoundedComp L k p`)
against `Prover.independent P` from state `s` produces the exact same output distribution as
sampling `f ← piPresample P L (BitString.shortWords L).toList d s` (for any depth vector `d` with
`∀ i, k ≤ d i`) and running `p` deterministically against `treeProver` from state `f`. -/
private theorem run_eq_bind_piPresample [Fintype ι] [DecidableEq ι]
    {p : WordQueryComp ι α} {L k : ℕ}
    (hp : IsBoundedComp L k p) (P : ι → Prover Unit) (d : ι → ℕ) (hd : ∀ i, k ≤ d i)
    (s : ∀ i, (P i).State) :
    ((OracleComp.interpret (Prover.independent P).respond p).run s).map Prod.fst =
      (piPresample P L (BitString.shortWords L).toList d s).bind fun f =>
        ((OracleComp.interpret (Prover.independent (fun _ : ι => treeProver)).respond p).run f).map
          Prod.fst := by
  induction hp generalizing d s with
  | pure k a =>
    change ((OracleComp.interpret (Prover.independent P).respond (pure a)).run s).map Prod.fst =
      (piPresample P L (BitString.shortWords L).toList d s).bind fun f =>
        ((OracleComp.interpret (Prover.independent (fun _ : ι => treeProver)).respond
          (pure a)).run f).map Prod.fst
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.pure_map, PMF.bind_const]
  | @liftBind k q next hq htake _ ih =>
    obtain ⟨i₀, m⟩ := q
    have hm : m ∈ (BitString.shortWords L).toList :=
      Finset.mem_toList.mpr (BitString.mem_shortWords.mpr hq)
    have hdi₀ : d i₀ = (d i₀ - 1) + 1 := by
      have := hd i₀
      lia
    have hd' : ∀ i, k ≤ Function.update d i₀ (d i₀ - 1) i := by
      intro i
      by_cases h : i = i₀
      · subst h
        have := hd i
        simp only [Function.update_self]
        lia
      · simp only [Function.update_of_ne h]
        exact (Nat.le_succ k).trans (hd i)
    change ((OracleComp.interpret (Prover.independent P).respond
        (OracleComp.query (i₀, m) >>= next)).run s).map Prod.fst =
      (piPresample P L (BitString.shortWords L).toList d s).bind fun f =>
        ((OracleComp.interpret (Prover.independent (fun _ : ι => treeProver)).respond
          (OracleComp.query (i₀, m) >>= next)).run f).map Prod.fst
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.map_bind]
    have hrhs (f : ι → Sigma TreeStrategy) :
        (((Prover.independent (fun _ : ι => treeProver)).respond (i₀, m)).run f).bind
          (fun x => ((OracleComp.interpret (Prover.independent (fun _ : ι => treeProver)).respond
            (next x.1)).run x.2).map Prod.fst) =
        let res := (f i₀).2.step m
        ((OracleComp.interpret (Prover.independent (fun _ : ι => treeProver)).respond
          (next res.1)).run (Function.update f i₀ res.2)).map Prod.fst := by
      simp only [treeProver, DetProver.toProver, TreeStrategy.toDetProver, StateT.run_mk,
        PMF.pure_map, PMF.pure_bind]
    simp only [hrhs]
    have hstep := congrArg (PMF.bind · fun (p : List Bool × (ι → Sigma TreeStrategy)) =>
        ((OracleComp.interpret (Prover.independent (fun _ : ι => treeProver)).respond
          (next p.1)).run p.2).map Prod.fst)
      (piPresample_step P L (BitString.shortWords L).toList d s i₀ (d i₀ - 1) hdi₀ hm)
    simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def] at hstep
    rw [hstep]
    simp only [StateT.run_mk, PMF.bind_map, Function.comp_def]
    congr 1
    funext ys
    rw [ih ys.1 (Function.update d i₀ (d i₀ - 1)) hd' (Function.update s i₀ ys.2)]
    congr 1
    funext f'
    rw [← htake ys.1]
    rfl

/-! ### Finite support of presampled trees and deterministic prover optimality -/

/-- Cartesian product of a list of candidate lists along `l : List α`. -/
private def listMapM : List α → (α → List β) → List (List β)
  | [], _ => [[]]
  | a :: rest, S => (S a).flatMap fun b => (listMapM rest S).map (b :: ·)

private theorem mem_listMapM {l : List α} {g : α → PMF β} {S : α → List β}
    (hS : ∀ a ∈ l, ∀ b ∈ (g a).support, b ∈ S a) :
    ∀ xs ∈ (l.mapM g).support, xs ∈ listMapM l S := by
  induction l with
  | nil =>
    intro xs hxs
    simp only [List.mapM_nil, Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hxs
    subst hxs
    exact List.mem_singleton_self []
  | cons a rest ih =>
    intro xs hxs
    simp only [List.mapM_cons, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hxs
    obtain ⟨b, hb, ys, hys, rfl⟩ := hxs
    simp only [listMapM, List.mem_flatMap, List.mem_map]
    exact ⟨b, hS a List.mem_cons_self b hb, ys,
      ih (fun a' ha' => hS a' (List.mem_cons_of_mem a ha')) ys hys, rfl⟩

/-- Finite list of all `TreeStrategy d` values reachable when queries come from `queries` and
replies come from `BitString.shortWords L`. -/
private noncomputable def allTrees (L : ℕ) (queries : List (List Bool)) :
    (d : ℕ) → List (TreeStrategy d)
  | 0 => [PUnit.unit]
  | d + 1 =>
    listMapM queries fun m =>
      (BitString.shortWords L).toList.flatMap fun y =>
        (allTrees L queries d).map fun child => (m, (y, child))

private theorem support_presampleTree_subset (Q : Prover Unit) (L : ℕ)
    (queries : List (List Bool)) :
    ∀ (d : ℕ) (s : Q.State) (t : TreeStrategy d),
      t ∈ (presampleTree Q L queries d s).support → t ∈ allTrees L queries d := by
  intro d
  induction d with
  | zero =>
    intro _ t _
    cases t
    exact List.mem_singleton_self PUnit.unit
  | succ d ih =>
    intro s t ht
    simp only [presampleTree] at ht
    simp only [allTrees]
    refine mem_listMapM (fun m _ entry hentry => ?_) t ht
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hentry
    obtain ⟨ys, _, child, hchild, rfl⟩ := hentry
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨ys.1.take L, ?_, child, ih ys.2 child hchild, rfl⟩
    exact Finset.mem_toList.mpr (BitString.mem_shortWords.mpr (List.length_take_le L ys.1))

/-- Finite list of all `ι → α` functions built by `listPiPMF` from finite candidate lists `S i`. -/
private def allListPi [DecidableEq ι] (default : α) (S : ι → List α) : List ι → List (ι → α)
  | [] => [fun _ => default]
  | i :: rest =>
    (S i).flatMap fun a => (allListPi default S rest).map fun f => Function.update f i a

private theorem support_listPiPMF_subset [DecidableEq ι] (default : α)
    {μ : ι → PMF α} {S : ι → List α}
    (l : List ι) (hS : ∀ i ∈ l, ∀ a ∈ (μ i).support, a ∈ S i) :
    ∀ f ∈ (listPiPMF default μ l).support, f ∈ allListPi default S l := by
  induction l with
  | nil =>
    intro f hf
    simp only [listPiPMF, PMF.mem_support_pure_iff] at hf
    subst hf
    exact List.mem_singleton_self _
  | cons i rest ih =>
    intro f hf
    simp only [listPiPMF, Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hf
    obtain ⟨a, ha, g, hg, rfl⟩ := hf
    simp only [allListPi, List.mem_flatMap, List.mem_map]
    exact ⟨a, hS i List.mem_cons_self a ha, g,
      ih (fun j hj => hS j (List.mem_cons_of_mem i hj)) g hg, rfl⟩

/-- Select an element from a list maximizing `g : α → ℝ≥0∞`. -/
private noncomputable def bestOfList (g : α → ℝ≥0∞) (default : α) : List α → α
  | [] => default
  | a :: l =>
    let b := bestOfList g default l
    if g b ≤ g a then a else b

private theorem le_bestOfList (g : α → ℝ≥0∞) (default : α) (l : List α) {x : α} (hx : x ∈ l) :
    g x ≤ g (bestOfList g default l) := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [bestOfList]
    rcases List.mem_cons.mp hx with rfl | hx
    · split_ifs with h
      · exact le_rfl
      · exact le_of_not_ge h
    · split_ifs with h
      · exact (ih hx).trans h
      · exact ih hx

private theorem tsum_mul_le_bestOfList (μ : PMF α) (g : α → ℝ≥0∞) (default : α) (l : List α)
    (hsupp : ∀ x ∈ μ.support, x ∈ l) :
    ∑' x, μ x * g x ≤ g (bestOfList g default l) := by
  calc ∑' x, μ x * g x
      ≤ ∑' x, μ x * g (bestOfList g default l) := by
        refine tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ μ.support
        · exact mul_le_mul_right (le_bestOfList g default l (hsupp x hx)) (μ x)
        · rw [PMF.mem_support_iff, not_not] at hx
          simp [hx]
    _ = g (bestOfList g default l) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Deterministic prover optimality for bounded multi-channel families**: for any finite family
`F : γ → WordQueryComp ι Bool` of `L`-bounded query programs of depth at most `d`, any weights
`w : γ → ℝ≥0∞`, and any independent prover family `P : ι → Prover Unit`, there exists an
independent family of deterministic provers `D : ι → DetProver` whose weighted acceptance
probability is at least that of `P`. -/
theorem exists_deterministic_prover_family [Finite ι] [DecidableEq ι] {γ : Type} [Fintype γ]
    {L d : ℕ} (F : γ → WordQueryComp ι Bool) (hF : ∀ c, IsBoundedComp L d (F c))
    (w : γ → ℝ≥0∞) (P : ι → Prover Unit) :
    ∃ D : ι → DetProver,
      ∑ c, w c * acceptFrom (Prover.independent P) (Prover.independent P).init (some (F c)) ≤
        ∑ c, w c * acceptFrom (Prover.independent fun i => (D i).toProver)
          (Prover.independent fun i => (D i).toProver).init (some (F c)) := by
  cases nonempty_fintype ι
  let queries := (BitString.shortWords L).toList
  let μ := piPresample P L queries (fun _ => d) (Prover.independent P).init
  let g (f : ι → Sigma TreeStrategy) : ℝ≥0∞ :=
    ∑ c, w c * ((OracleComp.interpret (Prover.independent (fun _ : ι => treeProver)).respond
      (F c)).run f).map Prod.fst true
  have hsum : ∑ c, w c *
      acceptFrom (Prover.independent P) (Prover.independent P).init (some (F c)) =
      ∑' f, μ f * g f := by
    have hc (c : γ) :
        acceptFrom (Prover.independent P) (Prover.independent P).init (some (F c)) =
        ∑' f, μ f * ((OracleComp.interpret (Prover.independent (fun _ : ι => treeProver)).respond
          (F c)).run f).map Prod.fst true := by
      dsimp only [acceptFrom, Functor.map]
      rw [run_eq_bind_piPresample (hF c) P (fun _ => d) (fun _ => le_rfl)
        (Prover.independent P).init, PMF.bind_apply]
    simp only [hc, ← ENNReal.tsum_mul_left]
    rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
    refine tsum_congr fun f => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [mul_left_comm]
  let defaultTree : Sigma TreeStrategy := ⟨0, PUnit.unit⟩
  let S (_ : ι) : List (Sigma TreeStrategy) :=
    (allTrees L queries d).map fun t => Sigma.mk d t
  let candidates : List (ι → Sigma TreeStrategy) :=
    allListPi defaultTree S (Finset.univ : Finset ι).toList
  have hsupp : ∀ f ∈ μ.support, f ∈ candidates := by
    refine support_listPiPMF_subset defaultTree (Finset.univ : Finset ι).toList ?_
    intro i _ st hst
    simp only [PMF.mem_support_map_iff] at hst
    obtain ⟨t, ht, rfl⟩ := hst
    exact List.mem_map_of_mem (support_presampleTree_subset (P i) L queries d (P i).init t ht)
  let fBest := bestOfList g (fun _ => defaultTree) candidates
  refine ⟨fun i => TreeStrategy.toDetProver (fBest i), ?_⟩
  rw [hsum]
  exact tsum_mul_le_bestOfList μ g (fun _ => defaultTree) candidates hsupp

/-! ### Pairwise history consistency and the candidate-filtering prover -/

/-- A single-prover history `h : List (List Bool × List Bool)` is valid for `D : DetProver` from
state `s` when each reply matches `D.respond` and the remaining history is valid from the next
state. -/
def DetProver.ValidFrom (D : DetProver) : D.State → List (List Bool × List Bool) → Prop
  | _, [] => True
  | s, (q, r) :: rest =>
    r = (D.respond q s).1 ∧ D.ValidFrom (D.respond q s).2 rest

/-- Truncate every reply of a `DetProver` to its first `L` bits. -/
abbrev DetProver.truncate (L : ℕ) (D : DetProver) : DetProver where
  State := D.State
  init := D.init
  respond q s :=
    let res := D.respond q s
    (res.1.take L, res.2)

/-- Truncating the replies of deterministic provers to `L` bits preserves the exact output of any
`L`-bounded query program. -/
theorem acceptFrom_truncate_eq [DecidableEq ι] {p : WordQueryComp ι Bool} {L k : ℕ}
    (hp : IsBoundedComp L k p) (D : ι → DetProver) (s : ∀ i, (D i).State) :
    acceptFrom (Prover.independent fun i => ((D i).truncate L).toProver) s (some p) =
      acceptFrom (Prover.independent fun i => (D i).toProver) s (some p) := by
  induction hp generalizing s with
  | pure k b => rfl
  | @liftBind k q next _ htake _ ih =>
    obtain ⟨i₀, m⟩ := q
    change acceptFrom (Prover.independent fun i => ((D i).truncate L).toProver) s
        (some (OracleComp.query (i₀, m) >>= next)) =
      acceptFrom (Prover.independent fun i => (D i).toProver) s
        (some (OracleComp.query (i₀, m) >>= next))
    simp only [acceptFrom, OracleComp.interpret_bind, OracleComp.interpret_query,
      StateT.run_bind, Probability.PMF.monad_bind_eq_bind,
      DetProver.toProver, DetProver.truncate, StateT.run_mk, PMF.pure_map, PMF.pure_bind]
    rw [(htake ((D i₀).respond m (s i₀)).1).symm]
    simpa only [acceptFrom, DetProver.toProver, DetProver.truncate, StateT.run_mk,
      PMF.pure_map] using
      ih ((D i₀).respond m (s i₀)).1 (Function.update s i₀ ((D i₀).respond m (s i₀)).2)

/-- Two single-prover `(query, reply)` histories `h₁, h₂` are consistent with a deterministic
prover iff, along their common local history, equal next queries receive equal replies.
As soon as they receive distinct queries, their states can
diverge and no further constraint applies. -/
def consistentHist : List (List Bool × List Bool) → List (List Bool × List Bool) → Bool
  | [], _ => true
  | _, [] => true
  | (q₁, r₁) :: rest₁, (q₂, r₂) :: rest₂ =>
    if q₁ == q₂ then (r₁ == r₂) && consistentHist rest₁ rest₂ else true

/-- Any two histories valid for the same `DetProver` from the same state `s` satisfy
`consistentHist h₁ h₂ = true`. -/
theorem DetProver.ValidFrom.consistentHist {D : DetProver} {s : D.State}
    {h₁ h₂ : List (List Bool × List Bool)} (hv₁ : D.ValidFrom s h₁) (hv₂ : D.ValidFrom s h₂) :
    MIP.consistentHist h₁ h₂ = true := by
  induction h₁ generalizing s h₂ with
  | nil => rfl
  | cons e₁ rest₁ ih =>
    obtain ⟨q₁, r₁⟩ := e₁
    cases h₂ with
    | nil => rfl
    | cons e₂ rest₂ =>
      obtain ⟨q₂, r₂⟩ := e₂
      obtain ⟨hr₁, hv₁'⟩ := hv₁
      obtain ⟨hr₂, hv₂'⟩ := hv₂
      simp only [MIP.consistentHist]
      by_cases hq : q₁ = q₂
      · subst hq
        simp only [beq_self_eq_true, ↓reduceIte, hr₁, ← hr₂, Bool.true_and]
        exact ih hv₁' hv₂'
      · have hq' : (q₁ == q₂) = false := beq_false_of_ne hq
        simp [hq']

/-- Filter a candidate list of histories on query `q`: keep the tails of histories starting with
`(q, r')` and emit the first matching reply `r'` (or `[]` if none match). -/
def stepCandidates (q : List Bool) (cand : List (List (List Bool × List Bool))) :
    List Bool × List (List (List Bool × List Bool)) :=
  let matching := cand.filterMap fun h =>
    match h with
    | (q', r') :: rest => if q' == q then some (r', rest) else none
    | [] => none
  match matching with
  | [] => ([], [])
  | (r, _) :: _ => (r, matching.map Prod.snd)

/-- The candidate-filtering deterministic prover built from a finite list of histories `H`. -/
def candidateProver (H : List (List (List Bool × List Bool))) : DetProver where
  State := List (List (List Bool × List Bool))
  init := H
  respond q cand := stepCandidates q cand

/-- If `cand` is a pairwise consistent list of histories and `h ∈ cand`, then `h` is a valid
history for `candidateProver H` starting from state `cand`. -/
theorem validFrom_candidateProver (H : List (List (List Bool × List Bool)))
    (cand : List (List (List Bool × List Bool)))
    (hcons : ∀ h₁ ∈ cand, ∀ h₂ ∈ cand, consistentHist h₁ h₂ = true)
    {h : List (List Bool × List Bool)} (hh : h ∈ cand) :
    (candidateProver H).ValidFrom cand h := by
  induction h generalizing cand with
  | nil => trivial
  | cons e rest ih =>
    obtain ⟨q, r⟩ := e
    let filterFn (h' : List (List Bool × List Bool)) :
        Option (List Bool × List (List Bool × List Bool)) :=
      match h' with
      | (q', r') :: rest' => if q' == q then some (r', rest') else none
      | [] => none
    have hmem_match : (r, rest) ∈ cand.filterMap filterFn := by
      rw [List.mem_filterMap]
      exact ⟨(q, r) :: rest, hh, by simp [filterFn]⟩
    cases hm : cand.filterMap filterFn with
    | nil =>
      rw [hm] at hmem_match
      cases hmem_match
    | cons first more =>
      obtain ⟨r₀, rest₀⟩ := first
      have hfirst_mem : (r₀, rest₀) ∈ cand.filterMap filterFn := by
        rw [hm]
        exact List.mem_cons_self
      rw [List.mem_filterMap] at hfirst_mem
      obtain ⟨h₀, hh₀, hfilter₀⟩ := hfirst_mem
      cases h₀ with
      | nil => simp [filterFn] at hfilter₀
      | cons e₀ tail₀ =>
        obtain ⟨q₀, r₀'⟩ := e₀
        simp only [filterFn, beq_iff_eq] at hfilter₀
        split_ifs at hfilter₀ with hq₀
        subst q₀
        simp only [Option.some.injEq, Prod.mk.injEq] at hfilter₀
        obtain ⟨rfl, rfl⟩ := hfilter₀
        have hc := hcons ((q, r₀') :: tail₀) hh₀ ((q, r) :: rest) hh
        simp only [consistentHist, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true,
          beq_iff_eq] at hc
        have hstep : (candidateProver H).respond q cand =
            (r₀', (cand.filterMap filterFn).map Prod.snd) := by
          simp only [candidateProver, stepCandidates, filterFn, hm]
        refine ⟨?_, ?_⟩
        · rw [hstep, hc.1]
        · rw [hstep]
          refine ih ((cand.filterMap filterFn).map Prod.snd) ?_
            (List.mem_map_of_mem hmem_match)
          intro t₁ ht₁ t₂ ht₂
          rw [List.mem_map] at ht₁ ht₂
          obtain ⟨⟨r₁, s₁⟩, hs₁, rfl⟩ := ht₁
          obtain ⟨⟨r₂, s₂⟩, hs₂, rfl⟩ := ht₂
          rw [List.mem_filterMap] at hs₁ hs₂
          obtain ⟨h₁, hh₁, hf₁⟩ := hs₁
          obtain ⟨h₂, hh₂, hf₂⟩ := hs₂
          cases h₁ with
          | nil => simp [filterFn] at hf₁
          | cons e₁ tail₁ =>
            obtain ⟨q₁, r₁'⟩ := e₁
            cases h₂ with
            | nil => simp [filterFn] at hf₂
            | cons e₂ tail₂ =>
              obtain ⟨q₂, r₂'⟩ := e₂
              simp only [filterFn, beq_iff_eq] at hf₁ hf₂
              split_ifs at hf₁ with hq₁
              split_ifs at hf₂ with hq₂
              subst q₁ q₂
              simp only [Option.some.injEq, Prod.mk.injEq] at hf₁ hf₂
              obtain ⟨rfl, rfl⟩ := hf₁
              obtain ⟨rfl, rfl⟩ := hf₂
              have hc12 := hcons ((q, r₁') :: tail₁) hh₁ ((q, r₂') :: tail₂) hh₂
              simp only [consistentHist, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hc12
              exact hc12.2

end Cslib.Complexity.MIP
