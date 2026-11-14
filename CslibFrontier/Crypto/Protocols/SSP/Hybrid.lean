/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SSP.Basic

/-!
# State-separating proofs: hybrid arguments over parallel sessions

The multi-session hybrid argument of state-separating proofs. To bound the advantage in
distinguishing `m` real sessions `parFin real` from `m` ideal sessions `parFin ideal`, replace the
sessions one at a time. The hop that replaces the session `j₀` is exactly a single-session
experiment: a reduction package runs every other session itself, each on its own persistent state,
and forwards the session `j₀` to the package under attack. Summing the hops bounds the
multi-session advantage by the sum of the single-session advantages.

The second half treats sessions sharing a global package `G`, as in universal composability with
global setup: the sessions import the interface of `G`, the environment also queries `G` directly,
and the reduction routes the queries of the sessions it runs itself to `G` through its own import.
Each hop is then a single-session experiment in which the environment also has direct access to
`G`.

## Main definitions

* `Cslib.Crypto.Protocols.SSP.hybridReduction`: runs all sessions but `j₀`, forwarding the session
  `j₀` to the package it is composed with.
* `Cslib.Crypto.Protocols.SSP.hybridFamily`: the `k`-th hybrid, ideal below `k` and real above.
* `Cslib.Crypto.Protocols.SSP.hybridDistinguisher`: the single-session distinguisher of a hop.
* `Cslib.Crypto.Protocols.SSP.globalWorld`: sessions sharing a global package.
* `Cslib.Crypto.Protocols.SSP.eucWorld`: one session with direct access to a global package.
* `Cslib.Crypto.Protocols.SSP.globalReduction`, `Cslib.Crypto.Protocols.SSP.globalDistinguisher`:
  the reduction and the single-session distinguisher of a hop with a global package.

## Main results

* `Cslib.Crypto.Protocols.SSP.eval_run_hybridReduction_comp`: the reduction composed with a
  package `Q` behaves as the sessions with `Q` in the forwarded slot.
* `Cslib.Crypto.Protocols.SSP.advantage_hybridFamily_succ`: each hop is a single-session advantage.
* `Cslib.Crypto.Protocols.SSP.advantage_parFin_le_sum`: the multi-session hybrid bound.
* `Cslib.Crypto.Protocols.SSP.advantage_globalWorld_hybridFamily_succ`,
  `Cslib.Crypto.Protocols.SSP.advantage_globalWorld_le_sum`: the same with a global package.

## References

* [C. Brzuska, A. Delignat-Lavaud, C. Fournet, K. Kohbrok, M. Kohlweiss, *State Separation for
  Code-Based Game-Playing Proofs*][BrzuskaDFKK2018]
* [R. Canetti, Y. Dodis, R. Pass, S. Walfish, *Universally Composable Security with Global
  Setup*][CanettiDPW2007]
-/

public section

namespace Cslib.Crypto.Protocols.SSP

open UC
open OracleComp (sumHandler)

variable {ιE : Type} {E : ιE → Type} {α : Type}

/-- Mapping the outputs of a program before closing and evaluating it. -/
private theorem eval_closeProgram_map_map {γ δ ε : Type} (f : γ → δ) (g : δ → ε)
    (p : ProbOracleComp OracleSpec.empty γ) :
    (Machine.closeProgram (f <$> p)).eval.map g = (Machine.closeProgram p).eval.map (g ∘ f) := by
  rw [Machine.closeProgram_map, ProbComp.eval_map, PMF.map_comp]

/-- State simulation through a sequential composition: `A.comp P` gives every program the same
output distribution as the closed package `M` when each pair of states of `A` and `P` is
represented by a state of `M`, compatibly with initialization and with every activation of `A` run
against `P`. -/
private theorem eval_run_comp_eq_of_represent {ιJ : Type} {J : ιJ → Type} (A : Machine J E)
    (P : Machine OracleSpec.empty J) (M : Machine OracleSpec.empty E)
    (represent : A.State → P.State → M.State)
    (init : (P.init.eval.bind fun sP => A.init.eval.bind fun sA => PMF.pure (represent sA sP)) =
      M.init.eval)
    (step : ∀ q sA sP, (Machine.closeProgram (P.runFrom ((A.handle q).run sA) sP)).eval.map
        (fun x => (x.1.1, represent x.1.2 x.2)) =
      (Machine.closeProgram ((M.handle q).run (represent sA sP))).eval)
    (program : ProbOracleComp E α) : ((A.comp P).run program).eval = (M.run program).eval := by
  refine eval_run_eq_of_represent (A.comp P) M (fun s => represent s.1 s.2) ?_ ?_ program
  · rw [← init]
    change PMF.map (fun (s : A.State × P.State) => represent s.1 s.2)
      (ProbComp.eval (P.init >>= fun sP => A.init >>= fun sA => pure (sA, sP))) = _
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
  · intro q s
    change PMF.map _ (Machine.closeProgram (Functor.map (β := E q × (A.comp P).State)
      ⇑(Equiv.prodAssoc (E q) A.State P.State) (P.runFrom ((A.handle q).run s.1) s.2))).eval = _
    refine (eval_closeProgram_map_map _ _ _).trans ?_
    exact step q s.1 s.2

/-! ### Filling in one coordinate -/

section Glue

variable {m : ℕ} {β : Fin m → Type} {j₀ : Fin m}

/-- Complete a tuple indexed by the coordinates other than `j₀` with a value at `j₀`. -/
private def glue (r : (j : Fin m) → j ≠ j₀ → β j) (t : β j₀) : (j : Fin m) → β j :=
  fun j => if h : j = j₀ then h ▸ t else r j h

private theorem glue_self (r : (j : Fin m) → j ≠ j₀ → β j) (t : β j₀) : glue r t j₀ = t :=
  dite_eq_left rfl

private theorem glue_of_ne (r : (j : Fin m) → j ≠ j₀ → β j) (t : β j₀) {j : Fin m}
    (h : j ≠ j₀) : glue r t j = r j h :=
  dite_eq_right h

private theorem update_glue_self (r : (j : Fin m) → j ≠ j₀ → β j) (t t' : β j₀) :
    Function.update (glue r t) j₀ t' = glue r t' := by
  funext j
  by_cases h : j = j₀
  · subst h
    rw [Function.update_self, glue_self]
  · rw [Function.update_of_ne h, glue_of_ne r t h, glue_of_ne r t' h]

private theorem update_glue_of_ne (r : (j : Fin m) → j ≠ j₀ → β j) (t : β j₀) {j : Fin m}
    (hj : j ≠ j₀) (s : β j) :
    Function.update (glue r t) j s = glue (Function.update r j fun _ => s) t := by
  funext i
  by_cases hi : i = j₀
  · subst hi
    rw [Function.update_of_ne (Ne.symm hj), glue_self, glue_self]
  · rw [glue_of_ne _ _ hi]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hij, Function.update_of_ne hij, glue_of_ne _ _ hi]

private theorem glue_const (r : (j : Fin m) → β j) (t : β j₀) :
    glue (fun j _ => r j) t = Function.update r j₀ t := by
  funext j
  by_cases h : j = j₀
  · subst h
    rw [glue_self, Function.update_self]
  · rw [glue_of_ne _ _ h, Function.update_of_ne h]

/-- Sampling the coordinates other than `j₀` of a product of independent programs, then the
coordinate `j₀`, samples the product. -/
private theorem eval_bind_pi_except {m : ℕ} {β : Fin m → Type} {γ : Type}
    (p : (j : Fin m) → ProbComp (β j)) (j₀ : Fin m) (k : ((j : Fin m) → β j) → PMF γ) :
    (p j₀).eval.bind (fun t => (ProbComp.eval (OracleComp.pi (α := fun j => j ≠ j₀ → β j)
      fun j => if h : j = j₀ then pure fun h' => absurd h h' else (fun s _ => s) <$> p j)).bind
        fun r => k (glue r t)) = (ProbComp.eval (OracleComp.pi p)).bind k := by
  have hinit : ProbComp.eval (OracleComp.pi (α := fun j => j ≠ j₀ → β j)
      fun j => if h : j = j₀ then pure fun h' => absurd h h' else (fun s _ => s) <$> p j) =
      (ProbComp.eval (OracleComp.pi p)).map fun r j _ => r j := by
    refine (ProbComp.eval_pi_congr fun j => ?_).trans
      (ProbComp.eval_pi_map (β := fun j => j ≠ j₀ → β j) p fun j (s : β j) (_ : j ≠ j₀) => s)
    by_cases h : j = j₀
    · rw [dite_eq_left h, ProbComp.eval_pure, ProbComp.eval_map]
      exact (PMF.map_const _ _).symm.trans
        (congrArg (PMF.map · _) (funext fun _ => funext fun h' => absurd h h'))
    · rw [dite_eq_right h]
  rw [hinit]
  simp only [PMF.bind_map, Function.comp_def, glue_const]
  conv_rhs => rw [← ProbComp.eval_bind_pi_update p j₀]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

end Glue

/-! ### The hybrid reduction -/

section Stateful

/-- The reduction for the session `j₀` of `m` sessions: it runs the closed packages `F j` of the
sessions `j ≠ j₀` itself, each on its own state, and forwards the queries to the session `j₀` to
the package it is composed with. -/
@[expose] def hybridReduction {m : ℕ} (j₀ : Fin m)
    (F : {j : Fin m // j ≠ j₀} → Machine OracleSpec.empty E) : Machine E (sessionSpec m E) where
  State := (j : Fin m) → (h : j ≠ j₀) → (F ⟨j, h⟩).State
  init := OracleComp.pi fun j =>
    if h : j = j₀ then pure fun h' => absurd h h' else (fun s (_ : j ≠ j₀) => s) <$> (F ⟨j, h⟩).init
  handle q r :=
    if h : q.1 = j₀ then (fun a => (a, r)) <$> ProbOracleComp.query q.2
    else (fun x => (x.1, Function.update r q.1 fun _ => x.2)) <$>
      ProbOracleComp.sample (Machine.closeProgram (((F ⟨q.1, h⟩).handle q.2).run (r q.1 h)))

/-- The reduction forwards a query to the session `j₀`. -/
private theorem hybridReduction_handle_self {m : ℕ} (j₀ : Fin m)
    (F : {j : Fin m // j ≠ j₀} → Machine OracleSpec.empty E) (e : ιE)
    (r : (hybridReduction j₀ F).State) :
    ((hybridReduction j₀ F).handle (j₀, e)).run r =
      (fun (a : E e) => ((a, r) : sessionSpec m E (j₀, e) × (hybridReduction j₀ F).State)) <$>
        ProbOracleComp.query (spec := E) e :=
  dite_eq_left rfl

/-- The reduction answers a query to a session `j ≠ j₀` itself, on the state of that session. -/
private theorem hybridReduction_handle_of_ne {m : ℕ} {j₀ : Fin m}
    (F : {j : Fin m // j ≠ j₀} → Machine OracleSpec.empty E) {j : Fin m} (h : j ≠ j₀) (e : ιE)
    (r : (hybridReduction j₀ F).State) :
    ((hybridReduction j₀ F).handle (j, e)).run r =
      (fun x => ((x.1, Function.update r j fun _ => x.2) :
          sessionSpec m E (j, e) × (hybridReduction j₀ F).State)) <$>
        ProbOracleComp.sample (Machine.closeProgram (((F ⟨j, h⟩).handle e).run (r j h))) :=
  dite_eq_right h

/-- The reduction for the session `j₀`, running the sessions `j ≠ j₀` with `G j` and composed with
`G j₀` itself, behaves as the sessions `G`. -/
private theorem eval_run_hybridReduction_comp_self {m : ℕ}
    (G : Fin m → Machine OracleSpec.empty E) (j₀ : Fin m) (A : ProbOracleComp (sessionSpec m E) α) :
    (((hybridReduction j₀ fun i => G i.1).comp (G j₀)).run A).eval = ((parFin G).run A).eval := by
  refine eval_run_comp_eq_of_represent (hybridReduction j₀ fun i => G i.1) (G j₀) (parFin G)
    (fun r t => glue (β := fun j => (G j).State) r t) ?_ ?_ A
  · exact (eval_bind_pi_except (fun j => (G j).init) j₀ PMF.pure).trans (PMF.bind_pure _)
  · rintro ⟨j, e⟩ r t
    rw [parFin_handle G j e (glue (β := fun j => (G j).State) r t)]
    by_cases h : j = j₀
    · subst h
      simp only [hybridReduction_handle_self, Machine.runFrom_map, Machine.runFrom_query,
        glue_self (β := fun j => (G j).State) r t,
        update_glue_self (β := fun j => (G j).State) r t, Machine.closeProgram_map,
        ProbComp.eval_map, PMF.map_comp]
      rfl
    · simp only [hybridReduction_handle_of_ne _ h, Machine.runFrom_map, Machine.runFrom_sample,
        glue_of_ne (β := fun j => (G j).State) r t h,
        update_glue_of_ne (β := fun j => (G j).State) r t h, Machine.closeProgram_map,
        Machine.closeProgram_sample, ProbComp.eval_map, PMF.map_comp]
      rfl

/-- **Hybrid reduction.** The reduction for the session `j₀`, running the sessions `j ≠ j₀` with
`G j` and composed with a closed package `Q`, behaves as the sessions `G` with the session `j₀`
replaced by `Q`. -/
theorem eval_run_hybridReduction_comp {m : ℕ} (G : Fin m → Machine OracleSpec.empty E)
    (j₀ : Fin m) (Q : Machine OracleSpec.empty E) (A : ProbOracleComp (sessionSpec m E) α) :
    (((hybridReduction j₀ fun i => G i.1).comp Q).run A).eval =
      ((parFin (Function.update G j₀ Q)).run A).eval := by
  have hF : (fun i : {j : Fin m // j ≠ j₀} => G i.1) = fun i => Function.update G j₀ Q i.1 :=
    funext fun i => (Function.update_of_ne i.2 Q G).symm
  have h := eval_run_hybridReduction_comp_self (Function.update G j₀ Q) j₀ A
  rw [Function.update_self, ← hF] at h
  exact h

/-- The `k`-th hybrid between two families: the sessions below `k` take the ideal component and
the others the real one. -/
@[expose] def hybridFamily {m : ℕ} {β : Type*} (real ideal : Fin m → β) (k : ℕ) : Fin m → β :=
  fun j => if j.val < k then ideal j else real j

@[simp] theorem hybridFamily_zero {m : ℕ} {β : Type*} (real ideal : Fin m → β) :
    hybridFamily real ideal 0 = real :=
  funext fun _ => ite_eq_right (Nat.not_lt_zero _)

@[simp] theorem hybridFamily_self {m : ℕ} {β : Type*} (real ideal : Fin m → β) :
    hybridFamily real ideal m = ideal :=
  funext fun j => ite_eq_left j.isLt

private theorem update_hybridFamily_real {m : ℕ} {β : Type*} (real ideal : Fin m → β)
    (j₀ : Fin m) :
    Function.update (hybridFamily real ideal j₀.val) j₀ (real j₀) =
      hybridFamily real ideal j₀.val := by
  funext j
  by_cases h : j = j₀
  · subst h
    simp [hybridFamily]
  · rw [Function.update_of_ne h]

private theorem update_hybridFamily_ideal {m : ℕ} {β : Type*} (real ideal : Fin m → β)
    (j₀ : Fin m) :
    Function.update (hybridFamily real ideal j₀.val) j₀ (ideal j₀) =
      hybridFamily real ideal (j₀.val + 1) := by
  funext j
  by_cases h : j = j₀
  · subst h
    simp [hybridFamily]
  · have hv : j.val ≠ j₀.val := fun hv => h (Fin.ext hv)
    rw [Function.update_of_ne h]
    simp only [hybridFamily]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- The single-session distinguisher of the hop at the session `j₀`: it runs `A` against the
reduction whose sessions below `j₀` are ideal and whose sessions above `j₀` are real. -/
@[expose] def hybridDistinguisher {m : ℕ} (real ideal : Fin m → Machine OracleSpec.empty E)
    (A : ProbOracleComp (sessionSpec m E) Bool) (j₀ : Fin m) : ProbOracleComp E Bool :=
  (hybridReduction j₀ fun i => hybridFamily real ideal j₀.val i.1).link A

/-- **Hybrid hop.** Replacing the session `j₀` of the hybrid is exactly distinguishing the real
package of that session from the ideal one, by the single-session distinguisher. -/
theorem advantage_hybridFamily_succ {m : ℕ} (real ideal : Fin m → Machine OracleSpec.empty E)
    (A : ProbOracleComp (sessionSpec m E) Bool) (j₀ : Fin m) :
    advantage A (parFin (hybridFamily real ideal j₀.val))
        (parFin (hybridFamily real ideal (j₀.val + 1))) =
      advantage (hybridDistinguisher real ideal A j₀) (real j₀) (ideal j₀) := by
  rw [hybridDistinguisher, ← advantage_comp]
  exact advantage_congr
    (by rw [eval_run_hybridReduction_comp _ j₀ (real j₀), update_hybridFamily_real])
    (by rw [eval_run_hybridReduction_comp _ j₀ (ideal j₀), update_hybridFamily_ideal])

/-- **Multi-session hybrid bound.** The advantage in distinguishing `m` real sessions from `m`
ideal sessions is at most the sum, over the sessions, of the advantage of the single-session
distinguisher of the hop at that session. -/
theorem advantage_parFin_le_sum {m : ℕ} (real ideal : Fin m → Machine OracleSpec.empty E)
    (A : ProbOracleComp (sessionSpec m E) Bool) :
    advantage A (parFin real) (parFin ideal) ≤
      ∑ j : Fin m, advantage (hybridDistinguisher real ideal A j) (real j) (ideal j) := by
  have h := advantage_le_sum_range A (fun k => parFin (hybridFamily real ideal k)) m
  simp only [hybridFamily_zero, hybridFamily_self] at h
  refine h.trans_eq ?_
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => advantage_hybridFamily_succ real ideal A j

end Stateful

/-! ### Sessions sharing a global package -/

section Global

variable {ιI : Type} {I : ιI → Type}

/-- A program querying the interface `I`, as a program querying the right summand of `E ⊕ₒ I`;
its private coins stay private. -/
@[expose] def liftInr (program : ProbOracleComp I α) : ProbOracleComp (E ⊕ₒ I) α :=
  OracleComp.interpret (spec := probOracleSpec I)
    (sumHandler (fun n => OracleComp.query (spec := probOracleSpec (E ⊕ₒ I)) (Sum.inl n))
      fun i => ProbOracleComp.query (spec := E ⊕ₒ I) (Sum.inr i)) program

private theorem id_handle (i : ιI) (u : (Machine.id I).State) :
    ((Machine.id I).handle i).run u = (fun a => (a, u)) <$> ProbOracleComp.query (spec := I) i := by
  rw [← Machine.runFrom_query, Machine.runFrom_id]

/-- A relabelled program run against a package placed beside the forwarding package only reaches
the forwarding package, so it runs unchanged and leaves the state untouched. -/
theorem runFrom_par_id_liftInr (Q : Machine I E) (program : ProbOracleComp I α)
    (s : (par Q (Machine.id I)).State) :
    (par Q (Machine.id I)).runFrom (liftInr program) s = (fun a => (a, s)) <$> program := by
  rw [Machine.runFrom, liftInr, OracleComp.interpret_interpret]
  calc _ = (OracleComp.interpret (fun q => StateT.lift (OracleComp.query q)) program).run s := by
        refine congrArg (fun h => StateT.run (OracleComp.interpret h program) s)
          (funext fun q => ?_)
        cases q with
        | inl n =>
          simp only [OracleComp.interpret_query, Machine.handler, ProbOracleComp.sample,
            ProbComp.unifFin]
        | inr i =>
          funext s'
          change (par Q (Machine.id I)).runFrom (ProbOracleComp.query (spec := E ⊕ₒ I) (.inr i))
              s' = ProbOracleComp.query (spec := I) i >>= fun a =>
            pure ((a, s') : (E ⊕ₒ I) (.inr i) × (par Q (Machine.id I)).State)
          rw [Machine.runFrom_query, par_handle_inr, id_handle]
          exact (Functor.map_map _ _ _).trans (bind_pure_comp _ _).symm
    _ = _ := by rw [OracleComp.run_interpret_lift, OracleComp.interpret_query_eq_self]

/-- The sessions `P j` sharing the global package `G`, which the environment also queries
directly. -/
@[expose] def globalWorld {m : ℕ} (P : Fin m → Machine I E) (G : Machine OracleSpec.empty I) :
    Machine OracleSpec.empty (sessionSpec m E ⊕ₒ I) :=
  (par (parFin P) (Machine.id I)).comp G

/-- One session `Q` with the global package `G`, which the environment also queries directly. -/
@[expose] def eucWorld (Q : Machine I E) (G : Machine OracleSpec.empty I) :
    Machine OracleSpec.empty (E ⊕ₒ I) :=
  (par Q (Machine.id I)).comp G

/-- The reduction for the session `j₀` of `m` sessions sharing a global package: it runs the
packages `F j` of the sessions `j ≠ j₀` itself, routing their queries to the global package
through the right summand of its import, and forwards both the queries to the session `j₀` and the
direct queries to the global package. -/
@[expose] def globalReduction {m : ℕ} (j₀ : Fin m) (F : {j : Fin m // j ≠ j₀} → Machine I E) :
    Machine (E ⊕ₒ I) (sessionSpec m E ⊕ₒ I) where
  State := (j : Fin m) → (h : j ≠ j₀) → (F ⟨j, h⟩).State
  init := OracleComp.pi fun j =>
    if h : j = j₀ then pure fun h' => absurd h h' else (fun s (_ : j ≠ j₀) => s) <$> (F ⟨j, h⟩).init
  handle
    | .inl q, r =>
      if h : q.1 = j₀ then (fun a => (a, r)) <$> ProbOracleComp.query (Sum.inl q.2)
      else (fun x => (x.1, Function.update r q.1 fun _ => x.2)) <$>
        liftInr (E := E) (((F ⟨q.1, h⟩).handle q.2).run (r q.1 h))
    | .inr i, r => (fun a => (a, r)) <$> ProbOracleComp.query (Sum.inr i)

/-- The reduction forwards a query to the session `j₀`. -/
private theorem globalReduction_handle_inl_self {m : ℕ} (j₀ : Fin m)
    (F : {j : Fin m // j ≠ j₀} → Machine I E) (e : ιE) (r : (globalReduction j₀ F).State) :
    ((globalReduction j₀ F).handle (.inl (j₀, e))).run r =
      (fun (a : (E ⊕ₒ I) (.inl e)) =>
          ((a, r) : (sessionSpec m E ⊕ₒ I) (.inl (j₀, e)) × (globalReduction j₀ F).State)) <$>
        ProbOracleComp.query (spec := E ⊕ₒ I) (.inl e) :=
  dite_eq_left rfl

/-- The reduction answers a query to a session `j ≠ j₀` itself, on the state of that session,
routing the queries of that session to the global package. -/
private theorem globalReduction_handle_inl_of_ne {m : ℕ} {j₀ : Fin m}
    (F : {j : Fin m // j ≠ j₀} → Machine I E) {j : Fin m} (h : j ≠ j₀) (e : ιE)
    (r : (globalReduction j₀ F).State) :
    ((globalReduction j₀ F).handle (.inl (j, e))).run r =
      (fun x => ((x.1, Function.update r j fun _ => x.2) :
          (sessionSpec m E ⊕ₒ I) (.inl (j, e)) × (globalReduction j₀ F).State)) <$>
        liftInr (E := E) (((F ⟨j, h⟩).handle e).run (r j h)) :=
  dite_eq_right h

/-- The reduction forwards a direct query to the global package. -/
private theorem globalReduction_handle_inr {m : ℕ} (j₀ : Fin m)
    (F : {j : Fin m // j ≠ j₀} → Machine I E) (i : ιI) (r : (globalReduction j₀ F).State) :
    ((globalReduction j₀ F).handle (.inr i)).run r =
      (fun (a : (E ⊕ₒ I) (.inr i)) =>
          ((a, r) : (sessionSpec m E ⊕ₒ I) (.inr i) × (globalReduction j₀ F).State)) <$>
        ProbOracleComp.query (spec := E ⊕ₒ I) (.inr i) :=
  rfl

/-- The initial distribution of a package placed beside the forwarding package, composed with a
global package. -/
private theorem eval_init_par_id_comp {ιK : Type} {K : ιK → Type} (X : Machine I K)
    (G : Machine OracleSpec.empty I) :
    ((par X (Machine.id I)).comp G).init.eval = G.init.eval.bind fun g => X.init.eval.bind fun s =>
      PMF.pure (α := ((par X (Machine.id I)).comp G).State) ((s, PUnit.unit), g) := by
  change ProbComp.eval (G.init >>= fun g => (X.init >>= fun s₁ =>
    (pure PUnit.unit : ProbComp PUnit) >>= fun s₂ => pure (s₁, s₂)) >>= fun s => pure (s, g)) = _
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  rfl

private theorem eval_eucWorld_init (Q : Machine I E) (G : Machine OracleSpec.empty I) :
    (eucWorld Q G).init.eval = G.init.eval.bind fun g => Q.init.eval.bind fun s =>
      PMF.pure (α := (eucWorld Q G).State) ((s, PUnit.unit), g) :=
  eval_init_par_id_comp Q G

private theorem eval_globalWorld_init {m : ℕ} (P : Fin m → Machine I E)
    (G : Machine OracleSpec.empty I) :
    (globalWorld P G).init.eval = G.init.eval.bind fun g =>
      (ProbComp.eval (OracleComp.pi fun j => (P j).init)).bind fun s =>
        PMF.pure (α := (globalWorld P G).State) ((s, PUnit.unit), g) :=
  eval_init_par_id_comp (parFin P) G

private theorem eucWorld_handle (Q : Machine I E) (G : Machine OracleSpec.empty I) (q : ιE ⊕ ιI)
    (s : (eucWorld Q G).State) :
    ((eucWorld Q G).handle q).run s =
      (fun x => ((x.1.1, (x.1.2, x.2)) : (E ⊕ₒ I) q × (eucWorld Q G).State)) <$>
        G.runFrom (((par Q (Machine.id I)).handle q).run s.1) s.2 :=
  rfl

private theorem eucWorld_runFrom (Q : Machine I E) (G : Machine OracleSpec.empty I) {β : Type}
    (program : ProbOracleComp (E ⊕ₒ I) β) (s : (eucWorld Q G).State) :
    (eucWorld Q G).runFrom program s =
      (fun x => ((x.1.1, (x.1.2, x.2)) : β × (eucWorld Q G).State)) <$>
        G.runFrom ((par Q (Machine.id I)).runFrom program s.1) s.2 :=
  Machine.runFrom_comp (par Q (Machine.id I)) G program s.1 s.2

/-- An activation of a session of `globalWorld P G`, on the state `((s, u), g)`. -/
private theorem globalWorld_handle_inl {m : ℕ} (P : Fin m → Machine I E)
    (G : Machine OracleSpec.empty I) (j : Fin m) (e : ιE) (s : (parFin P).State)
    (u : (Machine.id I).State) (g : G.State) :
    ((globalWorld P G).handle (.inl (j, e))).run ((s, u), g) =
      (fun x => ((x.1.1, (x.1.2, x.2)) :
          (sessionSpec m E ⊕ₒ I) (.inl (j, e)) × (globalWorld P G).State)) <$>
        G.runFrom ((fun x => ((x.1, (x.2, u)) :
            (sessionSpec m E ⊕ₒ I) (.inl (j, e)) × (par (parFin P) (Machine.id I)).State)) <$>
          ((fun x => ((x.1, Function.update s j x.2) :
              sessionSpec m E (j, e) × (parFin P).State)) <$>
            ((P j).handle e).run (s j))) g :=
  rfl

/-- A direct query to the global package of `globalWorld P G`, on the state `((s, u), g)`. -/
private theorem globalWorld_handle_inr {m : ℕ} (P : Fin m → Machine I E)
    (G : Machine OracleSpec.empty I) (i : ιI) (s : (parFin P).State) (u : (Machine.id I).State)
    (g : G.State) :
    ((globalWorld P G).handle (.inr i)).run ((s, u), g) =
      (fun x => ((x.1.1, (x.1.2, x.2)) :
          (sessionSpec m E ⊕ₒ I) (.inr i) × (globalWorld P G).State)) <$>
        G.runFrom ((fun x => ((x.1, (s, x.2)) :
            (sessionSpec m E ⊕ₒ I) (.inr i) × (par (parFin P) (Machine.id I)).State)) <$>
          ((Machine.id I).handle i).run u) g :=
  rfl

/-- The reduction for the session `j₀`, running the sessions `j ≠ j₀` with `P j` and composed with
the single-session world of `P j₀`, behaves as the sessions `P` sharing the global package. -/
private theorem eval_run_globalReduction_comp_self {m : ℕ} (P : Fin m → Machine I E)
    (G : Machine OracleSpec.empty I) (j₀ : Fin m) (A : ProbOracleComp (sessionSpec m E ⊕ₒ I) α) :
    (((globalReduction j₀ fun i => P i.1).comp (eucWorld (P j₀) G)).run A).eval =
      ((globalWorld P G).run A).eval := by
  refine eval_run_comp_eq_of_represent (globalReduction j₀ fun i => P i.1) (eucWorld (P j₀) G)
    (globalWorld P G) (fun r s => ((glue (β := fun j => (P j).State) r s.1.1, s.1.2), s.2)) ?_ ?_
    A
  · rw [eval_eucWorld_init, eval_globalWorld_init]
    simp only [PMF.bind_bind]
    refine congrArg (ProbComp.eval G.init).bind (funext fun g => ?_)
    refine Eq.trans ?_ (eval_bind_pi_except (fun j => (P j).init) j₀
      fun r => PMF.pure (α := (globalWorld P G).State) ((r, PUnit.unit), g))
    refine congrArg (ProbComp.eval (P j₀).init).bind (funext fun t => ?_)
    exact PMF.pure_bind _ _
  · rintro (⟨j, e⟩ | i) r s
    · rw [globalWorld_handle_inl P G j e (glue (β := fun j => (P j).State) r s.1.1) s.1.2 s.2]
      by_cases h : j = j₀
      · subst h
        rw [globalReduction_handle_inl_self j (fun k => P k.1) e r, Machine.runFrom_map,
          Machine.runFrom_query, eucWorld_handle (P j) G (.inl e) s,
          par_handle_inl (P j) (Machine.id I) e s.1]
        simp only [Machine.runFrom_map, glue_self (β := fun j => (P j).State) r s.1.1,
          update_glue_self (β := fun j => (P j).State) r s.1.1, Machine.closeProgram_map,
          ProbComp.eval_map, PMF.map_comp]
        rfl
      · simp only [globalReduction_handle_inl_of_ne _ h, Machine.runFrom_map, eucWorld_runFrom,
          runFrom_par_id_liftInr, glue_of_ne (β := fun j => (P j).State) r s.1.1 h,
          update_glue_of_ne (β := fun j => (P j).State) r s.1.1 h, Machine.closeProgram_map,
          ProbComp.eval_map, PMF.map_comp]
        rfl
    · rw [globalWorld_handle_inr P G i (glue (β := fun j => (P j).State) r s.1.1) s.1.2 s.2,
        globalReduction_handle_inr j₀ (fun k => P k.1) i r, Machine.runFrom_map,
        Machine.runFrom_query, eucWorld_handle (P j₀) G (.inr i) s,
        par_handle_inr (P j₀) (Machine.id I) i s.1]
      simp only [Machine.runFrom_map, Machine.runFrom_query, id_handle,
        Machine.closeProgram_map, ProbComp.eval_map, PMF.map_comp]
      rfl

/-- **Hybrid reduction with a global package.** The reduction for the session `j₀`, running the
sessions `j ≠ j₀` with `P j` and composed with the single-session world of `Q`, behaves as the
sessions `P` with the session `j₀` replaced by `Q`, sharing the global package. -/
theorem eval_run_globalReduction_comp {m : ℕ} (P : Fin m → Machine I E)
    (G : Machine OracleSpec.empty I) (j₀ : Fin m) (Q : Machine I E)
    (A : ProbOracleComp (sessionSpec m E ⊕ₒ I) α) :
    (((globalReduction j₀ fun i => P i.1).comp (eucWorld Q G)).run A).eval =
      ((globalWorld (Function.update P j₀ Q) G).run A).eval := by
  have hF : (fun i : {j : Fin m // j ≠ j₀} => P i.1) = fun i => Function.update P j₀ Q i.1 :=
    funext fun i => (Function.update_of_ne i.2 Q P).symm
  have h := eval_run_globalReduction_comp_self (Function.update P j₀ Q) G j₀ A
  rw [Function.update_self, ← hF] at h
  exact h

/-- The single-session distinguisher of the hop at the session `j₀` with a global package: it runs
`A` against the reduction whose sessions below `j₀` are ideal and whose sessions above `j₀` are
real. -/
@[expose] def globalDistinguisher {m : ℕ} (real ideal : Fin m → Machine I E)
    (A : ProbOracleComp (sessionSpec m E ⊕ₒ I) Bool) (j₀ : Fin m) : ProbOracleComp (E ⊕ₒ I) Bool :=
  (globalReduction j₀ fun i => hybridFamily real ideal j₀.val i.1).link A

/-- **Hybrid hop with a global package.** Replacing the session `j₀` of the hybrid is exactly
distinguishing the single-session worlds of the real and the ideal package of that session. -/
theorem advantage_globalWorld_hybridFamily_succ {m : ℕ} (real ideal : Fin m → Machine I E)
    (G : Machine OracleSpec.empty I) (A : ProbOracleComp (sessionSpec m E ⊕ₒ I) Bool)
    (j₀ : Fin m) :
    advantage A (globalWorld (hybridFamily real ideal j₀.val) G)
        (globalWorld (hybridFamily real ideal (j₀.val + 1)) G) =
      advantage (globalDistinguisher real ideal A j₀) (eucWorld (real j₀) G)
        (eucWorld (ideal j₀) G) := by
  rw [globalDistinguisher, ← advantage_comp]
  exact advantage_congr
    (by rw [eval_run_globalReduction_comp _ G j₀ (real j₀), update_hybridFamily_real])
    (by rw [eval_run_globalReduction_comp _ G j₀ (ideal j₀), update_hybridFamily_ideal])

/-- **Hybrid bound with a global package.** The advantage in distinguishing `m` real sessions from
`m` ideal sessions sharing the global package `G` is at most the sum, over the sessions, of the
advantage of the single-session distinguisher of the hop at that session, which also has direct
access to `G`. -/
theorem advantage_globalWorld_le_sum {m : ℕ} (real ideal : Fin m → Machine I E)
    (G : Machine OracleSpec.empty I) (A : ProbOracleComp (sessionSpec m E ⊕ₒ I) Bool) :
    advantage A (globalWorld real G) (globalWorld ideal G) ≤
      ∑ j : Fin m, advantage (globalDistinguisher real ideal A j) (eucWorld (real j) G)
        (eucWorld (ideal j) G) := by
  have h := advantage_le_sum_range A (fun k => globalWorld (hybridFamily real ideal k) G) m
  simp only [hybridFamily_zero, hybridFamily_self] at h
  refine h.trans_eq ?_
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => advantage_globalWorld_hybridFamily_succ real ideal G A j

end Global

end Cslib.Crypto.Protocols.SSP
