/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.HaltingTime
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic

/-!
# Randomized logarithmic space

A fair-coin machine (`Turing.MultiTapePTM`) reads each coin once, in order, so its randomness is
read-once. Its nondeterministic view (`Turing.MultiTapePTM.toNTM`) takes either coin at every
step; space is measured there, exactly as for `Cslib.Complexity.NL`. Every branch must halt: on
every encoded instance some number of steps `t` bounds every computation path. No clock is part of
the definition.

The acceptance probability on `input` is `acceptCoins input t / 2 ^ t`, where
`Turing.MultiTapePTM.acceptCoins` counts the coin strings of length `t` whose replay ends halted
with output `[true]`. Once every branch halts within `t` steps, this fraction no longer depends on
`t` (`Turing.MultiTapePTM.acceptCoins_succ`), so the classes quantify over one such `t` per
instance.

* `Cslib.Complexity.RL`: members are accepted with probability at least `1/2`, non-members never.
* `Cslib.Complexity.BPL`: members with probability at least `2/3`, non-members at most `1/3`.

The threshold `1/2` for `RL` can be raised to `1 - 2 ^ (-r)` for any fixed `r` by repetition
(`Cslib.Complexity.mem_RL_iff_error_le`), which also gives `Cslib.Complexity.RL_subset_BPL`.
The acceptance probability is an entry of a power or inverse of a polynomial-size configuration
matrix (`Cslib.Complexity.exists_configMatrix_of_mem_BPL`).

The model follows the decision recorded in issue #474: one-way coins, halting on every branch with
the polynomial clock a derived lemma, acceptance by counting coin strings, and space as for `NL`
[Arora and Barak, Section 7.7][AroraBarak09].

## Main definitions

* `Turing.MultiTapePTM.acceptCoins`: the accepting coin strings of a given length.
* `Cslib.Complexity.RL`, `Cslib.Complexity.BPL`: randomized logarithmic space with one-sided and
  bounded two-sided error.

## Main results

* `Turing.MultiTapePTM.acceptCoins_succ`: once every branch halts, one more coin doubles the count.
* `Turing.MultiTapePTM.acceptCoins_mul_two_pow`, `Turing.MultiTapePTM.two_pow_mul_le_iff`,
  `Turing.MultiTapePTM.mul_le_two_pow_iff`: the acceptance probability and its bounds do not depend
  on the halting time they are measured at.
* `Turing.MultiTapePTM.accepts_toNTM_iff`: the nondeterministic view accepts exactly when some
  coin string of a halting length is accepted.
* `Cslib.Complexity.L_subset_RL`, `Cslib.Complexity.L_subset_BPL`: deterministic logarithmic space
  is within both.
* `Cslib.Complexity.RL_subset_NL`: randomized logspace with one-sided error is within `NL`.
* `Cslib.Complexity.exists_polyClock_of_mem_RL`, `Cslib.Complexity.exists_polyClock_of_mem_BPL`:
  the derived polynomial clock; every branch halts within polynomially many steps.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.7][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)

open scoped Classical in
/-- The number of coin strings of length `t` whose replay from the initial configuration on
`input` ends halted with output `[true]`. -/
noncomputable def acceptCoins (input : List Bool) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin t → Bool =>
    (machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input)).Halted ∧
      (machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input)).output = [true]).card

/-- At most all coin strings are accepted. -/
theorem acceptCoins_le (input : List Bool) (t : ℕ) : machine.acceptCoins input t ≤ 2 ^ t :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- A halted configuration ignores its coin. -/
theorem step_withCoin_of_halted {input : List Bool} {c : Cfg k Bool State input} (h : c.Halted)
    (bit : Bool) : (machine.withCoin bit).toTM.step c = c :=
  MultiTapeTM.step_iff.mp ((MultiTapeNTM.step_of_halt h).mpr rfl)

/-- A halted configuration ignores any further coins. -/
theorem stepCoins_of_halted {input : List Bool} {c : Cfg k Bool State input} (h : c.Halted)
    (coins : List Bool) : machine.stepCoins coins c = c := by
  induction coins with
  | nil => rfl
  | cons bit coins ih => rw [stepCoins_cons, step_withCoin_of_halted machine h, ih]

/-- Under a time bound `t`, every replay of `t` or more coins ends halted. -/
theorem halted_stepCoins {input : List Bool} {t : ℕ} (ht : machine.toNTM.RunsInTime input t)
    {coins : List Bool} (hlen : t ≤ coins.length) :
    (machine.stepCoins coins (machine.toNTM.initCfg input)).Halted := by
  obtain ⟨p, hhead, hplen, hlast⟩ := (machine.exists_runPath_toNTM_iff
    (c := machine.toNTM.initCfg input)).mpr ⟨coins, rfl, rfl⟩
  have := ht ⟨p, hhead⟩ (by simpa [MultiTapeNTM.ComputationPath.time,
    MultiTapeNTM.RunPath.time, hplen] using hlen)
  simpa [hlast] using this

/-- **One more coin doubles the count** once every branch halts within `t` steps: the last coin
of a string of length `t + 1` is read by a halted configuration and ignored. -/
theorem acceptCoins_succ {input : List Bool} {t : ℕ} (ht : machine.toNTM.RunsInTime input t) :
    machine.acceptCoins input (t + 1) = 2 * machine.acceptCoins input t := by
  classical
  -- the replay of a string of length `t + 1` is the replay of its first `t` coins
  have hreplay (w : Fin (t + 1) → Bool) :
      machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input) =
        machine.stepCoins (List.ofFn (Fin.init w)) (machine.toNTM.initCfg input) := by
    rw [List.ofFn_succ', List.concat_eq_append, stepCoins_append,
      stepCoins_of_halted machine (halted_stepCoins machine ht (by simp))]
    rfl
  unfold acceptCoins
  rw [← Finset.card_map (Fin.snocEquiv fun _ => Bool).symm.toEmbedding]
  have hset : (Finset.univ.filter fun w : Fin (t + 1) → Bool =>
      (machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input)).Halted ∧
        (machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input)).output = [true]).map
      (Fin.snocEquiv fun _ => Bool).symm.toEmbedding =
      (Finset.univ : Finset Bool) ×ˢ (Finset.univ.filter fun w : Fin t → Bool =>
        (machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input)).Halted ∧
          (machine.stepCoins (List.ofFn w) (machine.toNTM.initCfg input)).output = [true]) := by
    ext ⟨b, w⟩
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_product]
    rw [hreplay]
    simp [Fin.snocEquiv, Fin.init_snoc]
  rw [hset, Finset.card_product, Finset.card_univ, Fintype.card_bool]

/-- Once every branch halts within `t` steps, the count scales with the number of extra coins. -/
theorem acceptCoins_add {input : List Bool} {t : ℕ} (ht : machine.toNTM.RunsInTime input t)
    (m : ℕ) : machine.acceptCoins input (t + m) = 2 ^ m * machine.acceptCoins input t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, acceptCoins_succ machine (ht.mono (Nat.le_add_right t m)), ih, pow_succ]
    ring

/-- **The acceptance probability does not depend on the clock**: for two halting times `t` and
`t'`, `acceptCoins input t / 2 ^ t = acceptCoins input t' / 2 ^ t'`. -/
theorem acceptCoins_mul_two_pow {input : List Bool} {t t' : ℕ}
    (ht : machine.toNTM.RunsInTime input t) (ht' : machine.toNTM.RunsInTime input t') :
    machine.acceptCoins input t' * 2 ^ t = machine.acceptCoins input t * 2 ^ t' := by
  wlog h : t ≤ t' generalizing t t'
  · exact (this ht' ht (le_of_not_ge h)).symm
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [acceptCoins_add machine ht m, pow_add]
  ring

/-- A lower bound `x / y` on the acceptance probability holds at one halting time exactly when it
holds at another. -/
theorem two_pow_mul_le_iff {input : List Bool} {t t' : ℕ}
    (ht : machine.toNTM.RunsInTime input t) (ht' : machine.toNTM.RunsInTime input t')
    (x y : ℕ) : x * 2 ^ t ≤ y * machine.acceptCoins input t ↔
      x * 2 ^ t' ≤ y * machine.acceptCoins input t' := by
  have e := machine.acceptCoins_mul_two_pow ht ht'
  constructor <;> intro h
  · have := Nat.mul_le_mul_right (2 ^ t') h
    exact Nat.le_of_mul_le_mul_right (by linarith [congrArg (y * ·) e]) (Nat.two_pow_pos t)
  · have := Nat.mul_le_mul_right (2 ^ t) h
    exact Nat.le_of_mul_le_mul_right (by linarith [congrArg (y * ·) e]) (Nat.two_pow_pos t')

/-- An upper bound `x / y` on the acceptance probability holds at one halting time exactly when it
holds at another. -/
theorem mul_le_two_pow_iff {input : List Bool} {t t' : ℕ}
    (ht : machine.toNTM.RunsInTime input t) (ht' : machine.toNTM.RunsInTime input t')
    (x y : ℕ) : y * machine.acceptCoins input t ≤ x * 2 ^ t ↔
      y * machine.acceptCoins input t' ≤ x * 2 ^ t' := by
  have e := machine.acceptCoins_mul_two_pow ht ht'
  constructor <;> intro h
  · have := Nat.mul_le_mul_right (2 ^ t') h
    exact Nat.le_of_mul_le_mul_right (by linarith [congrArg (y * ·) e]) (Nat.two_pow_pos t)
  · have := Nat.mul_le_mul_right (2 ^ t) h
    exact Nat.le_of_mul_le_mul_right (by linarith [congrArg (y * ·) e]) (Nat.two_pow_pos t')

/-- **Acceptance of the nondeterministic view** is acceptance by some coin string of a halting
length. -/
theorem accepts_toNTM_iff {input : List Bool} {t : ℕ} (ht : machine.toNTM.RunsInTime input t) :
    machine.toNTM.Accepts input ↔ 0 < machine.acceptCoins input t := by
  classical
  constructor
  · rintro ⟨p, hhalt, hout⟩
    obtain ⟨coins, hlen, hcoins⟩ := (machine.exists_runPath_toNTM_iff
      (c := machine.toNTM.initCfg input)).mp ⟨p.toRunPath, p.head_eq, rfl, rfl⟩
    -- pad or truncate the coins to length `t`; the configuration stays the halted one
    have hfinal : machine.stepCoins (coins ++ List.replicate t false)
        (machine.toNTM.initCfg input) = p.last := by
      rw [stepCoins_append, hcoins, stepCoins_of_halted machine hhalt]
    have htake : machine.stepCoins ((coins ++ List.replicate t false).take t)
        (machine.toNTM.initCfg input) = p.last := by
      have hh := halted_stepCoins machine ht (coins := (coins ++ List.replicate t false).take t)
        (by simp)
      rw [← hfinal, ← List.take_append_drop t (coins ++ List.replicate t false),
        stepCoins_append _ _ _ (c := machine.toNTM.initCfg input), stepCoins_of_halted machine hh,
        List.take_append_drop]
    let w : Fin t → Bool := fun i => ((coins ++ List.replicate t false).take t).getD i false
    have hw : List.ofFn w = (coins ++ List.replicate t false).take t := by
      apply List.ext_getElem (by simp)
      intro i h₁ h₂
      simp [w, List.getD_eq_getElem?_getD]
    refine Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hw, htake]
    exact ⟨hhalt, hout⟩
  · intro hpos
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    obtain ⟨hhalt, hout⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨p, hhead, -, hlast⟩ := (machine.exists_runPath_toNTM_iff
      (c := machine.toNTM.initCfg input)).mpr ⟨List.ofFn w, rfl, rfl⟩
    exact ⟨⟨p, hhead⟩, hlast ▸ hhalt, hlast ▸ hout⟩

/-! ### Deterministic machines -/

/-- The nondeterministic view of a deterministic machine run as a fair-coin machine is the
deterministic machine itself. -/
theorem toNTM_ofDeterministic (tm : MultiTapeTM k Bool State) :
    (ofDeterministic tm : MultiTapePTM k Bool State).toNTM = tm.toMultiTapeNTM := by
  cases tm with
  | mk ntm det =>
  simp only [toNTM, branches, MultiTapeMachine.toNTM, ofDeterministic]
  congr
  funext q s w a
  simp only [Set.mem_range, exists_const]
  apply propext
  rw [eq_comm, Equiv.symm_apply_eq]
  exact eq_comm.trans (MultiTapeTM.tr_iff (tm := ⟨ntm, det⟩)).symm

/-- A deterministic machine ignores its coins: every replay of `n` coins is its run of `n`
steps. -/
theorem stepCoins_ofDeterministic (tm : MultiTapeTM k Bool State) (input : List Bool)
    (coins : List Bool) :
    (ofDeterministic tm : MultiTapePTM k Bool State).stepCoins coins
      ((ofDeterministic tm : MultiTapePTM k Bool State).toNTM.initCfg input) =
      tm.runFrom (tm.initCfg input) coins.length := by
  have key : ∀ N : MultiTapeNTM k Bool State, N = tm.toMultiTapeNTM →
      ∀ p : N.RunPath input, p.head = N.initCfg input →
        p.last = tm.runFrom (tm.initCfg input) p.length := by
    rintro N rfl p hp
    exact MultiTapeTM.computationPath_last_eq_runFrom (tm := tm) ⟨p, hp⟩
  obtain ⟨p, hhead, hlen, hlast⟩ := ((ofDeterministic tm : MultiTapePTM k Bool State)
    |>.exists_runPath_toNTM_iff
      (c := (ofDeterministic tm : MultiTapePTM k Bool State).toNTM.initCfg input)).mpr
    ⟨coins, rfl, rfl⟩
  rw [← hlast, ← hlen]
  exact key _ (toNTM_ofDeterministic tm) p hhead

open scoped Classical in
/-- A deterministic machine accepts all coin strings of length `t` or none. -/
theorem acceptCoins_ofDeterministic (tm : MultiTapeTM k Bool State) (input : List Bool)
    (t : ℕ) : (ofDeterministic tm : MultiTapePTM k Bool State).acceptCoins input t =
      if (tm.runFrom (tm.initCfg input) t).Halted ∧
        (tm.runFrom (tm.initCfg input) t).output = [true] then 2 ^ t else 0 := by
  unfold acceptCoins
  simp only [stepCoins_ofDeterministic, List.length_ofFn]
  split_ifs with h
  · rw [Finset.filter_true_of_mem fun _ _ => h]
    simp
  · rw [Finset.filter_false_of_mem fun _ _ => h]
    simp

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **Randomized logarithmic space with one-sided error**
[Arora and Barak, Section 7.7][AroraBarak09]: some fair-coin machine with finitely many states, on
every encoded instance `enc a` of length `n`, visits at most `c * (Nat.log2 n + 1)` work-tape cells
on every branch, halts on every branch within some number of steps `t`, accepts members on at least
half of the coin strings of length `t`, and accepts non-members on none. -/
def RL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c : ℕ),
    ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
      ∃ t, M.toNTM.RunsInTime (enc a) t ∧
        (a ∈ A → 2 ^ t ≤ 2 * M.acceptCoins (enc a) t) ∧ (a ∉ A → M.acceptCoins (enc a) t = 0)}

/-- **Randomized logarithmic space with bounded two-sided error**
[Arora and Barak, Section 7.7][AroraBarak09]: as for `Cslib.Complexity.RL`, but members are accepted
on at least two thirds of the coin strings and non-members on at most one third. -/
def BPL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c : ℕ),
    ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
      ∃ t, M.toNTM.RunsInTime (enc a) t ∧
        (a ∈ A → 2 * 2 ^ t ≤ 3 * M.acceptCoins (enc a) t) ∧
        (a ∉ A → 3 * M.acceptCoins (enc a) t ≤ 2 ^ t)}

/-- **Randomized logspace with one-sided error is within `NL`**: the nondeterministic view of an
`RL` machine accepts exactly the members, since members have an accepting coin string and
non-members none. -/
theorem RL_subset_NL : RL enc ⊆ NL enc := by
  rintro A ⟨k, State, hfin, M, c, h⟩
  refine ⟨k, State, hfin, M.toNTM, c, fun a => ⟨(h a).1, ?_⟩, fun a => ?_⟩
  · obtain ⟨t, ht, hmem, hnot⟩ := (h a).2
    rw [M.accepts_toNTM_iff ht]
    constructor
    · intro ha
      have := hmem ha
      have : 0 < 2 ^ t := Nat.two_pow_pos t
      omega
    · intro hpos
      by_contra ha
      rw [hnot ha] at hpos
      exact Nat.lt_irrefl 0 hpos
  · obtain ⟨t, ht, -⟩ := (h a).2
    exact ⟨t, ht⟩

/-- **`RL` has a polynomial clock**: an `RL` machine, which only promises to halt on every branch,
halts within a polynomial number of steps `2 * (2 * (n + 1)) ^ d`, and the acceptance bounds hold
at that clock. -/
theorem exists_polyClock_of_mem_RL (h : A ∈ RL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c d : ℕ),
      ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
        M.toNTM.RunsInTime (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) ∧
        (a ∈ A → 2 ^ (2 * (2 * ((enc a).length + 1)) ^ d) ≤
          2 * M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d)) ∧
        (a ∉ A → M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) = 0) := by
  obtain ⟨k, State, hfin, M, c, hM⟩ := h
  obtain ⟨d, hd⟩ := MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log M.toNTM c
  refine ⟨k, State, hfin, M, c, d, fun a => ?_⟩
  obtain ⟨hs, t, ht, hmem, hnot⟩ := hM a
  have hT := hd hs ht
  refine ⟨hs, hT, fun ha => ?_, fun ha => ?_⟩
  · simpa using (M.two_pow_mul_le_iff ht hT 1 2).mp (by simpa using hmem ha)
  · exact Nat.le_zero.mp (by simpa using (M.mul_le_two_pow_iff ht hT 0 1).mp (by simp [hnot ha]))

/-- **`BPL` has a polynomial clock**: a `BPL` machine, which only promises to halt on every
branch, halts within a polynomial number of steps `2 * (2 * (n + 1)) ^ d`, and the acceptance
bounds hold at that clock. -/
theorem exists_polyClock_of_mem_BPL (h : A ∈ BPL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c d : ℕ),
      ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
        M.toNTM.RunsInTime (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) ∧
        (a ∈ A → 2 * 2 ^ (2 * (2 * ((enc a).length + 1)) ^ d) ≤
          3 * M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d)) ∧
        (a ∉ A → 3 * M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) ≤
          2 ^ (2 * (2 * ((enc a).length + 1)) ^ d)) := by
  obtain ⟨k, State, hfin, M, c, hM⟩ := h
  obtain ⟨d, hd⟩ := MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log M.toNTM c
  refine ⟨k, State, hfin, M, c, d, fun a => ?_⟩
  obtain ⟨hs, t, ht, hmem, hnot⟩ := hM a
  have hT := hd hs ht
  exact ⟨hs, hT, fun ha => (M.two_pow_mul_le_iff ht hT 2 3).mp (hmem ha),
    fun ha => (M.mul_le_two_pow_iff ht hT 1 3).mp (by simpa using hnot ha) |>.trans_eq (by simp)⟩

/-- A logspace decider, run as a fair-coin machine that ignores its coins, accepts members on all
coin strings and non-members on none. -/
private theorem exists_ofDeterministic_of_mem_L (h : A ∈ L enc) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c : ℕ),
      ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
        ∃ t, M.toNTM.RunsInTime (enc a) t ∧
          (a ∈ A → M.acceptCoins (enc a) t = 2 ^ t) ∧ (a ∉ A → M.acceptCoins (enc a) t = 0) := by
  obtain ⟨f, ⟨t, c, k, State, hfin, tm, htm⟩, hA⟩ := h
  refine ⟨k, State, hfin, MultiTapePTM.ofDeterministic tm, c, fun a => ?_⟩
  obtain ⟨⟨u, hhalt, hout⟩, -, hspace⟩ := htm a
  rw [MultiTapePTM.toNTM_ofDeterministic]
  have hacc : MultiTapePTM.acceptCoins (MultiTapePTM.ofDeterministic tm) (enc a) u =
      if f a = true then 2 ^ u else 0 := by
    rw [MultiTapePTM.acceptCoins_ofDeterministic, hout]
    split_ifs with hc hf hf
    · rfl
    · have h₂ := hc.2
      change [f a] = [true] at h₂
      exact absurd (by simpa using h₂) hf
    · exact absurd ⟨hhalt, by rw [hf]; rfl⟩ hc
    · rfl
  refine ⟨hspace, u, MultiTapeTM.runsInTime_of_halted hhalt, fun ha => ?_, fun ha => ?_⟩
  · rw [hacc]
    split_ifs with hf
    · rfl
    · exact absurd ((hA a).mp ha) hf
  · rw [hacc]
    split_ifs with hf
    · exact absurd ((hA a).mpr hf) ha
    · rfl

/-- **Deterministic logarithmic space is within `RL`**: a logspace decider ignores its coins. -/
theorem L_subset_RL : L enc ⊆ RL enc := by
  intro A h
  obtain ⟨k, State, hfin, M, c, hM⟩ := exists_ofDeterministic_of_mem_L h
  refine ⟨k, State, hfin, M, c, fun a => ⟨(hM a).1, ?_⟩⟩
  obtain ⟨t, ht, hmem, hnot⟩ := (hM a).2
  refine ⟨t, ht, fun ha => ?_, hnot⟩
  rw [hmem ha]
  omega

/-- **Deterministic logarithmic space is within `BPL`**: a logspace decider ignores its coins. -/
theorem L_subset_BPL : L enc ⊆ BPL enc := by
  intro A h
  obtain ⟨k, State, hfin, M, c, hM⟩ := exists_ofDeterministic_of_mem_L h
  refine ⟨k, State, hfin, M, c, fun a => ⟨(hM a).1, ?_⟩⟩
  obtain ⟨t, ht, hmem, hnot⟩ := (hM a).2
  have h2 := Nat.two_pow_pos t
  refine ⟨t, ht, fun ha => ?_, fun ha => ?_⟩
  · rw [hmem ha]
    omega
  · rw [hnot ha]
    omega

end Cslib.Complexity
