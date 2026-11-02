/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound
import Mathlib.Tactic.Ring

/-!
# Building an input prefix into a description

A description `d` and a word `p` give a description `Turing.MultiTapeTM.Universal.hardwire d p`
of a machine that behaves on every input of bits `x` as the machine described by `d` behaves on
`p ++ x` (`Turing.MultiTapeTM.Universal.Desc.computes_hardwire`). This is the s-m-n theorem for
descriptions, the counterpart of the machines printing a fixed word in
[Sipser, Lemma 6.1][Sipser2013]; that the new description is computed from `d` and `p` in
polynomial time is proved in `Complexity.Computability.Machines.Turing.MultiTape.Halting.SMN`.

The machine first writes a marker, then `p`, then a copy of its input on a new work tape, the
*virtual input tape*, and rewinds that tape to the marker. It then runs the transitions of `d`
with every reading and every move of the input head redirected to the virtual input tape
(`Turing.MultiTapeTM.Universal.Redirect.redirect`): the marker stands for the blank left of the
input, and moves are clamped at both ends as the input head's are. The redirected run is the run
of `d`, step for step (`Turing.MultiTapeTM.Universal.Redirect.iterate_stepOut_redirect`), since on
the virtual input tape the redirected transitions read what `d` reads on its input. Redirection is
independent of the prefix and is reused, after other preparations of the virtual input tape, in
`Complexity.Computability.Machines.Turing.MultiTape.Halting.Rice`.

## Main definitions

* `Turing.MultiTapeTM.Universal.Redirect.vtape`: a virtual input tape.
* `Turing.MultiTapeTM.Universal.Redirect.redirect`: transitions reading the input from the
  virtual input tape.
* `Turing.MultiTapeTM.Universal.hardwire`: the description with an input prefix built in.

## Main results

* `Turing.MultiTapeTM.Universal.Desc.computes_iff_of_iterate`: a description whose run is, after
  some steps, the image of the run of another description computes the same outputs.
* `Turing.MultiTapeTM.Universal.Redirect.iterate_stepOut_redirect`: redirected runs.
* `Turing.MultiTapeTM.Universal.Desc.computes_hardwire`,
  `Turing.MultiTapeTM.Universal.Desc.halts_hardwire`: the behavior of `hardwire d p`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

namespace Redirect

/-! ### Runs of descriptions -/

section Runs

variable {d : Desc} {x : List ℕ}

/-- A halted configuration is fixed by `stepOut`. -/
theorem stepOut_of_state_eq_none {c : SCfg} (h : c.state = none) (out : List ℕ) :
    stepOut d x (c, out) = (c, out) := by
  obtain ⟨_ | _, _, _⟩ := c
  · simp [stepOut, step]
  · simp at h

/-- Once halted, a run stays where it is. -/
theorem iterate_stepOut_of_state_eq_none {s : SCfg × List ℕ} {t t' : ℕ}
    (h : ((stepOut d x)^[t] s).1.state = none) (ht : t ≤ t') :
    (stepOut d x)^[t'] s = (stepOut d x)^[t] s := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' ht
  rw [Function.iterate_add_apply]
  exact Function.iterate_fixed (stepOut_of_state_eq_none h _) n

/-- One step through the transition `e` found for the current key. -/
theorem step_of_find? {c : SCfg} {q : ℕ} (hq : c.state = some q) {e : Key × Act}
    (he : d.table.find? (·.1 = c.key x q) = some e) : step d x c = (e.2.apply x c, e.2.output) := by
  obtain ⟨_, _, _⟩ := c
  subst hq
  simp only [step]
  rw [he]

/-- One step halting for want of a transition for the current key. -/
theorem step_of_find?_eq_none {c : SCfg} {q : ℕ} (hq : c.state = some q)
    (he : d.table.find? (·.1 = c.key x q) = none) :
    step d x c = ({ c with state := none }, none) := by
  obtain ⟨_, _, _⟩ := c
  subst hq
  simp only [step]
  rw [he]

/-- A transition is found for a key when it is the only one in the table, up to its action. -/
theorem find?_eq_some_of_mem {l : List (Key × Act)} {e : Key × Act} (hmem : e ∈ l)
    (huniq : ∀ e' ∈ l, e'.1 = e.1 → e'.2 = e.2) : l.find? (·.1 = e.1) = some e := by
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome (p := fun e' => decide (e'.1 = e.1)) |>.mpr ⟨e, hmem, decide_eq_true rfl⟩)
  have hk : e'.1 = e.1 := by
    have := List.find?_some he'
    simpa using this
  rw [he', Prod.ext hk (huniq e' (List.mem_of_find?_eq_some he') hk)]

end Runs

end Redirect

section Runs

open Redirect

variable {d D : Desc} {x X : List ℕ}

/-- **Runs agreeing after some steps.** If, after `u` steps, the run of `D` on `X` is the image
under `F` of the run of `d` on `x`, with the same outputs, and `F` preserves exactly the halted
configurations, then `D` and `d` halt with the same outputs. -/
theorem Desc.computes_iff_of_iterate (F : SCfg → SCfg)
    (hF : ∀ c, (F c).state = none ↔ c.state = none) (u : ℕ)
    (hu : ∀ t, (stepOut D X)^[u + t] (init D, []) =
      (F ((stepOut d x)^[t] (init d, [])).1, ((stepOut d x)^[t] (init d, [])).2))
    (o : List ℕ) : D.Computes X o ↔ d.Computes x o := by
  have hlive : ((stepOut D X)^[u] (init D, [])).1.state ≠ none := by
    rw [← add_zero u, hu 0]
    simp [hF, init]
  constructor
  · rintro ⟨T, hT⟩
    have hT' : ((stepOut D X)^[T] (init D, [])).1.state = none := by
      simpa [simulate] using congrArg Prod.snd hT
    have hle : u ≤ T := by
      by_contra hlt
      exact hlive (by rw [iterate_stepOut_of_state_eq_none hT' (by omega)]; exact hT')
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨t, ?_⟩
    simp only [simulate] at hT ⊢
    rw [hu t, Prod.mk.injEq, Option.isNone_iff_eq_none, hF] at hT
    rw [Prod.mk.injEq, Option.isNone_iff_eq_none]
    exact hT
  · rintro ⟨t, ht⟩
    refine ⟨u + t, ?_⟩
    simp only [simulate] at ht ⊢
    rw [hu t, Prod.mk.injEq, Option.isNone_iff_eq_none, hF]
    rwa [Prod.mk.injEq, Option.isNone_iff_eq_none] at ht

end Runs

namespace Redirect

/-! ### Virtual input tapes -/

/-- The symbol marking the left end of a virtual input. -/
def marker : ℕ := 2

/-- The cells of a virtual input: the marker, then the input. -/
def vcells (xs : List ℕ) : List (Option ℕ) := some marker :: xs.map some

/-- A virtual input tape for the input `xs`: the marker at position `base`, the input right of it
and blanks beyond, the cells `l` left of the marker, nearest first, and the head on the `v`-th cell
right of the marker. -/
def vtape (base : ℤ) (l : List (Option ℕ)) (xs : List ℕ) (v : ℕ) : Tape :=
  ⟨base + v, ((vcells xs).take v).reverse ++ l, (vcells xs).drop v⟩

/-- A tape holding the cells `cs` left of its head, which is on the first blank after them. -/
def wtape (cs : List (Option ℕ)) : Tape := ⟨cs.length, cs.reverse, []⟩

/-- The input symbol that a virtual input tape stands for when it reads `s`: the marker stands for
the blank left of the input. -/
def vsym (s : Option ℕ) : Option ℕ := if s = some marker then none else s

/-- The move of the head of a virtual input tape reading `s`, for the move `m` of the input head:
at the marker and at the blank after the input, the moves that the input head cannot make are
dropped. -/
def vmove (s : Option ℕ) (m : SignType) : SignType :=
  if s = some marker then (if m = .pos then .pos else .zero)
  else if s = none then (if m = .neg then .neg else .zero) else m

section VTape

variable {xs : List ℕ} {base : ℤ} {l : List (Option ℕ)} {v : ℕ}

theorem length_vcells (xs : List ℕ) : (vcells xs).length = xs.length + 1 := by
  simp [vcells]

theorem wtape_vcells (xs : List ℕ) : wtape (vcells xs) = vtape 0 [] xs (xs.length + 1) := by
  simp [wtape, vtape, length_vcells, List.take_of_length_le, List.drop_of_length_le]

@[simp]
theorem read_wtape (cs : List (Option ℕ)) : (wtape cs).read = none :=
  rfl

/-- Writing at the first blank and moving on appends a cell. -/
theorem wtape_write_move (cs : List (Option ℕ)) (s : Option ℕ) :
    ((wtape cs).write s).move .pos = wtape (cs ++ [s]) := by
  simp [wtape, Tape.write, Tape.move, Tape.read]

theorem read_vtape_zero : (vtape base l xs 0).read = some marker :=
  rfl

theorem read_vtape_succ (v : ℕ) : (vtape base l xs (v + 1)).read = inputSymbol xs (v + 1) := by
  simp only [vtape, vcells, Tape.read, List.drop_succ_cons, inputSymbol, Nat.add_one_ne_zero,
    ↓reduceIte, Nat.add_sub_cancel, ← List.map_drop]
  cases xs.drop v <;> rfl

theorem vtape_move_pos (hv : v ≤ xs.length) :
    (vtape base l xs v).move .pos = vtape base l xs (v + 1) := by
  have hlt : v < (vcells xs).length := by rw [length_vcells]; omega
  simp only [vtape, Tape.move, Tape.read, List.drop_eq_getElem_cons hlt, List.headD_cons,
    List.tail_cons, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
    List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append]
  push_cast
  rw [add_assoc]

theorem vtape_move_neg (hv : v ≤ xs.length) :
    (vtape base l xs (v + 1)).move .neg = vtape base l xs v := by
  have hlt : v < (vcells xs).length := by rw [length_vcells]; omega
  simp only [vtape, Tape.move, List.take_add_one, List.getElem?_eq_getElem hlt,
    Option.toList_some, List.reverse_append, List.reverse_singleton, List.cons_append,
    List.tail_cons, List.headD_cons, ← List.drop_eq_getElem_cons hlt, List.nil_append]
  congr 1
  push_cast
  ring

/-- On a virtual input tape, the redirected reading is the reading of the input head. -/
theorem vsym_read_vtape (hxs : ∀ a ∈ xs, a ≠ marker) :
    vsym (vtape base l xs v).read = inputSymbol xs v := by
  cases v with
  | zero => rfl
  | succ v =>
    rw [read_vtape_succ, vsym]
    split_ifs with h
    · simp only [inputSymbol, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h
      exact absurd rfl (hxs marker (List.mem_of_mem_drop (List.mem_of_mem_head? h)))
    · rfl

/-- On a virtual input tape, the redirected move is the move of the input head. -/
theorem move_vmove_vtape (hxs : ∀ a ∈ xs, a ≠ marker) (hv : v ≤ xs.length + 1) (m : SignType) :
    (vtape base l xs v).move (vmove (vtape base l xs v).read m) =
      vtape base l xs (moveInput v (inputSymbol xs v) m) := by
  cases v with
  | zero =>
    rw [read_vtape_zero]
    rcases m with _ | _ | _
    · rfl
    · rfl
    · exact vtape_move_pos (Nat.zero_le _)
  | succ v =>
    rw [read_vtape_succ]
    rcases Nat.lt_or_ge v xs.length with h | h
    · have hs : inputSymbol xs (v + 1) = some xs[v] := by
        simp [inputSymbol, List.head?_drop, List.getElem?_eq_getElem h]
      have hne : xs[v] ≠ marker := hxs _ (List.getElem_mem h)
      have hv : vmove (some xs[v]) m = m := by simp [vmove, hne]
      rw [hs, hv]
      rcases m with _ | _ | _
      · rfl
      · exact vtape_move_neg h.le
      · exact vtape_move_pos h
    · have hs : inputSymbol xs (v + 1) = none := by
        simp [inputSymbol, List.drop_of_length_le h]
      rw [hs]
      rcases m with _ | _ | _
      · rfl
      · exact vtape_move_neg (by omega)
      · rfl

end VTape

/-! ### Work tapes -/

section Tapes

theorem applyTapes_nil (ts : List Tape) : applyTapes ts [] = ts := by
  cases ts <;> rfl

/-- Actions that neither write nor move leave tapes as they are. -/
theorem applyTapes_append_idle {preT : List Tape} {pre : List (Option ℕ)}
    (h : pre.length = preT.length) (ts : List Tape) (as : List TapeAct) :
    applyTapes (preT ++ ts) ((pre.map fun _ => (none, .zero)) ++ as) =
      preT ++ applyTapes ts as := by
  induction preT generalizing pre with
  | nil => rw [List.length_eq_zero_iff.mp h]; rfl
  | cons t preT ih =>
    obtain ⟨p, pre, rfl⟩ := List.exists_cons_of_length_eq_add_one h
    simp only [List.map_cons, List.cons_append, applyTapes, ih (Nat.succ.inj h)]
    rfl

/-- Actions cut to the first work tapes leave the others as they are. -/
theorem applyTapes_append_take (ts us : List Tape) (as : List TapeAct) :
    applyTapes (ts ++ us) (as.take ts.length) = applyTapes ts as ++ us := by
  induction ts generalizing as with
  | nil => simp [applyTapes_nil, applyTapes]
  | cons t ts ih => cases as <;> simp [applyTapes, ih, applyTapes_nil]

variable {d : Desc} {xs : List ℕ} {c : SCfg}

/-- A step keeps the input head on the input or its boundaries. -/
theorem inputPos_step_le (hc : c.inputPos ≤ xs.length + 1) :
    (step d xs c).1.inputPos ≤ xs.length + 1 := by
  obtain ⟨_ | q, p, ws⟩ := c
  · exact hc
  · simp only [step]
    split
    · exact hc
    · exact moveInput_le hc _

/-- A step keeps the number of work tapes. -/
theorem length_workTapes_step : (step d xs c).1.workTapes.length = c.workTapes.length := by
  obtain ⟨_ | q, p, ws⟩ := c
  · rfl
  · simp only [step]
    split
    · rfl
    · exact length_applyTapes_eq _ _

end Tapes

/-! ### Redirecting the input -/

/-- The symbols that a virtual input tape reads where the input head reads `i`: the marker or a
blank for a blank, and `i` itself otherwise. Nothing stands for the marker itself, so transitions
reading the marker on the input are dropped. -/
def vlift : Option ℕ → List (Option ℕ)
  | none => [some marker, none]
  | some b => if b = marker then [] else [some b]

theorem mem_vlift {i s : Option ℕ} : s ∈ vlift i ↔ i = vsym s := by
  rcases i with _ | b <;> rcases s with _ | a <;> simp only [vlift, vsym] <;> split_ifs <;>
    simp_all [eq_comm]

variable {φ : ℕ → ℕ} {r : Option ℕ} {pre : List (Option ℕ)} {suf : ℕ}
  {adj : List TapeAct → List TapeAct}

/-- The transition `e` reading `s` on the virtual input tape, the first work tape: the state
renamed by `φ`, the input head reading `r` and kept in place, the work tapes of `e` after further
tapes reading `pre`, left alone, and before `suf` blank ones, and the actions on the work tapes of
`e` adjusted by `adj`. -/
def redirectEntry (φ : ℕ → ℕ) (r : Option ℕ) (pre : List (Option ℕ)) (suf : ℕ)
    (adj : List TapeAct → List TapeAct) (e : Key × Act) (s : Option ℕ) : Key × Act :=
  (⟨φ e.1.state, r, s :: (pre ++ (e.1.work ++ List.replicate suf none))⟩,
    ⟨.zero, (none, vmove s e.2.inputTape) :: ((pre.map fun _ => (none, .zero)) ++
      adj e.2.workTapes), e.2.output, e.2.state.map φ⟩)

/-- **Redirected transitions**: the transitions of `table` reading the input from the virtual
input tape (`Turing.MultiTapeTM.Universal.Redirect.redirectEntry`). -/
def redirect (φ : ℕ → ℕ) (r : Option ℕ) (pre : List (Option ℕ)) (suf : ℕ)
    (adj : List TapeAct → List TapeAct) (table : List (Key × Act)) : List (Key × Act) :=
  table.flatMap fun e => (vlift e.1.input).map (redirectEntry φ r pre suf adj e)

/-- The redirected transition found for a key is the redirection of the transition found for the
key it stands for. -/
theorem find?_redirect (hφ : φ.Injective) (q : ℕ) (s : Option ℕ) (ws : List (Option ℕ))
    (table : List (Key × Act)) :
    (redirect φ r pre suf adj table).find?
        (·.1 = ⟨φ q, r, s :: (pre ++ (ws ++ List.replicate suf none))⟩) =
      (table.find? (·.1 = ⟨q, vsym s, ws⟩)).map fun e => redirectEntry φ r pre suf adj e s := by
  induction table with
  | nil => rfl
  | cons e table ih =>
    have hkey (s' : Option ℕ) : (redirectEntry φ r pre suf adj e s').1 =
        ⟨φ q, r, s :: (pre ++ (ws ++ List.replicate suf none))⟩ ↔
          e.1.state = q ∧ s' = s ∧ e.1.work = ws := by
      simp [redirectEntry, hφ.eq_iff]
    rw [redirect, List.flatMap_cons, List.find?_append, ← redirect, ih, List.find?_cons,
      List.find?_map]
    by_cases he : e.1 = ⟨q, vsym s, ws⟩
    · have hs : s ∈ vlift e.1.input := mem_vlift.mpr (by rw [he])
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (List.find?_isSome
        (p := (fun x => decide (x.1 = (⟨φ q, r, s :: (pre ++ (ws ++ List.replicate suf none))⟩ :
          Key))) ∘ redirectEntry φ r pre suf adj e) |>.mpr ⟨s, hs, by simp [hkey, he]⟩)
      have := List.find?_some hs'
      simp only [Function.comp_apply, decide_eq_true_eq, hkey] at this
      rw [hs', this.2.1]
      simp [he]
    · have hnone : (vlift e.1.input).find? ((fun x => decide (x.1 =
          (⟨φ q, r, s :: (pre ++ (ws ++ List.replicate suf none))⟩ : Key))) ∘
            redirectEntry φ r pre suf adj e) = none := by
        refine List.find?_eq_none.mpr fun s' hs' h => he ?_
        simp only [Function.comp_apply, decide_eq_true_eq, hkey] at h
        obtain ⟨h₁, rfl, h₃⟩ := h
        obtain ⟨⟨q', i, w⟩, a⟩ := e
        simp only at h₁ h₃ hs' ⊢
        rw [h₁, h₃, mem_vlift.mp hs']
      rw [hnone]
      simp [he]

/-- The configuration standing for the configuration `c` of a redirected description: the state
renamed by `φ`, the input head at `rp`, the virtual input tape for `xs` with the head at the input
position of `c`, and the work tapes of `c` between `preT` and `sufT`. -/
def redirectCfg (φ : ℕ → ℕ) (rp : ℕ) (base : ℤ) (l : List (Option ℕ)) (xs : List ℕ)
    (preT sufT : List Tape) (c : SCfg) : SCfg :=
  ⟨c.state.map φ, rp, vtape base l xs c.inputPos :: (preT ++ (c.workTapes ++ sufT))⟩

section Step

variable {D d : Desc} {X xs : List ℕ} {rp : ℕ} {base : ℤ} {l : List (Option ℕ)}
  {preT sufT : List Tape}

/-- **A redirected step**: in a description holding the redirected transitions of `d` for the
renamed states, a step from a configuration standing for `c` stands for the step of `d` from `c`,
and emits the same symbol. -/
theorem step_redirect (hφ : φ.Injective)
    (hD : ∀ q ws, D.table.find? (·.1 = ⟨φ q, r, ws⟩) =
      (redirect φ r pre suf adj d.table).find? (·.1 = ⟨φ q, r, ws⟩))
    (hrp : inputSymbol X rp = r) (hxs : ∀ a ∈ xs, a ≠ marker) (hpre : preT.map Tape.read = pre)
    (hsuf : sufT.map Tape.read = List.replicate suf none) {c : SCfg}
    (hc : c.inputPos ≤ xs.length + 1)
    (hadj : ∀ was,
      applyTapes (c.workTapes ++ sufT) (adj was) = applyTapes c.workTapes was ++ sufT) :
    step D X (redirectCfg φ rp base l xs preT sufT c) =
      (redirectCfg φ rp base l xs preT sufT (step d xs c).1, (step d xs c).2) := by
  obtain ⟨_ | q, p, ws⟩ := c
  · rfl
  · have hkey : (redirectCfg φ rp base l xs preT sufT ⟨some q, p, ws⟩).key X (φ q) =
        ⟨φ q, r, (vtape base l xs p).read :: (pre ++ (ws.map Tape.read ++
          List.replicate suf none))⟩ := by
      simp [redirectCfg, SCfg.key, hrp, ← hpre, ← hsuf]
    have hfind := (hD q _).trans
      (find?_redirect hφ q (vtape base l xs p).read (ws.map Tape.read) d.table)
    rw [← hkey, vsym_read_vtape hxs,
      show (⟨q, inputSymbol xs p, ws.map Tape.read⟩ : Key) = SCfg.key ⟨some q, p, ws⟩ xs q
        from rfl] at hfind
    rcases hfe : d.table.find? (·.1 = SCfg.key ⟨some q, p, ws⟩ xs q) with _ | e
    · rw [step_of_find?_eq_none rfl hfe, step_of_find?_eq_none rfl (hfind.trans (by
        rw [hfe]; rfl))]
      rfl
    · rw [step_of_find? rfl hfe, step_of_find? rfl (hfind.trans (by rw [hfe]; rfl))]
      simp only [redirectCfg, Act.apply, redirectEntry, Prod.mk.injEq, SCfg.mk.injEq, and_true,
        true_and, applyTapes]
      refine ⟨rfl, ?_⟩
      rw [applyTapes_append_idle (by simp [← hpre]), hadj]
      exact congrArg₂ (· :: ·) (move_vmove_vtape hxs hc _) rfl

/-- **Redirected runs**: from a configuration standing for `c`, the run of `D` stands for the run
of `d` from `c`, with the same output. -/
theorem iterate_stepOut_redirect (hφ : φ.Injective)
    (hD : ∀ q ws, D.table.find? (·.1 = ⟨φ q, r, ws⟩) =
      (redirect φ r pre suf adj d.table).find? (·.1 = ⟨φ q, r, ws⟩))
    (hrp : inputSymbol X rp = r) (hxs : ∀ a ∈ xs, a ≠ marker) (hpre : preT.map Tape.read = pre)
    (hsuf : sufT.map Tape.read = List.replicate suf none) {n : ℕ}
    (hadj : ∀ ts : List Tape, ts.length = n → ∀ was,
      applyTapes (ts ++ sufT) (adj was) = applyTapes ts was ++ sufT)
    (t : ℕ) {c : SCfg} (hc : c.inputPos ≤ xs.length + 1) (hn : c.workTapes.length = n)
    (out : List ℕ) :
    (stepOut D X)^[t] (redirectCfg φ rp base l xs preT sufT c, out) =
      (redirectCfg φ rp base l xs preT sufT ((stepOut d xs)^[t] (c, out)).1,
        ((stepOut d xs)^[t] (c, out)).2) := by
  induction t generalizing c out with
  | zero => rfl
  | succ t ih =>
    have hs := step_redirect (base := base) (l := l) hφ hD hrp hxs hpre hsuf hc (hadj _ hn)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show stepOut D X (redirectCfg φ rp base l xs preT sufT c, out) =
        (redirectCfg φ rp base l xs preT sufT (stepOut d xs (c, out)).1,
          (stepOut d xs (c, out)).2) by simp only [stepOut, hs]]
    exact ih (inputPos_step_le hc) (length_workTapes_step.trans hn) _

end Step

/-! ### Rewinding the virtual input tape -/

@[simp]
theorem read_blank : Tape.blank.read = none :=
  rfl

theorem map_read_replicate_blank (k : ℕ) :
    (List.replicate k Tape.blank).map Tape.read = List.replicate k none := by
  simp only [List.map_replicate]
  rfl

@[simp]
theorem eBit_false : eBit false = 0 :=
  rfl

@[simp]
theorem eBit_true : eBit true = 1 :=
  rfl

/-- The symbols that the input head reads on an input of bits: blanks and the bits. -/
def bitSyms : List (Option ℕ) := [none, some 0, some 1]

theorem inputSymbol_map_eBit_mem (x : List Bool) (p : ℕ) :
    inputSymbol (x.map eBit) p ∈ bitSyms := by
  unfold inputSymbol
  split_ifs
  · simp [bitSyms]
  · rcases h : (x.drop (p - 1)).head? with _ | b
    · simp [bitSyms, ← List.map_drop, h]
    · cases b <;> simp [bitSyms, ← List.map_drop, h]

/-- Transitions rewinding the virtual input tape, the first work tape, in the state `q`, with the
input head reading `r` and the other work tapes reading `rest`: over blanks and bits to the marker,
and then onto the first cell after it, in the state `next`. -/
def rewindEntries (q : ℕ) (r : Option ℕ) (rest : List (Option ℕ)) (next : ℕ) :
    List (Key × Act) :=
  bitSyms.map (fun s => (⟨q, r, s :: rest⟩, ⟨.zero, [(none, .neg)], none, some q⟩)) ++
    [(⟨q, r, some marker :: rest⟩, ⟨.zero, [(none, .pos)], none, some next⟩)]

/-- **Rewinding** a virtual input tape of bits from the `v`-th cell takes `v + 1` steps. -/
theorem iterate_stepOut_rewind {D : Desc} {X : List ℕ} {q next rp : ℕ} {rest : List Tape}
    {base : ℤ} {l : List (Option ℕ)} {w : List ℕ}
    (hD : ∀ e ∈ rewindEntries q (inputSymbol X rp) (rest.map Tape.read) next,
      D.table.find? (·.1 = e.1) = some e)
    (hw : ∀ a ∈ w, a = 0 ∨ a = 1) (out : List ℕ) {v : ℕ} (hv : v ≤ w.length + 1) :
    (stepOut D X)^[v + 1] (⟨some q, rp, vtape base l w v :: rest⟩, out) =
      (⟨some next, rp, vtape base l w 1 :: rest⟩, out) := by
  induction v with
  | zero =>
    have he := hD (⟨q, inputSymbol X rp, some marker :: rest.map Tape.read⟩,
      ⟨.zero, [(none, .pos)], none, some next⟩) (by simp [rewindEntries])
    rw [Function.iterate_one, stepOut,
      step_of_find? (c := ⟨some q, rp, vtape base l w 0 :: rest⟩) (q := q) rfl he]
    simp only [Act.apply, moveInput, applyTapes, applyTapes_nil, Option.toList_none,
      List.append_nil]
    rw [show (vtape base l w 0).apply (none, .pos) = vtape base l w (0 + 1) from
      vtape_move_pos (Nat.zero_le _)]
  | succ v ih =>
    have hs : (vtape base l w (v + 1)).read ∈ bitSyms := by
      simp only [read_vtape_succ, inputSymbol, Nat.add_one_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel]
      rcases h : (w.drop v).head? with _ | a
      · simp [bitSyms]
      · rcases hw a (List.mem_of_mem_drop (List.mem_of_mem_head? h)) with rfl | rfl <;>
          simp [bitSyms]
    have he := hD (⟨q, inputSymbol X rp, (vtape base l w (v + 1)).read :: rest.map Tape.read⟩,
      ⟨.zero, [(none, .neg)], none, some q⟩)
      (List.mem_append_left _ (List.mem_map.mpr ⟨_, hs, rfl⟩))
    rw [Function.iterate_succ_apply,
      show stepOut D X (⟨some q, rp, vtape base l w (v + 1) :: rest⟩, out) =
        (⟨some q, rp, vtape base l w v :: rest⟩, out) by
        rw [stepOut, step_of_find? (c := ⟨some q, rp, vtape base l w (v + 1) :: rest⟩) (q := q)
          rfl he]
        simp only [Act.apply, moveInput, applyTapes, applyTapes_nil, Option.toList_none,
          List.append_nil]
        rw [show (vtape base l w (v + 1)).apply (none, .neg) = vtape base l w v from
          vtape_move_neg (by omega)]]
    exact ih (by omega)

end Redirect

/-! ### Building in an input prefix -/

namespace Hardwire

open Redirect

/-- The transitions writing the marker and the prefix `p` on the virtual input tape, before `k`
blank work tapes, whatever the input head reads: the marker in the state `0`, and the `i`-th symbol
from the end of `p` in the state `2 * i + 6`. The state after the last symbol is `4`. -/
def writeEntries (p : List Bool) (k : ℕ) : List (Key × Act) :=
  bitSyms.map (fun r => (⟨0, r, none :: List.replicate k none⟩,
    ⟨.zero, [(some (some marker), .pos)], none, some (2 * p.length + 4)⟩)) ++
  p.reverse.zipIdx.flatMap fun bi => bitSyms.map fun r =>
    (⟨2 * bi.2 + 6, r, none :: List.replicate k none⟩,
      ⟨.zero, [(some (some (eBit bi.1)), .pos)], none, some (2 * bi.2 + 4)⟩)

/-- The transitions copying the input of bits to the virtual input tape in the state `4`, before
`k` blank work tapes, and moving to the state `2` at its end. -/
def copyEntries (k : ℕ) : List (Key × Act) :=
  [(⟨4, some 0, none :: List.replicate k none⟩, ⟨.pos, [(some (some 0), .pos)], none, some 4⟩),
    (⟨4, some 1, none :: List.replicate k none⟩, ⟨.pos, [(some (some 1), .pos)], none, some 4⟩),
    (⟨4, none, none :: List.replicate k none⟩, ⟨.zero, [], none, some 2⟩)]

end Hardwire

open Redirect Hardwire in
/-- **The description `d` with the input prefix `p` built in.** It writes the marker and `p` on a
new first work tape, the virtual input tape
(`Turing.MultiTapeTM.Universal.Hardwire.writeEntries`), copies the input after them
(`Turing.MultiTapeTM.Universal.Hardwire.copyEntries`), rewinds that tape
(`Turing.MultiTapeTM.Universal.Redirect.rewindEntries`) and runs the transitions of `d` reading
the input from it (`Turing.MultiTapeTM.Universal.Redirect.redirect`). These steps use even states,
and the states of `d` become odd. -/
def hardwire (d : Desc) (p : List Bool) : Desc :=
  ⟨d.tapes + 1, 0, writeEntries p d.tapes ++ copyEntries d.tapes ++
    rewindEntries 2 none (List.replicate d.tapes none) (2 * d.q₀ + 1) ++
    redirect (fun q => 2 * q + 1) none [] 0 id d.table⟩

namespace Hardwire

open Redirect

/-- The action of the preparing transitions of `hardwire d p`, as a function of their keys. -/
def act (p : List Bool) (q₀ : ℕ) (key : Key) : Act :=
  if key.state = 0 then ⟨.zero, [(some (some marker), .pos)], none, some (2 * p.length + 4)⟩
  else if key.state = 2 then
    if key.work.head? = some (some marker) then ⟨.zero, [(none, .pos)], none, some q₀⟩
    else ⟨.zero, [(none, .neg)], none, some 2⟩
  else if key.state = 4 then
    match key.input with
    | some b => ⟨.pos, [(some (some b), .pos)], none, some 4⟩
    | none => ⟨.zero, [], none, some 2⟩
  else ⟨.zero, [(some (some (eBit (p.reverse.getD ((key.state - 6) / 2) false))), .pos)], none,
    some (key.state - 2)⟩

/-- The preparing transitions of `hardwire d p`. -/
def prep (d : Desc) (p : List Bool) : List (Key × Act) :=
  writeEntries p d.tapes ++ copyEntries d.tapes ++
    rewindEntries 2 none (List.replicate d.tapes none) (2 * d.q₀ + 1)

theorem table_hardwire (d : Desc) (p : List Bool) :
    (hardwire d p).table = prep d p ++ redirect (fun q => 2 * q + 1) none [] 0 id d.table :=
  rfl

/-- The preparing transitions have even states, and their actions are functions of their keys. -/
theorem prep_spec {d : Desc} {p : List Bool} {e : Key × Act} (he : e ∈ prep d p) :
    e.1.state % 2 = 0 ∧ e.2 = act p (2 * d.q₀ + 1) e.1 := by
  simp only [prep, writeEntries, copyEntries, rewindEntries, bitSyms, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ((⟨r, -, rfl⟩ | ⟨⟨b, i⟩, hbi, r, -, rfl⟩) | (rfl | rfl | rfl)) |
    (⟨s, hs, rfl⟩ | rfl)
  · simp [act]
  · rw [List.mem_zipIdx_iff_getElem?] at hbi
    dsimp only at hbi ⊢
    refine ⟨by omega, ?_⟩
    have h0 : 2 * i + 6 ≠ 0 := by omega
    have h2 : 2 * i + 6 ≠ 2 := by omega
    have h4 : 2 * i + 6 ≠ 4 := by omega
    simp only [act, h0, h2, h4, ↓reduceIte, show (2 * i + 6 - 6) / 2 = i by omega,
      List.getD_eq_getElem?_getD, hbi, Option.getD_some, show 2 * i + 6 - 2 = 2 * i + 4 by omega]
  · simp [act]
  · simp [act]
  · simp [act]
  · rcases hs with rfl | rfl | rfl <;> simp [act, marker]
  · simp [act]

theorem state_redirect {d : Desc} {e : Key × Act}
    (he : e ∈ redirect (fun q => 2 * q + 1) none [] 0 id d.table) : e.1.state % 2 = 1 := by
  simp only [redirect, List.mem_flatMap, List.mem_map] at he
  obtain ⟨e', -, s, -, rfl⟩ := he
  simp [redirectEntry]

/-- Each preparing transition is the one found for its key. -/
theorem find?_prep {d : Desc} {p : List Bool} {e : Key × Act} (he : e ∈ prep d p) :
    (hardwire d p).table.find? (·.1 = e.1) = some e := by
  refine find?_eq_some_of_mem (List.mem_append_left _ he) fun e' he' hk => ?_
  rw [table_hardwire, List.mem_append] at he'
  rcases he' with he' | he'
  · rw [(prep_spec he').2, (prep_spec he).2, hk]
  · have := state_redirect he'
    have := (prep_spec he).1
    rw [hk] at *
    omega

/-- For odd states, the transitions found are the redirected transitions of `d`. -/
theorem find?_redirect_hardwire (d : Desc) (p : List Bool) (q : ℕ) (ws : List (Option ℕ)) :
    (hardwire d p).table.find? (·.1 = ⟨2 * q + 1, none, ws⟩) =
      (redirect (fun q => 2 * q + 1) none [] 0 id d.table).find?
        (·.1 = ⟨2 * q + 1, none, ws⟩) := by
  rw [table_hardwire, List.find?_append, List.find?_eq_none.mpr fun e he h => by
    have := (prep_spec he).1
    rw [of_decide_eq_true h] at this
    simp at this, Option.none_or]


section Run

variable (d : Desc) (p x : List Bool)

/-- A step through a preparing transition. -/
theorem stepOut_of_mem_prep {c : SCfg} {q : ℕ} (hq : c.state = some q) {e : Key × Act}
    (he : e ∈ prep d p) (hkey : c.key (x.map eBit) q = e.1) (out : List ℕ) :
    stepOut (hardwire d p) (x.map eBit) (c, out) =
      (e.2.apply (x.map eBit) c, out ++ e.2.output.toList) := by
  have hf := find?_prep he
  rw [← hkey] at hf
  rw [stepOut, step_of_find? hq hf]

/-- Writing the marker and the first `j` symbols of the prefix takes `j + 1` steps. -/
theorem iterate_write {j : ℕ} (hj : j ≤ p.length) :
    (stepOut (hardwire d p) (x.map eBit))^[j + 1] (init (hardwire d p), []) =
      (⟨some (2 * (p.length - j) + 4), 1,
        wtape (some marker :: (p.take j).map (some ∘ eBit)) ::
          List.replicate d.tapes Tape.blank⟩, []) := by
  induction j with
  | zero =>
    have he : ((⟨0, inputSymbol (x.map eBit) 1, none :: List.replicate d.tapes none⟩,
        ⟨.zero, [(some (some marker), .pos)], none, some (2 * p.length + 4)⟩) : Key × Act) ∈
          prep d p := by
      simp only [prep, writeEntries, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl ⟨_, inputSymbol_map_eBit_mem x 1, rfl⟩))
    rw [Function.iterate_one, stepOut_of_mem_prep d p x rfl he (by
      simp [SCfg.key, init, hardwire, List.replicate_succ, Tape.read]) []]
    simp only [init, hardwire, List.replicate_succ, Act.apply, moveInput, applyTapes,
      applyTapes_nil, Option.toList_none, List.append_nil, Nat.sub_zero, List.take_zero,
      List.map_nil]
    rw [show Tape.blank = wtape [] from rfl]
    exact congrArg₂ _ (congrArg₂ _ rfl (congrArg₂ _ (wtape_write_move [] _) rfl)) rfl
  | succ j ih =>
    have hjl : j < p.length := by omega
    obtain ⟨i, hi⟩ : ∃ i, i = p.length - 1 - j := ⟨_, rfl⟩
    have hb : p.reverse[i]? = some p[j] := by
      rw [hi, List.getElem?_reverse (by omega), List.getElem?_eq_getElem (by omega)]
      congr 2
      omega
    have he : ((⟨2 * i + 6, inputSymbol (x.map eBit) 1, none :: List.replicate d.tapes none⟩,
        ⟨.zero, [(some (some (eBit p[j])), .pos)], none, some (2 * i + 4)⟩) : Key × Act) ∈
          prep d p := by
      simp only [prep, writeEntries, List.mem_append, List.mem_map, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inr ⟨(p[j], i), List.mem_zipIdx_iff_getElem?.mpr hb, _,
        inputSymbol_map_eBit_mem x 1, rfl⟩))
    rw [Function.iterate_succ_apply', ih hjl.le, stepOut_of_mem_prep d p x rfl he (by
      simp only [SCfg.key, List.map_cons, read_wtape, map_read_replicate_blank, Key.mk.injEq,
        and_true]
      omega) []]
    simp only [Act.apply, moveInput, applyTapes, applyTapes_nil, Option.toList_none,
      List.append_nil, SCfg.mk.injEq, Prod.mk.injEq, and_true, true_and]
    refine ⟨?_, ?_⟩
    · rw [hi]
      congr 2
      omega
    rw [show (wtape (some marker :: (p.take j).map (some ∘ eBit))).apply
        (some (some (eBit p[j])), .pos) = _ from wtape_write_move _ _, List.take_add_one,
      List.getElem?_eq_getElem hjl, Option.toList_some, List.map_append, List.cons_append]
    rfl

/-- Copying the first `j` symbols of the input takes `j` further steps. -/
theorem iterate_copy {j : ℕ} (hj : j ≤ x.length) :
    (stepOut (hardwire d p) (x.map eBit))^[p.length + 1 + j] (init (hardwire d p), []) =
      (⟨some 4, j + 1, wtape (some marker :: (p ++ x.take j).map (some ∘ eBit)) ::
          List.replicate d.tapes Tape.blank⟩, []) := by
  induction j with
  | zero =>
    rw [add_zero, iterate_write d p x le_rfl]
    simp
  | succ j ih =>
    have hjl : j < x.length := by omega
    have hs : inputSymbol (x.map eBit) (j + 1) = some (eBit x[j]) := by
      simp [inputSymbol, List.head?_drop, List.getElem?_eq_getElem hjl]
    have he : ((⟨4, some (eBit x[j]), none :: List.replicate d.tapes none⟩,
        ⟨.pos, [(some (some (eBit x[j])), .pos)], none, some 4⟩) : Key × Act) ∈ prep d p := by
      simp only [prep, copyEntries, List.mem_append, List.mem_cons]
      cases x[j] <;> simp
    rw [← add_assoc, Function.iterate_succ_apply', ih hjl.le, stepOut_of_mem_prep d p x rfl he (by
      simp [SCfg.key, hs]) []]
    simp only [Act.apply, applyTapes, applyTapes_nil, Option.toList_none, List.append_nil,
      SCfg.mk.injEq, Prod.mk.injEq, and_true, true_and]
    refine ⟨by simp [moveInput, hs], ?_⟩
    rw [show (wtape (some marker :: (p ++ x.take j).map (some ∘ eBit))).apply
        (some (some (eBit x[j])), .pos) = _ from wtape_write_move _ _, List.take_add_one,
      List.getElem?_eq_getElem hjl, Option.toList_some, ← List.append_assoc]
    simp only [List.map_append, List.map_take, List.append_assoc, List.map_cons, List.map_nil,
      List.cons_append]
    rfl

/-- **The preparation**: after `2 * (p.length + x.length) + 4` steps, `hardwire d p` is in the
configuration standing for the initial configuration of `d` on `p ++ x`, redirected. -/
theorem iterate_prepare :
    (stepOut (hardwire d p) (x.map eBit))^[2 * (p.length + x.length) + 4]
        (init (hardwire d p), []) =
      (redirectCfg (fun q => 2 * q + 1) (x.length + 1) 0 [] ((p ++ x).map eBit) [] []
        (init d), []) := by
  have hw : (some marker :: (p ++ x.take x.length).map (some ∘ eBit)) =
      vcells ((p ++ x).map eBit) := by
    simp [vcells, List.map_map]
  have he : ((⟨4, none, none :: List.replicate d.tapes none⟩, ⟨.zero, [], none, some 2⟩) :
      Key × Act) ∈ prep d p := by
    simp [prep, copyEntries]
  have hs : inputSymbol (x.map eBit) (x.length + 1) = none := by
    simp [inputSymbol]
  have hend := stepOut_of_mem_prep d p x (c := ⟨some 4, x.length + 1,
    wtape (vcells ((p ++ x).map eBit)) :: List.replicate d.tapes Tape.blank⟩) rfl he
      (by simp [SCfg.key, hs]) []
  simp only [Act.apply, moveInput, applyTapes_nil, Option.toList_none, List.append_nil] at hend
  have hrw := iterate_stepOut_rewind (D := hardwire d p) (X := x.map eBit) (q := 2)
    (next := 2 * d.q₀ + 1) (rp := x.length + 1) (rest := List.replicate d.tapes Tape.blank)
    (base := 0) (l := []) (w := (p ++ x).map eBit) (fun e he => find?_prep (by
      rw [hs, map_read_replicate_blank] at he
      exact List.mem_append_right _ he)) (fun a ha => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
        cases b <;> simp) [] (v := ((p ++ x).map eBit).length + 1)
    le_rfl
  rw [show 2 * (p.length + x.length) + 4 =
      (((p ++ x).map eBit).length + 1 + 1) + 1 + (p.length + 1 + x.length) by
        simp only [List.length_map, List.length_append]; omega,
    Function.iterate_add_apply, iterate_copy d p x le_rfl, hw, Function.iterate_succ_apply,
    hend, wtape_vcells, hrw]
  simp [redirectCfg, init, Tape.blank]

end Run

end Hardwire

open Redirect Hardwire in
/-- **The behavior of `hardwire d p`**: on every input of bits `x`, it halts with output `o`
exactly when `d` halts on `p ++ x` with output `o`. -/
theorem Desc.computes_hardwire (d : Desc) (p x : List Bool) (o : List ℕ) :
    (hardwire d p).Computes (x.map eBit) o ↔ d.Computes ((p ++ x).map eBit) o := by
  have hxs : ∀ a ∈ (p ++ x).map eBit, a ≠ marker := by
    intro a ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    cases b <;> simp [marker]
  refine Desc.computes_iff_of_iterate
    (redirectCfg (fun q => 2 * q + 1) (x.length + 1) 0 [] ((p ++ x).map eBit) [] [])
    (fun c => by simp [redirectCfg]) (2 * (p.length + x.length) + 4) (fun t => ?_) o
  rw [add_comm, Function.iterate_add_apply, iterate_prepare]
  exact iterate_stepOut_redirect (n := d.tapes) (fun _ _ h => by omega)
    (find?_redirect_hardwire d p) (by simp [inputSymbol]) hxs rfl rfl
    (fun ts _ was => by simp) t (by simp [init]) (by simp [init]) []

/-- **Halting of `hardwire d p`**: on every input of bits `x`, it halts exactly when `d` halts on
`p ++ x`. -/
theorem Desc.halts_hardwire (d : Desc) (p x : List Bool) :
    (hardwire d p).Halts (x.map eBit) ↔ d.Halts ((p ++ x).map eBit) := by
  simp only [Desc.halts_iff_exists_computes, Desc.computes_hardwire]

end Turing.MultiTapeTM.Universal
