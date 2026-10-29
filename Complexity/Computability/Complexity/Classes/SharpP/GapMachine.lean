/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Characterization
public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Alternative
public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Verdict

/-!
# The native counting-machine characterization of GapP

Successful witnesses contribute one chosen-sign leaf, and unsuccessful witnesses contribute
a balanced accepting/rejecting pair. An actual two-occurrence selector combines independently
sized witness families. No extra coin pads a halted computation. The resulting native gap is
the difference of the two verifier counts, including odd, negative and zero values.

All machine parameters and the polynomial clock are fixed before the encoded input. Preparation,
framing, buffering, verification and routing are actual native machine work. Halting is asserted
on the encoding's image, and `encBits` specializes this to all binary inputs.

## Main results

* `Turing.MultiTapeCTM.exists_signed_verifier_machine`: exact counts after balanced routing.
* `Turing.MultiTapeCTM.exists_verifier_difference_machine`: combine unequal witness lengths.
* `Cslib.Complexity.mem_GapP_iff_exists_machine`: the bidirectional native GapP characterization.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The concrete verifier construction and native calculus credits are preserved in
`MultiTape.Counting.Verifier`; the certified forward checker is in `Classes.SharpP.Machine`.
-/

@[expose] public section

open Cslib Turing Turing.MultiTapeTM Turing.MultiTapeMachine Polynomial

namespace Turing.MultiTapeCTM

variable {α : Type}

/-- A verifier with `N = 2 ^ p(n)` witnesses and `f` successes has routed counts `(N, N-f)`
for the positive sign and `(N-f, N)` for the negative sign. Routing and buffering are charged. -/
theorem exists_signed_verifier_machine (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (verifier : α × List Bool → Bool)
    (hverify : ComputableInPolyTime verifier (encPair enc encBits) encBool) (sign : Bool) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
      (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
        machine.HaltsWithin (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ∧
        machine.acceptCount (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) =
          (if sign then 2 ^ p.eval (enc a).length else
            2 ^ p.eval (enc a).length - Complexity.acceptCount verifier a (p.eval (enc a).length)) ∧
        machine.rejectCount (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) =
          (if sign then
            2 ^ p.eval (enc a).length - Complexity.acceptCount verifier a (p.eval (enc a).length)
            else 2 ^ p.eval (enc a).length) := by
  obtain ⟨k, State, hfinite, source, sourceClock, hnon, hm⟩ :=
    exists_verifier_machine enc p verifier hverify
  let machine := (verdictMachine sign).comp source true
  let clock := sourceClock + (sourceClock + 4 + 1)
  refine ⟨_, _, inferInstance, machine, clock, hnon.comp (VerdictMachine.nonblocking sign) true,
    fun a => ?_⟩
  have hhalt : source.HaltsWithin (sourceClock.eval (enc a).length)
      (Cfg.init source.initial (enc a)) := (hm a).1
  have hp : ((source.runList (sourceClock.eval (enc a).length)
      (Cfg.init source.initial (enc a))).map Cfg.output).Perm
      ((BitString.enumList (p.eval (enc a).length)).map
        (fun word => encBool (verifier (a, word)))) := (hm a).2
  have hbool : ∀ result ∈ source.runList (sourceClock.eval (enc a).length)
      (Cfg.init source.initial (enc a)), ∃ bit, result.output = encBool bit := by
    intro result hresult
    have hout := hp.mem_iff.mp (List.mem_map.mpr ⟨result, hresult, rfl⟩)
    obtain ⟨word, _, hword⟩ := List.mem_map.mp hout
    exact ⟨verifier (a, word), hword.symm⟩
  have hlength : (source.runList (sourceClock.eval (enc a).length)
      (Cfg.init source.initial (enc a))).length = 2 ^ p.eval (enc a).length := by
    simpa using hp.length_eq
  have hreject : source.rejectCount (sourceClock.eval (enc a).length)
      (Cfg.init source.initial (enc a)) =
      2 ^ p.eval (enc a).length - Complexity.acceptCount verifier a (p.eval (enc a).length) := by
    rw [rejectCount, hhalt.branchCount_eq_countP (fun out => !(out == [true]))]
    have hc := hp.countP_eq (fun out => !(out == [true]))
    simp only [List.countP_map, Function.comp_def] at hc
    rw [hc]
    have he := BitString.countP_enumList (p.eval (enc a).length)
      (fun word => !(encBool (verifier (a, word)) == [true]))
    have hn := Complexity.acceptCount_add_card_filter_eq_false
      (V := verifier) (a := a) (n := p.eval (enc a).length)
    rw [he]
    simpa [encBool_apply] using (show
      (Finset.univ.filter fun word : BitString (p.eval (enc a).length) =>
        verifier (a, List.ofFn word) = false).card =
      2 ^ p.eval (enc a).length - Complexity.acceptCount verifier a (p.eval (enc a).length) by lia)
  have hclock : clock.eval (enc a).length =
      sourceClock.eval (enc a).length + (sourceClock.eval (enc a).length + 4 + 1) := by
    simp [clock]
  refine ⟨?_, ?_, ?_⟩
  · rw [hclock]
    exact HaltsWithin.comp source (verdictMachine sign) hnon (VerdictMachine.nonblocking sign)
      true (enc a) _ 1 hhalt (fun result _ => VerdictMachine.haltsWithin sign result.output)
  · have hc := VerdictMachine.branchCount_comp source hnon (enc a) _ hhalt hbool sign true
    rw [hlength, hreject] at hc
    simpa [machine, hclock, acceptCount, initialConfig] using hc
  · have hc := VerdictMachine.branchCount_comp source hnon (enc a) _ hhalt hbool sign false
    rw [hlength, hreject] at hc
    cases sign <;> simpa [machine, hclock, rejectCount, initialConfig] using hc

/-- One native selector combines separately prepared verifier families with their original
witness lengths. Its signed difference is exact; halted branches acquire no padding choices. -/
theorem exists_verifier_difference_machine (enc : α ↪ List Bool) (p q : Polynomial ℕ)
    (positive negative : α × List Bool → Bool)
    (hpositive : ComputableInPolyTime positive (encPair enc encBits) encBool)
    (hnegative : ComputableInPolyTime negative (encPair enc encBits) encBool) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
      (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
        machine.HaltsWithin (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ∧
        (machine.acceptCount (clock.eval (enc a).length)
            (Cfg.init machine.initial (enc a)) : ℤ) -
          machine.rejectCount (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) =
          (Complexity.acceptCount positive a (p.eval (enc a).length) : ℤ) -
            Complexity.acceptCount negative a (q.eval (enc a).length) := by
  obtain ⟨kp, Sp, hfinitep, mp, tp, hnonp, hp⟩ :=
    exists_signed_verifier_machine enc p positive hpositive true
  obtain ⟨kn, Sn, hfiniten, mn, tn, hnonn, hn⟩ :=
    exists_signed_verifier_machine enc q negative hnegative false
  let left : MultiTapeCTM (kp + kn) Bool Sp := mp.extendTapes (Fin.castAddEmb kn)
  let right : MultiTapeCTM (kp + kn) Bool Sn := mn.extendTapes (Fin.natAddEmb kp)
  let machine := alternative left right
  let clock := tp + tn + 1
  have hleft : left.Nonblocking := hnonp.extendTapes _
  have hright : right.Nonblocking := hnonn.extendTapes _
  refine ⟨kp + kn, _, inferInstance, machine, clock, hleft.alternative hright, fun a => ?_⟩
  have hclock : clock.eval (enc a).length = tp.eval (enc a).length + tn.eval (enc a).length + 1 :=
    by simp [clock]
  have hpl : left.HaltsWithin (tp.eval (enc a).length) (Cfg.init left.initial (enc a)) :=
    HaltsWithin.extendTapes hnonp _ (enc a) _ (hp a).1
  have hnl : right.HaltsWithin (tn.eval (enc a).length) (Cfg.init right.initial (enc a)) :=
    HaltsWithin.extendTapes hnonn _ (enc a) _ (hn a).1
  have hcounts (verdict : List Bool → Bool) :
      machine.branchCount verdict (clock.eval (enc a).length)
          (Cfg.init machine.initial (enc a)) =
        mp.branchCount verdict (tp.eval (enc a).length) (Cfg.init mp.initial (enc a)) +
          mn.branchCount verdict (tn.eval (enc a).length) (Cfg.init mn.initial (enc a)) := by
    rw [hclock]
    change (alternative left right).branchCount verdict _
      (Cfg.init (alternative left right).initial (enc a)) = _
    rw [branchCount_alternative]
    have hpe : left.branchCount verdict (tp.eval (enc a).length + tn.eval (enc a).length)
        (Cfg.init left.initial (enc a)) =
        mp.branchCount verdict (tp.eval (enc a).length + tn.eval (enc a).length)
          (Cfg.init mp.initial (enc a)) := branchCount_extendTapes mp _ (enc a) _ verdict
    have hne : right.branchCount verdict (tp.eval (enc a).length + tn.eval (enc a).length)
        (Cfg.init right.initial (enc a)) =
        mn.branchCount verdict (tp.eval (enc a).length + tn.eval (enc a).length)
          (Cfg.init mn.initial (enc a)) := branchCount_extendTapes mn _ (enc a) _ verdict
    rw [hpe, hne, (hp a).1.branchCount_eq (by lia) verdict,
      (hn a).1.branchCount_eq (by lia) verdict]
  refine ⟨?_, ?_⟩
  · rw [hclock]
    exact HaltsWithin.alternative hleft hright _ (enc a)
      (hpl.mono (by lia)) (hnl.mono (by lia))
  · have ha := hcounts (· == [true])
    have hr := hcounts (fun out => !(out == [true]))
    change machine.acceptCount _ _ = mp.acceptCount _ _ + mn.acceptCount _ _ at ha
    change machine.rejectCount _ _ = mp.rejectCount _ _ + mn.rejectCount _ _ at hr
    rw [ha, hr, (hp a).2.1, (hp a).2.2, (hn a).2.1, (hn a).2.2]
    have hple := Complexity.acceptCount_le_two_pow (V := positive) (a := a)
      (n := p.eval (enc a).length)
    have hnle := Complexity.acceptCount_le_two_pow (V := negative) (a := a)
      (n := q.eval (enc a).length)
    simp only [↓reduceIte, Bool.false_eq_true]
    lia

end Turing.MultiTapeCTM

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {g : α → ℤ}

/-- The verifier definition of GapP equals the accepting-minus-rejecting count of one fixed
finite native machine with a polynomial all-branches clock in encoded input length. The
construction has a globally nonblocking table and requires no input-dependent machine advice. -/
theorem mem_GapP_iff_exists_machine :
    g ∈ GapP enc ↔
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
        (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
          machine.HaltsWithin (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ∧
          (machine.acceptCount (clock.eval (enc a).length)
              (Cfg.init machine.initial (enc a)) : ℤ) -
            machine.rejectCount (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) =
            g a := by
  constructor
  · rintro ⟨f₁, ⟨p, positive, hpositive, hf₁⟩, f₂, ⟨q, negative, hnegative, hf₂⟩, hg⟩
    obtain ⟨k, State, hfinite, machine, clock, hnon, hm⟩ :=
      MultiTapeCTM.exists_verifier_difference_machine enc p q positive negative hpositive
        hnegative
    refine ⟨k, State, hfinite, machine, clock, hnon, fun a => ⟨(hm a).1, ?_⟩⟩
    rw [(hm a).2, hg a, hf₁ a, hf₂ a]
  · rintro ⟨k, State, hfinite, machine, clock, _, hm⟩
    have heq : g = fun a => (machine.acceptCount (clock.eval (enc a).length)
        (Cfg.init machine.initial (enc a)) : ℤ) - machine.rejectCount (clock.eval (enc a).length)
          (Cfg.init machine.initial (enc a)) := funext fun a => (hm a).2.symm
    rw [heq]
    exact machine.gapCount_mem_GapP enc clock

end Cslib.Complexity
