/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeRetain

/-!
# Read-only native backward bucket scanning

Opposite-side bucket hits are recovered by the full backward quarter kernel
and scanned against the retained full-state dictionary until the first hit.
The returned words are a presence tag and a retained witness; no output array is
allocated. This is a component for [WangLvShenZhang2027], Theorem 7,
PDF p. 22. The composed class consumer is executable, but its general
termination/witness theorem and original-input decision endpoint remain open.
Reversed full-width operands and an existing dictionary remain prerequisites.
The sparse WordRAM model does not supply the source's multitape bit-time bound.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

private theorem pointer_bound (D ptr b c M N : ℕ) :
    ptr + 2 ≤ D + ptr + b + c + 8 * M + N + 4 := by omega

private theorem constant_bound (D ptr b c M N : ℕ) :
    1 ≤ D + ptr + b + c + 8 * M + N + 4 := by omega

private theorem slot_bound (D ptr b c M N r : ℕ) (hr : r < M) :
    D + 3 * r + 4 ≤ D + ptr + b + c + 8 * M + N + 4 := by omega

/-- Recover one backward hit and probe its complete state without stores.
The hit witness remains in `firstOperators`; `operators` is restored by the
backward kernel. `operand` and `bits` return the retained encoded witnesses. -/
@[expose] def probeBody : Code .standard 32 :=
  .seq (ram[ address ← link + one; state ← *address; address ← address + one;
    firstOperators ← *address; link ← *link ])
    (.seq backwardEvaluate (.seq (ram[ one ← #1 ]) Dictionary.get))

/-- Exact full backward-state probe on one actual linked node. Every load,
packed reversal, full-width operation and dictionary address is charged.
Neither the answer nor an execution/resource conclusion is a premise. -/
theorem probeBody_exec {W m b ptr D s u v : ℕ} (as : List (BitVec m)) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (hD : x.regs Dictionary.table = D)
    (hone : x.regs one = 1)
    (hs : x.mem (ptr + 1) = s) (hu : x.mem (ptr + 2) = u)
    (hsLt : s < 2 ^ m)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hfit : Fits W (D + ptr + b + as.length + 8 * 2 ^ m + 2 ^ as.length + 4)) :
    let result := (backward ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat
    ∃ y, ExecWithin W probeBody x y (18 * as.length + 33) ∧
      y.mem = x.mem ∧ y.regs state = result ∧
      y.regs firstOperators = u ∧ y.regs operators = v ∧
      y.regs link = x.mem ptr ∧
      y.regs operand = x.mem (Dictionary.slot D result) ∧
      y.regs bits = x.mem (Dictionary.slot D result + 1) ∧ y.regs one = 1 := by
  dsimp only
  have ha2 : Fits W (ptr + 2) :=
    hfit.of_le (pointer_bound D ptr b as.length (2 ^ m) (2 ^ as.length))
  have ha1 : Fits W (ptr + 1) := ha2.of_le (by omega)
  let loaded := x.set address (ptr + 1) |>.set state s |>.set address (ptr + 2)
    |>.set firstOperators u |>.set link (x.mem ptr)
  have heLoad : ExecWithin (B := .standard) W
      (ram[ address ← link + one; state ← *address; address ← address + one;
        firstOperators ← *address; link ← *link ]) x loaded 5 := by
    ram_eval [loaded, hl, hone, hs, hu, ha1, ha2, address, link, one, state,
      firstOperators, Fin.mk.injEq, Nat.add_assoc]
  obtain ⟨z, heEval, zs, zv, zm⟩ := backwardEvaluate_exec as (BitVec.ofNatLT s hsLt) loaded
    (v := v)
    (by simpa +decide [loaded, base, address, state, firstOperators, link] using hb)
    (by simpa +decide [loaded, count, address, state, firstOperators, link] using hc)
    (by simpa +decide [loaded, modulus, address, state, firstOperators, link] using hn)
    (by simp +decide [loaded, state, address, firstOperators, link])
    (by simpa +decide [loaded, operators, address, state, firstOperators, link] using hv) hfv
    hinput (hfit.of_le (by omega))
  have frame (r : Fin 32) (hr : backwardEvaluate.Preserves r) :
      z.regs r = loaded.regs r := heEval.regs_eq hr
  let result := (backward ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat
  have zr : z.regs state = result := by
    simpa only [result, BitVec.ofNatLT_eq_ofNat] using zs
  have zD : z.regs Dictionary.table = D := by
    rw [frame Dictionary.table (by decide)]
    simpa +decide [loaded, Dictionary.table, address, state, firstOperators, link] using hD
  let ready := z.set one 1
  have heOne : ExecWithin (B := .standard) W (ram[ one ← #1 ]) z ready 1 :=
    ExecWithin.const (hfit.of_le
      (constant_bound D ptr b as.length (2 ^ m) (2 ^ as.length)))
  obtain ⟨y, heGet, ym, yt, yw⟩ := Dictionary.get_exec ready
    (by simpa +decide [ready, Dictionary.table, one] using zD)
    (by simpa +decide [ready, state, one] using zr) (by simp [ready])
    (hfit.of_le (slot_bound D ptr b as.length (2 ^ m) (2 ^ as.length) result
      (backward ((decode as.length v).zip as) (BitVec.ofNat m s)).isLt))
  refine ⟨y, (heLoad.seq (heEval.seq (heOne.seq heGet))).mono (by omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ready, Data.set_mem, zm, loaded, Data.set_mem] using ym
  · exact ((heGet.regs_eq (by decide)).trans (heOne.regs_eq (by decide))).trans zr
  · rw [heGet.regs_eq (by decide), heOne.regs_eq (by decide), frame firstOperators (by decide)]
    simp +decide [loaded, firstOperators, link]
  · exact ((heGet.regs_eq (by decide)).trans (heOne.regs_eq (by decide))).trans zv
  · rw [heGet.regs_eq (by decide), heOne.regs_eq (by decide), frame link (by decide)]
    simp [loaded]
  · simpa only [ready, Data.set_mem, zm, loaded, Data.set_mem] using yt
  · simpa only [ready, Data.set_mem, zm, loaded, Data.set_mem] using yw
  · rw [heGet.regs_eq (by decide)]
    simp [ready]

/-- Scan a linked opposite-quarter bucket, stopping at the first present full key.
The presence tag is tested before advancing, so zero witnesses remain valid. -/
@[expose] def probeScanBody : Code .standard 32 :=
  .seq probeBody (.branch (.eq operand zero)
    (ram[ link ← link ]) (ram[ link ← zero ]))

/-- The linked scan allocates no output array and exits on a hit or null link. -/
@[expose] def probeScan : Code .standard 32 :=
  .loop (.lt zero link) probeScanBody

/-- Every actual linked hit is tested unless an earlier full key is present.
The initial tag must be zero, including for an empty bucket. Dictionary
validity is deliberately separate from this exact physical lookup contract. -/
theorem probeScan_witness_exec {W m b boundary ptr D v : ℕ} (as : List (BitVec m))
    (rs : List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (hD : x.regs Dictionary.table = D)
    (hone : x.regs one = 1) (hz : x.regs zero = 0) (htag : x.regs operand = 0)
    (hlinked : Linked x.mem boundary ptr rs)
    (hstates : ∀ r ∈ rs, r.1 < 2 ^ m)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hfit : Fits W (D + boundary + b + as.length + 8 * 2 ^ m + 2 ^ as.length + 4)) :
    ∃ y, ExecWithin W probeScan x y (rs.length * (18 * as.length + 39) + 2) ∧
      y.mem = x.mem ∧ y.regs link = 0 ∧ y.regs one = 1 ∧ y.regs operators = v ∧
      (y.regs operand ≠ 0 ↔ ∃ r ∈ rs, x.mem (Dictionary.slot D
        (backward ((decode as.length v).zip as) (BitVec.ofNat m r.1)).toNat) ≠ 0) ∧
      (y.regs operand ≠ 0 → ∃ r ∈ rs,
        y.regs firstOperators = r.2 ∧ y.regs operators = v ∧
        y.regs state = (backward ((decode as.length v).zip as)
          (BitVec.ofNat m r.1)).toNat ∧
        y.regs operand = x.mem (Dictionary.slot D (y.regs state)) ∧
        y.regs bits = x.mem (Dictionary.slot D (y.regs state) + 1)) := by
  induction rs generalizing x ptr with
  | nil =>
    cases hlinked
    refine ⟨x, ?_, rfl, hl, hone, hv, ?_, ?_⟩
    · simpa only [probeScan, List.length_nil, Nat.zero_mul, Nat.zero_add] using
        (ExecWithin.loop_exit (w := W) (x := x) (cond := .lt zero link)
          (body := probeScanBody) (by simp [Cond.holds_lt, hz, hl]))
    · simp [htag]
    · simp [htag]
  | cons r rs ih =>
    obtain ⟨s, u⟩ := r
    cases hlinked with
    | cons hp hbound hs hu htail =>
      obtain ⟨z, he, zm, zs, zu, zv, zl, ztag, zbits, zone⟩ :=
        probeBody_exec as x hb hc hn hv hfv hl hD hone hs hu
          (hstates _ List.mem_cons_self) hinput (hfit.of_le (by omega))
      have zz : z.regs zero = 0 := (he.regs_eq (by decide)).trans hz
      by_cases hit : z.regs operand = 0
      · let n := z.set link (z.regs link)
        have hnstep : ExecWithin W probeScanBody x n (18 * as.length + 36) :=
          (he.seq (ExecWithin.branch_pos (by simp [Cond.holds_eq, hit, zz])
            (ExecWithin.copy))).mono (by omega)
        have nm : n.mem = x.mem := zm
        have nl : n.regs link = x.mem ptr := by simpa [n] using zl
        have nt : n.regs operand = 0 := by simpa +decide [n, operand, link] using hit
        obtain ⟨y, hy, ym, yl, yo, yv, hiff, hw⟩ := ih n
          ((hnstep.regs_eq (by decide)).trans hb)
          ((hnstep.regs_eq (by decide)).trans hc)
          ((hnstep.regs_eq (by decide)).trans hn)
          (by simpa +decide [n, operators, link] using zv) nl
          ((hnstep.regs_eq (by decide)).trans hD)
          (by simpa +decide [n, one, link] using zone)
          ((hnstep.regs_eq (by decide)).trans hz) nt
          (by simpa only [nm] using htail)
          (fun r hr => hstates r (List.mem_cons_of_mem _ hr))
          (by simpa only [nm] using hinput)
        refine ⟨y, ?_, ym.trans nm, yl, yo, yv, ?_, ?_⟩
        · exact (ExecWithin.loop_iter (cond := .lt zero link) (by simp [Cond.holds_lt, hz, hl, hp])
            hnstep hy).mono (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
        · rw [hiff, nm]
          have hmiss := hit
          rw [ztag] at hmiss
          simp only [List.mem_cons, exists_eq_or_imp]
          simp only [hmiss, ne_eq, not_true_eq_false, false_or]
        · intro hit
          obtain ⟨r, hr, hu, hv, hs, ht, hb⟩ := hw hit
          exact ⟨r, List.mem_cons_of_mem _ hr, hu, hv, hs,
            by simpa only [nm] using ht, by simpa only [nm] using hb⟩
      · let n := z.set link 0
        have hnstep : ExecWithin W probeScanBody x n (18 * as.length + 36) := by
          have hcopy : ExecWithin (B := .standard) W (ram[ link ← zero ]) z n 1 := by
            simpa only [n, zz] using (ExecWithin.copy (B := .standard)
              (w := W) (x := z) (d := link) (s := zero))
          exact (he.seq (ExecWithin.branch_neg
            (by simp [Cond.holds_eq, hit, zz]) hcopy)).mono (by omega)
        refine ⟨n, ?_, zm, by simp [n],
          by simpa +decide [n, one, link] using zone,
          by simpa +decide [n, operators, link] using zv, ?_, ?_⟩
        · exact (ExecWithin.loop_iter (cond := .lt zero link)
            (by simp [Cond.holds_lt, hz, hl, hp]) hnstep
            (ExecWithin.loop_exit (x := n) (cond := .lt zero link)
              (by simp +decide [Cond.holds_lt, n, zero, link]))).mono
            (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
        · have hnTag : n.regs operand ≠ 0 := by
            simpa +decide [n, operand, link] using hit
          refine ⟨fun _ => ⟨(s, u), List.mem_cons_self, ?_⟩, fun _ => hnTag⟩
          rwa [ztag] at hit
        · intro _
          refine ⟨(s, u), List.mem_cons_self, ?_, ?_, ?_, ?_, ?_⟩
          · simpa +decide [n, firstOperators, link] using zu
          · simpa +decide [n, operators, link] using zv
          · simpa +decide [n, state, link] using zs
          · simpa +decide [n, operand, state, link, zs] using ztag
          · simpa +decide [n, bits, state, link, zs] using zbits

/-- Original four-quarter witness soundness for the native linked scan against
an actually filled retained dictionary. The two record lists are constructed
from full original-quarter evaluations, rather than an assumed dictionary
invariant or a supplied decoded-solution claim. The surrounding projected bucket
construction and whole-class iteration are not certified by this theorem. -/
theorem probeScan_original_exec {W m b boundary ptr D v : ℕ}
    (a₁ a₂ a₃ a₄ : List (BitVec m)) (s t : BitVec m)
    (us ws : List ℕ) (v₂ : ℕ) (mem : ℕ → ℕ) (top : ℕ) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = a₃.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (hD : x.regs Dictionary.table = D)
    (hone : x.regs one = 1) (hz : x.regs zero = 0) (htag : x.regs operand = 0)
    (hlinked : Linked x.mem boundary ptr (ws.map fun u =>
      ((backward ((decode a₄.length u).zip a₄) t).toNat, u)))
    (hmem : x.mem = Dictionary.filledMemory D
      (retainedEntries a₂ v₂
        (us.map fun u => ((eval ((decode a₁.length u).zip a₁) s).toNat, u))) mem top)
    (hzero : ∀ q, mem (Dictionary.slot D q) = 0)
    (hinput : ∀ i (hi : i < a₃.reverse.length), x.mem (b + i) = a₃.reverse[i].toNat)
    (hfit : Fits W (D + boundary + b + a₃.length + 8 * 2 ^ m + 2 ^ a₃.length + 4)) :
    ∃ y, ExecWithin W probeScan x y (ws.length * (18 * a₃.length + 39) + 2) ∧
      y.mem = x.mem ∧ y.regs link = 0 ∧
      (y.regs operand ≠ 0 →
        eval (((decode a₁.length (y.regs operand - 1)).zip a₁) ++
          ((decode a₂.length (y.regs bits)).zip a₂) ++
          ((decode a₃.length (y.regs operators)).zip a₃) ++
          ((decode a₄.length (y.regs firstOperators)).zip a₄)) s = t) := by
  obtain ⟨y, he, hm, hl, _, _, _, hw⟩ := probeScan_witness_exec a₃
    (ws.map fun u => ((backward ((decode a₄.length u).zip a₄) t).toNat, u))
    x hb hc hn hv hfv hl hD hone hz htag hlinked
    (by
      intro r hr
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hr
      exact (backward ((decode a₄.length u).zip a₄) t).isLt)
    hinput hfit
  refine ⟨y, by simpa only [List.length_map] using he, hm, hl, ?_⟩
  intro hit
  obtain ⟨r, hr, hu, hv, hs, ht, hb⟩ := hw hit
  obtain ⟨u₄, _, rfl⟩ := List.mem_map.mp hr
  have present : Dictionary.filledMemory D
      (retainedEntries a₂ v₂
        (us.map fun u => ((eval ((decode a₁.length u).zip a₁) s).toNat, u))) mem top
      (Dictionary.slot D (y.regs state)) ≠ 0 := by
    rw [← hmem, ← ht]
    exact hit
  obtain ⟨r, hr, hq, hfirst, hsecond⟩ := retained_provenance D top (y.regs state)
    mem a₂ v₂ (us.map fun u => ((eval ((decode a₁.length u).zip a₁) s).toNat, u)) (hzero _) present
  obtain ⟨u₁, _, rfl⟩ := List.mem_map.mp hr
  have htag : y.regs operand = u₁ + 1 := ht.trans (by simpa only [hmem] using hfirst)
  have hbits : y.regs bits = v₂ := hb.trans (by simpa only [hmem] using hsecond)
  have meet : eval ((decode a₂.length v₂).zip a₂) (eval ((decode a₁.length u₁).zip a₁) s) =
      backward ((decode a₃.length v).zip a₃)
        (backward ((decode a₄.length u₄).zip a₄) t) := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hq.trans hs
  rw [htag, Nat.add_sub_cancel, hbits, hv, hu]
  simp only [eval_append] at meet ⊢
  rw [meet, eval_backward, eval_backward]

/-- Membership-only form of `probeScan_witness_exec`. -/
theorem probeScan_exec {W m b boundary ptr D v : ℕ} (as : List (BitVec m))
    (rs : List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (hD : x.regs Dictionary.table = D)
    (hone : x.regs one = 1) (hz : x.regs zero = 0) (htag : x.regs operand = 0)
    (hlinked : Linked x.mem boundary ptr rs)
    (hstates : ∀ r ∈ rs, r.1 < 2 ^ m)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hfit : Fits W (D + boundary + b + as.length + 8 * 2 ^ m + 2 ^ as.length + 4)) :
    ∃ y, ExecWithin W probeScan x y (rs.length * (18 * as.length + 39) + 2) ∧
      y.mem = x.mem ∧ y.regs link = 0 ∧
      (y.regs operand ≠ 0 ↔ ∃ r ∈ rs, x.mem (Dictionary.slot D
        (backward ((decode as.length v).zip as) (BitVec.ofNat m r.1)).toNat) ≠ 0) := by
  obtain ⟨y, he, hm, hl, _, _, hit, _⟩ := probeScan_witness_exec as rs x
    hb hc hn hv hfv hl hD hone hz htag hlinked hstates hinput hfit
  exact ⟨y, he, hm, hl, hit⟩

/-- Reversed full-width operand base, preserved while filtering projected states. -/
abbrev fullBase : Fin 32 := 24
/-- Forward-order projected operand base. -/
abbrev projectedBase : Fin 32 := 29
/-- Projected state modulus. -/
abbrev projectedModulus : Fin 32 := 30
/-- Full state modulus. -/
abbrev fullModulus : Fin 32 := 31

/-- One opposite-class iteration. Exchanging forward/backward in Lemma 8
means applying the projected second quarter *forward* from the class value
`initial`, then reading that bucket of backward first-quarter records.
The full inverse is evaluated only on those records. `count` is common to the
projected and full arrays; the projected array is forward-order and the full
array is reversed. -/
@[expose] def probeClassBody : Code .standard 32 :=
  .seq (ram[ base ← projectedBase; modulus ← projectedModulus; state ← initial ])
    (.seq evaluate
      (.seq (ram[ address ← heads + state; link ← *address;
        base ← fullBase; modulus ← fullModulus; operand ← #0 ])
        (.seq probeScan (.branch (.eq operand zero)
          (ram[ operators ← operators + one ]) (ram[ stop ← operators ])))))

/-- Stream the entire opposite class, retaining no output array. On success
`operators` and `firstOperators` identify the current opposite-side quarters;
`operand` and `bits` hold the retained side's encoded witnesses. On exhaustion
`operand` is zero. `stop` initially holds the number of packed quarter words;
a hit lowers it to the current index to exit without destroying that witness.
Prepared buckets, projected/reversed arrays and retained dictionary are inputs,
so this is not yet an original-input decision or a global resource theorem. -/
@[expose] def probeClass : Code .standard 32 :=
  .seq (ram[ operators ← #0; operand ← #0; zero ← #0; one ← #1 ])
    (.loop (.lt operators stop) probeClassBody)

/-- Streaming across all packed indices performs no stores, including on early
exit. This is a syntactic property of the complete composed consumer. -/
theorem probeClass_no_store (a v : Fin 32) :
    Instr.op (Op.store a v) ∉ probeClass.program state := by
  simp [Code.program, Code.assemble, probeClass, probeClassBody, probeScan,
    probeScanBody, probeBody, backwardEvaluate, reverseOperators, reverseBody,
    evaluate, body, operation, Dictionary.get, Op.bin]

/-- Every continuing prefix of the class consumer preserves memory, rather
than merely restoring it at termination. Thus it allocates no opposite list. -/
theorem probeClass_prefix_memory {W k : ℕ} (x : Data 32) (u : State 32)
    (h : Runs W (probeClass.program state) ⟨0, x⟩ u k) : u.data.mem = x.mem :=
  h.mem_eq_of_no_store probeClass_no_store

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
