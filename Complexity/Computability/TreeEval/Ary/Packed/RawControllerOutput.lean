/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerNative
public import Complexity.Computability.TreeEval.Ary.Packed
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit

/-!
# Native decoding of a raw packed register

The value width, chunk width, modulus, chunk count and target register are runtime binary
naturals. A storage guard bounds the output length by the actual padded bank encoding before
any output loop runs. Decoding reads binary digits directly; it never constructs `2^m`.
The semantic statements distinguish decoding a register from obtaining the root value: the
latter requires that the masking procedure started with a zero target and coefficient one.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController.Output

open Turing MultiTapeTM ComputableInSpace Cslib.BitString

/-- Value width, chunk width, modulus, chunk count, target and the physical bank. -/
abbrev Args := (ℕ × ℕ × ℕ × ℕ × ℕ) × List ℕ

/-- Every parameter is binary; the bank retains the raw controller's framed cell encoding. -/
abbrev encArgs : Args ↪ List Bool :=
  encPair (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
    (encList encNat)

/-- Check output capacity and field-width payment using the actual input bank. No exponential
is computed, including on rejected inputs. -/
@[expose] def valid (q : Args) : Bool :=
  let ((b, m, p, r, _), bank) := q
  decide (0 < m) && decide (m ≤ p.size) && decide (b ≤ r * m) &&
    decide (r ≤ bank.length) && bank.all (fun v => decide (p ≤ v))

/-- One bit of the selected register, reduced in the runtime field before digit access. -/
@[expose] def bit (q : Args) (j : ℕ) : Bool :=
  let ((_, m, p, r, target), bank) := q
  (bank.getD (target * r + j / m) 0 % p).testBit (j % m)

private def count (q : Args) : ℕ := if valid q then q.1.1 else 0

private abbrev Work := Args × ℕ × List Bool
private abbrev encWork : Work ↪ List Bool :=
  encPair encArgs (encPair encNat (encList encBool))

private def step (s : Work) : Work := (s.1, s.2.1 + 1, s.2.2 ++ [bit s.1 s.2.1])

/-- Rejected inputs return the empty word. Accepted inputs stream exactly `b` output bits. -/
@[expose] def decode (q : Args) : List Bool :=
  if valid q then List.ofFn (fun j : Fin q.1.1 => bit q j) else []

private theorem iterate_step (q : Args) (j : ℕ) (out : List Bool) (n : ℕ) :
    step^[n] (q, j, out) =
      (q, j + n, out ++ (List.range n).map (fun i => bit q (j + i))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    congr 2

/-- The executable loop has the ordinary coordinatewise register-decoding semantics. -/
theorem decode_eq (q : Args) (hq : valid q = true) :
    decode q = List.ofFn (fun j : Fin q.1.1 => bit q j) := by
  simp only [decode, hq, ↓reduceIte]

private theorem decode_eq_loop (q : Args) :
    decode q = ((step^[count q]) (q, 0, [])).2.2 := by
  rw [iterate_step]
  by_cases hq : valid q = true
  · simp only [decode, count, hq, ↓reduceIte, Nat.zero_add, List.nil_append]
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  · simp [decode, count, hq]

/-- The guard charges every output bit to the actual encoded padded cells. -/
private theorem count_le_encoding (q : Args) : count q ≤ (encList encNat q.2).length := by
  by_cases h : valid q = true
  · have hs : 0 < q.1.2.1 ∧ q.1.2.1 ≤ q.1.2.2.1.size ∧
        q.1.1 ≤ q.1.2.2.2.1 * q.1.2.1 ∧ q.1.2.2.2.1 ≤ q.2.length ∧
        ∀ v ∈ q.2, q.1.2.2.1 ≤ v := by
      simpa only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] using h
    have hw := padded_width_le_encoding q.1.2.2.1 q.2 hs.2.2.2.2
    rw [length_encNat_eq_size] at hw
    have hm := Nat.mul_le_mul hs.2.2.2.1 hs.2.1
    simp only [count, h, ↓reduceIte]
    exact hs.2.2.1.trans (hm.trans hw)
  · simp [count, h]

private theorem valid_inSpace :
    ComputableInSpace valid encArgs encBool (fun q => (encArgs q).length) := by
  have hpar := fst (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
    (encList encNat)
  have hb := fst' hpar
  have hm := fst' (snd' hpar)
  have hp := fst' (snd' (snd' hpar))
  have hr := fst' (snd' (snd' (snd' hpar)))
  have hbank := snd (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
    (encList encNat)
  have hnot := fun {f : Args → Bool} (h : ComputableInSpace f encArgs encBool
    (fun q => (encArgs q).length)) => budget_finite (encC := encBool) Bool.not h
  have hand := fun {f g : Args → Bool} (hf : ComputableInSpace f encArgs encBool
    (fun q => (encArgs q).length)) (hg : ComputableInSpace g encArgs encBool
    (fun q => (encArgs q).length)) => budget_finite (encC := encBool)
      (fun a : Bool × Bool => a.1 && a.2) (budget_prod hf hg)
  have hpos := hnot (budget_natIsZero hm)
  have hwidth := hnot (budget_natLt (budget_comp_linear natSize hp) hm)
  have hcapacity := hnot (budget_natLt (budget_natMul hr hm) hb)
  have hrows := hnot (budget_natLt (budget_length hbank) hr)
  have hpad := budget_comp_linear bankPadding_inSpace (budget_prod hp hbank)
  refine (hand (hand (hand (hand hpos hwidth) hcapacity) hrows) hpad).of_enc_eq ?_
  intro q
  have hle (a b : ℕ) : (!decide (a < b)) = decide (b ≤ a) := by
    by_cases h : a < b
    · simp [h, show ¬b ≤ a by omega]
    · simp [h, show b ≤ a by omega]
  have hpos' : (!decide (q.1.2.1 = 0)) = decide (0 < q.1.2.1) := by
    by_cases h : q.1.2.1 = 0
    · simp [h]
    · simp [h, Nat.pos_of_ne_zero h]
  simp only [valid, hle, hpos']

private theorem step_inSpace :
    ComputableInSpace step encWork encWork (fun s => (encWork s).length) := by
  have hq := fst encArgs (encPair encNat (encList encBool))
  have hrest := snd encArgs (encPair encNat (encList encBool))
  have hj := fst' hrest
  have hout := snd' hrest
  have hpar := fst' hq
  have hm := fst' (snd' hpar)
  have hp := fst' (snd' (snd' hpar))
  have hr := fst' (snd' (snd' (snd' hpar)))
  have ht := snd' (snd' (snd' (snd' hpar)))
  have hbank := snd' hq
  have hindex := budget_natAdd (budget_natMul ht hr) (budget_natDiv hj hm)
  have hcell := budget_comp_lin getD (linear_mul 8) (budget_prod hbank hindex)
  have hbit := budget_comp_lin natTestBit (linear_mul 32)
    (budget_prod (budget_natMod hcell hp) (budget_natMod hj hm))
  exact (budget_prod hq (budget_prod (budget_natSucc hj) (budget_snoc hout hbit))).of_enc_eq
    fun _ => rfl

/-- Uniform native work space is linear in the actual binary arguments, including the output
word. No finite lookup on banks and no list of bit indices is used by the certificate. -/
theorem decode_inSpace :
    ComputableInSpace decode encArgs (encList encBool) (fun q => (encArgs q).length) := by
  have hb := fst' (fst
    (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
    (encList encNat))
  have hn := budget_ite valid_inSpace hb
    (budget_const (encB := encNat) 0 (.refl _))
  have hid : ComputableInSpace (fun q : Args => q) encArgs encArgs
      (fun q => (encArgs q).length) := of_inO ComputableInDegree.id'.inO_one
  have hinit := budget_prod hid (budget_prod
    (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encList encBool) [] (.refl _)))
  have hstate (q : Args) (i : ℕ) (hi : i ≤ count q) :
      (encWork (step^[i] (q, 0, []))).length ≤ 16 * ((encArgs q).length + 1) := by
    rw [iterate_step]
    have hn := count_le_encoding q
    have hl := length_le_encPair_right
      (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
      (encList encNat) q
    have hc := length_encNat_le_self i
    have hout : (encList encBool ((List.range i).map (fun j => bit q j))).length =
        3 * i := by
      simp [length_encList, List.map_map, Function.comp_def, encBool_apply, Nat.mul_comm]
    simp only [encWork, length_encPair, Nat.zero_add, List.nil_append] at ⊢
    rw [hout]
    simp only [length_encPair] at hl
    omega
  have hloop := ComputableInSpace.iterate (hn.of_enc_eq fun _ => rfl) hinit step_inSpace
    (Q := fun q => 16 * ((encArgs q).length + 1))
    (B := fun q => 16 * ((encArgs q).length + 1)) hstate hstate
  refine (snd' (snd' hloop)).weaken ?_ |>.of_enc_eq ?_
  · refine .of_le_linear 128 128 fun q => ?_
    -- The iteration combinator separately charges only the binary loop bound.
    have hb' := length_encNat_mono (count_le_encoding q)
    have hb'' := length_encNat_le_self (encList encNat q.2).length
    have hl := length_le_encPair_right
      (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
      (encList encNat) q
    change (encList encNat q.2).length ≤ (encArgs q).length at hl
    dsimp only [count] at hb' ⊢
    omega
  · intro q
    exact congrArg (encList encBool) (decode_eq_loop q)

/-- A raw register agrees with the existing unpacking map whenever its reduced cells equal
those chunks. This is a register statement and makes no claim about dirty target contents. -/
theorem bit_eq_unpackBits {b m p r t : ℕ} (hb : b ≤ r * m) (hm : 0 < m)
    (bank : List ℕ) (v : Fin r → Fin (2 ^ m))
    (hbank : ∀ i : Fin r, bank.getD (t * r + i) 0 % p = (v i).val) (j : Fin b) :
    bit ((b, m, p, r, t), bank) j = unpackBits hb v j := by
  have hj : j.val < r * m := j.isLt.trans_le hb
  have hdiv : j.val / m < r := (Nat.div_lt_iff_lt_mul hm).mpr hj
  change (bank.getD (t * r + j.val / m) 0 % p).testBit (j.val % m) = _
  rw [hbank ⟨j.val / m, hdiv⟩]
  change _ = (equivFin m).symm (v ((finProdFinEquiv.symm (Fin.castLE hb j)).1))
    ((finProdFinEquiv.symm (Fin.castLE hb j)).2)
  rw [equivFin_symm_apply]
  rfl

/-- A supplied register containing packed chunks decodes to the original Boolean word. -/
theorem decode_packBits {b m p r t : ℕ} (hb : b ≤ r * m) (hm : 0 < m)
    (bank : List ℕ) (v : Fin b → Bool)
    (hvalid : valid ((b, m, p, r, t), bank) = true)
    (hbank : ∀ i : Fin r, bank.getD (t * r + i) 0 % p = (packBits hb v i).val) :
    decode ((b, m, p, r, t), bank) = List.ofFn v := by
  rw [decode_eq _ hvalid]
  congr 1
  funext j
  rw [bit_eq_unpackBits hb hm bank (packBits hb v) hbank j, unpackBits_packBits]

/-- The canonical physical bank decodes any target that actually contains the packed word. -/
theorem decode_ofRegs {b m p d r : ℕ} [NeZero p] (hb : b ≤ r * m) (hm : 0 < m)
    (halphabet : 2 ^ m ≤ p)
    (S : Ary.State (ZMod p) d r) (t : Fin (d + 1)) (v : Fin b → Bool)
    (htarget : ∀ i, S t i = ((packBits hb v i).val : ZMod p)) :
    decode ((b, m, p, r, t.val), ofRegs S) = List.ofFn v := by
  have hwidth : m ≤ p.size := by
    have hw := Nat.size_le_size halphabet
    rw [Nat.size_pow] at hw
    omega
  have hrows : r ≤ (d + 1) * r := by nlinarith
  have hvalid : valid ((b, m, p, r, t.val), ofRegs S) = true := by
    simp only [valid, hm, hwidth, hb, decide_true, Bool.true_and, length_ofRegs, hrows]
    apply List.all_eq_true.mpr
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    simp
  apply decode_packBits hb hm (ofRegs S) v hvalid
  intro i
  have he := congrFun (congrFun (toRegs_ofRegs S) t) i
  change ((ofRegs S).getD (index r t i) 0 : ZMod p) = S t i at he
  rw [htarget] at he
  have hv := congrArg ZMod.val he
  have hlt := (packBits hb v i).isLt.trans_le halphabet
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, index, Nat.mul_comm r t.val,
    Nat.add_comm i.val (t.val * r)] using hv

/-- After a coefficient-one masking computation with an initially zero target, the actual
padded target decodes to the root word. Other registers may start dirty. The zero-target
hypothesis is essential: a general dirty target stores its mask plus the root encoding. -/
theorem decode_procWith_zero_target {b m p d r height : ℕ} [Fact p.Prime]
    (hb : b ≤ r * m) (hm : 0 < m) (halphabet : 2 ^ m ≤ p)
    (h : Fin (2 ^ m) ↪ ZMod p) (hcast : ∀ a, h a = (a.val : ZMod p))
    (hD : d * r * (Fintype.card (Fin (2 ^ m)) - 1) < Fintype.card (ZMod p) - 1)
    (T : Ary.Tree d b height) (S : Ary.State (ZMod p) d r) (t : Fin (d + 1))
    (hzero : S t = 0) :
    decode ((b, m, p, r, t.val), ofRegs
      (Ary.procWith (fun v i => h (packBits hb v i))
        (gateExtension h (packBits hb) (unpackBits hb)) (units p) T 1 t S)) =
      List.ofFn T.eval := by
  classical
  apply decode_ofRegs hb hm halphabet _ t T.eval
  intro i
  unfold units
  rw [procWith_gateExtension_eq h (packBits hb) (unpackBits hb)
    (unpackBits_packBits hb) hD TreeEval.Iter.nodup_zmodUnits TreeEval.Iter.mem_zmodUnits]
  simp only [Function.update_self, hzero, one_smul, zero_add, hcast]

/-- With the library's selected packed field and chunk parameters, a zero-target masking run
returns a physical register whose native decoder yields exactly the root's Boolean word.
All non-target initial registers may be dirty. This does not construct the run's suppliers. -/
theorem decode_packed_procWith_zero_target {d b height : ℕ} (hd : 0 < d) (hb : 0 < b)
    (T : Ary.Tree d b height)
    (S : Ary.State (ZMod (fieldModulus d b)) d (chunkCount d b))
    (t : Fin (d + 1)) (hzero : S t = 0) :
    letI : Fact (fieldModulus d b).Prime := ⟨fieldModulus_prime d b⟩
    decode ((b, chunkWidth d b, fieldModulus d b, chunkCount d b, t.val), ofRegs
      (Ary.procWith
        (fun v i => alphabetEmbedding hd hb (packBits (le_chunkCount_mul hd hb) v i))
        (gateExtension (alphabetEmbedding hd hb) (packBits (le_chunkCount_mul hd hb))
          (unpackBits (le_chunkCount_mul hd hb)))
        (units (fieldModulus d b)) T 1 t S)) = List.ofFn T.eval := by
  let : Fact (fieldModulus d b).Prime := ⟨fieldModulus_prime d b⟩
  apply decode_procWith_zero_target (le_chunkCount_mul hd hb) (chunkWidth_pos hd hb)
    (alphabetSize_lt hd hb).le (alphabetEmbedding hd hb) (fun _ => rfl) _ T S t hzero
  simpa only [Fintype.card_fin, ZMod.card, gateDegree] using gateDegree_lt d b

end Cslib.TreeEval.Ary.Packed.RawController.Output
