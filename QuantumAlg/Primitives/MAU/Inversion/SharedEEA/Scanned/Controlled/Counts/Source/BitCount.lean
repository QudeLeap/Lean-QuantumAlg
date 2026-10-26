/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Concrete
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.PortProgram
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.PortProgram
import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Unloading
import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Packing

/-!
# Numerical population counts of the actual fixed physical port masks

Population-count invariance under the actual terminal reversal avoids
expanding its width-256 recursive bitvector representation. The real
load and unload mask definitions remain the only constants counted.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open EncodedBit

/-- Exact number of set bits in the given public fixed width. -/
def bitCount (width constant : Nat) : Nat :=
  ∑ index ∈ Finset.range width, (constant.testBit index).toNat

private lemma filter_length {Index : Type} (indices : List Index) (predicate : Index → Bool) :
    (indices.filter predicate).length = (indices.map fun index => (predicate index).toNat).sum := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      cases value : predicate index <;> simp [value, inductionHypothesis, Nat.add_comm]

/-- The actual filtered physical mask has the same exact numerical population count. -/
lemma constantOneIndices_bitCount (width : Nat) (constant : Fin (2 ^ width)) :
    (Word.constantOneIndices constant).length = bitCount width constant.val := by
  rw [Word.constantOneIndices, filter_length, List.map_ofFn, Fin.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun index => (constant.val.testBit index).toNat) width

private lemma cpopNatRec_sum {width : Nat} (word : BitVec width) (count : Nat) :
    word.cpopNatRec count 0 =
      ∑ index ∈ Finset.range count, (word.getLsbD index).toNat := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq, inductionHypothesis,
        Finset.sum_range_succ, Nat.zero_add]

/-- The numerical count equals the standard bitvector population count without changing bits. -/
lemma bitCount_cpop {width : Nat} (word : BitVec width) :
    bitCount width word.toNat = word.cpop.toNat := by
  rw [BitVec.toNat_cpop, cpopNatRec_sum]
  rfl

private lemma bitCount_add (left right constant : Nat) :
    bitCount (left + right) constant = bitCount left constant +
      ∑ index ∈ Finset.range right, (constant.testBit (left + index)).toNat := by
  rw [bitCount, Finset.sum_range_add]
  rfl

private lemma ofNatLT_population (width value : Nat) (fits : value < 2 ^ width) :
    (BitVec.ofNatLT value fits).cpop.toNat = bitCount width value :=
  (bitCount_cpop (BitVec.ofNatLT value fits)).symm

private lemma block_sum (value : Nat → Nat) (width blocks : Nat) :
    (∑ index ∈ Finset.range (width * blocks), value index) =
      ∑ block ∈ Finset.range blocks,
        ∑ index ∈ Finset.range width, value (width * block + index) := by
  induction blocks with
  | zero => simp
  | succ blocks inductionHypothesis =>
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, inductionHypothesis]

private abbrev p256 := EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus

private lemma p256_population : bitCount 256 p256 = 129 := by
  unfold p256
  rw [EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus_eq_standard]
  rw [bitCount, block_sum _ 32 8]
  decide

/-- The actual initial mask contains precisely the selected main-word constant bits. -/
lemma p256_load_mask_population :
    (Word.constantOneIndices (InitialPortProgram.constant p256)).length = 127 := by
  rw [constantOneIndices_bitCount]
  have value : (InitialPortProgram.constant p256).val =
      578960446159621030456981386984159204943166082077852570353363967340519616413688 := by
    change (InitialPortProgram.mask p256).toNat = _
    simp only [InitialPortProgram.mask, NumberTheory.SharedEEA.WordUnloading.mainMask,
      NumberTheory.SharedEEA.PaddingClock.main, InitialPortProgram.initialWord,
      BitVec.toNat_append, BitVec.extractLsb', BitVec.toNat_ofNat]
    have size : p256.size = 256 := p256_size
    rw [size]
    unfold p256
    rw [EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus_eq_standard]
    have capacity258 : 2 ^ 258 =
        463168356949264781694283940034751631413079938662562256157830336031652518559744 := by
      calc
        2 ^ 258 = 2 ^ 256 * 2 ^ 2 := split_power 2 258 256 2 rfl
        _ = _ := by norm_num
    simp only [Nat.reduceAdd, p256_work_capacity, capacity258]
    decide
  rw [value]
  have size : p256.size = 256 := p256_size
  rw [size, bitCount_add 256 3, bitCount, block_sum _ 32 8]
  decide

/-- The actual terminal mask contains every reversed modulus bit and the final fixed one. -/
lemma p256_unload_mask_population :
    (Word.constantOneIndices (OutputPortProgram.constant p256)).length = 130 := by
  rw [constantOneIndices_bitCount]
  change bitCount (p256.size + 3)
    (NumberTheory.SharedEEA.TerminalPadding.terminalWord p256).toNat = 130
  rw [bitCount_cpop]
  simp only [NumberTheory.SharedEEA.TerminalPadding.terminalWord,
    NumberTheory.SharedEEA.TerminalPadding.terminalPayload,
    NumberTheory.SharedEEA.WordPacking.packWork2, BitVec.toNat_cpop_append,
    BitVec.cpop_reverse]
  rw [ofNatLT_population]
  have size : p256.size = 256 := p256_size
  rw [size, p256_population]
  decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts
