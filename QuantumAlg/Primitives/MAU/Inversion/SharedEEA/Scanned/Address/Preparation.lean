/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Addition.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.PrefixAddition
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Phase

/-!
# Coherent preparation of the complete metadata address

The actual program copies the full coefficient, adds the full quotient,
prepares the phase correction in the existing prefix word, adds that word,
and clears its preparation. Both source words retain their carry position.
Clean address and prefix premises are discharged at the real scan boundary;
the full source frame and separate conjunction remain unchanged.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressPreparation

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Compose the five paid native components without allocating any additional system. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (AddressCopy.program width).seq ((AddressAddition.program width).seq
    ((AddressPhase.program width).seq ((PrefixAddition.program width).seq
      (AddressPhase.program width))))

/-- Complete finite action of the same five actual native components. -/
def step (width : Nat) (state : Data width) : Data width :=
  AddressPhase.step width (PrefixAddition.step width
    (AddressPhase.step width (AddressAddition.step width (AddressCopy.step width state))))

/-- The whole coherent preparation follows from the certified actual components. -/
lemma program_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment (step width) :=
  (AddressCopy.program_realizes width environment).seq
    ((AddressAddition.program_realizes width environment).seq
      ((AddressPhase.program_realizes width environment).seq
        (((PrefixAddition.placement width).program_realizes environment).seq
          (AddressPhase.program_realizes width environment))))

/-- The independent full-carry arithmetic formula before using its finite-range certificate. -/
def value (width : Nat) (state : Registers width) : BitVec (ScanMetadata.addressWidth width) :=
  (if state.flags.first then 0#(ScanMetadata.addressWidth width)
    else 1#(ScanMetadata.addressWidth width)) +
    (BitVec.cons false state.quotientLength + BitVec.cons false state.coefficientLength)

/-- No high carry is lost for any complete finite source metadata label. -/
lemma value_eq_address (width : Nat) (state : Registers width) :
    value width state =
      ScanMetadata.address state.coefficientLength state.quotientLength state.flags.first := by
  apply BitVec.eq_of_toNat_eq
  rw [ScanMetadata.address_toNat]
  have totalBound : state.coefficientLength.toNat + state.quotientLength.toNat + 1 <
      2 ^ ScanMetadata.addressWidth width := by
    simpa only [ScanMetadata.position, Bool.false_eq_true, if_false] using
      (ScanMetadata.position_lt (width := width) state.coefficientLength
        state.quotientLength false)
  have positive : 0 < ScanMetadata.addressWidth width := by
    unfold ScanMetadata.addressWidth
    omega
  have sumBound : state.quotientLength.toNat + state.coefficientLength.toNat <
      2 ^ ScanMetadata.addressWidth width := by
    omega
  unfold value ScanMetadata.position
  cases chosen : state.flags.first
  · simp only [Bool.false_eq_true, if_false, BitVec.toNat_add, BitVec.toNat_one positive,
      BitVec.toNat_cons', Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_add]
    rw [Nat.mod_eq_of_lt sumBound]
    have reorderedBound : 1 + (state.quotientLength.toNat + state.coefficientLength.toNat) <
        2 ^ ScanMetadata.addressWidth width := by omega
    rw [Nat.mod_eq_of_lt reorderedBound]
    omega
  · simp only [if_true, BitVec.zero_add, BitVec.toNat_add, BitVec.toNat_cons',
      Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_add]
    rw [Nat.mod_eq_of_lt sumBound]
    omega

/-- A genuinely clean pool produces the exact original full metadata address and restores prefix. -/
lemma step_clean (width : Nat) (state : Data width)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (prefixZero : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    step width state = (state.1,
      (ScanMetadata.address state.1.coefficientLength state.1.quotientLength state.1.flags.first,
        (0#(ScanMetadata.addressWidth width), state.2.2.2))) := by
  rw [← value_eq_address]
  simp only [step, AddressPhase.step_eq, PrefixAddition.step_eq, AddressAddition.step_eq,
    AddressCopy.step, AddressCopy.value, AddressAddition.value, AddressCopy.padding,
    prefixBit_get, addressZero, prefixZero, BitVec.getMsbD_zero, BitVec.zero_xor]
  cases chosen : state.1.flags.first <;>
    simp [chosen, value, BitVec.xor_self]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressPreparation
