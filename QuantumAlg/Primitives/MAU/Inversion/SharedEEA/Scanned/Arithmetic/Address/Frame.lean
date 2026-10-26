/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Readout
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Subword

/-!
# Actual address arithmetic retaining the separate conjunction

The low ordered subwords of the complete geometry operands use the
original address and one original prefix padding bit. The conjunction
is outside this actual native arithmetic target, so it remains
available for the following streaming traversal on every finite label.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The same actual operands with their first, high position omitted by static placement. -/
def placement (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field) :
    Addition.TTK.WordPlacement (encoding width) (ScanMetadata.addressWidth width) :=
  (ArithmeticGeometry.placement width positive field).subword Fin.succ
    (Fin.succ_injective (ScanMetadata.addressWidth width))

/-- Every actual target bit is the original address bit at that ordered position. -/
lemma target_bit (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (index : Fin (ScanMetadata.addressWidth width)) :
    (placement width positive field).target.bit index = addressBit width index := by
  change (ArithmeticGeometry.target width).bit index.succ = _
  simp only [ArithmeticGeometry.target, Fin.val_succ, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, dite_false, Nat.add_sub_cancel]

/-- The complete original metadata value includes its real existing high padding bit. -/
def sourceValue (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (state : Data width) : BitVec (ScanMetadata.addressWidth width) :=
  BitVec.cons ((prefixBit width ⟨1, by
    have sizePositive := Nat.size_pos.mpr positive
    unfold ScanMetadata.addressWidth
    omega⟩).get state) (ArithmeticGeometry.fieldValue field state)

/-- The original address is read without losing or introducing a physical bit. -/
lemma target_get (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (state : Data width) (index : Fin (ScanMetadata.addressWidth width)) :
    ((placement width positive field).target.bit index).get state =
      state.2.1.getMsbD index.val := by
  rw [target_bit, addressBit_get]

/-- All metadata and the actual padding bit occur in the original most-significant-first order. -/
lemma source_get (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (state : Data width) (index : Fin (ScanMetadata.addressWidth width)) :
    ((placement width positive field).addend.bit index).get state =
      (sourceValue width positive field state).getMsbD index.val := by
  have actual := ArithmeticGeometry.source_get width positive field state index.succ
  change ((placement width positive field).addend.bit index).get state = _ at actual
  simpa only [ArithmeticGeometry.sourceValue, Fin.val_succ,
    BitVec.getMsbD_cons_succ, sourceValue] using actual

/-- Execute the actual rescheduled native TTK body on these declared original wires. -/
def program (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement width positive field).program

/-- Independent finite modular addition and its entire retained physical complement. -/
def step (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field) :
    Data width → Data width :=
  (placement width positive field).step

/-- Actual coherent semantics hold with arbitrary finite source fields and arbitrary padding. -/
lemma program_realizes (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width positive field) environment
      (step width positive field) :=
  (placement width positive field).program_realizes environment

/-- The entire original address receives the full padded metadata sum modulo its actual width. -/
lemma step_address (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (state : Data width) :
    (step width positive field state).2.1 = sourceValue width positive field state + state.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := (placement width positive field).step_target_get state
    (sourceValue width positive field state) state.2.1
    (source_get width positive field state) (target_get width positive field state)
    ⟨index, within⟩
  rw [target_bit, addressBit_get] at actual
  exact actual

/-- Every actual physical position outside the address survives this same native operation. -/
lemma step_observed (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (state : Data width) (observed : EncodedBit (encoding width))
    (outside : ∀ index, (addressBit width index).wire ≠ observed.wire) :
    observed.get (step width positive field state) = observed.get state := by
  apply (placement width positive field).step_get_of_target_ne state observed
  intro index
  rw [target_bit]
  exact outside index

/-- All original payload, metadata and phase fields remain unchanged on every finite label. -/
lemma step_source (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (state : Data width) : (step width positive field state).1 = state.1 := by
  apply Registers.eq_of_bit_get_eq
  intro observed
  exact step_observed width positive field state (sourceBit width observed)
    (fun index => (source_address_ne width observed index).symm)

/-- The complete prefix and the separate conjunction retain their actual initial values. -/
lemma step_workspace (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (state : Data width) : (step width positive field state).2.2 = state.2.2 := by
  apply Prod.ext
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    exact (prefixBit_get width ⟨index, within⟩ _).symm.trans
      ((step_observed width positive field state (prefixBit width ⟨index, within⟩)
        (fun other => address_prefix_ne width other ⟨index, within⟩)).trans
        (prefixBit_get width ⟨index, within⟩ state))
  · exact step_observed width positive field state (conjunctionBit width)
      (fun index => address_conjunction_ne width index)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
