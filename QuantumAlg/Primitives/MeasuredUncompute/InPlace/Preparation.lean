/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Assembly
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.PortProgram
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.RegisterFrame
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Trace

/-!
# Direct fixed preparation for the original in-place division frame

The two already supplied words are X and Y. The actual preparation adds
only the original shared-frame complement: its first n physical positions
are A=0, and every remaining auxiliary bit is the fixed small initial EEA
state [LYL+26, sec_point_add/sec_point_add.tex:45-79].

The prepared value depends only on the modulus. Work1 is not first prepared
as `100,p` and then erased for free. Its initial load is the existing actual
`InitialPortProgram` native X list [LYL+26, sec_EEA/sub_4phase.tex:104-117].
The exact basis assembly below retains both arbitrary input words and all
reference correlations. There is no extra Y bank or hidden allocation.
-/

namespace QuantumAlg.MeasuredUncompute.InPlacePreparation

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- Direct fixed first-word value has zero A and the prescribed three retained tail bits. -/
def firstWord (modulus : Nat) : BitVec (modulus.size + 3) :=
  InitialPortProgram.initialWord modulus ^^^ InitialPortProgram.mask modulus

/-- Only the fixed Work1 value differs from the standalone source initialization. -/
def fixedBit (modulus wire : Nat) : Bool :=
  if wire < modulus.size + 3 then (firstWord modulus).getMsbD wire
  else InputPreparation.fixedBit modulus wire

/-- Prepare the original auxiliary layout directly in A=0 and the fixed small initial state. -/
def preparation (modulus : Nat) :
    BasisPreparation (InputPreparation.auxiliaryLayout modulus.size) where
  value index := finTwoEquiv.symm
    (fixedBit modulus (InputPreparation.auxiliaryPhysicalIndex modulus.size index))

/-- Exact values are attached to the existing auxiliary physical identities. -/
theorem preparation_bit (modulus : Nat)
    (index : Fin (InputPreparation.auxiliaryWidth modulus.size)) :
    finTwoEquiv ((preparation modulus).value index) =
      fixedBit modulus (InputPreparation.auxiliaryPhysicalIndex modulus.size index) :=
  finTwoEquiv.apply_symm_apply _

/-- Every actual A position is prepared as zero, before the separately charged native load. -/
theorem firstWord_large_bit (modulus : Nat) (index : Fin modulus.size) :
    (firstWord modulus).getMsbD index.val = false :=
  InitialPortProgram.inputFrame_large_bit modulus (0 : Fin (2 ^ modulus.size)) index

/-- Every newly allocated auxiliary coordinate in the actual A region is a prepared zero. -/
theorem preparation_large_bit (modulus : Nat)
    (index : Fin (InputPreparation.auxiliaryWidth modulus.size))
    (large : InputPreparation.auxiliaryPhysicalIndex modulus.size index < modulus.size) :
    finTwoEquiv ((preparation modulus).value index) = false := by
  rw [preparation_bit, fixedBit, if_pos (by omega)]
  exact firstWord_large_bit modulus ⟨_, large⟩

private def frame (modulus : Nat)
    (old : (InputPreparation.before modulus.size).register.Index) : Registers modulus.size :=
  InputPreparedFrame.frameEquiv modulus.size
    (InputAssembly.assembly modulus.size ((preparation modulus).value, old))

private theorem frame_auxiliary (modulus : Nat)
    (old : (InputPreparation.before modulus.size).register.Index)
    (bit : EncodedBit (encoding modulus.size))
    (outside : bit.wire.val < InputPreparation.prefixWidth modulus.size ∨
      InputPreparation.prefixWidth modulus.size + modulus.size ≤ bit.wire.val) :
    bit.get (frame modulus old) = fixedBit modulus bit.wire.val := by
  rw [← bit.get_eq, InputPreparedFrame.wireIndex_val]
  change ((encoding modulus.size).encode (InputPreparedFrame.frameEquiv modulus.size
    (InputAssembly.assembly modulus.size ((preparation modulus).value, old)))).val.testBit
      bit.wire.rev.val = _
  rw [InputPreparedFrame.encode_frameEquiv]
  have complete := InputPreparation.complete_width modulus.size
  have bound := bit.wire.isLt
  obtain ⟨index, position⟩ : ∃ index : Fin (InputPreparation.auxiliaryWidth modulus.size),
      InputAssembly.auxiliaryPosition modulus.size index = bit.wire := by
    rcases outside with beforeInput | afterInput
    · refine ⟨⟨bit.wire.val, by unfold InputPreparation.auxiliaryWidth; omega⟩, ?_⟩
      apply Fin.ext
      change (if bit.wire.val < InputPreparation.prefixWidth modulus.size then bit.wire.val
        else modulus.size + bit.wire.val) = bit.wire.val
      rw [if_pos beforeInput]
    · refine ⟨⟨bit.wire.val - modulus.size, by omega⟩, ?_⟩
      apply Fin.ext
      change (if bit.wire.val - modulus.size < InputPreparation.prefixWidth modulus.size
        then bit.wire.val - modulus.size
        else modulus.size + (bit.wire.val - modulus.size)) = bit.wire.val
      rw [if_neg (by omega)]
      omega
  have actual := InputAssembly.basisEquiv_auxiliary modulus.size
    (preparation modulus).value old index
  rw [position, preparation_bit] at actual
  exact actual.trans (congrArg (fixedBit modulus)
    (congrArg (fun wire : Fin (encoding modulus.size).width => wire.val) position))

private theorem frame_input (modulus : Nat)
    (old : (InputPreparation.before modulus.size).register.Index)
    (bit : EncodedBit (encoding modulus.size)) (index : Fin modulus.size)
    (position : bit.wire = InputAssembly.inputPosition modulus.size index) :
    bit.get (frame modulus old) =
      (InputPreparation.inputBasisEquiv modulus.size old).val.testBit index.rev.val := by
  rw [← bit.get_eq, InputPreparedFrame.wireIndex_val]
  change ((encoding modulus.size).encode (InputPreparedFrame.frameEquiv modulus.size
    (InputAssembly.assembly modulus.size ((preparation modulus).value, old)))).val.testBit
      bit.wire.rev.val = _
  rw [InputPreparedFrame.encode_frameEquiv, position]
  exact InputAssembly.basisEquiv_input modulus.size (preparation modulus).value old index

private theorem frame_after_word (modulus : Nat)
    (old : (InputPreparation.before modulus.size).register.Index)
    (bit : EncodedBit (encoding modulus.size)) (afterWord : modulus.size + 3 ≤ bit.wire.val) :
    bit.get (frame modulus old) =
      bit.get (InitialFrame.initial modulus
        (InputPreparation.inputBasisEquiv modulus.size old)) := by
  have original := congrArg bit.get (InputPreparedFrame.preparedFrame_eq_initial modulus old)
  by_cases inInput : InputPreparation.prefixWidth modulus.size ≤ bit.wire.val ∧
      bit.wire.val < InputPreparation.prefixWidth modulus.size + modulus.size
  · let index : Fin modulus.size :=
      ⟨bit.wire.val - InputPreparation.prefixWidth modulus.size, by omega⟩
    have position : bit.wire = InputAssembly.inputPosition modulus.size index := by
      apply Fin.ext
      change bit.wire.val = InputPreparation.prefixWidth modulus.size +
        (bit.wire.val - InputPreparation.prefixWidth modulus.size)
      omega
    exact (frame_input modulus old bit index position).trans
      ((InputPreparedFrame.prepared_get_input modulus old bit index position).symm.trans original)
  · have outside : bit.wire.val < InputPreparation.prefixWidth modulus.size ∨
        InputPreparation.prefixWidth modulus.size + modulus.size ≤ bit.wire.val := by omega
    have actual := frame_auxiliary modulus old bit outside
    rw [fixedBit, if_neg (by omega)] at actual
    exact actual.trans
      ((InputPreparedFrame.prepared_get_auxiliary modulus old bit outside).symm.trans original)

/-- The single-input assembly is the complete required A=0 source frame for every input label. -/
theorem frame_eq_inputFrame (modulus : Nat)
    (old : (InputPreparation.before modulus.size).register.Index) :
    frame modulus old = InitialPortProgram.inputFrame modulus
      (InputPreparation.inputBasisEquiv modulus.size old) := by
  apply Registers.ext_fields
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (modulus.size + 3) := ⟨index, within⟩
    have actual := frame_auxiliary modulus old (firstWordBit modulus.size selected)
      (Or.inl (by
        rw [firstWordBit_wire]
        change index < InputPreparation.prefixWidth modulus.size
        unfold InputPreparation.prefixWidth
        omega))
    rw [firstWordBit_get, firstWordBit_wire, fixedBit, if_pos within] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have same := frame_after_word modulus old (secondWordBit modulus.size ⟨index, within⟩)
      (by rw [secondWordBit_wire]; omega)
    rw [secondWordBit_get, secondWordBit_get] at same
    exact same
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have same := frame_after_word modulus old (coefficientLengthBit modulus.size ⟨index, within⟩)
      (by rw [coefficientLengthBit_wire]; omega)
    rw [coefficientLengthBit_get, coefficientLengthBit_get] at same
    exact same
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have same := frame_after_word modulus old (quotientLengthBit modulus.size ⟨index, within⟩)
      (by rw [quotientLengthBit_wire]; omega)
    rw [quotientLengthBit_get, quotientLengthBit_get] at same
    exact same
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have same := frame_after_word modulus old (divisorLengthBit modulus.size ⟨index, within⟩)
      (by rw [divisorLengthBit_wire]; omega)
    rw [divisorLengthBit_get, divisorLengthBit_get] at same
    exact same
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have same := frame_after_word modulus old (shiftBit modulus.size ⟨index, within⟩)
      (by rw [shiftBit_wire]; omega)
    rw [shiftBit_get, shiftBit_get] at same
    exact same
  · exact frame_after_word modulus old (phase1Bit modulus.size)
      (by rw [phase1Bit_wire]; omega)
  · exact frame_after_word modulus old (phase2Bit modulus.size)
      (by rw [phase2Bit_wire]; omega)
  · exact frame_after_word modulus old (signBit modulus.size)
      (by rw [signBit_wire]; omega)
  · exact frame_after_word modulus old (iterationBit modulus.size)
      (by rw [iterationBit_wire]; omega)
  · exact frame_after_word modulus old (controlBit modulus.size)
      (by rw [controlBit_wire]; omega)

private theorem single_prepared (modulus : Nat)
    (old : (InputPreparation.before modulus.size).register.Index) :
    InputAssembly.basisEquiv modulus.size
        (InputAssembly.assembly modulus.size ((preparation modulus).value, old)) =
      (encoding modulus.size).encode (InitialPortProgram.inputFrame modulus
        (InputPreparation.inputBasisEquiv modulus.size old)) := by
  rw [← InputPreparedFrame.encode_frameEquiv]
  exact congrArg (encoding modulus.size).encode (frame_eq_inputFrame modulus old)

/-- The actual two-word basis assembly gives exactly `(inputFrame p x,y)`, for arbitrary x,y. -/
theorem prepared_input (modulus : Nat)
    (old : (InversePreparation.before modulus.size).register.Index) :
    InverseAssembly.basisEquiv modulus.size
        (InversePreparation.assembly modulus.size ((preparation modulus).value, old)) =
      (OutputCopy.encoding modulus.size).encode
        (InitialPortProgram.inputFrame modulus
          (InversePreparation.inputBasisEquiv modulus.size old).1,
          (InversePreparation.inputBasisEquiv modulus.size old).2) := by
  rw [InverseAssembly.basisEquiv_assembly]
  have source := single_prepared modulus (InverseAssembly.oldInput modulus.size old)
  have input : InputPreparation.inputBasisEquiv modulus.size
      (InverseAssembly.oldInput modulus.size old) =
        (InversePreparation.inputBasisEquiv modulus.size old).1 :=
    (InputPreparation.inputBasisEquiv modulus.size).apply_symm_apply _
  rw [input] at source
  exact congrArg
    (fun value : Fin (2 ^ (encoding modulus.size).width) =>
      prodEquiv (m := (encoding modulus.size).width) (n := modulus.size)
        (value, (InversePreparation.inputBasisEquiv modulus.size old).2)) source

/-- One actual fixed preparation retains the two already existing words in the same layout. -/
def circuit (modulus : Nat) :
    Circuit (InversePreparation.before modulus.size) (InversePreparation.after modulus.size) :=
  .prepare (InversePreparation.before modulus.size) InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) (preparation modulus)

/-- The charged event is the new directly prepared A=0 basis on the actual auxiliary layout. -/
theorem circuit_eventTrace (modulus : Nat) (path : (circuit modulus).Path) :
    (circuit modulus).eventTrace path = [(preparation modulus).event] := rfl

/-- The actual allocation visits exactly the existing two-word input and shared-frame output. -/
theorem circuit_visitedContexts (modulus : Nat) (path : (circuit modulus).Path) :
    (circuit modulus).visitedContexts path =
      [InversePreparation.before modulus.size, InversePreparation.after modulus.size] := rfl

/-- Resident peak includes both supplied words and the entire same allocated auxiliary layout. -/
theorem circuit_resident (modulus : Nat) (path : (circuit modulus).Path) :
    (circuit modulus).peakResidentSpace path = SpacePool.max
      (InversePreparation.before modulus.size).residentSpace
      (InversePreparation.after modulus.size).residentSpace := by
  change SpacePool.max (InversePreparation.before modulus.size).residentSpace
    (SpacePool.max (InversePreparation.after modulus.size).residentSpace 0) = _
  rw [SpacePool.max_zero]

/-- The same complete live register has the owned role; no additional auxiliary bank is present. -/
theorem circuit_auxiliary (modulus : Nat) (path : (circuit modulus).Path) :
    (circuit modulus).peakAuxiliarySpace path = SpacePool.max
      (InversePreparation.before modulus.size).auxiliarySpace
      (InversePreparation.after modulus.size).auxiliarySpace := by
  change SpacePool.max (InversePreparation.before modulus.size).auxiliarySpace
    (SpacePool.max (InversePreparation.after modulus.size).auxiliarySpace 0) = _
  rw [SpacePool.max_zero]

variable {Reference : Register} {H : Type} [Fintype H]

/-- The same full joint tensor includes arbitrary old coherences, not separable input factors. -/
theorem execute_joined_entry (modulus : Nat)
    (state : State (InversePreparation.before modulus.size) Reference H)
    (newRow newColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn :
      (Register.prod (InversePreparation.before modulus.size).register Reference).Index) :
    ((circuit modulus).execute Reference state).quantumMarginal.matrix
      (prepareContextBasisEquiv (InversePreparation.before modulus.size) Reference
        InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
        (InversePreparation.auxiliary_fresh modulus.size)
        (InversePreparation.auxiliary_disjoint modulus.size) (newRow, oldRow))
      (prepareContextBasisEquiv (InversePreparation.before modulus.size) Reference
        InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
        (InversePreparation.auxiliary_fresh modulus.size)
        (InversePreparation.auxiliary_disjoint modulus.size) (newColumn, oldColumn)) =
      ((preparation modulus).normalized.vec newRow *
        star ((preparation modulus).normalized.vec newColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn :=
  Circuit.prepare_joined_entry state InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) (preparation modulus)
    newRow newColumn oldRow oldColumn

/-- Every full external-reference matrix entry is preserved by this actual fixed preparation. -/
theorem execute_reference_entry (modulus : Nat)
    (state : State (InversePreparation.before modulus.size) Reference H)
    (left right : Reference.Index) :
    (∑ basis : (InversePreparation.after modulus.size).register.Index,
      ((circuit modulus).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (InversePreparation.before modulus.size).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) :=
  Circuit.prepare_reference_entry state InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) (preparation modulus) left right

/-- Actual preparation preserves the complete incoming mass without a basis-state restriction. -/
theorem execute_mass (modulus : Nat)
    (state : State (InversePreparation.before modulus.size) Reference H) :
    ((circuit modulus).execute Reference state).mass = state.mass :=
  Circuit.execute_mass (circuit modulus) Reference state

end

end QuantumAlg.MeasuredUncompute.InPlacePreparation
