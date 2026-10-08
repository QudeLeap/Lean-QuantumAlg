/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Placement
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Execute the physically placed shared-EEA control kernel

The source orders Ctrl after the four work groups; the actual preparation
prepends Ctrl. NativePlacement maps every source gate to that physical runtime
wire. The one circuit interpreter executes the placed gate sequence after the
real Ctrl-zero allocation. Matrix and event accounting observe that same
sequence, including arbitrary prior joint state and external references.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeRuntime

noncomputable section

open Execution ControlPreparation NativePlacement

/-- The source-register coordinate selected by the actual placed physical wires. -/
def nativeFrame (width : Nat) (basis : (after width).register.Index) : Registers width :=
  (PreparedFrame.registerLabelEquiv width).symm
    ((QubitLayout.canonical (encoding width).width).basisEquiv
      (UnitaryCircuit.basisAt
        (QubitLayout.canonical (encoding width).width).toQuantum
        (after width).quantumLayout (position width) (position_dimensions width) basis))

private theorem position_surjective (width : Nat) :
    Function.Surjective (position width) := by
  have sameWidth : (encoding width).width = (after width).systemCount := by
    rw [after_count]
    have complete := complete_width width
    omega
  let endomap := fun index : Fin (encoding width).width =>
    Fin.cast sameWidth.symm (position width index)
  have injective : Function.Injective endomap := by
    intro left right same
    apply (position width).injective
    exact Fin.cast_injective sameWidth.symm same
  intro target
  obtain ⟨source, same⟩ :=
    Finite.surjective_of_injective injective (Fin.cast sameWidth.symm target)
  exact ⟨source, Fin.cast_injective sameWidth.symm same⟩

/-- One placed native unitary acts on exactly the post-preparation runtime layout. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty (after width).quantumLayout :=
  NativePlacement.program width enough

/-- Each runtime matrix coordinate reads precisely the corresponding source gate coordinates. -/
theorem program_matrix_entry (width : Nat) (enough : 2 ≤ width.size)
    (row column : (after width).register.Index) :
    (program width enough).matrix row column =
      (NativeControl.program width enough).matrix
        (UnitaryCircuit.basisAt
          (QubitLayout.canonical (encoding width).width).toQuantum
          (after width).quantumLayout (position width) (position_dimensions width) row)
        (UnitaryCircuit.basisAt
          (QubitLayout.canonical (encoding width).width).toQuantum
          (after width).quantumLayout (position width) (position_dimensions width) column) := by
  rw [program, NativePlacement.program, UnitaryCircuit.placeAt_matrix]
  exact UnitaryCircuit.operatorAt_entry_of_surjective _ _ _ _
    (position_surjective width) _ row column

/-- The native phase-control step uses source labels decoded from the placed wires. -/
theorem program_source_entry (width : Nat) (enough : 2 ≤ width.size)
    (row column : (after width).register.Index) :
    (program width enough).matrix row column =
      if nativeFrame width row = NativeControl.step (nativeFrame width column) then 1 else 0 := by
  rw [program_matrix_entry]
  have sourceBasis (basis : (after width).register.Index) :
      UnitaryCircuit.basisAt
        (QubitLayout.canonical (encoding width).width).toQuantum
        (after width).quantumLayout (position width) (position_dimensions width) basis =
      (QubitLayout.canonical (encoding width).width).basisEquiv.symm
        ((encoding width).encode (nativeFrame width basis)) := by
    rw [← PreparedFrame.registerLabelEquiv_encode]
    change _ = (QubitLayout.canonical (encoding width).width).basisEquiv.symm
      (PreparedFrame.registerLabelEquiv width
        ((PreparedFrame.registerLabelEquiv width).symm _))
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  rw [sourceBasis row, sourceBasis column]
  have action := congrArg
    (fun vector : NormalizedVector
      (QubitLayout.canonical (encoding width).width).toQuantum.register =>
      vector ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
        ((encoding width).encode (nativeFrame width row))))
    ((NativeControl.program_realizes width enough).apply_encoded_ket
      (nativeFrame width column))
  change (NativeControl.program width enough).applyVec
      (NormalizedVector.ket ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
        ((encoding width).encode (nativeFrame width column))))
      ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
        ((encoding width).encode (nativeFrame width row))) = _ at action
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket, NormalizedVector.ket_apply] at action
  have basisIff :
      (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          ((encoding width).encode (nativeFrame width row)) =
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          ((encoding width).encode (NativeControl.step (nativeFrame width column))) ↔
      nativeFrame width row = NativeControl.step (nativeFrame width column) :=
    ((QubitLayout.canonical (encoding width).width).basisEquiv.symm.injective.eq_iff).trans
      (encoding width).encode_injective.eq_iff
  simpa only [basisIff] using action

/-- Execute the same placed native gates through the selected model interpreter. -/
def circuit (width : Nat) (enough : 2 ≤ width.size) :
    Circuit (.quantum AlgorithmGate.model .empty) (after width) (after width) :=
  .unitary (program width enough)

/-- Allocate Ctrl in zero and then run the native phase-control kernel. -/
def initializeThenControl (width : Nat) (enough : 2 ≤ width.size) :
    Circuit (.quantum AlgorithmGate.model .empty) (before width) (after width) :=
  .seq (ControlPreparation.circuit width) (circuit width enough)

theorem program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace = (NativeControl.program width enough).eventTrace :=
  NativePlacement.program_eventTrace width enough

theorem program_eventCost (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost = (NativeControl.program width enough).eventCost :=
  NativePlacement.program_eventCost width enough

/-- The allocation event and both predicate passes remain on one executed path. -/
theorem initializeThenControl_trace (width : Nat) (enough : 2 ≤ width.size)
    (path : (initializeThenControl width enough).Path) :
    (initializeThenControl width enough).eventTrace path =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty (controlLayout width) ++
        (NativeControl.program width enough).eventTrace := by
  change ZeroPreparation.eventTrace AlgorithmGate.model .empty (controlLayout width) ++
    (program width enough).eventTrace = _
  rw [program_eventTrace]

variable {Reference : Register} {H : Type} [Fintype H]

/-- Actual execution preserves every external-reference matrix entry. -/
theorem execute_reference_entry (width : Nat) (enough : 2 ≤ width.size)
    (state : State (after width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (left right : Reference.Index) :
    (∑ basis : (after width).register.Index,
      ((circuit width enough).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (after width).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) :=
  Circuit.unitary_reference_entry (operations := .empty) (classicalOracles := .empty)
    (program width enough) state left right

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeRuntime
