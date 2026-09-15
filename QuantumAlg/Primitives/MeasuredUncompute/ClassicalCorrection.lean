/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.PhaseCorrection
import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual stored-result selection of arithmetic phase corrections

The circuit reads an existing classical bit vector and executes the literal
Pauli-Z sequence selected by its value. The quantum state includes every live
system and an arbitrary external reference. Its interpretation, trace and
depth describe the same selected branch; it allocates no additional storage.

This is the classical feed-forward step after measured-word recomputation
[LYL+26, sec_point_add/sec_point_add.tex:85-105]. The surrounding Hadamards,
Z writes, reset, arithmetic recomputation and its inverse must be composed
with this circuit to establish complete measurement-assisted uncomputation.
-/

namespace QuantumAlg.MeasuredUncompute.ClassicalCorrection

noncomputable section

open Execution
open EncodedBit.Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum}

/-- The branch mask is obtained from the stored bit vector's structural projections. -/
def mask (value : CShape.Value (.bits width)) : Fin width → Bool :=
  fun index => (value.bitGet index).toBool

/-- Place the actual selected Z gates into the existing complete quantum frame. -/
def member (word : EncodedBit.Word encoding width)
    (basis : (Qubits encoding.width).Index ≃ ctx.register.Index)
    (value : CShape.Value (.bits width)) : UnitaryCircuit ctx.register :=
  .reindex basis (PhaseCorrection.program word (mask value))

/-- The selected member retains exactly the existing frame's physical identities. -/
theorem member_physical (word : EncodedBit.Word encoding width)
    (basis : (Qubits encoding.width).Index ≃ ctx.register.Index)
    (placed : List.range encoding.width = ctx.physicalIdx)
    (value : CShape.Value (.bits width)) :
    (member word basis value).physical_idx = ctx.physicalIdx :=
  (PhaseCorrection.phaseCorrection_sequence_physical word
    (PhaseCorrection.selected (mask value))).trans placed

/-- Read the actual classical register before choosing the concrete correction gates. -/
def code (word : EncodedBit.Word encoding width)
    (basis : (Qubits encoding.width).Index ≃ ctx.register.Index)
    (placed : List.range encoding.width = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width)) : Circuit ctx ctx :=
  .branch result (fun value =>
    .unitary (member word basis value) (member_physical word basis placed value))

/-- Each original store block chooses its stored correction, with the full reference. -/
theorem measuredCorrection_actual_reference (word : EncodedBit.Word encoding width)
    (basis : (Qubits encoding.width).Index ≃ ctx.register.Index)
    (placed : List.range encoding.width = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    ((code word basis placed result).execute Reference state).quantumMarginal =
      (state.applyUnitary (fun entry => UnitaryOperator.prodTensor
        (member word basis (entry.1.read result)).matrix
        (1 : UnitaryOperator Reference))).quantumMarginal :=
  Circuit.selectedUnitary_quantumMarginal result (member word basis)
    (member_physical word basis placed) state

/-- The actual selected trace contains only the executed native Pauli-Z occurrences. -/
theorem measuredCorrection_actual_trace (word : EncodedBit.Word encoding width)
    (basis : (Qubits encoding.width).Index ≃ ctx.register.Index)
    (placed : List.range encoding.width = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width)) (path : (code word basis placed result).Path) :
    (code word basis placed result).eventTrace path =
      List.replicate (PhaseCorrection.selected (mask path.1)).length
        (Gate.atomicEvent (.declared "QuantumAlg.Components.Gate" "pauli-z")) :=
  PhaseCorrection.phaseCorrection_sequence_trace word (PhaseCorrection.selected (mask path.1))

/-- The same actual path's unit depth equals its selected correction count. -/
theorem measuredCorrection_actual_depth (word : EncodedBit.Word encoding width)
    (basis : (Qubits encoding.width).Index ≃ ctx.register.Index)
    (placed : List.range encoding.width = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width)) (path : (code word basis placed result).Path) :
    (code word basis placed result).depth (fun _ => 1) path =
      (PhaseCorrection.selected (mask path.1)).length :=
  PhaseCorrection.phaseCorrection_sequence_depth word (PhaseCorrection.selected (mask path.1))

/-- Correction executes within the same complete context, with no allocation or release. -/
theorem measuredCorrection_actual_context (word : EncodedBit.Word encoding width)
    (basis : (Qubits encoding.width).Index ≃ ctx.register.Index)
    (placed : List.range encoding.width = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width)) (path : (code word basis placed result).Path) :
    (code word basis placed result).visitedContexts path = [ctx] := rfl

end

end QuantumAlg.MeasuredUncompute.ClassicalCorrection
