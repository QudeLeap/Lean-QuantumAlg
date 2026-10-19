/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.PhaseCorrection
import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Context.Layout.Unitary

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

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution
open EncodedBit.Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum}

/-- The branch mask is obtained from the stored bit vector's structural projections. -/
def mask (value : CShape.Value (.bits width)) : Fin width → Bool :=
  fun index => (value.bitGet index).toBool

/-- Place the actual selected Z gates into the existing complete quantum frame. -/
def member (word : EncodedBit.Word encoding width)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (value : CShape.Value (.bits width)) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  unitaryOfEqualWires (QubitLayout.canonical encoding.width).toQuantum
    ctx.quantumLayout sameWires
      (PhaseCorrection.program (QubitLayout.canonical _) .empty word (mask value))

/-- Read the actual classical register before choosing the concrete correction gates. -/
def code (word : EncodedBit.Word encoding width)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width)) :
    Circuit (.quantum AlgorithmGate.model .empty) ctx ctx :=
  .branch result (fun value => .unitary (member word sameWires value))

/-- Each original store block chooses its stored correction, with the full reference. -/
lemma measuredCorrection_actual_reference (word : EncodedBit.Word encoding width)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    ((code word sameWires result).execute environment Reference state).quantumMarginal =
      (state.applyUnitary (fun entry => UnitaryOperator.prodTensor
        ((member word sameWires (entry.1.read result)).matrix environment.quantum)
        (1 : UnitaryOperator Reference))).quantumMarginal :=
  Circuit.selectedUnitary_quantumMarginal result (member word sameWires) environment state

/-- The actual selected trace contains only the executed native Pauli-Z occurrences. -/
lemma measuredCorrection_actual_trace (word : EncodedBit.Word encoding width)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width)) (path : (code word sameWires result).Path) :
    (code word sameWires result).eventTrace path =
      List.replicate (PhaseCorrection.selected (mask path.1)).length
        (.gate .singleQubit) := by
  change (member word sameWires path.1).eventTrace .empty .empty = _
  rw [member, unitaryOfEqualWires_trace, PhaseCorrection.program,
    PhaseCorrection.phaseCorrection_sequence_trace]

/-- The same actual path's unit depth equals its selected correction count. -/
lemma measuredCorrection_actual_depth (word : EncodedBit.Word encoding width)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width)) (path : (code word sameWires result).Path) :
    (code word sameWires result).depth (fun _ => 1) path =
      (PhaseCorrection.selected (mask path.1)).length := by
  change (member word sameWires path.1).evaluatedEventDepth (fun _ => 1) = _
  rw [member, UnitaryCircuit.evaluatedEventDepth, unitaryOfEqualWires_depth]
  change (PhaseCorrection.program (QubitLayout.canonical _) .empty word
    (mask path.1)).evaluatedEventDepth (fun _ => 1) = _
  rw [PhaseCorrection.program,
    PhaseCorrection.phaseCorrection_sequence_depth]

/-- Correction executes within the same complete context, with no allocation or release. -/
lemma measuredCorrection_actual_context (word : EncodedBit.Word encoding width)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width)) (path : (code word sameWires result).Path) :
    (code word sameWires result).visitedContexts path = [ctx] := rfl

end

end QuantumAlg.MeasuredUncompute.ClassicalCorrection
