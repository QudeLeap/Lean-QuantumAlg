/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Conjugation
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Kets

/-!
# Exact multi-control phase with one restored arbitrary work bit

The literal target-H, multi-control-X, target-H sequence negates exactly
the basis states with all controls and the target equal to one. The full
encoded label is unchanged, including the arbitrary borrowed work bit.
The equality retains the exact sign, so it also applies under coherent
control and on superpositions correlated with an external reference.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

open NormalizedVector

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}
variable (layout : OneDirtyLayout (encoding := encoding) controls)
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- Conjugate the actual restored-dirty multi-control X by two target Hadamards. -/
def phaseProgram : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  layout.output.conjugateHadamard physical oracles
    (GateSpec.programList physical oracles layout.gates)

private theorem allControls_output_flip (state : Data) :
    (∀ index, (layout.source.bit index).get (layout.output.flip state) = true) ↔
      ∀ index, (layout.source.bit index).get state = true := by
  apply forall_congr'
  intro index
  rw [get_flip_of_wire_ne layout.output (layout.source.bit index)
    (layout.source_output_ne index).symm]

private theorem gates_applyVec (state : Data) :
    (GateSpec.programList physical oracles layout.gates).applyVec
        (ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      if ∀ index, (layout.source.bit index).get state = true then
        (ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode (layout.output.flip state)))).vec
      else (ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  have actual := congrArg NormalizedVector.vec
    ((layout.gates_realizes physical oracles).apply_encoded_ket state)
  change (GateSpec.programList physical oracles layout.gates).applyVec
      (ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode state))).vec =
    (ket (R := physical.toQuantum.register)
      (physical.basisEquiv.symm (encoding.encode
        (if ∀ index, (layout.source.bit index).get state = true
          then layout.output.flip state else state)))).vec at actual
  by_cases active : ∀ index, (layout.source.bit index).get state = true
  · simpa only [if_pos active] using actual
  · simpa only [if_neg active] using actual

/-- Exact diagonal action on every encoded input, without a cleanliness premise. -/
theorem phaseProgram_applyVec_encoded_ket (state : Data) :
    (layout.phaseProgram physical oracles).applyVec
        (ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      if (∀ index, (layout.source.bit index).get state = true) ∧
          layout.output.get state = true then
        -(ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec
      else (ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec :=
  layout.output.conjugateHadamard_applyVec_encoded_ket physical oracles
    (GateSpec.programList physical oracles layout.gates)
    (fun state => ∀ index, (layout.source.bit index).get state = true)
    layout.allControls_output_flip (layout.gates_applyVec physical oracles) state

/-- The actual trace contains the two Hadamards and the exact elementary MCX list. -/
theorem phaseProgram_eventTrace :
    (layout.phaseProgram physical oracles).eventTrace =
      [.gate .singleQubit] ++ layout.gates.map (GateSpec.event oracles) ++
        [.gate .singleQubit] := by
  simp only [phaseProgram, conjugateHadamard_eventTrace,
    GateSpec.programList_eventTrace]

/-- The phase bridge adds precisely two gates to the actual MCX list. -/
theorem phaseProgram_eventTrace_length :
    (layout.phaseProgram physical oracles).eventTrace.length = layout.gates.length + 2 := by
  rw [phaseProgram_eventTrace]
  simp only [List.length_append, List.length_singleton, List.length_map]
  omega

/-- The same literal phase circuit has linear event length. -/
theorem phaseProgram_eventTrace_length_le :
    (layout.phaseProgram physical oracles).eventTrace.length ≤ 8 * controls + 3 := by
  rw [phaseProgram_eventTrace_length]
  have actual := layout.gates_length_le
  omega

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
