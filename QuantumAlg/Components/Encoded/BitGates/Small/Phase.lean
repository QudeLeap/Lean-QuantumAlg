/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Conjugation
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit

/-!
# Elementary phases on two or three actual wires

The literal H, CNOT, H and H, Toffoli, H sequences need no work wire.
Their exact encoded-ket phases follow from the same Hadamard conjugation
law used by the arbitrary-restored-work construction.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- A controlled Z compiled to the actual addressed H, CNOT, H sequence. -/
def controlledZ (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) : UnitaryCircuit (Qubits encoding.width) :=
  target.conjugateHadamard (GateSpec.cnot control target different).program

/-- The two-wire phase is exact on the complete encoded label. -/
theorem controlledZ_applyVec_encoded_ket (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) (state : Data) :
    (control.controlledZ target different).applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      (if control.get state = true ∧ target.get state = true then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  have actual (state : Data) :
      (GateSpec.cnot control target different).program.applyVec
          (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
        if control.get state = true then
          (NormalizedVector.ket (R := Qubits encoding.width)
            (encoding.encode (target.flip state))).vec
        else (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
    calc
      _ = (NormalizedVector.ket (R := Qubits encoding.width)
          (encoding.encode ((GateSpec.cnot control target different).step state))).vec :=
        congrArg NormalizedVector.vec
          ((GateSpec.cnot control target different).realizes.apply_encoded_ket state)
      _ = _ := by
        simp only [GateSpec.step, cnotStep]
        cases control.get state <;> rfl
  have phase := target.conjugateHadamard_applyVec_encoded_ket
    (GateSpec.cnot control target different).program (fun state => control.get state = true)
    (fun state => by rw [get_flip_of_wire_ne target control different.symm]) actual state
  change (target.conjugateHadamard _).applyVec _ = _
  rw [phase]
  split <;> simp

/-- The controlled Z emits exactly its three elementary occurrences. -/
theorem controlledZ_eventTrace_length (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) :
    (control.controlledZ target different).eventTrace.length = 3 := by
  simp only [controlledZ, conjugateHadamard_eventTrace, GateSpec.program_eventTrace,
    List.length_append, List.length_singleton]

/-- A three-wire phase compiled to the actual addressed H, Toffoli, H sequence. -/
def doubleControlledZ (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) : UnitaryCircuit (Qubits encoding.width) :=
  target.conjugateHadamard
    (GateSpec.toffoli first second target firstSecond firstTarget secondTarget).program

/-- The three-wire phase changes no label and requires no work-state assumption. -/
theorem doubleControlledZ_applyVec_encoded_ket (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) (state : Data) :
    (first.doubleControlledZ second target firstSecond firstTarget secondTarget).applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      (if (first.get state = true ∧ second.get state = true) ∧ target.get state = true
        then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  have gateAction :=
    (GateSpec.toffoli first second target firstSecond firstTarget secondTarget).realizes
  have actual (state : Data) :
      (GateSpec.toffoli first second target firstSecond firstTarget secondTarget).program.applyVec
          (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
        if first.get state = true ∧ second.get state = true then
          (NormalizedVector.ket (R := Qubits encoding.width)
            (encoding.encode (target.flip state))).vec
        else (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
    calc
      _ = (NormalizedVector.ket (R := Qubits encoding.width)
          (encoding.encode
            ((GateSpec.toffoli first second target firstSecond firstTarget secondTarget).step
              state))).vec :=
        congrArg NormalizedVector.vec (gateAction.apply_encoded_ket state)
      _ = _ := by
        simp only [GateSpec.step, toffoliStep]
        cases first.get state <;> cases second.get state <;> rfl
  have phase := target.conjugateHadamard_applyVec_encoded_ket
    (GateSpec.toffoli first second target firstSecond firstTarget secondTarget).program
    (fun state => first.get state = true ∧ second.get state = true)
    (fun state => by
      rw [get_flip_of_wire_ne target first firstTarget.symm,
        get_flip_of_wire_ne target second secondTarget.symm]) actual state
  change (target.conjugateHadamard _).applyVec _ = _
  rw [phase]
  split <;> simp

/-- The three-wire phase still contains only three actual elementary gates. -/
theorem doubleControlledZ_eventTrace_length (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) :
    (first.doubleControlledZ second target firstSecond firstTarget secondTarget).eventTrace.length =
      3 := by
  simp only [doubleControlledZ, conjugateHadamard_eventTrace, GateSpec.program_eventTrace,
    List.length_append, List.length_singleton]

end

end QuantumAlg.EncodedBit
