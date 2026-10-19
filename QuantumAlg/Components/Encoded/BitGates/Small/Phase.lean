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
  (layout : QubitLayout encoding.width) (oracles : OracleModel)
variable {environment : oracles.Interpretation}

/-- A controlled Z compiled to the actual addressed H, CNOT, H sequence. -/
def controlledZ (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) :
    UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  target.conjugateHadamard layout oracles
    ((GateSpec.cnot control target different).program layout oracles)

/-- The two-wire phase is exact on the complete encoded label. -/
lemma controlledZ_applyVec_encoded_ket (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) (state : Data) :
    (control.controlledZ layout oracles target different).applyVec environment
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      (if control.get state = true ∧ target.get state = true then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
  have actual (state : Data) :
      ((GateSpec.cnot control target different).program layout oracles).applyVec environment
          (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
        if control.get state = true then
          (NormalizedVector.ket (R := layout.toQuantum.register)
            (layout.basisEquiv.symm (encoding.encode (target.flip state)))).vec
        else (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
    calc
      _ = (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm
            (encoding.encode ((GateSpec.cnot control target different).step state)))).vec :=
        congrArg NormalizedVector.vec
          ((GateSpec.realizes layout oracles (environment := environment)
            (.cnot control target different)).apply_encoded_ket state)
      _ = _ := by
        simp only [GateSpec.step, cnotStep]
        cases control.get state <;> simp
  have phase := target.conjugateHadamard_applyVec_encoded_ket layout oracles (environment :=
    environment)
    ((GateSpec.cnot control target different).program layout oracles)
    (fun state => control.get state = true)
    (fun state => by rw [get_flip_of_wire_ne target control different.symm]) actual state
  change (target.conjugateHadamard layout oracles _).applyVec environment _ = _
  rw [phase]
  split <;> simp

/-- The controlled Z emits exactly its three elementary occurrences. -/
lemma controlledZ_eventTrace_length (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) :
    (control.controlledZ layout oracles target different).eventTrace.length = 3 := by
  simp only [controlledZ, conjugateHadamard_eventTrace, GateSpec.program_eventTrace,
    List.length_append, List.length_singleton]

/-- A three-wire phase compiled to the actual addressed H, Toffoli, H sequence. -/
def doubleControlledZ (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) :
    UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  target.conjugateHadamard layout oracles
    ((GateSpec.toffoli first second target firstSecond firstTarget secondTarget).program
      layout oracles)

/-- The three-wire phase changes no label and requires no work-state assumption. -/
lemma doubleControlledZ_applyVec_encoded_ket (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) (state : Data) :
    (first.doubleControlledZ layout oracles second target
      firstSecond firstTarget secondTarget).applyVec environment
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      (if (first.get state = true ∧ second.get state = true) ∧ target.get state = true
        then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
  have gateAction :=
    GateSpec.realizes layout oracles (environment := environment)
      (.toffoli first second target firstSecond firstTarget secondTarget)
  have actual (state : Data) :
      ((GateSpec.toffoli first second target firstSecond firstTarget secondTarget).program
        layout oracles).applyVec environment
          (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
        if first.get state = true ∧ second.get state = true then
          (NormalizedVector.ket (R := layout.toQuantum.register)
            (layout.basisEquiv.symm (encoding.encode (target.flip state)))).vec
        else (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
    calc
      _ = (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode
            ((GateSpec.toffoli first second target firstSecond firstTarget secondTarget).step
              state)))).vec :=
        congrArg NormalizedVector.vec (gateAction.apply_encoded_ket state)
      _ = _ := by
        simp only [GateSpec.step, toffoliStep]
        cases first.get state <;> cases second.get state <;> simp
  have phase := target.conjugateHadamard_applyVec_encoded_ket layout oracles (environment :=
    environment)
    ((GateSpec.toffoli first second target firstSecond firstTarget secondTarget).program
      layout oracles)
    (fun state => first.get state = true ∧ second.get state = true)
    (fun state => by
      rw [get_flip_of_wire_ne target first firstTarget.symm,
        get_flip_of_wire_ne target second secondTarget.symm]) actual state
  change (target.conjugateHadamard layout oracles _).applyVec environment _ = _
  rw [phase]
  split <;> simp

/-- The three-wire phase still contains only three actual elementary gates. -/
lemma doubleControlledZ_eventTrace_length (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) :
    (first.doubleControlledZ layout oracles second target
      firstSecond firstTarget secondTarget).eventTrace.length =
      3 := by
  simp only [doubleControlledZ, conjugateHadamard_eventTrace, GateSpec.program_eventTrace,
    List.length_append, List.length_singleton]

end

end QuantumAlg.EncodedBit
