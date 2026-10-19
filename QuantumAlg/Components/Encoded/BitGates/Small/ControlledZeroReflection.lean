/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Small.Phase
import all QuantumAlg.Components.Encoded.BitGates.DiagonalConjugation
import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector

/-!
# Small controlled positive zero reflections without work wires

A one-wire source reflection is controlled Z. For two source wires,
complementing the source alone around H, Toffoli, H yields its negative
zero phase; one actual Z on the external control supplies the controlled
global minus. The external control is never complemented, and control
zero is exact identity on the complete encoded label.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)
variable {environment : oracles.Interpretation}

/-- The existing three-gate controlled Z controls the one-wire positive zero reflection. -/
lemma controlledZ_reflects_zero (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) (state : Data) :
    (control.controlledZ physical oracles target different).applyVec environment
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      if control.get state then
        if target.get state = false then
          (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec
        else -(NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec
      else (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  rw [controlledZ_applyVec_encoded_ket]
  cases control.get state <;> cases target.get state <;> simp

/-- Two source wires and one external control suffice for this eight-gate construction. -/
def controlledTwoWireZeroReflection (control first second : EncodedBit encoding)
    (controlFirst : control.wire ≠ first.wire)
    (controlSecond : control.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (GateSpec.conjugateProgram physical oracles [.x first, .x second]
    (control.doubleControlledZ physical oracles first second
      controlFirst controlSecond firstSecond)).seq
      (control.pauliZ physical oracles)

/-- The two-source controlled reflection has the exact phase on both control branches. -/
lemma controlledTwoWireZeroReflection_applyVec_encoded_ket
    (control first second : EncodedBit encoding)
    (controlFirst : control.wire ≠ first.wire)
    (controlSecond : control.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) (state : Data) :
    (control.controlledTwoWireZeroReflection physical oracles first second controlFirst
      controlSecond firstSecond).applyVec environment
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      if control.get state then
        if first.get state = false ∧ second.get state = false then
          (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec
        else -(NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec
      else (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  have controlRead :
      control.get (GateSpec.stepList [.x first, .x second] state) = control.get state := by
    change control.get (second.flip (first.flip state)) = _
    rw [get_flip_of_wire_ne second control controlSecond.symm,
      get_flip_of_wire_ne first control controlFirst.symm]
  have firstRead :
      first.get (GateSpec.stepList [.x first, .x second] state) = Bool.not (first.get state) := by
    change first.get (second.flip (first.flip state)) = _
    rw [get_flip_of_wire_ne second first firstSecond.symm, get_flip_self]
  have secondRead :
      second.get (GateSpec.stepList [.x first, .x second] state) = Bool.not (second.get state) := by
    change second.get (second.flip (first.flip state)) = _
    rw [get_flip_self, get_flip_of_wire_ne first second firstSecond]
  have middle := GateSpec.conjugateProgram_applyVec_encoded_ket physical oracles (environment :=
    environment)
    [.x first, .x second]
    (control.doubleControlledZ physical oracles first second
      controlFirst controlSecond firstSecond)
    (fun state => if (control.get state = true ∧ first.get state = true) ∧ second.get state = true
      then (-1 : ℂ) else 1)
    (control.doubleControlledZ_applyVec_encoded_ket physical oracles (environment := environment)
      first second
      controlFirst controlSecond firstSecond) state
  rw [controlledTwoWireZeroReflection, UnitaryCircuit.applyVec_seq, middle,
    UnitaryCircuit.applyVec_smul, pauliZ_applyVec_encoded_ket]
  simp only [controlRead, firstRead, secondRead]
  cases control.get state <;> cases first.get state <;> cases second.get state <;> simp

/-- The actual ledger includes four complements, three phase gates and the final control Z. -/
lemma controlledTwoWireZeroReflection_eventTrace_length
    (control first second : EncodedBit encoding)
    (controlFirst : control.wire ≠ first.wire)
    (controlSecond : control.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) :
    (control.controlledTwoWireZeroReflection physical oracles first second
      controlFirst controlSecond firstSecond).eventTrace.length = 8 := by
  simp only [controlledTwoWireZeroReflection, UnitaryCircuit.seq_eventTrace, List.length_append,
    GateSpec.conjugateProgram_eventTrace_length, List.length_cons, List.length_nil,
    doubleControlledZ_eventTrace_length, pauliZ_eventTrace]

end

end QuantumAlg.EncodedBit
