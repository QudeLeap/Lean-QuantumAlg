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
# Positive zero reflections at small widths without work wires

The one-wire source reflection is the existing Pauli Z. Two wires use
Z, Z, and the three-gate controlled Z. Three wires use complements around
the three-gate double-controlled Z followed by the exact one-gate global
minus. Every complete encoded label is preserved; no auxiliary position
or auxiliary-state premise occurs in these constructions.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  (layout : QubitLayout encoding.width) (oracles : OracleModel)
variable {environment : oracles.Interpretation}

/-- The existing Pauli Z is precisely the positive reflection through bit zero. -/
lemma pauliZ_reflects_zero (target : EncodedBit encoding) (state : Data) :
    (target.pauliZ layout oracles).applyVec environment
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      if target.get state = false then
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec
      else -(NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
  rw [pauliZ_applyVec_encoded_ket]
  cases target.get state <;> simp

/-- Two original wires suffice for this five-gate positive zero reflection. -/
def twoWireZeroReflection (first second : EncodedBit encoding)
    (different : first.wire ≠ second.wire) :
    UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  ((first.pauliZ layout oracles).seq (second.pauliZ layout oracles)).seq
    (first.controlledZ layout oracles second different)

/-- The two-wire construction has the source's exact positive zero phase. -/
lemma twoWireZeroReflection_applyVec_encoded_ket (first second : EncodedBit encoding)
    (different : first.wire ≠ second.wire) (state : Data) :
    (first.twoWireZeroReflection layout oracles second different).applyVec environment
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      if first.get state = false ∧ second.get state = false then
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec
      else -(NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
  simp only [twoWireZeroReflection, UnitaryCircuit.applyVec_seq]
  rw [pauliZ_applyVec_encoded_ket first layout oracles state,
    UnitaryCircuit.applyVec_smul, pauliZ_applyVec_encoded_ket second layout oracles state,
    UnitaryCircuit.applyVec_smul, UnitaryCircuit.applyVec_smul,
    controlledZ_applyVec_encoded_ket]
  cases first.get state <;> cases second.get state <;> simp

/-- The event trace contains the two Z gates and three controlled-Z elementary gates. -/
lemma twoWireZeroReflection_eventTrace_length (first second : EncodedBit encoding)
    (different : first.wire ≠ second.wire) :
    (first.twoWireZeroReflection layout oracles second different).eventTrace.length = 5 := by
  simp only [twoWireZeroReflection, UnitaryCircuit.seq_eventTrace, List.length_append,
    pauliZ_eventTrace, List.length_singleton, controlledZ_eventTrace_length]

/-- The three-wire construction uses only its three supplied physical wires. -/
def threeWireZeroReflection (first second third : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstThird : first.wire ≠ third.wire)
    (secondThird : second.wire ≠ third.wire) :
    UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  (GateSpec.conjugateProgram layout oracles [.x first, .x second, .x third]
    (first.doubleControlledZ layout oracles second third firstSecond firstThird secondThird)).seq
      (third.globalMinus layout oracles)

/-- Complementing three wires and restoring them retains the exact positive source phase. -/
lemma threeWireZeroReflection_applyVec_encoded_ket (first second third : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstThird : first.wire ≠ third.wire)
    (secondThird : second.wire ≠ third.wire) (state : Data) :
    (first.threeWireZeroReflection layout oracles second third
      firstSecond firstThird secondThird).applyVec environment
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      if (first.get state = false ∧ second.get state = false) ∧ third.get state = false then
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec
      else -(NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec := by
  have firstRead :
      first.get (GateSpec.stepList [.x first, .x second, .x third] state) =
        Bool.not (first.get state) := by
    change first.get (third.flip (second.flip (first.flip state))) = _
    rw [get_flip_of_wire_ne third first firstThird.symm,
      get_flip_of_wire_ne second first firstSecond.symm, get_flip_self]
  have secondRead :
      second.get (GateSpec.stepList [.x first, .x second, .x third] state) =
        Bool.not (second.get state) := by
    change second.get (third.flip (second.flip (first.flip state))) = _
    rw [get_flip_of_wire_ne third second secondThird.symm, get_flip_self,
      get_flip_of_wire_ne first second firstSecond]
  have thirdRead :
      third.get (GateSpec.stepList [.x first, .x second, .x third] state) =
        Bool.not (third.get state) := by
    change third.get (third.flip (second.flip (first.flip state))) = _
    rw [get_flip_self, get_flip_of_wire_ne second third secondThird,
      get_flip_of_wire_ne first third firstThird]
  have middle := GateSpec.conjugateProgram_applyVec_encoded_ket layout oracles (environment :=
    environment)
    [.x first, .x second, .x third]
    (first.doubleControlledZ layout oracles second third firstSecond firstThird secondThird)
    (fun state => if (first.get state = true ∧ second.get state = true) ∧ third.get state = true
      then (-1 : ℂ) else 1)
    (first.doubleControlledZ_applyVec_encoded_ket layout oracles (environment := environment) second
      third
      firstSecond firstThird secondThird) state
  rw [threeWireZeroReflection, UnitaryCircuit.applyVec_seq, middle,
    UnitaryCircuit.applyVec_smul, globalMinus_applyVec_encoded_ket]
  simp only [firstRead, secondRead, thirdRead]
  cases first.get state <;> cases second.get state <;> cases third.get state <;> simp

/-- All six complements, three phase gates, and one global-minus gate are actual events. -/
lemma threeWireZeroReflection_eventTrace_length (first second third : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstThird : first.wire ≠ third.wire)
    (secondThird : second.wire ≠ third.wire) :
    (first.threeWireZeroReflection layout oracles second third firstSecond firstThird
      secondThird).eventTrace.length = 10 := by
  simp only [threeWireZeroReflection, UnitaryCircuit.seq_eventTrace, List.length_append,
    GateSpec.conjugateProgram_eventTrace_length, List.length_cons, List.length_nil,
    doubleControlledZ_eventTrace_length, globalMinus_eventTrace_length]

end

end QuantumAlg.EncodedBit
