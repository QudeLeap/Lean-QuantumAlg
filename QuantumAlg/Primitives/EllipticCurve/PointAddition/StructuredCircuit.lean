/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.BaseGateRealization
public import QuantumAlg.Core.Components.EncodedBitGates
public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Controlled

/-!
# Encoded base-gate point-addition witnesses

This module provides the point-addition-facing wrapper for future concrete
Toffoli/CNOT/X generic and controlled ECADD programs.  The generic affine route
follows Proos--Zalka [PZ03, ecc.tex:525-640], and the controlled-addition
boundary follows RNSL17 [RNSL17, ECDLP.tex:488-580,650-696].  A closing witness
must supply a binary label encoding and a `BaseGateProgram` whose label action
implements the corresponding coordinate-target update.  The folded `Circuit` is
then the same object used for encoded-basis correctness and resource accounting.
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass

variable {p : ℕ}

noncomputable section

namespace GenericPointAddition

/-- Explicit state for a decomposed generic ECADD realization.  The modular
division substate is a real field of the encoded label, so the slope stage can
be supplied by a structured MAU division witness rather than by an endpoint
permutation gate. -/
structure DecomposedState (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) where
  /-- Generic-domain input point for adding the fixed addend `Q`. -/
  input : Input E Q
  /-- Target `x` coordinate accumulator. -/
  targetX : ZMod p
  /-- Target `y` coordinate accumulator. -/
  targetY : ZMod p
  /-- Scratch value holding the computed result `x` coordinate. -/
  resultX : ZMod p
  /-- Scratch value holding the computed result `y` coordinate. -/
  resultY : ZMod p
  /-- Modular-division substate used to compute the affine slope. -/
  division : ModularDivision.Data p
  /-- Temporary cleanup flag carried by the point-addition endpoint. -/
  flag : Bool
deriving DecidableEq

/-- Non-division fields of a decomposed generic ECADD state. -/
abbrev DecomposedRest (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) :=
  Input E Q × ZMod p × ZMod p × ZMod p × ZMod p × Bool

namespace DecomposedState

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- Product layout with the division substate isolated as the right component,
matching `BaseGateSameCircuitWitness.prodRight`. -/
def layout (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) :
    DecomposedState E Q ≃ DecomposedRest E Q × ModularDivision.Data p where
  toFun := fun s =>
    ((s.input, s.targetX, s.targetY, s.resultX, s.resultY, s.flag), s.division)
  invFun := fun x =>
    { input := x.1.1
      targetX := x.1.2.1
      targetY := x.1.2.2.1
      resultX := x.1.2.2.2.1
      resultY := x.1.2.2.2.2.1
      division := x.2
      flag := x.1.2.2.2.2.2 }
  left_inv := by
    intro s
    cases s
    rfl
  right_inv := by
    intro x
    rcases x with ⟨rest, division⟩
    rcases rest with ⟨input, targetX, targetY, resultX, resultY, flag⟩
    rfl

/-- Public endpoint projection from the decomposed ECADD state. -/
def toData (s : DecomposedState E Q) : Data E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  flag := s.flag

/-- Clean initial decomposed state with the modular-division substate loaded
with the affine secant numerator and denominator for the source formula. -/
def initial (P : Input E Q) (targetX targetY : ZMod p) :
    DecomposedState E Q where
  input := P
  targetX := targetX
  targetY := targetY
  resultX := 0
  resultY := 0
  division :=
    { denominator := genericAddDenominatorUnit P.1 Q P.2
      numerator := genericAddNumerator P.1 Q
      target := 0
      flag := false }
  flag := false

/-- Clean output expected after a decomposed generic ECADD run. -/
def cleanOutput (P : Input E Q) (targetX targetY : ZMod p) :
    DecomposedState E Q where
  input := P
  targetX := targetX + genericAddX E P.1 Q
  targetY := targetY + genericAddY E P.1 Q
  resultX := 0
  resultY := 0
  division :=
    { denominator := genericAddDenominatorUnit P.1 Q P.2
      numerator := genericAddNumerator P.1 Q
      target := 0
      flag := false }
  flag := false

/-- Run the modular-division subcircuit, adding the slope quotient into the
division target field. -/
def slopeStep (s : DecomposedState E Q) : DecomposedState E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  resultX := s.resultX
  resultY := s.resultY
  division := s.division.addQuotientIntoTarget
  flag := s.flag

/-- Undo the modular-division slope subcircuit. -/
def unslopeStep (s : DecomposedState E Q) : DecomposedState E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  resultX := s.resultX
  resultY := s.resultY
  division := s.division.subQuotientFromTarget
  flag := s.flag

/-- Compute affine result coordinates from the materialized slope and add them
into result scratch. -/
def coordinateStep (s : DecomposedState E Q) : DecomposedState E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  resultX := s.resultX + genericAddXFromSlope E s.input.1 Q s.division.target
  resultY := s.resultY + genericAddYFromSlope E s.input.1 Q s.division.target
  division := s.division
  flag := s.flag

/-- Uncompute the affine result-coordinate scratch. -/
def uncoordinateStep (s : DecomposedState E Q) : DecomposedState E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  resultX := s.resultX - genericAddXFromSlope E s.input.1 Q s.division.target
  resultY := s.resultY - genericAddYFromSlope E s.input.1 Q s.division.target
  division := s.division
  flag := s.flag

/-- Add the computed result-coordinate scratch into the public targets. -/
def targetStep (s : DecomposedState E Q) : DecomposedState E Q where
  input := s.input
  targetX := s.targetX + s.resultX
  targetY := s.targetY + s.resultY
  resultX := s.resultX
  resultY := s.resultY
  division := s.division
  flag := s.flag

/-- The decomposed ECADD stage list: slope division, coordinate compute,
target write, coordinate uncompute, and slope uncompute. -/
def stageSteps : List (DecomposedState E Q -> DecomposedState E Q) :=
  [slopeStep, coordinateStep, targetStep, uncoordinateStep, unslopeStep]

/-- Folded semantic action of the decomposed generic ECADD stage list. -/
def fullStep : DecomposedState E Q -> DecomposedState E Q :=
  BaseGateProgram.Realizes.stepList stageSteps

@[simp] theorem slopeStep_unslopeStep (s : DecomposedState E Q) :
    slopeStep (unslopeStep s) = s := by
  cases s
  simp [slopeStep, unslopeStep, ModularDivision.Data.addQuotientIntoTarget,
    ModularDivision.Data.subQuotientFromTarget, sub_eq_add_neg, add_assoc]

@[simp] theorem coordinateStep_uncoordinateStep (s : DecomposedState E Q) :
    coordinateStep (uncoordinateStep s) = s := by
  cases s
  simp [coordinateStep, uncoordinateStep, sub_eq_add_neg, add_assoc]

/-- Clean decomposed execution reaches the public generic ECADD endpoint and
cleans both point-operation scratch and the modular-division target. -/
theorem fullStep_initial (P : Input E Q) (targetX targetY : ZMod p) :
    fullStep (initial P targetX targetY) = cleanOutput P targetX targetY := by
  simp [fullStep, stageSteps, BaseGateProgram.Realizes.stepList, initial,
    cleanOutput, slopeStep, coordinateStep, targetStep, uncoordinateStep,
    unslopeStep, ModularDivision.Data.addQuotientIntoTarget,
    ModularDivision.Data.subQuotientFromTarget,
    genericAddSlope_eq_quotientResidue E P.1 Q P.2, genericAddX, genericAddY]

@[simp] theorem cleanOutput_toData (P : Input E Q) (targetX targetY : ZMod p) :
    (cleanOutput P targetX targetY).toData =
      ({ input := P
         targetX := targetX + genericAddX E P.1 Q
         targetY := targetY + genericAddY E P.1 Q
         flag := false } : Data E Q) :=
  rfl

/-- The clean decomposed output projects to the existing generic ECADD endpoint
map. -/
theorem cleanOutput_toData_eq_addIntoTarget
    (P : Input E Q) (targetX targetY : ZMod p) :
    (cleanOutput P targetX targetY).toData =
      ({ input := P
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget :=
  rfl

/-- The folded decomposed generic ECADD action, from clean input, projects to
the existing generic ECADD endpoint map. -/
theorem fullStep_initial_toData_eq_addIntoTarget
    (P : Input E Q) (targetX targetY : ZMod p) :
    (fullStep (initial P targetX targetY)).toData =
      ({ input := P
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget := by
  rw [fullStep_initial]
  rfl

end DecomposedState

/-- Encoding used by a decomposed generic ECADD witness.  The left component is
chosen by the caller for the point-operation fields; the right component is the
encoding already carried by the structured MAU division witness. -/
def decomposedEncoding {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E}
    (restEncoding : BinaryLabelEncoding (DecomposedRest E Q))
    (divisionWitness : ModularDivision.StructuredCircuitWitness p) :
    BinaryLabelEncoding (DecomposedState E Q) :=
  (BinaryLabelEncoding.prod restEncoding divisionWitness.encoding).relabel
    (DecomposedState.layout E Q)

/-- Lift a structured modular-division witness into the explicit slope substate
of a decomposed generic ECADD label. -/
def slopeSameCircuit {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E}
    (restEncoding : BinaryLabelEncoding (DecomposedRest E Q))
    (divisionWitness : ModularDivision.StructuredCircuitWitness p) :
    BaseGateSameCircuitWitness (DecomposedState E Q) DecomposedState.slopeStep :=
  ((BaseGateSameCircuitWitness.prodRight restEncoding divisionWitness).relabel
    (DecomposedState.layout E Q)).congrStep (by
      intro s
      cases s
      rfl)

/-- A decomposed generic ECADD witness assembled from one structured MAU
division subcircuit and point-operation coordinate/target programs over the
same explicit encoding. -/
structure DecomposedWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) where
  /-- Encoding for the non-division point-operation fields. -/
  restEncoding : BinaryLabelEncoding (DecomposedRest E Q)
  /-- Structured MAU division witness used for the slope stage. -/
  divisionWitness : ModularDivision.StructuredCircuitWitness p
  /-- Program computing affine coordinates from the slope into result scratch. -/
  coordinateProgram :
    BaseGateProgram (slopeSameCircuit restEncoding divisionWitness).encoding.width
  /-- Correctness of the coordinate program under the decomposed encoding. -/
  coordinateRealizes :
    BaseGateProgram.Realizes (slopeSameCircuit restEncoding divisionWitness).encoding
      coordinateProgram DecomposedState.coordinateStep
  /-- Program adding result-coordinate scratch into the public targets. -/
  targetProgram :
    BaseGateProgram (slopeSameCircuit restEncoding divisionWitness).encoding.width
  /-- Correctness of the target-write program under the decomposed encoding. -/
  targetRealizes :
    BaseGateProgram.Realizes (slopeSameCircuit restEncoding divisionWitness).encoding
      targetProgram DecomposedState.targetStep

namespace DecomposedWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- The common encoding used by every subprogram in the decomposed ECADD
witness. -/
def encoding (w : DecomposedWitness E Q) :
    BinaryLabelEncoding (DecomposedState E Q) :=
  (slopeSameCircuit w.restEncoding w.divisionWitness).encoding

/-- The structured slope subcircuit lifted from modular division. -/
def slopeWitness (w : DecomposedWitness E Q) :
    BaseGateSameCircuitWitness (DecomposedState E Q) DecomposedState.slopeStep :=
  slopeSameCircuit w.restEncoding w.divisionWitness

@[simp] theorem slopeWitness_encoding (w : DecomposedWitness E Q) :
    w.slopeWitness.encoding = w.encoding :=
  rfl

/-- Folded program for the decomposed generic ECADD witness. -/
def program (w : DecomposedWitness E Q) :
    BaseGateProgram w.encoding.width :=
  BaseGateProgram.appendList
    [ w.slopeWitness.program,
      w.coordinateProgram,
      w.targetProgram,
      BaseGateProgram.inverse w.coordinateProgram,
      BaseGateProgram.inverse w.slopeWitness.program ]

/-- The folded decomposed program realizes the five-stage ECADD semantic
action. -/
theorem realizes (w : DecomposedWitness E Q) :
    BaseGateProgram.Realizes w.encoding w.program DecomposedState.fullStep := by
  dsimp [program, encoding, DecomposedState.fullStep, DecomposedState.stageSteps,
    slopeWitness]
  have huncoordinate :
      BaseGateProgram.Realizes (slopeSameCircuit w.restEncoding w.divisionWitness).encoding
        (BaseGateProgram.inverse w.coordinateProgram) DecomposedState.uncoordinateStep :=
    BaseGateProgram.Realizes.inverse_of_rightInverse
      w.coordinateRealizes DecomposedState.coordinateStep_uncoordinateStep
  have hunslope :
      BaseGateProgram.Realizes (slopeSameCircuit w.restEncoding w.divisionWitness).encoding
        (BaseGateProgram.inverse w.slopeWitness.program) DecomposedState.unslopeStep := by
    exact
      BaseGateProgram.Realizes.inverse_of_rightInverse
        w.slopeWitness.realizes DecomposedState.slopeStep_unslopeStep
  exact
    BaseGateProgram.Realizes.appendList
      (slopeSameCircuit w.restEncoding w.divisionWitness).encoding
      [ w.slopeWitness.program,
        w.coordinateProgram,
        w.targetProgram,
        BaseGateProgram.inverse w.coordinateProgram,
        BaseGateProgram.inverse w.slopeWitness.program ]
      [ DecomposedState.slopeStep,
        DecomposedState.coordinateStep,
        DecomposedState.targetStep,
        DecomposedState.uncoordinateStep,
        DecomposedState.unslopeStep ]
      (by
        constructor
        · exact (slopeSameCircuit w.restEncoding w.divisionWitness).realizes
        constructor
        · exact w.coordinateRealizes
        constructor
        · exact w.targetRealizes
        constructor
        · exact huncoordinate
        constructor
        · exact hunslope
        · constructor)

/-- Same-Circuit witness for the full decomposed generic ECADD program. -/
def sameCircuit (w : DecomposedWitness E Q) :
    BaseGateSameCircuitWitness (DecomposedState E Q) DecomposedState.fullStep where
  encoding := w.encoding
  program := w.program
  realizes := w.realizes

/-- The decomposed generic ECADD circuit history bottoms out in base gates. -/
theorem structured (w : DecomposedWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.sameCircuit

/-- Encoded-basis correctness for all decomposed generic ECADD labels. -/
theorem apply_ket (w : DecomposedWitness E Q) (x : DecomposedState E Q) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.fullStep x)) :
        StateVector (Qubits w.encoding.width)) :=
  BaseGateSameCircuitWitness.apply_encoded_ket w.sameCircuit x

/-- Clean encoded-basis action for the decomposed generic ECADD program. -/
theorem apply_clean_ket (w : DecomposedWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (DecomposedState.initial P targetX targetY)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.cleanOutput P targetX targetY)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [DecomposedState.fullStep_initial] using
    apply_ket w (DecomposedState.initial P targetX targetY)

/-- Clean decomposed output projects to the existing public generic ECADD
endpoint shape. -/
theorem cleanOutput_toData (P : Input E Q) (targetX targetY : ZMod p) :
    (DecomposedState.cleanOutput (E := E) (Q := Q) P targetX targetY).toData =
      ({ input := P
         targetX := targetX + genericAddX E P.1 Q
         targetY := targetY + genericAddY E P.1 Q
         flag := false } : Data E Q) :=
  rfl

/-- The clean decomposed output projects to the existing generic ECADD endpoint
map. -/
theorem cleanOutput_toData_eq_addIntoTarget
    (P : Input E Q) (targetX targetY : ZMod p) :
    (DecomposedState.cleanOutput (E := E) (Q := Q) P targetX targetY).toData =
      ({ input := P
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget :=
  rfl

/-- Resource counters are projected from the same decomposed generic ECADD
circuit used for correctness. -/
theorem resources_eq (w : DecomposedWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.sameCircuit

/-- Circuit depth is projected from the same decomposed generic ECADD circuit. -/
theorem depth_eq (w : DecomposedWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.sameCircuit

/-- Query depth is projected from the same decomposed generic ECADD circuit. -/
theorem queryDepth_eq (w : DecomposedWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.sameCircuit

/-- Resource-correct witness for the clean decomposed generic ECADD endpoint. -/
def cleanResourceCorrectWitness (w : DecomposedWitness E Q) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ P : Input E Q, ∀ targetX targetY : ZMod p,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (DecomposedState.initial P targetX targetY)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (DecomposedState.cleanOutput P targetX targetY)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.sameCircuit
  correctness := fun P targetX targetY => apply_clean_ket w P targetX targetY
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end DecomposedWitness

/-- Semantic update implemented by a gate-structured generic ECADD witness. -/
abbrev encodedStep {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} : Data E Q -> Data E Q :=
  Data.addIntoTarget

/-- Gate-structured encoded generic ECADD witness. -/
abbrev StructuredCircuitWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) :=
  BaseGateSameCircuitWitness (Data E Q) (encodedStep (E := E) (Q := Q))

namespace StructuredCircuitWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- The structured generic ECADD circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : StructuredCircuitWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w

/-- Encoded-basis correctness for all generic ECADD data labels. -/
theorem apply_ket (w : StructuredCircuitWitness E Q) (x : Data E Q) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addIntoTarget) :
        StateVector (Qubits w.encoding.width)) :=
  by
    simpa [encodedStep] using BaseGateSameCircuitWitness.apply_encoded_ket w x

/-- Clean public-form encoded-basis action for generic ECADD. -/
theorem apply_clean_ket (w : StructuredCircuitWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := P
               targetX := targetX
               targetY := targetY
               flag := false } : Data E Q)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := P
             targetX := targetX + genericAddX E P.1 Q
             targetY := targetY + genericAddY E P.1 Q
             flag := false } : Data E Q)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [encodedStep, Data.addIntoTarget] using
    apply_ket (E := E) (Q := Q) w
      ({ input := P, targetX := targetX, targetY := targetY, flag := false } :
        Data E Q)

/-- Resource counters are projected from the same structured generic ECADD circuit. -/
theorem resources_eq (w : StructuredCircuitWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w).resources =
      (BaseGateSameCircuitWitness.profile w).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w

/-- Circuit depth is projected from the same structured generic ECADD circuit. -/
theorem depth_eq (w : StructuredCircuitWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w).depth =
      (BaseGateSameCircuitWitness.profile w).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w

/-- Query depth is projected from the same structured generic ECADD circuit. -/
theorem queryDepth_eq (w : StructuredCircuitWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w).queryDepth =
      (BaseGateSameCircuitWitness.profile w).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w

/-- Resource-correct witness for the encoded generic ECADD statement. -/
def resourceCorrectWitness (w : StructuredCircuitWitness E Q) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ x : Data E Q,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w)
          ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode x.addIntoTarget) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w).resources =
          (BaseGateSameCircuitWitness.profile w).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w).depth =
          (BaseGateSameCircuitWitness.profile w).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w).queryDepth =
          (BaseGateSameCircuitWitness.profile w).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w
  correctness := apply_ket w
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end StructuredCircuitWitness

end GenericPointAddition

namespace ControlledPointAddition

/-- Explicit state for a decomposed controlled ECADD realization.  The
controlled wrapper carries the branch bit alongside the generic decomposed
state, whose slope substate is backed by the structured MAU division route. -/
structure DecomposedState (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) where
  /-- Control bit selecting whether the generic ECADD route is applied. -/
  control : Bool
  /-- Generic decomposed ECADD state used on the active branch. -/
  generic : GenericPointAddition.DecomposedState E Q
deriving DecidableEq

namespace DecomposedState

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- Public controlled-ECADD endpoint projection from the decomposed state. -/
def toData (s : DecomposedState E Q) : Data E Q where
  input := s.generic.input
  control := s.control
  targetX := s.generic.targetX
  targetY := s.generic.targetY
  flag := s.generic.flag

/-- Clean initial controlled decomposed state. -/
def initial (P : Input E Q) (control : Bool) (targetX targetY : ZMod p) :
    DecomposedState E Q where
  control := control
  generic := GenericPointAddition.DecomposedState.initial P targetX targetY

/-- Clean controlled output: inactive branches preserve the generic clean input,
and active branches run the generic decomposed ECADD route. -/
def cleanOutput (P : Input E Q) (control : Bool) (targetX targetY : ZMod p) :
    DecomposedState E Q where
  control := control
  generic :=
    if control then
      GenericPointAddition.DecomposedState.cleanOutput P targetX targetY
    else
      GenericPointAddition.DecomposedState.initial P targetX targetY

/-- Folded semantic action of a decomposed controlled ECADD circuit. -/
def fullStep (s : DecomposedState E Q) : DecomposedState E Q :=
  if s.control then
    { control := s.control
      generic := GenericPointAddition.DecomposedState.fullStep s.generic }
  else
    s

@[simp] theorem fullStep_initial_false (P : Input E Q)
    (targetX targetY : ZMod p) :
    fullStep (initial P false targetX targetY) =
      cleanOutput P false targetX targetY := by
  simp [fullStep, initial, cleanOutput]

@[simp] theorem fullStep_initial_true (P : Input E Q)
    (targetX targetY : ZMod p) :
    fullStep (initial P true targetX targetY) =
      cleanOutput P true targetX targetY := by
  simp [fullStep, initial, cleanOutput,
    GenericPointAddition.DecomposedState.fullStep_initial]

@[simp] theorem cleanOutput_false_toData (P : Input E Q)
    (targetX targetY : ZMod p) :
    (cleanOutput P false targetX targetY).toData =
      ({ input := P
         control := false
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q) :=
  rfl

/-- The inactive decomposed controlled branch projects to the existing
controlled ECADD endpoint map. -/
theorem cleanOutput_false_toData_eq_addIntoTarget (P : Input E Q)
    (targetX targetY : ZMod p) :
    (cleanOutput P false targetX targetY).toData =
      ({ input := P
         control := false
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget :=
  rfl

/-- The inactive folded decomposed controlled ECADD action, from clean input,
projects to the existing controlled ECADD endpoint map. -/
theorem fullStep_initial_false_toData_eq_addIntoTarget (P : Input E Q)
    (targetX targetY : ZMod p) :
    (fullStep (initial P false targetX targetY)).toData =
      ({ input := P
         control := false
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget := by
  rw [fullStep_initial_false]
  rfl

@[simp] theorem cleanOutput_true_toData (P : Input E Q)
    (targetX targetY : ZMod p) :
    (cleanOutput P true targetX targetY).toData =
      ({ input := P
         control := true
         targetX := targetX + genericAddX E P.1 Q
         targetY := targetY + genericAddY E P.1 Q
         flag := false } : Data E Q) :=
  rfl

/-- The active decomposed controlled branch projects to the existing controlled
ECADD endpoint map. -/
theorem cleanOutput_true_toData_eq_addIntoTarget (P : Input E Q)
    (targetX targetY : ZMod p) :
    (cleanOutput P true targetX targetY).toData =
      ({ input := P
         control := true
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget :=
  rfl

/-- The active folded decomposed controlled ECADD action, from clean input,
projects to the existing controlled ECADD endpoint map. -/
theorem fullStep_initial_true_toData_eq_addIntoTarget (P : Input E Q)
    (targetX targetY : ZMod p) :
    (fullStep (initial P true targetX targetY)).toData =
      ({ input := P
         control := true
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget := by
  rw [fullStep_initial_true]
  rfl

end DecomposedState

/-- Decomposed controlled ECADD witness.  The controlled program is derived
mechanically from the MAU-backed generic ECADD witness by lifting the generic
program between a control bit and a hidden clean work bit, then applying the
raw clean-work control decomposition. -/
structure DecomposedWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) where
  /-- MAU-backed generic ECADD witness used by the active branch. -/
  genericWitness : GenericPointAddition.DecomposedWitness E Q

namespace DecomposedWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- Uncontrolled generic ECADD witness lifted between the outer control bit
and a hidden clean work bit. -/
def genericLiftedWitness (w : DecomposedWitness E Q) :
    BaseGateSameCircuitWitness
      ((Bool × GenericPointAddition.DecomposedState E Q) × Bool)
      (fun x =>
        ((x.1.1, GenericPointAddition.DecomposedState.fullStep x.1.2),
          x.2)) :=
  BaseGateSameCircuitWitness.prodLeft
    (BaseGateSameCircuitWitness.prodRight BinaryLabelEncoding.bool
      w.genericWitness.sameCircuit)
    BinaryLabelEncoding.bool

/-- Exact physical encoding used by the controlled decomposed circuit, including
the hidden clean work bit. -/
def baseEncoding (w : DecomposedWitness E Q) :
    BinaryLabelEncoding
      ((Bool × GenericPointAddition.DecomposedState E Q) × Bool) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
      w.genericWitness.encoding)
    BinaryLabelEncoding.bool

/-- Semantic controlled-state encoding.  The final Boolean component is an
internal clean work bit that is always initialized to `false` for semantic
labels. -/
def encoding (w : DecomposedWitness E Q) :
    BinaryLabelEncoding (DecomposedState E Q) where
  width := w.baseEncoding.width
  encode := fun s => w.baseEncoding.encode ((s.control, s.generic), false)
  encode_injective := by
    intro x y h
    have hxy := w.baseEncoding.encode_injective h
    cases x
    cases y
    cases hxy
    rfl

/-- Encoded bit selecting the controlled ECADD branch. -/
def controlBit (w : DecomposedWitness E Q) :
    EncodedBit w.baseEncoding :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
      w.genericWitness.encoding)
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
      w.genericWitness.encoding BinaryLabelEncoding.boolBit)

/-- Hidden clean work bit used to control-lift Toffoli stages. -/
def workBit (w : DecomposedWitness E Q) :
    EncodedBit w.baseEncoding :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
      w.genericWitness.encoding)
    BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit

/-- Physical wire of the outer control bit. -/
def controlWire (w : DecomposedWitness E Q) : Fin w.baseEncoding.width :=
  w.controlBit.wire

/-- Physical wire of the hidden clean work bit. -/
def workWire (w : DecomposedWitness E Q) : Fin w.baseEncoding.width :=
  w.workBit.wire

/-- Generic ECADD program lifted into the middle field between control and work. -/
def genericLiftedProgram (w : DecomposedWitness E Q) :
    BaseGateProgram w.baseEncoding.width :=
  BaseGateProgram.prodLeft (n := 1)
    (BaseGateProgram.prodRight (m := 1) w.genericWitness.program)

/-- The outer control wire and hidden work wire are physically distinct. -/
theorem controlWork_ne (w : DecomposedWitness E Q) :
    w.controlWire ≠ w.workWire := by
  intro h
  have hv := congrArg Fin.val h
  simp [controlWire, workWire, controlBit, workBit, baseEncoding,
    BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hv
  omega

/-- The lifted generic program never reads or writes the outer control wire. -/
theorem controlDisjoint (w : DecomposedWitness E Q) :
    ∀ op, op ∈ w.genericLiftedProgram ->
      BaseGateOp.wireDisjoint w.controlWire op := by
  intro op hop
  simp only [genericLiftedProgram, BaseGateProgram.prodLeft,
    BaseGateProgram.prodRight] at hop
  rcases List.mem_map.mp hop with ⟨innerOp, hinnerMem, hopEq⟩
  subst op
  rcases List.mem_map.mp hinnerMem with ⟨sourceOp, _hsource, hinnerEq⟩
  subst innerOp
  have hinner :
      BaseGateOp.wireDisjoint
        (BaseGateOp.prodLeftWire
          (n := w.genericWitness.encoding.width)
          BinaryLabelEncoding.boolBit.wire)
        (BaseGateOp.prodRight (m := 1) sourceOp) :=
    BaseGateOp.wireDisjoint_prodRight_leftWire
      BinaryLabelEncoding.boolBit.wire sourceOp
  simpa [controlWire, controlBit, baseEncoding, genericLiftedWitness,
    BaseGateSameCircuitWitness.prodLeft, BaseGateSameCircuitWitness.prodRight,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire,
    BaseGateOp.prodLeftWire] using
      BaseGateOp.wireDisjoint_prodLeft_of_wireDisjoint
        (n := 1) hinner

/-- The lifted generic program never reads or writes the hidden clean work wire. -/
theorem workDisjoint (w : DecomposedWitness E Q) :
    ∀ op, op ∈ w.genericLiftedProgram ->
      BaseGateOp.wireDisjoint w.workWire op := by
  intro op hop
  simp only [genericLiftedProgram, BaseGateProgram.prodLeft,
    BaseGateProgram.prodRight] at hop
  rcases List.mem_map.mp hop with ⟨innerOp, hinnerMem, hopEq⟩
  subst op
  rcases List.mem_map.mp hinnerMem with ⟨sourceOp, _hsource, hinnerEq⟩
  subst innerOp
  simpa [workWire, workBit, baseEncoding, genericLiftedWitness,
    BaseGateSameCircuitWitness.prodLeft, BaseGateSameCircuitWitness.prodRight,
    GenericPointAddition.DecomposedWitness.sameCircuit,
    GenericPointAddition.DecomposedWitness.encoding,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.prodRightWire,
    BaseGateOp.prodRightWire] using
      BaseGateOp.wireDisjoint_prodLeft_rightWire
        (m := 1 + w.genericWitness.encoding.width)
        BinaryLabelEncoding.boolBit.wire
        (BaseGateOp.prodRight (m := 1) sourceOp)

/-- Controlled folded program derived mechanically from the lifted generic
ECADD program. -/
def program (w : DecomposedWitness E Q) :
    BaseGateProgram w.encoding.width :=
  BaseGateProgram.controlledWithCleanWork w.controlWire w.workWire
    w.genericLiftedProgram w.controlDisjoint w.workDisjoint w.controlWork_ne

/-- The semantic encoding exposes the state control field on the outer control
wire. -/
theorem controlBit_get_encode (w : DecomposedWitness E Q)
    (s : DecomposedState E Q) :
    (w.encoding.encode s).val.testBit
        (WireAddress.bitIndex w.controlWire).val =
      s.control := by
  simpa [encoding, controlWire, controlBit, baseEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.boolBit] using
    w.controlBit.get_eq ((s.control, s.generic), false)

/-- The hidden work bit is clean on every semantic encoded label. -/
theorem workBit_get_encode (w : DecomposedWitness E Q)
    (s : DecomposedState E Q) :
    (w.encoding.encode s).val.testBit
        (WireAddress.bitIndex w.workWire).val =
      false := by
  simpa [encoding, workWire, workBit, baseEncoding,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.boolBit] using
    w.workBit.get_eq ((s.control, s.generic), false)

/-- The lifted generic program applies the generic decomposed ECADD step in the
middle register while preserving the outer control and hidden work bits. -/
theorem genericLiftedProgram_applyLabel (w : DecomposedWitness E Q)
    (control : Bool) (generic : GenericPointAddition.DecomposedState E Q) :
    BaseGateProgram.applyLabel w.genericLiftedProgram
        (w.baseEncoding.encode ((control, generic), false)) =
      w.baseEncoding.encode
        ((control, GenericPointAddition.DecomposedState.fullStep generic),
          false) := by
  have hright :
      BaseGateProgram.Realizes
        (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
          w.genericWitness.encoding)
        (BaseGateProgram.prodRight (m := 1) w.genericWitness.program)
        (fun x : Bool × GenericPointAddition.DecomposedState E Q =>
          (x.1, GenericPointAddition.DecomposedState.fullStep x.2)) :=
    BaseGateProgram.Realizes.prodRight
      (left := BinaryLabelEncoding.bool)
      (right := w.genericWitness.encoding)
      w.genericWitness.realizes
  have hleft :
      BaseGateProgram.Realizes w.baseEncoding w.genericLiftedProgram
        (fun x :
          (Bool × GenericPointAddition.DecomposedState E Q) × Bool =>
          ((x.1.1, GenericPointAddition.DecomposedState.fullStep x.1.2),
            x.2)) :=
    BaseGateProgram.Realizes.prodLeft
      (left := BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        w.genericWitness.encoding)
      (right := BinaryLabelEncoding.bool)
      hright
  simpa [genericLiftedProgram, baseEncoding] using
    hleft.applyLabel_eq ((control, generic), false)

/-- Correctness of the mechanically control-lifted decomposed controlled ECADD
program under the semantic encoding with hidden clean work. -/
theorem realizes (w : DecomposedWitness E Q) :
    BaseGateProgram.Realizes w.encoding w.program DecomposedState.fullStep where
  applyLabel_eq := by
    intro s
    cases hcontrol : s.control
    · have hfalse :=
        BaseGateProgram.applyLabel_controlledWithCleanWork_of_control_false
          w.controlWire w.workWire w.genericLiftedProgram
          w.controlDisjoint w.workDisjoint w.controlWork_ne
          (w.encoding.encode s)
          (by
            have hread := w.controlBit_get_encode s
            simpa [hcontrol] using hread)
      calc
        BaseGateProgram.applyLabel w.program (w.encoding.encode s) =
            w.encoding.encode s := by
          simpa [program, encoding] using hfalse
        _ = w.encoding.encode (DecomposedState.fullStep s) := by
          simp [DecomposedState.fullStep, hcontrol]
    · have htrue :=
        BaseGateProgram.applyLabel_controlledWithCleanWork_of_control_true
          w.controlWire w.workWire w.genericLiftedProgram
          w.controlDisjoint w.workDisjoint w.controlWork_ne
          (w.encoding.encode s)
          (by
            have hread := w.controlBit_get_encode s
            simpa [hcontrol] using hread)
          (by
            simpa using w.workBit_get_encode s)
      have hgeneric := w.genericLiftedProgram_applyLabel s.control s.generic
      have htrue' :
          BaseGateProgram.applyLabel w.program (w.encoding.encode s) =
            BaseGateProgram.applyLabel w.genericLiftedProgram
              (w.encoding.encode s) := by
        simpa [program, encoding] using htrue
      have hgeneric' :
          BaseGateProgram.applyLabel w.genericLiftedProgram
              (w.encoding.encode s) =
            w.encoding.encode (DecomposedState.fullStep s) := by
        simpa [encoding, DecomposedState.fullStep, hcontrol] using hgeneric
      exact htrue'.trans hgeneric'

/-- Same-Circuit witness for the decomposed controlled ECADD program. -/
def sameCircuit (w : DecomposedWitness E Q) :
    BaseGateSameCircuitWitness (DecomposedState E Q) DecomposedState.fullStep where
  encoding := w.encoding
  program := w.program
  realizes := w.realizes

/-- The decomposed controlled ECADD circuit history bottoms out in base gates. -/
theorem structured (w : DecomposedWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.sameCircuit

/-- Encoded-basis correctness for all decomposed controlled ECADD labels. -/
theorem apply_ket (w : DecomposedWitness E Q) (x : DecomposedState E Q) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.fullStep x)) :
        StateVector (Qubits w.encoding.width)) :=
  BaseGateSameCircuitWitness.apply_encoded_ket w.sameCircuit x

/-- Encoded zero-control branch for the decomposed controlled ECADD program. -/
theorem apply_zero_branch (w : DecomposedWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (DecomposedState.initial P false targetX targetY)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.cleanOutput P false targetX targetY)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [DecomposedState.fullStep_initial_false] using
    apply_ket w (DecomposedState.initial P false targetX targetY)

/-- Encoded one-control branch for the decomposed controlled ECADD program. -/
theorem apply_one_branch (w : DecomposedWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (DecomposedState.initial P true targetX targetY)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.cleanOutput P true targetX targetY)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [DecomposedState.fullStep_initial_true] using
    apply_ket w (DecomposedState.initial P true targetX targetY)

/-- Resource counters are projected from the same decomposed controlled ECADD
circuit used for branch correctness. -/
theorem resources_eq (w : DecomposedWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.sameCircuit

/-- Circuit depth is projected from the same decomposed controlled ECADD circuit. -/
theorem depth_eq (w : DecomposedWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.sameCircuit

/-- Query depth is projected from the same decomposed controlled ECADD circuit. -/
theorem queryDepth_eq (w : DecomposedWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.sameCircuit

/-- Resource-correct witness for the decomposed controlled ECADD branch
statements. -/
def branchResourceCorrectWitness (w : DecomposedWitness E Q) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      ((∀ P : Input E Q, ∀ targetX targetY : ZMod p,
          Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
            ((PureState.ket (R := Qubits w.encoding.width)
              (w.encoding.encode (DecomposedState.initial P false targetX targetY)) :
              PureState (Qubits w.encoding.width)) :
              StateVector (Qubits w.encoding.width)) =
            (PureState.ket (R := Qubits w.encoding.width)
              (w.encoding.encode (DecomposedState.cleanOutput P false targetX targetY)) :
              StateVector (Qubits w.encoding.width))) ∧
        (∀ P : Input E Q, ∀ targetX targetY : ZMod p,
          Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
            ((PureState.ket (R := Qubits w.encoding.width)
              (w.encoding.encode (DecomposedState.initial P true targetX targetY)) :
              PureState (Qubits w.encoding.width)) :
              StateVector (Qubits w.encoding.width)) =
            (PureState.ket (R := Qubits w.encoding.width)
              (w.encoding.encode (DecomposedState.cleanOutput P true targetX targetY)) :
              StateVector (Qubits w.encoding.width))))
      ((BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
          (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.sameCircuit
  correctness :=
    ⟨fun P targetX targetY => apply_zero_branch w P targetX targetY,
      fun P targetX targetY => apply_one_branch w P targetX targetY⟩
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end DecomposedWitness

/-- Semantic update implemented by a gate-structured controlled ECADD witness. -/
abbrev encodedStep {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} : Data E Q -> Data E Q :=
  Data.addIntoTarget

/-- Gate-structured encoded controlled ECADD witness. -/
abbrev StructuredCircuitWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) :=
  BaseGateSameCircuitWitness (Data E Q) (encodedStep (E := E) (Q := Q))

namespace StructuredCircuitWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- The structured controlled ECADD circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : StructuredCircuitWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w

/-- Encoded-basis correctness for all controlled ECADD data labels. -/
theorem apply_ket (w : StructuredCircuitWitness E Q) (x : Data E Q) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addIntoTarget) :
        StateVector (Qubits w.encoding.width)) :=
  by
    simpa [encodedStep] using BaseGateSameCircuitWitness.apply_encoded_ket w x

/-- Encoded zero-control branch: target registers are unchanged. -/
theorem apply_zero_branch (w : StructuredCircuitWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := P
               control := false
               targetX := targetX
               targetY := targetY
               flag := false } : Data E Q)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := P
             control := false
             targetX := targetX
             targetY := targetY
             flag := false } : Data E Q)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [encodedStep, Data.addIntoTarget] using
    apply_ket (E := E) (Q := Q) w
      ({ input := P
         control := false
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q)

/-- Encoded one-control branch: the generic affine update is applied. -/
theorem apply_one_branch (w : StructuredCircuitWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := P
               control := true
               targetX := targetX
               targetY := targetY
               flag := false } : Data E Q)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := P
             control := true
             targetX := targetX + genericAddX E P.1 Q
             targetY := targetY + genericAddY E P.1 Q
             flag := false } : Data E Q)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [encodedStep, Data.addIntoTarget] using
    apply_ket (E := E) (Q := Q) w
      ({ input := P
         control := true
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q)

/-- Resource counters are projected from the same structured controlled ECADD circuit. -/
theorem resources_eq (w : StructuredCircuitWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w).resources =
      (BaseGateSameCircuitWitness.profile w).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w

/-- Circuit depth is projected from the same structured controlled ECADD circuit. -/
theorem depth_eq (w : StructuredCircuitWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w).depth =
      (BaseGateSameCircuitWitness.profile w).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w

/-- Query depth is projected from the same structured controlled ECADD circuit. -/
theorem queryDepth_eq (w : StructuredCircuitWitness E Q) :
    (BaseGateSameCircuitWitness.circuit w).queryDepth =
      (BaseGateSameCircuitWitness.profile w).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w

/-- Resource-correct witness for the encoded controlled ECADD statement. -/
def resourceCorrectWitness (w : StructuredCircuitWitness E Q) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ x : Data E Q,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w)
          ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode x.addIntoTarget) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w).resources =
          (BaseGateSameCircuitWitness.profile w).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w).depth =
          (BaseGateSameCircuitWitness.profile w).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w).queryDepth =
          (BaseGateSameCircuitWitness.profile w).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w
  correctness := apply_ket w
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end StructuredCircuitWitness

end ControlledPointAddition

end

end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg
