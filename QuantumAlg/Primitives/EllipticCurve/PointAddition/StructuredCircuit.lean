/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Controlled

/-!
# Encoded point-addition circuits

This module provides point-addition-facing actual circuits for concrete
Toffoli/CNOT/X generic and controlled ECADD programs.  The generic affine route
follows Proos--Zalka [PZ03, ecc.tex:525-640], and the controlled-addition
boundary follows RNSL17 [RNSL17, ECDLP.tex:488-580,650-696].  Each domain
witness carries an actual `UnitaryCircuit` whose normalized encoded-basis action
implements the corresponding coordinate-target update, so the same object is
used for correctness and resource accounting.
-/

section

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
  division : MAU.Division.Data p
  /-- Temporary cleanup flag carried by the point-addition endpoint. -/
  flag : Bool
deriving DecidableEq

/-- Non-division fields of a decomposed generic ECADD state. -/
abbrev DecomposedRest (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) :=
  Input E Q × ZMod p × ZMod p × ZMod p × ZMod p × Bool

namespace DecomposedState

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- Product layout with the division substate isolated as the right component. -/
def layout (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) :
    DecomposedState E Q ≃ DecomposedRest E Q × MAU.Division.Data p where
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
  UnitaryCircuit.Realizes.stepList stageSteps

@[simp] theorem slopeStep_unslopeStep (s : DecomposedState E Q) :
    slopeStep (unslopeStep s) = s := by
  cases s
  simp [slopeStep, unslopeStep, MAU.Division.Data.addQuotientIntoTarget,
    MAU.Division.Data.subQuotientFromTarget, sub_eq_add_neg, add_assoc]

@[simp] theorem coordinateStep_uncoordinateStep (s : DecomposedState E Q) :
    coordinateStep (uncoordinateStep s) = s := by
  cases s
  simp [coordinateStep, uncoordinateStep, sub_eq_add_neg, add_assoc]

/-- Clean decomposed execution reaches the public generic ECADD endpoint and
cleans both point-operation scratch and the modular-division target. -/
theorem fullStep_initial (P : Input E Q) (targetX targetY : ZMod p) :
    fullStep (initial P targetX targetY) = cleanOutput P targetX targetY := by
  simp [fullStep, stageSteps, UnitaryCircuit.Realizes.stepList, initial,
    cleanOutput, slopeStep, coordinateStep, targetStep, uncoordinateStep,
    unslopeStep, MAU.Division.Data.addQuotientIntoTarget,
    MAU.Division.Data.subQuotientFromTarget,
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
    (divisionWitness : MAU.Division.StructuredCircuitWitness p) :
    BinaryLabelEncoding (DecomposedState E Q) :=
  (BinaryLabelEncoding.prod restEncoding divisionWitness.encoding).relabel
    (DecomposedState.layout E Q)

/-- Lift the actual modular-division circuit into the explicit slope substate
of a decomposed generic ECADD label. -/
def slopeProgram {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E}
    (restEncoding : BinaryLabelEncoding (DecomposedRest E Q))
    (divisionWitness : MAU.Division.StructuredCircuitWitness p) :
    UnitaryCircuit (Qubits
      (decomposedEncoding restEncoding divisionWitness).width) :=
  UnitaryCircuit.prodRight (m := restEncoding.width) divisionWitness.circuit

/-- The lifted modular-division circuit realizes the slope update. -/
theorem slope_realizes {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E}
    (restEncoding : BinaryLabelEncoding (DecomposedRest E Q))
    (divisionWitness : MAU.Division.StructuredCircuitWitness p) :
    UnitaryCircuit.Realizes (decomposedEncoding restEncoding divisionWitness)
      (slopeProgram restEncoding divisionWitness)
      DecomposedState.slopeStep := by
  have hproduct := UnitaryCircuit.Realizes.prodRight
    (left := restEncoding) (right := divisionWitness.encoding)
    divisionWitness.realizes
  have hrelabel := UnitaryCircuit.Realizes.relabel
    (DecomposedState.layout E Q) hproduct
  exact hrelabel.congrStep (by
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
  divisionWitness : MAU.Division.StructuredCircuitWitness p
  /-- Program computing affine coordinates from the slope into result scratch. -/
  coordinateProgram :
    UnitaryCircuit (Qubits (decomposedEncoding restEncoding divisionWitness).width)
  /-- Correctness of the coordinate program under the decomposed encoding. -/
  coordinateRealizes :
    UnitaryCircuit.Realizes (decomposedEncoding restEncoding divisionWitness)
      coordinateProgram DecomposedState.coordinateStep
  /-- Program adding result-coordinate scratch into the public targets. -/
  targetProgram :
    UnitaryCircuit (Qubits (decomposedEncoding restEncoding divisionWitness).width)
  /-- Correctness of the target-write program under the decomposed encoding. -/
  targetRealizes :
    UnitaryCircuit.Realizes (decomposedEncoding restEncoding divisionWitness)
      targetProgram DecomposedState.targetStep
  /-- Exact primitive gate list underlying the complete five-stage program. -/
  fullGates :
    List (EncodedBit.GateSpec
      (decomposedEncoding restEncoding divisionWitness))
  /-- Provenance tying the actual stage-folded program to the primitive list
  consumed by outer control lifting. -/
  fullProgram_eq_programList :
    [ slopeProgram restEncoding divisionWitness,
        coordinateProgram,
        targetProgram,
        coordinateProgram.dagger,
        (slopeProgram restEncoding divisionWitness).dagger ].foldr
      UnitaryCircuit.seq
        (UnitaryCircuit.identity
          (Qubits (decomposedEncoding restEncoding divisionWitness).width)
          [] (by simp)) =
      EncodedBit.GateSpec.programList fullGates

namespace DecomposedWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- The common encoding used by every subprogram in the decomposed ECADD
witness. -/
abbrev encoding (w : DecomposedWitness E Q) :
    BinaryLabelEncoding (DecomposedState E Q) :=
  decomposedEncoding w.restEncoding w.divisionWitness

/-- Folded program for the decomposed generic ECADD witness. -/
def program (w : DecomposedWitness E Q) :
    UnitaryCircuit (Qubits w.encoding.width) :=
  [ slopeProgram w.restEncoding w.divisionWitness,
      w.coordinateProgram,
      w.targetProgram,
      w.coordinateProgram.dagger,
      (slopeProgram w.restEncoding w.divisionWitness).dagger ].foldr
    UnitaryCircuit.seq (UnitaryCircuit.identity (Qubits w.encoding.width) [] (by simp))

/-- The actual five-stage generic ECADD program is exactly the circuit folded
from its recorded primitive gate list. -/
theorem program_eq_programList (w : DecomposedWitness E Q) :
    w.program = EncodedBit.GateSpec.programList w.fullGates := by
  simpa only [program] using w.fullProgram_eq_programList

/-- The folded decomposed program realizes the five-stage ECADD semantic
action. -/
theorem realizes (w : DecomposedWitness E Q) :
    UnitaryCircuit.Realizes w.encoding w.program DecomposedState.fullStep := by
  dsimp [program, DecomposedState.fullStep, DecomposedState.stageSteps]
  have huncoordinate :
      UnitaryCircuit.Realizes w.encoding w.coordinateProgram.dagger
        DecomposedState.uncoordinateStep :=
    UnitaryCircuit.Realizes.dagger_of_rightInverse
      w.coordinateRealizes DecomposedState.coordinateStep_uncoordinateStep
  have hunslope :
      UnitaryCircuit.Realizes w.encoding
        (slopeProgram w.restEncoding w.divisionWitness).dagger
        DecomposedState.unslopeStep := by
    exact
      UnitaryCircuit.Realizes.dagger_of_rightInverse
        (slope_realizes w.restEncoding w.divisionWitness)
        DecomposedState.slopeStep_unslopeStep
  exact
    UnitaryCircuit.Realizes.appendList w.encoding
      [ slopeProgram w.restEncoding w.divisionWitness,
        w.coordinateProgram,
        w.targetProgram,
        w.coordinateProgram.dagger,
        (slopeProgram w.restEncoding w.divisionWitness).dagger ]
      [ DecomposedState.slopeStep,
        DecomposedState.coordinateStep,
        DecomposedState.targetStep,
        DecomposedState.uncoordinateStep,
        DecomposedState.unslopeStep ]
      (by
        constructor
        · exact slope_realizes w.restEncoding w.divisionWitness
        constructor
        · exact w.coordinateRealizes
        constructor
        · exact w.targetRealizes
        constructor
        · exact huncoordinate
        constructor
        · exact hunslope
        · constructor)

/-- The recorded primitive list has the same folded semantic action as the
actual generic ECADD program. -/
theorem fullGates_step (w : DecomposedWitness E Q)
    (x : DecomposedState E Q) :
    EncodedBit.GateSpec.stepList w.fullGates x =
      DecomposedState.fullStep x := by
  have hlist :=
    (EncodedBit.GateSpec.realizesList w.fullGates).apply_encoded_ket x
  have hfull :
      UnitaryCircuit.Realizes w.encoding
        (EncodedBit.GateSpec.programList w.fullGates)
        DecomposedState.fullStep := by
    rw [← w.program_eq_programList]
    exact w.realizes
  have hket := hlist.symm.trans (hfull.apply_encoded_ket x)
  exact w.encoding.encode_injective (NormalizedVector.ket_injective hket)

/-- Encoded-basis correctness for all decomposed generic ECADD labels. -/
theorem apply_ket (w : DecomposedWitness E Q) (x : DecomposedState E Q) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x)) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.fullStep x)) :=
  w.realizes.apply_encoded_ket x

/-- Clean encoded-basis action for the decomposed generic ECADD program. -/
theorem apply_clean_ket (w : DecomposedWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (DecomposedState.initial P targetX targetY))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.cleanOutput P targetX targetY)) := by
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


end DecomposedWitness

/-- Semantic update implemented by a gate-structured generic ECADD witness. -/
abbrev encodedStep {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} : Data E Q -> Data E Q :=
  Data.addIntoTarget

/-- Domain-specific generic ECADD witness tied to one actual circuit and its
public encoded-basis endpoint. -/
structure StructuredCircuitWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) where
  /-- Faithful encoding of generic ECADD labels. -/
  encoding : BinaryLabelEncoding (Data E Q)
  /-- Actual generic ECADD circuit. -/
  circuit : UnitaryCircuit (Qubits encoding.width)
  /-- Direct realization of the public generic ECADD update. -/
  realizes : UnitaryCircuit.Realizes encoding circuit
    (encodedStep (E := E) (Q := Q))

namespace StructuredCircuitWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- Encoded-basis correctness for all generic ECADD data labels. -/
theorem apply_ket (w : StructuredCircuitWitness E Q) (x : Data E Q) :
    w.circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x)) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addIntoTarget) :=
  by
    simpa [encodedStep] using w.realizes.apply_encoded_ket x

/-- Clean public-form encoded-basis action for generic ECADD. -/
theorem apply_clean_ket (w : StructuredCircuitWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    w.circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := P
               targetX := targetX
               targetY := targetY
               flag := false } : Data E Q))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := P
             targetX := targetX + genericAddX E P.1 Q
             targetY := targetY + genericAddY E P.1 Q
             flag := false } : Data E Q)) := by
  simpa [encodedStep, Data.addIntoTarget] using
    apply_ket (E := E) (Q := Q) w
      ({ input := P, targetX := targetX, targetY := targetY, flag := false } :
        Data E Q)


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

/-- Product layout exposing the leading control and generic decomposed state. -/
def layout (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) :
    DecomposedState E Q ≃
      Bool × GenericPointAddition.DecomposedState E Q where
  toFun := fun s => (s.control, s.generic)
  invFun := fun x => { control := x.1, generic := x.2 }
  left_inv := by intro s; cases s; rfl
  right_inv := by intro x; cases x; rfl

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
mechanically from the MAU-backed generic ECADD gate list by lifting it between
an outer control bit and a hidden clean work bit. -/
structure DecomposedWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) where
  /-- MAU-backed generic ECADD witness used by the active branch. -/
  genericWitness : GenericPointAddition.DecomposedWitness E Q

namespace DecomposedWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- Exact physical encoding used by the controlled decomposed circuit,
including the trailing hidden clean work bit. -/
abbrev baseEncoding (w : DecomposedWitness E Q) :
    BinaryLabelEncoding
      ((Bool × GenericPointAddition.DecomposedState E Q) × Bool) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
      w.genericWitness.encoding)
    BinaryLabelEncoding.bool

/-- Embed a semantic controlled state into the physical carrier with clean
hidden work. -/
def cleanCarrier (s : DecomposedState E Q) :
    (Bool × GenericPointAddition.DecomposedState E Q) × Bool :=
  ((s.control, s.generic), false)

/-- Semantic controlled-state encoding.  The final physical Boolean is hidden
from the semantic label and is always encoded as clean. -/
abbrev encoding (w : DecomposedWitness E Q) :
    BinaryLabelEncoding (DecomposedState E Q) where
  width := w.baseEncoding.width
  encode := fun s => w.baseEncoding.encode (cleanCarrier s)
  encode_injective := by
    intro x y h
    have hxy := w.baseEncoding.encode_injective h
    rcases x with ⟨xControl, xGeneric⟩
    rcases y with ⟨yControl, yGeneric⟩
    change ((xControl, xGeneric), false) =
      ((yControl, yGeneric), false) at hxy
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

/-- Hidden clean work bit used by the exact Toffoli control expansion. -/
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

/-- Generic primitive gates lifted into the middle field between the outer
control and hidden work bits. -/
def genericLiftedGates (w : DecomposedWitness E Q) :
    List (EncodedBit.GateSpec w.baseEncoding) :=
  (w.genericWitness.fullGates.map
    (EncodedBit.GateSpec.prodRight BinaryLabelEncoding.bool)).map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)

/-- The outer control bit and hidden work bit are physically distinct. -/
theorem controlBit_workBit_ne (w : DecomposedWitness E Q) :
    w.controlBit.wire ≠ w.workBit.wire := by
  simpa only [controlBit, workBit] using
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        w.genericWitness.encoding)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
        w.genericWitness.encoding BinaryLabelEncoding.boolBit)).symm

/-- Physical-wire form of control/work separation. -/
theorem controlWork_ne (w : DecomposedWitness E Q) :
    w.controlWire ≠ w.workWire := by
  simpa only [controlWire, workWire] using w.controlBit_workBit_ne

/-- Every lifted generic gate is disjoint from the outer control bit. -/
theorem controlDisjoint (w : DecomposedWitness E Q) :
    ∀ gate, gate ∈ w.genericLiftedGates →
      EncodedBit.GateSpec.bitDisjoint w.controlBit gate := by
  intro gate hgate
  unfold genericLiftedGates at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, hinner, rfl⟩
  rcases List.mem_map.mp hinner with ⟨sourceGate, _hsource, rfl⟩
  have hright := EncodedBit.GateSpec.bitDisjoint_prodRight_leftBit
    BinaryLabelEncoding.bool w.genericWitness.encoding
    BinaryLabelEncoding.boolBit sourceGate
  simpa only [controlBit] using
    EncodedBit.GateSpec.bitDisjoint_prodLeft_of_bitDisjoint
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
        w.genericWitness.encoding BinaryLabelEncoding.boolBit)
      (EncodedBit.GateSpec.prodRight BinaryLabelEncoding.bool sourceGate)
      hright

/-- Every lifted generic gate is disjoint from the hidden clean work bit. -/
theorem workDisjoint (w : DecomposedWitness E Q) :
    ∀ gate, gate ∈ w.genericLiftedGates →
      EncodedBit.GateSpec.bitDisjoint w.workBit gate := by
  intro gate hgate
  unfold genericLiftedGates at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, hinner, rfl⟩
  rcases List.mem_map.mp hinner with ⟨sourceGate, _hsource, rfl⟩
  simpa only [workBit] using
    EncodedBit.GateSpec.bitDisjoint_prodLeft_rightBit
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
        w.genericWitness.encoding)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit
      (EncodedBit.GateSpec.prodRight BinaryLabelEncoding.bool sourceGate)

/-- Lifting the generic gate list preserves its folded action in the middle
register and preserves both surrounding Boolean fields. -/
theorem genericLiftedGates_step (w : DecomposedWitness E Q)
    (x : (Bool × GenericPointAddition.DecomposedState E Q) × Bool) :
    EncodedBit.GateSpec.stepList w.genericLiftedGates x =
      ((x.1.1,
        GenericPointAddition.DecomposedState.fullStep x.1.2), x.2) := by
  unfold genericLiftedGates
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rw [EncodedBit.GateSpec.stepList_prodRight]
  rw [w.genericWitness.fullGates_step]

/-- Exact clean-work control expansion of the lifted generic gate list. -/
def gates (w : DecomposedWitness E Q) :
    List (EncodedBit.GateSpec w.baseEncoding) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    w.controlBit w.workBit w.genericLiftedGates
    w.controlDisjoint w.workDisjoint w.controlBit_workBit_ne

/-- Folded semantic action of the exact controlled gate list on the complete
physical carrier. -/
def baseStep (w : DecomposedWitness E Q) :
    ((Bool × GenericPointAddition.DecomposedState E Q) × Bool) →
      ((Bool × GenericPointAddition.DecomposedState E Q) × Bool) :=
  EncodedBit.GateSpec.controlledListWithWorkStep
    w.controlBit w.workBit w.genericLiftedGates
    w.controlDisjoint w.workDisjoint w.controlBit_workBit_ne

/-- Controlled program compiled directly from the exact expanded gate list. -/
def program (w : DecomposedWitness E Q) :
    UnitaryCircuit (Qubits w.baseEncoding.width) :=
  EncodedBit.GateSpec.programList w.gates

/-- The semantic encoding exposes the state control field on the outer control
wire. -/
theorem controlBit_get_encode (w : DecomposedWitness E Q)
    (s : DecomposedState E Q) :
    (w.encoding.encode s).val.testBit
        (WireAddress.bitIndex w.controlWire).val =
      s.control := by
  simpa [encoding, cleanCarrier, controlWire, controlBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.boolBit] using
    w.controlBit.get_eq (cleanCarrier s)

/-- Every semantic label initializes the hidden work wire to `false`. -/
theorem workBit_get_encode (w : DecomposedWitness E Q)
    (s : DecomposedState E Q) :
    (w.encoding.encode s).val.testBit
        (WireAddress.bitIndex w.workWire).val = false := by
  simpa [encoding, cleanCarrier, workWire, workBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.boolBit] using
    w.workBit.get_eq (cleanCarrier s)

/-- Correctness of the exact controlled gate list on the complete physical
carrier. -/
theorem base_realizes (w : DecomposedWitness E Q) :
    UnitaryCircuit.Realizes w.baseEncoding w.program w.baseStep := by
  simpa only [program, gates, baseStep] using
    EncodedBit.GateSpec.controlledListWithWorkWitness
      w.controlBit w.workBit w.genericLiftedGates
      w.controlDisjoint w.workDisjoint w.controlBit_workBit_ne

/-- On a clean hidden-work input, the exact controlled list either preserves
the complete carrier or runs the lifted generic gate list and restores work. -/
theorem baseStep_clean (w : DecomposedWitness E Q)
    (control : Bool)
    (generic : GenericPointAddition.DecomposedState E Q) :
    w.baseStep ((control, generic), false) =
      ((control,
        if control then
          GenericPointAddition.DecomposedState.fullStep generic
        else generic), false) := by
  cases control
  · change w.baseStep ((false, generic), false) = ((false, generic), false)
    simpa only [baseStep] using
      EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
        w.controlBit w.workBit w.genericLiftedGates
        w.controlDisjoint w.workDisjoint w.controlBit_workBit_ne
        ((false, generic), false) (by rfl)
  · change w.baseStep ((true, generic), false) =
      ((true, GenericPointAddition.DecomposedState.fullStep generic), false)
    calc
      w.baseStep ((true, generic), false) =
          EncodedBit.GateSpec.stepList w.genericLiftedGates
            ((true, generic), false) :=
        by
          simpa only [baseStep] using
            EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
              w.controlBit w.workBit w.genericLiftedGates
              w.controlDisjoint w.workDisjoint w.controlBit_workBit_ne
              ((true, generic), false) (by rfl) (by rfl)
      _ = ((true,
          GenericPointAddition.DecomposedState.fullStep generic), false) :=
        w.genericLiftedGates_step ((true, generic), false)

/-- Correctness of the mechanically control-lifted decomposed ECADD program
under the semantic encoding with hidden clean work. -/
theorem realizes (w : DecomposedWitness E Q) :
    UnitaryCircuit.Realizes w.encoding w.program DecomposedState.fullStep where
  apply_encoded_ket := by
    intro s
    change
      w.program.applyNormalized
          (NormalizedVector.ket
            (w.baseEncoding.encode (cleanCarrier s))) =
        NormalizedVector.ket
          (w.baseEncoding.encode
            (cleanCarrier (DecomposedState.fullStep s)))
    calc
      w.program.applyNormalized
          (NormalizedVector.ket
            (w.baseEncoding.encode (cleanCarrier s))) =
        NormalizedVector.ket
          (w.baseEncoding.encode (w.baseStep (cleanCarrier s))) :=
        w.base_realizes.apply_encoded_ket (cleanCarrier s)
      _ = NormalizedVector.ket
          (w.baseEncoding.encode
            (cleanCarrier (DecomposedState.fullStep s))) := by
        apply congrArg (fun carrier =>
          NormalizedVector.ket (R := Qubits w.baseEncoding.width)
            (w.baseEncoding.encode carrier))
        rcases s with ⟨control, generic⟩
        cases control
        · change w.baseStep ((false, generic), false) =
            ((false, generic), false)
          exact w.baseStep_clean false generic
        · change w.baseStep ((true, generic), false) =
            ((true,
              GenericPointAddition.DecomposedState.fullStep generic), false)
          exact w.baseStep_clean true generic

/-- Encoded-basis correctness for all decomposed controlled ECADD labels. -/
theorem apply_ket (w : DecomposedWitness E Q) (x : DecomposedState E Q) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x)) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.fullStep x)) :=
  w.realizes.apply_encoded_ket x

/-- Encoded zero-control branch for the decomposed controlled ECADD program. -/
theorem apply_zero_branch (w : DecomposedWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (DecomposedState.initial P false targetX targetY))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.cleanOutput P false targetX targetY)) := by
  simpa [DecomposedState.fullStep_initial_false] using
    apply_ket w (DecomposedState.initial P false targetX targetY)

/-- Encoded one-control branch for the decomposed controlled ECADD program. -/
theorem apply_one_branch (w : DecomposedWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (DecomposedState.initial P true targetX targetY))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (DecomposedState.cleanOutput P true targetX targetY)) := by
  simpa [DecomposedState.fullStep_initial_true] using
    apply_ket w (DecomposedState.initial P true targetX targetY)


end DecomposedWitness

/-- Semantic update implemented by a gate-structured controlled ECADD witness. -/
abbrev encodedStep {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} : Data E Q -> Data E Q :=
  Data.addIntoTarget

/-- Domain-specific controlled ECADD witness tied to one actual circuit and its
public encoded-basis endpoint. -/
structure StructuredCircuitWitness (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) where
  /-- Faithful encoding of controlled ECADD labels. -/
  encoding : BinaryLabelEncoding (Data E Q)
  /-- Actual controlled ECADD circuit. -/
  circuit : UnitaryCircuit (Qubits encoding.width)
  /-- Direct realization of the public controlled ECADD update. -/
  realizes : UnitaryCircuit.Realizes encoding circuit
    (encodedStep (E := E) (Q := Q))

namespace StructuredCircuitWitness

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}

/-- Encoded-basis correctness for all controlled ECADD data labels. -/
theorem apply_ket (w : StructuredCircuitWitness E Q) (x : Data E Q) :
    w.circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x)) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addIntoTarget) :=
  by
    simpa [encodedStep] using w.realizes.apply_encoded_ket x

/-- Encoded zero-control branch: target registers are unchanged. -/
theorem apply_zero_branch (w : StructuredCircuitWitness E Q)
    (P : Input E Q) (targetX targetY : ZMod p) :
    w.circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := P
               control := false
               targetX := targetX
               targetY := targetY
               flag := false } : Data E Q))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := P
             control := false
             targetX := targetX
             targetY := targetY
             flag := false } : Data E Q)) := by
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
    w.circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := P
               control := true
               targetX := targetX
               targetY := targetY
               flag := false } : Data E Q))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := P
             control := true
             targetX := targetX + genericAddX E P.1 Q
             targetY := targetY + genericAddY E P.1 Q
             flag := false } : Data E Q)) := by
  simpa [encodedStep, Data.addIntoTarget] using
    apply_ket (E := E) (Q := Q) w
      ({ input := P
         control := true
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q)


end StructuredCircuitWitness

end ControlledPointAddition

end

end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
