/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Placement
import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Actual native gates, carry measurements and stored phase instructions

The static adder word compiles into the single execution AST. Vents execute
the accepted native H/MZ/write/read/reset word; phase instructions read those
actual stored outcomes and select a native Z or identity. The caller supplies
every existing record cell and the complete ordered physical-wire equality.
No child instruction allocates or releases storage [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

noncomputable section

open Execution

/-- A static adder instruction, with actual encoded gate arguments and record-cell index. -/
inductive Instruction {Data : Type} (encoding : BinaryLabelEncoding Data) (records : Nat) where
  | native (gates : List (EncodedBit.GateSpec encoding))
  | vent (target : EncodedBit encoding) (record : Fin records)
  | phase (target : EncodedBit encoding) (record : Fin records)

namespace Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Cast only the finite shape of the existing outcome cell for the same physical qubit. -/
def finiteOutput {dimension : ℕ+} (qubit : dimension = 2)
    (output : CWriteRef ctx (.finite 2)) : CWriteRef ctx (.finite dimension) :=
  Eq.mpr (congrArg (fun size : ℕ+ => CWriteRef ctx (.finite size)) qubit) output

/-- The selected stored outcome pays for one actual native Z exactly when it is one. -/
def phaseProgram (physical : QubitLayout encoding.width) (target : EncodedBit encoding)
    (outcome : Fin 2) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  if outcome = 1 then target.pauliZ physical oracles
  else UnitaryCircuit.identity AlgorithmGate.model oracles physical.toQuantum

/-- Compile one instruction on the same complete physical systems and existing record cells. -/
def circuit (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) :
    Instruction encoding records →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false
  | .native gates => .unitary (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout
      sameWires (EncodedBit.GateSpec.programList physical oracles gates))
  | .vent target record =>
      EncodedBit.MeasuredUncompute.placedCircuit target physical ctx sameWires
        (finiteOutput (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)
          (output record)) operations services false
  | .phase target record =>
      .branch (.storage (output record).toCStorageRef) fun value =>
        .unitary (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (phaseProgram physical target value.toFin))

/-- A static word executes its actual instructions in chronological source order. -/
def wordCircuit (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) :
    List (Instruction encoding records) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false
  | [] => .id (model := .quantum AlgorithmGate.model oracles operations services) ctx
  | first :: rest => (circuit (oracles := oracles) (operations := operations)
      (services := services) physical sameWires output first).seq
      (wordCircuit physical sameWires output rest)

end Instruction

end

end QuantumAlg.MAU.Addition.Gidney.Measured
