/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Hadamard.Layer.Matrix
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries

/-!
# Actual parallel Hadamards on the original result word

The committed native Hadamard bank is placed at the supplied distinct result
positions. Its full matrix includes the identity on every existing physical
complement coordinate, so no spectator initialization or separability is used.
The same actual placement retains its native single-qubit ledger and depth.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Inject the original ordered result positions into the complete existing physical frame. -/
def wordPosition (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire)) :
    Fin width ↪ Fin encoding.width :=
  ⟨fun index => (target.bit index).wire, distinct⟩

private lemma wordHadamard_dimensions (physical : QubitLayout encoding.width)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire)) (index : Fin width) :
    ((Gate.HadamardLayer.layout width).wire index).dimension =
      (physical.toQuantum.wire (wordPosition target distinct index)).dimension := rfl

/-- One physical parallel H bank on the original existing result systems. -/
def wordHadamardProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire)) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  UnitaryCircuit.placeAt (Gate.HadamardLayer.layout width) physical.toQuantum
    (wordPosition target distinct) (wordHadamard_dimensions physical target distinct)
    (Gate.HadamardLayer.circuit oracles width)

/-- Exact full-register H entries, retaining all unselected spectator coherences. -/
lemma wordHadamardProgram_matrix_entry (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (row column : physical.toQuantum.Basis) (environment : oracles.Interpretation) :
    (wordHadamardProgram physical oracles target distinct).matrix environment row column =
      (∏ index : Fin width, Gate.HOp (row (target.bit index).wire)
        (column (target.bit index).wire)) *
          (if physical.toQuantum.restrictComplementBasis
              (Finset.univ.map (wordPosition target distinct)) row =
            physical.toQuantum.restrictComplementBasis
              (Finset.univ.map (wordPosition target distinct)) column then 1 else 0) := by
  rw [wordHadamardProgram, UnitaryCircuit.placeAt_matrix, UnitaryCircuit.operatorAt_entry,
    Gate.HadamardLayer.hadamardLayer_circuit_matrix_entry]
  congr 1

/-- The exact native single-qubit multiplicity is the number of original result positions. -/
lemma wordHadamardProgram_eventCost (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire)) :
    (wordHadamardProgram physical oracles target distinct).eventCost = width •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rw [wordHadamardProgram, UnitaryCircuit.placeAt_eventCost,
    Gate.HadamardLayer.hadamardLayer_circuit_eventCost]

private lemma hadamardLayer_quantumTime (oracles : OracleModel) (width : Nat) :
    (Gate.HadamardLayer.circuit oracles width).evaluatedEventDepth Resource.Event.quantumDuration =
      if width = 0 then 0 else 1 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [Gate.HadamardLayer.circuit, UnitaryCircuit.castLayout_evaluatedEventDepth,
        UnitaryCircuit.tensor_native_evaluatedEventDepth]
      change max ((Gate.HadamardLayer.circuit oracles width).evaluatedEventDepth
        Resource.Event.quantumDuration) 1 = 1
      rw [ih]
      split <;> rfl

/-- Parallel native Hadamards have one quantum dependency for a nonempty original word. -/
lemma wordHadamardProgram_quantumTime (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire)) :
    (wordHadamardProgram physical oracles target distinct).evaluatedEventDepth
      Resource.Event.quantumDuration = if width = 0 then 0 else 1 := by
  rw [wordHadamardProgram, UnitaryCircuit.placeAt_evaluatedEventDepth, hadamardLayer_quantumTime]

end

end QuantumAlg.EncodedBit.WindowLookup
