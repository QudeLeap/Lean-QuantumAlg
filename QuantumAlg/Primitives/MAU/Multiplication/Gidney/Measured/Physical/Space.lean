/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Space
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.Layout.Qubit

/-!
# Actual closed qubit peak on the explicit complete physical multiplier frame

The proof reads the dimensions of the same complete ordered physical wire
records used by execution. Resident qubits include the original control,
both words, two helpers and flag. Existing classical record cells remain
counted in the caller's separate classical ledger [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical

noncomputable section

open Execution

variable {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Every actual path of the explicit complete physical program has exactly `2n+4` live qubits. -/
lemma multiplicationCircuit_qubits (width : Nat) (wide : 2 ≤ width) (modulus : BitVec width)
    (coefficient inverseCoefficient : Nat)
    (sameWires : (qubits width).toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : ((layout width).multiplicationCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient inverseCoefficient
        (qubits width) sameWires output).Path) :
    ((layout width).multiplicationCircuit wide modulus coefficient inverseCoefficient
      (qubits width) sameWires output).peakResidentSpace path (.quantumSystems 2) =
        2 * width + 4 := by
  rw [(Layout.multiplicationCircuit_spaces (layout width) wide modulus coefficient
    inverseCoefficient (qubits width) sameWires output path).1,
    RuntimeCtx.residentSpace_quantumSystems]
  have dimensions := congrArg
    (fun wires : List QuantumWire => (wires.map QuantumWire.dimension).count 2) sameWires
  have sameDimensions : ctx.quantumLayout.dimensionCount 2 =
      (qubits width).toQuantum.dimensionCount 2 := by
    simpa only [QuantumLayout.wires, List.map_ofFn, Function.comp_def,
      QuantumLayout.dimensionCount, QuantumLayout.dimensions] using dimensions.symm
  rw [sameDimensions]
  simp only [QuantumLayout.dimensionCount, QuantumLayout.dimensions]
  have actualDimensions :
      (fun index : Fin (encoding width).width => ((qubits width).toQuantum.wire index).dimension) =
        fun _ => (2 : ℕ+) := by
    funext index
    rfl
  rw [actualDimensions, List.ofFn_const, List.count_replicate]
  rfl

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical
