/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Construction
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.Layout.Qubit

/-!
# Actual measured recycling qubits and complete original storage

The qubit count reads the dimensions of the same complete ordered physical
wires used by both measured exponent streams. Retained outputs and reused
vent results remain in the separate actual classical capacity ledger
[G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

/-- Every original allocated qubit belongs to the complete measured arithmetic frame. -/
lemma measuredContext_qubits :
    (context base noQuantum m ell width).residentSpace (.quantumSystems 2) = 2 * width + 4 := by
  rw [RuntimeCtx.residentSpace_quantumSystems]
  have dimensions := congrArg
    (fun wires : List QuantumWire => (wires.map QuantumWire.dimension).count 2)
    (context_wires base noQuantum m ell width)
  have same : (context base noQuantum m ell width).quantumLayout.dimensionCount 2 =
      (Physical.qubits width).toQuantum.dimensionCount 2 := by
    simpa only [QuantumLayout.wires, List.map_ofFn, Function.comp_def,
      QuantumLayout.dimensionCount, QuantumLayout.dimensions] using dimensions.symm
  rw [same]
  simp only [QuantumLayout.dimensionCount, QuantumLayout.dimensions]
  have actual :
      (fun index : Fin (Physical.encoding width).width =>
        ((Physical.qubits width).toQuantum.wire index).dimension) = fun _ => (2 : ℕ+) := by
    funext index
    rfl
  rw [actual, List.ofFn_const, List.count_replicate]
  rfl

/-- Both actual measured exponent streams retain exactly 2n+4 simultaneous physical qubits. -/
lemma measuredMember_qubits (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : (ZMod modulus.toNat)ˣ)
    (path : (member base noQuantum m ell width wide modulus generator target).Path) :
    (member base noQuantum m ell width wide modulus generator target).peakResidentSpace path
      (.quantumSystems 2) = 2 * width + 4 := by
  rw [Circuit.fixed_peakResidentSpace]
  exact measuredContext_qubits base noQuantum m ell width

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
