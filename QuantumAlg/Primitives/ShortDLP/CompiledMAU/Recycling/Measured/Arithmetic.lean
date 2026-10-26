/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Context
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Toffoli
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Coordinates
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Measurements
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Time

/-!
# Actual measured selected multiplication on the allocated recycling context

The arithmetic stage executes the literal forward MAC, original controlled
exchange and separately emitted negative inverse MAC. Its physical vent
results overwrite only the allocated reusable bank; chronological records
remain part of the real execution [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The original measured arithmetic word, on the exact allocated ordered physical systems. -/
def arithmetic (wide : 2 ≤ width) (modulus : BitVec width)
    (coefficient : (ZMod modulus.toNat)ˣ) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) false :=
  (Physical.layout width).multiplicationCircuit wide modulus
    (coefficient : ZMod modulus.toNat).val
    ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
    (Physical.qubits width) (context_wires base noQuantum m ell width)
    (ventCell base noQuantum m ell width)

/-- Every actual selected multiplication path inherits the original native Toffoli bound. -/
lemma arithmetic_toffoli_bound (wide : 2 ≤ width) (large : 5 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient : (ZMod modulus.toNat)ˣ)
    (path : (arithmetic base noQuantum m ell width wide modulus coefficient).Path) :
    ResourcePool.count (model := model) (.gate .toffoli)
      ((arithmetic base noQuantum m ell width wide modulus coefficient).resourcePool path) ≤
        28 * width ^ 2 - 45 * width :=
  Layout.multiplicationCircuit_toffoli_bound _ wide large modulus positive odd _ _
    (Physical.qubits width) (context_wires base noQuantum m ell width)
    (ventCell base noQuantum m ell width) path

/-- The actual selected multiplication keeps all paid H/reset/Z and native gate durations. -/
lemma arithmetic_quantumTime_bound (wide : 2 ≤ width) (large : 5 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient : (ZMod modulus.toNat)ˣ)
    (path : (arithmetic base noQuantum m ell width wide modulus coefficient).Path) :
    (arithmetic base noQuantum m ell width wide modulus coefficient).quantumTime path ≤
      160 * width ^ 2 - 255 * width :=
  Layout.multiplicationCircuit_quantumTime_bound _ wide large modulus positive odd _ _
    (Physical.qubits width) (context_wires base noQuantum m ell width)
    (ventCell base noQuantum m ell width) path

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
