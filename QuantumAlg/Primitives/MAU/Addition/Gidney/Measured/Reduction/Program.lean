/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Circuit

/-!
# Literal measured clean-flag controlled modular-addition program

The same original flag selects each of two actual measured static additions.
Native comparisons compute its first value and clear its final value; one
paid Toffoli toggles it between the additions. The same original two helpers
and dirty outputs are reused. A zero static offset is literal identity.
No measured instrument is inverted [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open Execution EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The one actual middle Toffoli toggles the existing flag under both original active controls. -/
def toggleFlagGates (layout : Layout encoding width) : List (GateSpec encoding) :=
  [.toffoli layout.control layout.selector layout.flag
    (layout.wire_ne (by simp))
    (layout.wire_ne (by intro impossible; cases impossible))
    (layout.wire_ne (by intro impossible; cases impossible))]

/-- Actual comparison/addition/toggle/addition/comparison order, with reused original ports. -/
def modularWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) : List (Instruction encoding (width - 2)) :=
  if constant = 0 then [] else
    [.native (layout.comparisonGates wide (modulus - constant))] ++
      layout.adderLayout.adderWord wide constant ++ [.native layout.toggleFlagGates] ++
        layout.adderLayout.adderWord wide (constant - modulus) ++
          [.native (layout.comparisonGates wide constant)]

/-- Compile exactly that measured source word, reusing the caller's original finite record bank. -/
def modularCircuit (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2)) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  wordCircuit physical sameWires output (layout.modularWord wide modulus constant)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
