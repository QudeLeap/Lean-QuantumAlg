/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Program

/-!
# Actual measured modular multiplier with an explicitly paid inverse MAC

The literal program executes forward MAC, the original controlled physical
word swap and a separately emitted negative-inverse-coefficient MAC. Every
measured row retains its real Store/path history; no unitary dagger is
assigned to either instrument [VBE95, 9511018.tex:333-367;
G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The actual forward, controlled-swap, explicit-negative-inverse instruction word. -/
def multiplicationWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat) :
    List (Instruction encoding (width - 2)) :=
  layout.forwardMACWord wide modulus coefficient ++ [.native layout.swapWordGates] ++
    layout.inverseMACWord wide modulus inverseCoefficient

/-- The same actual measured word placed on the complete original physical frame and record bank. -/
def multiplicationCircuit (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2)) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  wordCircuit physical sameWires output
    (layout.multiplicationWord wide modulus coefficient inverseCoefficient)

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
