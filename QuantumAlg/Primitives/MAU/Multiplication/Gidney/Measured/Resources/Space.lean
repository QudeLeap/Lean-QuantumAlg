/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import QuantumAlg.Core.Execution.Circuit.Allocation

/-!
# Exact actual multiplier storage peaks on the complete original caller frame

The same actual fixed-context circuit preserves every original live storage
entry. All measured record cells belong to that caller frame and are reused
by subsequent rows. Its actual visited contexts therefore introduce no
hidden classical or quantum allocation [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Actual resident and auxiliary peaks equal the complete caller storage on every real path. -/
lemma multiplicationCircuit_spaces (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.multiplicationCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient inverseCoefficient
        physical sameWires output).Path) :
    (layout.multiplicationCircuit wide modulus coefficient inverseCoefficient
      physical sameWires output).peakResidentSpace path = ctx.residentSpace ∧
    (layout.multiplicationCircuit wide modulus coefficient inverseCoefficient
      physical sameWires output).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ path, Circuit.fixed_peakAuxiliarySpace _ path⟩

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
