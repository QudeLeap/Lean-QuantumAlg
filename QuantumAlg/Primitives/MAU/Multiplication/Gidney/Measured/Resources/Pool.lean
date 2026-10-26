/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Toffoli
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Coordinates
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Measurements
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Pool

/-!
# Complete independent native allowance for the actual measured multiplier

All four coordinates bound the same actual forward MAC, native exchange
and explicit negative inverse MAC. Paid H/reset/Z and every physical MZ
remain in the allowance; there is no arithmetic operation or service query
inside this static generator [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Width-only separate native coordinate allowances for the original measured construction. -/
def multiplicationBudget (oracles : OracleModel) (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
  coordinatePool oracles operations services (28 * width ^ 2 - 45 * width)
    (108 * width ^ 2 - 178 * width) (24 * width ^ 2 - 32 * width) (4 * width * (width - 2))

/-- Every actual complete multiplier path satisfies the complete independent native pool bound. -/
lemma multiplicationCircuit_pool_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 5 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.multiplicationCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient inverseCoefficient
        physical sameWires output).Path) :
    (layout.multiplicationCircuit wide modulus coefficient inverseCoefficient
      physical sameWires output).resourcePool path ≤
        multiplicationBudget oracles operations services width := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output
      (layout.multiplicationWord wide modulus coefficient inverseCoefficient)).Path at path
  have actual := wordCircuit_pool_bound physical sameWires output
    (layout.multiplicationWord wide modulus coefficient inverseCoefficient) path
  have toffoli := multiplicationWord_toffoli_bound layout wide large modulus positive odd
    coefficient inverseCoefficient
  have other := multiplicationWord_coordinate_bounds layout wide (by omega) modulus
    coefficient inverseCoefficient
  have measured := multiplicationWord_measurement_bound layout wide modulus
    coefficient inverseCoefficient
  exact actual.trans (coordinatePool_mono toffoli other.1 other.2 measured)

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
