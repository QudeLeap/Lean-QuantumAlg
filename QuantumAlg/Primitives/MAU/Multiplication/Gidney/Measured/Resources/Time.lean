/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Toffoli
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Coordinates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Time

/-!
# Quantum time of the actual measured forward/exchange/negative-inverse multiplier

All paid H/reset/Z and native X/CNOT/Toffoli instructions come from the same
actual chronological circuit. Physical measurement has zero default quantum
duration. This bound does not assert a parallel scheduling improvement
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

private lemma native_time_formula (large : 5 ≤ width) :
    (28 * width ^ 2 - 45 * width) + (108 * width ^ 2 - 178 * width) +
      (24 * width ^ 2 - 32 * width) = 160 * width ^ 2 - 255 * width := by
  have first : 45 * width ≤ 28 * width ^ 2 := by nlinarith
  have second : 178 * width ≤ 108 * width ^ 2 := by nlinarith
  have third : 32 * width ≤ 24 * width ^ 2 := by nlinarith
  have total : 255 * width ≤ 160 * width ^ 2 := by nlinarith
  omega

/-- Every actual path has the native time bound of its original measured arithmetic word. -/
lemma multiplicationCircuit_quantumTime_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 5 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (odd : modulus.getLsbD 0 = true) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.multiplicationCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient inverseCoefficient
        physical sameWires output).Path) :
    (layout.multiplicationCircuit wide modulus coefficient inverseCoefficient
      physical sameWires output).quantumTime path ≤ 160 * width ^ 2 - 255 * width := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output
      (layout.multiplicationWord wide modulus coefficient inverseCoefficient)).Path at path
  have actual := wordCircuit_quantumTime_bound physical sameWires output
    (layout.multiplicationWord wide modulus coefficient inverseCoefficient) path
  have toffoli := multiplicationWord_toffoli_bound layout wide large modulus positive odd
    coefficient inverseCoefficient
  have other := multiplicationWord_coordinate_bounds layout wide (by omega) modulus
    coefficient inverseCoefficient
  exact actual.trans ((Nat.add_le_add (Nat.add_le_add toffoli other.1) other.2).trans
    (Nat.le_of_eq (native_time_formula large)))

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
