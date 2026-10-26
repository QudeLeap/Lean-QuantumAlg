/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Lower
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Clean

/-!
# Literal native controlled comparison with the original helpers and reduction flag

One native Toffoli computes the two active controls into the second helper.
The full clean-low carry word is followed by the reversed lower native word,
one paid flag CNOT and the same Toffoli restoring that helper. The zero static
threshold selects literal identity. This is a native comparison construction;
no measured instrument is reversed [G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- One actual native Toffoli on the two excluded active controls and the original second helper. -/
def activePairGates (layout : Layout encoding width) : List (GateSpec encoding) :=
  [.toffoli layout.control layout.selector (layout.clean 1)
    (layout.wire_ne (by simp))
    (layout.wire_ne (by intro impossible; cases impossible))
    (layout.wire_ne (by intro impossible; cases impossible))]

/-- Actual native compute/full-carry/lower-uncompute/flag-toggle/uncompute comparison order. -/
def comparisonGates (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) : List (GateSpec encoding) :=
  if threshold = 0 then [] else
    layout.activePairGates ++
      (layout.comparisonLayout wide).cleanLowGates (-threshold) ++
        ((layout.comparisonLowerLayout wide).cleanLowGates
          ((-threshold).setWidth (width - 1))).reverse ++
          [.cnot (layout.clean 1) layout.flag
            (layout.wire_ne (by intro impossible; cases impossible))] ++ layout.activePairGates

/-- Compile exactly this native source word at the original physical qubit layout. -/
def comparisonProgram (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  programList physical oracles (layout.comparisonGates wide threshold)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
