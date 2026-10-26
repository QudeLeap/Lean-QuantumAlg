/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Carry
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Program
import all QuantumAlg.Primitives.MAU.Addition.TTK.Comparison

/-!
# Literal two-quantum-operand P-256 modular-addition body

The complete native program adds the two actual words with an XOR carry,
computes the sparse-complement carry, corrects the target under that same
flag and performs the actual operand comparison for flag cleanup. It uses
only the original two words and flag. Its canonical arithmetic and clean
output boundary are proved separately from this all-label composition.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

/-- The four literal native stages on the unchanged physical frame. -/
def additionGates : List (GateSpec encoding) :=
  MAU.Addition.TTK.overflowGates width ++ complementCarryGates ++
    sparseComplementGates ++ MAU.Addition.TTK.comparisonGates width

/-- No new resident word or work bit is allocated by the native body. -/
def additionProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty additionGates

/-- The exact all-label action, before imposing the canonical clean-flag boundary. -/
def additionStep (state : Registers) : Registers :=
  MAU.Addition.TTK.comparisonOutput
    (sparseComplementStep (complementCarryStep (MAU.Addition.TTK.overflowOutput state)))

lemma additionGates_step (state : Registers) :
    stepList additionGates state = additionStep state := by
  simp only [additionGates, stepList_append, MAU.Addition.TTK.ttkOverflow_step,
    complementCarryGates_step, sparseComplementGates_step, MAU.Addition.TTK.ttkComparison_step,
    additionStep]

/-- The actual complete native composition preserves every amplitude and phase. -/
lemma addition_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding additionProgram environment additionStep :=
  realizesList_congrStep (QubitLayout.canonical _) .empty additionGates
    additionGates_step environment

/-- Every actual instruction in the inverse is required for complete restoration. -/
lemma addition_reverse_restores (state : Registers) :
    stepList additionGates.reverse (additionStep state) = state := by
  rw [← additionGates_step]
  exact stepList_reverse_stepList additionGates state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
