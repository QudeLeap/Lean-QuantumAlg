/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix

/-!
# Literal controlled sparse-complement correction

The P-256 complement is `1 + 2^224 - 2^192 - 2^96`. Its four selected
increments and decrements use the existing quantum reduction control,
target word and borrowed addend bits. Decrements reverse the complete
actual increment instruction list, including every borrowed-bit repair.
The whole-word arithmetic readout is a separate interface.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

/-- Four actual controlled suffix traversals, in their physical execution order. -/
def sparseComplementGates : List (GateSpec encoding) :=
  suffixIncrementGates width le_rfl ++ suffixIncrementGates 32 (by decide) ++
    (suffixIncrementGates 64 (by decide)).reverse ++
      (suffixIncrementGates 160 (by decide)).reverse

/-- The literal correction program allocates no additional word or flag. -/
def sparseComplementProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty sparseComplementGates

/-- Exact composition of the four actual subsystem actions on the complete frame. -/
def sparseComplementStep (state : Registers) : Registers :=
  stepList (suffixIncrementGates 160 (by decide)).reverse
    (stepList (suffixIncrementGates 64 (by decide)).reverse
      (suffixIncrementStep 32 (by decide) (suffixIncrementStep width le_rfl state)))

lemma sparseComplementGates_step (state : Registers) :
    stepList sparseComplementGates state = sparseComplementStep state := by
  simp only [sparseComplementGates, stepList_append, suffixIncrementGates_step,
    sparseComplementStep]

/-- The same actual native instructions retain every amplitude and relative phase. -/
lemma sparseComplement_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding sparseComplementProgram environment sparseComplementStep :=
  realizesList_congrStep (QubitLayout.canonical _) .empty sparseComplementGates
    sparseComplementGates_step environment

/-- Reversing the actual correction restores the complete original joint label. -/
lemma sparseComplement_reverse_restores (state : Registers) :
    stepList sparseComplementGates.reverse (sparseComplementStep state) = state := by
  rw [← sparseComplementGates_step]
  exact stepList_reverse_stepList sparseComplementGates state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
