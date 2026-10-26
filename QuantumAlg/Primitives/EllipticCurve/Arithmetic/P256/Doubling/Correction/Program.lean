/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Program

/-! # Actual low-bit CNOT and complete high-suffix correction for doubling -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Correction

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private lemma reduction_low_ne : reductionBit.wire ≠ targetLow.wire := by
  intro same
  have positions := congrArg Fin.val same
  change width + width = width + (width - 1 - 0) at positions
  have positive : 0 < width := by decide
  omega

/-- The original reduction flag controls one actual target-LSB CNOT. -/
def correctionGates : List (GateSpec encoding) :=
  [.cnot reductionBit targetLow reduction_low_ne] ++
    suffixIncrementGates 32 (by decide) ++
      (suffixIncrementGates 64 (by decide)).reverse ++
        (suffixIncrementGates 160 (by decide)).reverse

def correctionProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty correctionGates

/-- Every incoming label has the literal native action, including both control branches. -/
def correctionStep (state : Registers) : Registers :=
  stepList (suffixIncrementGates 160 (by decide)).reverse
    (stepList (suffixIncrementGates 64 (by decide)).reverse
      (suffixIncrementStep 32 (by decide) (cnotStep reductionBit targetLow state)))

lemma correctionGates_step (state : Registers) :
    stepList correctionGates state = correctionStep state := by
  simp only [correctionGates, stepList_append, stepList, step, suffixIncrementGates_step,
    correctionStep, id_eq]

/-- The same native instructions preserve all relative phases and external references. -/
lemma correction_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding correctionProgram environment correctionStep :=
  realizesList_congrStep (QubitLayout.canonical _) .empty correctionGates
    correctionGates_step environment

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Correction
