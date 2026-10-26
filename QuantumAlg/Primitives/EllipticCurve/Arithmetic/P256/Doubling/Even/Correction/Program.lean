/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Reverse

/-! # Literal sparse even correction controlled by the original low target bit -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

/-- Add `2^224`, subtract `2^192`, and subtract `2^96` using the same actual low-bit control. -/
def evenCorrectionGates : List (GateSpec encoding) :=
  evenSuffixGates 32 (by decide) ++
    (evenSuffixGates 64 (by decide)).reverse ++ (evenSuffixGates 160 (by decide)).reverse

def evenCorrectionProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty evenCorrectionGates

/-- All three actual selected actions retain the original unused complement. -/
def evenCorrectionStep (state : Registers) : Registers :=
  stepList (evenSuffixGates 160 (by decide)).reverse
    (stepList (evenSuffixGates 64 (by decide)).reverse
      (evenSuffixStep 32 (by decide) state))

lemma evenCorrectionGates_step (state : Registers) :
    stepList evenCorrectionGates state = evenCorrectionStep state := by
  rw [evenCorrectionGates, stepList_append, stepList_append, evenSuffixGates_step]
  rfl

/-- Literal native instructions realize the complete original-frame action. -/
lemma evenCorrection_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding evenCorrectionProgram environment evenCorrectionStep :=
  realizesList_congrStep (QubitLayout.canonical _) .empty evenCorrectionGates
    evenCorrectionGates_step environment

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
