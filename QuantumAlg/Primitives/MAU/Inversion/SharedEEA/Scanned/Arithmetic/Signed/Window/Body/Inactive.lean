/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Window.Body

/-!
# Inactive complete arithmetic on every finite address

An actual disabled native stage restores its moving flag for every
address, including out-of-range addresses and source width zero. The
whole six-stage body therefore needs no range premise when inactive.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSignedWindow

noncomputable section

open EncodedBit ArithmeticTemplate NumberTheory.SharedEEA

private lemma stageProgram_apply_disabled (width : Nat) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (stageProgram width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state)) := by
  cases stage with
  | preXor =>
      exact forwardProgram_apply_disabled width .preXor environment state clean zero disabled
  | descendingXor =>
      exact ArithmeticSigned.reverseProgram_apply_disabled width .pre
        environment state clean zero disabled
  | carry =>
      exact ArithmeticSigned.forwardProgram_apply_disabled width .carry
        environment state clean zero disabled
  | descendingUncompute =>
      exact reverseProgram_apply_disabled width .descendingUncompute
        environment state clean zero disabled
  | ascendingXor =>
      exact forwardProgram_apply_disabled width .ascendingXor
        environment state clean zero disabled
  | finalXor =>
      exact forwardProgram_apply_disabled width .finalXor environment state clean zero disabled

private lemma stagesProgram_apply_disabled (width : Nat) (selected : List Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (stagesProgram width selected).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state)) := by
  induction selected with
  | nil =>
      exact (UnitaryCircuit.Realizes.identityAt AlgorithmGate.model .empty
        (Scanned.encoding width) (QubitLayout.canonical _) environment).apply_encoded_ket state
  | cons stage rest ih =>
      rw [stagesProgram, UnitaryCircuit.applyNormalized_seq,
        stageProgram_apply_disabled width stage environment state clean zero disabled]
      exact ih

/-- The same complete original frame is retained on every disabled finite address. -/
lemma program_apply_disabled (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (program width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state)) :=
  stagesProgram_apply_disabled width ArithmeticWindow.stages environment state clean zero disabled

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSignedWindow
