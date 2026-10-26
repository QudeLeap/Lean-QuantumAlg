/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Blocks
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.SignQuotient

/-! # Actual scanned arithmetic blocks retain the complete original microstep actions -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

open EncodedBit

/-- The native scanned remainder block has the entire original prepared-Ctrl action. -/
lemma remainderProgram_apply_original (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (prefixZero : state.2.2.1 = 0) (borrowZero : state.2.2.2 = false)
    (addressZero : state.2.1 = 0) (control : state.1.control = false) :
    (ArithmeticBlocks.remainderProgram width positive).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (SharedEEA.ArithmeticBlocks.remainderStep width state.1,
          state.2))) := by
  rw [SharedEEA.ArithmeticBlocks.remainderStep_eq_source width state.1 control]
  exact ArithmeticBlocks.remainderProgram_apply_source width positive environment state
    prefixZero borrowZero addressZero control

/-- The actual scanned corrected Sign exchange and quotient word retain the original full action. -/
lemma signProgram_apply_original (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Data width) (addressZero : state.2.1 = 0) (prefixZero : state.2.2.1 = 0)
    (control : state.1.control = false) :
    (SignQuotient.program width).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (SharedEEA.SignQuotient.step width state.1, state.2))) := by
  rw [SharedEEA.SignQuotient.step_eq_sourceStep width state.1 control]
  exact SignQuotient.program_apply_source width environment state addressZero prefixZero control

/-- The native scanned coefficient block has the entire original prepared-Ctrl action. -/
lemma coefficientProgram_apply_original (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (prefixZero : state.2.2.1 = 0) (borrowZero : state.2.2.2 = false)
    (addressZero : state.2.1 = 0) (control : state.1.control = false) :
    (ArithmeticBlocks.coefficientProgram width positive).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (SharedEEA.ArithmeticBlocks.coefficientStep width state.1,
          state.2))) := by
  rw [SharedEEA.ArithmeticBlocks.coefficientStep_eq_source width state.1 control]
  exact ArithmeticBlocks.coefficientProgram_apply_source width positive environment state
    prefixZero borrowZero addressZero control

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep
