/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Arithmetic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Seed

/-!
# The original quantum source preparation in the actual point instrument

These are the existing small fixed native source preparation and its
own adjoint. The labels include the entire original bank, arbitrary
binary numerical words, C/N/W, address and external reference. They
neither prepare classical point data nor reset a bad branch.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus InstrumentBranchAction referenceKet nativeOperator
  Window.sourceBlank Arithmetic.Call.clearedInitial

/-- The actual first native instrument prepares exactly the complete original initializer. -/
lemma sourceSeedInstrument_blank (store : Store ctx)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction environment
      (parameters.nativeFragmentInstrument environment
        (Window.suffixProgram Inversion.Seed.program))
      store () 1 (Window.sourceBlank input numerator flags address)
      (Arithmetic.Call.clearedInitial input numerator flags address) reference := by
  unfold InstrumentBranchAction
  rw [nativeFragmentInstrument_operator, one_smul]
  exact parameters.nativeOperator_original _ environment.quantum _ _
    (Window.sourceSeedProgram_blank environment.quantum input numerator flags address) reference

/-- The actual final adjoint clears its own complete source at the updated binary coordinates. -/
lemma sourceSeedInstrument_dagger (store : Store ctx)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction environment
      (parameters.nativeFragmentInstrument environment
        (Window.suffixProgram
          (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty))))
      store () 1 (Arithmetic.Call.clearedInitial input numerator flags address)
      (Window.sourceBlank input numerator flags address) reference := by
  unfold InstrumentBranchAction
  rw [nativeFragmentInstrument_operator, one_smul]
  exact parameters.nativeOperator_original _ environment.quantum _ _
    (Window.sourceSeedProgram_dagger environment.quantum input numerator flags address) reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
