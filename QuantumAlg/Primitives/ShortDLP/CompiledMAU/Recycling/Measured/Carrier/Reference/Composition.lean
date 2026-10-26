/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Carrier.Reference

/-!
# Chronological logical products beside the unchanged complete reference
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open scoped Kronecker

/-- Extending the identity retains every complete local/reference coordinate. -/
lemma sourceWithReference_one (Local Reference : Register) :
    sourceWithReference (1 : HilbertOperator Local) Reference = 1 := by
  rw [sourceWithReference_kronecker, Matrix.one_kronecker_one]

/-- Reference extension preserves the exact chronological order of arbitrary logical products. -/
lemma sourceWithReference_mul {Local : Register} (first second : HilbertOperator Local)
    (Reference : Register) :
    sourceWithReference (first * second) Reference =
      sourceWithReference first Reference * sourceWithReference second Reference := by
  simpa only [sourceWithReference_kronecker, Matrix.one_mul] using
    (Matrix.mul_kronecker_mul first second (1 : HilbertOperator Reference)
      (1 : HilbertOperator Reference))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
