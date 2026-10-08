/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model
public import QuantumAlg.Util.Classical.Modular.Basic
public import QuantumAlg.Util.FiniteCyclicDLP

/-!
# The original public-order modulus for finite-cyclic recovery

The same known order and Fourier capacity determine the original modular
specification. This pure owner does not import execution, repetition or any
resource wrapper. No new admissibility certificate is supplied by callers.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical

noncomputable section

universe u

variable {G : Type u} [Group G]

open ClassicalAlgorithms ClassicalAlgorithms.Modular

/-- The modulus specification used by the nontrivial branch, constructed
solely from the public group order and its Fourier width. -/
@[expose] public def resourceModulusSpec (P : KnownOrderProblem G) (two_le : 2 ≤ P.order) :
    ModulusSpec (orderWidth P) where
  modulus := P.order
  two_le := two_le
  le_capacity := by
    simpa [ClassicalAlgorithms.modulus, fourierModulus] using
      order_le_fourierModulus P

end

end QuantumAlg.FiniteCyclicDLP.Canonical
