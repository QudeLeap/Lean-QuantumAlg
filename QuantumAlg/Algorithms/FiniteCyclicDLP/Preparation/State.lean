/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation

/-!
# Original range-uniform exponent states

The original mathematical state and its existing concrete view are independent
of the classical recovery layer. Their declarations and full names are retained.
-/

namespace QuantumAlg.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G]

namespace Canonical.BornBridge

/-- The exact source range-uniform state for either exponent register. -/
def exponentState (P : KnownOrderProblem G) :
    NormalizedVector (Qubits (orderWidth P)) :=
  rangeUniformState P.order (orderWidth P) P.order_pos
    (order_le_fourierModulus P)

@[simp] lemma exponentState_apply (P : KnownOrderProblem G)
    (index : Fin (2 ^ orderWidth P)) :
    exponentState P index =
      if index.val < P.order then invSqrtOrder P.order else 0 :=
  rfl

end Canonical.BornBridge

namespace Concrete.BornBridge

/-- The exact source range-uniform state for either exponent register. -/
def exponentState (P : KnownOrderProblem G) :
    NormalizedVector (Qubits (orderWidth P)) :=
  QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge.exponentState P

@[simp] lemma exponentState_apply (P : KnownOrderProblem G)
    (index : Fin (2 ^ orderWidth P)) :
    exponentState P index =
      if index.val < P.order then invSqrtOrder P.order else 0 :=
  QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge.exponentState_apply P index

end Concrete.BornBridge

end

end QuantumAlg.FiniteCyclicDLP
