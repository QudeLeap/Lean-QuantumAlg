/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Example.Curve
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Expansion

/-!
# Literal preparation data for the order-seven example

The same certified subgroup order is `7 = 1 + 2 + 4`. Its increasing
binary expansion supplies the original literal preparation used by the
complete ECDLP endpoint; no sampling or recovery certificate is supplied.
-/

namespace QuantumAlg.EllipticCurve.Example

open PrimeFieldShortWeierstrass

noncomputable section

/-- The actual order-seven source preparation has set-bit exponents zero, one and two. -/
def orderExpansion : FiniteCyclicDLP.OrderExpansion ecdLPInstance.subgroupOrder where
  count := 3
  count_pos := by norm_num
  ell := fun index => index.val
  ell_strict := fun _ _ ordered => ordered
  sum_powers := by
    norm_num [ecdLPInstance, subgroupOrder, Fin.sum_univ_succ]

end

end QuantumAlg.EllipticCurve.Example
