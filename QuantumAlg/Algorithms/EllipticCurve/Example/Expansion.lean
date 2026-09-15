/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Example.Curve
import all QuantumAlg.Algorithms.EllipticCurve.DLP.OrderPreparation

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
def orderExpansion : ECDLP.Canonical.OrderExpansion canonicalProblem.order where
  s := 2
  ell := fun index => index.val
  ell_strict := fun _ _ ordered => ordered
  sum_powers := by
    norm_num [canonicalProblem, ECDLP.Canonical.problem, ecdLPInstance, subgroupOrder,
      Fin.sum_univ_succ]
  N_pos := ecdLPInstance.subgroupOrder_pos

end

end QuantumAlg.EllipticCurve.Example
