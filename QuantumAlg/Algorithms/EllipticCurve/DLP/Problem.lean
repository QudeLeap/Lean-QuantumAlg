/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.EllipticCurve
public import QuantumAlg.Util.EllipticCurve
public import QuantumAlg.Util.FiniteCyclicDLP

/-!
# Elliptic-curve discrete-logarithm problem bridge

This module contains only the mathematical reduction from a certified
prime-field ECDLP instance to the known-order finite-cyclic DLP problem.  It is
independent of the quantum workspace representation and of endpoint resource
accounting.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ECDLP
namespace Canonical

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Known-order group problem induced by a prime-field elliptic-curve instance.

**Input.**
- A prime-field elliptic curve, a finite base point $P$ of known order $r$, and
  a target point $Q$ certified to lie in $\langle P\rangle$; all data is
  classical and no runtime register is supplied.
**Output.**
- The mathematically equivalent cyclic-group discrete-logarithm instance with
  generator $P$, target $Q$, and order $r$.
**Resource budget.**
- Classical operations: none; this mathematical reduction has no executable trace.
- Classical memory: none beyond the supplied mathematical data.
- Quantum resources and depth: none.
**Success.**
- A candidate $m$ is accepted exactly when $Q=[m]P$; no probabilistic run occurs.
**Source.**
- [PZ03, ecc.tex:448-462].
-/
@[expose] public def problem (I : ECDLPInstance E) :
    FiniteCyclicDLP.KnownOrderProblem (GroupPoint E) where
  generator := I.basePoint.toGroupPoint
  target := I.targetPoint.toGroupPoint
  target_mem_zpowers := by
    rcases I.target_mem_span with ⟨scalar, scalarSpec⟩
    rw [← scalarSpec]
    exact Subgroup.npow_mem_zpowers I.basePoint.toGroupPoint scalar.val
  order := I.subgroupOrder
  order_eq_orderOf := I.subgroupOrder_eq_orderOf
  order_ne_zero := Nat.ne_of_gt I.subgroupOrder_pos

/-- A canonical hidden scalar selected from the subgroup-membership promise. -/
def secret (I : ECDLPInstance E) : ZMod I.subgroupOrder :=
  Classical.choose I.target_mem_span

/-- The selected scalar satisfies the actual elliptic-curve group equation. -/
theorem secret_spec (I : ECDLPInstance E) :
    ECDLPInstance.CandidateScalar I (secret I) :=
  Classical.choose_spec I.target_mem_span

end

end Canonical
end ECDLP
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
