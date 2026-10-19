/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Analysis
import all QuantumAlg.Primitives.MAU.Multiplication.VBECircuit
import all QuantumAlg.Util.Order.Finding

/-!
# Order-finding to factoring mathematics

This module contains only the reusable number-theoretic reduction.  The later
factoring endpoint composes it with `OrderFinding.ShorSourceJoint.SourceNativeEndpoint.algorithm`
directly, so no detached circuit/resource witness is retained here.
-/

section

namespace QuantumAlg

noncomputable section

namespace OrderFinding

/-- A successful public-register order-finding source event and the standard
even-order hypotheses jointly provide the two nontrivial gcd factors.  Resource
accounting remains owned by the named order-finding algorithm. -/
lemma shorSourceJointGcdBridge
    {N n a t r : Nat}
    (D : ModularMultiplicationDomain N n)
    (hinput : OrderFinding.Input N a r)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2)
    (heven : Even r)
    (hleft : ¬ (a ^ (r / 2) - 1) ≡ 0 [MOD N])
    (hright : ¬ (a ^ (r / 2) + 1) ≡ 0 [MOD N]) :
    orderFindingOutputSuccessLowerBound r ≤
        orderFindingOutputSuccessMass
          (ZMod.unitOfCoprime a hinput.coprime)
          (orderFindingPublicOutcomeProbability t r) ∧
      (1 < Nat.gcd (a ^ (r / 2) - 1) N ∧
          Nat.gcd (a ^ (r / 2) - 1) N < N) ∧
      (1 < Nat.gcd (a ^ (r / 2) + 1) N ∧
          Nat.gcd (a ^ (r / 2) + 1) N < N) := by
  refine ⟨ShorSourceJoint.SourceAnalysis.sourceOutputSuccessLowerBound
    hinput hregister hupper, ?_⟩
  exact shor_gcd_bridge_of_input_order D hinput heven hleft hright

end OrderFinding

end

end QuantumAlg

end
