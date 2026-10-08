/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Probability
public import QuantumAlg.Core.Measure
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Util.Classical.TerminalDecode

/-!
# Pure recoverable phase outcome

A terminal phase word is recoverable when one source orbit coordinate certifies
the true order as a continued-fraction denominator. This mathematical event
does not depend on a circuit construction or a runtime distribution.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

/-- A phase outcome has a source-certified recoverable orbit coordinate. -/
def NativeRecoverableOutcome {G : Type*} [Monoid G] {t : Nat}
    (g : G) (r : Nat) (outcome : TerminalZMeasure.Outcome t) : Prop :=
  ∃ k : Fin r,
    orderFindingOutputSuccessEvent g
      (ClassicalAlgorithms.TerminalDecode.fullRegisterIndex outcome, k)

end QuantumAlg.OrderFinding.ShorSourceJoint
