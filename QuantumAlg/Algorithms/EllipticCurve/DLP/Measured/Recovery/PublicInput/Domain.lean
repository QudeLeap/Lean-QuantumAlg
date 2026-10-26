/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Frame
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points
import all QuantumAlg.Util.FiniteCyclicDLP

/-!
# The original local domain of borrowed public point inputs

Only the two caller-supplied point values are prescribed. The condition is
independent of a sampler, a prepared bank, recovery workspace or probability
proof, and imposes no condition on an external quantum reference.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
namespace Support

noncomputable section

open QuantumAlg.Execution
open QuantumAlg.FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)

/-- The local domain prescribes exactly the original two public point values. -/
def inputDomain (problem : KnownOrderProblem E.GroupPoint)
    (state : ExecutionState (Store (Recovery.PublicInput.frame E m))
      (Recovery.PublicInput.frame E m).register) : Prop :=
  ∀ stored, 0 < (state.block stored).mass →
    stored.read (Recovery.PublicInput.baseRef E m) =
        ECDLP.Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
      stored.read (Recovery.PublicInput.targetRef E m) =
        ECDLP.Canonical.Runtime.Context.pointValue E problem.target.toMathlib

private lemma frame_store_eq_of_borrowed_eq
    (first second : Store (Recovery.PublicInput.frame E m))
    (same : first.readBorrowedClassical = second.readBorrowedClassical) : first = second := by
  obtain ⟨firstTarget, firstBase, firstUnit⟩ := first
  obtain ⟨secondTarget, secondBase, secondUnit⟩ := second
  cases firstUnit
  cases secondUnit
  change CShape.Value.product firstTarget (.product firstBase .unit) =
    CShape.Value.product secondTarget (.product secondBase .unit) at same
  cases same
  rfl

end

end Support

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
