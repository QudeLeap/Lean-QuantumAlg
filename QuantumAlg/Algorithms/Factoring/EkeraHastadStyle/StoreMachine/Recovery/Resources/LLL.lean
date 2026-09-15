/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Resources.Budget

/-!
# LLL and nearest-plane cardinality bounds

The complete actual fixed-fuel execution includes both terminal decoders,
source basis and target loading, LLL, three saved-target copies, and the
three-coordinate nearest-plane pass. Its event count satisfies the independent
public-width polynomial below without counting unselected branch allowances.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources

open Execution

noncomputable section

/-- Public-width event ceiling for wide LLL, saving its target, and the original
three-coordinate nearest-plane pass. -/
def nearestPlaneSavedTargetCardBound (m ell : Nat) : Nat :=
  8 * m + 12 * ell + 258 + 264 * RSA.shortLogRecoveryFuel m ell

private theorem savedTargetOperationBound_le (N : Nat) :
    LatticePairNearestPlaneSavedTarget.operationBound N ≤
      nearestPlaneSavedTargetCardBound (shortLogBits N) (tradeoffBits N) := by
  have measurementEq :
      measurementBits N = shortLogBits N + 2 * tradeoffBits N := by
    unfold measurementBits registerParameters
    simp only [ShortDLP.CompiledMAU.registerParameters, ShortDLP.firstBits]
    omega
  unfold LatticePairNearestPlaneSavedTarget.operationBound
    LatticeWideLllMachine.operationBound LatticeWideLllMachine.decodeTargetOperationBound
    LatticeWideInitializationPrefix.operationBound nearestPlaneSavedTargetCardBound
  rw [measurementEq]
  change 2 * (2 * (shortLogBits N + 2 * tradeoffBits N) + tradeoffBits N + 3) +
    (2 * (tradeoffBits N + shortLogBits N) + 8) + (2 * shortLogBits N + 16) +
      (32 + 130 * RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N)) + 131 ≤ _
  omega

/-- Every actual saved-target path satisfies the original independent public-width event bound. -/
theorem pairNearestSavedTarget_eventCount_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (refs : LatticePairNearestPlaneSavedTarget.Refs ctx N)
    (path : (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs).Path) :
    ((LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs).eventTrace
      path).length ≤ nearestPlaneSavedTargetCardBound (shortLogBits N) (tradeoffBits N) :=
  (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_eventCount_le
    refs path).trans (savedTargetOperationBound_le N)

/-- The complete actual dependency depth satisfies the same independent public-width bound. -/
theorem pairNearestSavedTarget_depth_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (refs : LatticePairNearestPlaneSavedTarget.Refs ctx N)
    (path : (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs).Path) :
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs).depth
      (fun _ => 1) path ≤ nearestPlaneSavedTargetCardBound (shortLogBits N) (tradeoffBits N) :=
  (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_depth_le
    refs path).trans (savedTargetOperationBound_le N)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources
