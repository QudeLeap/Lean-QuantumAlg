/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Resources.Support

/-!
# Independent coordinate budgets for source-to-LLL execution

The complete allowance combines the original decoder, basis, target, reset,
and prescribed-fuel instruction budgets. Its parameters do not depend on an
actual path or its resource ledger.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent coordinate budget for both sample decoders, basis loading, and target centering. -/
def decodeTargetEventEnvelope (N : Nat) : ResourcePool model :=
  LatticeWideInitializationPrefix.eventEnvelope N +
    LatticeWideTargetMachine.eventEnvelope (shortLogBits N) (tradeoffBits N) (Width N)

/-- Independent initialization allowance, kept folded when specializing the recovery fuel. -/
@[irreducible] def initializedEventEnvelope (fuel width : Nat) : ResourcePool model :=
  ResourcePool.ofList (LatticeFixedFuelMachine.refreshResetTrace width) +
    LatticeFixedFuelMachine.fixedFuelEventEnvelope fuel width

/-- The folded initialization allowance is exactly the original reset and fixed-fuel formula. -/
theorem initializedEventEnvelope_eq (fuel width : Nat) :
    initializedEventEnvelope (model := model) fuel width =
      ResourcePool.ofList (LatticeFixedFuelMachine.refreshResetTrace width) +
        LatticeFixedFuelMachine.fixedFuelEventEnvelope fuel width := by
  unfold initializedEventEnvelope
  rfl

/-- Independent full coordinate budget at the original prescribed recovery fuel. -/
def eventEnvelope (N : Nat) : ResourcePool model :=
  decodeTargetEventEnvelope N +
    initializedEventEnvelope
      (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N)) (Width N)

/-- Every actual source-and-target path meets the independent combined coordinate allowance. -/
theorem decodeTargetInto_pool_le (refs : Refs ctx N) (path : (decodeTargetInto refs).Path) :
    (decodeTargetInto refs).resourcePool path ≤ decodeTargetEventEnvelope N := by
  unfold decodeTargetEventEnvelope
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (LatticeWideInitializationPrefix.decodeBasisInto_pool_le (prefixRefs refs) path.1)
    (LatticeWideTargetMachine.loadTargetInto_resourcePool_le refs.target path.2)

/-- Reset and iteration allowances compose before specializing the public recovery fuel. -/
private theorem initialized_pool_le {width : Nat} (fuel : Nat)
    (refs : LatticeFixedFuelMachine.Refs ctx width)
    (path : (LatticeFixedFuelMachine.initializedInto fuel refs).Path) :
    (LatticeFixedFuelMachine.initializedInto fuel refs).resourcePool path ≤
      initializedEventEnvelope fuel width := by
  rw [initializedEventEnvelope_eq]
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (LatticeFixedFuelMachine.refreshResetInto_resourcePool refs path.1).le
    (LatticeFixedFuelMachine.fixedFuelInto_pool_le fuel refs path.2)

/-- Every actual source-to-LLL path satisfies the independent full native coordinate budget. -/
theorem pairToLllInto_pool_le (refs : Refs ctx N) (path : (pairToLllInto refs).Path) :
    (pairToLllInto refs).resourcePool path ≤ eventEnvelope N := by
  have decoded := decodeTargetInto_pool_le refs path.1
  have initialized :
      (LatticeFixedFuelMachine.initializedInto
        (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
        refs.initialization.driver).resourcePool path.2 ≤
      initializedEventEnvelope
        (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N)) (Width N) :=
    initialized_pool_le (model := model) (ctx := ctx) (width := Width N)
      (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N))
      refs.initialization.driver path.2
  unfold eventEnvelope
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add decoded initialized

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine
