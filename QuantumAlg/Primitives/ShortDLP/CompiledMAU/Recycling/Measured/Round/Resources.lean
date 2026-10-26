/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.SuffixResources
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Native resource and time bounds for the same complete actual measured round

The original member, paid packing, full-frame measurement/correction and
native loader are charged from their actual constituent paths. Quantum time
is an upper bound on the true execution schedule [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round

noncomputable section

open Execution

/-- The original source widths determine the single paid packing leaf. -/
def packingBudget (m ell : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation
    (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packFiniteBits (resultBits m ell)))))

/-- Independent full-round envelope includes every original member, pack, reset and loader event. -/
def eventBudget (m ell width N : Nat) : ResourcePool model :=
  Resources.memberBudget m ell width + packingBudget m ell +
    (BankReset.eventBudget width + EncodedBit.Word.BasisLoad.xCount (seedLabel width N) •
      ResourcePool.singleton (model := model) (.gate .singleQubit))

/-- Full-round quantum time includes the true correction layer and the native seed loader. -/
def quantumTimeLimit (m ell width N : Nat) : Nat :=
  Resources.memberTime m ell width + (1 + EncodedBit.Word.BasisLoad.xCount (seedLabel width N))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev RoundResourcesCtx := context base noQuantum m ell width

variable {shape : CShape}
  (parameter : CInputRef (RoundResourcesCtx base noQuantum m ell width) shape)
  (wide : 2 ≤ width) (large : 5 ≤ width) (modulus : BitVec width) (positive : 0 < modulus.toNat)
  (odd : modulus.getLsbD 0 = true) (generator target : shape.Value → (ZMod modulus.toNat)ˣ)

include large positive odd

/-- Every actual stored-parameter branch pays the same complete native member allowance. -/
lemma measuredRound_selected_events
    (path : (selected base noQuantum m ell width parameter wide modulus generator target).Path) :
    (selected base noQuantum m ell width parameter wide modulus generator target).resourcePool
        path ≤
      Resources.memberBudget m ell width := by
  change (Circuit.embed (allowAllocation := true)
    (ContextEmbedding.identity (RoundResourcesCtx base noQuantum m ell width))
    (member base noQuantum m ell width wide modulus (generator path.1)
      (target path.1))).resourcePool path.2 ≤ _
  rw [Circuit.resourcePool_embed]
  exact Resources.measuredMember_events base noQuantum m ell width wide large modulus positive odd
    (generator path.1) (target path.1) path.2

/-- Real stored-parameter selection preserves the original member's actual time bound. -/
lemma measuredRound_selected_time
    (path : (selected base noQuantum m ell width parameter wide modulus generator target).Path) :
    (selected base noQuantum m ell width parameter wide modulus generator target).quantumTime path ≤
      Resources.memberTime m ell width := by
  change (Circuit.embed (allowAllocation := true)
    (ContextEmbedding.identity (RoundResourcesCtx base noQuantum m ell width))
    (member base noQuantum m ell width wide modulus (generator path.1)
      (target path.1))).quantumTime path.2 ≤ _
  rw [Circuit.quantumTime_embed]
  exact Resources.measuredMember_time base noQuantum m ell width wide large modulus positive odd
    (generator path.1) (target path.1) path.2

variable (result : CWriteRef (RoundResourcesCtx base noQuantum m ell width)
  (.bits (resultBits m ell)))

omit large positive odd in
/-- The actual single paid packing instruction contributes its declaration-owned coordinate. -/
lemma measuredRound_packing_events
    (path : (Packing.code base noQuantum m ell width result).Path) :
    (Packing.code base noQuantum m ell width result).resourcePool path = packingBudget m ell := by
  change ResourcePool.ofList
    ((Packing.code base noQuantum m ell width result).eventTrace path) = _
  rw [Packing.measuredPacking_eventTrace]
  rfl

/-- The actual member and paid packing accumulate their native ledgers on the same path. -/
lemma measuredRound_sampled_events
    (path : (sampled base noQuantum m ell width parameter wide modulus generator target
      result).Path) :
    (sampled base noQuantum m ell width parameter wide modulus generator target result).resourcePool
        path ≤ Resources.memberBudget m ell width + packingBudget m ell := by
  have first := measuredRound_selected_events base noQuantum m ell width parameter wide large
    modulus positive odd generator target path.1
  have second := measuredRound_packing_events base noQuantum m ell width result path.2
  simpa only [sampled, Circuit.resourcePool, Circuit.eventTrace, ResourcePool.ofList_append,
    second] using add_le_add first second.le

omit large positive odd in
/-- Full reset and literal reload contribute their own actual native paths. -/
lemma measuredRound_restart_events
    (path : (Reload.resetReload base noQuantum m ell width modulus.toNat).Path) :
    (Reload.resetReload base noQuantum m ell width modulus.toNat).resourcePool path ≤
      BankReset.eventBudget width +
        EncodedBit.Word.BasisLoad.xCount (seedLabel width modulus.toNat) •
          ResourcePool.singleton (model := model) (.gate .singleQubit) := by
  have reset := BankReset.measuredBankReset_events base noQuantum m ell width path.1
  have reload := Reload.measuredReload_events base noQuantum m ell width modulus.toNat path.2
  simpa only [Reload.resetReload, Circuit.resourcePool, Circuit.eventTrace,
    ResourcePool.ofList_append, reload] using add_le_add reset reload.le

/-- The same complete actual round obeys the independent native event envelope. -/
lemma measuredRound_events
    (path : (code base noQuantum m ell width parameter wide modulus generator target result).Path) :
    (code base noQuantum m ell width parameter wide modulus generator target result).resourcePool
        path ≤ eventBudget m ell width modulus.toNat := by
  have first := measuredRound_sampled_events base noQuantum m ell width parameter wide large modulus
    positive odd generator target result path.1
  have second := measuredRound_restart_events base noQuantum m ell width modulus path.2
  simpa only [code, eventBudget, Circuit.resourcePool, Circuit.eventTrace,
    ResourcePool.ofList_append] using add_le_add first second

/-- The paid native packing adds zero quantum time to its actual selected member. -/
lemma measuredRound_sampled_time
    (path : (sampled base noQuantum m ell width parameter wide modulus generator target
      result).Path) :
    (sampled base noQuantum m ell width parameter wide modulus generator target result).quantumTime
        path ≤ Resources.memberTime m ell width := by
  have first := measuredRound_selected_time base noQuantum m ell width parameter wide large modulus
    positive odd generator target path.1
  have second := Packing.measuredPacking_quantumTime base noQuantum m ell width result path.2
  change (selected base noQuantum m ell width parameter wide modulus generator target).quantumTime
      path.1 + (Packing.code base noQuantum m ell width result).quantumTime path.2 ≤ _
  rw [second, Nat.add_zero]
  exact first

/-- The actual full round charges reset and reload after every selected member, including last. -/
lemma measuredRound_time
    (path : (code base noQuantum m ell width parameter wide modulus generator target result).Path) :
    (code base noQuantum m ell width parameter wide modulus generator target result).quantumTime
        path ≤ quantumTimeLimit m ell width modulus.toNat :=
  Nat.add_le_add
    (measuredRound_sampled_time base noQuantum m ell width parameter wide large modulus positive odd
      generator target result path.1)
    (Reload.measuredResetReload_quantumTime base noQuantum m ell width modulus.toNat path.2)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round
