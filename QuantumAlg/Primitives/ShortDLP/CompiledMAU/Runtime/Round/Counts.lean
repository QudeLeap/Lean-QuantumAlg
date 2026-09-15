/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Resources
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Scalar observations of one reusable-bank round's native allowance

The event count sums the existing native-coordinate allowance. Each reset
wire contributes three allowance entries: one measurement and both possible
correction labels. This is an envelope cardinality, not the count of an actual
path, which selects only one correction. Every gate keeps its original control
label. The sole classical-operation coordinate is the actual finite-bit pack;
the stored-value correction dispatch does not add a classical operation.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

/-- Scalar count of the independent complete native-coordinate allowance. -/
def eventCountBound (m ell width N : Nat) : Nat :=
  polynomialPrimitiveBound m ell width N + resultBits m ell width + 1 +
    3 * totalQubits (registerParameters m ell width) + reloadXCount m ell width N

/-- Modulus-independent count ceiling, using the physical bank width for seed reload. -/
def eventCountWidthBound (m ell width : Nat) : Nat :=
  polynomialPrimitiveWidthBound m ell width + resultBits m ell width + 1 +
    4 * totalQubits (registerParameters m ell width)

private theorem resetEnvelope_card (width : Nat) :
    (ZReset.Bank.envelope width).card = 3 * width := by
  have one : (ZReset.eventEnvelope 2).card = 3 := rfl
  rw [ZReset.Bank.envelope, Multiset.card_nsmul, one, Nat.mul_comm]

/-- Exact cardinality of the complete coordinate allowance, including both reset alternatives. -/
theorem eventEnvelope_card (m ell width N : Nat) :
    (eventEnvelope m ell width N).card = eventCountBound m ell width N := by
  simp only [eventEnvelope, Multiset.card_add, compiledCircuitEventEnvelope_card,
    Multiset.card_nsmul, ResourcePool.singleton, Multiset.card_replicate, Nat.mul_one,
    resetEnvelope_card, eventCountBound]
  omega

/-- The complete scalar allowance admits the same independent width-only ceiling. -/
theorem eventCountBound_le_widthBound (m ell width N : Nat) :
    eventCountBound m ell width N ≤ eventCountWidthBound m ell width := by
  have compiled := polynomialPrimitiveBound_le_widthBound m ell width N
  have reload := shortDLP_reload_count_le m ell width N
  unfold eventCountBound eventCountWidthBound
  omega

private theorem control_classicalWeight (dimension : Nat) (pool : ResourcePool .quantum) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (ResourcePool.controlForDimension dimension pool) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool := by
  have observation :
      (Resource.Event.classicalOperationWeight ∘
        fun event : Resource.Event .quantum => event.controlForDimensions [dimension]) =
      Resource.Event.classicalOperationWeight := by
    funext event
    cases event <;> rfl
  simp only [ResourcePool.weightedCount, ResourcePool.controlForDimension,
    ResourcePool.controlForDimensions, Multiset.map_map, observation]

private theorem exponentiation_classicalWeight (bits width N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (exponentiationEventEnvelope bits width N) = 0 := by
  unfold exponentiationEventEnvelope
  split
  · simp [MAU.Exponentiation.Gidney.nativeBudget, MAU.Exponentiation.Gidney.stageNativeBudget,
      MAU.Multiplication.Gidney.nativeBudget, MAU.Multiplication.Gidney.wordSwapBudget,
      MAU.Multiplication.Accumulate.Gidney.nativeBudget,
      MAU.Multiplication.Accumulate.Gidney.nativeAlphabet, MAU.Addition.Gidney.offsetAlphabet,
      EncodedBit.GateSpec.primitiveAlphabet, control_classicalWeight,
      Resource.Event.classicalOperationWeight]
  · exact ResourcePool.weightedCount_zero _

private theorem compiled_classicalWeight (m ell width N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (compiledCircuitEventEnvelope m ell width N) = 0 := by
  simp [compiledCircuitEventEnvelope, preparationEventEnvelope,
    compiledGroupActionEventEnvelope, firstExponentiationEventEnvelope,
    secondExponentiationEventEnvelope, exponentiation_classicalWeight,
    readoutEventEnvelope, qftEventEnvelope, WalshHadamard.hadamardEvent,
    Resource.Event.classicalOperationWeight]

private theorem reset_classicalWeight (width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ZReset.Bank.envelope width) = 0 := by
  have one : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ZReset.eventEnvelope 2) = 0 := rfl
  rw [ZReset.Bank.envelope, ResourcePool.weightedCount_nsmul, one, Nat.mul_zero]

/-- The actual packing instruction is the sole classical operation in the round allowance. -/
theorem eventEnvelope_classicalWeight (m ell width N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventEnvelope m ell width N) = 1 := by
  simp [eventEnvelope, compiled_classicalWeight, reset_classicalWeight,
    Circuit.zEvent, Resource.Event.classicalOperationWeight]

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  {shape : CShape} (parameter : CInputRef ctx shape)
  (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
  (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
  (result : CWriteRef ctx (.bits (resultBits m ell width)))
  (path : (code m ell width sameWires parameter N generator target cells result).Path)

/-- Every actual path's event cardinality obeys the complete native-coordinate allowance. -/
theorem shortDLP_runtimeRound_eventCount_le :
    ((code m ell width sameWires parameter N generator target cells result).resourcePool
      path).card ≤
      eventCountBound m ell width N :=
  (Multiset.card_le_card (shortDLP_runtimeRound_resourcePool_le
    m ell width sameWires parameter N generator target cells result path)).trans_eq
      (eventEnvelope_card m ell width N)

/-- The same actual path obeys the modulus-independent scalar ceiling. -/
theorem shortDLP_runtimeRound_eventCount_le_widthBound :
    ((code m ell width sameWires parameter N generator target cells result).resourcePool
      path).card ≤
      eventCountWidthBound m ell width :=
  (shortDLP_runtimeRound_eventCount_le
    m ell width sameWires parameter N generator target cells result path).trans
      (eventCountBound_le_widthBound m ell width N)

/-- The complete native path allowance permits at most the one real packing operation. -/
theorem shortDLP_runtimeRound_classicalWeight_le :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((code m ell width sameWires parameter N generator target cells result).resourcePool path) ≤
      1 :=
  (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
    (shortDLP_runtimeRound_resourcePool_le
      m ell width sameWires parameter N generator target cells result path)).trans_eq
        (eventEnvelope_classicalWeight m ell width N)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
