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
wire contributes two allowance entries: one measurement and one possible
single-qubit correction. A zero outcome requires no correction gate. The
sole classical-operation coordinate is the actual finite-bit pack;
the stored-value correction dispatch does not add a classical operation.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

/-- Scalar count of the independent complete native-coordinate allowance. -/
def eventCountBound (m ell width N : Nat) : Nat :=
  polynomialPrimitiveBound m ell width N + resultBits m ell width + 1 +
    2 * totalQubits (registerParameters m ell width) + reloadXCount m ell width N

/-- Modulus-independent count ceiling, using the physical bank width for seed reload. -/
def eventCountWidthBound (m ell width : Nat) : Nat :=
  polynomialPrimitiveWidthBound m ell width + resultBits m ell width + 1 +
    3 * totalQubits (registerParameters m ell width)

private lemma resetEnvelope_card (width : Nat) :
    (ZReset.Bank.envelope (oracles := .empty) width BitWord.model).card = 2 * width := by
  have one : (ZReset.eventEnvelope (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := BitWord.model) (services := .empty) 2
      (ResourcePool.singleton (model := model)
        (.gate AlgorithmGate.Coordinate.singleQubit))).card = 2 := rfl
  rw [ZReset.Bank.envelope, Multiset.card_nsmul, one, Nat.mul_comm]

/-- Exact cardinality of the native allowance, with one possible correction per reset wire. -/
lemma eventEnvelope_card (m ell width N : Nat) :
    (eventEnvelope m ell width N).card = eventCountBound m ell width N := by
  simp only [eventEnvelope, Multiset.card_add,
    compiledCircuitEventEnvelopeInClassicalContext_card, Multiset.card_nsmul,
    ResourcePool.singleton, Multiset.card_replicate, Nat.mul_one,
    resetEnvelope_card, eventCountBound]
  omega

/-- The complete scalar allowance admits the same independent width-only ceiling. -/
lemma eventCountBound_le_widthBound (m ell width N : Nat) :
    eventCountBound m ell width N ≤ eventCountWidthBound m ell width := by
  have compiled := polynomialPrimitiveBound_le_widthBound m ell width N
  have reload := shortDLP_reload_count_le m ell width N
  unfold eventCountBound eventCountWidthBound
  omega

private lemma compiled_classicalWeight (m ell width N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (compiledCircuitEventEnvelopeInClassicalContext m ell width N BitWord.model .empty) = 0 := by
  unfold compiledCircuitEventEnvelopeInClassicalContext
  generalize compiledCircuitEventEnvelope m ell width N = pool
  induction pool using Multiset.induction_on with
  | empty => rfl
  | cons event pool ih =>
      simp only [ResourcePool.weightedCount, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      cases event <;> try cases ‹Empty›
      all_goals
        change 0 + _ = 0
        simpa only [Nat.zero_add] using ih

private lemma reset_classicalWeight (width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ZReset.Bank.envelope (oracles := .empty) width BitWord.model) = 0 := by
  have one : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ZReset.eventEnvelope (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := BitWord.model) (services := .empty) 2
        (ResourcePool.singleton (model := model)
          (.gate AlgorithmGate.Coordinate.singleQubit))) = 0 := rfl
  rw [ZReset.Bank.envelope, ResourcePool.weightedCount_nsmul, one, Nat.mul_zero]

/-- The actual packing instruction is the sole classical operation in the round allowance. -/
lemma eventEnvelope_classicalWeight (m ell width N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventEnvelope m ell width N) = 1 := by
  simp [eventEnvelope, compiled_classicalWeight, reset_classicalWeight,
    Resource.Event.classicalOperationWeight]

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  {shape : CShape} (parameter : CInputRef ctx shape)
  (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
  (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
  (result : CWriteRef ctx (.bits (resultBits m ell width)))
  (path : (code m ell width sameWires parameter N generator target cells result).Path)

/-- Every actual path's event cardinality obeys the complete native-coordinate allowance. -/
lemma shortDLP_runtimeRound_eventCount_le :
    ((code m ell width sameWires parameter N generator target cells result).resourcePool
      path).card ≤
      eventCountBound m ell width N :=
  (Multiset.card_le_card (shortDLP_runtimeRound_resourcePool_le
    m ell width sameWires parameter N generator target cells result path)).trans_eq
      (eventEnvelope_card m ell width N)

/-- The same actual path obeys the modulus-independent scalar ceiling. -/
lemma shortDLP_runtimeRound_eventCount_le_widthBound :
    ((code m ell width sameWires parameter N generator target cells result).resourcePool
      path).card ≤
      eventCountWidthBound m ell width :=
  (shortDLP_runtimeRound_eventCount_le
    m ell width sameWires parameter N generator target cells result path).trans
      (eventCountBound_le_widthBound m ell width N)

/-- The complete native path allowance permits at most the one real packing operation. -/
lemma shortDLP_runtimeRound_classicalWeight_le :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((code m ell width sameWires parameter N generator target cells result).resourcePool path) ≤
      1 :=
  (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
    (shortDLP_runtimeRound_resourcePool_le
      m ell width sameWires parameter N generator target cells result path)).trans_eq
        (eventEnvelope_classicalWeight m ell width N)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
