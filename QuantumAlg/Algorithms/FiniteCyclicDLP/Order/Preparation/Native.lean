/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Complete
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Complete
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.State
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix

/-!
# Endpoint-width native range preparation

The semantic intrinsic circuit is padded only by an untouched high prefix to
the reviewed Fourier register width.  Padding emits no event and preserves the
literal native schedule, so the same circuit supplies both execution and proof.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderPreparation.Native

noncomputable section

open scoped BigOperators

universe u

variable {G : Type u} [Group G]
variable {P : KnownOrderProblem G}

/-- Every positive expansion fits in the one-qubit envelope above its highest
set bit. -/
public theorem order_le_intrinsicCapacity {N : Nat}
    (expansion : OrderExpansion N) :
    N ≤ 2 ^ Intrinsic.width expansion := by
  classical
  calc
    N = ∑ index, 2 ^ expansion.ell index := expansion.sum_powers
    _ = ∑ exponent ∈ Finset.univ.image expansion.ell, 2 ^ exponent := by
      rw [Finset.sum_image]
      exact expansion.ell_strict.injective.injOn
    _ ≤ 2 ^ Intrinsic.width expansion :=
      (Nat.geomSum_lt (m := 2) (s := Finset.univ.image expansion.ell)
        (n := Intrinsic.width expansion) (by omega) (by
          intro exponent member
          rcases Finset.mem_image.mp member with ⟨index, -, rfl⟩
          exact Intrinsic.ell_lt_width expansion index)).le

/-- The intrinsic active register is a suffix of the reviewed exponent
register. -/
public theorem intrinsicWidth_le (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    Intrinsic.width expansion ≤ width P := by
  unfold Intrinsic.width
  exact Nat.succ_le_iff.mpr
    (OrderPreparation.ell_lt_width P expansion
      ⟨expansion.count - 1, by
        have positive := expansion.count_pos
        omega⟩)

/-- Pad a canonical binary word by an untouched high prefix. -/
public def padHigh {source target : Nat} (within : source ≤ target)
    {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles
      (QuantumSignature.qubits target).canonicalPlacement.layout :=
  (UnitaryCircuit.onBinarySuffix (target - source) body).castQubitWidth
    (Nat.sub_add_cancel within)

@[simp] public theorem padHigh_eventTrace {source target : Nat}
    (within : source ≤ target) {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout) :
    (padHigh within body).eventTrace = body.eventTrace := by
  simp [padHigh, UnitaryCircuit.castQubitWidth_eventTrace,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventTrace]

@[simp] public theorem padHigh_eventCost {source target : Nat}
    (within : source ≤ target) {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout) :
    (padHigh within body).eventCost = body.eventCost := by
  rw [padHigh, UnitaryCircuit.castQubitWidth_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost]

@[simp] public theorem padHigh_evaluatedEventDepth {source target : Nat}
    (within : source ≤ target) {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (padHigh within body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  rw [padHigh, UnitaryCircuit.castQubitWidth_evaluatedEventDepth,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_evaluatedEventDepth]

/-- The actual endpoint preparation is precisely the proven intrinsic word,
with only a high identity prefix added to reach the Fourier width. -/
@[expose] public def circuit (oracles : OracleModel) (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    UnitaryCircuit AlgorithmGate.model oracles (layout P) :=
  padHigh (intrinsicWidth_le P expansion)
    (Intrinsic.circuit oracles expansion)

private theorem intrinsicInitialX_single_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (Intrinsic.initialX oracles expansion).eventCost = expansion.gaps := by
  rw [Intrinsic.initialX, UnitaryCircuit.indexedProduct_eventCost,
    ResourcePool.count_add, ResourcePool.count_finset_sum]
  have each (gap : Fin expansion.gaps) :
      ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
          (Intrinsic.xAt oracles expansion
            (Intrinsic.wire expansion
              (OrderPreparation.rightIndex expansion gap))).eventCost = 1 := by
    change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (QubitPrimitive.circuit
          (.x (Intrinsic.wire expansion
            (OrderPreparation.rightIndex expansion gap)))
          (QubitLayout.canonical (Intrinsic.width expansion)) oracles).eventCost = 1
    rw [QubitPrimitive.primitiveCircuit_eventCost]
    exact ResourcePool.count_singleton_self _ 1
  simp_rw [each]
  simp

private theorem intrinsicInitialX_cnot_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (Intrinsic.initialX oracles expansion).eventCost = 0 := by
  rw [Intrinsic.initialX, UnitaryCircuit.indexedProduct_eventCost,
    ResourcePool.count_add, ResourcePool.count_finset_sum]
  have each (gap : Fin expansion.gaps) :
      ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
          (Intrinsic.xAt oracles expansion
            (Intrinsic.wire expansion
              (OrderPreparation.rightIndex expansion gap))).eventCost = 0 := by
    change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (QubitPrimitive.circuit
          (.x (Intrinsic.wire expansion
            (OrderPreparation.rightIndex expansion gap)))
          (QubitLayout.canonical (Intrinsic.width expansion)) oracles).eventCost = 0
    rw [QubitPrimitive.primitiveCircuit_eventCost]
    exact ResourcePool.count_singleton_of_ne (by simp [QubitPrimitive.event,
      QubitPrimitive.nativeToken]) 1
  simp_rw [each]
  simp

private theorem intrinsicInitialX_unit_depth (oracles : OracleModel)
    (expansion : OrderExpansion P.order) :
    (Intrinsic.initialX oracles expansion).evaluatedEventDepth (fun _ => 1) =
      expansion.gaps := by
  rw [Intrinsic.initialX, UnitaryCircuit.evaluatedEventDepth_indexedProduct]
  have each : ∀ gap : Fin expansion.gaps,
      (Intrinsic.xAt oracles expansion
        (Intrinsic.wire expansion
          (OrderPreparation.rightIndex expansion gap))).evaluatedEventDepth
            (fun _ => 1) = 1 := by
    intro gap
    change UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
        (QubitPrimitive.circuit
          (.x (Intrinsic.wire expansion
            (OrderPreparation.rightIndex expansion gap)))
          (QubitLayout.canonical (Intrinsic.width expansion)) oracles) = 1
    rfl
  simp_rw [each]
  simp

private theorem intrinsicLowHadamards_single_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (Intrinsic.lowHadamards oracles expansion).eventCost = expansion.first := by
  rw [Intrinsic.lowHadamards, UnitaryCircuit.castQubitWidth_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost]
  have events := congrArg
    (ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit))
    (Gate.HadamardLayer.hadamardLayer_circuit_eventCost oracles expansion.first)
  simpa using events

private theorem intrinsicLowHadamards_cnot_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (Intrinsic.lowHadamards oracles expansion).eventCost = 0 := by
  rw [Intrinsic.lowHadamards, UnitaryCircuit.castQubitWidth_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost]
  have events := congrArg
    (ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot))
    (Gate.HadamardLayer.hadamardLayer_circuit_eventCost oracles expansion.first)
  simpa using events

private theorem intrinsicLowHadamards_unit_depth (oracles : OracleModel)
    (expansion : OrderExpansion P.order) :
    (Intrinsic.lowHadamards oracles expansion).evaluatedEventDepth (fun _ => 1) =
      if expansion.first = 0 then 0 else 1 := by
  rw [Intrinsic.lowHadamards,
    UnitaryCircuit.castQubitWidth_evaluatedEventDepth,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_evaluatedEventDepth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth
    oracles expansion.first

private theorem intrinsicGapHadamards_single_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (Intrinsic.gapHadamards oracles expansion gap).eventCost =
        4 * OrderPreparation.gapWidth expansion gap := by
  rw [Intrinsic.gapHadamards, UnitaryCircuit.indexedProduct_eventCost,
    ResourcePool.count_add, ResourcePool.count_finset_sum]
  simp_rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_eventCost,
    Gate.OpenControl.hadamard_eventCost, ResourcePool.count_add]
  simp [Nat.mul_comm]

private theorem intrinsicGapHadamards_cnot_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (Intrinsic.gapHadamards oracles expansion gap).eventCost =
        OrderPreparation.gapWidth expansion gap := by
  rw [Intrinsic.gapHadamards, UnitaryCircuit.indexedProduct_eventCost,
    ResourcePool.count_add, ResourcePool.count_finset_sum]
  simp_rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_eventCost,
    Gate.OpenControl.hadamard_eventCost, ResourcePool.count_add]
  simp

private theorem intrinsicGapHadamards_unit_depth (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    (Intrinsic.gapHadamards oracles expansion gap).evaluatedEventDepth
        (fun _ => 1) = 3 * OrderPreparation.gapWidth expansion gap := by
  rw [Intrinsic.gapHadamards,
    UnitaryCircuit.evaluatedEventDepth_indexedProduct]
  simp_rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_evaluatedEventDepth,
    Gate.OpenControl.hadamard_unit_depth]
  simp [Nat.mul_comm]

private theorem intrinsicInitialRotation_single_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (Intrinsic.rotYAt oracles expansion
        (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
        (OrderPreparation.sourceAngle expansion gap)).eventCost = 1 := by
  rw [Intrinsic.rotYAt, UnitaryCircuit.unitaryCircuit_onBinaryWire_eventCost,
    Intrinsic.singleQubit, Gate.singleQubitAt_eventCost,
    ResourcePool.count_singleton_self]

private theorem intrinsicInitialRotation_cnot_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (Intrinsic.rotYAt oracles expansion
        (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
        (OrderPreparation.sourceAngle expansion gap)).eventCost = 0 := by
  rw [Intrinsic.rotYAt, UnitaryCircuit.unitaryCircuit_onBinaryWire_eventCost,
    Intrinsic.singleQubit, Gate.singleQubitAt_eventCost]
  exact ResourcePool.count_singleton_of_ne (by simp) 1

private theorem intrinsicInitialRotation_unit_depth (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    (Intrinsic.rotYAt oracles expansion
      (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
      (OrderPreparation.sourceAngle expansion gap)).evaluatedEventDepth
        (fun _ => 1) = 1 := by
  rw [Intrinsic.rotYAt,
    UnitaryCircuit.unitaryCircuit_onBinaryWire_evaluatedEventDepth]
  rfl

private theorem intrinsicControlledRotation_single_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (UnitaryCircuit.onBinarySeparated
        (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
        (Intrinsic.wire expansion (OrderPreparation.leftIndex expansion gap))
        (Intrinsic.rightWire_lt_leftWire expansion gap)
        (Gate.OpenControl.rotYRight oracles
          (OrderPreparation.sourceAngle expansion gap))).eventCost = 4 := by
  simp [UnitaryCircuit.unitaryCircuit_onBinarySeparated_eventCost,
    Gate.OpenControl.rotYRight_eventCost, ResourcePool.count_add]

private theorem intrinsicControlledRotation_cnot_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (UnitaryCircuit.onBinarySeparated
        (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
        (Intrinsic.wire expansion (OrderPreparation.leftIndex expansion gap))
        (Intrinsic.rightWire_lt_leftWire expansion gap)
        (Gate.OpenControl.rotYRight oracles
          (OrderPreparation.sourceAngle expansion gap))).eventCost = 2 := by
  simp [UnitaryCircuit.unitaryCircuit_onBinarySeparated_eventCost,
    Gate.OpenControl.rotYRight_eventCost, ResourcePool.count_add]

private theorem intrinsicControlledRotation_unit_depth (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    (UnitaryCircuit.onBinarySeparated
      (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
      (Intrinsic.wire expansion (OrderPreparation.leftIndex expansion gap))
      (Intrinsic.rightWire_lt_leftWire expansion gap)
      (Gate.OpenControl.rotYRight oracles
        (OrderPreparation.sourceAngle expansion gap))).evaluatedEventDepth
        (fun _ => 1) = 5 := by
  rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_evaluatedEventDepth,
    Gate.OpenControl.rotYRight_unit_depth]

private theorem intrinsicGapStage_single_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (Intrinsic.gapStage oracles expansion gap).eventCost =
        (if gap.val = 0 then 1 else 4) +
          4 * OrderPreparation.gapWidth expansion gap := by
  by_cases first : gap.val = 0
  · simp only [Intrinsic.gapStage, if_pos first,
      UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
    rw [intrinsicInitialRotation_single_count,
      intrinsicGapHadamards_single_count]
  · simp only [Intrinsic.gapStage, if_neg first,
      UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
    rw [intrinsicControlledRotation_single_count,
      intrinsicGapHadamards_single_count]

private theorem intrinsicGapStage_cnot_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (Intrinsic.gapStage oracles expansion gap).eventCost =
        (if gap.val = 0 then 0 else 2) +
          OrderPreparation.gapWidth expansion gap := by
  by_cases first : gap.val = 0
  · simp only [Intrinsic.gapStage, if_pos first,
      UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
    rw [intrinsicInitialRotation_cnot_count,
      intrinsicGapHadamards_cnot_count]
  · simp only [Intrinsic.gapStage, if_neg first,
      UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
    rw [intrinsicControlledRotation_cnot_count,
      intrinsicGapHadamards_cnot_count]

private theorem intrinsicGapStage_unit_depth (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    (Intrinsic.gapStage oracles expansion gap).evaluatedEventDepth (fun _ => 1) =
      (if gap.val = 0 then 1 else 5) +
        3 * OrderPreparation.gapWidth expansion gap := by
  by_cases first : gap.val = 0
  · simp only [Intrinsic.gapStage, if_pos first,
      UnitaryCircuit.evaluatedEventDepth_seq]
    rw [intrinsicInitialRotation_unit_depth,
      intrinsicGapHadamards_unit_depth]
  · simp only [Intrinsic.gapStage, if_neg first,
      UnitaryCircuit.evaluatedEventDepth_seq]
    rw [intrinsicControlledRotation_unit_depth,
      intrinsicGapHadamards_unit_depth]

private theorem intrinsicInitialX_toffoli_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (Intrinsic.initialX oracles expansion).eventCost = 0 := by
  rw [Intrinsic.initialX, UnitaryCircuit.indexedProduct_eventCost,
    ResourcePool.count_add, ResourcePool.count_finset_sum]
  have each (gap : Fin expansion.gaps) :
      ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
          (Intrinsic.xAt oracles expansion
            (Intrinsic.wire expansion
              (OrderPreparation.rightIndex expansion gap))).eventCost = 0 := by
    change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (QubitPrimitive.circuit
          (.x (Intrinsic.wire expansion
            (OrderPreparation.rightIndex expansion gap)))
          (QubitLayout.canonical (Intrinsic.width expansion)) oracles).eventCost = 0
    rw [QubitPrimitive.primitiveCircuit_eventCost]
    exact ResourcePool.count_singleton_of_ne (by
      simp [QubitPrimitive.event, QubitPrimitive.nativeToken]) 1
  simp_rw [each]
  simp

private theorem intrinsicLowHadamards_toffoli_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (Intrinsic.lowHadamards oracles expansion).eventCost = 0 := by
  rw [Intrinsic.lowHadamards, UnitaryCircuit.castQubitWidth_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost]
  have events := congrArg
    (ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli))
    (Gate.HadamardLayer.hadamardLayer_circuit_eventCost oracles expansion.first)
  simpa using events

private theorem intrinsicGapHadamards_toffoli_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (Intrinsic.gapHadamards oracles expansion gap).eventCost = 0 := by
  rw [Intrinsic.gapHadamards, UnitaryCircuit.indexedProduct_eventCost,
    ResourcePool.count_add, ResourcePool.count_finset_sum]
  simp_rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_eventCost,
    Gate.OpenControl.hadamard_eventCost]
  simp

private theorem intrinsicInitialRotation_toffoli_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (Intrinsic.rotYAt oracles expansion
        (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
        (OrderPreparation.sourceAngle expansion gap)).eventCost = 0 := by
  rw [Intrinsic.rotYAt, UnitaryCircuit.unitaryCircuit_onBinaryWire_eventCost,
    Intrinsic.singleQubit, Gate.singleQubitAt_eventCost]
  exact ResourcePool.count_singleton_of_ne (by simp) 1

private theorem intrinsicControlledRotation_toffoli_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (UnitaryCircuit.onBinarySeparated
        (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
        (Intrinsic.wire expansion (OrderPreparation.leftIndex expansion gap))
        (Intrinsic.rightWire_lt_leftWire expansion gap)
        (Gate.OpenControl.rotYRight oracles
          (OrderPreparation.sourceAngle expansion gap))).eventCost = 0 := by
  rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_eventCost,
    Gate.OpenControl.rotYRight_eventCost]
  simp

private theorem intrinsicGapStage_toffoli_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (Intrinsic.gapStage oracles expansion gap).eventCost = 0 := by
  by_cases first : gap.val = 0
  · simp only [Intrinsic.gapStage, if_pos first,
      UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
    rw [intrinsicInitialRotation_toffoli_count,
      intrinsicGapHadamards_toffoli_count]
  · simp only [Intrinsic.gapStage, if_neg first,
      UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
    rw [intrinsicControlledRotation_toffoli_count,
      intrinsicGapHadamards_toffoli_count]

private theorem intrinsicInitialX_oracle_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (query : oracles.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (Intrinsic.initialX oracles expansion).eventCost = 0 := by
  rw [Intrinsic.initialX, UnitaryCircuit.indexedProduct_eventCost,
    ResourcePool.count_add, ResourcePool.count_finset_sum]
  have each (gap : Fin expansion.gaps) :
      ResourcePool.count
          (model := .quantum AlgorithmGate.model oracles) (.oracle query)
          (Intrinsic.xAt oracles expansion
            (Intrinsic.wire expansion
              (OrderPreparation.rightIndex expansion gap))).eventCost = 0 := by
    apply QubitPrimitive.primitiveCircuit_eventCount_of_ne
    simp [QubitPrimitive.event, QubitPrimitive.nativeToken]
  simp_rw [each]
  simp

private theorem intrinsicLowHadamards_oracle_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (query : oracles.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (Intrinsic.lowHadamards oracles expansion).eventCost = 0 := by
  rw [Intrinsic.lowHadamards, UnitaryCircuit.castQubitWidth_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost]
  have events := congrArg
    (ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.oracle query))
    (Gate.HadamardLayer.hadamardLayer_circuit_eventCost oracles expansion.first)
  simpa using events

private theorem intrinsicGapHadamards_oracle_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps)
    (query : oracles.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (Intrinsic.gapHadamards oracles expansion gap).eventCost = 0 := by
  rw [Intrinsic.gapHadamards, UnitaryCircuit.indexedProduct_eventCost,
    ResourcePool.count_add, ResourcePool.count_finset_sum]
  simp_rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_eventCost,
    Gate.OpenControl.hadamard_eventCost]
  simp

private theorem intrinsicInitialRotation_oracle_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps)
    (query : oracles.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (Intrinsic.rotYAt oracles expansion
        (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
        (OrderPreparation.sourceAngle expansion gap)).eventCost = 0 := by
  rw [Intrinsic.rotYAt, UnitaryCircuit.unitaryCircuit_onBinaryWire_eventCost,
    Intrinsic.singleQubit, Gate.singleQubitAt_eventCost]
  exact ResourcePool.count_singleton_of_ne (by simp) 1

private theorem intrinsicControlledRotation_oracle_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps)
    (query : oracles.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (UnitaryCircuit.onBinarySeparated
        (Intrinsic.wire expansion (OrderPreparation.rightIndex expansion gap))
        (Intrinsic.wire expansion (OrderPreparation.leftIndex expansion gap))
        (Intrinsic.rightWire_lt_leftWire expansion gap)
        (Gate.OpenControl.rotYRight oracles
          (OrderPreparation.sourceAngle expansion gap))).eventCost = 0 := by
  rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_eventCost,
    Gate.OpenControl.rotYRight_eventCost]
  simp

private theorem intrinsicGapStage_oracle_count (oracles : OracleModel)
    (expansion : OrderExpansion P.order) (gap : Fin expansion.gaps)
    (query : oracles.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (Intrinsic.gapStage oracles expansion gap).eventCost = 0 := by
  by_cases first : gap.val = 0
  · simp only [Intrinsic.gapStage, if_pos first,
      UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
    rw [intrinsicInitialRotation_oracle_count,
      intrinsicGapHadamards_oracle_count]
  · simp only [Intrinsic.gapStage, if_neg first,
      UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
    rw [intrinsicControlledRotation_oracle_count,
      intrinsicGapHadamards_oracle_count]

/-- Range preparation uses only declared native gates and performs no oracle query. -/
public theorem circuit_oracle_count (oracles : OracleModel)
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order)
    (query : oracles.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (circuit oracles P expansion).eventCost = 0 := by
  rw [circuit, padHigh_eventCost, Intrinsic.circuit,
    UnitaryCircuit.indexedProduct_eventCost, ResourcePool.count_add,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ResourcePool.count_finset_sum, intrinsicInitialX_oracle_count,
    intrinsicLowHadamards_oracle_count]
  simp_rw [intrinsicGapStage_oracle_count]
  simp

/-- The all-order range preparation contains no native Toffoli occurrence. -/
public theorem circuit_toffoli_count (oracles : OracleModel)
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (circuit oracles P expansion).eventCost = 0 := by
  rw [circuit, padHigh_eventCost, Intrinsic.circuit,
    UnitaryCircuit.indexedProduct_eventCost, ResourcePool.count_add,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ResourcePool.count_finset_sum, intrinsicInitialX_toffoli_count,
    intrinsicLowHadamards_toffoli_count]
  simp_rw [intrinsicGapStage_toffoli_count]
  simp

/-- Endpoint padding preserves the exact one-qubit count of the intrinsic
native preparation word. -/
public theorem circuit_singleQubit_count (oracles : OracleModel)
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (circuit oracles P expansion).eventCost =
        OrderPreparation.singleQubitCount expansion := by
  rw [circuit, padHigh_eventCost, Intrinsic.circuit,
    UnitaryCircuit.indexedProduct_eventCost, ResourcePool.count_add,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ResourcePool.count_finset_sum, intrinsicInitialX_single_count,
    intrinsicLowHadamards_single_count]
  simp_rw [intrinsicGapStage_single_count]
  rfl

/-- Endpoint padding preserves the exact CNOT count of the intrinsic word. -/
public theorem circuit_cnot_count (oracles : OracleModel)
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (circuit oracles P expansion).eventCost =
        OrderPreparation.cnotCount expansion := by
  rw [circuit, padHigh_eventCost, Intrinsic.circuit,
    UnitaryCircuit.indexedProduct_eventCost, ResourcePool.count_add,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ResourcePool.count_finset_sum, intrinsicInitialX_cnot_count,
    intrinsicLowHadamards_cnot_count]
  simp_rw [intrinsicGapStage_cnot_count]
  simp [OrderPreparation.cnotCount]

/-- Endpoint padding preserves the exact max-plus unit dependency depth. -/
public theorem circuit_unit_depth (oracles : OracleModel)
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    (circuit oracles P expansion).evaluatedEventDepth (fun _ => 1) =
      OrderPreparation.unitDepth expansion := by
  rw [circuit, padHigh_evaluatedEventDepth, Intrinsic.circuit,
    UnitaryCircuit.evaluatedEventDepth_indexedProduct,
    UnitaryCircuit.evaluatedEventDepth_seq, intrinsicInitialX_unit_depth,
    intrinsicLowHadamards_unit_depth]
  simp_rw [intrinsicGapStage_unit_depth]
  rfl

private theorem zero_split {source target : Nat} (within : source ≤ target) :
    (NormalizedVector.ket (R := Qubits target) 0 :
        HilbertVector (Qubits target)) =
      UnitaryCircuit.castQubitWidthVec (Nat.sub_add_cancel within)
        (HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits (target - source)) 0 :
            HilbertVector (Qubits (target - source)))
          (NormalizedVector.ket (R := Qubits source) 0 :
            HilbertVector (Qubits source))) := by
  have tensorZero :
      HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits (target - source)) 0 :
            HilbertVector (Qubits (target - source)))
          (NormalizedVector.ket (R := Qubits source) 0 :
            HilbertVector (Qubits source)) =
        (NormalizedVector.ket (R := Qubits ((target - source) + source))
          (prodEquiv (m := target - source) (n := source) (0, 0)) :
          HilbertVector (Qubits ((target - source) + source))) := by
    simpa only [NormalizedVector.coe_tensor] using congrArg
      (fun state : NormalizedVector (Qubits ((target - source) + source)) =>
        (state : HilbertVector (Qubits ((target - source) + source))))
      (NormalizedVector.tensor_ket
        (0 : Fin (2 ^ (target - source))) (0 : Fin (2 ^ source)))
  rw [tensorZero, UnitaryCircuit.castQubitWidthVec_ket]
  congr 2

private theorem paddedRangeVector_eq_state (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    UnitaryCircuit.castQubitWidthVec
      (Nat.sub_add_cancel (intrinsicWidth_le P expansion))
      (HilbertVector.tensor
        (NormalizedVector.ket
          (R := Qubits (width P - Intrinsic.width expansion)) 0 :
          HilbertVector (Qubits (width P - Intrinsic.width expansion)))
        (Intrinsic.rangeVector expansion)) =
      (state P : HilbertVector (Qubits (width P))) := by
  let same := Nat.sub_add_cancel (intrinsicWidth_le P expansion)
  let equivalence := finCongr (congrArg (fun current => 2 ^ current) same)
  apply WithLp.ofLp_injective
  funext index
  rw [UnitaryCircuit.castQubitWidthVec_apply]
  obtain ⟨⟨high, low⟩, sourceEq⟩ :=
    (prodEquiv (m := width P - Intrinsic.width expansion)
      (n := Intrinsic.width expansion)).surjective (equivalence.symm index)
  have indexEq : index = equivalence
      (prodEquiv (m := width P - Intrinsic.width expansion)
        (n := Intrinsic.width expansion) (high, low)) := by
    calc
      index = equivalence (equivalence.symm index) :=
        (equivalence.apply_symm_apply index).symm
      _ = equivalence (prodEquiv
          (m := width P - Intrinsic.width expansion)
          (n := Intrinsic.width expansion) (high, low)) :=
        congrArg equivalence sourceEq.symm
  change (HilbertVector.tensor
      (NormalizedVector.ket
        (R := Qubits (width P - Intrinsic.width expansion)) 0 :
        HilbertVector (Qubits (width P - Intrinsic.width expansion)))
      (Intrinsic.rangeVector expansion)) (equivalence.symm index) = state P index
  rw [← sourceEq, HilbertVector.tensor_apply_prod, indexEq,
    Intrinsic.rangeVector_apply, state_apply]
  by_cases highZero : high = 0
  · subst high
    have valueEq :
        (equivalence (prodEquiv
          (m := width P - Intrinsic.width expansion)
          (n := Intrinsic.width expansion) (0, low))).val = low.val := by
      simp [equivalence, prodEquiv, finProdFinEquiv]
    simp [NormalizedVector.ket_apply, valueEq]
  · have highVal : high.val ≠ 0 := by
      intro zero
      apply highZero
      exact Fin.ext zero
    have positive : 1 ≤ high.val := Nat.one_le_iff_ne_zero.mpr highVal
    have capacity : P.order ≤ 2 ^ Intrinsic.width expansion :=
      order_le_intrinsicCapacity expansion
    have notBelow : ¬(equivalence (prodEquiv
        (m := width P - Intrinsic.width expansion)
        (n := Intrinsic.width expansion) (high, low))).val < P.order := by
      intro smaller
      have lower : 2 ^ Intrinsic.width expansion ≤
          (equivalence (prodEquiv
            (m := width P - Intrinsic.width expansion)
            (n := Intrinsic.width expansion) (high, low))).val := by
        change 2 ^ Intrinsic.width expansion ≤
          low.val + 2 ^ Intrinsic.width expansion * high.val
        have scaled : 2 ^ Intrinsic.width expansion ≤
            2 ^ Intrinsic.width expansion * high.val := by
          simpa using Nat.mul_le_mul_left
            (2 ^ Intrinsic.width expansion) positive
        omega
      exact (Nat.not_lt_of_ge (capacity.trans lower)) smaller
    simp [NormalizedVector.ket_apply, highZero, notBelow]

/-- The endpoint circuit sends the all-zero exponent register to the exact
known-order range state for every positive order. -/
public theorem circuit_applyVec_zero (oracles : OracleModel)
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    (circuit oracles P expansion).applyBinaryVec
        (NormalizedVector.ket (R := Qubits (width P)) 0 :
          HilbertVector (Qubits (width P))) =
      (state P : HilbertVector (Qubits (width P))) := by
  let within := intrinsicWidth_le P expansion
  rw [zero_split within]
  change (circuit oracles P expansion).binaryMatrix.applyVec _ = _
  unfold circuit padHigh
  rw [UnitaryCircuit.castQubitWidth_binaryMatrix_applyVec,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_applyVec_tensor]
  change UnitaryCircuit.castQubitWidthVec _
      (HilbertVector.tensor _
        ((Intrinsic.circuit oracles expansion).applyBinaryVec _)) = _
  rw [Intrinsic.circuit_applyVec_zero oracles expansion
      (Nat.pos_of_ne_zero P.order_ne_zero),
    paddedRangeVector_eq_state]

/-- Normalized-state form used by the complete finite-cyclic experiment. -/
public theorem circuit_apply_zero (oracles : OracleModel)
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    (circuit oracles P expansion).binaryMatrix.apply
        (NormalizedVector.ket (R := Qubits (width P)) 0) = state P := by
  apply NormalizedVector.ext
  intro index
  change (circuit oracles P expansion).applyBinaryVec
      (NormalizedVector.ket (R := Qubits (width P)) 0 :
        HilbertVector (Qubits (width P))) index = state P index
  rw [circuit_applyVec_zero]

end

end QuantumAlg.FiniteCyclicDLP.OrderPreparation.Native
