/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Resources.Half

/-!
# Complete actual split-address feedback ledger

Both retained high-address traversals pay their real parity rows and native
feedback. The two physical X gates are included. These bounds hold for every
actual path, independently of the clean-workspace semantic promise.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (measured : CInputRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))

/-- The complete pool is the chronological pair of actual halves and two original X gates. -/
lemma phaseCircuit_resourcePool
    (path : (frame.phaseCircuit (services := services)
      physical sameWires measured parity table).Path) :
    (frame.phaseCircuit physical sameWires measured parity table).resourcePool path =
      ResourcePool.ofList (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        [.gate .singleQubit] +
        ((frame.halfCircuit physical sameWires measured parity (table false)).resourcePool
          path.2.1 + (ResourcePool.ofList
            (model := .quantum AlgorithmGate.model .empty BitWord.model services)
            [.gate .singleQubit] +
            (frame.halfCircuit physical sameWires measured parity (table true)).resourcePool
              path.2.2.2)) := by
  change ResourcePool.ofList
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    ([.gate .singleQubit] ++ (_ ++ ([.gate .singleQubit] ++ _))) = _
  simp only [ResourcePool.ofList_append]
  rfl

private lemma phaseCircuit_gate_count_le
    (coordinate : AlgorithmGate.Coordinate) (bound : Nat)
    (halfBound : ∀ top current, ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      ((frame.halfCircuit physical sameWires measured parity (table top)).resourcePool
        current) ≤ bound)
    (path : (frame.phaseCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      ((frame.phaseCircuit physical sameWires measured parity table).resourcePool path) ≤
        2 * (if AlgorithmGate.Coordinate.singleQubit = coordinate then 1 else 0) +
          2 * bound := by
  have left := halfBound false path.2.1
  have right := halfBound true path.2.2.2
  rw [frame.phaseCircuit_resourcePool physical sameWires measured parity table]
  simp only [ResourcePool.count_add]
  have single : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      (ResourcePool.ofList [.gate .singleQubit]) =
        if AlgorithmGate.Coordinate.singleQubit = coordinate then 1 else 0 := by
    cases coordinate <;> rfl
  rw [single]
  omega

/-- Every actual Toffoli is charged to one of the two real high-prefix traversals. -/
lemma phaseCircuit_toffoli_count_le
    (path : (frame.phaseCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
      ((frame.phaseCircuit physical sameWires measured parity table).resourcePool path) ≤
        2 * 2 ^ (highRemaining + 1) - 4 := by
  have actual := frame.phaseCircuit_gate_count_le physical sameWires measured parity table
    .toffoli (2 * (2 ^ highRemaining - 1))
    (fun top current => frame.halfCircuit_toffoli_count_le physical sameWires
      measured parity (table top) current) path
  have positive := Nat.two_pow_pos highRemaining
  simp only [reduceCtorEq, ↓reduceIte,
    Nat.mul_zero, Nat.zero_add] at actual
  rw [pow_succ]
  omega

/-- Every original masked fan-in and inverse CNOT remains in the complete feedback count. -/
lemma phaseCircuit_cnot_count_le
    (path : (frame.phaseCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((frame.phaseCircuit physical sameWires measured parity table).resourcePool path) ≤
        2 * 2 ^ (highRemaining + 1) * 2 ^ lowWidth - 2 := by
  have actual := frame.phaseCircuit_gate_count_le physical sameWires measured parity table
    .cnot ((2 ^ highRemaining - 1) +
      2 ^ highRemaining * (2 * 2 ^ lowWidth - 1))
    (fun top current => frame.halfCircuit_cnot_count_le physical sameWires
      measured parity (table top) current) path
  have positive := Nat.two_pow_pos highRemaining
  have lowPositive := Nat.two_pow_pos lowWidth
  have highSub : 2 ^ highRemaining - 1 + 1 = 2 ^ highRemaining := by omega
  have lowSub : 2 * 2 ^ lowWidth - 1 + 1 = 2 * 2 ^ lowWidth := by omega
  have lowScaled := congrArg (fun value => 2 ^ highRemaining * value) lowSub
  simp only [reduceCtorEq, ↓reduceIte, Nat.mul_zero, Nat.zero_add] at actual
  rw [pow_succ]
  apply Nat.le_sub_of_add_le
  nlinarith

/-- The actual top-bit flips, prefix flips and all leaf Hadamards are counted together. -/
lemma phaseCircuit_singleQubit_count_le
    (path : (frame.phaseCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
      ((frame.phaseCircuit physical sameWires measured parity table).resourcePool path) ≤
        4 * 2 ^ (highRemaining + 1) - 2 := by
  have actual := frame.phaseCircuit_gate_count_le physical sameWires measured parity table
    .singleQubit (2 * (2 ^ highRemaining - 1) + 2 * 2 ^ highRemaining)
    (fun top current => frame.halfCircuit_singleQubit_count_le physical sameWires
      measured parity (table top) current) path
  have positive := Nat.two_pow_pos highRemaining
  simp only [↓reduceIte, Nat.mul_one] at actual
  rw [pow_succ]
  omega

/-- Every real column clear and measured-bit XOR in both halves is paid. -/
lemma phaseCircuit_classical_weight_le
    (path : (frame.phaseCircuit (services := services)
      physical sameWires measured parity table).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.phaseCircuit physical sameWires measured parity table).resourcePool path) ≤
        2 ^ (highRemaining + 1) * 2 ^ lowWidth * (resultWidth + 1) := by
  have left := frame.halfCircuit_classical_weight_le physical sameWires measured parity
    (table false) path.2.1
  have right := frame.halfCircuit_classical_weight_le physical sameWires measured parity
    (table true) path.2.2.2
  rw [frame.phaseCircuit_resourcePool physical sameWires measured parity table]
  simp only [ResourcePool.weightedCount_add, ResourcePool.weightedCount_ofList,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Resource.Event.classicalOperationWeight, Nat.zero_add]
  rw [pow_succ]
  nlinarith

/-- The physical fan-in layers retain their original parallel depth in both actual halves. -/
lemma phaseCircuit_quantumTime_le
    (path : (frame.phaseCircuit (services := services)
      physical sameWires measured parity table).Path) :
    (frame.phaseCircuit physical sameWires measured parity table).depth
      Resource.Event.quantumDuration path ≤
        (2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8 := by
  have left := frame.halfCircuit_quantumTime_le physical sameWires measured parity
    (table false) path.2.1
  have right := frame.halfCircuit_quantumTime_le physical sameWires measured parity
    (table true) path.2.2.2
  change 1 + ((frame.halfCircuit physical sameWires measured parity (table false)).depth
    Resource.Event.quantumDuration path.2.1 +
    (1 + (frame.halfCircuit physical sameWires measured parity (table true)).depth
      Resource.Event.quantumDuration path.2.2.2)) ≤ _
  have positive := Nat.two_pow_pos highRemaining
  have highSub : 2 ^ highRemaining - 1 + 1 = 2 ^ highRemaining := by omega
  rw [pow_succ]
  apply Nat.le_sub_of_add_le
  nlinarith

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
