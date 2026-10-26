/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Schedule
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Window
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Preparation

/-!
# Independent quantum coordinates of the actual table-lifetime schedule

All constants, base families and full table builders remain actual paid
classical code. Their quantum coordinates vanish separately. Every real
query retains its own native CNOT, Toffoli and measurement coordinates.
This is a table/query fragment, with no point-arithmetic resource claim.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open EncodedBit.WindowLookup EncodedBit.WindowLookup.RuntimeTable

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

attribute [local irreducible] Frame.windowCircuit
attribute [local irreducible] Frame.initializeConstants Frame.preparePairedBases

variable (spec : ModulusSpec 256) (coefficient : Nat)
  (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord 256))
  (column : Fin 6 → Fin 5)
  (full : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    Fin 3 → Fin 2 → Fin 16 → Fin 6 → QueryPlacement encoding inner 256 8 7)
  (tail : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    Fin 3 → Fin 2 → Fin 6 → QueryPlacement encoding inner 256 2 1)
  (focus : Resource.Event
    (.quantum AlgorithmGate.model OracleModel.empty BitWord.model services))
  (nativeFree : ∀ coordinate, focus ≠ .classicalOperation coordinate)
  (fullLimit tailLimit : Nat)
  (fullBound : ∀ {inner : RuntimeCtx .quantum}
    (placement : QueryPlacement encoding inner 256 8 7)
    (source : CInputRef inner (.fixedVector (2 ^ 16) (.unsignedWord 256)))
    (path : (placement.circuit (services := services) source).Path),
    ResourcePool.count focus
      ((placement.circuit (services := services) source).resourcePool path) ≤ fullLimit)
  (tailBound : ∀ {inner : RuntimeCtx .quantum}
    (placement : QueryPlacement encoding inner 256 2 1)
    (source : CInputRef inner (.fixedVector (2 ^ 4) (.unsignedWord 256)))
    (path : (placement.circuit (services := services) source).Path),
    ResourcePool.count focus
      ((placement.circuit (services := services) source).resourcePool path) ≤ tailLimit)

include nativeFree fullBound tailBound in
/-- The actual stream nesting retains six query pairs inside each real table lifetime. -/
lemma roundCircuit_quantum_count_le (round : Fin 3)
    (path : (roundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column round full tail).Path) :
    ResourcePool.count focus ((roundCircuit spec coefficient firstX firstY secondX secondY column
      round full tail).resourcePool path) ≤ 2 * (16 * (6 * fullLimit) + 6 * tailLimit) := by
  unfold roundCircuit withCells
  apply QuantumAccounting.allocation_count_le
  intro inner cells distinct lift separated selected
  let frame := Frame.ofCells cells distinct
  have constants := QuantumAccounting.initialization_count_zero focus nativeFree frame
    spec coefficient selected.1
  have bases := QuantumAccounting.pairedBases_count_zero focus nativeFree frame spec
    (lift.liftInput firstX) (lift.liftInput firstY)
    (lift.liftInput secondX) (lift.liftInput secondY) selected.2.1
  have streams : ResourcePool.count focus
      (Circuit.resourcePool (Circuit.forRange 2 fun stream =>
        .seq
          (Circuit.forRange 16 fun window =>
            frame.windowCircuit spec (baseRow stream window.castSucc) column
              (fun inside occurrence =>
                full (lift.compose inside) round stream window occurrence))
          (frame.windowCircuit spec (baseRow stream ⟨16, by decide⟩) column
            (fun inside occurrence => tail (lift.compose inside) round stream occurrence)))
        selected.2.2) ≤ 2 * (16 * (6 * fullLimit) + 6 * tailLimit) := by
    apply QuantumAccounting.range_count_le
    intro stream current
    have fullWindows := QuantumAccounting.range_count_le focus 16
      (fun window => frame.windowCircuit (services := services) spec
        (baseRow stream window.castSucc) column (fun inside occurrence =>
          full (lift.compose inside) round stream window occurrence)) (6 * fullLimit)
      (fun window => frame.windowCircuit_quantum_count_le spec
        (baseRow stream window.castSucc) column
        (fun inside occurrence => full (lift.compose inside) round stream window occurrence)
        focus nativeFree fullLimit fullBound) current.1
    have last := frame.windowCircuit_quantum_count_le (services := services) spec
      (baseRow stream ⟨16, by decide⟩) column
      (fun inside occurrence => tail (lift.compose inside) round stream occurrence)
      focus nativeFree tailLimit tailBound current.2
    rw [Circuit.resourcePool_count_seq]
    exact Nat.add_le_add fullWindows last
  rw [Circuit.resourcePool_count_seq, Circuit.resourcePool_count_seq, constants, bases,
    Nat.zero_add, Nat.zero_add]
  exact streams

attribute [local irreducible] roundCircuit threeRoundCircuit

include nativeFree fullBound tailBound in
/-- All three actual rounds retain the independent selected native coordinate. -/
lemma threeRoundCircuit_quantum_count_le
    (path : (threeRoundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column full tail).Path) :
    ResourcePool.count focus ((threeRoundCircuit spec coefficient firstX firstY secondX secondY
      column full tail).resourcePool path) ≤ 3 * (2 * (16 * (6 * fullLimit) + 6 * tailLimit)) := by
  unfold threeRoundCircuit at path ⊢
  exact QuantumAccounting.range_count_le focus 3 _ _
    (fun round => roundCircuit_quantum_count_le spec coefficient firstX firstY secondX secondY
      column full tail focus nativeFree fullLimit tailLimit fullBound tailBound round) path

/-- CNOT has its own bound, independent of the paid native-classical coordinate. -/
lemma threeRoundCircuit_cnot_count_le
    (path : (threeRoundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column full tail).Path) :
    ResourcePool.count (model := Model) (.gate .cnot)
      ((threeRoundCircuit spec coefficient firstX firstY secondX secondY column
        full tail).resourcePool path) ≤ 19403437896 := by
  have actual := threeRoundCircuit_quantum_count_le spec coefficient firstX firstY secondX secondY
    column full tail (.gate .cnot) (fun _ same => by cases same)
    (staticCycleCnotLimit 256 7 8) (staticCycleCnotLimit 256 1 2)
    (fun placement source selected =>
      placement.circuit_cnot_count_le (services := services) source selected)
    (fun placement source selected =>
      placement.circuit_cnot_count_le (services := services) source selected)
    path
  norm_num [staticCycleCnotLimit] at actual ⊢
  exact actual

/-- Toffolis are paid by their actual native query instructions, with no classical exchange. -/
lemma threeRoundCircuit_toffoli_count_le
    (path : (threeRoundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column full tail).Path) :
    ResourcePool.count (model := Model) (.gate .toffoli)
      ((threeRoundCircuit spec coefficient firstX firstY secondX secondY column
        full tail).resourcePool path) ≤ 76082904 := by
  have actual := threeRoundCircuit_quantum_count_le spec coefficient firstX firstY secondX secondY
    column full tail (.gate .toffoli) (fun _ same => by cases same) 132086 38
    (fun placement source selected =>
      placement.circuit_toffoli_count_le (services := services) source selected)
    (fun placement source selected =>
      placement.circuit_toffoli_count_le (services := services) source selected) path
  norm_num at actual ⊢
  exact actual

/-- Every real query physically measures its original 256 result systems. -/
lemma threeRoundCircuit_measurement_count_le
    (path : (threeRoundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column full tail).Path) :
    ResourcePool.count (model := Model) (.measurement (2 : ℕ+))
      ((threeRoundCircuit spec coefficient firstX firstY secondX secondY column
        full tail).resourcePool path) ≤ 156672 := by
  have actual := threeRoundCircuit_quantum_count_le spec coefficient firstX firstY secondX secondY
    column full tail (.measurement (2 : ℕ+)) (fun _ same => by cases same) 256 256
    (fun placement source selected =>
      (placement.circuit_measurement_count (services := services) source selected).le)
    (fun placement source selected =>
      (placement.circuit_measurement_count (services := services) source selected).le) path
  norm_num at actual ⊢
  exact actual

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
