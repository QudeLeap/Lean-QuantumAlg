/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Schedule
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Time.Window

/-!
# Actual three-round native quantum time with real table lifetimes

Classical preparations and actual table builds remain paid in the separate
native-classical coordinate. Their zero quantum duration is proved from
their actual pools. All physical query layers retain their own original
dependency depths, without replacing them by a total gate count.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

attribute [local irreducible] Frame.windowCircuit
attribute [local irreducible] Frame.initializeConstants Frame.preparePairedBases

/-- The actual original full and tail native mask trees have height eight. -/
def roundQuantumTimeLimit : Nat :=
  2 * (16 * (6 * queryQuantumLimit 7 8 8) + 6 * queryQuantumLimit 1 2 8)

variable (spec : ModulusSpec 256) (coefficient : Nat)
  (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord 256))
  (column : Fin 6 → Fin 5)
  (full : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    Fin 3 → Fin 2 → Fin 16 → Fin 6 → QueryPlacement encoding inner 256 8 7)
  (tail : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    Fin 3 → Fin 2 → Fin 6 → QueryPlacement encoding inner 256 2 1)
  (fullHeight : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
    round stream window occurrence, (full lift round stream window occurrence).height ≤ 8)
  (tailHeight : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
    round stream occurrence, (tail lift round stream occurrence).height ≤ 8)

include fullHeight tailHeight in
/-- One real round retains native depth through both streams and every lexical table scope. -/
lemma roundCircuit_quantumTime_le (round : Fin 3)
    (path : (roundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column round full tail).Path) :
    (roundCircuit spec coefficient firstX firstY secondX secondY column
      round full tail).depth Resource.Event.quantumDuration path ≤ roundQuantumTimeLimit := by
  unfold roundCircuit withCells
  apply withCellsFrom_depth_le
  intro inner cells distinct lift separated selected
  let frame := Frame.ofCells cells distinct
  have actual := QuantumAccounting.preparedStreams_depth_le
    Resource.Event.quantumDuration
    (frame.initializeConstants (model := Model) spec coefficient)
    (frame.preparePairedBases (model := Model) spec
      (lift.liftInput firstX) (lift.liftInput firstY)
      (lift.liftInput secondX) (lift.liftInput secondY)) 2 16
    (fun stream window => frame.windowCircuit (services := services) spec
      (baseRow stream window.castSucc) column
      (fun inside occurrence => full (lift.compose inside) round stream window occurrence))
    (fun stream => frame.windowCircuit (services := services) spec
      (baseRow stream ⟨16, by decide⟩) column
      (fun inside occurrence => tail (lift.compose inside) round stream occurrence))
    0 0 (6 * queryQuantumLimit 7 8 8) (6 * queryQuantumLimit 1 2 8)
    (fun chosen => (QuantumAccounting.quantumTime_zero _
      (fun focus nativeFree =>
        QuantumAccounting.initialization_count_zero focus nativeFree frame spec coefficient)
      chosen).le)
    (fun chosen => (QuantumAccounting.quantumTime_zero _
      (fun focus nativeFree => QuantumAccounting.pairedBases_count_zero focus nativeFree frame spec
        (lift.liftInput firstX) (lift.liftInput firstY)
        (lift.liftInput secondX) (lift.liftInput secondY)) chosen).le)
    (fun stream window => frame.windowCircuit_quantumTime_le (services := services) spec
      (baseRow stream window.castSucc) column
      (fun inside occurrence => full (lift.compose inside) round stream window occurrence) 8
      (fun inside occurrence => fullHeight (lift.compose inside) round stream window occurrence))
    (fun stream => frame.windowCircuit_quantumTime_le (services := services) spec
      (baseRow stream ⟨16, by decide⟩) column
      (fun inside occurrence => tail (lift.compose inside) round stream occurrence) 8
      (fun inside occurrence => tailHeight (lift.compose inside) round stream occurrence))
    selected
  exact actual.trans_eq ((Nat.zero_add _).trans (Nat.zero_add _))

attribute [local irreducible] roundCircuit threeRoundCircuit

include fullHeight tailHeight in
/-- Every actual table/query path preserves the original native parallel-layer allowance. -/
lemma threeRoundCircuit_quantumTime_le
    (path : (threeRoundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column full tail).Path) :
    (threeRoundCircuit spec coefficient firstX firstY secondX secondY column
      full tail).depth Resource.Event.quantumDuration path ≤ 834321528 := by
  unfold threeRoundCircuit at path ⊢
  have actual := QuantumAccounting.range_depth_le Resource.Event.quantumDuration 3 _
    roundQuantumTimeLimit (fun round => roundCircuit_quantumTime_le spec coefficient
      firstX firstY secondX secondY column full tail fullHeight tailHeight round) path
  have displayed : 3 * roundQuantumTimeLimit = 834321528 := by
    norm_num [roundQuantumTimeLimit, queryQuantumLimit]
  exact actual.trans_eq displayed

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
