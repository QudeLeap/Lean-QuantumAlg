/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Schedule
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Window.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Budget.Values

/-!
# Native-classical ceiling of the actual lexical three-round table fragment

Ninety-six full tables and six tail tables are each constructed once and
used six times before release. Six small-base preparations and all three
real constant-loader preparations remain paid separately. This is the
table/query fragment; no complete point-kernel resource claim is made.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open EncodedBit.WindowLookup.RuntimeTable

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

attribute [local irreducible] Frame.windowCircuit

/-- Real public constant loaders and both real base families in every round. -/
def roundPreparationClassicalBudget : Nat :=
  (4 * 256 + 3) + 2 * (2 + 16 * (16 * (30 * 256 + 127)))

/-- The original stream/window/six-call nesting fixes every table lifetime and multiplicity. -/
def roundClassicalBudget : Nat :=
  roundPreparationClassicalBudget +
    2 * (16 * windowClassicalBudget 256 8 7 + windowClassicalBudget 256 2 1)

/-- The resulting independent classical allowance retains all paid native work. -/
lemma threeRoundClassicalBudget_value : 3 * roundClassicalBudget = 20250120903 := by
  norm_num [roundClassicalBudget, roundPreparationClassicalBudget, windowClassicalBudget,
    TableFrame.constructionBudget_full16, TableFrame.constructionBudget_tail4,
    runtimeCycleClassicalLimit]

variable (spec : ModulusSpec 256) (coefficient : Nat)
  (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord 256))
  (column : Fin 6 → Fin 5)
  (full : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    Fin 3 → Fin 2 → Fin 16 → Fin 6 → QueryPlacement encoding inner 256 8 7)
  (tail : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    Fin 3 → Fin 2 → Fin 6 → QueryPlacement encoding inner 256 2 1)

/-- One actual round includes its original preparations and every short-lived table query body. -/
lemma roundCircuit_classical_weight_le (round : Fin 3)
    (path : (roundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column round full tail).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((roundCircuit spec coefficient firstX firstY secondX secondY column
        round full tail).resourcePool path) ≤ roundClassicalBudget := by
  unfold roundCircuit withCells
  apply Accounting.allocation_weight_le
  intro inner cells distinct lift separated selected
  let frame := Frame.ofCells cells distinct
  have constants := frame.initializeConstants_classical_weight_le (model := Model)
    spec coefficient selected.1
  have bases := frame.preparePairedBases_classical_weight_le (model := Model) spec
    (lift.liftInput firstX) (lift.liftInput firstY)
    (lift.liftInput secondX) (lift.liftInput secondY) selected.2.1
  have streams : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Circuit.resourcePool (Circuit.forRange 2 fun stream =>
        .seq
          (Circuit.forRange 16 fun window =>
            frame.windowCircuit spec (baseRow stream window.castSucc) column
              (fun inside occurrence =>
                full (lift.compose inside) round stream window occurrence))
          (frame.windowCircuit spec (baseRow stream ⟨16, by decide⟩) column
            (fun inside occurrence => tail (lift.compose inside) round stream occurrence)))
        selected.2.2) ≤
          2 * (16 * windowClassicalBudget 256 8 7 + windowClassicalBudget 256 2 1) := by
    apply Accounting.range_weight_le
    intro stream current
    have fullWindows := Accounting.range_weight_le 16
      (fun window => frame.windowCircuit (services := services) spec
        (baseRow stream window.castSucc) column (fun inside occurrence =>
          full (lift.compose inside) round stream window occurrence))
      Resource.Event.classicalOperationWeight (windowClassicalBudget 256 8 7)
      (fun window => frame.windowCircuit_classical_weight_le spec
        (baseRow stream window.castSucc) column _) current.1
    have last := frame.windowCircuit_classical_weight_le (services := services) spec
      (baseRow stream ⟨16, by decide⟩) column
      (fun inside occurrence => tail (lift.compose inside) round stream occurrence) current.2
    exact Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight _ _ current
      fullWindows last
  have rest := Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight _ _
    selected.2 bases streams
  have total := Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight _ _ selected
    constants rest
  simpa only [roundClassicalBudget, roundPreparationClassicalBudget, Nat.add_assoc] using total

attribute [local irreducible] roundCircuit threeRoundCircuit

/-- The actual three-round fragment has a classical bound derived from its real syntax. -/
lemma threeRoundCircuit_classical_weight_le
    (path : (threeRoundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column full tail).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((threeRoundCircuit spec coefficient firstX firstY secondX secondY column
        full tail).resourcePool path) ≤ 20250120903 := by
  unfold threeRoundCircuit at path ⊢
  exact (Accounting.range_weight_le 3 _ Resource.Event.classicalOperationWeight
    roundClassicalBudget
    (fun round => roundCircuit_classical_weight_le spec coefficient
      firstX firstY secondX secondY column full tail round) path).trans_eq
        threeRoundClassicalBudget_value

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
