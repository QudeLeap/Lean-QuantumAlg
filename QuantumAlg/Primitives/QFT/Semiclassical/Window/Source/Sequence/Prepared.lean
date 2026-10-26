/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence

/-!
# Complete source histories and the literal prepared sequence paths

Each physical block executes its real first circuit, native preparation and
real last circuit. The source observation omits only the native instruction's
unique unit path. The exact bijection below inserts those genuine unit paths
and the final identity path; it preserves all real measurement outcomes.
This is a record-coordinate law, not a source-preparation or Born assertion.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

/-- One original source stage beside its actual native physical preparation instruction. -/
structure PreparedStage (ctx : RuntimeCtx .quantum) (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) (Reference : Register) where
  stage : Stage ctx operations services Reference
  prepare : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout

namespace PreparedStage

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference : Register}

/-- The original reset/preparation/middle order, including the real native H instruction. -/
def code (prepared : PreparedStage ctx operations services Reference) :
    Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true :=
  prepared.stage.first.seq
    ((Circuit.unitary (operations := operations) (classicalOracles := services)
      (allowAllocation := true) prepared.prepare).seq prepared.stage.last)

/-- A structural list of the same physical blocks, ending with the actual identity instruction. -/
def sequence : List (PreparedStage ctx operations services Reference) →
    Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true
  | [] => Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := true) ctx
  | head :: rest => head.code.seq (sequence rest)

private def stageHistoryEquiv (History First Last Rest : Type) :
    ((History × First) × Last) × Rest ≃ History × ((First × (Unit × Last)) × Rest) where
  toFun value := (value.1.1.1, ((value.1.1.2, ((), value.1.2)), value.2))
  invFun value := (((value.1, value.2.1.1), value.2.1.2.2), value.2.2)
  left_inv _ := rfl
  right_inv value := by
    rcases value with ⟨history, ⟨first, nativePath, last⟩, rest⟩
    cases nativePath
    rfl

/-- Every original source history is in bijection with all actual physical sequence paths. -/
def historyEquiv : (prepared : List (PreparedStage ctx operations services Reference)) →
    (History : Type) →
      Stage.Records (prepared.map PreparedStage.stage) History ≃
        History × (sequence prepared).Path
  | [], _ =>
      { toFun := fun history => (history, ())
        invFun := Prod.fst
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨history, identityPath⟩; cases identityPath; rfl }
  | head :: rest, History =>
      (historyEquiv rest ((History × head.stage.first.Path) × head.stage.last.Path)).trans
        (stageHistoryEquiv History head.stage.first.Path head.stage.last.Path
          (sequence rest).Path)

/-- The genuine empty physical sequence retains its original history and unique identity path. -/
lemma historyEquiv_nil (History : Type) (history : History) :
    historyEquiv (ctx := ctx) (operations := operations) (services := services)
        (Reference := Reference) [] History history = (history, ()) := rfl

/-- The complete head reset and measured-last paths survive, beside the real unique native path. -/
lemma historyEquiv_cons (head : PreparedStage ctx operations services Reference)
    (rest : List (PreparedStage ctx operations services Reference)) (History : Type)
    (records : Stage.Records ((head :: rest).map PreparedStage.stage) History) :
    historyEquiv (head :: rest) History records =
      let tail := historyEquiv rest ((History × head.stage.first.Path) × head.stage.last.Path)
        records
      (tail.1.1.1, ((tail.1.1.2, ((), tail.1.2)), tail.2)) := rfl

end PreparedStage

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
