/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Accounting
public import QuantumAlg.Core.Base.Depth.Expr
public import QuantumAlg.Core.Base.Classical.Model
public import QuantumAlg.Core.Base.Classical.Oracle
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
public import QuantumAlg.Core.Base.Accounting.Event
import all QuantumAlg.Core.Base.Accounting.Event

/-!
# Pure actual quantum duration and unit dependency depth

A pure circuit's actual syntax emits only native gate and oracle events.
Each has canonical quantum duration one in every surrounding classical
context. The proof preserves the actual sequential and parallel dependency
constructors, including compact physical embeddings and native macros.
-/

namespace QuantumAlg

noncomputable section

namespace UnitarySequence

variable {gates : GateModel} {oracles : OracleModel} {count : Nat}
  {layout : QuantumLayout count}

private lemma quantumDuration_eq_unit_depth (body : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    DepthExpr.depthEval Resource.Event.quantumDuration (body.eventDepth operations services) =
      DepthExpr.depthEval (fun _ => 1) (body.eventDepth operations services) := by
  induction body with
  | id => rfl
  | leaf value => cases value <;> rfl
  | seq left right leftIH rightIH => simp [eventDepth, leftIH, rightIH]
  | embed placement body bodyIH => exact bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp [eventDepth, leftIH, rightIH]
  | iterate repetitions body bodyIH => simp [eventDepth, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp [eventDepth, startIH, stepIH]
  | macroCall name body bodyIH => exact bodyIH

end UnitarySequence

namespace UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel} {count : Nat}
  {layout : QuantumLayout count}

/-- Pure actual quantum duration equals unit dependency depth in every classical context. -/
public lemma unitaryCircuit_quantumDuration_eq_unit_depth
    (body : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    DepthExpr.depthEval Resource.Event.quantumDuration (body.eventDepth operations services) =
      DepthExpr.depthEval (fun _ => 1) (body.eventDepth operations services) :=
  UnitarySequence.quantumDuration_eq_unit_depth body.sequence operations services

/-- The actual pure quantum duration is independent of the surrounding classical model. -/
public lemma unitaryCircuit_quantumDuration_classical_context
    (body : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    DepthExpr.depthEval Resource.Event.quantumDuration (body.eventDepth operations services) =
      body.evaluatedEventDepth Resource.Event.quantumDuration := by
  rw [unitaryCircuit_quantumDuration_eq_unit_depth,
    unitaryCircuit_unit_depth_classical_context]
  exact (unitaryCircuit_quantumDuration_eq_unit_depth body .empty .empty).symm

end UnitaryCircuit

end

end QuantumAlg
