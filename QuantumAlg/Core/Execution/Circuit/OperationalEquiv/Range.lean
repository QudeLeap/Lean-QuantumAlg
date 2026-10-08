/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit.OperationalEquiv
public import QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Circuit.OperationalEquiv
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Exact equivalence of finite repeated executions

The proof composes one checked body at a time while retaining every recorded
path and weighted state. It applies at symbolic `count`; no iteration is
expanded into a fixed-size table.
-/

namespace QuantumAlg.Circuit.OperationalEquiv

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Pointwise equivalent actual bodies yield equivalent indexed finite runs. -/
def forRange (count : Nat)
    (source target : Fin count → Circuit model ctx ctx)
    (equivalent : ∀ index, OperationalEquiv (source index) (target index)) :
    OperationalEquiv (Circuit.forRange count source) (Circuit.forRange count target) := by
  induction count with
  | zero =>
      exact OperationalEquiv.refl (Circuit.id (model := model) ctx)
  | succ count ih =>
      let sourceTail : Fin count → Circuit model ctx ctx := fun index => source index.succ
      let targetTail : Fin count → Circuit model ctx ctx := fun index => target index.succ
      have tail : OperationalEquiv (Circuit.forRange count sourceTail)
          (Circuit.forRange count targetTail) :=
        ih sourceTail targetTail (fun index => equivalent index.succ)
      change OperationalEquiv
        ((source 0).seq (Circuit.forRange count sourceTail))
        ((target 0).seq (Circuit.forRange count targetTail))
      exact (OperationalEquiv.append (equivalent 0)
        (Circuit.forRange count sourceTail)).trans
          (OperationalEquiv.prepend (target 0) tail)

end

end QuantumAlg.Circuit.OperationalEquiv
