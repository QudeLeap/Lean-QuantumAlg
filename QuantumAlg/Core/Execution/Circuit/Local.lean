/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Circuit

/-!
# Local-fragment syntax facts

The predicate and endpoint equality describe the existing circuit syntax.
They do not compile, reframe or execute a circuit.
-/

namespace QuantumAlg.Circuit

/-- The allocation-free quantum/read fragment of the existing circuit language. -/
@[expose]
public def IsLocal : {allowAllocation : Bool} → {model : ExecutionModel} → {pre post : RuntimeCtx
    model.kind} →
    Circuit model pre post allowAllocation → Prop
  | _, _, _, _, .id _ => True
  | _, _, _, _, .classical _ => False
  | _, _, _, _, .classicalQuery _ => False
  | _, _, _, _, .unitary _ => True
  | _, _, _, _, .measureZ _ _ => True
  | _, _, _, _, .retain _ _ _ _ => False
  | _, _, _, _, .prepareZero _ _ _ _ _ => False
  | _, _, _, _, .seq first second => IsLocal first ∧ IsLocal second
  | _, _, _, _, .branch _ body => ∀ value, IsLocal (body value)
  | _, _, _, _, .iterate _ body => IsLocal body
  | _, _, _, _, .workspace _ _ _ _ _ => False
  | _, _, _, _, .embed _ _ => False
  | _, _, _, _, .parallelClassical _ _ _ _ => False
  | _, _, _, _, .parallelQuantum _ _ _ _ => False

/-- A member of the local fragment has exactly the same input and output context. -/
public lemma isLocal_endpoints {allowAllocation : Bool} {model : ExecutionModel} {pre post :
    RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (supported : IsLocal code) : pre = post := by
  induction code with
  | id | unitary | measureZ => rfl
  | classical | classicalQuery | retain | prepareZero | workspace
  | embed | parallelClassical | parallelQuantum =>
      exact False.elim supported
  | seq first second firstIH secondIH =>
      exact (firstIH supported.1).trans (secondIH supported.2)
  | branch input body bodyIH =>
      exact bodyIH (CShape.initialValue _) (supported _)
  | iterate => rfl

end QuantumAlg.Circuit
