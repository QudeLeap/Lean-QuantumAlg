/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Circuit.OperationalEquiv.Rotation

/-!
# Structural regrouping of arbitrary finite ranges

The same actual sections are unfolded and regrouped by symbolic induction.
Every nonterminal body ends at the following original reset. No instruction
is commuted, omitted or added, and no fixed retry count is expanded.
-/

namespace QuantumAlg.Circuit.Reassociation

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Pointwise regrouping of the same bodies preserves the literal finite range. -/
def forRange (count : Nat) (source target : Fin count → Circuit model ctx ctx)
    (sameBodies : ∀ index, Reassociation (source index) (target index)) :
    Reassociation (Circuit.forRange count source) (Circuit.forRange count target) := by
  induction count with
  | zero => exact .refl (Circuit.id (model := model) ctx)
  | succ count ih =>
      let sourceTail : Fin count → Circuit model ctx ctx := fun index => source index.succ
      let targetTail : Fin count → Circuit model ctx ctx := fun index => target index.succ
      have tail : Reassociation (Circuit.forRange count sourceTail)
          (Circuit.forRange count targetTail) :=
        ih sourceTail targetTail (fun index => sameBodies index.succ)
      change Reassociation
        ((source 0).seq (Circuit.forRange count sourceTail))
        ((target 0).seq (Circuit.forRange count targetTail))
      exact .seq (sameBodies 0) tail

/-- Expose the first reset and the unchanged actual body/reset suffix. -/
def rotateRange (reset body : Circuit model ctx ctx) (count : Nat) :
    Reassociation (Circuit.forRange (count + 1) (fun _ => reset.seq body))
      (reset.seq (OperationalEquiv.rotatedTail reset body count)) := by
  induction count with
  | zero =>
      change Reassociation ((reset.seq body).seq (Circuit.id (model := model) ctx))
        (reset.seq (body.seq (Circuit.id (model := model) ctx)))
      exact .seqAssoc reset body (Circuit.id ctx)
  | succ count ih =>
      change Reassociation
        ((reset.seq body).seq (Circuit.forRange (count + 1) (fun _ => reset.seq body)))
        (reset.seq ((body.seq reset).seq (OperationalEquiv.rotatedTail reset body count)))
      exact ((Reassociation.seq (.refl (reset.seq body)) ih).trans
        (.seqAssoc reset body (reset.seq (OperationalEquiv.rotatedTail reset body count)))).trans
        (.seq (.refl reset)
          (Reassociation.seqAssoc body reset (OperationalEquiv.rotatedTail reset body count)).symm)

/-- At least two symbolic attempts expose the first real reset-bounded section. -/
def rotateRangeFirstCycle (reset body : Circuit model ctx ctx) (count : Nat) :
    Reassociation (Circuit.forRange ((count + 1) + 1) (fun _ => reset.seq body))
      (((reset.seq body).seq reset).seq (OperationalEquiv.rotatedTail reset body count)) := by
  let tail := OperationalEquiv.rotatedTail reset body count
  change Reassociation (Circuit.forRange ((count + 1) + 1) (fun _ => reset.seq body))
    (((reset.seq body).seq reset).seq tail)
  exact (rotateRange reset body (count + 1)).trans
    ((Reassociation.seq (.refl reset) (.seqAssoc body reset tail)).trans
      ((Reassociation.seqAssoc reset body (reset.seq tail)).symm.trans
        (Reassociation.seqAssoc (reset.seq body) reset tail).symm))

end

end QuantumAlg.Circuit.Reassociation
