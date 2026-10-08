/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit.OperationalEquiv.Range
import all QuantumAlg.Core.Execution.Circuit.OperationalEquiv.Range

/-!
# Exact rotation of repeated reset boundaries

A finite run of `reset; body` can be associated into one initial reset,
intermediate `body; reset` sections, and a final body. This only changes path
parentheses. It does not commute, omit, or duplicate an instruction.
-/

namespace QuantumAlg.Circuit.OperationalEquiv

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- The suffix after the first reset: every nonterminal section ends in the
next physical reset, while the last body keeps the finite range's final id. -/
def rotatedTail (reset body : Circuit model ctx ctx) : Nat → Circuit model ctx ctx
  | 0 => body.seq (Circuit.id (model := model) ctx)
  | count + 1 => (body.seq reset).seq (rotatedTail reset body count)

/-- Exact symbolic rotation of the boundaries of arbitrarily many attempts. -/
def rotateRange (reset body : Circuit model ctx ctx) (count : Nat) :
    OperationalEquiv
      (Circuit.forRange (count + 1) (fun _ => reset.seq body))
      (reset.seq (rotatedTail reset body count)) := by
  induction count with
  | zero =>
      change OperationalEquiv
        ((reset.seq body).seq (Circuit.id (model := model) ctx))
        (reset.seq (body.seq (Circuit.id (model := model) ctx)))
      exact Circuit.seqAssocOperationalEquiv reset body (Circuit.id ctx)
  | succ count ih =>
      change OperationalEquiv
        ((reset.seq body).seq
          (Circuit.forRange (count + 1) (fun _ => reset.seq body)))
        (reset.seq ((body.seq reset).seq (rotatedTail reset body count)))
      exact ((prepend (reset.seq body) ih).trans
        (Circuit.seqAssocOperationalEquiv reset body
          (reset.seq (rotatedTail reset body count)))).trans
        (prepend reset
          (Circuit.seqAssocOperationalEquiv body reset
            (rotatedTail reset body count)).symm)

/-- With at least two attempts, the first complete intermediate section ends
in the next actual reset, with the remaining rotated suffix unchanged. -/
def rotateRangeFirstCycle (reset body : Circuit model ctx ctx) (count : Nat) :
    OperationalEquiv
      (Circuit.forRange ((count + 1) + 1) (fun _ => reset.seq body))
      (((reset.seq body).seq reset).seq (rotatedTail reset body count)) := by
  let tail := rotatedTail reset body count
  have initial := rotateRange reset body (count + 1)
  change OperationalEquiv
    (Circuit.forRange ((count + 1) + 1) (fun _ => reset.seq body))
    (((reset.seq body).seq reset).seq tail)
  exact initial.trans
    ((prepend reset (Circuit.seqAssocOperationalEquiv body reset tail)).trans
      ((Circuit.seqAssocOperationalEquiv reset body (reset.seq tail)).symm.trans
        (Circuit.seqAssocOperationalEquiv (reset.seq body) reset tail).symm))

end

end QuantumAlg.Circuit.OperationalEquiv
