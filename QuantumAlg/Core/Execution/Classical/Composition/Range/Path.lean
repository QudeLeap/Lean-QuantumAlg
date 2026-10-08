/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Range
import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual component paths of finite indexed execution

Each component path is projected from the complete chronological execution path.
Its exact events and dependency depth then compose by concatenation and addition.
A component may contain parallel operations; its depth is not replaced by the
sum of the durations in a linear event list.
-/

namespace QuantumAlg.Circuit

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Project each body's actual path from the existing finite sequential path. -/
def forRangeComponentPath : (count : Nat) → (body : Fin count → Circuit model ctx ctx) →
    (forRange count body).Path → (index : Fin count) → (body index).Path
  | 0, _, _, index => Fin.elim0 index
  | count + 1, body, path, index =>
      Fin.cases path.1 (fun next =>
        forRangeComponentPath count (fun item => body item.succ) path.2 next) index

/-- Concatenation retains the complete native trace of every actual component. -/
theorem forRange_eventTrace_eq (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (path : (forRange count body).Path) :
    (forRange count body).eventTrace path =
      (List.ofFn fun index =>
        (body index).eventTrace (forRangeComponentPath count body path index)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.flatten_cons]
      change (body 0).eventTrace path.1 ++
        (forRange count (fun index => body index.succ)).eventTrace path.2 =
          (body 0).eventTrace path.1 ++
            (List.ofFn fun index => (body index.succ).eventTrace
              (forRangeComponentPath count (fun item => body item.succ) path.2 index)).flatten
      rw [ih]

/-- Exact event multiplicities include each component's complete actual expansion. -/
theorem forRange_eventCount_eq_sum (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (path : (forRange count body).Path) :
    ((forRange count body).eventTrace path).length =
      ∑ index, ((body index).eventTrace (forRangeComponentPath count body path index)).length := by
  induction count with
  | zero => exact (Fin.sum_univ_zero _).symm
  | succ count ih =>
      rw [Fin.sum_univ_succ]
      change ((body 0).eventTrace path.1 ++
        (forRange count (fun index => body index.succ)).eventTrace path.2).length = _
      rw [List.length_append, ih]
      rfl

/-- Sequential composition adds actual dependency depths without flattening internal parallelism. -/
theorem forRange_depth_eq_sum (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (duration : Resource.Event model → Nat) (path : (forRange count body).Path) :
    (forRange count body).depth duration path =
      ∑ index, (body index).depth duration (forRangeComponentPath count body path index) := by
  induction count with
  | zero => exact (Fin.sum_univ_zero _).symm
  | succ count ih =>
      rw [Fin.sum_univ_succ]
      change (body 0).depth duration path.1 +
        (forRange count (fun index => body index.succ)).depth duration path.2 = _
      rw [ih]
      rfl

end QuantumAlg.Circuit
