/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Full actual space from single bank preparation through all sampling rounds

The actual preparation visits the original context and the one allocated
bank context. That same physical bank remains throughout every true sampling,
reset and reload iteration. All retained tuples and intermediate sampler
workspace contribute to the existing independent finite-batch allowance.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativePreparedBatch

noncomputable section

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = []) (N count : Nat)

/-- Exact actual final resident capacity includes the single bank and every retained tuple. -/
theorem context_resident :
    (context ctx noQuantum N count).residentSpace =
      (NativeBank.context ctx noQuantum N).residentSpace +
        SpacePool.ofShape (.bits (count * (22 * modulusBits N + 1))) :=
  NativeBatch.context_resident (NativeBank.context ctx noQuantum N) N count

private theorem prepare_resident_le (path : (NativeBank.prepare ctx noQuantum N).Path) :
    (NativeBank.prepare ctx noQuantum N).peakResidentSpace path ≤
      (NativeBank.context ctx noQuantum N).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have location : visited = ctx ∨ visited = NativeBank.context ctx noQuantum N := by
    change visited ∈ [ctx, NativeBank.context ctx noQuantum N] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
  rcases location with old | prepared
  · subst visited
    rw [NativeBank.resident]
    exact fun _ => Nat.le_add_left _ _
  · subst visited
    exact le_rfl

/-- One preparation and the same-bank rounds obey the full independent resident batch allowance. -/
theorem resident_le (path : (code ctx noQuantum N count).Path) :
    (code ctx noQuantum N count).peakResidentSpace path ≤
      (NativeBank.context ctx noQuantum N).residentSpace +
        SpacePool.ofShape (.bits (NativeBatch.additionalBits N count)) := by
  refine (Circuit.peakResidentSpace_seq (NativeBank.prepare ctx noQuantum N)
    (NativeBatch.code (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count) path).le.trans ?_
  exact SpacePool.max_le
    ((prepare_resident_le ctx noQuantum N path.1).trans (fun _ => Nat.le_add_right _ _))
    (NativeBatch.resident_le (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count path.2)

/-- Exact actual final auxiliary capacity includes the single bank and every retained tuple. -/
theorem context_auxiliary :
    (context ctx noQuantum N count).auxiliarySpace =
      (NativeBank.context ctx noQuantum N).auxiliarySpace +
        SpacePool.ofShape (.bits (count * (22 * modulusBits N + 1))) :=
  NativeBatch.context_auxiliary (NativeBank.context ctx noQuantum N) N count

private theorem prepare_auxiliary_le (path : (NativeBank.prepare ctx noQuantum N).Path) :
    (NativeBank.prepare ctx noQuantum N).peakAuxiliarySpace path ≤
      (NativeBank.context ctx noQuantum N).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have location : visited = ctx ∨ visited = NativeBank.context ctx noQuantum N := by
    change visited ∈ [ctx, NativeBank.context ctx noQuantum N] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
  rcases location with old | prepared
  · subst visited
    rw [NativeBank.auxiliary]
    exact fun _ => Nat.le_add_left _ _
  · subst visited
    exact le_rfl

/-- One preparation and the same-bank rounds obey the full independent auxiliary batch allowance. -/
theorem auxiliary_le (path : (code ctx noQuantum N count).Path) :
    (code ctx noQuantum N count).peakAuxiliarySpace path ≤
      (NativeBank.context ctx noQuantum N).auxiliarySpace +
        SpacePool.ofShape (.bits (NativeBatch.additionalBits N count)) := by
  refine (Circuit.peakAuxiliarySpace_seq (NativeBank.prepare ctx noQuantum N)
    (NativeBatch.code (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count) path).le.trans ?_
  exact SpacePool.max_le
    ((prepare_auxiliary_le ctx noQuantum N path.1).trans (fun _ => Nat.le_add_right _ _))
    (NativeBatch.auxiliary_le (NativeBank.context ctx noQuantum N) N
      (NativeBank.quantumWires ctx noQuantum N) count path.2)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativePreparedBatch
