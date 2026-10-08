/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Resources
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Space
import all QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Util.Order.Finding
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent exact-dyadic native order-finding specification

The empty runtime input admits arbitrary normalized external references.
A valid positive-width instance has a least positive order dividing the
phase-register cardinality. The complete result is one retained unsigned
word on the exact order grid, with probability one. Independent budgets
include the native source word and real stored-bit decoding.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

/-- An unsigned output lies on the exact dyadic order grid. -/
def SuccessfulOutcome (r : Nat) {t : Nat}
    (output : CShape.Value (.unsignedWord t)) : Prop :=
  match output with
  | .unsignedWord word =>
      ∃ sample : Fin r, word.val = sample.val * (2 ^ t / r)

/-- **Input.** A positive phase width, a valid modular order instance, and an
order dividing `2 ^ t`; the caller supplies a normalized state and the declared
modular-exponentiation access.

**Output.** The retained unsigned value of the measured phase word on the
exact `r`-point grid.

**Resource budget.** Independent native event, unit-depth, resident and
auxiliary formulas for the source sample and the finite decoder.

**Success.** Every valid input produces an exact-grid word with probability one.

**Source.** [dW19, qcnotes.tex:2243-2251], with the physical source circuit
and stored-bit decoder used for the same result. -/
public def problem {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (r : Nat) :
    Problem (Sampling.Native.model access) Sampling.Native.pre
      (post t width) (.unsignedWord t) where
  valid := fun _ => 0 < t ∧ OrderFinding.Input N x r ∧ r ∣ 2 ^ t
  initialization := fun _ => True
  accepts := fun _ output => SuccessfulOutcome r output
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := eventBudget access
      resident := spaceBudget t width
      auxiliary := spaceBudget t width }
  depth :=
    { duration := fun _ => 1
      limit := depthBudget t width
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
