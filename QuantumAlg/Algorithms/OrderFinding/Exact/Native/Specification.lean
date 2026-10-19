/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Util.Order.Finding
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Resources
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Resources
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Space
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
@[expose] public def SuccessfulOutcome (r : Nat) {t : Nat}
    (output : CShape.Value (.unsignedWord t)) : Prop :=
  match output with
  | .unsignedWord word =>
      ∃ sample : Fin r, word.val = sample.val * (2 ^ t / r)

/-- The unknown order and the source access assumptions belong only to the specification. -/
public structure Witness (N x t width : Nat) where
  /-- The least positive modular order asserted by the source instance. -/
  order : Nat
  /-- Source capacity and positivity assumptions for the declared modular operator. -/
  access : ModExpOracleAccess N x t width

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
@[expose] public def problem (N x t width : Nat) :
    Problem (Sampling.Native.model t width) Sampling.Native.pre
      (post t width) (.unsignedWord t) where
  Witness := Witness N x t width
  valid := fun environment witness _ =>
    environment.quantum = OrderFinding.Native.interpretation witness.access ∧
      0 < t ∧ OrderFinding.Input N x witness.order ∧ witness.order ∣ 2 ^ t
  initialization := fun _ _ _ => True
  accepts := fun _ witness _ output => SuccessfulOutcome witness.order output
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => []
  resources :=
    { events := eventBudget t width
      resident := spaceBudget t width
      auxiliary := spaceBudget t width }
  quantumTimeLimit := depthBudget t width

/-- The canonical interpretation admits exactly the original exact-dyadic source domain. -/
public lemma problem_valid_source {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (order : Nat)
    (state : ExecutionState (Execution.Store Sampling.Native.pre) Sampling.Native.pre.register) :
    (problem N x t width).valid (Sampling.Native.environment access) ⟨order, access⟩ state ↔
      0 < t ∧ OrderFinding.Input N x order ∧ order ∣ 2 ^ t := by
  constructor
  · exact fun valid => valid.2
  · exact fun valid => ⟨rfl, valid⟩

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
