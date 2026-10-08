/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded.Admission
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Completion

/-!
# The genuine initialized and completed producers supply local physical admission

Each continuation consumes the actual prefix's next input. Only mathematical
execution histories are grouped; actual stores, quantum blocks and persistent
service state remain. The original initializer and completed feedback/reset
each supply the independent fixed-basis local domain for every reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual initialization supplies the local fixed-zero domain in its genuine next input. -/
theorem Initialized.nextInput_local_support (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    {Reference : Register}
    (original : OracleInput (executionModel input).classicalOracles base Reference)
    (entry : Store (Initialized.bank base noQuantum N) × (executionModel input).HiddenState)
    (basis : (Initialized.bank base noQuantum N).register.Index)
    (outside : basis ≠ (Initialized.bank base noQuantum N).quantumLayout.zeroLabel) :
    (((Initialized.ready base noQuantum N input).nextInput original).localState.block entry).matrix
      basis basis = 0 := by
  let actual := Initialized.ready base noQuantum N input
  let entered := original.state.mapClassical (fun entry => (entry.1, (entry.2, ())))
  have grouped : BasisSeeded.Holds (Initialized.bank base noQuantum N).quantumLayout.zeroLabel
      (actual.nextInput original).state :=
    BasisSeeded.mapStore (Initialized.bank base noQuantum N).quantumLayout.zeroLabel
      (actual.execute Reference entered) (Initialized.ready_seeded base noQuantum N input entered)
      id (fun record => record.2.1)
  exact BasisSeeded.block_marginal_support
    (Initialized.bank base noQuantum N).quantumLayout.zeroLabel
    (actual.nextInput original).state grouped entry basis outside

/-- Complete real recovery and reset supply that same local domain for the next actual round. -/
theorem Completion.nextInput_local_support (ctx : RuntimeCtx .quantum) (N : Nat)
    (input : Input N) (sameWires : ctx.quantumWires = (layout N).wires)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {Reference : Register}
    (original : OracleInput (executionModel input).classicalOracles ctx Reference)
    (entry : Store (Iteration.context ctx N) × (executionModel input).HiddenState)
    (basis : (Iteration.context ctx N).register.Index)
    (outside : basis ≠ (Iteration.context ctx N).quantumLayout.zeroLabel) :
    (((Completion.code ctx N input sameWires cells result).nextInput
      original).localState.block entry).matrix basis basis = 0 := by
  let actual := Completion.code ctx N input sameWires cells result
  let entered := original.state.mapClassical (fun entry => (entry.1, (entry.2, ())))
  have grouped : BasisSeeded.Holds (Iteration.context ctx N).quantumLayout.zeroLabel
      (actual.nextInput original).state :=
    BasisSeeded.mapStore (Iteration.context ctx N).quantumLayout.zeroLabel
      (actual.execute Reference entered)
      (Completion.code_seeded ctx N input sameWires cells result entered)
      id (fun record => record.2.1)
  exact BasisSeeded.block_marginal_support (Iteration.context ctx N).quantumLayout.zeroLabel
    (actual.nextInput original).state grouped entry basis outside

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
