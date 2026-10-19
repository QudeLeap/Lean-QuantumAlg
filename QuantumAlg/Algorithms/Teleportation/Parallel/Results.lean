/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Store.Instrument.Target
import all QuantumAlg.Algorithms.Teleportation.Parallel.Target
import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Classical.Support.Target
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Full measured teleportation state contract

The real final store blocks retain the complete quantum system and external
reference. Their exact unnormalized matrices determine their actual masses.
Grouping by the stored result preserves the output-dependent mixed target,
including zero-mass blocks, without selecting a new admitted input.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.Results

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual run's complete final-store block has the independent full joint target. -/
lemma full_store_matrix (environment : model.Environment) (count : Nat) {Reference : Register}
    (input : OracleInput .empty (context count) Reference)
    (admitted : localBellMarginal count input.caller.localState.quantumMarginal =
      DensityOperator.ofPure (bellBank count)) (stored : Store (context count)) :
    ((((algorithm count).run.finalState environment) Reference input.state).block stored).matrix =
      ((1 / 4 : Real) ^ count) •
        (Target.target count input.caller (stored.read (resultInput count))).matrix := by
  let recorded : State (context count) Reference (model.HiddenState × Store (context count)) :=
    input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have storedMatrix :
      ((((algorithm count).run.finalState environment) Reference input.state).block stored).matrix =
        (ExecutionState.filterClassical (((code count).execute environment) Reference recorded)
          (fun entry => entry.1 = stored)).quantumMarginal.matrix :=
    BasisSeeded.store_matrix (((code count).execute environment) Reference recorded) stored
  ext ⟨row, leftRef⟩ ⟨column, rightRef⟩
  exact (congrArg
    (fun matrix : HilbertOperator ((context count).register.prod Reference) =>
      matrix (row, leftRef) (column, rightRef)) storedMatrix).trans
        (StoreInstrument.code_store_target_entry environment count input admitted stored
          row column leftRef rightRef)

private lemma mixed_of_matrix {R : Register} (actual target : DensityOperator R)
    (normalized : target.IsNormalized) (weight : Real)
    (matrixEquation : actual.matrix = weight • target.matrix) :
    (StatePromise.mixed target normalized).Holds actual := by
  have actualMass : actual.mass = weight := by
    change actual.matrix.trace.re = weight
    rw [matrixEquation, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    change weight * target.mass = weight
    rw [normalized, mul_one]
  change actual.matrix = actual.mass • target.matrix
  exact matrixEquation.trans
    (congrArg (fun coefficient : Real => coefficient • target.matrix) actualMass.symm)

/-- The original local promise proves every full-layout, reference-aware output block. -/
lemma requirement_holds (environment : model.Environment) (count : Nat) {Reference : Register}
    (input : OracleInput .empty (context count) Reference)
    (admitted : localBellMarginal count input.caller.localState.quantumMarginal =
      DensityOperator.ofPure (bellBank count)) :
    (Target.requirement count).Holds input.caller
      (((algorithm count).run.finalState environment) Reference input.state) := by
  intro value
  apply StatePromise.mixed_fullSelection (context count).quantumLayout Reference
    (Target.target count input.caller value)
    (Target.target_normalized count input.caller value)
  exact ExecutionState.mapClassical_mixed_target
    (((algorithm count).run.finalState environment) Reference input.state)
    (fun stored => stored.read (resultInput count))
    (Target.target count input.caller)
    (Target.target_normalized count input.caller)
    (fun stored => mixed_of_matrix _ _
      (Target.target_normalized count input.caller (stored.read (resultInput count)))
      ((1 / 4 : Real) ^ count) (full_store_matrix environment count input admitted stored)) value

end

end QuantumAlg.QuantumTeleportation.Parallel.Results
