/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Builder
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Actual five-array lifetimes and allocation-free runtime queries

Each real query retains the whole caller, including all five constructed
arrays and all four scalar work words. Only the builder uses additional
arithmetic scratch. The arrays are charged once through their lexical
build/six-query/release lifetime, rather than once for every query.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

/-- Identity placement keeps every real caller role resident without a new allocation. -/
lemma QueryPlacement.liveSpace (placement : QueryPlacement encoding ctx wordWidth lowWidth
    highRemaining) (source : CInputRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth))) :
    LiveSpace.Bound 0 (placement.circuit (services := services) source) := by
  unfold LiveSpace.Bound QueryPlacement.circuit
  intro path
  rw [Circuit.peakResidentSpace_embed, Circuit.peakAuxiliarySpace_embed, zero_add, zero_add]
  exact ⟨le_rfl, le_rfl⟩

/-- The real table arrays coexist with the real reused arithmetic allowance throughout the body. -/
lemma Frame.windowCircuit_liveSpace (frame : Frame ctx wordWidth)
    (spec : ModulusSpec wordWidth) (row : Fin 34) (column : Fin 6 → Fin 5)
    (queries : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 6 → QueryPlacement encoding inner wordWidth lowWidth highRemaining) :
    LiveSpace.Bound (model := Model)
      (tableSpace .quantum wordWidth (2 ^ (highRemaining + lowWidth + 1)) +
        coefficientScratchSpace .quantum wordWidth)
      (frame.windowCircuit (services := services) spec row column queries) := by
  unfold Frame.windowCircuit withCells
  apply LiveSpace.allocate
  intro inner cells distinct lift separated
  let table := frame.tableFrame lift cells distinct separated row
  apply LiveSpace.seq
  · exact LiveSpace.builder table spec
  · apply LiveSpace.range
    intro occurrence
    exact ((queries lift occurrence).liveSpace _).mono zero_le

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
