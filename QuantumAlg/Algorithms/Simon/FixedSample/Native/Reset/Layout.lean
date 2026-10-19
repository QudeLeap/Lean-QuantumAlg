/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Layout
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Correction
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Two physical Simon register halves sharing the existing result cells

Each batch addresses exactly one of the two original n-wire registers.
Both use the same n distinct finite result cells, while every packed sample
slot and caller entry stays outside those writes. No context entry is split
and no additional storage is allocated.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- One of the two original physical registers, in its original wire order. -/
def positions (half : Fin 2) : Fin n ↪ Fin (context base noQuantum n count).systemCount where
  toFun index := wireEquiv n (nativeSimon_context_wires base noQuantum n count)
    (finProdFinEquiv (half, index))
  inj' _ _ same := congrArg Prod.snd (finProdFinEquiv.injective
    ((wireEquiv n (nativeSimon_context_wires base noQuantum n count)).injective same))

/-- The two batches address disjoint physical quantum systems. -/
lemma positions_separate (first second : Fin n) :
    positions base noQuantum n count 0 first ≠ positions base noQuantum n count 1 second := by
  intro same
  have halves := congrArg Prod.fst (finProdFinEquiv.injective
    ((wireEquiv n (nativeSimon_context_wires base noQuantum n count)).injective same))
  exact Fin.zero_ne_one halves

/-- Every bank position is addressed once by exactly one batch. -/
lemma positions_cover (wire : Fin (context base noQuantum n count).systemCount) :
    ∃ half index, positions base noQuantum n count half index = wire := by
  let source := (wireEquiv n (nativeSimon_context_wires base noQuantum n count)).symm wire
  refine ⟨(finProdFinEquiv.symm source).1, (finProdFinEquiv.symm source).2, ?_⟩
  change wireEquiv n (nativeSimon_context_wires base noQuantum n count)
    (finProdFinEquiv (finProdFinEquiv.symm source)) = wire
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The actual selected bank systems have the native qubit dimension. -/
lemma qubits (half : Fin 2) (index : Fin n) :
    ((context base noQuantum n count).quantumLayout.wire
      (positions base noQuantum n count half index)).dimension = 2 :=
  nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count) _

/-- Each batch writes its actual measured values into the already retained finite cells. -/
def readouts (half : Fin 2) : List (ZReadout (context base noQuantum n count)) :=
  QubitReadouts.readouts (positions base noQuantum n count half)
    (qubits base noQuantum n count half) (cells base noQuantum n count)

/-- A batch retains all n outcomes until its corresponding correction layer has run. -/
lemma cells_distinct : Function.Injective fun index : Fin n =>
    (cells base noQuantum n count index).key :=
  MeasurementCells.reference_key_injective (bankContext base noQuantum n count) 2 n

/-- Original caller data and packed sample slots are outside both batches' writes. -/
lemma readouts_separate (half : Fin 2) {shape : CShape}
    (input : CInputRef (bankContext base noQuantum n count) shape)
    (item : ZReadout (context base noQuantum n count))
    (present : item ∈ readouts base noQuantum n count half) :
    item.output.key ∉ (MeasurementCells.liftInput 2 input n).storageKeys := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  rw [QubitReadouts.readout_key]
  exact MeasurementCells.reference_not_mem_liftInput 2 input n index

/-- The parallel word uses the dimensions of those exact selected physical positions. -/
lemma dimensions (half : Fin 2) (index : Fin n) :
    ((Gate.HadamardLayer.layout n).wire index).dimension =
      ((context base noQuantum n count).quantumLayout.wire
        (positions base noQuantum n count half index)).dimension :=
  (qubits base noQuantum n count half index).symm

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
