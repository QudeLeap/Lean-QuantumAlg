/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Measurement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Extraction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Readout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Packed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.Measurement
import all QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Distribution
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Base.State.Density
import Mathlib.Data.List.OfFn

/-!
# Exact old runtime readout frequencies and complete physical Store writes

The actual measurement labels are proved
equivalent to both canonical exponent frequencies. Consequently the complete
old packedBasisStore, including every untouched prior cell, depends only on
those frequencies. This is derived from the literal real measurement paths
and existing charged packing, not merely from the final packed output value.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordReadout

noncomputable section

variable {environment : RuntimeRound.model.Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma labelsAgree_iff {ctx : RuntimeCtx .quantum} (readouts : List (ZReadout ctx))
    (left right : ctx.register.Index) :
    Circuit.measurementLabelsAgree readouts left right ↔
      ∀ item ∈ readouts, left item.wire = right item.wire := by
  induction readouts with
  | nil => simp [Circuit.measurementLabelsAgree]
  | cons head tail induction => simp [Circuit.measurementLabelsAgree, induction]

private lemma same_writes {ctx : RuntimeCtx .quantum} (readouts : List (ZReadout ctx))
    (left right : ctx.register.Index) (agree : Circuit.measurementLabelsAgree readouts left right)
    (original : Store ctx) :
    Circuit.writeMeasurementPath (allowAllocation := true) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := BitWord.model) (classicalOracles := .empty)
        readouts original
        (Circuit.measurementBasisPath (allowAllocation := true) (gates := AlgorithmGate.model)
          (oracles := .empty) (operations := BitWord.model) (classicalOracles := .empty)
          readouts left) =
      Circuit.writeMeasurementPath (allowAllocation := true) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := BitWord.model) (classicalOracles := .empty)
        readouts original
        (Circuit.measurementBasisPath (allowAllocation := true) (gates := AlgorithmGate.model)
          (oracles := .empty) (operations := BitWord.model) (classicalOracles := .empty)
          readouts right) := by
  revert agree
  induction readouts generalizing original with
  | nil => intro _; rfl
  | cons head tail induction =>
      intro agree
      change left head.wire = right head.wire ∧
        Circuit.measurementLabelsAgree tail left right at agree
      simp only [Circuit.writeMeasurementPath, Circuit.measurementBasisPath]
      rw [agree.1]
      exact induction _ agree.2

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))

/-- The old actual source measurement is the canonical combined frequency, independently of work. -/
lemma source_readout_frequency
    (basis : Fin (2 ^ totalQubits (registerParameters m ell width))) :
    (ShortDLP.measurement (registerParameters m ell width)).readout basis =
      BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width)
        (prodEquiv (FullWordExtraction.frequency m ell width basis)) := by
  obtain ⟨⟨⟨first, second⟩, workspace⟩, rfl⟩ :=
    (tripleEquiv (registerParameters m ell width)).surjective basis
  change (ShortDLP.measurement (registerParameters m ell width)).readout
      (prodEquiv (prodEquiv (first, second), workspace)) = _
  rw [BornProbability.shortDLPMeasurement_readout_triple]
  change _ = BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width)
    (prodEquiv (((tripleEquiv (registerParameters m ell width)).symm
      ((tripleEquiv (registerParameters m ell width)) ((first, second), workspace))).1))
  rw [Equiv.symm_apply_apply]

private lemma labelsAgree_readout (left right : ctx.register.Index) :
    Circuit.measurementLabelsAgree (RuntimeRound.readouts m ell width sameWires cells)
        left right ↔
      (ShortDLP.measurement (registerParameters m ell width)).readout
          (RuntimePlacement.basisEquiv m ell width sameWires left) =
        (ShortDLP.measurement (registerParameters m ell width)).readout
          (RuntimePlacement.basisEquiv m ell width sameWires right) := by
  rw [labelsAgree_iff, RuntimeRound.readouts, List.forall_mem_ofFn_iff]
  constructor
  · intro same
    funext index
    rw [← RuntimeRound.shortDLP_runtimeMeasuredWire_bit,
      ← RuntimeRound.shortDLP_runtimeMeasuredWire_bit]
    exact congrArg (fun value : Nat => decide (value = 1)) (congrArg Fin.val (same index))
  · intro same index
    apply Fin.ext
    have bits := congrFun same index
    rw [← RuntimeRound.shortDLP_runtimeMeasuredWire_bit,
      ← RuntimeRound.shortDLP_runtimeMeasuredWire_bit] at bits
    have equalOne := decide_eq_decide.mp bits
    have dimension :
        ((ctx.quantumLayout.wire
          (RuntimeRound.measuredWire m ell width sameWires index)).dimension : Nat) = 2 :=
      congrArg (fun value : PNat => (value : Nat))
        (RuntimeRound.shortDLP_runtimeMeasuredWire_dimension m ell width sameWires index)
    have firstBound : (left (RuntimeRound.measuredWire m ell width sameWires index)).val < 2 :=
      (congrArg (fun bound : Nat =>
        (left (RuntimeRound.measuredWire m ell width sameWires index)).val < bound)
        dimension).mp (left (RuntimeRound.measuredWire m ell width sameWires index)).isLt
    have secondBound : (right (RuntimeRound.measuredWire m ell width sameWires index)).val < 2 :=
      (congrArg (fun bound : Nat =>
        (right (RuntimeRound.measuredWire m ell width sameWires index)).val < bound)
        dimension).mp (right (RuntimeRound.measuredWire m ell width sameWires index)).isLt
    change (left (RuntimeRound.measuredWire m ell width sameWires index)).val =
      (right (RuntimeRound.measuredWire m ell width sameWires index)).val
    omega

/-- Both real measured label vectors agree exactly when their two canonical frequencies agree. -/
lemma labelsAgree_frequency (left right : ctx.register.Index) :
    Circuit.measurementLabelsAgree (RuntimeRound.readouts m ell width sameWires cells)
        left right ↔
      FullWordExtraction.frequency m ell width
          (RuntimePlacement.basisEquiv m ell width sameWires left) =
        FullWordExtraction.frequency m ell width
          (RuntimePlacement.basisEquiv m ell width sameWires right) := by
  rw [labelsAgree_readout, source_readout_frequency, source_readout_frequency,
    (BornProbability.shortDLPMeasurementOutcome_injective (registerParameters m ell width)).eq_iff,
    prodEquiv.injective.eq_iff]

/-- Equal real frequencies give the same entire final Store, including every original cell. -/
lemma packedBasisStore_eq_of_frequency
    (result : CWriteRef ctx (.bits (RuntimeRound.resultBits m ell width)))
    (original : Store ctx) (left right : ctx.register.Index)
    (same : FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires left) =
      FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires right)) :
    RuntimeRound.packedBasisStore m ell width sameWires cells result original left =
      RuntimeRound.packedBasisStore m ell width sameWires cells result original right := by
  unfold RuntimeRound.packedBasisStore
  rw [same_writes (RuntimeRound.readouts m ell width sameWires cells) left right
    ((labelsAgree_frequency m ell width sameWires cells left right).mpr same)]

/-- An ordinary representative names the already derived frequency-only write function. -/
def frequencyStore (result : CWriteRef ctx (.bits (RuntimeRound.resultBits m ell width)))
    (original : Store ctx) (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) : Store ctx :=
  RuntimeRound.packedBasisStore m ell width sameWires cells result original
    ((RuntimePlacement.basisEquiv m ell width sameWires).symm
      (tripleIndex (registerParameters m ell width) first second 0))

/-- This representative preserves the real writes without executing an extra operation. -/
lemma packedBasisStore_frequencyStore
    (result : CWriteRef ctx (.bits (RuntimeRound.resultBits m ell width)))
    (original : Store ctx) (basis : ctx.register.Index) :
    RuntimeRound.packedBasisStore m ell width sameWires cells result original basis =
      frequencyStore m ell width sameWires cells result original
        (FullWordExtraction.frequency m ell width
          (RuntimePlacement.basisEquiv m ell width sameWires basis)).1
        (FullWordExtraction.frequency m ell width
          (RuntimePlacement.basisEquiv m ell width sameWires basis)).2 := by
  apply packedBasisStore_eq_of_frequency
  rw [Equiv.apply_symm_apply]
  change _ = ((tripleEquiv (registerParameters m ell width)).symm
    ((tripleEquiv (registerParameters m ell width))
      (FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires basis), 0))).1
  rw [Equiv.symm_apply_apply]

/-- Real selection, measurement and paid packing retain this full frequency-indexed Store block. -/
lemma selectedMeasuredPacking_frequency_store_entry {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef ctx (.bits (RuntimeRound.resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (RuntimeRound.model.HiddenState × History))
    (stored : Store ctx) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) :
    (((FullWordMeasurement.selectedMeasuredPacking m ell width sameWires parameter N
      generator target cells result).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      let first := FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires left)
      let second := FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires right)
      if first = second then
        ∑ original : Store ctx,
          if frequencyStore m ell width sameWires cells result original first.1 first.2 =
              stored then
            (DensityOperator.applyUnitary
              (UnitaryOperator.prodTensor
                ((RuntimePlacement.memberProgram m ell width sameWires N
                  (generator (original.read parameter)) (target (original.read parameter))).matrix
                    environment.quantum)
                (1 : UnitaryOperator Reference))
              (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal).matrix
                (left, leftRef) (right, rightRef)
          else 0
      else 0 := by
  rw [FullWordMeasurement.selectedMeasuredPacking_store_entry]
  simp_rw [labelsAgree_frequency, packedBasisStore_frequencyStore]
  simp only [DensityOperator.applyUnitary_matrix]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordReadout
