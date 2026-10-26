/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Schedule
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Window
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Preparation

/-!
# Native lexical peak of the actual three-round table fragment

The ten-cell package, one five-array window and one original arithmetic
scratch scope suffice. Windows, streams and rounds reuse this capacity.
Every original caller bit and every original quantum system remains in
the peak; no fixed external caller size is silently substituted.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalAlgorithms.NumberTheory.XGCD
open NumberTheory.XGCD.Native NumberTheory.Checked.SignedReduction
open NumberTheory.Checked.SignedReduction.Native Modular.Reduce.Native

noncomputable section

/-- The actual shared package and one complete full-window table coexist with the inverse scope. -/
def roundAdditionalSpace (kind : ProblemKind) : SpacePool kind :=
  sharedSpace kind 256 + (tableSpace kind 256 (2 ^ 16) + coefficientScratchSpace kind 256)

private lemma tableSpace_mono (kind : ProblemKind) (width first second : Nat)
    (lengths : first ≤ second) : tableSpace kind width first ≤ tableSpace kind width second := by
  intro axis
  cases axis with
  | classicalBits =>
      rw [tableSpace_classicalBits, tableSpace_classicalBits]
      exact Nat.mul_le_mul_right width (Nat.mul_le_mul_left 5 lengths)
  | quantumSystems dimension =>
      rw [tableSpace_quantumSystems, tableSpace_quantumSystems]

/-- The display bound retains the original widened coefficient engine and its actual live cells. -/
lemma roundAdditionalSpace_classicalBits_le (kind : ProblemKind) :
    roundAdditionalSpace kind .classicalBits ≤ 85098816 := by
  have scratch := coefficientScratchSpace256_classicalBits_le kind
  simp only [roundAdditionalSpace, Pi.add_apply, sharedSpace_classicalBits,
    tableSpace_classicalBits]
  omega

private lemma shapeList_quantum (shapes : List CShape) (dimension : ℕ+) :
    ((shapes.map (SpacePool.ofShape (kind := .quantum))).sum) (.quantumSystems dimension) = 0 := by
  induction shapes with
  | nil => rfl
  | cons head rest ih =>
      simpa only [List.map_cons, List.sum_cons, Pi.add_apply, SpacePool.ofShape,
        Nat.zero_add] using ih

/-- Classical table preparation adds no quantum system of any dimension. -/
lemma roundAdditionalSpace_quantumSystems (dimension : ℕ+) :
    roundAdditionalSpace .quantum (.quantumSystems dimension) = 0 := by
  simp [roundAdditionalSpace, sharedSpace_quantumSystems, tableSpace_quantumSystems,
    coefficientScratchSpace, Field.Native.coefficientActiveSpace, rawScratchSpace,
    signedReductionSpaceLimit, signedReductionScratchSpace, signedReductionArithmeticSpace,
    negativeCorrectionScratchSpace, SpacePool.max, SpacePool.ofShape, shapeList_quantum]

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

attribute [local irreducible] Frame.windowCircuit

variable (spec : ModulusSpec 256) (coefficient : Nat)
  (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord 256))
  (column : Fin 6 → Fin 5)
  (full : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    Fin 3 → Fin 2 → Fin 16 → Fin 6 → QueryPlacement encoding inner 256 8 7)
  (tail : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    Fin 3 → Fin 2 → Fin 6 → QueryPlacement encoding inner 256 2 1)

/-- Actual allocations are added once; sequential stages and windows share their scratch. -/
lemma roundCircuit_liveSpace (round : Fin 3) :
    LiveSpace.Bound (model := Model) (roundAdditionalSpace .quantum)
      (roundCircuit (services := services) spec coefficient firstX firstY secondX secondY
        column round full tail) := by
  unfold roundCircuit withCells
  apply LiveSpace.allocate
  intro inner cells distinct lift separated
  let frame := Frame.ofCells cells distinct
  apply LiveSpace.seq
  · exact (LiveSpace.initialization frame spec coefficient).mono zero_le
  · apply LiveSpace.seq
    · exact (LiveSpace.pairedBases frame spec (lift.liftInput firstX) (lift.liftInput firstY)
        (lift.liftInput secondX) (lift.liftInput secondY)).mono (fun axis => Nat.le_add_left _ _)
    · apply LiveSpace.range
      intro stream
      apply LiveSpace.seq
      · apply LiveSpace.range
        intro window
        exact frame.windowCircuit_liveSpace spec (baseRow stream window.castSucc) column
          (fun inside occurrence => full (lift.compose inside) round stream window occurrence)
      · exact (frame.windowCircuit_liveSpace spec (baseRow stream ⟨16, by decide⟩) column
          (fun inside occurrence => tail (lift.compose inside) round stream occurrence)).mono
            (fun axis => Nat.add_le_add
              (tableSpace_mono .quantum 256 (2 ^ 4) (2 ^ 16) (by norm_num) axis) (Nat.le_refl _))

attribute [local irreducible] roundCircuit threeRoundCircuit

/-- All three actual rounds reuse the same complete live package. -/
lemma threeRoundCircuit_liveSpace :
    LiveSpace.Bound (model := Model) (roundAdditionalSpace .quantum)
      (threeRoundCircuit (services := services) spec coefficient firstX firstY secondX secondY
        column full tail) := by
  unfold threeRoundCircuit
  exact LiveSpace.range _ _ _ (fun round => roundCircuit_liveSpace spec coefficient
    firstX firstY secondX secondY column full tail round)

/-- Every caller bit is retained beside the actual full-table peak ceiling. -/
lemma threeRoundCircuit_classical_peaks
    (path : (threeRoundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column full tail).Path) :
    Circuit.peakResidentSpace
      (threeRoundCircuit spec coefficient firstX firstY secondX secondY column full tail)
      path .classicalBits ≤ 85098816 + ctx.residentSpace .classicalBits ∧
      Circuit.peakAuxiliarySpace
        (threeRoundCircuit spec coefficient firstX firstY secondX secondY column full tail)
        path .classicalBits ≤ 85098816 + ctx.auxiliarySpace .classicalBits := by
  have actual := threeRoundCircuit_liveSpace spec coefficient firstX firstY secondX secondY
    column full tail path
  exact ⟨(actual.1 .classicalBits).trans
      (Nat.add_le_add (roundAdditionalSpace_classicalBits_le .quantum) (Nat.le_refl _)),
    (actual.2 .classicalBits).trans
      (Nat.add_le_add (roundAdditionalSpace_classicalBits_le .quantum) (Nat.le_refl _))⟩

/-- The complete real table fragment adds no system to the caller's actual quantum peak. -/
lemma threeRoundCircuit_quantum_peaks (dimension : ℕ+)
    (path : (threeRoundCircuit (services := services) spec coefficient
      firstX firstY secondX secondY column full tail).Path) :
    Circuit.peakResidentSpace
      (threeRoundCircuit spec coefficient firstX firstY secondX secondY column full tail)
      path (.quantumSystems dimension) ≤
          ctx.residentSpace (.quantumSystems dimension) ∧
      Circuit.peakAuxiliarySpace
        (threeRoundCircuit spec coefficient firstX firstY secondX secondY column full tail)
        path (.quantumSystems dimension) ≤
          ctx.auxiliarySpace (.quantumSystems dimension) := by
  have actual := threeRoundCircuit_liveSpace spec coefficient firstX firstY secondX secondY
    column full tail path
  simpa only [Pi.add_apply, roundAdditionalSpace_quantumSystems, Nat.zero_add] using
    And.intro (actual.1 (.quantumSystems dimension)) (actual.2 (.quantumSystems dimension))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
