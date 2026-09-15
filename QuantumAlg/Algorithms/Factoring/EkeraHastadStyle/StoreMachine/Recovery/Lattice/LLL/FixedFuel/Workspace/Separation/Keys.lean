/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Package
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Workspace.Views

/-!
# Physical-key projections for the fixed-fuel workspace
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelScratchWorkspaceSeparation

open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open Execution

noncomputable section

/-- The exact physical cells needed by the fixed-fuel driver, independent of other packages. -/
structure PhysicalSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N) : Prop where
  stateDistinct : state.Distinct
  scratchDistinct : scratch.Distinct
  stateScratch : ClassicalWorkspace.CrossSeparated state scratch

/-- A structural read of one cell avoids every different physical key. -/
private theorem storageRead_avoids_of_key_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CWriteRef ctx shape} {target : StorageKey}
    (different : source.key ≠ target) :
    target ∉ (CInputRef.storage source.toCStorageRef).storageKeys := by
  intro member
  exact different (List.mem_singleton.mp member).symm

/-- Physical LLL scratch cell underlying one named Gram cell. -/
def metricCell : LatticeMetricMachine.MetricCell →
    LatticeFixedFuelScratchWorkspaceLayout.Cell
  | .g11 => .metricG11
  | .g21 => .metricG21
  | .g31 => .metricG31
  | .g22 => .metricG22
  | .g32 => .metricG32
  | .g33 => .metricG33
  | .product => .metricProduct

/-- Physical state cell underlying one named basis coordinate. -/
def basisCell : LatticeMetricMachine.BasisCell →
    LatticePairStateWorkspaceLayout.Cell
  | .firstFirst => .basis11
  | .firstSecond => .basis12
  | .firstThird => .basis13
  | .secondFirst => .basis21
  | .secondSecond => .basis22
  | .secondThird => .basis23
  | .thirdFirst => .basis31
  | .thirdSecond => .basis32
  | .thirdThird => .basis33

/-- The semantic Gram-cell projection is injective. -/
theorem metricCell_injective : Function.Injective metricCell := by
  intro left right equal
  cases left <;> cases right <;> simp [metricCell] at equal ⊢

/-- Metric keys are exactly their named physical scratch keys. -/
theorem metricKey_eq_cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N)
    (cell : LatticeMetricMachine.MetricCell) :
    LatticeMetricMachine.metricCellKey
        (LatticeFixedFuelScratchWorkspaceViews.metricRefs scratch) cell =
      (LatticeFixedFuelScratchWorkspaceLayout.cellRef scratch
        (metricCell cell)).toCStorageRef.key := by
  cases cell <;> rfl

/-- The state basis and seven-cell Gram view satisfy the metric machine's
complete physical separation contract. -/
theorem metricSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeMetricMachine.Separation
      (LatticePairStateWorkspaceViews.basisRefs state)
      (LatticeFixedFuelScratchWorkspaceViews.metricRefs scratch) := by
  refine {
    keyInjective := ?_
    basisAvoids := ?_ }
  · intro left right equal
    apply metricCell_injective
    apply LatticeFixedFuelScratchWorkspaceLayout.cellRef_key_injective scratch
      certificates.scratchDistinct
    simpa only [metricKey_eq_cellRef] using equal
  · intro source target
    cases source <;> cases target <;>
      apply storageRead_avoids_of_key_ne <;>
      exact certificates.stateScratch.keysNe _ _

/-- The same persistent package supplies the fixed-fuel machine's eleven-cell
injectivity invariant. -/
theorem machineSeparated {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    (LatticePairStateWorkspaceViews.machineRefs state).Separated :=
  LatticePairStateWorkspaceSeparation.machineSeparated state
    certificates.stateDistinct

/-- Unified physical name for persistent state and phase-local LLL scratch. -/
abbrev DriverCell :=
  LatticePairStateWorkspaceLayout.Cell ⊕
    LatticeFixedFuelScratchWorkspaceLayout.Cell

/-- Physical key of one unified driver cell. -/
def driverKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N) :
    DriverCell → StorageKey
  | .inl cell =>
      (LatticePairStateWorkspaceLayout.cellRef state cell).toCStorageRef.key
  | .inr cell =>
      (LatticeFixedFuelScratchWorkspaceLayout.cellRef scratch cell).toCStorageRef.key

/-- Local distinctness and the state-to-LLL cross certificate make the unified
driver key projection injective. -/
theorem driverKey_injective {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    Function.Injective (driverKey state scratch) := by
  intro left right equal
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          apply congrArg Sum.inl
          apply LatticePairStateWorkspaceLayout.cellRef_key_injective
            state certificates.stateDistinct
          exact equal
      | inr right =>
          exact (certificates.stateScratch.keysNe
            (LatticePairStateWorkspaceLayout.cellIndex N left)
            (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N right) equal).elim
  | inr left =>
      cases right with
      | inl right =>
          exact (certificates.stateScratch.keysNe
            (LatticePairStateWorkspaceLayout.cellIndex N right)
            (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N left)
              equal.symm).elim
      | inr right =>
          apply congrArg Sum.inr
          apply LatticeFixedFuelScratchWorkspaceLayout.cellRef_key_injective
            scratch certificates.scratchDistinct
          exact equal

/-- Unified physical cell underlying one first-pair transition cell. -/
def firstTransitionCell : LatticeFirstPairMachine.TransitionCell → DriverCell
  | .b11 => .inl .basis11
  | .b12 => .inl .basis12
  | .b13 => .inl .basis13
  | .b21 => .inl .basis21
  | .b22 => .inl .basis22
  | .b23 => .inl .basis23
  | .b31 => .inl .basis31
  | .b32 => .inl .basis32
  | .b33 => .inl .basis33
  | .g11 => .inr .metricG11
  | .g21 => .inr .metricG21
  | .g31 => .inr .metricG31
  | .g22 => .inr .metricG22
  | .g32 => .inr .metricG32
  | .g33 => .inr .metricG33
  | .metricProduct => .inr .metricProduct
  | .magnitude => .inr .division32Magnitude
  | .negative => .inr .division32Negative
  | .wideNumerator => .inr .division32WideNumerator
  | .wideDenominator => .inr .division32WideDenominator
  | .division => .inr .division32Division
  | .coefficient => .inr .division32Output
  | .reduceProduct => .inr .reduceProduct
  | .refreshProduct => .inr .refreshG21Product
  | .passes => .inr .lovaszPasses
  | .swapScratch => .inr .swapScratch

/-- The first-phase semantic cell projection is injective. -/
theorem firstTransitionCell_injective : Function.Injective firstTransitionCell := by
  intro left right equal
  cases left <;> cases right <;> simp [firstTransitionCell] at equal ⊢

/-- First-pair semantic keys are their unified physical driver keys. -/
theorem firstCellKey_eq_driverKey {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N)
    (cell : LatticeFirstPairMachine.TransitionCell) :
    LatticeFirstPairMachine.cellKey
        (LatticeFixedFuelScratchWorkspaceViews.firstRefs state scratch) cell =
      driverKey state scratch (firstTransitionCell cell) := by
  cases cell <;> rfl

/-- The physical state and scratch packages supply first-phase global key
separation. -/
theorem firstPhaseSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeFirstPairMachine.PhaseSeparation
      (LatticeFixedFuelScratchWorkspaceViews.firstRefs
        state scratch) := by
  refine ⟨?_⟩
  intro left right equal
  apply firstTransitionCell_injective
  apply driverKey_injective certificates
  simpa only [firstCellKey_eq_driverKey] using equal

/-- Unified physical cell underlying one second-pair prefix cell. -/
def secondTransitionCell : LatticeSecondPairMachine.TransitionCell → DriverCell
  | .b11 => .inl .basis11
  | .b12 => .inl .basis12
  | .b13 => .inl .basis13
  | .b21 => .inl .basis21
  | .b22 => .inl .basis22
  | .b23 => .inl .basis23
  | .b31 => .inl .basis31
  | .b32 => .inl .basis32
  | .b33 => .inl .basis33
  | .g11 => .inr .metricG11
  | .g21 => .inr .metricG21
  | .g31 => .inr .metricG31
  | .g22 => .inr .metricG22
  | .g32 => .inr .metricG32
  | .g33 => .inr .metricG33
  | .metricProduct => .inr .metricProduct
  | .refreshG21Product => .inr .refreshG21Product
  | .refreshG32Product => .inr .refreshG32Product
  | .nu32 => .inr .nu32
  | .d32 => .inr .d32
  | .reductionInputsProduct => .inr .reductionInputsProduct
  | .division32 .magnitude => .inr .division32Magnitude
  | .division32 .negative => .inr .division32Negative
  | .division32 .wideNumerator => .inr .division32WideNumerator
  | .division32 .wideDenominator => .inr .division32WideDenominator
  | .division32 .division => .inr .division32Division
  | .division32 .output => .inr .division32Output
  | .division31 .magnitude => .inr .division31Magnitude
  | .division31 .negative => .inr .division31Negative
  | .division31 .wideNumerator => .inr .division31WideNumerator
  | .division31 .wideDenominator => .inr .division31WideDenominator
  | .division31 .division => .inr .division31Division
  | .division31 .output => .inr .division31Output
  | .reduceProduct => .inr .reduceProduct

/-- The second-prefix semantic cell projection is injective. -/
def secondTransitionCellInverse : DriverCell →
    Option LatticeSecondPairMachine.TransitionCell
  | .inl .basis11 => some .b11
  | .inl .basis12 => some .b12
  | .inl .basis13 => some .b13
  | .inl .basis21 => some .b21
  | .inl .basis22 => some .b22
  | .inl .basis23 => some .b23
  | .inl .basis31 => some .b31
  | .inl .basis32 => some .b32
  | .inl .basis33 => some .b33
  | .inr .metricG11 => some .g11
  | .inr .metricG21 => some .g21
  | .inr .metricG31 => some .g31
  | .inr .metricG22 => some .g22
  | .inr .metricG32 => some .g32
  | .inr .metricG33 => some .g33
  | .inr .metricProduct => some .metricProduct
  | .inr .refreshG21Product => some .refreshG21Product
  | .inr .refreshG32Product => some .refreshG32Product
  | .inr .nu32 => some .nu32
  | .inr .d32 => some .d32
  | .inr .reductionInputsProduct => some .reductionInputsProduct
  | .inr .division32Magnitude => some (.division32 .magnitude)
  | .inr .division32Negative => some (.division32 .negative)
  | .inr .division32WideNumerator => some (.division32 .wideNumerator)
  | .inr .division32WideDenominator => some (.division32 .wideDenominator)
  | .inr .division32Division => some (.division32 .division)
  | .inr .division32Output => some (.division32 .output)
  | .inr .division31Magnitude => some (.division31 .magnitude)
  | .inr .division31Negative => some (.division31 .negative)
  | .inr .division31WideNumerator => some (.division31 .wideNumerator)
  | .inr .division31WideDenominator => some (.division31 .wideDenominator)
  | .inr .division31Division => some (.division31 .division)
  | .inr .division31Output => some (.division31 .output)
  | .inr .reduceProduct => some .reduceProduct
  | _ => none

private theorem secondTransitionCellInverse_apply
    (cell : LatticeSecondPairMachine.TransitionCell) :
    secondTransitionCellInverse (secondTransitionCell cell) = some cell := by
  cases cell <;> try rfl
  case division32 cell => cases cell <;> rfl
  case division31 cell => cases cell <;> rfl

theorem secondTransitionCell_injective :
    Function.Injective secondTransitionCell := by
  intro left right equal
  have mapped := congrArg secondTransitionCellInverse equal
  rw [secondTransitionCellInverse_apply,
    secondTransitionCellInverse_apply] at mapped
  exact Option.some.inj mapped

/-- Second-prefix semantic keys are their unified physical driver keys. -/
theorem secondCellKey_eq_driverKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N)
    (cell : LatticeSecondPairMachine.TransitionCell) :
    LatticeSecondPairMachine.cellKey
        (LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs state scratch)
          cell =
      driverKey state scratch (secondTransitionCell cell) := by
  cases cell <;> try rfl
  case division32 cell => cases cell <;> rfl
  case division31 cell => cases cell <;> rfl

/-- The physical packages supply second-prefix global key separation. -/
theorem secondPhaseSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeSecondPairMachine.PhaseSeparation
      (LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
        state scratch) := by
  refine ⟨?_⟩
  intro left right equal
  apply secondTransitionCell_injective
  apply driverKey_injective certificates
  simpa only [secondCellKey_eq_driverKey] using equal

/-- Unified physical cell underlying one complete second-pair cell. -/
def secondFullCell : LatticeSecondPairFullMachine.Cell → DriverCell
  | .transition cell => secondTransitionCell cell
  | .area12ProductLeft => .inr .area12ProductLeft
  | .area12ProductRight => .inr .area12ProductRight
  | .area12CrossFirst => .inr .area12CrossFirst
  | .area12CrossSecond => .inr .area12CrossSecond
  | .area12CrossThird => .inr .area12CrossThird
  | .area12Result => .inr .area12Result
  | .area12NormProduct => .inr .area12NormProduct
  | .area13ProductLeft => .inr .area13ProductLeft
  | .area13ProductRight => .inr .area13ProductRight
  | .area13CrossFirst => .inr .area13CrossFirst
  | .area13CrossSecond => .inr .area13CrossSecond
  | .area13CrossThird => .inr .area13CrossThird
  | .area13Result => .inr .area13Result
  | .area13NormProduct => .inr .area13NormProduct
  | .lovaszDoubled => .inr .lovaszDoubled
  | .lovaszPasses => .inr .lovaszPasses
  | .swapScratch => .inr .swapScratch

/-- A partial inverse used to prove the complete second-pair projection
injective without quadratic case splitting. -/
def secondFullCellInverse (cell : DriverCell) :
    Option LatticeSecondPairFullMachine.Cell :=
  match secondTransitionCellInverse cell with
  | some transition => some (.transition transition)
  | none =>
      match cell with
      | .inr .area12ProductLeft => some .area12ProductLeft
      | .inr .area12ProductRight => some .area12ProductRight
      | .inr .area12CrossFirst => some .area12CrossFirst
      | .inr .area12CrossSecond => some .area12CrossSecond
      | .inr .area12CrossThird => some .area12CrossThird
      | .inr .area12Result => some .area12Result
      | .inr .area12NormProduct => some .area12NormProduct
      | .inr .area13ProductLeft => some .area13ProductLeft
      | .inr .area13ProductRight => some .area13ProductRight
      | .inr .area13CrossFirst => some .area13CrossFirst
      | .inr .area13CrossSecond => some .area13CrossSecond
      | .inr .area13CrossThird => some .area13CrossThird
      | .inr .area13Result => some .area13Result
      | .inr .area13NormProduct => some .area13NormProduct
      | .inr .lovaszDoubled => some .lovaszDoubled
      | .inr .lovaszPasses => some .lovaszPasses
      | .inr .swapScratch => some .swapScratch
      | _ => none

private theorem secondFullCellInverse_apply
    (cell : LatticeSecondPairFullMachine.Cell) :
    secondFullCellInverse (secondFullCell cell) = some cell := by
  cases cell with
  | transition cell =>
      unfold secondFullCell secondFullCellInverse
      rw [secondTransitionCellInverse_apply]
  | area12ProductLeft => rfl
  | area12ProductRight => rfl
  | area12CrossFirst => rfl
  | area12CrossSecond => rfl
  | area12CrossThird => rfl
  | area12Result => rfl
  | area12NormProduct => rfl
  | area13ProductLeft => rfl
  | area13ProductRight => rfl
  | area13CrossFirst => rfl
  | area13CrossSecond => rfl
  | area13CrossThird => rfl
  | area13Result => rfl
  | area13NormProduct => rfl
  | lovaszDoubled => rfl
  | lovaszPasses => rfl
  | swapScratch => rfl

/-- The complete second-pair semantic cell projection is injective. -/
theorem secondFullCell_injective : Function.Injective secondFullCell := by
  intro left right equal
  have mapped := congrArg secondFullCellInverse equal
  rw [secondFullCellInverse_apply, secondFullCellInverse_apply] at mapped
  exact Option.some.inj mapped

private theorem secondPhase_ne_secondFullCell
    (cell : LatticeSecondPairFullMachine.Cell) :
    (Sum.inl .secondPhase : DriverCell) ≠ secondFullCell cell := by
  intro equal
  have mapped := congrArg secondFullCellInverse equal
  rw [secondFullCellInverse_apply] at mapped
  change (none : Option LatticeSecondPairFullMachine.Cell) = some cell at mapped
  cases mapped

private theorem done_ne_secondFullCell
    (cell : LatticeSecondPairFullMachine.Cell) :
    (Sum.inl .done : DriverCell) ≠ secondFullCell cell := by
  intro equal
  have mapped := congrArg secondFullCellInverse equal
  rw [secondFullCellInverse_apply] at mapped
  change (none : Option LatticeSecondPairFullMachine.Cell) = some cell at mapped
  cases mapped

/-- Complete second-pair semantic keys are their unified physical keys. -/
theorem secondFullCellKey_eq_driverKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N)
    (cell : LatticeSecondPairFullMachine.Cell) :
    LatticeSecondPairFullMachine.cellKey
        (LatticeFixedFuelScratchWorkspaceViews.secondRefs state scratch) cell =
      driverKey state scratch (secondFullCell cell) := by
  cases cell with
  | transition cell => exact secondCellKey_eq_driverKey state scratch cell
  | area12ProductLeft => rfl
  | area12ProductRight => rfl
  | area12CrossFirst => rfl
  | area12CrossSecond => rfl
  | area12CrossThird => rfl
  | area12Result => rfl
  | area12NormProduct => rfl
  | area13ProductLeft => rfl
  | area13ProductRight => rfl
  | area13CrossFirst => rfl
  | area13CrossSecond => rfl
  | area13CrossThird => rfl
  | area13Result => rfl
  | area13NormProduct => rfl
  | lovaszDoubled => rfl
  | lovaszPasses => rfl
  | swapScratch => rfl

/-- The complete physical packages make the second-pair key projection
injective. -/
theorem secondFullKeyInjective {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    Function.Injective
      (LatticeSecondPairFullMachine.cellKey
        (LatticeFixedFuelScratchWorkspaceViews.secondRefs
          state scratch)) := by
  intro left right equal
  apply secondFullCell_injective
  apply driverKey_injective certificates
  simpa only [secondFullCellKey_eq_driverKey] using equal

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelScratchWorkspaceSeparation
