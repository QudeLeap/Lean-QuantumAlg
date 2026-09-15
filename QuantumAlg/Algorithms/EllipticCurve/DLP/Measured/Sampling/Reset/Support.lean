/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout.Density

/-!
# Actual reset support in the original scalar coordinates

Every actual reset block has the prescribed complete local ket. Splitting
the existing public frame and terminal cells only changes proof coordinates.
The resulting scalar quantum marginal therefore has exactly the original
initialized basis support, retaining arbitrary old stores, histories and the
full conditional reference without normalizing any measurement branch.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open MeasuredUncompute MAU.Inversion.SharedEEA

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem marginal_supported {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (label : ctx.register.Index)
    (supported : ∀ record basis, basis.1 ≠ label →
      (state.block record).matrix basis basis = 0)
    (basis : (ctx.register.prod Reference).Index) (outside : basis.1 ≠ label) :
    state.quantumMarginal.matrix basis basis = 0 := by
  change (∑ record, (state.block record).matrix) basis basis = 0
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun record _ => supported record basis outside)

private theorem unionSplit_supported (ctx frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint ctx frame) (label : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion frame separate) Reference History)
    (supported : ∀ basis,
      (unionBasisEquiv ctx frame separate basis.1).1 ≠ label →
        state.quantumMarginal.matrix basis basis = 0)
    (basis : (ctx.register.prod (frame.register.prod Reference)).Index)
    (outside : basis.1 ≠ label) :
    (splitState ctx frame separate state).quantumMarginal.matrix basis basis = 0 := by
  unfold splitState
  rw [Circuit.marginal_reindex, ExecutionState.mapClassical_quantumMarginal,
    DensityOperator.reindex_entry]
  apply supported
  have coordinates := (referenceBasis ctx frame separate Reference).apply_symm_apply basis
  have first := congrArg Prod.fst coordinates
  exact fun same => outside (first.symm.trans same)

private theorem retainedSplit_supported (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (shape : CShape) (fresh : key ∉ ctx.keys) (label : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.addRetained key shape fresh) Reference History)
    (supported : ∀ basis, basis.1 ≠ label →
      state.quantumMarginal.matrix basis basis = 0)
    (basis : (ctx.register.prod
      ((Circuit.retainedLocalFrame (kind := .quantum) key shape).register.prod Reference)).Index)
    (outside : basis.1 ≠ label) :
    (Circuit.underRetainedSplitState key shape fresh state).quantumMarginal.matrix basis basis =
      0 := by
  rw [Circuit.retainedSplit_marginal, DensityOperator.reindex_entry]
  apply supported
  intro same
  apply outside
  funext wire
  apply Fin.ext
  have value := Circuit.retainedReadoutBasis_value ctx key shape fresh Reference
    ((Circuit.retainedReadoutBasis ctx key shape fresh Reference).symm basis) wire
  rw [Equiv.apply_symm_apply, same] at value
  exact value

private theorem cellsSplit_supported (ctx : RuntimeCtx .quantum) (count : Nat)
    (label : ctx.register.Index) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (MeasurementCells.context ctx 2 count) Reference History)
    (supported : ∀ basis, basis.1 ≠ MeasurementCells.basisEquiv ctx 2 count label →
      state.quantumMarginal.matrix basis basis = 0)
    (basis : (ctx.register.prod (Circuit.measurementCellsReference ctx 2 count Reference)).Index)
    (outside : basis.1 ≠ label) :
    (Circuit.underMeasurementCellsSplitState ctx 2 count state).quantumMarginal.matrix basis basis =
      0 := by
  induction count generalizing Reference History with
  | zero =>
      simp only [Circuit.underMeasurementCellsSplitState]
      erw [State.mapHistory_quantumMarginal]
      exact supported basis outside
  | succ count ih =>
      let inner := MeasurementCells.context ctx 2 count
      have next := retainedSplit_supported inner inner.canonicalFreshKey (.finite 2)
        inner.canonicalFreshKey_fresh (MeasurementCells.basisEquiv ctx 2 count label) state
        supported
      have rest := ih
        (Circuit.underRetainedSplitState inner.canonicalFreshKey (.finite 2)
          inner.canonicalFreshKey_fresh state) next basis outside
      simp only [Circuit.underMeasurementCellsSplitState]
      erw [State.mapHistory_quantumMarginal]
      exact rest

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Actual reset establishes the original initialized local ket in the full scalar coordinates. -/
theorem samplingResetSplit_supported (fieldTail exponentWidth : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (PublicInput.terminal E exponentWidth) Reference History)
    (basis : ((Allocation.after p.size (2 * exponentWidth)).register.prod
      (Circuit.measurementCellsReference (Allocation.after p.size (2 * exponentWidth)) 2
        (2 * exponentWidth) (Register.prod (PublicInput.frame E exponentWidth).register
          Reference))).Index)
    (outside : basis.1 ≠ Allocation.initializedAssembly p (2 * exponentWidth)
      ((BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth))).value,
        (InPlacePreparation.preparation p).value,
        Encoding.pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed (0, 0))) :
    (samplingReadoutSplitState E exponentWidth
      ((samplingReset E fieldTail exponentWidth sameWidth fits seed).execute
        Reference state)).quantumMarginal.matrix basis basis = 0 := by
  let label := Allocation.initializedAssembly p (2 * exponentWidth)
    ((BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth))).value,
      (InPlacePreparation.preparation p).value,
      Encoding.pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed (0, 0))
  let completed := (samplingReset E fieldTail exponentWidth sameWidth fits seed).execute
    Reference state
  have original : ∀ input, input.1 ≠
      samplingResetLabel E exponentWidth fieldTail sameWidth fits seed →
        completed.quantumMarginal.matrix input input = 0 := by
    apply marginal_supported completed
      (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed)
    intro record input different
    rcases input with ⟨localBasis, external⟩
    exact (samplingReset_block_factor E fieldTail exponentWidth sameWidth fits seed state
      record localBasis localBasis external external).trans (by
        simp only [NormalizedVector.ket_apply, different, if_false, zero_mul])
  have framed := unionSplit_supported (exponentMeasurementContext p exponentWidth)
    (PublicInput.frame E exponentWidth) (PublicInput.terminal_disjoint E exponentWidth)
    (MeasurementCells.basisEquiv (Allocation.after p.size (2 * exponentWidth)) 2
      (2 * exponentWidth) label) completed (by
        intro input different
        apply original input
        intro same
        apply different
        rw [same, samplingResetLabel, Equiv.apply_symm_apply])
  exact cellsSplit_supported (Allocation.after p.size (2 * exponentWidth))
    (2 * exponentWidth) label
    (splitState (exponentMeasurementContext p exponentWidth) (PublicInput.frame E exponentWidth)
      (PublicInput.terminal_disjoint E exponentWidth) completed) framed basis outside

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
