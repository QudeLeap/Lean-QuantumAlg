/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Preparation.Reset
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Reset.Range

/-!
# Exact deterministic actual records of a zero active-bank reset

Every selected wire really executes MZ and its same-cell native correction.
On the internally established zero-bank subspace these operations preserve
all quantum entries, write their real zero results and retain every real
Path. The finite recursion keeps the width symbolic and needs no distinct
wire or fresh-cell assumption.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private instance resetZeroDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Cleanup.Parameters

variable (parameters : Cleanup.Parameters ctx)

/-- The actual zero MZ, zero write and branch path, with no measurement removed. -/
def zeroOneRecord (wire : Fin ctx.systemCount) (store : Store ctx) :
    Store ctx × (parameters.one (services := services) wire).Path :=
  (store.write (parameters.outputAt wire) (.finite 0),
    ((0 : Fin (ctx.quantumLayout.wire wire).dimension), ⟨.finite 0, ()⟩))

/-- Deterministic record of the same actual finite reset sequence on zero input. -/
def zeroRunRecord (count : Nat) (wires : Fin count → Fin ctx.systemCount) :
    Store ctx → Store ctx × (parameters.run (services := services) count wires).Path :=
  Circuit.forRangeStoreRecord count (fun index => parameters.one (wires index))
    (fun index => parameters.zeroOneRecord (wires index))

/-- The complete zero-wire record of the original instruction, for every surrounding state. -/
lemma zeroOne_execute (wire : Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : QuditShift.WireSupported wire 0 state) :
    (parameters.one wire).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := parameters.zeroOneRecord (services := services) wire entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  QuantumFourierTransform.Semiclassical.Window.window_preparation_reset_zero_record
    wire (parameters.outputAt wire) (parameters.shifts wire) environment state supported

/-- The whole zero-bank reset is exactly its original Store writes and chronological zero Paths. -/
lemma zeroRun_execute (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ index, QuditShift.WireSupported (wires index) 0 state) :
    (parameters.run count wires).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := parameters.zeroRunRecord (services := services) count wires entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  let goodState : {Earlier : Type} → [Fintype Earlier] →
      State ctx Reference (services.HiddenState × Earlier) → Prop :=
    fun {_} _ current => ∀ index, QuditShift.WireSupported (wires index) 0 current
  refine QuantumFourierTransform.Semiclassical.Window.window_reset_range_records_on_invariant
    count (fun index => parameters.one (wires index))
    environment Reference (fun index => parameters.zeroOneRecord (wires index)) goodState
    ?_ ?_ state supported
  · intro index earlier _ current good
    exact parameters.zeroOne_execute (wires index) environment current (good index)
  · intro index earlier _ current good observed
    have first := parameters.zeroOne_execute (wires index) environment current (good index)
    rw [first]
    let update : Store ctx × (services.HiddenState × earlier) →
        Store ctx × (services.HiddenState ×
          (earlier × (parameters.one (services := services) (wires index)).Path)) :=
      fun entry =>
        let result := parameters.zeroOneRecord (services := services) (wires index) entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))
    intro entry left right refLeft refRight different
    change ((current.mapClassical update).block entry).matrix
      (left, refLeft) (right, refRight) = 0
    rw [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro original _
    split_ifs
    · exact good observed original left right refLeft refRight different
    · rfl

end Cleanup.Parameters

namespace Sampling.Parameters

variable (parameters : Sampling.Parameters ctx)

/-- Real pre-H active-bank reset has deterministic zero records on every zero-bank state. -/
lemma reset_zero_record (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ bit, QuditShift.WireSupported (parameters.wire index bit) 0 state) :
    (parameters.reset index).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := parameters.resetParameters.zeroRunRecord (services := services)
          (index.lowerWidth + 1) (parameters.wire index) entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  (parameters.reset_execute index environment Reference state).trans
    (parameters.resetParameters.zeroRun_execute (index.lowerWidth + 1)
      (parameters.wire index) environment state supported)

end Sampling.Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
