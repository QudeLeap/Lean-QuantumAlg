/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset.Instrument
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Execution.Measurement.Effect

/-!
# Every actual reset outcome on the zero-bank subspace

The same specified reset instrument acts as identity on the all-zero outcome
and annihilates every other outcome. The arbitrary external reference stays
in the complete ket, so this column equation extends linearly to coherent
source sums without replacing the reset by a different channel.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Reset

noncomputable section

open QuantumAlg.Execution.Instrument

open Execution
open QuantumFourierTransform.Semiclassical.Window.Source

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private def ResetLocalZeroKetStatement : Prop :=
  ∀ (wire : Fin ctx.systemCount)
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension)
    (basis : ctx.register.Index) (_zero : basis wire = 0),
    (resetLocalOperator wire outcome).applyVec
        (NormalizedVector.ket (R := ctx.register) basis).vec =
      (if outcome = 0 then (1 : Complex) else 0) •
        (NormalizedVector.ket (R := ctx.register) basis).vec

private lemma resetLocalOperator_zero_ket :
    ResetLocalZeroKetStatement (ctx := ctx) := by
  unfold ResetLocalZeroKetStatement
  intro wire outcome basis zero
  classical
  rw [resetLocalOperator, HilbertOperator.mul_applyVec, ZMeasurement.projector_ket, zero]
  by_cases selected : outcome = 0
  · subst outcome
    rw [if_pos rfl, neg_zero, QuditShift.zero_shift_operator]
    rw [Submonoid.coe_one, HilbertOperator.one_applyVec]
    simp only [↓reduceIte, one_smul]
  · rw [if_neg (Ne.symm selected), if_neg selected, zero_smul]
    exact HilbertOperator.applyVec_zero _

/-- Every real primitive reset outcome has its exact complete-reference zero-input column. -/
lemma one_zero_column (parameters : Cleanup.Parameters ctx) (wire : Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (store : Store ctx)
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension)
    (basis : ctx.register.Index) (zero : basis wire = 0)
    {Reference : Register} (reference : Reference.Index) :
    (Instrument.referenceLift Reference
      ((oneInstrument parameters wire environment).operator store outcome)).applyVec
        ((NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec :
          HilbertVector (ctx.register.prod Reference)) =
      (if outcome = 0 then (1 : Complex) else 0) •
        ((NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec :
          HilbertVector (ctx.register.prod Reference)) :=
  Instrument.reference_applyVec_ket (resetLocalOperator wire outcome) basis basis _
    (resetLocalOperator_zero_ket wire outcome basis zero) reference

private lemma product_indicator {First Second : Type}
    (first firstZero : First) (second secondZero : Second)
    [Decidable (first = firstZero)] [Decidable (second = secondZero)]
    [pairDecision : Decidable ((first, second) = (firstZero, secondZero))] :
    (if first = firstZero then (1 : Complex) else 0) *
        (if second = secondZero then 1 else 0) =
      (if (first, second) = (firstZero, secondZero) then 1 else 0) := by
  by_cases head : first = firstZero <;> by_cases tail : second = secondZero <;>
    simp [head, tail]

/-- All outcomes of the original ordered reset, for each complete zero-bank basis ket. -/
private def RunZeroColumnStatement : Prop :=
  ∀ (parameters : Cleanup.Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (store : Store ctx) (outcome : Outcome count wires)
    (basis : ctx.register.Index) (_zero : ∀ bit, basis (wires bit) = 0)
    {Reference : Register} (reference : Reference.Index),
    (Instrument.referenceLift Reference
      ((runInstrument parameters environment count wires).operator store outcome)).applyVec
        ((NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec :
          HilbertVector (ctx.register.prod Reference)) =
      (if outcome = zeroOutcome count wires then (1 : Complex) else 0) •
        ((NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec :
          HilbertVector (ctx.register.prod Reference))

private lemma runZeroColumnStatement_proof :
    RunZeroColumnStatement (ctx := ctx) (services := services) := by
  unfold RunZeroColumnStatement
  intro parameters environment count wires store outcome basis zero Reference reference
  classical
  induction count generalizing store with
  | zero =>
      cases outcome
      change (Instrument.referenceLift Reference (1 : HilbertOperator ctx.register)).applyVec _ = _
      rw [referenceLift_identity, HilbertOperator.one_applyVec]
      have scalar : (if (PUnit.unit : Outcome 0 wires) = zeroOutcome 0 wires
          then (1 : Complex) else 0) = 1 := if_pos rfl
      exact ((congrArg (fun coefficient : Complex => coefficient •
        (NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec)
          scalar).trans (one_smul Complex _)).symm
  | succ count ih =>
      rcases outcome with ⟨head, tail⟩
      let vector : HilbertVector (ctx.register.prod Reference) :=
        (NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec
      have action := instrument_seq_reference_applyVec
        (oneInstrument parameters (wires 0) environment)
        (runInstrument parameters environment count (fun index => wires index.succ))
        store head tail Reference
        vector vector vector
        (if head = 0 then 1 else 0)
        (if tail = zeroOutcome count (fun index => wires index.succ) then 1 else 0)
        (one_zero_column parameters (wires 0) environment store head basis (zero 0) reference)
        (ih (fun index => wires index.succ) _ tail (fun index => zero index.succ))
      have indicator :
          (if head = (0 : Fin (ctx.quantumLayout.wire (wires 0)).dimension)
              then (1 : Complex) else 0) *
            (if tail = zeroOutcome count (fun index => wires index.succ) then 1 else 0) =
          (if ((head, tail) : Outcome (count + 1) wires) = zeroOutcome (count + 1) wires
            then 1 else 0) :=
        product_indicator head 0 tail (zeroOutcome count (fun index => wires index.succ))
          (pairDecision := Classical.propDecidable _)
      exact action.trans (congrArg (fun scalar : Complex => scalar • vector) indicator)


/-- All outcomes of the original ordered reset, for each complete zero-bank basis ket. -/
lemma run_zero_column (parameters : Cleanup.Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (store : Store ctx) (outcome : Outcome count wires)
    (basis : ctx.register.Index) (zero : ∀ bit, basis (wires bit) = 0)
    {Reference : Register} (reference : Reference.Index) :
    (Instrument.referenceLift Reference
      ((runInstrument parameters environment count wires).operator store outcome)).applyVec
        ((NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec :
          HilbertVector (ctx.register.prod Reference)) =
      (if outcome = zeroOutcome count wires then (1 : Complex) else 0) •
        ((NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec :
          HilbertVector (ctx.register.prod Reference)) := by
  have action := runZeroColumnStatement_proof (ctx := ctx) (services := services)
  unfold RunZeroColumnStatement at action
  exact action parameters environment count wires store outcome basis zero reference

/-- The allocating sampler embeds exactly those same all-outcome reset columns. -/
lemma zero_column (parameters : Sampling.Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (store : Store ctx)
    (outcome : Outcome (index.lowerWidth + 1) (parameters.wire index))
    (basis : ctx.register.Index) (zero : ∀ bit, basis (parameters.wire index bit) = 0)
    {Reference : Register} (reference : Reference.Index) :
    (Instrument.referenceLift Reference
      ((instrument parameters index environment).operator store outcome)).applyVec
        ((NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec :
          HilbertVector (ctx.register.prod Reference)) =
      (if outcome = zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
        then (1 : Complex) else 0) •
          (NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)).vec :=
  run_zero_column parameters.resetParameters environment (index.lowerWidth + 1)
    (parameters.wire index) store outcome basis zero reference

end

end Reset

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
