/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Recorded
import all QuantumAlg.Core.Execution.Instrument.Vector
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Locality.Reset
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset.Zero

/-!
# Specified instruments of the actual active-bank reset

The outcome carrier and record follow the original ordered reset circuit.
The distinguished all-zero outcome retains the original zero Store writes
and both paths at each step. No instrument is selected existentially.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Reset

noncomputable section

open QuantumAlg.Execution.Instrument

open Execution
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
private instance resetDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

private lemma referenceLift_identity (Local Reference : Register) :
    Instrument.referenceLift Reference (1 : HilbertOperator Local) = 1 := by
  ext row column
  rcases row with ⟨left, referenceLeft⟩
  rcases column with ⟨right, referenceRight⟩
  by_cases same : left = right <;> by_cases referenceSame : referenceLeft = referenceRight <;>
    simp [Instrument.referenceLift, Matrix.one_apply, Prod.mk.injEq, same, referenceSame]

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private def identityInstrument
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Instrument (Circuit.id
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (allowAllocation := false) ctx) Unit environment where
  record store _ := (store, ())
  operator _ _ := 1
  blocks := by
    intro Reference History _ state result
    rcases result with ⟨store, hidden, history, path⟩
    cases path
    refine (congrArg DensityOperator.matrix
      (Circuit.execute_id_block environment state store hidden history)).trans ?_
    simp only [Fintype.sum_unique, referenceLift_identity, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]
    symm
    rw [Finset.sum_eq_single (store, (hidden, history))]
    · exact if_pos rfl
    · intro original _ different
      refine if_neg ?_
      intro same
      exact different (congrArg (fun value : Store ctx ×
        (services.HiddenState × (History × Unit)) =>
          (value.1, (value.2.1, value.2.2.1))) same)
    · intro absent
      exact (absent (Finset.mem_univ _)).elim

/-- This is the same MZ, same-cell branch and native correction, with its original actual Path. -/
def oneInstrument (parameters : Cleanup.Parameters ctx) (wire : Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Instrument (parameters.one wire) (Fin (ctx.quantumLayout.wire wire).dimension) environment where
  record store outcome :=
    (store.write (parameters.outputAt wire) (.finite outcome),
      (outcome, ⟨.finite outcome, ()⟩))
  operator _ outcome := resetLocalOperator wire outcome
  blocks := by
    intro Reference History _ state result
    exact (window_sourceReset_local_blocks wire (parameters.outputAt wire)
      (parameters.shifts wire) environment Reference state result).trans
        (sum_condition_decisions _ _ _ _)

/-- One finite outcome for every real measurement, in its actual execution order. -/
def Outcome {ctx : RuntimeCtx .quantum} :
    (count : Nat) → (Fin count → Fin ctx.systemCount) → Type
  | 0, _ => Unit
  | count + 1, wires =>
      Fin (ctx.quantumLayout.wire (wires 0)).dimension ×
        Outcome count (fun index => wires index.succ)

instance outcomeFintype {ctx : RuntimeCtx .quantum} :
    (count : Nat) → (wires : Fin count → Fin ctx.systemCount) → Fintype (Outcome count wires)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | count + 1, wires => by
      letI := outcomeFintype count (fun index => wires index.succ)
      exact inferInstanceAs (Fintype
        (Fin (ctx.quantumLayout.wire (wires 0)).dimension ×
          Outcome count (fun index => wires index.succ)))

/-- The literal all-zero tuple of real MZ outcomes. -/
def zeroOutcome {ctx : RuntimeCtx .quantum} :
    (count : Nat) → (wires : Fin count → Fin ctx.systemCount) → Outcome count wires
  | 0, _ => ()
  | count + 1, wires => (0, zeroOutcome count (fun index => wires index.succ))

/-- Compose specified primitive instruments through the same actual reset circuit. -/
def runInstrument (parameters : Cleanup.Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    (count : Nat) → (wires : Fin count → Fin ctx.systemCount) →
      Instrument (parameters.run count wires) (Outcome count wires) environment
  | 0, _ => identityInstrument environment
  | count + 1, wires =>
      (oneInstrument parameters (wires 0) environment).seq
        (runInstrument parameters environment count (fun index => wires index.succ))

/-- The selected zero outcome carries the original chronological zero record exactly. -/
lemma runInstrument_zero_record (parameters : Cleanup.Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (store : Store ctx) :
    (runInstrument parameters environment count wires).record store (zeroOutcome count wires) =
      parameters.zeroRunRecord (services := services) count wires store := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      exact congrArg
        (fun last : Store ctx ×
            (parameters.run (services := services) count
              (fun index => wires index.succ)).Path =>
          (last.1,
            ((parameters.zeroOneRecord (services := services) (wires 0) store).2,
              last.2)))
        (ih (fun index => wires index.succ)
          (parameters.zeroOneRecord (services := services) (wires 0) store).1)

/-- Identity embedding gives the specified instrument of the actual sampler reset. -/
def instrument (parameters : Sampling.Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Instrument (parameters.reset index)
      (Outcome (index.lowerWidth + 1) (parameters.wire index)) environment :=
  (runInstrument parameters.resetParameters environment (index.lowerWidth + 1)
    (parameters.wire index)).embedIdentity

end

end Reset

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
