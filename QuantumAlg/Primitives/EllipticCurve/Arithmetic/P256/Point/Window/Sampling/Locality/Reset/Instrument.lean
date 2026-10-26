/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Reference
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Reset
import all
QuantumAlg.Core.Execution.Instrument.Recorded
import all
QuantumAlg.Core.Execution.Instrument.Exists

/-!
# Complete instruments of the original active-bank reset

Each real MZ result selects its real native correction. Structural induction
composes the same ordered reset program, including its true empty-path
identity. No clean input, service-state promise or replacement channel is
used. The actual caller cell, overwrites, History and Reference remain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma referenceLift_identity (Local Reference : Register) :
    Execution.Instrument.referenceLift Reference (1 : HilbertOperator Local) = 1 := by
  ext row column
  rcases row with ⟨left, referenceLeft⟩
  rcases column with ⟨right, referenceRight⟩
  by_cases same : left = right <;> by_cases referenceSame : referenceLeft = referenceRight <;>
    simp [Execution.Instrument.referenceLift, Matrix.one_apply, Prod.mk.injEq, same, referenceSame]

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private def resetIdentityInstrument
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Execution.Instrument (Circuit.id
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
def resetOneInstrument (parameters : Cleanup.Parameters ctx) (wire : Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Execution.Instrument (parameters.one wire) (Fin (ctx.quantumLayout.wire wire).dimension)
      environment where
  record store outcome :=
    (store.write (parameters.outputAt wire) (.finite outcome),
      (outcome, ⟨.finite outcome, ()⟩))
  operator _ outcome := resetLocalOperator wire outcome
  blocks := by
    intro Reference History _ state result
    exact (window_sourceReset_local_blocks wire (parameters.outputAt wire)
      (parameters.shifts wire) environment Reference state result).trans
        (Execution.sum_condition_decisions _ _ _ _)

/-- The entire original arbitrary-count reset has an actual finite full-record instrument. -/
lemma resetRun_hasInstrument (parameters : Cleanup.Parameters ctx) (count : Nat)
    (wires : Fin count → Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.HasInstrument (parameters.run count wires) environment :=
        by
  induction count with
  | zero => exact (resetIdentityInstrument environment).to_exists
  | succ count ih =>
      exact (resetOneInstrument parameters (wires 0) environment).to_exists.seq
        (ih (fun index => wires index.succ))

/-- Identity embedding retains that same real active-bank reset in the allocating sampler. -/
lemma sampling_reset_hasInstrument (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.HasInstrument (parameters.reset index) environment := by
  rcases resetRun_hasInstrument parameters.resetParameters (index.lowerWidth + 1)
      (parameters.wire index) environment with ⟨Outcome, finite, ⟨actual⟩⟩
  let : Fintype Outcome := finite
  exact actual.embedIdentity.to_exists

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
