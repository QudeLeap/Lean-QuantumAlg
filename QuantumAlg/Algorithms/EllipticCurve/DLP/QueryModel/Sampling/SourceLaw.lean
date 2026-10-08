/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Readout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Readout
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# Complete independent source law of the executed ECDLP sampler

Every final store and both full quantum-reference coordinates are retained.
The only quantum amplitudes in the source expression are the independent
prepared-query-Fourier state. Its reference coefficient comes from real zero
allocation of the original input, selected by the actual measurement writes.
This scalar observation does not introduce another state or execution carrier.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The actual input-reference block after zero allocation, before any quantum sampling. -/
@[expose] public def referenceCoefficient (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I A).HiddenState × History))
    (stored : Store (post I)) (leftRef rightRef : Reference.Index) : ℂ :=
  ((((initialCode I A).execute Reference state).mapClassical
    (fun record => record.1)).block stored).matrix
      ((post I).quantumLayout.zeroLabel, leftRef)
      ((post I).quantumLayout.zeroLabel, rightRef)

/-- Independent source amplitudes and the actual original-reference write fiber. -/
@[expose] public def sourceEntry (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I A).HiddenState × History))
    (stored : Store (post I)) (left right : (post I).register.Index)
    (leftRef rightRef : Reference.Index) : ℂ :=
  if readoutsAgree I left right then
    sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
      (basisEquiv I left)) *
    (∑ original : Store (post I),
      if writtenStore I A original left = stored then
        referenceCoefficient I A state original leftRef rightRef else 0) *
    star (sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
      (basisEquiv I right)))
  else 0

private theorem weighted_store_entries (ctx : RuntimeCtx .quantum)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store ctx → ℂ)
    (left right : (Register.prod ctx.register Reference).Index) :
    ExecutionState.weightedMatrixEntry state (fun record => weight record.1) left right =
      ∑ original : Store ctx, weight original *
        ((state.mapClassical (fun record => record.1)).block original).matrix
          left right := by
  exact (ExecutionState.weightedMatrixEntry_mapClassical state
    (fun record => record.1) weight left right).symm

/-- The actual complete sampler equals the independent source law in every full matrix entry. -/
public theorem code_store_entry (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I A).HiddenState × History))
    (stored : Store (post I)) (left right : (post I).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((code I A expansion).execute Reference state).mapClassical
      (fun record => record.1)).block stored).matrix
        (left, leftRef) (right, rightRef) =
      sourceEntry I A state stored left right leftRef rightRef := by
  rw [BasisSeeded.store_matrix, code, Circuit.seq_store_marginal,
    ← BasisSeeded.store_matrix, readoutCode_store_entry]
  unfold readoutEntry sourceEntry
  split_ifs with agrees
  · refine (weighted_store_entries (post I)
      ((beforeMeasurement I A expansion).execute Reference state)
      (fun original => if writtenStore I A original left = stored then 1 else 0)
      (left, leftRef) (right, rightRef)).trans ?_
    calc
      _ = ∑ original : Store (post I),
          (if writtenStore I A original left = stored then 1 else 0) *
          (sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
            (basisEquiv I left)) * referenceCoefficient I A state original leftRef rightRef *
            star (sourceState I A ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
              (basisEquiv I right)))) := by
        apply Finset.sum_congr rfl
        intro original _
        exact congrArg (fun coefficient : ℂ =>
          (if writtenStore I A original left = stored then 1 else 0) * coefficient)
          (beforeMeasurement_store_entry I A expansion state original left right leftRef rightRef)
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro original _
        by_cases writes : writtenStore I A original left = stored
        · simp only [writes, if_true, one_mul]
        · simp only [writes, if_false, zero_mul, mul_zero]
  · rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
