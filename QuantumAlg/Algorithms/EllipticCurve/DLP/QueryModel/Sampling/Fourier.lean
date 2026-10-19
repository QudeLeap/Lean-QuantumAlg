/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.FourierLaw
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.SourceLaw
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.SourceLaw

/-!
# Full executed ECDLP measurement law in independent Fourier coordinates

The actual retained store and both complete quantum-reference entries have
the original group-action Fourier amplitudes. No supplied probability law,
state invariant or alternative execution is used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Every complete stored-state entry is the independent group-action Fourier law. -/
public lemma code_fourier_store_entry (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I).HiddenState × History))
    (stored : Store (post I)) (left right : (post I).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((code I expansion).execute (sourceEnvironment I A) Reference state).mapClassical
      (fun record => record.1)).block stored).matrix
        (left, leftRef) (right, rightRef) =
      if readoutsAgree I left right then
        sourceAmplitudeAt I ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
          (basisEquiv I left)) *
        (∑ original : Store (post I),
          if writtenStore I original left = stored then
            referenceCoefficient I A state original leftRef rightRef else 0) *
        star (sourceAmplitudeAt I
          ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)) (basisEquiv I right)))
      else 0 := by
  rw [code_store_entry, sourceEntry]
  simp only [sourceState_eq_sourceAmplitudeAt]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
