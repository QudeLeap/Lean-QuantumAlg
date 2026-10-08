/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Laws
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Restart
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded.Record.Pure
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Seed

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round

/-!
# Actual original-input initialization fixes the entire retained quantum bank
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Actual bank and measurement/reset-cell allocation fixes zero without an input seed. -/
theorem ecdlpInitialAllocation_reinitializedAt (I : ECDLPInstance E) (A : Access I) :
    Circuit.ReinitializedAt (Sampling.Reuse.initialCode I A) (Sampling.Reuse.zeroSeed I) := by
  have empty : (Sampling.Reuse.context I).borrowedSelection = ∅ := by
    ext wire
    simp [RuntimeCtx.mem_borrowedSelection, Sampling.Reuse.ecdlpReuse_noBorrowedQuantum I]
  have all : (Sampling.Reuse.context I).borrowedSelectionᶜ = Finset.univ := by simp [empty]
  unfold Circuit.ReinitializedAt Sampling.Reuse.zeroSeed
  rw [all]
  intro Reference History _ state record
  have allocated := BasisSeeded.retain (model := Sampling.executionModel I A)
    (Sampling.post I).quantumLayout.zeroLabel ((Sampling.initialCode I A).execute Reference state)
    (Sampling.initialCode_seeded I A state) (Sampling.post I).canonicalFreshKey (.finite 2)
    (Sampling.post I).canonicalFreshKey_fresh
  have seeded := BasisSeeded.seq (Sampling.initialCode I A)
    (Circuit.retain (model := Sampling.executionModel I A) (Sampling.post I)
      (Sampling.post I).canonicalFreshKey (.finite 2) (Sampling.post I).canonicalFreshKey_fresh)
    (Sampling.Reuse.context I).quantumLayout.zeroLabel state allocated
  exact BasisSeeded.block_pure_fullSelection (Sampling.Reuse.context I).quantumLayout.zeroLabel
    ((Sampling.Reuse.initialCode I A).execute Reference state) seeded record

namespace Recovery

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

/-- Actual initialization and seven destinations establish the unchanged zero bank. -/
public theorem ecdlpRecovery_allocation_reinitializedAt (I : ECDLPInstance E) (A : Access I) :
    Circuit.ReinitializedAt (allocationCode I A) (roundZeroSeed I) :=
  followedByPersistentAt (Sampling.Reuse.initialCode I A) (fieldWidth E) (scalarWidth I)
    (Sampling.Reuse.zeroSeed I) (ecdlpInitialAllocation_reinitializedAt I A)

end Recovery

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
