/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.AmplitudeEstimation.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Components.Oracle.AmplitudeAmplification
public import QuantumAlg.Core.Base.Accounting.Weighted
public import Mathlib.Data.Nat.Choose.Basic
public import QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import all QuantumAlg.Algorithms.AmplitudeEstimation.Basic
import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Distribution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Restoration
import all QuantumAlg.Algorithms.AmplitudeEstimation.Resources
import all QuantumAlg.Algorithms.AmplitudeEstimation.Space
import all QuantumAlg.Algorithms.AmplitudeEstimation.Specification
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Util.Real.PeriodicSinSq

/-!
# Complete native prepared-state amplitude estimation

The original source model and selected precision determine one actual
prepare, source-query, Z-write, and packing circuit. Complete Output retains
all of its phase/source systems and classical cells. Its own block masses
prove the original additive-error guarantee for every external reference,
while its actual paths satisfy independent native resource and depth bounds.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The public selected-width execution, including actual preparation and complete live Output. -/
public def algorithm (n : Nat) (eps η : Real) :
    Algorithm (model n) pre (post (selectedPhaseQubits eps η) n)
      (.bits (selectedPhaseQubits eps η)) where
  run := run n (selectedPhaseQubits eps η)

end

end QuantumAlg.AmplitudeEstimation
