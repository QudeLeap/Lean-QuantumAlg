/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling

/-!
# Original granted ECDLP environments

Every originally granted access supplies an admissible interpretation of the
same public query signature. Its action on unencoded basis labels remains
unrestricted by this bridge. The hidden scalar is a specification witness;
neither it nor the access operator is an argument of the actual program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original basis-action promise constrains only the interpretation. -/
@[expose] public def Admissible (I : ECDLPInstance E)
    (environment : (executionModel I).Environment) : Prop :=
  ∃ access : Access I, environment.quantum = interpretation I access

/-- Every access admitted by the original source remains admitted. -/
public lemma sourceEnvironment_admissible (I : ECDLPInstance E) (access : Access I) :
    Admissible I (sourceEnvironment I access) := ⟨access, rfl⟩

/-- Empty classical grants add no restriction to the original access promise. -/
public lemma admissible_iff_sourceEnvironment (I : ECDLPInstance E)
    (environment : (executionModel I).Environment) :
    Admissible I environment ↔ ∃ access : Access I, environment = sourceEnvironment I access := by
  constructor
  · rintro ⟨access, same⟩
    refine ⟨access, ?_⟩
    cases environment with
    | mk quantum classical =>
        cases classical
        cases same
        rfl
  · rintro ⟨access, rfl⟩
    exact sourceEnvironment_admissible I access

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
