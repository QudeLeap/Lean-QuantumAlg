/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Execution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Execution

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Cycle
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Ambient
public import QuantumAlg.Util.Real.LogCeiling
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Cycle
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Encoding
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Base.Depth.Expr
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Scalar
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun

import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Finite-cyclic discrete logarithms with one actual binary quantum bank

The complete execution uses the minimal binary group representation, retains
its classical samples and physically resets the reused bank after every sample.
All displayed native resources and complete-run quantum-time bounds belong
to this same execution, including every positive order and arbitrary external
references [Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Known-order finite-cyclic discrete logarithm over every positive order.

**Input.** Empty executable input, a known finite generator order and target in
its cyclic subgroup, with arbitrary external reference and hidden group service.

**Output.** The optional native word of the advertised secret, all retained
sample cells, and the same binary bank after the last physical reset.

**Resource budget.** The algorithm owns one binary bank shared by every independent sample.
Each sample includes its final physical reset, and the group register uses
the minimal identity-anchored binary encoding. It uses only the declared
quantum action and the declared stateful classical group service, whose
accumulator is reset explicitly before each power check. The output is the
optional native word of the advertised secret. The event budget separates
gates, measurements, native word operations, quantum queries and classical
queries. Resident and auxiliary limits retain the one physical bank, all
measurement cells, the reset scratch, the result and the reused recovery
workspace.

**Success.** The exact answer is required with probability at least 2/3.

**Source.** [Sho95, source.tex:1713-1984].
-/
@[expose] public def problem (P : KnownOrderProblem G) :
    Problem (Reusable.model P) Reusable.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  Witness := FiniteCyclicDLP.Input P
  valid := fun environment _ _ => environment = Reusable.sourceEnvironment P
  initialization := fun _ _ _ => True
  accepts := fun _ secret => accepts secret
  successLB := fun _ _ => successLowerBound
  states := fun _ _ => []
  resources := resourceBudget P
  quantumTimeLimit := quantumTimeLimit P


end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The complete execution solves the independent all-order contract. -/
private lemma complete_correct (P : KnownOrderProblem G) :
    Algorithm.Solves (algorithm P) (problem P) where
  success := fun environment secret _ input => solves_success P environment secret input
  states := fun environment secret _ input => solves_states P environment secret input
  borrowed := fun environment secret _ input => solves_borrowed P environment secret input
  events := fun environment secret _ input => solves_events P environment secret input
  resident := fun environment secret _ input => solves_resident P environment secret input
  auxiliary := fun environment secret _ input => solves_auxiliary P environment secret input
  time := fun environment secret _ input => solves_time P environment secret input

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- A complete solver meets the independent finite-cyclic discrete-logarithm problem. -/
public theorem main (P : KnownOrderProblem G) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem P) :=
  ⟨algorithm P, complete_correct P⟩

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
