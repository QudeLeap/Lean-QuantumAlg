/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Execution.Minimum
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Execution.Minimum

public import QuantumAlg.Algorithms.OrderFinding.Oracle.Canonical
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Projections
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.GateCounts
public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.ClassicalCounts
public import QuantumAlg.Util.Nat.ChooseTwo
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Util.Order.Finding
import all QuantumAlg.Util.Classical.OrderRecovery

/-!
# General order finding on signed inputs and canonical register widths

The mathematical integer base is represented by its canonical residue in the
original borrowed input cell. Both widths are fixed by the modulus, so the
source window and the complete resource bounds need no extra access premise.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint.Canonical

noncomputable section

/-- **Input.** An arbitrary integer base represented in its original canonical
borrowed cell, with its least positive modular order and modulus at least two.
The target and phase widths are respectively the ceilings of the binary
logarithms of the modulus and its square.

**Output.** The recovered modular order, or a reported unsuccessful sample.

**Resource budget.** Independent native event, quantum and classical storage,
and complete-execution depth budgets of the source sample and finite recovery.

**Success.** The true order is returned with probability at least
`Nat.totient r / (3 * r)`; the borrowed cell and its correlations are restored.

**Source.** [Sho95, source.tex:1124-1185]. -/
@[expose] public def problem {N : Nat} (modulus : 2 ≤ N) (x : Int) :=
  SourceNativeEndpoint.problem (modulusSpec modulus) (x : ZMod N).val (phaseWidth N)

/-- The canonical-width execution satisfies the entire independent specification. -/
private lemma complete_correct {N : Nat} (modulus : 2 ≤ N) (x : Int) :
    Algorithm.Solves (algorithm modulus) (problem modulus x) :=
  SourceNativeEndpoint.algorithm_solves (modulusSpec modulus) (x : ZMod N).val (phaseWidth N)

/-- One canonical execution handles every admitted signed source and unknown order. -/
public theorem main {N : Nat} (x : Int) (modulus : 2 ≤ N) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem modulus x) :=
  ⟨algorithm modulus, complete_correct modulus x⟩

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint.Canonical
