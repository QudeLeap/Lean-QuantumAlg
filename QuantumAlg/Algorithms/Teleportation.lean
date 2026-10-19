/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Mathematics
public import QuantumAlg.Algorithms.Teleportation.Parallel.Construction
public import QuantumAlg.Algorithms.Teleportation.Parallel.BellResource
public import QuantumAlg.Algorithms.Teleportation.Parallel.Target
public import QuantumAlg.Algorithms.Teleportation.Parallel.Resources
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource
import all QuantumAlg.Algorithms.Teleportation.Parallel.Target
import all QuantumAlg.Algorithms.Teleportation.Parallel.Results
import all QuantumAlg.Algorithms.Teleportation.Parallel.Restoration
import all QuantumAlg.Algorithms.Teleportation.Parallel.Resources
import all QuantumAlg.Algorithms.Teleportation.Parallel.Time
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Complete measured quantum teleportation

The independent local Bell-resource promise permits arbitrary joint input and
reference correlations. The actual parallel protocol retains every measured
Alice system, every Bob system, and the real classical result cells. The
supporting mathematics also preserves the separate source communication
profile; the execution language contains no transmission event.
-/

namespace QuantumAlg.QuantumTeleportation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- **Input.** The n unknown input qubits may have arbitrary joint entanglement
and arbitrary external-reference correlations. The supplied 2n resource
systems have the specified local pure Bell-bank marginal. Initial result
cells need not be clean or independent of the quantum input.
**Output.** All 3n original quantum systems and the 2n actual measured bits
remain live. In every actual readout block, Alice's systems carry that basis
label and Bob together with the entire reference carries the original joint
input/reference density.
**Resource budget.** At most n CNOTs, 3n one-qubit gates, and 2n dimension-two
measurements. Resident space is 3n qubits and 2n classical bits; auxiliary
space is 2n classical bits. Quantum computation time is zero for an empty
bank and at most four otherwise. No communication latency is modeled.
**Success.** Probability one, with the complete reference-aware state promise
and restoration of the full borrowed observation.
**Source.** The CNOT/H measurement circuit and X/Z feedback in
[dW19, qcnotes.tex:785-809]. -/
@[expose] public def problem (count : Nat) :
    Problem Parallel.model (Parallel.context count) (Parallel.context count)
      (Parallel.resultShape count) where
  Witness := Unit
  valid := fun _ _ localState => Parallel.localBellMarginal count localState.quantumMarginal =
    DensityOperator.ofPure (Parallel.bellBank count)
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [Parallel.Target.requirement count]
  resources :=
    { events := Parallel.Resources.eventBudget count
      resident := Parallel.Resources.residentBudget count
      auxiliary := Parallel.Resources.auxiliaryBudget count }
  quantumTimeLimit := if count = 0 then 0 else 4

/-- One complete native measured protocol solves the independently specified teleportation task. -/
public theorem main (count : Nat) :
    ∃ candidate : Algorithm Parallel.model (Parallel.context count)
        (Parallel.context count) (Parallel.resultShape count) false,
      candidate.Solves (problem count) := by
  refine ⟨Parallel.algorithm count, ?_⟩
  constructor
  · intro environment _witness _Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness _Reference input admitted _initialization requirement present
    have same : requirement = Parallel.Target.requirement count :=
      List.mem_singleton.mp present
    subst requirement
    exact Parallel.Results.requirement_holds environment count input admitted
  · intro environment _witness _Reference input _valid _initialization
    exact Parallel.Restoration.borrowed environment count input
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact Parallel.Resources.code_events count path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact (Parallel.Resources.code_space count path).1.le
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact (Parallel.Resources.code_space count path).2.le
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact Parallel.code_time_le count path

end

end QuantumAlg.QuantumTeleportation
