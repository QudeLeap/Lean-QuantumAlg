/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Arithmetic.Counts
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Forward
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Shift
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Selection.Quotient
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Predicates.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Boundary.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Initialization
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Completion
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters

/-!
# Direct complete native ledger of the actual paired EEA forward

The same actual producer retains load, full initialization, 2044 bodies,
511 complete boundaries, full decoder/correction and physical unload.
The new paired arithmetic ledger composes directly with unchanged genuine
components. No complete old body/forward resource equality supplies a
native bound, and no planning allowance substitutes for actual events.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

private lemma body_nativePool (width : Nat) (enough : 2 ≤ width.size) :
    (bodyProgram width enough).eventCost = (ControlledShiftBlock.program width false).eventCost +
      ((arithmeticProgram width
        (NativeMicrostep.positive_of_enough width enough) false).eventCost +
        ((ControlledSignQuotient.program width).eventCost +
          ((arithmeticProgram width
            (NativeMicrostep.positive_of_enough width enough) true).eventCost +
            ((ControlledShiftBlock.program width true).eventCost +
              ((ControlledPhaseUpdates.program width enough false).eventCost +
                (ControlledPhaseUpdates.program width enough true).eventCost))))) := by rfl

private lemma body_native_bound (width : Nat) (enough : 2 ≤ width.size)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (first second third fourth fifth sixth seventh : Nat)
    (firstBound : ResourcePool.count focus
      (ControlledShiftBlock.program width false).eventCost ≤ first)
    (secondBound : ResourcePool.count focus (arithmeticProgram width
      (NativeMicrostep.positive_of_enough width enough) false).eventCost ≤ second)
    (thirdBound : ResourcePool.count focus (ControlledSignQuotient.program width).eventCost ≤ third)
    (fourthBound : ResourcePool.count focus (arithmeticProgram width
      (NativeMicrostep.positive_of_enough width enough) true).eventCost ≤ fourth)
    (fifthBound : ResourcePool.count focus
      (ControlledShiftBlock.program width true).eventCost ≤ fifth)
    (sixthBound : ResourcePool.count focus
      (ControlledPhaseUpdates.program width enough false).eventCost ≤ sixth)
    (seventhBound : ResourcePool.count focus
      (ControlledPhaseUpdates.program width enough true).eventCost ≤ seventh) :
    ResourcePool.count focus (bodyProgram width enough).eventCost ≤
      first + (second + (third + (fourth + (fifth + (sixth + seventh))))) := by
  simp only [body_nativePool, ResourcePool.count_add]
  exact Nat.add_le_add firstBound (Nat.add_le_add secondBound (Nat.add_le_add thirdBound
    (Nat.add_le_add fourthBound (Nat.add_le_add fifthBound
      (Nat.add_le_add sixthBound seventhBound)))))

private lemma body_native_time_bound (width : Nat) (enough : 2 ≤ width.size)
    (first second third fourth fifth sixth seventh : Nat)
    (firstBound : (ControlledShiftBlock.program width false).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ first)
    (secondBound : (arithmeticProgram width
      (NativeMicrostep.positive_of_enough width enough) false).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ second)
    (thirdBound : (ControlledSignQuotient.program width).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ third)
    (fourthBound : (arithmeticProgram width
      (NativeMicrostep.positive_of_enough width enough) true).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ fourth)
    (fifthBound : (ControlledShiftBlock.program width true).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ fifth)
    (sixthBound : (ControlledPhaseUpdates.program width enough false).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ sixth)
    (seventhBound : (ControlledPhaseUpdates.program width enough true).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ seventh) :
    (bodyProgram width enough).evaluatedEventDepth Resource.Event.quantumDuration ≤
      first + (second + (third + (fourth + (fifth + (sixth + seventh))))) := by
  simp only [bodyProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  exact Nat.add_le_add firstBound (Nat.add_le_add secondBound (Nat.add_le_add thirdBound
    (Nat.add_le_add fourthBound (Nat.add_le_add fifthBound
      (Nat.add_le_add sixthBound seventhBound)))))

/-- Every actual body component remains in the independent native Toffoli cap. -/
lemma p256_bodyProgram_toffoli_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (bodyProgram 256 (by decide)).eventCost ≤ 75570 := by
  have actual := body_native_bound 256 (by decide) (.gate .toffoli)
    3106 43348 1731 23625 3106 196 458
    (ControlledShiftBlock.p256_program_toffoli_count false).le
    (p256_arithmeticProgram_toffoli_direct false)
    ControlledSignQuotient.p256_program_toffoli_count.le
    (p256_arithmeticProgram_toffoli_direct true)
    (ControlledShiftBlock.p256_program_toffoli_count true).le
    (ControlledPhaseUpdates.p256_program_toffoli_count false).le
    (ControlledPhaseUpdates.p256_program_toffoli_count true).le
  exact actual.trans (by decide)

/-- The complete original arithmetic, address and negative-predicate CNOTs are all charged. -/
lemma p256_bodyProgram_cnot_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (bodyProgram 256 (by decide)).eventCost ≤ 61628 := by
  have actual := body_native_bound 256 (by decide) (.gate .cnot)
    72 49930 984 10576 66 0 0
    (ControlledShiftBlock.p256_program_cnot_count false).le
    (p256_arithmeticProgram_cnot_direct false)
    ControlledSignQuotient.p256_program_cnot_count.le
    (p256_arithmeticProgram_cnot_direct true)
    (ControlledShiftBlock.p256_program_cnot_count true).le
    (ControlledPhaseUpdates.p256_program_cnot_count false).le
    (ControlledPhaseUpdates.p256_program_cnot_count true).le
  exact actual.trans (by decide)

/-- Native X instructions retain their exact whole-body count even on inactive quantum controls. -/
lemma p256_bodyProgram_singleQubit_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (bodyProgram 256 (by decide)).eventCost = 22196 := by
  simp only [body_nativePool, ResourcePool.count_add,
    ControlledShiftBlock.p256_program_singleQubit_count,
    p256_arithmeticProgram_singleQubit_direct,
    ControlledSignQuotient.p256_program_singleQubit_count,
    ControlledPhaseUpdates.p256_program_singleQubit_count, Bool.false_eq_true, if_false, if_true]

/-- Serial chronological composition retains each actual component's native dependency schedule. -/
lemma p256_bodyProgram_quantumTime_direct :
    (bodyProgram 256 (by decide)).evaluatedEventDepth Resource.Event.quantumDuration ≤ 140000 := by
  have actual := body_native_time_bound 256 (by decide) 3178 84650 3169 44881 3172 304 646
    (ControlledShiftBlock.p256_program_quantumTime false).le
    (p256_arithmeticProgram_quantumTime_direct false)
    ControlledSignQuotient.p256_program_quantumTime_le
    (p256_arithmeticProgram_quantumTime_direct true)
    (ControlledShiftBlock.p256_program_quantumTime true).le
    (ControlledPhaseUpdates.p256_program_quantumTime false).le
    (ControlledPhaseUpdates.p256_program_quantumTime true).le
  exact actual.trans (by decide)

/-- Every actual cycle contains four complete body pools and the unchanged full boundary. -/
lemma cycleProgram_nativePool (width : Nat) (enough : 2 ≤ width.size) :
    (cycleProgram width enough).eventCost = 4 • (bodyProgram width enough).eventCost +
      (ControlledBoundary.program width enough).eventCost := by
  simp only [cycleProgram, UnitaryCircuit.seq_eventCost]
  abel

private lemma iterate_cycle_nativePool (width count : Nat) (enough : 2 ≤ width.size) :
    (UnitaryCircuit.iterate count (cycleProgram width enough)).eventCost =
      (4 * count) • (bodyProgram width enough).eventCost +
        count • (ControlledBoundary.program width enough).eventCost := by
  rw [UnitaryCircuit.iterate_eventCost, cycleProgram_nativePool, nsmul_add, smul_smul,
    Nat.mul_comm count 4]

/-- Exact full native event multiplicities follow this same actual program's assembly. -/
lemma program_nativePool (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventCost =
      (ControlledInitialization.loadProgram modulus).eventCost +
        (ControlledInitialization.program modulus).eventCost +
        (4 * (2 * modulus.size - 1)) •
          (bodyProgram modulus.size
            (PredicateLayout.modulus_length_width modulus nontrivial)).eventCost +
        (2 * modulus.size - 1) •
          (ControlledBoundary.program modulus.size
            (PredicateLayout.modulus_length_width modulus nontrivial)).eventCost +
        (ControlledCompletion.program modulus).eventCost +
        (ControlledCompletion.unloadProgram modulus).eventCost := by
  simp only [program, UnitaryCircuit.seq_eventCost, iterate_cycle_nativePool]
  abel

/-- Actual time follows the internal schedules of these same retained components. -/
lemma program_quantumTime_native (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration =
      (ControlledInitialization.loadProgram modulus).evaluatedEventDepth
          Resource.Event.quantumDuration +
        (ControlledInitialization.program modulus).evaluatedEventDepth
          Resource.Event.quantumDuration +
        (2 * modulus.size - 1) *
          (4 * (bodyProgram modulus.size
            (PredicateLayout.modulus_length_width modulus nontrivial)).evaluatedEventDepth
              Resource.Event.quantumDuration +
            (ControlledBoundary.program modulus.size
              (PredicateLayout.modulus_length_width modulus nontrivial)).evaluatedEventDepth
                Resource.Event.quantumDuration) +
        (ControlledCompletion.program modulus).evaluatedEventDepth
          Resource.Event.quantumDuration +
        (ControlledCompletion.unloadProgram modulus).evaluatedEventDepth
          Resource.Event.quantumDuration := by
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq, iterate_cycle_quantumTime]
  omega

lemma program_dagger_nativePool (modulus : Nat) (nontrivial : 1 < modulus) :
    ((program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost =
        (program modulus nontrivial).eventCost :=
  AlgorithmGate.algorithmGate_emptyAdjoints_eventCost _

lemma program_dagger_quantumTime_native (modulus : Nat) (nontrivial : 1 < modulus) :
    ((program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth
        Resource.Event.quantumDuration =
      (program modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration :=
  AlgorithmGate.algorithmGate_emptyAdjoints_quantumTime _

private abbrev p256 := EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus

private lemma p256_enough : 2 ≤ p256.size.size :=
  PredicateLayout.modulus_length_width p256 (by decide)

private lemma p256_width : p256.size = 256 := ControlledCounts.p256_size

private lemma body_count_width (width : Nat) (enough : 2 ≤ width.size) (same : width = 256)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (bodyProgram width enough).eventCost =
      ResourcePool.count focus (bodyProgram 256 (by decide)).eventCost := by
  subst width
  rfl

private lemma boundary_count_width (width : Nat) (enough : 2 ≤ width.size) (same : width = 256)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (ControlledBoundary.program width enough).eventCost =
      ResourcePool.count focus (ControlledBoundary.program 256 (by decide)).eventCost := by
  subst width
  rfl

private lemma body_time_width (width : Nat) (enough : 2 ≤ width.size) (same : width = 256) :
    (bodyProgram width enough).evaluatedEventDepth
        Resource.Event.quantumDuration =
      (bodyProgram 256 (by decide)).evaluatedEventDepth
        Resource.Event.quantumDuration := by
  subst width
  rfl

private lemma boundary_time_width (width : Nat) (enough : 2 ≤ width.size) (same : width = 256) :
    (ControlledBoundary.program width enough).evaluatedEventDepth
        Resource.Event.quantumDuration =
      (ControlledBoundary.program 256 (by decide)).evaluatedEventDepth
        Resource.Event.quantumDuration := by
  subst width
  rfl

private lemma forward_native_bound (modulus : Nat) (nontrivial : 1 < modulus)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (load initial body boundary finish unload : Nat)
    (loadBound : ResourcePool.count focus
      (ControlledInitialization.loadProgram modulus).eventCost ≤ load)
    (initialBound : ResourcePool.count focus
      (ControlledInitialization.program modulus).eventCost ≤ initial)
    (bodyBound : ResourcePool.count focus (bodyProgram modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)).eventCost ≤ body)
    (boundaryBound : ResourcePool.count focus (ControlledBoundary.program modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)).eventCost ≤ boundary)
    (finishBound : ResourcePool.count focus
      (ControlledCompletion.program modulus).eventCost ≤ finish)
    (unloadBound : ResourcePool.count focus
      (ControlledCompletion.unloadProgram modulus).eventCost ≤ unload) :
    ResourcePool.count focus (program modulus nontrivial).eventCost ≤
      load + initial + (4 * (2 * modulus.size - 1)) * body +
        (2 * modulus.size - 1) * boundary + finish + unload := by
  rw [program_nativePool]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add loadBound initialBound) (Nat.mul_le_mul_left _ bodyBound))
      (Nat.mul_le_mul_left _ boundaryBound)) finishBound) unloadBound

private lemma forward_native_exact (modulus : Nat) (nontrivial : 1 < modulus)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (load initial body boundary finish unload : Nat)
    (loadEq : ResourcePool.count focus
      (ControlledInitialization.loadProgram modulus).eventCost = load)
    (initialEq : ResourcePool.count focus
      (ControlledInitialization.program modulus).eventCost = initial)
    (bodyEq : ResourcePool.count focus (bodyProgram modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)).eventCost = body)
    (boundaryEq : ResourcePool.count focus (ControlledBoundary.program modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)).eventCost = boundary)
    (finishEq : ResourcePool.count focus
      (ControlledCompletion.program modulus).eventCost = finish)
    (unloadEq : ResourcePool.count focus
      (ControlledCompletion.unloadProgram modulus).eventCost = unload) :
    ResourcePool.count focus (program modulus nontrivial).eventCost =
      load + initial + (4 * (2 * modulus.size - 1)) * body +
        (2 * modulus.size - 1) * boundary + finish + unload := by
  rw [program_nativePool]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul,
    loadEq, initialEq, bodyEq, boundaryEq, finishEq, unloadEq]

private lemma forward_time_bound (modulus : Nat) (nontrivial : 1 < modulus)
    (load initial body boundary finish unload : Nat)
    (loadBound : (ControlledInitialization.loadProgram modulus).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ load)
    (initialBound : (ControlledInitialization.program modulus).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ initial)
    (bodyBound : (bodyProgram modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ body)
    (boundaryBound : (ControlledBoundary.program modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ boundary)
    (finishBound : (ControlledCompletion.program modulus).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ finish)
    (unloadBound : (ControlledCompletion.unloadProgram modulus).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ unload) :
    (program modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration ≤
      load + initial + (2 * modulus.size - 1) * (4 * body + boundary) + finish + unload := by
  rw [program_quantumTime_native]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add loadBound initialBound)
    (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left 4 bodyBound) boundaryBound)))
      finishBound) unloadBound

/-- Independent complete actual forward native toffoli cap, from every emitted component. -/
lemma p256_program_toffoli_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program p256 (by decide)).eventCost ≤ 210279839 := by
  have actual := forward_native_bound p256 (by decide) (.gate .toffoli)
    0 4774778 75570 85995 7096149 387
    ControlledInitialization.p256_loadProgram_counts.1.le
    ControlledInitialization.p256_program_toffoli_count.le
    ((body_count_width p256.size p256_enough p256_width (.gate .toffoli)).trans_le
      p256_bodyProgram_toffoli_direct)
    ((boundary_count_width p256.size p256_enough p256_width (.gate .toffoli)).trans_le
      ControlledBoundary.p256_program_toffoli_count_le)
    ControlledCompletion.p256_program_toffoli_count.le
    ControlledCompletion.p256_unloadProgram_counts.1.le
  exact actual.trans (by rw [p256_width])

/-- Independent complete actual forward native cnot cap, from every emitted component. -/
lemma p256_program_cnot_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program p256 (by decide)).eventCost ≤ 149962185 := by
  have actual := forward_native_bound p256 (by decide) (.gate .cnot)
    127 466321 61628 46043 2 130
    ControlledInitialization.p256_loadProgram_counts.2.1.le
    ControlledInitialization.p256_program_cnot_count.le
    ((body_count_width p256.size p256_enough p256_width (.gate .cnot)).trans_le
      p256_bodyProgram_cnot_direct)
    ((boundary_count_width p256.size p256_enough p256_width (.gate .cnot)).trans_le
      ControlledBoundary.p256_program_cnot_count_le)
    ControlledCompletion.p256_program_cnot_count.le
    ControlledCompletion.p256_unloadProgram_counts.2.1.le
  exact actual.trans (by rw [p256_width])

/-- Exact native single-qubit multiplicity retains every body and complete boundary. -/
lemma p256_program_singleQubit_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program p256 (by decide)).eventCost = 62544356 := by
  have actual := forward_native_exact p256 (by decide) (.gate .singleQubit) 0 0 22196 33612 0 0
    ControlledInitialization.p256_loadProgram_counts.2.2
    ControlledInitialization.p256_program_singleQubit_count
    ((body_count_width p256.size p256_enough p256_width (.gate .singleQubit)).trans
      p256_bodyProgram_singleQubit_direct)
    ((boundary_count_width p256.size p256_enough p256_width (.gate .singleQubit)).trans
      ControlledBoundary.p256_program_singleQubit_count)
    ControlledCompletion.p256_program_singleQubit_count
    ControlledCompletion.p256_unloadProgram_counts.2.2
  exact actual.trans (by rw [p256_width])

/-- Actual default quantumDuration depth preserves all emitted component dependency schedules. -/
lemma p256_program_quantumTime_direct :
    (program p256 (by decide)).evaluatedEventDepth Resource.Event.quantumDuration ≤ 383077592 := by
  have actual := forward_time_bound p256 (by decide) 127 5241099 140000 165518 7096151 517
    ControlledInitialization.p256_loadProgram_quantumTime.le
    ControlledInitialization.p256_program_quantumTime.le
    ((body_time_width p256.size p256_enough p256_width).trans_le
      p256_bodyProgram_quantumTime_direct)
    ((boundary_time_width p256.size p256_enough p256_width).trans_le
      ControlledBoundary.p256_program_quantumTime_le)
    ControlledCompletion.p256_program_quantumTime.le
    ControlledCompletion.p256_unloadProgram_quantumTime.le
  exact actual.trans (by rw [p256_width])

/-- The literal actual adjoint retains the independently counted complete forward Toffoli cap. -/
lemma p256_dagger_toffoli_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      ((program p256 (by decide)).dagger (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost ≤
        210279839 := by
  rw [program_dagger_nativePool]
  exact p256_program_toffoli_direct

/-- Every actual native CNOT remains in the same-forward adjoint resource pool. -/
lemma p256_dagger_cnot_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      ((program p256 (by decide)).dagger (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost ≤
        149962185 := by
  rw [program_dagger_nativePool]
  exact p256_program_cnot_direct

/-- Exact native X multiplicity also survives the literal adjoint of this unitary forward. -/
lemma p256_dagger_singleQubit_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      ((program p256 (by decide)).dagger (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost =
        62544356 := by
  rw [program_dagger_nativePool]
  exact p256_program_singleQubit_direct

/-- This actual same-forward adjoint retains the same full default native dependency duration. -/
lemma p256_dagger_quantumTime_direct :
    ((program p256 (by decide)).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 383077592 := by
  rw [program_dagger_quantumTime_native]
  exact p256_program_quantumTime_direct

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
