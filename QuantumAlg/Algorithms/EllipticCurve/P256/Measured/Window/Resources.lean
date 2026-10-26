/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Algorithm
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Algorithm
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Run
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Space
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.PublicInput
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Parameters.Representation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Frame

/-!
# Numeric resources of the actual public P-256 window algorithm

Every statement concerns the literal paid factory and every complete actual
path. The original two borrowed points add 1026 resident classical bits and no
auxiliary capacity. The physical bank has an 854-qubit ceiling in both roles;
every other quantum dimension is absent. Preparation, all three checked
34-window attempts, nearest recovery, terminal cleanup and the final pack remain
part of that same run. The sharp classical-work ceiling comes from its actual
weighted trace, independently of the conservative finite native-event envelope.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Resources

noncomputable section

open PrimeFieldShortWeierstrass ClassicalRoutines.EllipticCurve

attribute [local irreducible] Nat.size Nat.clog Circuit.resourcePool
  Circuit.peakResidentSpace Circuit.peakAuxiliarySpace
  RuntimeCtx.residentSpace RuntimeCtx.auxiliarySpace

private lemma publicFrame_resident (I : DomainParameters.PublicKeyInstance) :
    (Factory.publicFrame I).residentSpace = SpacePool.ofShape (.bits 1026) := by
  change (ECDLP.Measured.Recovery.PublicInput.frame
    (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)).residentSpace = _
  rw [ECDLP.Measured.Recovery.PublicInput.frame_resident]
  simp only [ECDLP.Canonical.Runtime.Context.PointShape]
  ext axis
  cases axis <;>
    norm_num [SpacePool.ofShape, PointShape, CShape.bitWidth, originalFieldWidth_eq_256 I]

private lemma publicFrame_auxiliary (I : DomainParameters.PublicKeyInstance) :
    (Factory.publicFrame I).auxiliarySpace = 0 :=
  ECDLP.Measured.Recovery.PublicInput.frame_auxiliary
    (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)

/-- Both storage roles charge at most 854 actual qubits and no systems of another dimension. -/
public lemma run_quantumSystems_le (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) (dimension : ℕ+) :
    ((algorithm I).run.code.peakResidentSpace path) (.quantumSystems dimension) ≤
        (if (2 : ℕ+) = dimension then 854 else 0) ∧
      ((algorithm I).run.code.peakAuxiliarySpace path) (.quantumSystems dimension) ≤
        (if (2 : ℕ+) = dimension then 854 else 0) := by
  have resident := Factory.paidRun_resident_quantumSystems_le
    (services := .empty) (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I) dimension path
  have auxiliary := Factory.paidRun_auxiliary_quantumSystems_le
    (services := .empty) (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I) dimension path
  rw [publicFrame_resident] at resident
  rw [publicFrame_auxiliary] at auxiliary
  simp only [SpacePool.ofShape, Nat.add_zero] at resident
  simp only [Pi.zero_apply, Nat.add_zero] at auxiliary
  exact ⟨resident, auxiliary⟩

private lemma zero_counts {resident auxiliary : Nat} {dimension : ℕ+}
    (different : (2 : ℕ+) ≠ dimension)
    (bounds : resident ≤ (if (2 : ℕ+) = dimension then 854 else 0) ∧
      auxiliary ≤ (if (2 : ℕ+) = dimension then 854 else 0)) :
    resident = 0 ∧ auxiliary = 0 := by
  rw [if_neg different] at bounds
  exact ⟨Nat.eq_zero_of_le_zero bounds.1, Nat.eq_zero_of_le_zero bounds.2⟩

/-- Every positive quantum dimension other than two has exactly zero peak occupancy. -/
public lemma run_nonQubit_zero (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) (dimension : ℕ+)
    (different : (2 : ℕ+) ≠ dimension) :
    ((algorithm I).run.code.peakResidentSpace path) (.quantumSystems dimension) = 0 ∧
      ((algorithm I).run.code.peakAuxiliarySpace path) (.quantumSystems dimension) = 0 :=
  zero_counts different (run_quantumSystems_le I path dimension)

/-- Resident bits include both original borrowed points; auxiliary bits preserve their roles. -/
public lemma run_classicalBits_le (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) :
    ((algorithm I).run.code.peakResidentSpace path) .classicalBits ≤ 85102168 ∧
      ((algorithm I).run.code.peakAuxiliarySpace path) .classicalBits ≤
        85101142 := by
  have resident := Factory.paidRun_resident_classical_le
    (services := .empty) (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I) path
  have auxiliary := Factory.paidRun_auxiliary_classical_le
    (services := .empty) (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I) path
  rw [publicFrame_resident] at resident
  rw [publicFrame_auxiliary] at auxiliary
  exact ⟨resident, auxiliary⟩

/-- The three native quantum gate ceilings belong to every complete actual public path. -/
public lemma run_native_le (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate coordinate) ((algorithm I).run.code.resourcePool path) ≤
      match coordinate with
      | .toffoli => 99272733288
      | .cnot => 81134896044
      | .singleQubit => 25700867624 :=
  Factory.paidRun_native_le (services := .empty)
    (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I) coordinate path

/-- All 215432 actual measurements include arithmetic masks, sampling and terminal cleanup. -/
public lemma run_measurement_count (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.measurement (2 : ℕ+)) ((algorithm I).run.code.resourcePool path) = 215432 :=
  Factory.paidRun_measurement_count (services := .empty)
    (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I) path

/-- The same complete public path retains the independently proved quantum-time ceiling. -/
public lemma run_quantumTime_le (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) :
    (algorithm I).run.code.quantumTime path ≤ 171185448791 :=
  Factory.paidRun_quantumTime_le (services := .empty)
    (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I) path

/-- The sharp modeled classical-work bound includes signed preparation and paid recovery. -/
public lemma run_classicalOperations_le (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm I).run.code.resourcePool path) ≤ 20292181815 :=
  Factory.paidRun_classical_le (services := .empty)
    (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
    (Factory.publicBaseRef I) (Factory.publicTargetRef I) path

/-- Seven numeric coordinates of one complete actual public window execution. -/
@[expose] public def SevenCoordinateBounds (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) : Prop :=
  (∀ dimension : ℕ+,
    ((algorithm I).run.code.peakResidentSpace path) (.quantumSystems dimension) ≤
        (if (2 : ℕ+) = dimension then 854 else 0) ∧
      ((algorithm I).run.code.peakAuxiliarySpace path) (.quantumSystems dimension) ≤
        (if (2 : ℕ+) = dimension then 854 else 0)) ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .toffoli)
      ((algorithm I).run.code.resourcePool path) ≤ 99272733288 ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .cnot)
      ((algorithm I).run.code.resourcePool path) ≤ 81134896044 ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate .singleQubit)
      ((algorithm I).run.code.resourcePool path) ≤ 25700867624 ∧
  (algorithm I).run.code.quantumTime path ≤ 171185448791 ∧
  (((algorithm I).run.code.peakResidentSpace path) .classicalBits ≤ 85102168 ∧
    ((algorithm I).run.code.peakAuxiliarySpace path) .classicalBits ≤ 85101142) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm I).run.code.resourcePool path) ≤ 20292181815

/-- All seven bounds concern the same actual run and full Path, without input assumptions. -/
public lemma run_sevenCoordinates (I : DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) : SevenCoordinateBounds I path :=
  ⟨run_quantumSystems_le I path, run_native_le I path .toffoli,
    run_native_le I path .cnot, run_native_le I path .singleQubit,
    run_quantumTime_le I path, run_classicalBits_le I path, run_classicalOperations_le I path⟩

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Resources
