/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256
public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources
public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Coordinates
public import QuantumAlg.Algorithms.EllipticCurve.Resources.Results
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Results
import all QuantumAlg.Algorithms.EllipticCurve.P256
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Execution
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Memory
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Contract
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.Space
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Workspace

/-!
# The concrete P-256 contract and the independent public problem coordinates

Correctness, all seven numerical bounds and chronological unit-event depth
hold for the same concrete candidate and complete actual Path. The independent
problem's classical allowances keep the original exact coefficient widths and
numeric ceilings. Its two quantum storage roles contain exactly the 818-qubit streaming bank.

The public entry continues to expose only problem and existential main.
These separate results introduce no second execution or compatibility facade.
-/

namespace QuantumAlg.EllipticCurve.P256.StreamingResources

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.ExecutionContract
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local irreducible] ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth

/-- The fixed native P-256 problem carries only the unit specification witness. -/
public def unitWitness (I : P256.DomainParameters.PublicKeyInstance) :
    (P256LogicalResources.problem I).Witness := by
  letI : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.unitWitness (P256.DomainParameters.curve I.curveCert)
    (P256.Cascade.ecdlpInstance I) 4714 ((1 : ℝ) / 100)

/-- Supply the original public points with every normalized external reference retained. -/
public def sourceInput (I : P256.DomainParameters.PublicKeyInstance) {Reference : Register}
    (original : Input (P256.ActualRun.Pre I) Reference) :
    OracleInput .empty (P256.ActualRun.Pre I) Reference := by
  letI : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.sourceInput (P256.DomainParameters.curve I.curveCert)
    (P256.Cascade.ecdlpInstance I) original

/-- The original public-point input is legal for the same fixed P-256 program in every
  environment. -/
public lemma source_admits (I : P256.DomainParameters.PublicKeyInstance)
    (environment : ExecutionModel.Environment (.quantum AlgorithmGate.model .empty BitWord.model))
    {Reference : Register} (original : Input (P256.ActualRun.Pre I) Reference) :
    (P256LogicalResources.problem I).Admits environment (unitWitness I) (sourceInput I original)
      := by
  exact LogicalResources.source_admits (P256.DomainParameters.curve I.curveCert)
    (P256.Cascade.ecdlpInstance I) 4714 ((1 : ℝ) / 100) environment original

/-- The original public-point input satisfies P-256 validity. -/
public lemma source_valid (I : P256.DomainParameters.PublicKeyInstance)
    (environment : ExecutionModel.Environment (.quantum AlgorithmGate.model .empty BitWord.model))
    {Reference : Register} (original : Input (P256.ActualRun.Pre I) Reference) :
    (P256LogicalResources.problem I).valid environment (unitWitness I)
      (sourceInput I original).caller.localState :=
  (source_admits I environment original).1

/-- The original public-point input satisfies P-256 initialization. -/
public lemma source_initialized (I : P256.DomainParameters.PublicKeyInstance)
    (environment : ExecutionModel.Environment (.quantum AlgorithmGate.model .empty BitWord.model))
    {Reference : Register} (original : Input (P256.ActualRun.Pre I) Reference) :
    (P256LogicalResources.problem I).initialization environment (unitWitness I)
      (sourceInput I original).localState :=
  (source_admits I environment original).2

/-- Every mathematical and resource component concerns one concrete actual P-256 candidate. -/
public lemma p256_completeContract (I : P256.DomainParameters.PublicKeyInstance) :
    (P256.ActualRun.algorithm I).Solves (P256LogicalResources.problem I) ∧
      (∀ path : (P256.ActualRun.algorithm I).run.code.Path,
        SevenCoordinateBounds I path) ∧
      (∀ path : (P256.ActualRun.algorithm I).run.code.Path,
        (P256.ActualRun.algorithm I).run.code.depth (fun _ => 1) path ≤
          P256LogicalResources.Limits.wholeRunDepth) :=
  ⟨P256LogicalResources.candidate_solves I, run_sevenCoordinates I,
    run_wholeRunDepth_le I⟩

private lemma resident_pool (I : P256.DomainParameters.PublicKeyInstance) :
    (P256LogicalResources.problem I).resources.resident =
      recoveryTailScratchSpace .quantum
          (ECDLP.Canonical.Layout.fieldWidth (P256.DomainParameters.curve I.curveCert))
          (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))) +
        persistentCellSpace .quantum
          (ECDLP.Canonical.Layout.fieldWidth (P256.DomainParameters.curve I.curveCert))
          (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))) +
        (ECDLP.Measured.Recovery.PublicInput.context
          (P256.DomainParameters.curve I.curveCert)
          (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)))).residentSpace := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  rfl

private lemma auxiliary_pool (I : P256.DomainParameters.PublicKeyInstance) :
    (P256LogicalResources.problem I).resources.auxiliary =
      recoveryTailScratchSpace .quantum
          (ECDLP.Canonical.Layout.fieldWidth (P256.DomainParameters.curve I.curveCert))
          (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))) +
        persistentCellSpace .quantum
          (ECDLP.Canonical.Layout.fieldWidth (P256.DomainParameters.curve I.curveCert))
          (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))) +
        (ECDLP.Measured.Recovery.PublicInput.context
          (P256.DomainParameters.curve I.curveCert)
          (orderWidth (ECDLP.Canonical.problem
            (P256.Cascade.ecdlpInstance I)))).auxiliarySpace := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  rfl

private lemma signed_width (width : Nat) :
    ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth width =
      ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth (width + 1) := rfl

private lemma fixed_arithmetic (coefficient : Nat → Nat) (physical field sample : Nat)
    (copies extra total : Nat)
    (physicalValue : physical = 256) (fieldValue : field = 256) (sampleValue : sample = 260)
    (constantValue : copies * 256 + 4 * 260 + 256 + extra = total) :
    max (25 * sample + 9 * coefficient sample + 16)
        (27 * field + 9 * coefficient field + 15) +
      copies * field + 4 * sample + physical + extra =
      max (6516 + 9 * coefficient 260) (6927 + 9 * coefficient 256) + total := by
  subst physical field sample
  omega

private lemma fixed_widths (coefficient : Nat → Nat) (extra : Nat) :
    max (6516 + 9 * coefficient (260 + 1)) (6927 + 9 * coefficient (256 + 1)) + extra =
      max (6516 + 9 * coefficient 261) (6927 + 9 * coefficient 257) + extra := rfl

private lemma signed_coordinates (extra : Nat) :
    max (6516 + 9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth 260)
        (6927 + 9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth 256) +
        extra =
      max (6516 + 9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 261)
        (6927 + 9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 257) +
        extra :=
  (congrArg₂ (fun sample field => max (6516 + 9 * sample) (6927 + 9 * field) + extra)
    (signed_width 260) (signed_width 256)).trans
      (fixed_widths ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth extra)

private lemma resident_classical_formula
    {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat) :
    SpacePool.count .classicalBits
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        (ECDLP.Measured.Recovery.PublicInput.context E m).residentSpace) =
      max
        (25 * m + 9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth m + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth
            (ECDLP.Canonical.Layout.fieldWidth E) + 15) +
        6 * ECDLP.Canonical.Layout.fieldWidth E + 4 * m + p.size + 7 := by
  rw [SpacePool.count_add, SpacePool.count_add,
    recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits,
    (ECDLP.Measured.Recovery.ExecutionContract.Coordinates.publicContext_classicalBits E m).1]
  simp only [SpacePool.count_classicalBits_ofShape, CShape.bitWidth]
  omega

private lemma resident_classical_coordinates
    {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)
    (field : ECDLP.Canonical.Layout.fieldWidth E = 256) (sample : m = 260)
    (modulus : p.size = 256) :
    SpacePool.count .classicalBits
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        (ECDLP.Measured.Recovery.PublicInput.context E m).residentSpace) =
      P256LogicalResources.residentClassicalBitLimit :=
  (resident_classical_formula E m).trans
    ((fixed_arithmetic ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth
      _ _ _ 6 7 2839 modulus field sample rfl).trans
      ((signed_coordinates 2839).trans
        (P256LogicalResources.classicalBitLimit_eq
          ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 2839)))

private lemma auxiliary_classical_formula
    {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat) :
    SpacePool.count .classicalBits
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        (ECDLP.Measured.Recovery.PublicInput.context E m).auxiliarySpace) =
      max
        (25 * m + 9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth m + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth
            (ECDLP.Canonical.Layout.fieldWidth E) + 15) +
        2 * ECDLP.Canonical.Layout.fieldWidth E + 4 * m + p.size + 5 := by
  rw [SpacePool.count_add, SpacePool.count_add,
    recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits,
    (ECDLP.Measured.Recovery.ExecutionContract.Coordinates.publicContext_classicalBits E m).2]
  simp only [SpacePool.count_classicalBits_ofShape, CShape.bitWidth]
  omega

private lemma auxiliary_classical_coordinates
    {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)
    (field : ECDLP.Canonical.Layout.fieldWidth E = 256) (sample : m = 260)
    (modulus : p.size = 256) :
    SpacePool.count .classicalBits
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        (ECDLP.Measured.Recovery.PublicInput.context E m).auxiliarySpace) =
      P256LogicalResources.auxiliaryClassicalBitLimit :=
  (auxiliary_classical_formula E m).trans
    ((fixed_arithmetic ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth
      _ _ _ 2 5 1813 modulus field sample rfl).trans
      ((signed_coordinates 1813).trans
        (P256LogicalResources.classicalBitLimit_eq
          ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 1813)))

/-- The resident allowance is computed directly from the complete streaming context. -/
public lemma p256_problem_resident_classicalBits (I : P256.DomainParameters.PublicKeyInstance) :
    SpacePool.count .classicalBits (P256LogicalResources.problem I).resources.resident =
      P256LogicalResources.residentClassicalBitLimit :=
  (congrArg (SpacePool.count .classicalBits) (resident_pool I)).trans
    (resident_classical_coordinates (P256.DomainParameters.curve I.curveCert)
      (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)))
      (P256.Measured.canonicalFieldWidth I.curveCert) (P256.Measured.orderWidth_eq_260 I)
      P256.Measured.fieldModulus_size)

/-- The auxiliary classical allowance omits precisely the two borrowed public points. -/
public lemma p256_problem_auxiliary_classicalBits (I : P256.DomainParameters.PublicKeyInstance) :
    SpacePool.count .classicalBits (P256LogicalResources.problem I).resources.auxiliary =
      P256LogicalResources.auxiliaryClassicalBitLimit :=
  (congrArg (SpacePool.count .classicalBits) (auxiliary_pool I)).trans
    (auxiliary_classical_coordinates (P256.DomainParameters.curve I.curveCert)
      (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)))
      (P256.Measured.canonicalFieldWidth I.curveCert) (P256.Measured.orderWidth_eq_260 I)
      P256.Measured.fieldModulus_size)

private lemma resident_quantum_coordinates
    {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat) (modulus : p.size = 256)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        (ECDLP.Measured.Recovery.PublicInput.context E m).residentSpace) =
      if 2 = dimension then 818 else 0 := by
  rw [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits,
    ECDLP.Measured.Recovery.PublicInput.context_resident,
    ECDLP.Measured.Recovery.Layout.streamingTerminal_residentSpace]
  have arithmetic : 3 * (256 : Nat) + 4 * (256 : Nat).size + 14 = 818 := by decide
  simp [SpacePool.count, SpacePool.ofShape, OwnedQubits.space, modulus, arithmetic]

private lemma auxiliary_quantum_coordinates
    {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat) (modulus : p.size = 256)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) m +
        (ECDLP.Measured.Recovery.PublicInput.context E m).auxiliarySpace) =
      if 2 = dimension then 818 else 0 := by
  rw [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits,
    ECDLP.Measured.Recovery.PublicInput.context_auxiliary,
    ECDLP.Measured.Recovery.Layout.streamingTerminal_auxiliarySpace]
  have arithmetic : 3 * (256 : Nat) + 4 * (256 : Nat).size + 14 = 818 := by decide
  simp [SpacePool.count, SpacePool.ofShape, OwnedQubits.space, modulus, arithmetic]

/-- The problem resident pool contains exactly 818 qubits and zero systems in other dimensions. -/
public lemma p256_problem_resident_quantumSystems (I : P256.DomainParameters.PublicKeyInstance)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      (P256LogicalResources.problem I).resources.resident =
      if 2 = dimension then 818 else 0 :=
  (congrArg (SpacePool.count (.quantumSystems dimension)) (resident_pool I)).trans
    (resident_quantum_coordinates (P256.DomainParameters.curve I.curveCert)
      (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)))
      P256.Measured.fieldModulus_size dimension)

/-- The problem auxiliary pool has the same 818 owned qubits in every quantum dimension. -/
public lemma p256_problem_auxiliary_quantumSystems (I : P256.DomainParameters.PublicKeyInstance)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      (P256LogicalResources.problem I).resources.auxiliary =
      if 2 = dimension then 818 else 0 :=
  (congrArg (SpacePool.count (.quantumSystems dimension)) (auxiliary_pool I)).trans
    (auxiliary_quantum_coordinates (P256.DomainParameters.curve I.curveCert)
      (orderWidth (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)))
      P256.Measured.fieldModulus_size dimension)

/-- The fixed independent success target is exactly ninety-nine percent. -/
public lemma p256_problem_successLowerBound_eq (I : P256.DomainParameters.PublicKeyInstance)
    (environment : ExecutionModel.Environment (.quantum AlgorithmGate.model .empty BitWord.model))
    (witness : (P256LogicalResources.problem I).Witness) :
    ((P256LogicalResources.problem I).successLB environment witness).value =
      ENNReal.ofReal ((99 : ℝ) / 100) := by
  change 1 - ENNReal.ofReal ((1 : ℝ) / 100) = ENNReal.ofReal ((99 : ℝ) / 100)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
  norm_num

/-- The new public problem preserves the original resident classical bit ceiling. -/
public lemma p256_problem_resident_classicalBits_le
    (I : P256.DomainParameters.PublicKeyInstance) :
    SpacePool.count .classicalBits (P256LogicalResources.problem I).resources.resident ≤ 1237909 :=
  (p256_problem_resident_classicalBits I).le.trans P256LogicalResources.residentClassicalBitLimit_le

/-- The new public problem preserves the original auxiliary classical bit ceiling. -/
public lemma p256_problem_auxiliary_classicalBits_le
    (I : P256.DomainParameters.PublicKeyInstance) :
    SpacePool.count .classicalBits (P256LogicalResources.problem I).resources.auxiliary ≤ 1236883 :=
  (p256_problem_auxiliary_classicalBits I).le.trans
    P256LogicalResources.auxiliaryClassicalBitLimit_le

end

end QuantumAlg.EllipticCurve.P256.StreamingResources
