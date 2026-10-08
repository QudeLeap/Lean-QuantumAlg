/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Space

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Space

/-!
# Independent scalar space bounds for seven actual RSA-2048 batches

Only independent scalar width formulas are evaluated. The resulting numbers
equal the accepted finite-run allowance and bound actual resident and auxiliary
peaks on the same path; they do not assert that a path reaches that allowance.
The fixed key model is used only in proofs of the public modulus's widths.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

open Execution ClassicalRoutines.NumberTheory

noncomputable section

/-- Independent classical-bit allowance for seven complete native batches and selection. -/
@[expose] public def classicalBitBound : Nat := 1_053_148_427_049

/-- The one actual bank shared by all seven complete batches contains 6,147 qubits. -/
@[expose] public def qubitBound : Nat := 6_147

-- Use the already proved coordinate width without reducing its operand envelope.
attribute [local irreducible] RSA.ShortLogWidths.coordinateWidth

private theorem pair_arithmetic (width modulus measured jWidth kWidth : Nat)
    (combined : measured = jWidth + kWidth) :
    104 * width + 5 * modulus + 4 * measured + 2 * jWidth + 2 * kWidth + 33 =
      104 * width + 5 * modulus + 6 * measured + 33 := by omega

private theorem pair_allocation (N : Nat) :
    LatticePairRecoveryWorkspace.allocationBits N =
      104 * LatticeWideLllMachine.Width N + 5 * Canonical.modulusBits N +
        6 * measurementBits N + 33 :=
  pair_arithmetic (LatticeWideLllMachine.Width N) (Canonical.modulusBits N)
    (measurementBits N) (BatchMachine.JWidth N) (BatchMachine.KWidth N)
    (BatchMachine.measurementBits_eq_jkWidth N)

private theorem model_pairAllocation_eq {N : Nat} (model : FixedWidthModel N) :
    LatticePairRecoveryWorkspace.allocationBits N = 782_338_382_083 := by
  conv_lhs =>
    rw [pair_allocation]
    unfold LatticeWideLllMachine.Width
    rw [model_coordinateWidth_eq model, model_modulusBits_eq model,
      model_measurementBits_eq model]
  norm_num [modulusBits, primeBits]

private theorem model_quadraticAllocation_eq {N : Nat} (model : FixedWidthModel N) :
    QuadraticScratchLayout.allocationBits N = 255_764_463_735 := by
  have coordinate : LatticePairCandidateRecovery.Width N = 7_522_484_226 :=
    model_coordinateWidth_eq model
  let scalar (width : Nat) :=
    5 * QuadraticPrefix.discriminantWidth width +
      7 * QuadraticCandidateCheck.CandidateWidth width + QuadraticPrefix.centerWidth width +
      8 * NatSqrt.workWidth (QuadraticPrefix.discriminantWidth width) + 10
  have transport : QuadraticScratchLayout.allocationBits N = scalar 7_522_484_226 :=
    congrArg scalar coordinate
  have numeric : scalar 7_522_484_226 = 255_764_463_735 := by
    norm_num [scalar, QuadraticPrefix.discriminantWidth, QuadraticPrefix.centerWidth,
      QuadraticCandidateCheck.CandidateWidth, NatSqrt.workWidth]
  exact transport.trans numeric

private theorem model_factorWidth_eq {N : Nat} (model : FixedWidthModel N) :
    LatticeBatchRecoveryWorkspaceLayout.FactorWidth N = 7_522_484_228 := by
  have coordinate : LatticePairCandidateRecovery.Width N = 7_522_484_226 :=
    model_coordinateWidth_eq model
  exact (congrArg (fun width => width + 1 + 1) coordinate).trans (by norm_num)

private theorem model_allocationBits_eq {N : Nat} (model : FixedWidthModel N) :
    LatticeBatchRecoveryWorkspace.allocationBits N = 1_053_147_816_325 := by
  conv_lhs =>
    rw [LatticeBatchRecoveryWorkspace.allocationBits, model_factorWidth_eq model,
      model_modulusBits_eq model, model_pairAllocation_eq model,
      model_quadraticAllocation_eq model]
  norm_num [modulusBits, primeBits]

/-- The fixed classical number is proved from the complete independent seven-batch formula. -/
theorem model_classicalBitBound_eq {N : Nat} (model : FixedWidthModel N) :
    NativeFiniteRetry.classicalBitBound N rounds = classicalBitBound := by
  change LatticeBatchRecoveryWorkspace.allocationBits N + 36 * Canonical.modulusBits N +
    17 * measurementBits N + 19 +
      7 * (19 * Canonical.modulusBits N + 16 * measurementBits N + 2) = classicalBitBound
  rw [model_allocationBits_eq model, model_modulusBits_eq model, model_measurementBits_eq model]
  norm_num [classicalBitBound, modulusBits, primeBits]

/-- Seven positive batches use exactly the independent allowance of one 6,147-qubit bank. -/
theorem model_qubitBound_eq {N : Nat} (model : FixedWidthModel N) :
    NativeFiniteRetry.qubitBound N rounds = qubitBound := by
  change shortLogBits N + 2 * tradeoffBits N + 2 * arithmeticBits N = qubitBound
  rw [model_shortLogBits_eq model, model_tradeoffBits_eq model, model_arithmeticBits_eq model]
  norm_num [qubitBound, modulusBits, primeBits]

/-- Independent fixed-size allowance on every native space coordinate. -/
@[expose] public def additionalSpace : SpacePool .quantum
  | .classicalBits => classicalBitBound
  | .quantumSystems dimension => if dimension = 2 then qubitBound else 0

/-- The parameterized complete allowance specializes to the fixed numeric pool. -/
theorem model_additionalSpace_eq {N : Nat} (model : FixedWidthModel N) :
    NativeFiniteRetry.additionalSpace N rounds = additionalSpace := by
  funext axis
  cases axis with
  | classicalBits =>
      exact (NativeFiniteRetry.additionalSpace_classicalBits N rounds).trans
        (model_classicalBitBound_eq model)
  | quantumSystems dimension =>
      by_cases same : dimension = 2
      · subst dimension
        exact (NativeFiniteRetry.additionalSpace_qubits N rounds).trans
          (model_qubitBound_eq model)
      · change NativeFiniteRetry.additionalSpace N (6 + 1) (.quantumSystems dimension) = _
        rw [NativeFiniteRetry.additionalSpace_succ_quantum_layout,
          ShortDLP.CompiledMAU.shortDLP_runtimeLayout_eq_source]
        simp only [QubitLayout.toQuantumLayout_dimensionCount, same, Ne.symm same, ↓reduceIte,
          additionalSpace]

-- Reuse the accepted actual run bounds without unfolding its seven-batch path type.
attribute [local irreducible] NativeFiniteRetry.run NativeFiniteRetry.code NativeFiniteRetry.context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every actual fixed-run path obeys the independently derived resident classical-bit bound. -/
theorem run_resident_classicalBits_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.run base noQuantum input rounds).code.Path) :
    (NativeFiniteRetry.run base noQuantum input rounds).code.peakResidentSpace path
        .classicalBits ≤ base.residentSpace .classicalBits + classicalBitBound := by
  simpa only [model_classicalBitBound_eq model] using
    NativeFiniteRetry.run_resident_classicalBits_le base noQuantum input rounds path

/-- The same actual fixed-run path obeys the independent auxiliary classical-bit bound. -/
theorem run_auxiliary_classicalBits_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.run base noQuantum input rounds).code.Path) :
    (NativeFiniteRetry.run base noQuantum input rounds).code.peakAuxiliarySpace path
        .classicalBits ≤ base.auxiliarySpace .classicalBits + classicalBitBound := by
  simpa only [model_classicalBitBound_eq model] using
    NativeFiniteRetry.run_auxiliary_classicalBits_le base noQuantum input rounds path

/-- Every actual fixed-run resident quantum peak is bounded by the single shared bank. -/
theorem run_resident_qubits_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.run base noQuantum input rounds).code.Path) :
    (NativeFiniteRetry.run base noQuantum input rounds).code.peakResidentSpace path
        (.quantumSystems 2) ≤ base.residentSpace (.quantumSystems 2) + qubitBound := by
  simpa only [model_qubitBound_eq model] using
    NativeFiniteRetry.run_resident_qubits_le base noQuantum input rounds path

/-- Every actual fixed-run auxiliary quantum peak has the same single-bank upper bound. -/
theorem run_auxiliary_qubits_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.run base noQuantum input rounds).code.Path) :
    (NativeFiniteRetry.run base noQuantum input rounds).code.peakAuxiliarySpace path
        (.quantumSystems 2) ≤ base.auxiliarySpace (.quantumSystems 2) + qubitBound := by
  simpa only [model_qubitBound_eq model] using
    NativeFiniteRetry.run_auxiliary_qubits_le base noQuantum input rounds path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048
