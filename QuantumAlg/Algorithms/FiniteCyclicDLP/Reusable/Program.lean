/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
public import QuantumAlg.Primitives.ZReset.Bank
public import QuantumAlg.Core.Execution.Classical.Composition.Range
public import QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Literal sequential sampling with one restored finite-cyclic DLP bank

Every round applies the native binary word, writes its own exponent cells and
physically resets the entire bank through the one shared scratch bit. The last
round performs the same reset. The program never prepares another bank and
never substitutes an abstract independent-sample operation
[Sho95, source.tex:1713-1984] [dW19, qcnotes.tex:5405-5420].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Real measurement and selected-X correction of every already-owned qubit. -/
public def reset (P : KnownOrderProblem G) (count : Nat) :
    QuantumAlg.Circuit (model P) (context P count) (context P count) :=
  ZReset.Bank.code (oracles := Binary.Oracle.model P) (qubits P count) (scratch P count)
    BitWord.model (ClassicalFiniteGroupOracle.model G)

/-- One complete native sample includes its required terminal physical reset. -/
public def round (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    QuantumAlg.Circuit (model P) (context P count) (context P count) :=
  (QuantumAlg.Circuit.unitary (nativeProgram P count expansion)).seq
    ((QuantumAlg.Circuit.measurementSequence (readouts P slot)).seq (reset P count))

/-- Each real retained sample slot is filled once in chronological order. -/
public def rounds (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    QuantumAlg.Circuit (model P) (context P count) (context P count) :=
  QuantumAlg.Circuit.forRange count fun slot => round P slot expansion

/-- One zero preparation followed by literal sequential reuse of the same full bank. -/
public def code (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    QuantumAlg.Circuit (model P) pre (context P count) :=
  (initialCode P count).seq (rounds P count expansion)

/-- The full manifest retains the one bank, every sample bit and the reset scratch. -/
public def run (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    AlgorithmRun (model P) pre (context P count)
      (.fixedVector count (.fixedVector (sampleWidth P) (.finite 2))) where
  code := code P count expansion
  output := Output.all (context P count) (.read (samplesInput P count))

end

end QuantumAlg.FiniteCyclicDLP.Reusable
