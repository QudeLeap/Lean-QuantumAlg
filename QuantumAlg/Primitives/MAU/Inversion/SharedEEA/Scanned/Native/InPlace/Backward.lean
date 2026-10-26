/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Reuse

/-!
# Actual same-port native adjoint on the physically reused numerator workspace

The original large workspace is now the saved product. The actually
reset numerator takes its former role in the same native source
adjoint. The original input, all small source history and the complete
scan pool keep their physical identities. Every placement acts on the
actual supplied native circuit and charges its unchanged native events.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInPlaceFrame

noncomputable section

/-- Literal same-source native adjoint beside a completely retained complementary word. -/
def backwardSource (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum :=
  UnitaryCircuit.prodLeft (n := modulus.size)
    ((InPlaceForward.program modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))

/-- The actual native adjoint uses the physical numerator as its former large-workspace port. -/
def backward (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum :=
  (WorkspaceReuse.placement modulus.size).place (backwardSource modulus nontrivial)

/-- Complete admitted-input action retains every saved product bit and the same whole pool. -/
lemma backward_result (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input saved : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    (backward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((OutputCopy.encoding modulus.size).encode
            ((WorkspaceReuse.placement modulus.size).grouping.symm
              ((SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool),
                saved))))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((OutputCopy.encoding modulus.size).encode
          ((WorkspaceReuse.placement modulus.size).grouping.symm
            ((InitialPortProgram.inputFrame modulus input, pool), saved)))) := by
  have sourceActual := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (encoding modulus.size) (BinaryLabelEncoding.finIdentity modulus.size)
    ((InPlaceForward.program modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
    (SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool)
    (InitialPortProgram.inputFrame modulus input, pool) saved
    (InPlaceForward.dagger_result modulus nontrivial environment input coprime positive bounded
      pool addressZero prefixZero borrowZero)
  exact (WorkspaceReuse.placement modulus.size).place_ket_of_eq
    (backwardSource modulus nontrivial) _ _ sourceActual

/-- The same actual forward source is placed on the same reused physical workspace. -/
def reusedForward (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum :=
  (WorkspaceReuse.placement modulus.size).place (forward modulus nontrivial)

/-- The physically reused forward retains the arbitrary original saved product and pool. -/
lemma reusedForward_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input saved : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    (reusedForward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((OutputCopy.encoding modulus.size).encode
            ((WorkspaceReuse.placement modulus.size).grouping.symm
              ((InitialPortProgram.inputFrame modulus input, pool), saved))))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((OutputCopy.encoding modulus.size).encode
          ((WorkspaceReuse.placement modulus.size).grouping.symm
            ((SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool),
              saved)))) :=
  (WorkspaceReuse.placement modulus.size).place_ket_of_eq (forward modulus nontrivial) _ _
    (forward_initial modulus nontrivial environment input saved coprime positive bounded
      pool addressZero prefixZero borrowZero)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInPlaceFrame
