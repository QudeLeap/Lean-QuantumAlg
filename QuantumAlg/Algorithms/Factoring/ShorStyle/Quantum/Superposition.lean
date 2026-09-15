/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.PowerAction
import all QuantumAlg.Algorithms.OrderFinding.BornModel

/-!
# Coherent modular powers from the original phase Hadamards

The actual preparation layer produces a uniform phase register and leaves
the unit power and zero arithmetic auxiliary untouched. Linearity of the
same compiled MAU operator gives the coherent sum of all original modular
powers with that same auxiliary zero. No classical distribution replaces
the quantum superposition [Sho95, source.tex:1183-1245].
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

open scoped BigOperators
open Nat.FixedWidth

private theorem circuit_applyVec_sum {R : Register} {Index : Type} [Fintype Index]
    (circuit : UnitaryCircuit R) (vectors : Index → HilbertVector R) :
    circuit.applyVec (∑ index, vectors index) = ∑ index, circuit.applyVec (vectors index) :=
  HilbertOperator.applyVec_sum (circuit : HilbertOperator R) vectors

/-- Original phase Hadamards preserve the literal unit and zero auxiliary seed. -/
theorem preparation_apply_seed (N : Nat) :
    (OrderFinding.orderFindingPreparationCircuit (phaseBits N)
      (modulusBits N + modulusBits N)).applyVec
        (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)).vec =
      HilbertVector.tensor (WalshHadamard.uniformState (phaseBits N)).vec
        (NormalizedVector.ket (R := Qubits (modulusBits N + modulusBits N))
          (prodEquiv ((1 : Fin (2 ^ modulusBits N)), (0 : Fin (2 ^ modulusBits N))))).vec := by
  change (OrderFinding.orderFindingPreparationCircuit (phaseBits N)
    (modulusBits N + modulusBits N)).applyVec
      (NormalizedVector.ket (prodEquiv ((0 : Fin (2 ^ phaseBits N)),
        prodEquiv ((1 : Fin (2 ^ modulusBits N)), (0 : Fin (2 ^ modulusBits N)))))).vec = _
  rw [← NormalizedVector.tensor_ket]
  change (OrderFinding.orderFindingPreparationCircuit (phaseBits N)
    (modulusBits N + modulusBits N)).matrix.applyVec
      (HilbertVector.tensor
        (NormalizedVector.ket (R := Qubits (phaseBits N)) 0).vec
        (NormalizedVector.ket (R := Qubits (modulusBits N + modulusBits N))
          (prodEquiv ((1 : Fin (2 ^ modulusBits N)), (0 : Fin (2 ^ modulusBits N))))).vec) = _
  rw [OrderFinding.orderFindingPreparationCircuit, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor _
    ((UnitaryCircuit.identity (Qubits (modulusBits N + modulusBits N))
      (List.range' (phaseBits N) (modulusBits N + modulusBits N)) List.nodup_range').applyVec _) = _
  rw [UnitaryCircuit.applyVec_identity]
  congr 1
  rw [WalshHadamard.hadamardLayer_matrix]
  exact congrArg NormalizedVector.vec WalshHadamard.hadamardLayerOperator_apply_zero

/-- The source phase register is a coherent basis expansion on the unchanged seed words. -/
theorem preparation_seed_sum (N : Nat) :
    (OrderFinding.orderFindingPreparationCircuit (phaseBits N)
      (modulusBits N + modulusBits N)).applyVec
        (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)).vec =
      ∑ exponent : Fin (2 ^ phaseBits N), WalshHadamard.invSqrtCard (phaseBits N) •
        (NormalizedVector.ket (R := Qubits (totalQubits N))
          ((MAU.Exponentiation.Gidney.encoding (phaseBits N) (modulusBits N)).encode
            (exponent, 1, 0))).vec := by
  classical
  rw [preparation_apply_seed]
  change HilbertVector.tensor _ _ =
    ∑ exponent : Fin (2 ^ phaseBits N), WalshHadamard.invSqrtCard (phaseBits N) •
      (NormalizedVector.ket (R := Qubits (phaseBits N + (modulusBits N + modulusBits N)))
        (prodEquiv (exponent,
          prodEquiv ((1 : Fin (2 ^ modulusBits N)), (0 : Fin (2 ^ modulusBits N)))))).vec
  apply WithLp.ofLp_injective
  funext basis
  obtain ⟨⟨phase, target⟩, rfl⟩ :=
    (prodEquiv (m := phaseBits N) (n := modulusBits N + modulusBits N)).surjective basis
  by_cases isSeed : target =
      prodEquiv ((1 : Fin (2 ^ modulusBits N)), (0 : Fin (2 ^ modulusBits N)))
  · simp [WalshHadamard.uniformState_apply, NormalizedVector.ket_apply, isSeed]
  · simp [WalshHadamard.uniformState_apply, NormalizedVector.ket_apply, isSeed]

/-- The actual power operator acts coherently on all exponents and returns the auxiliary to zero. -/
theorem power_after_preparation {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (MAU.Exponentiation.Gidney.program (phaseBits N) (modulusBits N)
      (modulus N) (selectedUnit parameter)).applyVec
        ((OrderFinding.orderFindingPreparationCircuit (phaseBits N)
          (modulusBits N + modulusBits N)).applyVec
            (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)).vec) =
      ∑ exponent : Fin (2 ^ phaseBits N), WalshHadamard.invSqrtCard (phaseBits N) •
        (NormalizedVector.ket (R := Qubits (totalQubits N))
          ((MAU.Exponentiation.Gidney.encoding (phaseBits N) (modulusBits N)).encode
            (exponent, unitResidueWord (modulus N) input.modulus_pos
              (selectedUnit parameter ^ exponent.val), 0))).vec := by
  let power := MAU.Exponentiation.Gidney.program (phaseBits N) (modulusBits N)
    (modulus N) (selectedUnit (N := N) parameter)
  have prepared := congrArg power.applyVec (preparation_seed_sum N)
  have distributed := circuit_applyVec_sum power
    (fun exponent : Fin (2 ^ phaseBits N) => WalshHadamard.invSqrtCard (phaseBits N) •
      (NormalizedVector.ket (R := Qubits (totalQubits N))
        ((MAU.Exponentiation.Gidney.encoding (phaseBits N) (modulusBits N)).encode
          (exponent, 1, 0))).vec)
  refine prepared.trans (distributed.trans ?_)
  apply Finset.sum_congr rfl
  intro exponent _present
  refine (UnitaryCircuit.applyVec_smul power _ _).trans ?_
  exact congrArg (fun vector : NormalizedVector (Qubits (totalQubits N)) =>
    WalshHadamard.invSqrtCard (phaseBits N) • vector.vec)
      (power_apply_seed input parameter exponent)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
