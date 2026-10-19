/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Canonical
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Canonical
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

/-- The canonical window adds no restriction to the original admitted signed instances. -/
public lemma valid_iff {N : Nat} (modulus : 2 ≤ N) (x : Int)
    (environment : (Sampling.Native.model (phaseWidth N) (targetWidth N)).Environment)
    (order : Nat)
    (state : ExecutionState (Execution.Store (pre (targetWidth N)))
      (pre (targetWidth N)).register) :
    (problem modulus x).valid environment order state ↔
      ∃ hinput : OrderFinding.Input N (x : ZMod N).val order,
        environment.quantum = OrderFinding.Native.interpretation
          (sourceAccess (modulusSpec modulus) (x : ZMod N).val (phaseWidth N)) ∧
        HasCanonicalBase hinput
          (sourceAccess (modulusSpec modulus) (x : ZMod N).val (phaseWidth N)) state := by
  constructor
  · rintro ⟨hinput, same, base, _⟩
    exact ⟨hinput, same, base⟩
  · rintro ⟨hinput, same, base⟩
    exact ⟨hinput, same, base, (orderFinding_widths_positive modulus).2,
      orderFinding_phaseWidth_fits N, orderFinding_phaseWidth_upper modulus⟩

/-- The complete canonical execution preserves the original order-dependent lower bound. -/
public lemma canonicalOrderFinding_problem_successLB {N : Nat}
    (modulus : 2 ≤ N) (x : Int)
    (environment : (Sampling.Native.model (phaseWidth N) (targetWidth N)).Environment)
    (order : Nat) :
    ((problem modulus x).successLB environment order).value =
      ENNReal.ofReal ((Nat.totient order : Real) / (3 * (order : Real))) := rfl

/-- The canonical-width execution satisfies the entire independent specification. -/
public lemma canonicalOrderFinding_algorithm_solves {N : Nat}
    (modulus : 2 ≤ N) (x : Int) :
    Algorithm.Solves (algorithm modulus) (problem modulus x) :=
  complete_correct modulus x

/-- An accepted retained unsigned word contains the original mathematical order. -/
public lemma canonicalOrderFinding_accepts_iff {N r : Nat} {x : Int}
    (hinput : OrderFinding.Input N (x : ZMod N).val r)
    (environment : (Sampling.Native.model (phaseWidth N) (targetWidth N)).Environment)
    (before : Execution.Store (pre (targetWidth N)))
    (word : Fin (2 ^ (phaseWidth N + 1))) :
    (problem hinput.modulus_ge_two x).accepts environment r
      before (.optionSome (.unsignedWord word)) ↔ word.val = r := by
  have modulusSquared : N ≤ N ^ 2 := by nlinarith [hinput.modulus_ge_two]
  have small : r < 2 ^ (phaseWidth N + 1) :=
    (lt_of_lt_of_le
      (lt_of_lt_of_le (input_order_lt_modulus hinput) modulusSquared)
      (orderFinding_phaseWidth_fits N)).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
  change CShape.Value.optionSome (.unsignedWord word) =
      .optionSome (.unsignedWord
        (ClassicalAlgorithms.OrderRecovery.candidateWord (phaseWidth N) r)) ↔ _
  simp only [CShape.Value.optionSome.injEq, CShape.Value.unsignedWord.injEq,
    Fin.ext_iff, ClassicalAlgorithms.OrderRecovery.candidateWord_val_of_lt small]

/-- Canonical phase sizing simplifies the full resident classical capacity. -/
public lemma canonicalOrderFinding_problem_classicalBits {N : Nat}
    (modulus : 2 ≤ N) (x : Int) :
    (problem modulus x).resources.resident .classicalBits =
      12 * phaseWidth N + 11 * targetWidth N + 17 := by
  change (SourceNativeEndpoint.problem (modulusSpec modulus)
    (x : ZMod N).val (phaseWidth N)).resources.resident .classicalBits = _
  rw [generalOrderFinding_problem_resident_classical]
  have width := orderFinding_phaseWidth_le_twice_targetWidth N
  rw [max_eq_right (by omega)]
  omega

/-- All owned quantum systems belong to the two canonical source registers. -/
public lemma canonicalOrderFinding_problem_qubits {N : Nat}
    (modulus : 2 ≤ N) (x : Int) :
    (problem modulus x).resources.resident (.quantumSystems 2) =
      phaseWidth N + targetWidth N := by
  change (SourceNativeEndpoint.problem (modulusSpec modulus)
    (x : ZMod N).val (phaseWidth N)).resources.resident (.quantumSystems 2) = _
  rw [generalOrderFinding_problem_resident_quantum]
  simp

/-- Every complete path has the expanded public classical-operation bound. -/
public lemma canonicalOrderFinding_algorithm_classicalOperations_le {N : Nat}
    (modulus : 2 ≤ N) (path : (algorithm modulus).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm modulus).run.code.resourcePool path) ≤
      12 * (phaseWidth N) ^ 2 + 4 * targetWidth N * phaseWidth N +
        64 * phaseWidth N + 4 * targetWidth N + 57 := by
  have bounded := generalOrderFinding_algorithm_classicalOperations_le
    (modulusSpec modulus) (phaseWidth N) path
  have formula :
      4 * (phaseWidth N + 1) + 5 +
          2 * (phaseWidth N + 1) * (2 * targetWidth N + 18 + 6 * (phaseWidth N + 1)) =
        12 * (phaseWidth N) ^ 2 + 4 * targetWidth N * phaseWidth N +
          64 * phaseWidth N + 4 * targetWidth N + 57 := by ring
  exact bounded.trans_eq formula

/-- The actual canonical-width execution has the stated query and standard gate counts. -/
public lemma canonicalOrderFinding_algorithm_nativeCounts {N : Nat}
    (modulus : 2 ≤ N) (path : (algorithm modulus).run.code.Path) :
    ResourcePool.count
        (model := Sampling.Native.Framed.model (phaseWidth N) (targetWidth N))
        (.oracle UnitarySource.Coordinate.ordinary)
        ((algorithm modulus).run.code.resourcePool path) = 1 ∧
    ResourcePool.count
        (model := Sampling.Native.Framed.model (phaseWidth N) (targetWidth N))
        (.gate .cnot) ((algorithm modulus).run.code.resourcePool path) =
      phaseWidth N * (phaseWidth N - 1) + 3 * (phaseWidth N / 2) ∧
    ResourcePool.count
        (model := Sampling.Native.Framed.model (phaseWidth N) (targetWidth N))
        (.gate .singleQubit) ((algorithm modulus).run.code.resourcePool path) =
      phaseWidth N * (3 * phaseWidth N + 1) / 2 := by
  constructor
  · exact generalOrderFinding_algorithm_modExpCount (modulusSpec modulus) (phaseWidth N) path
  constructor
  · simpa only [algorithm, ChooseTwo.twice_choose_two] using
      generalOrderFinding_algorithm_cnotCount (modulusSpec modulus) (phaseWidth N) path
  · simpa only [algorithm, ChooseTwo.two_mul_add_three_mul_choose_two] using
      generalOrderFinding_algorithm_singleQubitCount (modulusSpec modulus) (phaseWidth N) path

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint.Canonical
