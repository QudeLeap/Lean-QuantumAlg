/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Preparation
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Uniform preparation for every positive subgroup order

The public ECDLP statement permits a binary expansion with one set bit
(`s = 0`) as well as the non-power-of-two case.  The latter is prepared by
Algorithm 1 of [SV24, Uniform.tex:622-664,775-805,996-1024].  The former is
the ordinary parallel Hadamard layer on the occupied low bits.  Both literal
circuits are padded only by high zero wires and prepare the same range-uniform
state used by the finite-cyclic Born analysis.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ECDLP
namespace Canonical

noncomputable section

/-- A strictly increasing binary expansion with one or more set bits.
Unlike `UniformSuperposition.BinaryExpansion`, this public ECDLP boundary also
admits the one-term power-of-two case `s = 0`. -/
public structure OrderExpansion (N : Nat) where
  /-- Largest index in the set-bit sequence. -/
  s : Nat
  /-- Set-bit exponents in increasing order. -/
  ell : Fin (s + 1) → Nat
  /-- The bit positions are strictly increasing. -/
  ell_strict : StrictMono ell
  /-- The certified binary expansion. -/
  sum_powers : N = ∑ j, 2 ^ ell j
  /-- The represented order is positive. -/
  N_pos : 0 < N

namespace OrderExpansion

variable {N : Nat}

attribute [local simp] ResourcePool.count_singleton_of_ne
attribute [local simp] Resource.GateLabel.mk.injEq

/-- Lowest set-bit exponent. -/
def first (B : OrderExpansion N) : Nat :=
  B.ell 0

/-- Highest set-bit exponent. -/
def last (B : OrderExpansion N) : Nat :=
  B.ell (Fin.last B.s)

/-- Locked aggregate one-qubit allowance for one preparation. -/
def singleQubitBound (B : OrderExpansion N) : Nat :=
  5 * B.s + 6 * B.last - 5 * B.first

/-- Locked CNOT allowance for one preparation. -/
def cnotBound (B : OrderExpansion N) : Nat :=
  B.last - B.first + 2 * B.s

/-- Locked sequential depth allowance for one preparation. -/
def depthBound (B : OrderExpansion N) : Nat :=
  5 * (B.last - B.first) + 5 * B.s + 1

/-- The non-power-of-two branch uses the reusable expansion of Algorithm 1
[SV24, Uniform.tex:640-659]. -/
def toBinaryExpansion (B : OrderExpansion N) (positive : 1 ≤ B.s) :
    UniformSuperposition.BinaryExpansion N where
  s := B.s
  s_pos := positive
  ell := B.ell
  ell_strict := B.ell_strict
  sum_powers := B.sum_powers
  N_pos := B.N_pos

@[simp]
theorem toBinaryExpansion_first (B : OrderExpansion N) (positive : 1 ≤ B.s) :
    (B.toBinaryExpansion positive).first = B.first :=
  rfl

@[simp]
theorem toBinaryExpansion_last (B : OrderExpansion N) (positive : 1 ≤ B.s) :
    (B.toBinaryExpansion positive).last = B.last :=
  rfl

@[simp]
theorem toBinaryExpansion_singleQubitBound
    (B : OrderExpansion N) (positive : 1 ≤ B.s) :
    (B.toBinaryExpansion positive).singleQubitBound = B.singleQubitBound :=
  rfl

@[simp]
theorem toBinaryExpansion_cnotBound
    (B : OrderExpansion N) (positive : 1 ≤ B.s) :
    (B.toBinaryExpansion positive).cnotBound = B.cnotBound :=
  rfl

@[simp]
theorem toBinaryExpansion_depthBound
    (B : OrderExpansion N) (positive : 1 ≤ B.s) :
    (B.toBinaryExpansion positive).depthBound = B.depthBound :=
  rfl

/-- A one-term expansion is the corresponding power of two. -/
theorem eq_pow_first_of_s_eq_zero (B : OrderExpansion N)
    (zero : B.s = 0) :
    N = 2 ^ B.first := by
  calc
    N = ∑ j, 2 ^ B.ell j := B.sum_powers
    _ = 2 ^ B.ell 0 := by
      classical
      rw [Finset.sum_eq_single 0]
      · intro index _ indexNe
        exfalso
        apply indexNe
        apply Fin.ext
        have indexBound := index.isLt
        simp only [Fin.val_zero]
        omega
      · simp
    _ = 2 ^ B.first := rfl

/-- In the one-term branch the first and last exponents coincide. -/
theorem last_eq_first_of_s_eq_zero (B : OrderExpansion N)
    (zero : B.s = 0) :
    B.last = B.first := by
  unfold last first
  congr 1
  apply Fin.ext
  simpa using zero

/-- The occupied low Hadamard block fits in the oversampled Fourier register. -/
theorem first_le_orderWidth_of_s_eq_zero
    {G : Type*} [Group G] (P : FiniteCyclicDLP.KnownOrderProblem G)
    (B : OrderExpansion P.order) (zero : B.s = 0) :
    B.first ≤ FiniteCyclicDLP.orderWidth P := by
  have powerBound : 2 ^ B.first ≤
      2 ^ FiniteCyclicDLP.orderWidth P := by
    rw [← B.eq_pow_first_of_s_eq_zero zero]
    exact FiniteCyclicDLP.order_le_fourierModulus P
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp powerBound

/-- The full-range Hadamard state is the finite-range uniform state at a
power-of-two range size. -/
theorem hadamardLayer_apply_zero_uniformState (width : Nat) :
    (WalshHadamard.hadamardLayer width).applyNormalized
        (NormalizedVector.ket (R := Qubits width) 0) =
      UniformSuperposition.uniformState (2 ^ width) width
        (by positivity) (le_refl _) := by
  rw [UnitaryCircuit.applyNormalized, WalshHadamard.hadamardLayer_matrix,
    WalshHadamard.hadamardLayerOperator_apply_zero]
  apply NormalizedVector.ext
  intro index
  simp only [WalshHadamard.uniformState_apply,
    UniformSuperposition.uniformState_apply, if_pos index.isLt]
  rfl

/-- The literal preparation at the oversampled register width.  Algorithm 1
handles every multi-term expansion; a single low Hadamard layer handles the
one-term power-of-two boundary. -/
def paddedPreparation
    {G : Type*} [Group G] (P : FiniteCyclicDLP.KnownOrderProblem G)
    (B : OrderExpansion P.order) :
    UnitaryCircuit (Qubits (FiniteCyclicDLP.orderWidth P)) :=
  if positive : 1 ≤ B.s then
    FiniteCyclicDLP.Canonical.GateLevelAttempt.paddedPreparation P
      (B.toBinaryExpansion positive)
  else
    UniformSuperposition.withCanonicalFootprint
      (UniformSuperposition.padHigh
        (B.first_le_orderWidth_of_s_eq_zero P (by omega))
        (WalshHadamard.hadamardLayer B.first))

@[simp]
theorem paddedPreparation_physical_idx
    {G : Type*} [Group G] (P : FiniteCyclicDLP.KnownOrderProblem G)
    (B : OrderExpansion P.order) :
    (B.paddedPreparation P).physical_idx =
      List.range (FiniteCyclicDLP.orderWidth P) := by
  unfold paddedPreparation
  split_ifs with positive
  · exact
      FiniteCyclicDLP.Canonical.GateLevelAttempt.paddedPreparation_physical_idx P
        (B.toBinaryExpansion positive)
  · apply UniformSuperposition.withCanonicalFootprint_physical_idx
    unfold UniformSuperposition.padHigh
    rw [UniformSuperposition.castWidth_physical_idx]
    have contained := UnitaryCircuit.prodRight_physical_idx_subset_range
      (m := FiniteCyclicDLP.orderWidth P - B.first)
      (WalshHadamard.hadamardLayer B.first) (by
        rw [WalshHadamard.hadamardLayer_physical_idx]
        intro index member
        exact member)
    simpa [Nat.sub_add_cancel
      (B.first_le_orderWidth_of_s_eq_zero P (by omega))] using contained

/-- Both branches prepare the exact range-uniform state consumed by the
established analytical experiment. -/
theorem paddedPreparation_apply_zero
    {G : Type*} [Group G] (P : FiniteCyclicDLP.KnownOrderProblem G)
    (B : OrderExpansion P.order) :
    (B.paddedPreparation P).applyNormalized
        (NormalizedVector.ket
          (R := Qubits (FiniteCyclicDLP.orderWidth P)) 0) =
      FiniteCyclicDLP.rangeUniformState P.order
        (FiniteCyclicDLP.orderWidth P) P.order_pos
        (FiniteCyclicDLP.order_le_fourierModulus P) := by
  unfold paddedPreparation
  split_ifs with positive
  · exact
      FiniteCyclicDLP.Canonical.GateLevelAttempt.paddedPreparation_apply_zero P
        (B.toBinaryExpansion positive)
  · have zero : B.s = 0 := by omega
    rw [UniformSuperposition.withCanonicalFootprint_applyNormalized]
    have sourceFit : P.order ≤ 2 ^ B.first := by
      exact (B.eq_pow_first_of_s_eq_zero zero).le
    have preparedPower := UniformSuperposition.padHigh_apply_zero
      (N := P.order) P.order_pos sourceFit
      (B.first_le_orderWidth_of_s_eq_zero P zero)
      (WalshHadamard.hadamardLayer B.first) (by
        simpa only [B.eq_pow_first_of_s_eq_zero zero] using
          hadamardLayer_apply_zero_uniformState B.first)
    exact preparedPower.trans
      (FiniteCyclicDLP.Canonical.GateLevelAttempt.uniformState_eq_rangeUniformState
        P.order (FiniteCyclicDLP.orderWidth P) P.order_pos
        (FiniteCyclicDLP.order_le_fourierModulus P))

/-- Every event outside the four elementary preparation coordinates has zero
multiplicity in the literal preparation circuit. -/
theorem paddedPreparation_count_zero_of_not_elementary
    {G : Type*} [Group G] (P : FiniteCyclicDLP.KnownOrderProblem G)
    (B : OrderExpansion P.order) (event : Resource.Event .quantum)
    (notElementary : ¬ UniformSuperposition.elementaryEvent event) :
    ResourcePool.count event (B.paddedPreparation P).eventCost = 0 := by
  unfold paddedPreparation
  split_ifs with positive
  · let source := B.toBinaryExpansion positive
    rw [FiniteCyclicDLP.Canonical.GateLevelAttempt.paddedPreparation,
      source.algorithm1CircuitPadded_eventCost]
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, ResourcePool.count_ofList,
      List.count_eq_zero]
    intro member
    exact notElementary
      ((List.forall_iff_forall_mem.mp source.algorithm1Circuit_elementary_trace)
        event member)
  · rw [UniformSuperposition.withCanonicalFootprint_eventCost,
      UniformSuperposition.padHigh_eventCost,
      WalshHadamard.hadamardLayer_eventCost]
    apply ResourcePool.count_singleton_of_ne
    intro equality
    apply notElementary
    exact Or.inl equality

/-- Aggregate one-qubit gates of the literal preparation obey the locked
formula in both the Algorithm-1 and one-term branches. -/
theorem paddedPreparation_singleQubitCost_le
    {G : Type*} [Group G] (P : FiniteCyclicDLP.KnownOrderProblem G)
    (B : OrderExpansion P.order) :
    UniformSuperposition.singleQubitCost (B.paddedPreparation P) ≤
      B.singleQubitBound := by
  unfold paddedPreparation
  split_ifs with positive
  · simpa only [FiniteCyclicDLP.Canonical.GateLevelAttempt.paddedPreparation,
      toBinaryExpansion_singleQubitBound] using
      (B.toBinaryExpansion positive).algorithm1CircuitPadded_single_qubit_bound
        (FiniteCyclicDLP.Canonical.GateLevelAttempt.binaryExpansion_width_le_orderWidth
          P (B.toBinaryExpansion positive))
  · have zero : B.s = 0 := by omega
    rw [UniformSuperposition.singleQubitCost_withCanonicalFootprint,
      UniformSuperposition.singleQubitCost_padHigh,
      UniformSuperposition.singleQubitCost]
    rw [WalshHadamard.hadamardLayer_eventCost,
      show WalshHadamard.hadamardEvent =
        (.gate (.builtin "hadamard") : Resource.Event .quantum) from rfl,
      UniformSuperposition.rotationYEvent_eq_gate,
      ResourcePool.count_singleton_self,
      ResourcePool.count_singleton_of_ne (by decide),
      ResourcePool.count_singleton_of_ne (by decide)]
    simp only [Nat.add_zero]
    have lastEq := B.last_eq_first_of_s_eq_zero zero
    unfold singleQubitBound
    omega

/-- Literal CNOTs of the same preparation obey the locked formula. -/
theorem paddedPreparation_cnotCost_le
    {G : Type*} [Group G] (P : FiniteCyclicDLP.KnownOrderProblem G)
    (B : OrderExpansion P.order) :
    UniformSuperposition.cnotCost (B.paddedPreparation P) ≤ B.cnotBound := by
  unfold paddedPreparation
  split_ifs with positive
  · simpa only [FiniteCyclicDLP.Canonical.GateLevelAttempt.paddedPreparation,
      toBinaryExpansion_cnotBound] using
      (B.toBinaryExpansion positive).algorithm1CircuitPadded_cnot_bound
        (FiniteCyclicDLP.Canonical.GateLevelAttempt.binaryExpansion_width_le_orderWidth
          P (B.toBinaryExpansion positive))
  · rw [UniformSuperposition.cnotCost_withCanonicalFootprint,
      UniformSuperposition.cnotCost_padHigh,
      UniformSuperposition.cnotCost]
    rw [WalshHadamard.hadamardLayer_eventCost,
      show WalshHadamard.hadamardEvent =
        (.gate (.builtin "hadamard") : Resource.Event .quantum) from rfl,
      UniformSuperposition.cnotEvent_eq_gate,
      ResourcePool.count_singleton_of_ne (by decide)]
    exact Nat.zero_le _

/-- The one-preparation circuit depth is the same locked expression in both
branches. -/
theorem paddedPreparation_depth_le
    {G : Type*} [Group G] (P : FiniteCyclicDLP.KnownOrderProblem G)
    (B : OrderExpansion P.order) :
    (B.paddedPreparation P).evaluatedEventDepth (fun _ => 1) ≤ B.depthBound := by
  unfold paddedPreparation
  split_ifs with positive
  · simpa only [FiniteCyclicDLP.Canonical.GateLevelAttempt.paddedPreparation,
      toBinaryExpansion_depthBound] using
      (B.toBinaryExpansion positive).algorithm1CircuitPadded_depth_bound
        (FiniteCyclicDLP.Canonical.GateLevelAttempt.binaryExpansion_width_le_orderWidth
          P (B.toBinaryExpansion positive))
  · have zero : B.s = 0 := by omega
    rw [UniformSuperposition.withCanonicalFootprint_evaluatedEventDepth,
      UniformSuperposition.padHigh_evaluatedEventDepth]
    change DepthExpr.depthEval (fun _ => 1)
      (WalshHadamard.hadamardLayer B.first).eventDepth ≤ _
    rw [WalshHadamard.hadamardLayer_eventDepth,
      WalshHadamard.parallelHadamardEventDepth_unit_depth]
    have lastEq := B.last_eq_first_of_s_eq_zero zero
    unfold depthBound
    split <;> omega

end OrderExpansion

end

end Canonical
end ECDLP
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
