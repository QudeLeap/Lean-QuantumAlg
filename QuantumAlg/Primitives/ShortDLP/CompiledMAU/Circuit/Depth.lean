/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Resources

/-!
# Independent duration envelope of the complete short-DLP member

Parallel preparation and parallel inverse-QFT readout retain the source
register organization. Independent serial native budgets surround the
actual shared arithmetic sequence. All duration bounds apply to every
natural-number event assignment and preserve the original event labels.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- The independent parallel-Hadamard preparation schedule. -/
def preparationDepthEnvelope (m ell : Nat) : DepthExpr (Resource.Event .quantum) :=
  .tensor
    (.tensor (WalshHadamard.parallelHadamardEventDepth (ell + m))
      (WalshHadamard.parallelHadamardEventDepth ell)) .id

/-- Independent serial envelope for the native H, controlled phase, and swap occurrences. -/
def qftDepthEnvelope (bits : Nat) : DepthExpr (Resource.Event .quantum) :=
  .seq (.seq (.iterate bits (.atom (.gate (.builtin "hadamard"))))
      (.iterate (bits.choose 2) (.atom (.gate qftControlledPhaseLabel))))
    (.iterate (bits / 2) (.atom (.gate (.builtin "swap"))))

theorem qftDepthEnvelope_eval (bits : Nat) (assignment : Resource.Event .quantum → Nat) :
    DepthExpr.depthEval assignment (qftDepthEnvelope bits) =
      ResourcePool.weightedCount assignment (qftEventEnvelope bits) := by
  simp only [qftDepthEnvelope, DepthExpr.depthEval_seq, DepthExpr.depthEval_iterate,
    DepthExpr.depthEval_atom, qftEventEnvelope, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton, Nat.one_mul]

theorem QFTCircuit_eventDepth_le_envelope (bits : Nat)
    (assignment : Resource.Event .quantum → Nat) :
    DepthExpr.depthEval assignment (QFTCircuit bits).eventDepth ≤
      DepthExpr.depthEval assignment (qftDepthEnvelope bits) := by
  rw [qftDepthEnvelope_eval]
  apply DepthExpr.depthEval_le_weightedCount_of_eventPool_le
  change (QFTCircuit bits).resourcesFromEventDepth ≤ _
  exact le_of_eq ((UnitaryCircuit.resourcesFromEventDepth_eq_eventCost _).trans
    (QFTCircuit_eventCost_eq_envelope bits))

@[simp] theorem qftDepthEnvelope_unit (bits : Nat) :
    DepthExpr.depthEval (fun _ => 1) (qftDepthEnvelope bits) = qftPrimitiveBound bits := by
  simp only [qftDepthEnvelope, DepthExpr.depthEval_seq, DepthExpr.depthEval_iterate,
    DepthExpr.depthEval_atom, Nat.mul_one, Nat.choose_two_right, qftPrimitiveBound]

/-- The two readout envelopes run on the disjoint exponent words. -/
def readoutDepthEnvelope (m ell : Nat) : DepthExpr (Resource.Event .quantum) :=
  .tensor (.tensor (.inverse (qftDepthEnvelope (ell + m)))
    (.inverse (qftDepthEnvelope ell))) .id

theorem preparationCircuit_eventDepth_eq_envelope (m ell width : Nat) :
    (preparationCircuit (registerParameters m ell width)).eventDepth =
      preparationDepthEnvelope m ell := by
  rw [preparationCircuit_eventDepth]
  rfl

theorem readoutCircuit_eventDepth_le_envelope (m ell width : Nat)
    (assignment : Resource.Event .quantum → Nat) :
    DepthExpr.depthEval assignment
        (readoutCircuit (registerParameters m ell width)).eventDepth ≤
      DepthExpr.depthEval assignment (readoutDepthEnvelope m ell) := by
  rw [readoutCircuit_eventDepth]
  simp only [readoutDepthEnvelope, DepthExpr.depthEval_tensor, DepthExpr.depthEval_inverse,
    DepthExpr.depthEval_id, max_zero]
  exact max_le_max (QFTCircuit_eventDepth_le_envelope (ell + m) assignment)
    (QFTCircuit_eventDepth_le_envelope ell assignment)

/-- Independent complete member envelope with source preparation/readout parallelism. -/
def compiledCircuitDepthEnvelope (m ell width N : Nat) : DepthExpr (Resource.Event .quantum) :=
  .seq (preparationDepthEnvelope m ell)
    (.seq (compiledGroupActionDepthEnvelope m ell width N) (readoutDepthEnvelope m ell))

theorem compiledCircuit_eventDepth_le (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (assignment : Resource.Event .quantum → Nat) :
    DepthExpr.depthEval assignment (compiledCircuit m ell width N g x).eventDepth ≤
      DepthExpr.depthEval assignment (compiledCircuitDepthEnvelope m ell width N) := by
  rw [compiledCircuit, UnitaryCircuit.seq_eventDepth, UnitaryCircuit.seq_eventDepth,
    preparationCircuit_eventDepth_eq_envelope, compiledCircuitDepthEnvelope]
  simp only [DepthExpr.depthEval_seq]
  exact Nat.add_le_add_left
    (Nat.add_le_add (compiledGroupActionProgram_eventDepth_le m ell width N g x assignment)
      (readoutCircuit_eventDepth_le_envelope m ell width assignment)) _

/-- Closed unit-duration value of the independently capped complete member envelope. -/
def compiledCircuitEventUnitDepth (m ell width N : Nat) : Nat :=
  max (if ell + m = 0 then 0 else 1) (if ell = 0 then 0 else 1) +
    (groupActionPrimitiveBound m ell width N +
      max (qftUnitDepth (ell + m)) (qftUnitDepth ell))

/-- Modulus-independent envelope ceiling with the same preparation/readout parallelism. -/
def compiledCircuitEventUnitDepthWidthBound (m ell width : Nat) : Nat :=
  max (if ell + m = 0 then 0 else 1) (if ell = 0 then 0 else 1) +
    (groupActionPrimitiveWidthBound m ell width +
      max (qftUnitDepth (ell + m)) (qftUnitDepth ell))

theorem compiledCircuitDepthEnvelope_unit (m ell width N : Nat) :
    DepthExpr.depthEval (fun _ => 1) (compiledCircuitDepthEnvelope m ell width N) =
      compiledCircuitEventUnitDepth m ell width N := by
  simp only [compiledCircuitDepthEnvelope, DepthExpr.depthEval_seq,
    preparationDepthEnvelope, readoutDepthEnvelope, DepthExpr.depthEval_tensor,
    DepthExpr.depthEval_inverse, DepthExpr.depthEval_id, max_zero,
    WalshHadamard.parallelHadamardEventDepth_unit_depth,
    compiledGroupActionDepthEnvelope_unit, qftDepthEnvelope_unit]
  rfl

theorem compiledCircuitEventUnitDepth_le_widthBound (m ell width N : Nat) :
    compiledCircuitEventUnitDepth m ell width N ≤
      compiledCircuitEventUnitDepthWidthBound m ell width := by
  exact Nat.add_le_add_left
    (Nat.add_le_add_right (groupActionPrimitiveBound_le_widthBound m ell width N) _) _

theorem compiledCircuitEventUnitDepth_le_polynomial (m ell width N : Nat) :
    compiledCircuitEventUnitDepth m ell width N ≤ polynomialPrimitiveBound m ell width N := by
  have preparation :
      max (if ell + m = 0 then 0 else 1) (if ell = 0 then 0 else 1) ≤ m + 2 * ell := by
    by_cases hm : m = 0 <;> by_cases hell : ell = 0 <;> simp [hm, hell] <;> omega
  have readout : max (qftUnitDepth (ell + m)) (qftUnitDepth ell) ≤
      qftPrimitiveBound (m + ell) + qftPrimitiveBound ell := by
    change max (qftPrimitiveBound (ell + m)) (qftPrimitiveBound ell) ≤ _
    rw [Nat.add_comm ell m]
    exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  unfold compiledCircuitEventUnitDepth polynomialPrimitiveBound
  omega

theorem compiledCircuit_eventUnitDepth_le (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledCircuit m ell width N g x).evaluatedEventDepth (fun _ => 1) ≤
      compiledCircuitEventUnitDepth m ell width N :=
  (compiledCircuit_eventDepth_le m ell width N g x (fun _ => 1)).trans_eq
    (compiledCircuitDepthEnvelope_unit m ell width N)

/-- Tighter actual depth ceiling, using total occurrences instead of independent coordinate caps. -/
def compiledCircuitActualDepthBound (m ell width : Nat) : Nat :=
  max (if ell + m = 0 then 0 else 1) (if ell = 0 then 0 else 1) +
    (groupActionActualEventBound m ell width +
      max (qftUnitDepth (ell + m)) (qftUnitDepth ell))

theorem compiledCircuit_actual_depth_bound (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledCircuit m ell width N g x).evaluatedEventDepth (fun _ => 1) ≤
      compiledCircuitActualDepthBound m ell width := by
  have group := compiledGroupActionProgram_actual_depth_bound m ell width N g x
  have readout := readoutCircuit_eventDepth_le_envelope m ell width (fun _ => 1)
  change DepthExpr.depthEval (fun _ => 1)
    (compiledCircuit m ell width N g x).eventDepth ≤ _
  rw [compiledCircuit, UnitaryCircuit.seq_eventDepth, UnitaryCircuit.seq_eventDepth,
    preparationCircuit_eventDepth_eq_envelope]
  simp only [DepthExpr.depthEval_seq, preparationDepthEnvelope, DepthExpr.depthEval_tensor,
    DepthExpr.depthEval_id, max_zero, WalshHadamard.parallelHadamardEventDepth_unit_depth]
  unfold compiledCircuitActualDepthBound
  apply Nat.add_le_add_left
  apply Nat.add_le_add group
  have qftFirst : qftPrimitiveBound (ell + m) = qftUnitDepth (ell + m) := rfl
  have qftSecond : qftPrimitiveBound ell = qftUnitDepth ell := rfl
  simpa only [readoutDepthEnvelope, DepthExpr.depthEval_tensor, DepthExpr.depthEval_inverse,
    DepthExpr.depthEval_id, max_zero, qftDepthEnvelope_unit, qftFirst, qftSecond] using readout

end

end QuantumAlg.ShortDLP.CompiledMAU
