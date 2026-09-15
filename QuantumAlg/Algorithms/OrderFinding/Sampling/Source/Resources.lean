/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Source
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Budget
import all QuantumAlg.Algorithms.OrderFinding.Construction
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Source preparation and unitary depth facts

These facts concern only the original source operations. They are independent
of retained classical input cells and the sampler execution context.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

private theorem preparation_value (t n : Nat) (index : Fin (t + n)) :
    ((inputPreparation t n).value index).val = 0 := by
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ (t + n))).val.testBit index.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

theorem inputPreparation_event (t n : Nat) :
    (inputPreparation t n).event = basisPreparationEvent t n := by
  have dimensions : (runtimeLayout t n).dimensions.map PNat.val =
      List.replicate (t + n) 2 := by
    change (List.ofFn (fun _ : Fin (t + n) => (2 : ℕ+))).map
      PNat.val = _
    rw [List.map_ofFn]
    exact List.ofFn_const (t + n) 2
  have values : List.ofFn (fun index => ((inputPreparation t n).value index).val) =
      List.replicate (t + n) 0 := by
    simp only [preparation_value, List.ofFn_const]
  change Resource.Event.preparation
    { family := "builtin", name := "computational-basis",
      parameters := (t + n) ::
        ((runtimeLayout t n).dimensions.map PNat.val ++
          List.ofFn (fun index => ((inputPreparation t n).value index).val)) } = _
  rw [dimensions, values]
  rfl

theorem preparation_depth (t n : Nat) :
    (orderFindingPreparationCircuit t n).evaluatedEventDepth (fun _ => 1) =
      if t = 0 then 0 else 1 := by
  simp only [orderFindingPreparationCircuit, UnitaryCircuit.evaluatedEventDepth_tensorQubits]
  change max (DepthExpr.depthEval (fun _ => 1)
    (WalshHadamard.hadamardLayer t).eventDepth) 0 = _
  rw [Nat.max_zero, WalshHadamard.hadamardLayer_eventDepth,
    WalshHadamard.parallelHadamardEventDepth_unit_depth]

theorem readout_depth (t n : Nat) :
    (orderFindingReadoutCircuit t n).evaluatedEventDepth (fun _ => 1) =
      t + t * (t - 1) / 2 + t / 2 := by
  simp only [orderFindingReadoutCircuit, UnitaryCircuit.evaluatedEventDepth_tensorQubits]
  change max ((UnitaryCircuit.dagger (QFTCircuit t)).evaluatedEventDepth (fun _ => 1)) 0 = _
  rw [Nat.max_zero, UnitaryCircuit.evaluatedEventDepth_dagger,
    QFTCircuit_evaluatedEventDepth_of_one]

end

end QuantumAlg.OrderFinding.Sampling
