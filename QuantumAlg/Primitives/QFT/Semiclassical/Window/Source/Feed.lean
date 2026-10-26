/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Ports
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Geometry
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import all QuantumAlg.Core.Base.Gate.Effect.Unitary

/-!
# Mathematical source coordinates for one genuinely recycled bank

The virtual source is only an input space for a positive observable. The
permutation below exchanges its current mathematical block with the existing
physical bank and preserves all other coordinates. It is not Circuit syntax,
an executed free permutation, an allocation, or a resource claim. Uniform
source amplitudes are identified explicitly on these same coordinates.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open NormalizedVector

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

private abbrev Remainder (ports : Ports ctx totalBits active) (Reference : Register) :=
  ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection × Reference.Index

/-- Exchange only the two mathematical active-block coordinates, retaining every other index. -/
def feedBasis (ports : Ports ctx totalBits active) (Reference : Register)
    (row : (ctx.register.prod ((Qubits active).prod Reference)).Index) :
    (ctx.register.prod ((Qubits active).prod Reference)).Index :=
  let physical := bankCoordinates ports.wires ports.qubits row.1
  ((bankCoordinates ports.wires ports.qubits).symm
      ((binaryEquiv active).symm row.2.1, physical.2),
    (binaryEquiv active physical.1, row.2.2))

lemma window_sourceFeed_involutive (ports : Ports ctx totalBits active) (Reference : Register) :
    Function.Involutive (feedBasis ports Reference) := by
  rintro ⟨physical, virtual, reference⟩
  simp only [feedBasis, Equiv.apply_symm_apply, Equiv.symm_apply_apply, Prod.eta]

def feedEquiv (ports : Ports ctx totalBits active) (Reference : Register) :
    Equiv.Perm (ctx.register.prod ((Qubits active).prod Reference)).Index :=
  (window_sourceFeed_involutive ports Reference).toPerm (feedBasis ports Reference)

/-- A mathematical permutation operator on the source observation space, never a circuit. -/
def feedOperator (ports : Ports ctx totalBits active) (Reference : Register) :
    UnitaryOperator (ctx.register.prod ((Qubits active).prod Reference)) :=
  UnitaryOperator.ofPerm (feedEquiv ports Reference)

lemma window_sourceFeed_bank (ports : Ports ctx totalBits active) (Reference : Register)
    (row : (ctx.register.prod ((Qubits active).prod Reference)).Index) :
    bankCoordinates ports.wires ports.qubits (feedBasis ports Reference row).1 =
      ((binaryEquiv active).symm row.2.1,
        (bankCoordinates ports.wires ports.qubits row.1).2) :=
  (bankCoordinates ports.wires ports.qubits).apply_symm_apply _

lemma window_sourceFeed_reference (ports : Ports ctx totalBits active) (Reference : Register)
    (row : (ctx.register.prod ((Qubits active).prod Reference)).Index) :
    (feedBasis ports Reference row).2.2 = row.2.2 := rfl

/-- Zero physical bank and a uniform mathematical source block, with arbitrary saved amplitudes. -/
def uniformSourceInput (ports : Ports ctx totalBits active) (Reference : Register)
    (saved : Remainder ports Reference → Complex) :
    HilbertVector (ctx.register.prod ((Qubits active).prod Reference)) :=
  WithLp.toLp 2 fun row =>
    if (bankCoordinates ports.wires ports.qubits row.1).1 = Partner.zeroBits active then
      invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits row.1).2, row.2.2)
    else 0

/-- After feeding, the same selected physical bank is uniform and the consumed source is zero. -/
def uniformBankOutput (ports : Ports ctx totalBits active) (Reference : Register)
    (saved : Remainder ports Reference → Complex) :
    HilbertVector (ctx.register.prod ((Qubits active).prod Reference)) :=
  WithLp.toLp 2 fun row =>
    if row.2.1 = binaryEquiv active (Partner.zeroBits active) then
      invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits row.1).2, row.2.2)
    else 0

/-- Exact uniform-source feed identity on the full complement and arbitrary Reference amplitudes. -/
lemma window_sourceFeed_uniform (ports : Ports ctx totalBits active) (Reference : Register)
    (saved : Remainder ports Reference → Complex) :
    (feedOperator ports Reference).applyVec (uniformSourceInput ports Reference saved) =
      uniformBankOutput ports Reference saved := by
  ext row
  rw [feedOperator, UnitaryOperator.ofPerm_applyVec]
  change (if (bankCoordinates ports.wires ports.qubits (feedBasis ports Reference row).1).1 =
      Partner.zeroBits active then
    invSqrt2 ^ active * saved
      ((bankCoordinates ports.wires ports.qubits (feedBasis ports Reference row).1).2,
        (feedBasis ports Reference row).2.2) else 0) = _
  rw [window_sourceFeed_bank, window_sourceFeed_reference]
  change (if (binaryEquiv active).symm row.2.1 = Partner.zeroBits active then
    invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits row.1).2, row.2.2)
      else 0) = _
  have same : ((binaryEquiv active).symm row.2.1 = Partner.zeroBits active) ↔
      row.2.1 = binaryEquiv active (Partner.zeroBits active) := by
    constructor
    · intro equal
      exact ((binaryEquiv active).apply_symm_apply row.2.1).symm.trans
        (congrArg (binaryEquiv active) equal)
    · intro equal
      exact (congrArg (binaryEquiv active).symm equal).trans
        ((binaryEquiv active).symm_apply_apply (Partner.zeroBits active))
  by_cases selected : row.2.1 = binaryEquiv active (Partner.zeroBits active)
  · simp only [uniformBankOutput, if_pos selected, if_pos (same.mpr selected)]
  · simp only [uniformBankOutput, if_neg selected,
      if_neg (fun equal => selected (same.mp equal))]

/-- Every final positive contraction gives a positive contraction on the full virtual source. -/
def feedObservation (ports : Ports ctx totalBits active) (Reference : Register)
    (effect : Effect (ctx.register.prod ((Qubits active).prod Reference))) :
    Effect (ctx.register.prod ((Qubits active).prod Reference)) :=
  Effect.pullbackUnitary (feedOperator ports Reference) effect

lemma window_sourceFeed_observation_weight (ports : Ports ctx totalBits active)
    (Reference : Register) (effect : Effect (ctx.register.prod ((Qubits active).prod Reference)))
    (density : DensityOperator (ctx.register.prod ((Qubits active).prod Reference))) :
    (feedObservation ports Reference effect).weight density =
      effect.weight (DensityOperator.applyUnitary (feedOperator ports Reference) density) :=
  Effect.weight_pullbackUnitary (feedOperator ports Reference) effect density

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
