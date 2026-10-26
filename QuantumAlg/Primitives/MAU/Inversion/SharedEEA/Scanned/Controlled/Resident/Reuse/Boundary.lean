/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Reuse.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Reuse

/-!
# Actual post-reset readouts identify the full reused adjoint boundary

The physical A value is independent of the inverse input. Every original
bit outside its payload, the entire pool and all C/N/W systems must be
retained, and Y must actually be zero. These complete premises identify
the exact same forward's result, including all finite source history.
The literal reused adjoint can then consume that physical boundary.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentReuse

noncomputable section

/-- Actual complete physical readouts identify the same forward's whole reused result. -/
lemma result_of_saved_reset (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) (state : ControlledResidentFrame.Data modulus.size)
    (retained : ∀ bit : EncodedBit (SharedEEA.encoding modulus.size),
      modulus.size ≤ bit.wire.val → bit.get state.1.1.1 =
        bit.get (ControlledResident.result modulus input positive bounded 0 pool flags).1.1.1)
    (poolSame : state.1.1.2 = pool) (reset : state.1.2 = 0) (flagsSame : state.2 = flags) :
    state = result modulus input positive bounded
      (WorkspaceReuse.reverseWord (WorkspaceReuse.largeWord state.1)) pool flags := by
  have grouped := WorkspaceReuse.grouping_saved_reset modulus.size
    (ControlledResident.result modulus input positive bounded 0 pool flags).1.1 state.1
    (ControlledResident.result_large_bit modulus input coprime positive bounded 0 pool flags)
    retained poolSame reset
  apply (layout modulus.size).grouping.injective
  rw [result, Equiv.apply_symm_apply]
  change ((WorkspaceReuse.placement modulus.size).grouping state.1, state.2) = _
  rw [grouped, flagsSame]
  rfl

/-- The literal same-program adjoint applies once the actual reset and full retention are proved. -/
lemma backward_saved_reset (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : ControlledResidentFrame.Flags) (selected : flags.2.1 = true)
    (state : ControlledResidentFrame.Data modulus.size)
    (retained : ∀ bit : EncodedBit (SharedEEA.encoding modulus.size),
      modulus.size ≤ bit.wire.val → bit.get state.1.1.1 =
        bit.get (ControlledResident.result modulus input positive bounded 0 pool flags).1.1.1)
    (poolSame : state.1.1.2 = pool) (reset : state.1.2 = 0) (flagsSame : state.2 = flags) :
    (backward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode
          (initial modulus input (WorkspaceReuse.reverseWord (WorkspaceReuse.largeWord state.1))
            pool flags))) := by
  have same := result_of_saved_reset modulus input coprime positive bounded pool flags state
    retained poolSame reset flagsSame
  have actual := backward_result modulus nontrivial environment input
    (WorkspaceReuse.reverseWord (WorkspaceReuse.largeWord state.1)) coprime positive bounded
    pool addressZero prefixZero borrowZero flags selected
  exact (congrArg (fun value => (backward modulus nontrivial).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledResidentFrame.encoding modulus.size).encode value)))) same).trans actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentReuse
