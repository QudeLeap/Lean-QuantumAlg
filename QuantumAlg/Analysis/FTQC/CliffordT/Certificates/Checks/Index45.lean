/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word45Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word45State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word45Step0 :
    word45Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word45State1 := by decide +kernel

private def word45Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .h]
private def word45State2 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word45Step1 :
    word45Chunk1.foldl (fun acc a => a.applyPacked acc)
      word45State1 = word45State2 := by decide +kernel

private def word45Chunk2 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word45State3 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word45Step2 :
    word45Chunk2.foldl (fun acc a => a.applyPacked acc)
      word45State2 = word45State3 := by decide +kernel

private def word45Chunk3 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word45State4 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word45Step3 :
    word45Chunk3.foldl (fun acc a => a.applyPacked acc)
      word45State3 = word45State4 := by decide +kernel

private def word45Chunk4 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word45State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((7 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word45Step4 :
    word45Chunk4.foldl (fun acc a => a.applyPacked acc)
      word45State4 = word45State5 := by decide +kernel

private def word45Chunk5 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word45State6 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-11 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((11 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word45Step5 :
    word45Chunk5.foldl (fun acc a => a.applyPacked acc)
      word45State5 = word45State6 := by decide +kernel

private def word45Chunk6 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word45State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((13 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((23 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-23 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-13 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word45Step6 :
    word45Chunk6.foldl (fun acc a => a.applyPacked acc)
      word45State6 = word45State7 := by decide +kernel

private def word45Chunk7 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word45State8 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((15 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-9 : Dyadic) * half ^ 5)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((21 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((15 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word45Step7 :
    word45Chunk7.foldl (fun acc a => a.applyPacked acc)
      word45State7 = word45State8 := by decide +kernel

private def word45Chunk8 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State9 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 6),
        ((-47 : Dyadic) * half ^ 7)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((7 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-27 : Dyadic) * half ^ 7)⟩,
       ⟨((-1 : Dyadic) * half ^ 6),
        ((55 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 7)⟩,
       ⟨((-41 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((-31 : Dyadic) * half ^ 7)⟩,
       ⟨((27 : Dyadic) * half ^ 6),
        ((33 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word45Step8 :
    word45Chunk8.foldl (fun acc a => a.applyPacked acc)
      word45State8 = word45State9 := by decide +kernel

private def word45Chunk9 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word45State10 : PackedMat2 :=
    ⟨⟨⟨((-93 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((47 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-23 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((23 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-93 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-47 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word45Step9 :
    word45Chunk9.foldl (fun acc a => a.applyPacked acc)
      word45State9 = word45State10 := by decide +kernel

private def word45Chunk10 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word45State11 : PackedMat2 :=
    ⟨⟨⟨((55 : Dyadic) * half ^ 8),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((143 : Dyadic) * half ^ 8),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-43 : Dyadic) * half ^ 7),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((-93 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-115 : Dyadic) * half ^ 8),
        ((-87 : Dyadic) * half ^ 8)⟩,
       ⟨((71 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 6),
        ((-99 : Dyadic) * half ^ 8)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word45Step10 :
    word45Chunk10.foldl (fun acc a => a.applyPacked acc)
      word45State10 = word45State11 := by decide +kernel

private def word45Chunk11 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word45State12 : PackedMat2 :=
    ⟨⟨⟨((-243 : Dyadic) * half ^ 9),
        ((69 : Dyadic) * half ^ 8)⟩,
       ⟨((43 : Dyadic) * half ^ 9),
        ((-127 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-73 : Dyadic) * half ^ 9),
        ((-15 : Dyadic) * half ^ 7)⟩,
       ⟨((-161 : Dyadic) * half ^ 9),
        ((-215 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-155 : Dyadic) * half ^ 9),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((-275 : Dyadic) * half ^ 9),
        ((-117 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((265 : Dyadic) * half ^ 9),
        ((-143 : Dyadic) * half ^ 9)⟩,
       ⟨((-11 : Dyadic) * half ^ 9),
        ((25 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word45Step11 :
    word45Chunk11.foldl (fun acc a => a.applyPacked acc)
      word45State11 = word45State12 := by decide +kernel

private def word45Chunk12 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word45State13 : PackedMat2 :=
    ⟨⟨⟨((49 : Dyadic) * half ^ 10),
        ((57 : Dyadic) * half ^ 9)⟩,
       ⟨((-253 : Dyadic) * half ^ 10),
        ((-529 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((401 : Dyadic) * half ^ 10),
        ((-79 : Dyadic) * half ^ 8)⟩,
       ⟨((-131 : Dyadic) * half ^ 10),
        ((97 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((401 : Dyadic) * half ^ 10),
        ((-79 : Dyadic) * half ^ 8)⟩,
       ⟨((131 : Dyadic) * half ^ 10),
        ((-97 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-49 : Dyadic) * half ^ 10),
        ((-57 : Dyadic) * half ^ 9)⟩,
       ⟨((-253 : Dyadic) * half ^ 10),
        ((-529 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word45Step12 :
    word45Chunk12.foldl (fun acc a => a.applyPacked acc)
      word45State12 = word45State13 := by decide +kernel

private def word45Chunk13 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word45State14 : PackedMat2 :=
    ⟨⟨⟨((39 : Dyadic) * half ^ 6),
        ((125 : Dyadic) * half ^ 10)⟩,
       ⟨((9 : Dyadic) * half ^ 10),
        ((111 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-183 : Dyadic) * half ^ 9),
        ((371 : Dyadic) * half ^ 11)⟩,
       ⟨((15 : Dyadic) * half ^ 9),
        ((-807 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-589 : Dyadic) * half ^ 10),
        ((99 : Dyadic) * half ^ 9)⟩,
       ⟨((-109 : Dyadic) * half ^ 9),
        ((-21 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-97 : Dyadic) * half ^ 10),
        ((615 : Dyadic) * half ^ 11)⟩,
       ⟨((-347 : Dyadic) * half ^ 10),
        ((-633 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word45Step13 :
    word45Chunk13.foldl (fun acc a => a.applyPacked acc)
      word45State13 = word45State14 := by decide +kernel

private def word45Chunk14 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word45State15 : PackedMat2 :=
    ⟨⟨⟨((-125 : Dyadic) * half ^ 11),
        ((1175 : Dyadic) * half ^ 12)⟩,
       ⟨((519 : Dyadic) * half ^ 10),
        ((1075 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-283 : Dyadic) * half ^ 11),
        ((-175 : Dyadic) * half ^ 12)⟩,
       ⟨((-291 : Dyadic) * half ^ 9),
        ((875 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((291 : Dyadic) * half ^ 9),
        ((-875 : Dyadic) * half ^ 12)⟩,
       ⟨((283 : Dyadic) * half ^ 11),
        ((175 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((519 : Dyadic) * half ^ 10),
        ((1075 : Dyadic) * half ^ 12)⟩,
       ⟨((-125 : Dyadic) * half ^ 11),
        ((1175 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word45Step14 :
    word45Chunk14.foldl (fun acc a => a.applyPacked acc)
      word45State14 = word45State15 := by decide +kernel

private def word45Chunk15 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word45State16 : PackedMat2 :=
    ⟨⟨⟨((331 : Dyadic) * half ^ 11),
        ((-1103 : Dyadic) * half ^ 12)⟩,
       ⟨((325 : Dyadic) * half ^ 10),
        ((451 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1039 : Dyadic) * half ^ 12),
        ((-651 : Dyadic) * half ^ 11)⟩,
       ⟨((-533 : Dyadic) * half ^ 12),
        ((-427 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((1039 : Dyadic) * half ^ 12),
        ((-651 : Dyadic) * half ^ 11)⟩,
       ⟨((533 : Dyadic) * half ^ 12),
        ((427 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-331 : Dyadic) * half ^ 11),
        ((1103 : Dyadic) * half ^ 12)⟩,
       ⟨((325 : Dyadic) * half ^ 10),
        ((451 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word45Step15 :
    word45Chunk15.foldl (fun acc a => a.applyPacked acc)
      word45State15 = word45State16 := by decide +kernel

private def word45Chunk16 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word45State17 : PackedMat2 :=
    ⟨⟨⟨((-337 : Dyadic) * half ^ 13),
        ((-239 : Dyadic) * half ^ 9)⟩,
       ⟨((-767 : Dyadic) * half ^ 13),
        ((941 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-73 : Dyadic) * half ^ 10),
        ((-685 : Dyadic) * half ^ 13)⟩,
       ⟨((317 : Dyadic) * half ^ 12),
        ((945 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1205 : Dyadic) * half ^ 13),
        ((-25 : Dyadic) * half ^ 13)⟩,
       ⟨((2575 : Dyadic) * half ^ 13),
        ((609 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 11),
        ((-69 : Dyadic) * half ^ 10)⟩,
       ⟨((-1897 : Dyadic) * half ^ 11),
        ((215 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word45Step16 :
    word45Chunk16.foldl (fun acc a => a.applyPacked acc)
      word45State16 = word45State17 := by decide +kernel

private def word45Chunk17 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word45State18 : PackedMat2 :=
    ⟨⟨⟨((-7465 : Dyadic) * half ^ 14),
        ((-2393 : Dyadic) * half ^ 13)⟩,
       ⟨((6557 : Dyadic) * half ^ 14),
        ((-6481 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1667 : Dyadic) * half ^ 14),
        ((675 : Dyadic) * half ^ 13)⟩,
       ⟨((2429 : Dyadic) * half ^ 14),
        ((3713 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1667 : Dyadic) * half ^ 14),
        ((675 : Dyadic) * half ^ 13)⟩,
       ⟨((-2429 : Dyadic) * half ^ 14),
        ((-3713 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((7465 : Dyadic) * half ^ 14),
        ((2393 : Dyadic) * half ^ 13)⟩,
       ⟨((6557 : Dyadic) * half ^ 14),
        ((-6481 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word45Step17 :
    word45Chunk17.foldl (fun acc a => a.applyPacked acc)
      word45State17 = word45State18 := by decide +kernel

private def word45Chunk18 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word45State19 : PackedMat2 :=
    ⟨⟨⟨((117 : Dyadic) * half ^ 12),
        ((2803 : Dyadic) * half ^ 14)⟩,
       ⟨((-13859 : Dyadic) * half ^ 14),
        ((-309 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1085 : Dyadic) * half ^ 13),
        ((-2325 : Dyadic) * half ^ 15)⟩,
       ⟨((1881 : Dyadic) * half ^ 13),
        ((-8463 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-3069 : Dyadic) * half ^ 14),
        ((199 : Dyadic) * half ^ 12)⟩,
       ⟨((-2697 : Dyadic) * half ^ 13),
        ((1483 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((4039 : Dyadic) * half ^ 14),
        ((14327 : Dyadic) * half ^ 15)⟩,
       ⟨((-1567 : Dyadic) * half ^ 14),
        ((13391 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word45Step18 :
    word45Chunk18.foldl (fun acc a => a.applyPacked acc)
      word45State18 = word45State19 := by decide +kernel

private def word45Chunk19 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word45State20 : PackedMat2 :=
    ⟨⟨⟨((23227 : Dyadic) * half ^ 15),
        ((-5055 : Dyadic) * half ^ 16)⟩,
       ⟨((83 : Dyadic) * half ^ 14),
        ((-24437 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((1943 : Dyadic) * half ^ 13),
        ((15275 : Dyadic) * half ^ 16)⟩,
       ⟨((-6761 : Dyadic) * half ^ 15),
        ((-407 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((6761 : Dyadic) * half ^ 15),
        ((407 : Dyadic) * half ^ 16)⟩,
       ⟨((-1943 : Dyadic) * half ^ 13),
        ((-15275 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((83 : Dyadic) * half ^ 14),
        ((-24437 : Dyadic) * half ^ 16)⟩,
       ⟨((23227 : Dyadic) * half ^ 15),
        ((-5055 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word45Step19 :
    word45Chunk19.foldl (fun acc a => a.applyPacked acc)
      word45State19 = word45State20 := by decide +kernel

private def word45Chunk20 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word45State21 : PackedMat2 :=
    ⟨⟨⟨((655 : Dyadic) * half ^ 14),
        ((5339 : Dyadic) * half ^ 13)⟩,
       ⟨((-2161 : Dyadic) * half ^ 14),
        ((-2867 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((12345 : Dyadic) * half ^ 16),
        ((-3555 : Dyadic) * half ^ 16)⟩,
       ⟨((-7381 : Dyadic) * half ^ 16),
        ((12573 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((12345 : Dyadic) * half ^ 16),
        ((-3555 : Dyadic) * half ^ 16)⟩,
       ⟨((7381 : Dyadic) * half ^ 16),
        ((-12573 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-655 : Dyadic) * half ^ 14),
        ((-5339 : Dyadic) * half ^ 13)⟩,
       ⟨((-2161 : Dyadic) * half ^ 14),
        ((-2867 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word45Step20 :
    word45Chunk20.foldl (fun acc a => a.applyPacked acc)
      word45State20 = word45State21 := by decide +kernel

private def word45Chunk21 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State22 : PackedMat2 :=
    ⟨⟨⟨((106413 : Dyadic) * half ^ 17),
        ((483 : Dyadic) * half ^ 15)⟩,
       ⟨((4267 : Dyadic) * half ^ 17),
        ((21495 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-2349 : Dyadic) * half ^ 17),
        ((-10735 : Dyadic) * half ^ 15)⟩,
       ⟨((28847 : Dyadic) * half ^ 17),
        ((-13803 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((29137 : Dyadic) * half ^ 17),
        ((7799 : Dyadic) * half ^ 16)⟩,
       ⟨((-56743 : Dyadic) * half ^ 17),
        ((13249 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-19563 : Dyadic) * half ^ 17),
        ((51073 : Dyadic) * half ^ 17)⟩,
       ⟨((-23427 : Dyadic) * half ^ 17),
        ((-13835 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word45Step21 :
    word45Chunk21.foldl (fun acc a => a.applyPacked acc)
      word45State21 = word45State22 := by decide +kernel

private def word45Chunk22 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word45State23 : PackedMat2 :=
    ⟨⟨⟨((37989 : Dyadic) * half ^ 18),
        ((10189 : Dyadic) * half ^ 15)⟩,
       ⟨((-49985 : Dyadic) * half ^ 18),
        ((19639 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((163043 : Dyadic) * half ^ 18),
        ((-26389 : Dyadic) * half ^ 17)⟩,
       ⟨((-88881 : Dyadic) * half ^ 18),
        ((-73021 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((163043 : Dyadic) * half ^ 18),
        ((-26389 : Dyadic) * half ^ 17)⟩,
       ⟨((88881 : Dyadic) * half ^ 18),
        ((73021 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-37989 : Dyadic) * half ^ 18),
        ((-10189 : Dyadic) * half ^ 15)⟩,
       ⟨((-49985 : Dyadic) * half ^ 18),
        ((19639 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word45Step22 :
    word45Chunk22.foldl (fun acc a => a.applyPacked acc)
      word45State22 = word45State23 := by decide +kernel

private def word45Chunk23 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word45State24 : PackedMat2 :=
    ⟨⟨⟨((43605 : Dyadic) * half ^ 18),
        ((55431 : Dyadic) * half ^ 19)⟩,
       ⟨((48755 : Dyadic) * half ^ 18),
        ((157489 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-58913 : Dyadic) * half ^ 18),
        ((121031 : Dyadic) * half ^ 18)⟩,
       ⟨((-5609 : Dyadic) * half ^ 16),
        ((-92823 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-5609 : Dyadic) * half ^ 16),
        ((-92823 : Dyadic) * half ^ 18)⟩,
       ⟨((-58913 : Dyadic) * half ^ 18),
        ((121031 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-48755 : Dyadic) * half ^ 18),
        ((-157489 : Dyadic) * half ^ 19)⟩,
       ⟨((-43605 : Dyadic) * half ^ 18),
        ((-55431 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word45Step23 :
    word45Chunk23.foldl (fun acc a => a.applyPacked acc)
      word45State23 = word45State24 := by decide +kernel

private def word45Chunk24 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word45State25 : PackedMat2 :=
    ⟨⟨⟨((-115181 : Dyadic) * half ^ 19),
        ((-299419 : Dyadic) * half ^ 20)⟩,
       ⟨((78791 : Dyadic) * half ^ 17),
        ((-46175 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((188743 : Dyadic) * half ^ 19),
        ((-185253 : Dyadic) * half ^ 20)⟩,
       ⟨((5345 : Dyadic) * half ^ 16),
        ((351509 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-5345 : Dyadic) * half ^ 16),
        ((-351509 : Dyadic) * half ^ 20)⟩,
       ⟨((-188743 : Dyadic) * half ^ 19),
        ((185253 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((78791 : Dyadic) * half ^ 17),
        ((-46175 : Dyadic) * half ^ 20)⟩,
       ⟨((-115181 : Dyadic) * half ^ 19),
        ((-299419 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word45Step24 :
    word45Chunk24.foldl (fun acc a => a.applyPacked acc)
      word45State24 = word45State25 := by decide +kernel

private def word45Chunk25 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word45State26 : PackedMat2 :=
    ⟨⟨⟨((-173101 : Dyadic) * half ^ 19),
        ((-165085 : Dyadic) * half ^ 20)⟩,
       ⟨((-19557 : Dyadic) * half ^ 18),
        ((140603 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-354635 : Dyadic) * half ^ 20),
        ((-25273 : Dyadic) * half ^ 17)⟩,
       ⟨((713049 : Dyadic) * half ^ 20),
        ((-74929 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-176021 : Dyadic) * half ^ 19),
        ((179207 : Dyadic) * half ^ 20)⟩,
       ⟨((-26163 : Dyadic) * half ^ 19),
        ((-266921 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-116121 : Dyadic) * half ^ 20),
        ((212215 : Dyadic) * half ^ 20)⟩,
       ⟨((446291 : Dyadic) * half ^ 20),
        ((133987 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word45Step25 :
    word45Chunk25.foldl (fun acc a => a.applyPacked acc)
      word45State25 = word45State26 := by decide +kernel

private def word45Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word45State27 : PackedMat2 :=
    ⟨⟨⟨((-99527 : Dyadic) * half ^ 21),
        ((-15583 : Dyadic) * half ^ 18)⟩,
       ⟨((-330181 : Dyadic) * half ^ 21),
        ((429315 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1866017 : Dyadic) * half ^ 21),
        ((-3553 : Dyadic) * half ^ 20)⟩,
       ⟨((294619 : Dyadic) * half ^ 21),
        ((394015 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((401121 : Dyadic) * half ^ 21),
        ((540159 : Dyadic) * half ^ 20)⟩,
       ⟨((386909 : Dyadic) * half ^ 21),
        ((-785699 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-553979 : Dyadic) * half ^ 21),
        ((115327 : Dyadic) * half ^ 21)⟩,
       ⟨((-304651 : Dyadic) * half ^ 21),
        ((107427 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word45Step26 :
    word45Chunk26.foldl (fun acc a => a.applyPacked acc)
      word45State26 = word45State27 := by decide +kernel

private def word45Chunk27 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State28 : PackedMat2 :=
    ⟨⟨⟨((240987 : Dyadic) * half ^ 21),
        ((137869 : Dyadic) * half ^ 20)⟩,
       ⟨((286503 : Dyadic) * half ^ 20),
        ((-38767 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-431405 : Dyadic) * half ^ 21),
        ((-2144705 : Dyadic) * half ^ 22)⟩,
       ⟨((-691319 : Dyadic) * half ^ 21),
        ((502367 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((691319 : Dyadic) * half ^ 21),
        ((-502367 : Dyadic) * half ^ 22)⟩,
       ⟨((431405 : Dyadic) * half ^ 21),
        ((2144705 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((286503 : Dyadic) * half ^ 20),
        ((-38767 : Dyadic) * half ^ 17)⟩,
       ⟨((240987 : Dyadic) * half ^ 21),
        ((137869 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word45Step27 :
    word45Chunk27.foldl (fun acc a => a.applyPacked acc)
      word45State27 = word45State28 := by decide +kernel

private def word45Chunk28 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word45State29 : PackedMat2 :=
    ⟨⟨⟨((-712849 : Dyadic) * half ^ 22),
        ((2224885 : Dyadic) * half ^ 23)⟩,
       ⟨((-715481 : Dyadic) * half ^ 21),
        ((-447217 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-253299 : Dyadic) * half ^ 19),
        ((-124633 : Dyadic) * half ^ 23)⟩,
       ⟨((-170025 : Dyadic) * half ^ 22),
        ((-4078819 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1050863 : Dyadic) * half ^ 21),
        ((-2196417 : Dyadic) * half ^ 23)⟩,
       ⟨((1977093 : Dyadic) * half ^ 22),
        ((-1856367 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-444417 : Dyadic) * half ^ 21),
        ((2143811 : Dyadic) * half ^ 23)⟩,
       ⟨((-1336051 : Dyadic) * half ^ 22),
        ((-718113 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word45Step28 :
    word45Chunk28.foldl (fun acc a => a.applyPacked acc)
      word45State28 = word45State29 := by decide +kernel

private def word45Chunk29 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word45State30 : PackedMat2 :=
    ⟨⟨⟨((726735 : Dyadic) * half ^ 22),
        ((-296047 : Dyadic) * half ^ 22)⟩,
       ⟨((444243 : Dyadic) * half ^ 21),
        ((2303555 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((4886359 : Dyadic) * half ^ 23),
        ((15275 : Dyadic) * half ^ 21)⟩,
       ⟨((-5389055 : Dyadic) * half ^ 23),
        ((163819 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-89547 : Dyadic) * half ^ 20),
        ((62837 : Dyadic) * half ^ 21)⟩,
       ⟨((2321 : Dyadic) * half ^ 15),
        ((-5137707 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1711461 : Dyadic) * half ^ 23),
        ((1615221 : Dyadic) * half ^ 23)⟩,
       ⟨((-2895649 : Dyadic) * half ^ 23),
        ((-161751 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word45Step29 :
    word45Chunk29.foldl (fun acc a => a.applyPacked acc)
      word45State29 = word45State30 := by decide +kernel

private def word45Chunk30 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word45State31 : PackedMat2 :=
    ⟨⟨⟨((2427895 : Dyadic) * half ^ 24),
        ((-1505361 : Dyadic) * half ^ 24)⟩,
       ⟨((1174221 : Dyadic) * half ^ 24),
        ((561889 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((7288227 : Dyadic) * half ^ 24),
        ((3267319 : Dyadic) * half ^ 23)⟩,
       ⟨((7650381 : Dyadic) * half ^ 24),
        ((-5920049 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((12454687 : Dyadic) * half ^ 24),
        ((-181077 : Dyadic) * half ^ 24)⟩,
       ⟨((-614589 : Dyadic) * half ^ 24),
        ((-933663 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((2629139 : Dyadic) * half ^ 24),
        ((-626837 : Dyadic) * half ^ 24)⟩,
       ⟨((-381583 : Dyadic) * half ^ 24),
        ((900529 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word45Step30 :
    word45Chunk30.foldl (fun acc a => a.applyPacked acc)
      word45State30 = word45State31 := by decide +kernel

private def word45Chunk31 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State32 : PackedMat2 :=
    ⟨⟨⟨((516859 : Dyadic) * half ^ 21),
        ((35095 : Dyadic) * half ^ 20)⟩,
       ⟨((2030431 : Dyadic) * half ^ 24),
        ((-1950111 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((4024017 : Dyadic) * half ^ 24),
        ((12581439 : Dyadic) * half ^ 25)⟩,
       ⟨((-2466727 : Dyadic) * half ^ 24),
        ((15986077 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-2466727 : Dyadic) * half ^ 24),
        ((15986077 : Dyadic) * half ^ 25)⟩,
       ⟨((4024017 : Dyadic) * half ^ 24),
        ((12581439 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-2030431 : Dyadic) * half ^ 24),
        ((1950111 : Dyadic) * half ^ 23)⟩,
       ⟨((-516859 : Dyadic) * half ^ 21),
        ((-35095 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word45Step31 :
    word45Chunk31.foldl (fun acc a => a.applyPacked acc)
      word45State31 = word45State32 := by decide +kernel

private def word45Chunk32 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word45State33 : PackedMat2 :=
    ⟨⟨⟨((4364219 : Dyadic) * half ^ 23),
        ((-21423 : Dyadic) * half ^ 25)⟩,
       ⟨((23329149 : Dyadic) * half ^ 25),
        ((1776059 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1935081 : Dyadic) * half ^ 25),
        ((20163197 : Dyadic) * half ^ 26)⟩,
       ⟨((4770309 : Dyadic) * half ^ 25),
        ((-9035581 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((14599389 : Dyadic) * half ^ 25),
        ((-3352695 : Dyadic) * half ^ 25)⟩,
       ⟨((-173869 : Dyadic) * half ^ 20),
        ((-708807 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((898741 : Dyadic) * half ^ 24),
        ((5872273 : Dyadic) * half ^ 26)⟩,
       ⟨((438659 : Dyadic) * half ^ 23),
        ((40786025 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word45Step32 :
    word45Chunk32.foldl (fun acc a => a.applyPacked acc)
      word45State32 = word45State33 := by decide +kernel

private def word45Chunk33 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word45State34 : PackedMat2 :=
    ⟨⟨⟨((-10718457 : Dyadic) * half ^ 25),
        ((11198437 : Dyadic) * half ^ 27)⟩,
       ⟨((25779303 : Dyadic) * half ^ 26),
        ((37579871 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((8212441 : Dyadic) * half ^ 24),
        ((5122573 : Dyadic) * half ^ 27)⟩,
       ⟨((-34299811 : Dyadic) * half ^ 26),
        ((26151697 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((15637135 : Dyadic) * half ^ 26),
        ((-1450047 : Dyadic) * half ^ 27)⟩,
       ⟨((-5257281 : Dyadic) * half ^ 25),
        ((67149575 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-12194577 : Dyadic) * half ^ 25),
        ((-4342389 : Dyadic) * half ^ 27)⟩,
       ⟨((13190717 : Dyadic) * half ^ 26),
        ((47216217 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word45Step33 :
    word45Chunk33.foldl (fun acc a => a.applyPacked acc)
      word45State33 = word45State34 := by decide +kernel

private def word45Chunk34 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word45State35 : PackedMat2 :=
    ⟨⟨⟨((-30218001 : Dyadic) * half ^ 27),
        ((-19750913 : Dyadic) * half ^ 26)⟩,
       ⟨((26657519 : Dyadic) * half ^ 27),
        ((-1098133 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((31905769 : Dyadic) * half ^ 26),
        ((10972555 : Dyadic) * half ^ 26)⟩,
       ⟨((5726343 : Dyadic) * half ^ 24),
        ((-55346633 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-31905769 : Dyadic) * half ^ 26),
        ((-10972555 : Dyadic) * half ^ 26)⟩,
       ⟨((5726343 : Dyadic) * half ^ 24),
        ((-55346633 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-30218001 : Dyadic) * half ^ 27),
        ((-19750913 : Dyadic) * half ^ 26)⟩,
       ⟨((-26657519 : Dyadic) * half ^ 27),
        ((1098133 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word45Step34 :
    word45Chunk34.foldl (fun acc a => a.applyPacked acc)
      word45State34 = word45State35 := by decide +kernel

private def word45Chunk35 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State36 : PackedMat2 :=
    ⟨⟨⟨((-169472709 : Dyadic) * half ^ 28),
        ((-49966845 : Dyadic) * half ^ 28)⟩,
       ⟨((11200211 : Dyadic) * half ^ 28),
        ((-17047735 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-32138525 : Dyadic) * half ^ 28),
        ((79656345 : Dyadic) * half ^ 28)⟩,
       ⟨((-73539247 : Dyadic) * half ^ 28),
        ((8744015 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((9704225 : Dyadic) * half ^ 28),
        ((20700361 : Dyadic) * half ^ 28)⟩,
       ⟨((-149608465 : Dyadic) * half ^ 28),
        ((26419443 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-18224095 : Dyadic) * half ^ 28),
        ((22584115 : Dyadic) * half ^ 26)⟩,
       ⟨((-118157785 : Dyadic) * half ^ 28),
        ((-79136249 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word45Step35 :
    word45Chunk35.foldl (fun acc a => a.applyPacked acc)
      word45State35 = word45State36 := by decide +kernel

private def word45Chunk36 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word45State37 : PackedMat2 :=
    ⟨⟨⟨((1953405 : Dyadic) * half ^ 22),
        ((-42130795 : Dyadic) * half ^ 29)⟩,
       ⟨((-66673045 : Dyadic) * half ^ 27),
        ((-140568499 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((1977847 : Dyadic) * half ^ 23),
        ((-49274761 : Dyadic) * half ^ 27)⟩,
       ⟨((10768239 : Dyadic) * half ^ 28),
        ((-46550753 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((51998769 : Dyadic) * half ^ 28),
        ((-52522865 : Dyadic) * half ^ 29)⟩,
       ⟨((-145100275 : Dyadic) * half ^ 28),
        ((74059343 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((12304713 : Dyadic) * half ^ 26),
        ((129182005 : Dyadic) * half ^ 28)⟩,
       ⟨((91349647 : Dyadic) * half ^ 28),
        ((4164085 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word45Step36 :
    word45Chunk36.foldl (fun acc a => a.applyPacked acc)
      word45State36 = word45State37 := by decide +kernel

private def word45Chunk37 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word45State38 : PackedMat2 :=
    ⟨⟨⟨((154506399 : Dyadic) * half ^ 29),
        ((193505295 : Dyadic) * half ^ 30)⟩,
       ⟨((-13159409 : Dyadic) * half ^ 28),
        ((-215721469 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-332885203 : Dyadic) * half ^ 29),
        ((261814509 : Dyadic) * half ^ 30)⟩,
       ⟨((-40789123 : Dyadic) * half ^ 27),
        ((-316131065 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((13579139 : Dyadic) * half ^ 28),
        ((496041695 : Dyadic) * half ^ 30)⟩,
       ⟨((-288972787 : Dyadic) * half ^ 29),
        ((169728711 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-11108087 : Dyadic) * half ^ 29),
        ((128187581 : Dyadic) * half ^ 30)⟩,
       ⟨((102306691 : Dyadic) * half ^ 28),
        ((180825217 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word45Step37 :
    word45Chunk37.foldl (fun acc a => a.applyPacked acc)
      word45State37 = word45State38 := by decide +kernel

private def word45Chunk38 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word45State39 : PackedMat2 :=
    ⟨⟨⟨((34252033 : Dyadic) * half ^ 28),
        ((1046295485 : Dyadic) * half ^ 31)⟩,
       ⟨((224482935 : Dyadic) * half ^ 30),
        ((-208321371 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-253343987 : Dyadic) * half ^ 30),
        ((663836805 : Dyadic) * half ^ 31)⟩,
       ⟨((-13539445 : Dyadic) * half ^ 27),
        ((-660963815 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-13539445 : Dyadic) * half ^ 27),
        ((-660963815 : Dyadic) * half ^ 31)⟩,
       ⟨((-253343987 : Dyadic) * half ^ 30),
        ((663836805 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-224482935 : Dyadic) * half ^ 30),
        ((208321371 : Dyadic) * half ^ 31)⟩,
       ⟨((-34252033 : Dyadic) * half ^ 28),
        ((-1046295485 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word45Step38 :
    word45Chunk38.foldl (fun acc a => a.applyPacked acc)
      word45State38 = word45State39 := by decide +kernel

private def word45Chunk39 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word45State40 : PackedMat2 :=
    ⟨⟨⟨((-30071433 : Dyadic) * half ^ 31),
        ((47828395 : Dyadic) * half ^ 29)⟩,
       ⟨((81075493 : Dyadic) * half ^ 31),
        ((-405865781 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((301214707 : Dyadic) * half ^ 31),
        ((304160363 : Dyadic) * half ^ 29)⟩,
       ⟨((956910243 : Dyadic) * half ^ 31),
        ((-342572837 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1559214289 : Dyadic) * half ^ 31),
        ((40980971 : Dyadic) * half ^ 28)⟩,
       ⟨((874068615 : Dyadic) * half ^ 31),
        ((629062475 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((597179361 : Dyadic) * half ^ 31),
        ((-55573463 : Dyadic) * half ^ 31)⟩,
       ⟨((214552201 : Dyadic) * half ^ 31),
        ((-12751015 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word45Step39 :
    word45Chunk39.foldl (fun acc a => a.applyPacked acc)
      word45State39 = word45State40 := by decide +kernel

private def word45Chunk40 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word45State41 : PackedMat2 :=
    ⟨⟨⟨((187885693 : Dyadic) * half ^ 29),
        ((-183594099 : Dyadic) * half ^ 32)⟩,
       ⟨((-6121105 : Dyadic) * half ^ 30),
        ((1839322843 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((110006923 : Dyadic) * half ^ 31),
        ((-398025301 : Dyadic) * half ^ 31)⟩,
       ⟨((7763891 : Dyadic) * half ^ 27),
        ((124810199 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-7763891 : Dyadic) * half ^ 27),
        ((-124810199 : Dyadic) * half ^ 28)⟩,
       ⟨((-110006923 : Dyadic) * half ^ 31),
        ((398025301 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-6121105 : Dyadic) * half ^ 30),
        ((1839322843 : Dyadic) * half ^ 32)⟩,
       ⟨((187885693 : Dyadic) * half ^ 29),
        ((-183594099 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word45Step40 :
    word45Chunk40.foldl (fun acc a => a.applyPacked acc)
      word45State40 = word45State41 := by decide +kernel

private def word45Chunk41 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State42 : PackedMat2 :=
    ⟨⟨⟨((-295574145 : Dyadic) * half ^ 32),
        ((-2333200483 : Dyadic) * half ^ 33)⟩,
       ⟨((620214673 : Dyadic) * half ^ 30),
        ((587972083 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-233128767 : Dyadic) * half ^ 30),
        ((62373505 : Dyadic) * half ^ 33)⟩,
       ⟨((2858512879 : Dyadic) * half ^ 32),
        ((-731200189 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-167206671 : Dyadic) * half ^ 31),
        ((1925997811 : Dyadic) * half ^ 33)⟩,
       ⟨((396786847 : Dyadic) * half ^ 32),
        ((-3791027947 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((109076775 : Dyadic) * half ^ 29),
        ((-2185284547 : Dyadic) * half ^ 33)⟩,
       ⟨((1460586283 : Dyadic) * half ^ 32),
        ((2776432837 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word45Step41 :
    word45Chunk41.foldl (fun acc a => a.applyPacked acc)
      word45State41 = word45State42 := by decide +kernel

private def word45Chunk42 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State43 : PackedMat2 :=
    ⟨⟨⟨((-5148472517 : Dyadic) * half ^ 33),
        ((373438719 : Dyadic) * half ^ 33)⟩,
       ⟨((689184785 : Dyadic) * half ^ 33),
        ((-581255523 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-961762587 : Dyadic) * half ^ 32),
        ((-1659557247 : Dyadic) * half ^ 33)⟩,
       ⟨((-101564487 : Dyadic) * half ^ 32),
        ((2138958025 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((961762587 : Dyadic) * half ^ 32),
        ((1659557247 : Dyadic) * half ^ 33)⟩,
       ⟨((-101564487 : Dyadic) * half ^ 32),
        ((2138958025 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-5148472517 : Dyadic) * half ^ 33),
        ((373438719 : Dyadic) * half ^ 33)⟩,
       ⟨((-689184785 : Dyadic) * half ^ 33),
        ((581255523 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word45Step42 :
    word45Chunk42.foldl (fun acc a => a.applyPacked acc)
      word45State42 = word45State43 := by decide +kernel

private def word45Chunk43 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word45State44 : PackedMat2 :=
    ⟨⟨⟨((913030623 : Dyadic) * half ^ 33),
        ((281584895 : Dyadic) * half ^ 33)⟩,
       ⟨((3149519771 : Dyadic) * half ^ 33),
        ((-4073612331 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-13824106353 : Dyadic) * half ^ 34),
        ((-1546343349 : Dyadic) * half ^ 34)⟩,
       ⟨((4629899045 : Dyadic) * half ^ 34),
        ((702962997 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-6588909 : Dyadic) * half ^ 27),
        ((-2298551827 : Dyadic) * half ^ 33)⟩,
       ⟨((-1124653173 : Dyadic) * half ^ 33),
        ((-9227002699 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3510442541 : Dyadic) * half ^ 34),
        ((-2031275197 : Dyadic) * half ^ 33)⟩,
       ⟨((-4636782121 : Dyadic) * half ^ 34),
        ((559122287 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word45Step43 :
    word45Chunk43.foldl (fun acc a => a.applyPacked acc)
      word45State43 = word45State44 := by decide +kernel

private def word45Chunk44 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word45State45 : PackedMat2 :=
    ⟨⟨⟨((-5734114491 : Dyadic) * half ^ 35),
        ((8963167607 : Dyadic) * half ^ 34)⟩,
       ⟨((2644938315 : Dyadic) * half ^ 35),
        ((-5871057047 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-14660603629 : Dyadic) * half ^ 35),
        ((-2270724787 : Dyadic) * half ^ 33)⟩,
       ⟨((-3434458421 : Dyadic) * half ^ 35),
        ((4321071953 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((13403971101 : Dyadic) * half ^ 35),
        ((1403268151 : Dyadic) * half ^ 33)⟩,
       ⟨((-4761827195 : Dyadic) * half ^ 35),
        ((-9047531025 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((23797392261 : Dyadic) * half ^ 35),
        ((-4189526403 : Dyadic) * half ^ 35)⟩,
       ⟨((-12055278167 : Dyadic) * half ^ 35),
        ((193073511 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word45Step44 :
    word45Chunk44.foldl (fun acc a => a.applyPacked acc)
      word45State44 = word45State45 := by decide +kernel

private def word45Chunk45 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word45State46 : PackedMat2 :=
    ⟨⟨⟨((4950940253 : Dyadic) * half ^ 34),
        ((-21391133 : Dyadic) * half ^ 28)⟩,
       ⟨((-6357200695 : Dyadic) * half ^ 35),
        ((14809402277 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-4816091517 : Dyadic) * half ^ 33),
        ((-14792149179 : Dyadic) * half ^ 36)⟩,
       ⟨((1509204611 : Dyadic) * half ^ 34),
        ((-14061945657 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-1509204611 : Dyadic) * half ^ 34),
        ((14061945657 : Dyadic) * half ^ 36)⟩,
       ⟨((4816091517 : Dyadic) * half ^ 33),
        ((14792149179 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-6357200695 : Dyadic) * half ^ 35),
        ((14809402277 : Dyadic) * half ^ 35)⟩,
       ⟨((4950940253 : Dyadic) * half ^ 34),
        ((-21391133 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word45Step45 :
    word45Chunk45.foldl (fun acc a => a.applyPacked acc)
      word45State45 = word45State46 := by decide +kernel

private def word45Chunk46 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State47 : PackedMat2 :=
    ⟨⟨⟨((-2137338575 : Dyadic) * half ^ 36),
        ((4246902115 : Dyadic) * half ^ 37)⟩,
       ⟨((7348131391 : Dyadic) * half ^ 33),
        ((-3398382259 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-3020969887 : Dyadic) * half ^ 33),
        ((5152018075 : Dyadic) * half ^ 37)⟩,
       ⟨((-23424431219 : Dyadic) * half ^ 36),
        ((-14231460783 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-2269860677 : Dyadic) * half ^ 35),
        ((-47592190315 : Dyadic) * half ^ 37)⟩,
       ⟨((9691739429 : Dyadic) * half ^ 36),
        ((-743327877 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-53032491 : Dyadic) * half ^ 33),
        ((-56647712553 : Dyadic) * half ^ 37)⟩,
       ⟨((-3822642187 : Dyadic) * half ^ 36),
        ((60922389703 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word45Step46 :
    word45Chunk46.foldl (fun acc a => a.applyPacked acc)
      word45State46 = word45State47 := by decide +kernel

private def word45Chunk47 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word45State48 : PackedMat2 :=
    ⟨⟨⟨((-59077870367 : Dyadic) * half ^ 37),
        ((-24234242603 : Dyadic) * half ^ 37)⟩,
       ⟨((4156018595 : Dyadic) * half ^ 37),
        ((60536838247 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((14076094683 : Dyadic) * half ^ 36),
        ((-45375884981 : Dyadic) * half ^ 37)⟩,
       ⟨((-21110931033 : Dyadic) * half ^ 36),
        ((4806386335 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-14076094683 : Dyadic) * half ^ 36),
        ((45375884981 : Dyadic) * half ^ 37)⟩,
       ⟨((-21110931033 : Dyadic) * half ^ 36),
        ((4806386335 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-59077870367 : Dyadic) * half ^ 37),
        ((-24234242603 : Dyadic) * half ^ 37)⟩,
       ⟨((-4156018595 : Dyadic) * half ^ 37),
        ((-60536838247 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word45Step47 :
    word45Chunk47.foldl (fun acc a => a.applyPacked acc)
      word45State47 = word45State48 := by decide +kernel

private def word45Chunk48 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word45State49 : PackedMat2 :=
    ⟨⟨⟨((-42045792557 : Dyadic) * half ^ 38),
        ((36526359017 : Dyadic) * half ^ 38)⟩,
       ⟨((64949295849 : Dyadic) * half ^ 38),
        ((-61332907663 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-9049050115 : Dyadic) * half ^ 36),
        ((-96156026617 : Dyadic) * half ^ 38)⟩,
       ⟨((-49602475977 : Dyadic) * half ^ 36),
        ((-2568957023 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-106431854709 : Dyadic) * half ^ 38),
        ((-14662881523 : Dyadic) * half ^ 35)⟩,
       ⟨((-85880198525 : Dyadic) * half ^ 38),
        ((20276712931 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((12403274323 : Dyadic) * half ^ 37),
        ((-5725875823 : Dyadic) * half ^ 37)⟩,
       ⟨((-12232408335 : Dyadic) * half ^ 35),
        ((53497544203 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word45Step48 :
    word45Chunk48.foldl (fun acc a => a.applyPacked acc)
      word45State48 = word45State49 := by decide +kernel

private def word45Chunk49 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word45State50 : PackedMat2 :=
    ⟨⟨⟨((44299622645 : Dyadic) * half ^ 39),
        ((115443141723 : Dyadic) * half ^ 39)⟩,
       ⟨((-363121511791 : Dyadic) * half ^ 39),
        ((45599913387 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-35947941883 : Dyadic) * half ^ 39),
        ((10605986649 : Dyadic) * half ^ 39)⟩,
       ⟨((-121697152493 : Dyadic) * half ^ 39),
        ((-116616511431 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((35947941883 : Dyadic) * half ^ 39),
        ((-10605986649 : Dyadic) * half ^ 39)⟩,
       ⟨((-121697152493 : Dyadic) * half ^ 39),
        ((-116616511431 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((44299622645 : Dyadic) * half ^ 39),
        ((115443141723 : Dyadic) * half ^ 39)⟩,
       ⟨((363121511791 : Dyadic) * half ^ 39),
        ((-45599913387 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word45Step49 :
    word45Chunk49.foldl (fun acc a => a.applyPacked acc)
      word45State49 = word45State50 := by decide +kernel

private def word45Chunk50 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word45State51 : PackedMat2 :=
    ⟨⟨⟨((-158150895859 : Dyadic) * half ^ 40),
        ((308940148205 : Dyadic) * half ^ 39)⟩,
       ⟨((-157732085165 : Dyadic) * half ^ 40),
        ((-332150871727 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((354281682335 : Dyadic) * half ^ 40),
        ((14735119877 : Dyadic) * half ^ 37)⟩,
       ⟨((-142384914425 : Dyadic) * half ^ 40),
        ((-25033609515 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((354281682335 : Dyadic) * half ^ 40),
        ((14735119877 : Dyadic) * half ^ 37)⟩,
       ⟨((142384914425 : Dyadic) * half ^ 40),
        ((25033609515 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((158150895859 : Dyadic) * half ^ 40),
        ((-308940148205 : Dyadic) * half ^ 39)⟩,
       ⟨((-157732085165 : Dyadic) * half ^ 40),
        ((-332150871727 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word45Step50 :
    word45Chunk50.foldl (fun acc a => a.applyPacked acc)
      word45State50 = word45State51 := by decide +kernel

private def word45Chunk51 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word45State52 : PackedMat2 :=
    ⟨⟨⟨((35731424891 : Dyadic) * half ^ 39),
        ((383528034055 : Dyadic) * half ^ 40)⟩,
       ⟨((-455816233413 : Dyadic) * half ^ 40),
        ((201909894523 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((373623015713 : Dyadic) * half ^ 40),
        ((581013824213 : Dyadic) * half ^ 41)⟩,
       ⟨((113566547619 : Dyadic) * half ^ 40),
        ((-773366245289 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((113566547619 : Dyadic) * half ^ 40),
        ((-773366245289 : Dyadic) * half ^ 41)⟩,
       ⟨((373623015713 : Dyadic) * half ^ 40),
        ((581013824213 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((455816233413 : Dyadic) * half ^ 40),
        ((-201909894523 : Dyadic) * half ^ 40)⟩,
       ⟨((-35731424891 : Dyadic) * half ^ 39),
        ((-383528034055 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word45Step51 :
    word45Chunk51.foldl (fun acc a => a.applyPacked acc)
      word45State51 = word45State52 := by decide +kernel

private def word45Chunk52 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word45State53 : PackedMat2 :=
    ⟨⟨⟨((-303591240517 : Dyadic) * half ^ 39),
        ((399294015489 : Dyadic) * half ^ 41)⟩,
       ⟨((444247428073 : Dyadic) * half ^ 41),
        ((713923662023 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((802162841135 : Dyadic) * half ^ 41),
        ((187914629873 : Dyadic) * half ^ 42)⟩,
       ⟨((-1072126826171 : Dyadic) * half ^ 41),
        ((-172294624721 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((180104627297 : Dyadic) * half ^ 41),
        ((937144833653 : Dyadic) * half ^ 41)⟩,
       ⟨((-488125161 : Dyadic) * half ^ 37),
        ((67490996259 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((157314823267 : Dyadic) * half ^ 40),
        ((1658612390141 : Dyadic) * half ^ 42)⟩,
       ⟨((139152209689 : Dyadic) * half ^ 38),
        ((-770117533995 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word45Step52 :
    word45Chunk52.foldl (fun acc a => a.applyPacked acc)
      word45State52 = word45State53 := by decide +kernel

private def word45Chunk53 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word45State54 : PackedMat2 :=
    ⟨⟨⟨((-223911119115 : Dyadic) * half ^ 41),
        ((-4044491878055 : Dyadic) * half ^ 43)⟩,
       ⟨((-858644464193 : Dyadic) * half ^ 42),
        ((1514788262403 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((5709561747 : Dyadic) * half ^ 39),
        ((2575208337969 : Dyadic) * half ^ 43)⟩,
       ⟨((185620788341 : Dyadic) * half ^ 42),
        ((-3384186346515 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-404489004273 : Dyadic) * half ^ 42),
        ((231297282317 : Dyadic) * half ^ 43)⟩,
       ⟨((1489848671121 : Dyadic) * half ^ 41),
        ((-139944294365 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((632425903913 : Dyadic) * half ^ 41),
        ((1306466702423 : Dyadic) * half ^ 43)⟩,
       ⟨((2779640070229 : Dyadic) * half ^ 42),
        ((-410822225963 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word45Step53 :
    word45Chunk53.foldl (fun acc a => a.applyPacked acc)
      word45State53 = word45State54 := by decide +kernel

private def word45Chunk54 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word45State55 : PackedMat2 :=
    ⟨⟨⟨((-2787014742499 : Dyadic) * half ^ 43),
        ((-354197627967 : Dyadic) * half ^ 44)⟩,
       ⟨((-58449619805 : Dyadic) * half ^ 38),
        ((3819427683477 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((7462918446897 : Dyadic) * half ^ 43),
        ((982619959077 : Dyadic) * half ^ 44)⟩,
       ⟨((752535165057 : Dyadic) * half ^ 42),
        ((-781727959913 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-50222999791 : Dyadic) * half ^ 42),
        ((-8967988777011 : Dyadic) * half ^ 44)⟩,
       ⟨((-882173959495 : Dyadic) * half ^ 43),
        ((-5957848116783 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((1732615027755 : Dyadic) * half ^ 43),
        ((-4657402576259 : Dyadic) * half ^ 44)⟩,
       ⟨((-1043406327861 : Dyadic) * half ^ 42),
        ((-916626908739 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word45Step54 :
    word45Chunk54.foldl (fun acc a => a.applyPacked acc)
      word45State54 = word45State55 := by decide +kernel

private def word45Chunk55 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word45State56 : PackedMat2 :=
    ⟨⟨⟨((-611541065795 : Dyadic) * half ^ 41),
        ((-2682238461663 : Dyadic) * half ^ 44)⟩,
       ⟨((1160529224565 : Dyadic) * half ^ 43),
        ((-150199310119 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-10872829560015 : Dyadic) * half ^ 44),
        ((1350689622413 : Dyadic) * half ^ 43)⟩,
       ⟨((7928681950125 : Dyadic) * half ^ 44),
        ((1728227253131 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-10872829560015 : Dyadic) * half ^ 44),
        ((1350689622413 : Dyadic) * half ^ 43)⟩,
       ⟨((-7928681950125 : Dyadic) * half ^ 44),
        ((-1728227253131 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((611541065795 : Dyadic) * half ^ 41),
        ((2682238461663 : Dyadic) * half ^ 44)⟩,
       ⟨((1160529224565 : Dyadic) * half ^ 43),
        ((-150199310119 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word45Step55 :
    word45Chunk55.foldl (fun acc a => a.applyPacked acc)
      word45State55 = word45State56 := by decide +kernel

private def word45Chunk56 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word45State57 : PackedMat2 :=
    ⟨⟨⟨((2979200126037 : Dyadic) * half ^ 45),
        ((-12190863632971 : Dyadic) * half ^ 45)⟩,
       ⟨((-1815000936671 : Dyadic) * half ^ 45),
        ((-19952247599929 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((1106127502959 : Dyadic) * half ^ 42),
        ((446076367801 : Dyadic) * half ^ 43)⟩,
       ⟨((121436955479 : Dyadic) * half ^ 40),
        ((-4035962629715 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((2251657158511 : Dyadic) * half ^ 45),
        ((-1591875324875 : Dyadic) * half ^ 43)⟩,
       ⟨((-5820268100919 : Dyadic) * half ^ 45),
        ((-620379681043 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-8035777808225 : Dyadic) * half ^ 43),
        ((582099594683 : Dyadic) * half ^ 45)⟩,
       ⟨((3880691983479 : Dyadic) * half ^ 44),
        ((1198550265677 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word45Step56 :
    word45Chunk56.foldl (fun acc a => a.applyPacked acc)
      word45State56 = word45State57 := by decide +kernel

private def word45Chunk57 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word45State58 : PackedMat2 :=
    ⟨⟨⟨((-29600567328703 : Dyadic) * half ^ 46),
        ((14710984861141 : Dyadic) * half ^ 46)⟩,
       ⟨((-776916676673 : Dyadic) * half ^ 46),
        ((-16029346520041 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((34854491522733 : Dyadic) * half ^ 46),
        ((1450708725717 : Dyadic) * half ^ 43)⟩,
       ⟨((-846649468877 : Dyadic) * half ^ 46),
        ((-7130276414037 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((18735946219773 : Dyadic) * half ^ 46),
        ((17850570495805 : Dyadic) * half ^ 46)⟩,
       ⟨((-4475393391699 : Dyadic) * half ^ 46),
        ((-1062745064183 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-46769677901223 : Dyadic) * half ^ 46),
        ((14411825326015 : Dyadic) * half ^ 46)⟩,
       ⟨((-17347708178941 : Dyadic) * half ^ 46),
        ((-7416377931 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word45Step57 :
    word45Chunk57.foldl (fun acc a => a.applyPacked acc)
      word45State57 = word45State58 := by decide +kernel

private def word45Chunk58 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word45State59 : PackedMat2 :=
    ⟨⟨⟨((64215488089831 : Dyadic) * half ^ 47),
        ((29230117201887 : Dyadic) * half ^ 47)⟩,
       ⟨((49628263705299 : Dyadic) * half ^ 47),
        ((-22698872898783 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-22157723318711 : Dyadic) * half ^ 47),
        ((40546984510125 : Dyadic) * half ^ 47)⟩,
       ⟨((-41239476583077 : Dyadic) * half ^ 47),
        ((-7725691660039 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((22157723318711 : Dyadic) * half ^ 47),
        ((-40546984510125 : Dyadic) * half ^ 47)⟩,
       ⟨((-41239476583077 : Dyadic) * half ^ 47),
        ((-7725691660039 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((64215488089831 : Dyadic) * half ^ 47),
        ((29230117201887 : Dyadic) * half ^ 47)⟩,
       ⟨((-49628263705299 : Dyadic) * half ^ 47),
        ((22698872898783 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word45Step58 :
    word45Chunk58.foldl (fun acc a => a.applyPacked acc)
      word45State58 = word45State59 := by decide +kernel

private def word45Chunk59 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word45State60 : PackedMat2 :=
    ⟨⟨⟨((-406123585747 : Dyadic) * half ^ 47),
        ((141311833838291 : Dyadic) * half ^ 48)⟩,
       ⟨((-49014877327791 : Dyadic) * half ^ 47),
        ((69317504275003 : Dyadic) * half ^ 48)⟩⟩,
     ⟨⟨((3317681781489 : Dyadic) * half ^ 43),
        ((32833459609505 : Dyadic) * half ^ 47)⟩,
       ⟨((-4667696799785 : Dyadic) * half ^ 47),
        ((3300560059657 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((3691612443731 : Dyadic) * half ^ 44),
        ((57750605303609 : Dyadic) * half ^ 48)⟩,
       ⟨((-18067009834581 : Dyadic) * half ^ 46),
        ((-48415211704039 : Dyadic) * half ^ 48)⟩⟩,
     ⟨⟨((-8999291195411 : Dyadic) * half ^ 45),
        ((-12152188435511 : Dyadic) * half ^ 46)⟩,
       ⟨((105314669056647 : Dyadic) * half ^ 47),
        ((-24710500456769 : Dyadic) * half ^ 47)⟩⟩⟩
private lemma word45Step59 :
    word45Chunk59.foldl (fun acc a => a.applyPacked acc)
      word45State59 = word45State60 := by decide +kernel

private def word45Chunk60 : List Letter := [.t, .h]
private def word45State61 : PackedMat2 :=
    ⟨⟨⟨((206978753057301 : Dyadic) * half ^ 48),
        ((52676784918077 : Dyadic) * half ^ 48)⟩,
       ⟨((62716384155689 : Dyadic) * half ^ 48),
        ((-22173590264003 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((-75644914619281 : Dyadic) * half ^ 48),
        ((53489032089571 : Dyadic) * half ^ 48)⟩,
       ⟨((75918624394317 : Dyadic) * half ^ 48),
        ((-6710321765947 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((75644914619281 : Dyadic) * half ^ 48),
        ((-53489032089571 : Dyadic) * half ^ 48)⟩,
       ⟨((75918624394317 : Dyadic) * half ^ 48),
        ((-6710321765947 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((206978753057301 : Dyadic) * half ^ 48),
        ((52676784918077 : Dyadic) * half ^ 48)⟩,
       ⟨((-62716384155689 : Dyadic) * half ^ 48),
        ((22173590264003 : Dyadic) * half ^ 47)⟩⟩⟩
private lemma word45Step60 :
    word45Chunk60.foldl (fun acc a => a.applyPacked acc)
      word45State60 = word45State61 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word45_check : check word45 45 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word45 = word45State61.toMatrix := by
    unfold evalRingPacked
    change ((
      word45Chunk0 ++ word45Chunk1 ++ word45Chunk2 ++ word45Chunk3 ++
      word45Chunk4 ++ word45Chunk5 ++ word45Chunk6 ++ word45Chunk7 ++
      word45Chunk8 ++ word45Chunk9 ++ word45Chunk10 ++ word45Chunk11 ++
      word45Chunk12 ++ word45Chunk13 ++ word45Chunk14 ++ word45Chunk15 ++
      word45Chunk16 ++ word45Chunk17 ++ word45Chunk18 ++ word45Chunk19 ++
      word45Chunk20 ++ word45Chunk21 ++ word45Chunk22 ++ word45Chunk23 ++
      word45Chunk24 ++ word45Chunk25 ++ word45Chunk26 ++ word45Chunk27 ++
      word45Chunk28 ++ word45Chunk29 ++ word45Chunk30 ++ word45Chunk31 ++
      word45Chunk32 ++ word45Chunk33 ++ word45Chunk34 ++ word45Chunk35 ++
      word45Chunk36 ++ word45Chunk37 ++ word45Chunk38 ++ word45Chunk39 ++
      word45Chunk40 ++ word45Chunk41 ++ word45Chunk42 ++ word45Chunk43 ++
      word45Chunk44 ++ word45Chunk45 ++ word45Chunk46 ++ word45Chunk47 ++
      word45Chunk48 ++ word45Chunk49 ++ word45Chunk50 ++ word45Chunk51 ++
      word45Chunk52 ++ word45Chunk53 ++ word45Chunk54 ++ word45Chunk55 ++
      word45Chunk56 ++ word45Chunk57 ++ word45Chunk58 ++ word45Chunk59 ++
      word45Chunk60
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word45Step0, word45Step1, word45Step2, word45Step3, word45Step4,
      word45Step5, word45Step6, word45Step7, word45Step8, word45Step9,
      word45Step10, word45Step11, word45Step12, word45Step13, word45Step14,
      word45Step15, word45Step16, word45Step17, word45Step18, word45Step19,
      word45Step20, word45Step21, word45Step22, word45Step23, word45Step24,
      word45Step25, word45Step26, word45Step27, word45Step28, word45Step29,
      word45Step30, word45Step31, word45Step32, word45Step33, word45Step34,
      word45Step35, word45Step36, word45Step37, word45Step38, word45Step39,
      word45Step40, word45Step41, word45Step42, word45Step43, word45Step44,
      word45Step45, word45Step46, word45Step47, word45Step48, word45Step49,
      word45Step50, word45Step51, word45Step52, word45Step53, word45Step54,
      word45Step55, word45Step56, word45Step57, word45Step58, word45Step59,
      word45Step60]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
