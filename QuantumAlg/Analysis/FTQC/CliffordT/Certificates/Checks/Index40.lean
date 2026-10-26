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
private def word40Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word40State1 : PackedMat2 :=
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
private lemma word40Step0 :
    word40Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word40State1 := by decide +kernel

private def word40Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word40State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
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
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word40Step1 :
    word40Chunk1.foldl (fun acc a => a.applyPacked acc)
      word40State1 = word40State2 := by decide +kernel

private def word40Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word40State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word40Step2 :
    word40Chunk2.foldl (fun acc a => a.applyPacked acc)
      word40State2 = word40State3 := by decide +kernel

private def word40Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .s]
private def word40State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word40Step3 :
    word40Chunk3.foldl (fun acc a => a.applyPacked acc)
      word40State3 = word40State4 := by decide +kernel

private def word40Chunk4 : List Letter := [.h, .s, .s, .h, .h, .t, .h, .s]
private def word40State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word40Step4 :
    word40Chunk4.foldl (fun acc a => a.applyPacked acc)
      word40State4 = word40State5 := by decide +kernel

private def word40Chunk5 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word40State6 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word40Step5 :
    word40Chunk5.foldl (fun acc a => a.applyPacked acc)
      word40State5 = word40State6 := by decide +kernel

private def word40Chunk6 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word40State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word40Step6 :
    word40Chunk6.foldl (fun acc a => a.applyPacked acc)
      word40State6 = word40State7 := by decide +kernel

private def word40Chunk7 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word40State8 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word40Step7 :
    word40Chunk7.foldl (fun acc a => a.applyPacked acc)
      word40State7 = word40State8 := by decide +kernel

private def word40Chunk8 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word40State9 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word40Step8 :
    word40Chunk8.foldl (fun acc a => a.applyPacked acc)
      word40State8 = word40State9 := by decide +kernel

private def word40Chunk9 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word40State10 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word40Step9 :
    word40Chunk9.foldl (fun acc a => a.applyPacked acc)
      word40State9 = word40State10 := by decide +kernel

private def word40Chunk10 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word40State11 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 6),
        ((29 : Dyadic) * half ^ 6)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((25 : Dyadic) * half ^ 6),
        ((21 : Dyadic) * half ^ 6)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((25 : Dyadic) * half ^ 6),
        ((21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((15 : Dyadic) * half ^ 6),
        ((-29 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word40Step10 :
    word40Chunk10.foldl (fun acc a => a.applyPacked acc)
      word40State10 = word40State11 := by decide +kernel

private def word40Chunk11 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word40State12 : PackedMat2 :=
    ⟨⟨⟨((11 : Dyadic) * half ^ 4),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 7)⟩,
       ⟨((15 : Dyadic) * half ^ 6),
        ((35 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-23 : Dyadic) * half ^ 6),
        ((-9 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 6),
        ((17 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word40Step11 :
    word40Chunk11.foldl (fun acc a => a.applyPacked acc)
      word40State11 = word40State12 := by decide +kernel

private def word40Chunk12 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word40State13 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 6),
        ((131 : Dyadic) * half ^ 8)⟩,
       ⟨((25 : Dyadic) * half ^ 7),
        ((-63 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 8)⟩,
       ⟨((63 : Dyadic) * half ^ 7),
        ((-27 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 8)⟩,
       ⟨((-63 : Dyadic) * half ^ 7),
        ((27 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 6),
        ((-131 : Dyadic) * half ^ 8)⟩,
       ⟨((25 : Dyadic) * half ^ 7),
        ((-63 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word40Step12 :
    word40Chunk12.foldl (fun acc a => a.applyPacked acc)
      word40State12 = word40State13 := by decide +kernel

private def word40Chunk13 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word40State14 : PackedMat2 :=
    ⟨⟨⟨((53 : Dyadic) * half ^ 8),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((55 : Dyadic) * half ^ 8),
        ((43 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-163 : Dyadic) * half ^ 8),
        ((-7 : Dyadic) * half ^ 8)⟩,
       ⟨((-39 : Dyadic) * half ^ 8),
        ((69 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((163 : Dyadic) * half ^ 8),
        ((7 : Dyadic) * half ^ 8)⟩,
       ⟨((-39 : Dyadic) * half ^ 8),
        ((69 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((53 : Dyadic) * half ^ 8),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((-55 : Dyadic) * half ^ 8),
        ((-43 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word40Step13 :
    word40Chunk13.foldl (fun acc a => a.applyPacked acc)
      word40State13 = word40State14 := by decide +kernel

private def word40Chunk14 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word40State15 : PackedMat2 :=
    ⟨⟨⟨((63 : Dyadic) * half ^ 9),
        ((-161 : Dyadic) * half ^ 9)⟩,
       ⟨((417 : Dyadic) * half ^ 9),
        ((17 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 9),
        ((-91 : Dyadic) * half ^ 9)⟩,
       ⟨((-73 : Dyadic) * half ^ 9),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((73 : Dyadic) * half ^ 9),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((7 : Dyadic) * half ^ 9),
        ((91 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((417 : Dyadic) * half ^ 9),
        ((17 : Dyadic) * half ^ 8)⟩,
       ⟨((63 : Dyadic) * half ^ 9),
        ((-161 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word40Step14 :
    word40Chunk14.foldl (fun acc a => a.applyPacked acc)
      word40State14 = word40State15 := by decide +kernel

private def word40Chunk15 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word40State16 : PackedMat2 :=
    ⟨⟨⟨((-333 : Dyadic) * half ^ 9),
        ((-35 : Dyadic) * half ^ 10)⟩,
       ⟨((69 : Dyadic) * half ^ 9),
        ((347 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((77 : Dyadic) * half ^ 8),
        ((-37 : Dyadic) * half ^ 10)⟩,
       ⟨((23 : Dyadic) * half ^ 7),
        ((-325 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-181 : Dyadic) * half ^ 9),
        ((123 : Dyadic) * half ^ 9)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((31 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 7),
        ((33 : Dyadic) * half ^ 7)⟩,
       ⟨((191 : Dyadic) * half ^ 9),
        ((201 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word40Step15 :
    word40Chunk15.foldl (fun acc a => a.applyPacked acc)
      word40State15 = word40State16 := by decide +kernel

private def word40Chunk16 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word40State17 : PackedMat2 :=
    ⟨⟨⟨((77 : Dyadic) * half ^ 10),
        ((-1259 : Dyadic) * half ^ 11)⟩,
       ⟨((-65 : Dyadic) * half ^ 9),
        ((41 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 10),
        ((369 : Dyadic) * half ^ 11)⟩,
       ⟨((-181 : Dyadic) * half ^ 9),
        ((-255 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 10),
        ((-369 : Dyadic) * half ^ 11)⟩,
       ⟨((-181 : Dyadic) * half ^ 9),
        ((-255 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((77 : Dyadic) * half ^ 10),
        ((-1259 : Dyadic) * half ^ 11)⟩,
       ⟨((65 : Dyadic) * half ^ 9),
        ((-41 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word40Step16 :
    word40Chunk16.foldl (fun acc a => a.applyPacked acc)
      word40State16 = word40State17 := by decide +kernel

private def word40Chunk17 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word40State18 : PackedMat2 :=
    ⟨⟨⟨((-289 : Dyadic) * half ^ 9),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-61 : Dyadic) * half ^ 9),
        ((-887 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((101 : Dyadic) * half ^ 8),
        ((-475 : Dyadic) * half ^ 11)⟩,
       ⟨((-49 : Dyadic) * half ^ 10),
        ((-99 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-277 : Dyadic) * half ^ 11),
        ((453 : Dyadic) * half ^ 11)⟩,
       ⟨((673 : Dyadic) * half ^ 11),
        ((-355 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-759 : Dyadic) * half ^ 11),
        ((57 : Dyadic) * half ^ 8)⟩,
       ⟨((-1015 : Dyadic) * half ^ 11),
        ((-175 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word40Step17 :
    word40Chunk17.foldl (fun acc a => a.applyPacked acc)
      word40State17 = word40State18 := by decide +kernel

private def word40Chunk18 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word40State19 : PackedMat2 :=
    ⟨⟨⟨((265 : Dyadic) * half ^ 12),
        ((-361 : Dyadic) * half ^ 11)⟩,
       ⟨((-3603 : Dyadic) * half ^ 12),
        ((-17 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-93 : Dyadic) * half ^ 12),
        ((275 : Dyadic) * half ^ 11)⟩,
       ⟨((1427 : Dyadic) * half ^ 12),
        ((127 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1427 : Dyadic) * half ^ 12),
        ((127 : Dyadic) * half ^ 12)⟩,
       ⟨((-93 : Dyadic) * half ^ 12),
        ((275 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((3603 : Dyadic) * half ^ 12),
        ((17 : Dyadic) * half ^ 12)⟩,
       ⟨((-265 : Dyadic) * half ^ 12),
        ((361 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word40Step18 :
    word40Chunk18.foldl (fun acc a => a.applyPacked acc)
      word40State18 = word40State19 := by decide +kernel

private def word40Chunk19 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word40State20 : PackedMat2 :=
    ⟨⟨⟨((-1281 : Dyadic) * half ^ 13),
        ((811 : Dyadic) * half ^ 11)⟩,
       ⟨((-2189 : Dyadic) * half ^ 13),
        ((1317 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1521 : Dyadic) * half ^ 13),
        ((1865 : Dyadic) * half ^ 12)⟩,
       ⟨((837 : Dyadic) * half ^ 13),
        ((1631 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2099 : Dyadic) * half ^ 13),
        ((171 : Dyadic) * half ^ 12)⟩,
       ⟨((-5361 : Dyadic) * half ^ 13),
        ((-1179 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1927 : Dyadic) * half ^ 13),
        ((-227 : Dyadic) * half ^ 12)⟩,
       ⟨((4561 : Dyadic) * half ^ 13),
        ((-1735 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word40Step19 :
    word40Chunk19.foldl (fun acc a => a.applyPacked acc)
      word40State19 = word40State20 := by decide +kernel

private def word40Chunk20 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word40State21 : PackedMat2 :=
    ⟨⟨⟨((1685 : Dyadic) * half ^ 13),
        ((-75 : Dyadic) * half ^ 13)⟩,
       ⟨((-9 : Dyadic) * half ^ 12),
        ((2643 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1993 : Dyadic) * half ^ 12),
        ((933 : Dyadic) * half ^ 12)⟩,
       ⟨((-2151 : Dyadic) * half ^ 13),
        ((3377 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2151 : Dyadic) * half ^ 13),
        ((3377 : Dyadic) * half ^ 13)⟩,
       ⟨((1993 : Dyadic) * half ^ 12),
        ((933 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 12),
        ((-2643 : Dyadic) * half ^ 13)⟩,
       ⟨((-1685 : Dyadic) * half ^ 13),
        ((75 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word40Step20 :
    word40Chunk20.foldl (fun acc a => a.applyPacked acc)
      word40State20 = word40State21 := by decide +kernel

private def word40Chunk21 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word40State22 : PackedMat2 :=
    ⟨⟨⟨((-817 : Dyadic) * half ^ 11),
        ((3321 : Dyadic) * half ^ 15)⟩,
       ⟨((8257 : Dyadic) * half ^ 14),
        ((-37 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 6),
        ((-9635 : Dyadic) * half ^ 15)⟩,
       ⟨((9695 : Dyadic) * half ^ 14),
        ((-1037 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((667 : Dyadic) * half ^ 11),
        ((-6367 : Dyadic) * half ^ 15)⟩,
       ⟨((4299 : Dyadic) * half ^ 14),
        ((13023 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((821 : Dyadic) * half ^ 13),
        ((1721 : Dyadic) * half ^ 15)⟩,
       ⟨((1679 : Dyadic) * half ^ 14),
        ((-14793 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word40Step21 :
    word40Chunk21.foldl (fun acc a => a.applyPacked acc)
      word40State21 = word40State22 := by decide +kernel

private def word40Chunk22 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word40State23 : PackedMat2 :=
    ⟨⟨⟨((-201 : Dyadic) * half ^ 12),
        ((-425 : Dyadic) * half ^ 13)⟩,
       ⟨((1561 : Dyadic) * half ^ 14),
        ((9399 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-12933 : Dyadic) * half ^ 14),
        ((-1149 : Dyadic) * half ^ 15)⟩,
       ⟨((-6311 : Dyadic) * half ^ 14),
        ((153 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-12933 : Dyadic) * half ^ 14),
        ((-1149 : Dyadic) * half ^ 15)⟩,
       ⟨((6311 : Dyadic) * half ^ 14),
        ((-153 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((201 : Dyadic) * half ^ 12),
        ((425 : Dyadic) * half ^ 13)⟩,
       ⟨((1561 : Dyadic) * half ^ 14),
        ((9399 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word40Step22 :
    word40Chunk22.foldl (fun acc a => a.applyPacked acc)
      word40State22 = word40State23 := by decide +kernel

private def word40Chunk23 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word40State24 : PackedMat2 :=
    ⟨⟨⟨((-477 : Dyadic) * half ^ 16),
        ((-4385 : Dyadic) * half ^ 16)⟩,
       ⟨((20937 : Dyadic) * half ^ 16),
        ((-8911 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-775 : Dyadic) * half ^ 16),
        ((-33127 : Dyadic) * half ^ 16)⟩,
       ⟨((-23773 : Dyadic) * half ^ 16),
        ((-227 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((18599 : Dyadic) * half ^ 16),
        ((-11499 : Dyadic) * half ^ 16)⟩,
       ⟨((-47655 : Dyadic) * half ^ 16),
        ((-6137 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((13437 : Dyadic) * half ^ 16),
        ((-10707 : Dyadic) * half ^ 16)⟩,
       ⟨((22207 : Dyadic) * half ^ 16),
        ((-5115 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word40Step23 :
    word40Chunk23.foldl (fun acc a => a.applyPacked acc)
      word40State23 = word40State24 := by decide +kernel

private def word40Chunk24 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word40State25 : PackedMat2 :=
    ⟨⟨⟨((-6685 : Dyadic) * half ^ 14),
        ((2817 : Dyadic) * half ^ 17)⟩,
       ⟨((-1153 : Dyadic) * half ^ 12),
        ((-16575 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-31709 : Dyadic) * half ^ 16),
        ((31575 : Dyadic) * half ^ 17)⟩,
       ⟨((-14677 : Dyadic) * half ^ 16),
        ((-52515 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((14677 : Dyadic) * half ^ 16),
        ((52515 : Dyadic) * half ^ 17)⟩,
       ⟨((31709 : Dyadic) * half ^ 16),
        ((-31575 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-1153 : Dyadic) * half ^ 12),
        ((-16575 : Dyadic) * half ^ 17)⟩,
       ⟨((-6685 : Dyadic) * half ^ 14),
        ((2817 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word40Step24 :
    word40Chunk24.foldl (fun acc a => a.applyPacked acc)
      word40State24 = word40State25 := by decide +kernel

private def word40Chunk25 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word40State26 : PackedMat2 :=
    ⟨⟨⟨((-7755 : Dyadic) * half ^ 14),
        ((16597 : Dyadic) * half ^ 17)⟩,
       ⟨((23985 : Dyadic) * half ^ 16),
        ((1327 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3095 : Dyadic) * half ^ 15),
        ((30083 : Dyadic) * half ^ 16)⟩,
       ⟨((-97 : Dyadic) * half ^ 14),
        ((-38915 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((99081 : Dyadic) * half ^ 17),
        ((3289 : Dyadic) * half ^ 16)⟩,
       ⟨((-21251 : Dyadic) * half ^ 17),
        ((-2901 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-11289 : Dyadic) * half ^ 17),
        ((55005 : Dyadic) * half ^ 17)⟩,
       ⟨((21905 : Dyadic) * half ^ 17),
        ((-7035 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word40Step25 :
    word40Chunk25.foldl (fun acc a => a.applyPacked acc)
      word40State25 = word40State26 := by decide +kernel

private def word40Chunk26 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word40State27 : PackedMat2 :=
    ⟨⟨⟨((-19409 : Dyadic) * half ^ 16),
        ((4635 : Dyadic) * half ^ 17)⟩,
       ⟨((493 : Dyadic) * half ^ 15),
        ((28591 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((8777 : Dyadic) * half ^ 15),
        ((123127 : Dyadic) * half ^ 18)⟩,
       ⟨((68397 : Dyadic) * half ^ 17),
        ((-14691 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-8777 : Dyadic) * half ^ 15),
        ((-123127 : Dyadic) * half ^ 18)⟩,
       ⟨((68397 : Dyadic) * half ^ 17),
        ((-14691 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-19409 : Dyadic) * half ^ 16),
        ((4635 : Dyadic) * half ^ 17)⟩,
       ⟨((-493 : Dyadic) * half ^ 15),
        ((-28591 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word40Step26 :
    word40Chunk26.foldl (fun acc a => a.applyPacked acc)
      word40State26 = word40State27 := by decide +kernel

private def word40Chunk27 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word40State28 : PackedMat2 :=
    ⟨⟨⟨((-275 : Dyadic) * half ^ 11),
        ((71591 : Dyadic) * half ^ 19)⟩,
       ⟨((-37489 : Dyadic) * half ^ 17),
        ((-238831 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((14559 : Dyadic) * half ^ 18),
        ((89003 : Dyadic) * half ^ 19)⟩,
       ⟨((139455 : Dyadic) * half ^ 18),
        ((-119629 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((15313 : Dyadic) * half ^ 18),
        ((-77007 : Dyadic) * half ^ 18)⟩,
       ⟨((-26079 : Dyadic) * half ^ 16),
        ((3903 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-20905 : Dyadic) * half ^ 16),
        ((-55089 : Dyadic) * half ^ 18)⟩,
       ⟨((155211 : Dyadic) * half ^ 18),
        ((19889 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word40Step27 :
    word40Chunk27.foldl (fun acc a => a.applyPacked acc)
      word40State27 = word40State28 := by decide +kernel

private def word40Chunk28 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word40State29 : PackedMat2 :=
    ⟨⟨⟨((80941 : Dyadic) * half ^ 18),
        ((14417 : Dyadic) * half ^ 20)⟩,
       ⟨((-378347 : Dyadic) * half ^ 19),
        ((46531 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-16759 : Dyadic) * half ^ 16),
        ((38569 : Dyadic) * half ^ 20)⟩,
       ⟨((50141 : Dyadic) * half ^ 19),
        ((407691 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-16759 : Dyadic) * half ^ 16),
        ((38569 : Dyadic) * half ^ 20)⟩,
       ⟨((-50141 : Dyadic) * half ^ 19),
        ((-407691 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-80941 : Dyadic) * half ^ 18),
        ((-14417 : Dyadic) * half ^ 20)⟩,
       ⟨((-378347 : Dyadic) * half ^ 19),
        ((46531 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word40Step28 :
    word40Chunk28.foldl (fun acc a => a.applyPacked acc)
      word40State28 = word40State29 := by decide +kernel

private def word40Chunk29 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word40State30 : PackedMat2 :=
    ⟨⟨⟨((260235 : Dyadic) * half ^ 19),
        ((242287 : Dyadic) * half ^ 21)⟩,
       ⟨((-418121 : Dyadic) * half ^ 20),
        ((-118315 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-180851 : Dyadic) * half ^ 18),
        ((198271 : Dyadic) * half ^ 21)⟩,
       ⟨((-87981 : Dyadic) * half ^ 20),
        ((365341 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-140903 : Dyadic) * half ^ 19),
        ((811385 : Dyadic) * half ^ 21)⟩,
       ⟨((83535 : Dyadic) * half ^ 20),
        ((635423 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((30993 : Dyadic) * half ^ 19),
        ((102349 : Dyadic) * half ^ 21)⟩,
       ⟨((180301 : Dyadic) * half ^ 20),
        ((938591 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word40Step29 :
    word40Chunk29.foldl (fun acc a => a.applyPacked acc)
      word40State29 = word40State30 := by decide +kernel

private def word40Chunk30 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word40State31 : PackedMat2 :=
    ⟨⟨⟨((572427 : Dyadic) * half ^ 21),
        ((381149 : Dyadic) * half ^ 20)⟩,
       ⟨((-321249 : Dyadic) * half ^ 21),
        ((-98921 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((704373 : Dyadic) * half ^ 21),
        ((-846917 : Dyadic) * half ^ 21)⟩,
       ⟨((-878533 : Dyadic) * half ^ 21),
        ((-109989 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((704373 : Dyadic) * half ^ 21),
        ((-846917 : Dyadic) * half ^ 21)⟩,
       ⟨((878533 : Dyadic) * half ^ 21),
        ((109989 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-572427 : Dyadic) * half ^ 21),
        ((-381149 : Dyadic) * half ^ 20)⟩,
       ⟨((-321249 : Dyadic) * half ^ 21),
        ((-98921 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word40Step30 :
    word40Chunk30.foldl (fun acc a => a.applyPacked acc)
      word40State30 = word40State31 := by decide +kernel

private def word40Chunk31 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word40State32 : PackedMat2 :=
    ⟨⟨⟨((2802751 : Dyadic) * half ^ 22),
        ((857349 : Dyadic) * half ^ 22)⟩,
       ⟨((913671 : Dyadic) * half ^ 22),
        ((-87601 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-250845 : Dyadic) * half ^ 22),
        ((939951 : Dyadic) * half ^ 22)⟩,
       ⟨((1444535 : Dyadic) * half ^ 22),
        ((-319653 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((1444535 : Dyadic) * half ^ 22),
        ((-319653 : Dyadic) * half ^ 20)⟩,
       ⟨((-250845 : Dyadic) * half ^ 22),
        ((939951 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-913671 : Dyadic) * half ^ 22),
        ((87601 : Dyadic) * half ^ 20)⟩,
       ⟨((-2802751 : Dyadic) * half ^ 22),
        ((-857349 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word40Step31 :
    word40Chunk31.foldl (fun acc a => a.applyPacked acc)
      word40State31 = word40State32 := by decide +kernel

private def word40Chunk32 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word40State33 : PackedMat2 :=
    ⟨⟨⟨((-1423665 : Dyadic) * half ^ 22),
        ((129305 : Dyadic) * half ^ 20)⟩,
       ⟨((1153647 : Dyadic) * half ^ 21),
        ((1109137 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((64741 : Dyadic) * half ^ 20),
        ((-295905 : Dyadic) * half ^ 20)⟩,
       ⟨((-1620897 : Dyadic) * half ^ 22),
        ((467717 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((124093 : Dyadic) * half ^ 21),
        ((1361933 : Dyadic) * half ^ 23)⟩,
       ⟨((1059527 : Dyadic) * half ^ 21),
        ((-1879861 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1626357 : Dyadic) * half ^ 22),
        ((883629 : Dyadic) * half ^ 23)⟩,
       ⟨((-591917 : Dyadic) * half ^ 22),
        ((-3730959 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word40Step32 :
    word40Chunk32.foldl (fun acc a => a.applyPacked acc)
      word40State32 = word40State33 := by decide +kernel

private def word40Chunk33 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word40State34 : PackedMat2 :=
    ⟨⟨⟨((-867255 : Dyadic) * half ^ 22),
        ((-4616433 : Dyadic) * half ^ 24)⟩,
       ⟨((-3725499 : Dyadic) * half ^ 23),
        ((1570663 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1090393 : Dyadic) * half ^ 22),
        ((3410673 : Dyadic) * half ^ 24)⟩,
       ⟨((-675619 : Dyadic) * half ^ 23),
        ((-7818315 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2203821 : Dyadic) * half ^ 23),
        ((-2856405 : Dyadic) * half ^ 24)⟩,
       ⟨((2807247 : Dyadic) * half ^ 22),
        ((-1505167 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1522885 : Dyadic) * half ^ 23),
        ((5460009 : Dyadic) * half ^ 24)⟩,
       ⟨((773387 : Dyadic) * half ^ 21),
        ((-1990989 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word40Step33 :
    word40Chunk33.foldl (fun acc a => a.applyPacked acc)
      word40State33 = word40State34 := by decide +kernel

private def word40Chunk34 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word40State35 : PackedMat2 :=
    ⟨⟨⟨((-1566553 : Dyadic) * half ^ 24),
        ((-6428999 : Dyadic) * half ^ 24)⟩,
       ⟨((-2344633 : Dyadic) * half ^ 24),
        ((-4328379 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((7811791 : Dyadic) * half ^ 24),
        ((14735 : Dyadic) * half ^ 18)⟩,
       ⟨((-8264591 : Dyadic) * half ^ 24),
        ((1668967 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1197447 : Dyadic) * half ^ 23),
        ((-8038191 : Dyadic) * half ^ 24)⟩,
       ⟨((2140487 : Dyadic) * half ^ 23),
        ((-7075 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-525155 : Dyadic) * half ^ 22),
        ((24315 : Dyadic) * half ^ 20)⟩,
       ⟨((5378689 : Dyadic) * half ^ 23),
        ((1955593 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word40Step34 :
    word40Chunk34.foldl (fun acc a => a.applyPacked acc)
      word40State34 = word40State35 := by decide +kernel

private def word40Chunk35 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word40State36 : PackedMat2 :=
    ⟨⟨⟨((-6454025 : Dyadic) * half ^ 25),
        ((113159 : Dyadic) * half ^ 18)⟩,
       ⟨((-2167507 : Dyadic) * half ^ 25),
        ((-3113173 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((402539 : Dyadic) * half ^ 25),
        ((2021399 : Dyadic) * half ^ 23)⟩,
       ⟨((21923909 : Dyadic) * half ^ 25),
        ((3807705 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-21923909 : Dyadic) * half ^ 25),
        ((-3807705 : Dyadic) * half ^ 25)⟩,
       ⟨((-402539 : Dyadic) * half ^ 25),
        ((-2021399 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2167507 : Dyadic) * half ^ 25),
        ((-3113173 : Dyadic) * half ^ 25)⟩,
       ⟨((-6454025 : Dyadic) * half ^ 25),
        ((113159 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word40Step35 :
    word40Chunk35.foldl (fun acc a => a.applyPacked acc)
      word40State35 = word40State36 := by decide +kernel

private def word40Chunk36 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word40State37 : PackedMat2 :=
    ⟨⟨⟨((-11890631 : Dyadic) * half ^ 26),
        ((-20899947 : Dyadic) * half ^ 26)⟩,
       ⟨((7409399 : Dyadic) * half ^ 26),
        ((-12764607 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-17665945 : Dyadic) * half ^ 26),
        ((1729791 : Dyadic) * half ^ 26)⟩,
       ⟨((42558553 : Dyadic) * half ^ 26),
        ((-169173 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2406483 : Dyadic) * half ^ 26),
        ((30112249 : Dyadic) * half ^ 26)⟩,
       ⟨((1053099 : Dyadic) * half ^ 26),
        ((388947 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((4629267 : Dyadic) * half ^ 26),
        ((-9650015 : Dyadic) * half ^ 26)⟩,
       ⟨((46429161 : Dyadic) * half ^ 26),
        ((280077 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word40Step36 :
    word40Chunk36.foldl (fun acc a => a.applyPacked acc)
      word40State36 = word40State37 := by decide +kernel

private def word40Chunk37 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word40State38 : PackedMat2 :=
    ⟨⟨⟨((-7885837 : Dyadic) * half ^ 25),
        ((1488599 : Dyadic) * half ^ 24)⟩,
       ⟨((-10195253 : Dyadic) * half ^ 26),
        ((-1770905 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-25494801 : Dyadic) * half ^ 26),
        ((-2368075 : Dyadic) * half ^ 23)⟩,
       ⟨((-3303591 : Dyadic) * half ^ 24),
        ((34908779 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-15964179 : Dyadic) * half ^ 26),
        ((38709165 : Dyadic) * half ^ 27)⟩,
       ⟨((53853379 : Dyadic) * half ^ 26),
        ((12280437 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-141153 : Dyadic) * half ^ 23),
        ((-25966927 : Dyadic) * half ^ 27)⟩,
       ⟨((203719 : Dyadic) * half ^ 20),
        ((-5576421 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word40Step37 :
    word40Chunk37.foldl (fun acc a => a.applyPacked acc)
      word40State37 = word40State38 := by decide +kernel

private def word40Chunk38 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word40State39 : PackedMat2 :=
    ⟨⟨⟨((4647 : Dyadic) * half ^ 14),
        ((-56085273 : Dyadic) * half ^ 28)⟩,
       ⟨((-83792293 : Dyadic) * half ^ 27),
        ((-20762151 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-5886403 : Dyadic) * half ^ 25),
        ((-94840233 : Dyadic) * half ^ 28)⟩,
       ⟨((31284741 : Dyadic) * half ^ 27),
        ((-58741507 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-5886403 : Dyadic) * half ^ 25),
        ((-94840233 : Dyadic) * half ^ 28)⟩,
       ⟨((-31284741 : Dyadic) * half ^ 27),
        ((58741507 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-4647 : Dyadic) * half ^ 14),
        ((56085273 : Dyadic) * half ^ 28)⟩,
       ⟨((-83792293 : Dyadic) * half ^ 27),
        ((-20762151 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word40Step38 :
    word40Chunk38.foldl (fun acc a => a.applyPacked acc)
      word40State38 = word40State39 := by decide +kernel

private def word40Chunk39 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word40State40 : PackedMat2 :=
    ⟨⟨⟨((32511 : Dyadic) * half ^ 21),
        ((1029183 : Dyadic) * half ^ 28)⟩,
       ⟨((-3494667 : Dyadic) * half ^ 26),
        ((-5154011 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-82096599 : Dyadic) * half ^ 27),
        ((16933889 : Dyadic) * half ^ 27)⟩,
       ⟨((-41519853 : Dyadic) * half ^ 26),
        ((-26516451 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-60384229 : Dyadic) * half ^ 28),
        ((-943107 : Dyadic) * half ^ 28)⟩,
       ⟨((7351327 : Dyadic) * half ^ 28),
        ((-165136305 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((83493359 : Dyadic) * half ^ 28),
        ((4535019 : Dyadic) * half ^ 27)⟩,
       ⟨((81434993 : Dyadic) * half ^ 28),
        ((2454315 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word40Step39 :
    word40Chunk39.foldl (fun acc a => a.applyPacked acc)
      word40State39 = word40State40 := by decide +kernel

private def word40Chunk40 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word40State41 : PackedMat2 :=
    ⟨⟨⟨((107144593 : Dyadic) * half ^ 28),
        ((-180827761 : Dyadic) * half ^ 29)⟩,
       ⟨((-152694397 : Dyadic) * half ^ 28),
        ((-72301681 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-5365529 : Dyadic) * half ^ 26),
        ((68240283 : Dyadic) * half ^ 28)⟩,
       ⟨((25391393 : Dyadic) * half ^ 28),
        ((8812255 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-5365529 : Dyadic) * half ^ 26),
        ((68240283 : Dyadic) * half ^ 28)⟩,
       ⟨((-25391393 : Dyadic) * half ^ 28),
        ((-8812255 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-107144593 : Dyadic) * half ^ 28),
        ((180827761 : Dyadic) * half ^ 29)⟩,
       ⟨((-152694397 : Dyadic) * half ^ 28),
        ((-72301681 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word40Step40 :
    word40Chunk40.foldl (fun acc a => a.applyPacked acc)
      word40State40 = word40State41 := by decide +kernel

private def word40Chunk41 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word40State42 : PackedMat2 :=
    ⟨⟨⟨((-201559549 : Dyadic) * half ^ 30),
        ((354963271 : Dyadic) * half ^ 30)⟩,
       ⟨((-202585849 : Dyadic) * half ^ 30),
        ((-219681523 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-103252777 : Dyadic) * half ^ 30),
        ((-97286291 : Dyadic) * half ^ 30)⟩,
       ⟨((-61524121 : Dyadic) * half ^ 30),
        ((223551171 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-61524121 : Dyadic) * half ^ 30),
        ((223551171 : Dyadic) * half ^ 29)⟩,
       ⟨((-103252777 : Dyadic) * half ^ 30),
        ((-97286291 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((202585849 : Dyadic) * half ^ 30),
        ((219681523 : Dyadic) * half ^ 29)⟩,
       ⟨((201559549 : Dyadic) * half ^ 30),
        ((-354963271 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word40Step41 :
    word40Chunk41.foldl (fun acc a => a.applyPacked acc)
      word40State41 = word40State42 := by decide +kernel

private def word40Chunk42 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word40State43 : PackedMat2 :=
    ⟨⟨⟨((425494135 : Dyadic) * half ^ 30),
        ((684905839 : Dyadic) * half ^ 31)⟩,
       ⟨((-591769209 : Dyadic) * half ^ 30),
        ((55091131 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((17384347 : Dyadic) * half ^ 29),
        ((-110992073 : Dyadic) * half ^ 31)⟩,
       ⟨((31015983 : Dyadic) * half ^ 26),
        ((-513773683 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((156191439 : Dyadic) * half ^ 29),
        ((-265512211 : Dyadic) * half ^ 30)⟩,
       ⟨((-201390805 : Dyadic) * half ^ 30),
        ((230743517 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((369998485 : Dyadic) * half ^ 30),
        ((-83137537 : Dyadic) * half ^ 30)⟩,
       ⟨((157453677 : Dyadic) * half ^ 29),
        ((63578959 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word40Step42 :
    word40Chunk42.foldl (fun acc a => a.applyPacked acc)
      word40State42 = word40State43 := by decide +kernel

private def word40Chunk43 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word40State44 : PackedMat2 :=
    ⟨⟨⟨((56960775 : Dyadic) * half ^ 29),
        ((135878349 : Dyadic) * half ^ 32)⟩,
       ⟨((-144396433 : Dyadic) * half ^ 29),
        ((849687999 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((411311431 : Dyadic) * half ^ 31),
        ((-1881590243 : Dyadic) * half ^ 32)⟩,
       ⟨((749470217 : Dyadic) * half ^ 31),
        ((1646133853 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((749470217 : Dyadic) * half ^ 31),
        ((1646133853 : Dyadic) * half ^ 32)⟩,
       ⟨((411311431 : Dyadic) * half ^ 31),
        ((-1881590243 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((144396433 : Dyadic) * half ^ 29),
        ((-849687999 : Dyadic) * half ^ 32)⟩,
       ⟨((-56960775 : Dyadic) * half ^ 29),
        ((-135878349 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word40Step43 :
    word40Chunk43.foldl (fun acc a => a.applyPacked acc)
      word40State43 = word40State44 := by decide +kernel

private def word40Chunk44 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word40State45 : PackedMat2 :=
    ⟨⟨⟨((92788503 : Dyadic) * half ^ 29),
        ((1465996337 : Dyadic) * half ^ 33)⟩,
       ⟨((1709523437 : Dyadic) * half ^ 32),
        ((-2945142525 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-586764491 : Dyadic) * half ^ 30),
        ((-952390395 : Dyadic) * half ^ 33)⟩,
       ⟨((-683730081 : Dyadic) * half ^ 32),
        ((-2502820797 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((431901399 : Dyadic) * half ^ 30),
        ((3030788045 : Dyadic) * half ^ 33)⟩,
       ⟨((-775215201 : Dyadic) * half ^ 32),
        ((1663327883 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-369786547 : Dyadic) * half ^ 31),
        ((2451831461 : Dyadic) * half ^ 33)⟩,
       ⟨((2205569431 : Dyadic) * half ^ 32),
        ((-967215413 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word40Step44 :
    word40Chunk44.foldl (fun acc a => a.applyPacked acc)
      word40State44 = word40State45 := by decide +kernel

private def word40Chunk45 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word40State46 : PackedMat2 :=
    ⟨⟨⟨((740671783 : Dyadic) * half ^ 32),
        ((885679705 : Dyadic) * half ^ 32)⟩,
       ⟨((-620500927 : Dyadic) * half ^ 31),
        ((4263149103 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((383303769 : Dyadic) * half ^ 30),
        ((2121857385 : Dyadic) * half ^ 33)⟩,
       ⟨((-74085253 : Dyadic) * half ^ 29),
        ((-38243329 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((383303769 : Dyadic) * half ^ 30),
        ((2121857385 : Dyadic) * half ^ 33)⟩,
       ⟨((74085253 : Dyadic) * half ^ 29),
        ((38243329 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-740671783 : Dyadic) * half ^ 32),
        ((-885679705 : Dyadic) * half ^ 32)⟩,
       ⟨((-620500927 : Dyadic) * half ^ 31),
        ((4263149103 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word40Step45 :
    word40Chunk45.foldl (fun acc a => a.applyPacked acc)
      word40State45 = word40State46 := by decide +kernel

private def word40Chunk46 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word40State47 : PackedMat2 :=
    ⟨⟨⟨((1575300601 : Dyadic) * half ^ 34),
        ((-1930977491 : Dyadic) * half ^ 34)⟩,
       ⟨((11183219835 : Dyadic) * half ^ 34),
        ((-442083309 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-16765757 : Dyadic) * half ^ 34),
        ((-543533167 : Dyadic) * half ^ 34)⟩,
       ⟨((2667861349 : Dyadic) * half ^ 34),
        ((2137331517 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((9092859235 : Dyadic) * half ^ 34),
        ((1342313553 : Dyadic) * half ^ 34)⟩,
       ⟨((8005792901 : Dyadic) * half ^ 34),
        ((331386949 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-162644255 : Dyadic) * half ^ 34),
        ((-4803959617 : Dyadic) * half ^ 34)⟩,
       ⟨((3699310727 : Dyadic) * half ^ 34),
        ((-3189630109 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word40Step46 :
    word40Chunk46.foldl (fun acc a => a.applyPacked acc)
      word40State46 = word40State47 := by decide +kernel

private def word40Chunk47 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word40State48 : PackedMat2 :=
    ⟨⟨⟨((-5600022299 : Dyadic) * half ^ 33),
        ((2437151205 : Dyadic) * half ^ 34)⟩,
       ⟨((2457685895 : Dyadic) * half ^ 34),
        ((-110449453 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((2741905025 : Dyadic) * half ^ 34),
        ((-1481675911 : Dyadic) * half ^ 34)⟩,
       ⟨((2011161025 : Dyadic) * half ^ 33),
        ((982960417 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-2011161025 : Dyadic) * half ^ 33),
        ((-982960417 : Dyadic) * half ^ 31)⟩,
       ⟨((-2741905025 : Dyadic) * half ^ 34),
        ((1481675911 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((2457685895 : Dyadic) * half ^ 34),
        ((-110449453 : Dyadic) * half ^ 34)⟩,
       ⟨((-5600022299 : Dyadic) * half ^ 33),
        ((2437151205 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word40Step47 :
    word40Chunk47.foldl (fun acc a => a.applyPacked acc)
      word40State47 = word40State48 := by decide +kernel

private def word40Chunk48 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word40State49 : PackedMat2 :=
    ⟨⟨⟨((7267637311 : Dyadic) * half ^ 35),
        ((-34038500669 : Dyadic) * half ^ 36)⟩,
       ⟨((-7036466883 : Dyadic) * half ^ 34),
        ((-683805565 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-13651900427 : Dyadic) * half ^ 35),
        ((-14265330781 : Dyadic) * half ^ 36)⟩,
       ⟨((-3049227099 : Dyadic) * half ^ 34),
        ((-7052189009 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-10658759895 : Dyadic) * half ^ 35),
        ((-19750354625 : Dyadic) * half ^ 36)⟩,
       ⟨((-1803285443 : Dyadic) * half ^ 34),
        ((-7553446229 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((17361153117 : Dyadic) * half ^ 35),
        ((6805296455 : Dyadic) * half ^ 36)⟩,
       ⟨((521167111 : Dyadic) * half ^ 30),
        ((-21340571077 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word40Step48 :
    word40Chunk48.foldl (fun acc a => a.applyPacked acc)
      word40State48 = word40State49 := by decide +kernel

private def word40Chunk49 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word40State50 : PackedMat2 :=
    ⟨⟨⟨((-1283175687 : Dyadic) * half ^ 32),
        ((18156261343 : Dyadic) * half ^ 36)⟩,
       ⟨((186423537 : Dyadic) * half ^ 35),
        ((-11928359447 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((4188117107 : Dyadic) * half ^ 33),
        ((642792813 : Dyadic) * half ^ 32)⟩,
       ⟨((-383714643 : Dyadic) * half ^ 34),
        ((-24152033737 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-4188117107 : Dyadic) * half ^ 33),
        ((-642792813 : Dyadic) * half ^ 32)⟩,
       ⟨((-383714643 : Dyadic) * half ^ 34),
        ((-24152033737 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-1283175687 : Dyadic) * half ^ 32),
        ((18156261343 : Dyadic) * half ^ 36)⟩,
       ⟨((-186423537 : Dyadic) * half ^ 35),
        ((11928359447 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word40Step49 :
    word40Chunk49.foldl (fun acc a => a.applyPacked acc)
      word40State49 = word40State50 := by decide +kernel

private def word40Chunk50 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word40State51 : PackedMat2 :=
    ⟨⟨⟨((49807024341 : Dyadic) * half ^ 37),
        ((-1582391405 : Dyadic) * half ^ 34)⟩,
       ⟨((-102680967525 : Dyadic) * half ^ 37),
        ((1009210703 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((16403771037 : Dyadic) * half ^ 37),
        ((23788994317 : Dyadic) * half ^ 36)⟩,
       ⟨((27213849619 : Dyadic) * half ^ 37),
        ((-1702002597 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-27213849619 : Dyadic) * half ^ 37),
        ((1702002597 : Dyadic) * half ^ 37)⟩,
       ⟨((-16403771037 : Dyadic) * half ^ 37),
        ((-23788994317 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-102680967525 : Dyadic) * half ^ 37),
        ((1009210703 : Dyadic) * half ^ 37)⟩,
       ⟨((49807024341 : Dyadic) * half ^ 37),
        ((-1582391405 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word40Step50 :
    word40Chunk50.foldl (fun acc a => a.applyPacked acc)
      word40State50 = word40State51 := by decide +kernel

private def word40Chunk51 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word40State52 : PackedMat2 :=
    ⟨⟨⟨((-1667596199 : Dyadic) * half ^ 36),
        ((33042553071 : Dyadic) * half ^ 37)⟩,
       ⟨((45779040049 : Dyadic) * half ^ 37),
        ((-8675068561 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-2993774981 : Dyadic) * half ^ 37),
        ((-9714749615 : Dyadic) * half ^ 35)⟩,
       ⟨((2674695689 : Dyadic) * half ^ 35),
        ((36833199373 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((17403700143 : Dyadic) * half ^ 36),
        ((7705007775 : Dyadic) * half ^ 38)⟩,
       ⟨((-56262698603 : Dyadic) * half ^ 36),
        ((-13692557737 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-15692415949 : Dyadic) * half ^ 37),
        ((-42443847651 : Dyadic) * half ^ 38)⟩,
       ⟨((-50392690193 : Dyadic) * half ^ 37),
        ((49114232447 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word40Step51 :
    word40Chunk51.foldl (fun acc a => a.applyPacked acc)
      word40State51 = word40State52 := by decide +kernel

private def word40Chunk52 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word40State53 : PackedMat2 :=
    ⟨⟨⟨((55113466379 : Dyadic) * half ^ 38),
        ((35734897223 : Dyadic) * half ^ 39)⟩,
       ⟨((-18820107981 : Dyadic) * half ^ 35),
        ((143950628503 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-104109195625 : Dyadic) * half ^ 38),
        ((-195764195105 : Dyadic) * half ^ 39)⟩,
       ⟨((46973166159 : Dyadic) * half ^ 37),
        ((-7206198961 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((104109195625 : Dyadic) * half ^ 38),
        ((195764195105 : Dyadic) * half ^ 39)⟩,
       ⟨((46973166159 : Dyadic) * half ^ 37),
        ((-7206198961 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((55113466379 : Dyadic) * half ^ 38),
        ((35734897223 : Dyadic) * half ^ 39)⟩,
       ⟨((18820107981 : Dyadic) * half ^ 35),
        ((-143950628503 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word40Step52 :
    word40Chunk52.foldl (fun acc a => a.applyPacked acc)
      word40State52 = word40State53 := by decide +kernel

private def word40Chunk53 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word40State54 : PackedMat2 :=
    ⟨⟨⟨((135618529901 : Dyadic) * half ^ 39),
        ((56011083111 : Dyadic) * half ^ 38)⟩,
       ⟨((194031896057 : Dyadic) * half ^ 39),
        ((-26728249007 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-138224000405 : Dyadic) * half ^ 39),
        ((105294598175 : Dyadic) * half ^ 39)⟩,
       ⟨((-389383487839 : Dyadic) * half ^ 39),
        ((-51636730991 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((78465664583 : Dyadic) * half ^ 38),
        ((125579743717 : Dyadic) * half ^ 39)⟩,
       ⟨((-3353616699 : Dyadic) * half ^ 35),
        ((131901872061 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-109467581125 : Dyadic) * half ^ 38),
        ((14603341539 : Dyadic) * half ^ 38)⟩,
       ⟨((2554585097 : Dyadic) * half ^ 38),
        ((164825212979 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word40Step53 :
    word40Chunk53.foldl (fun acc a => a.applyPacked acc)
      word40State53 = word40State54 := by decide +kernel

private def word40Chunk54 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word40State55 : PackedMat2 :=
    ⟨⟨⟨((186943765553 : Dyadic) * half ^ 40),
        ((184055634823 : Dyadic) * half ^ 39)⟩,
       ⟨((-131865329339 : Dyadic) * half ^ 40),
        ((569857806401 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((381037521939 : Dyadic) * half ^ 40),
        ((-1793143323 : Dyadic) * half ^ 35)⟩,
       ⟨((-236388292193 : Dyadic) * half ^ 40),
        ((-119263676685 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-236388292193 : Dyadic) * half ^ 40),
        ((-119263676685 : Dyadic) * half ^ 40)⟩,
       ⟨((381037521939 : Dyadic) * half ^ 40),
        ((-1793143323 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((131865329339 : Dyadic) * half ^ 40),
        ((-569857806401 : Dyadic) * half ^ 40)⟩,
       ⟨((-186943765553 : Dyadic) * half ^ 40),
        ((-184055634823 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word40Step54 :
    word40Chunk54.foldl (fun acc a => a.applyPacked acc)
      word40State54 = word40State55 := by decide +kernel

private def word40Chunk55 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word40State56 : PackedMat2 :=
    ⟨⟨⟨((138059520103 : Dyadic) * half ^ 38),
        ((-263650364163 : Dyadic) * half ^ 41)⟩,
       ⟨((29550683013 : Dyadic) * half ^ 36),
        ((293626526643 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-5119104909 : Dyadic) * half ^ 40),
        ((1070159005025 : Dyadic) * half ^ 41)⟩,
       ⟨((164726967061 : Dyadic) * half ^ 40),
        ((74342391117 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-572250698071 : Dyadic) * half ^ 40),
        ((-19950982769 : Dyadic) * half ^ 38)⟩,
       ⟨((-248954153477 : Dyadic) * half ^ 39),
        ((84923035985 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((1873510155 : Dyadic) * half ^ 37),
        ((256262252155 : Dyadic) * half ^ 39)⟩,
       ⟨((-278638445403 : Dyadic) * half ^ 40),
        ((19856788051 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word40Step55 :
    word40Chunk55.foldl (fun acc a => a.applyPacked acc)
      word40State55 = word40State56 := by decide +kernel

private def word40Chunk56 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word40State57 : PackedMat2 :=
    ⟨⟨⟨((-413899159661 : Dyadic) * half ^ 41),
        ((-1099296831247 : Dyadic) * half ^ 42)⟩,
       ⟨((-44325421731 : Dyadic) * half ^ 41),
        ((-572463819103 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((448071492977 : Dyadic) * half ^ 40),
        ((1268376419305 : Dyadic) * half ^ 42)⟩,
       ⟨((532570465845 : Dyadic) * half ^ 40),
        ((-1518127149637 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((532570465845 : Dyadic) * half ^ 40),
        ((-1518127149637 : Dyadic) * half ^ 42)⟩,
       ⟨((448071492977 : Dyadic) * half ^ 40),
        ((1268376419305 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((44325421731 : Dyadic) * half ^ 41),
        ((572463819103 : Dyadic) * half ^ 42)⟩,
       ⟨((413899159661 : Dyadic) * half ^ 41),
        ((1099296831247 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word40Step56 :
    word40Chunk56.foldl (fun acc a => a.applyPacked acc)
      word40State56 = word40State57 := by decide +kernel

private def word40Chunk57 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word40State58 : PackedMat2 :=
    ⟨⟨⟨((-174643227637 : Dyadic) * half ^ 41),
        ((-967683146701 : Dyadic) * half ^ 41)⟩,
       ⟨((-79481597573 : Dyadic) * half ^ 39),
        ((-1145583380467 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-57190283429 : Dyadic) * half ^ 40),
        ((-1125214455489 : Dyadic) * half ^ 42)⟩,
       ⟨((559825407955 : Dyadic) * half ^ 40),
        ((-185529376775 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((383096948389 : Dyadic) * half ^ 42),
        ((77126961423 : Dyadic) * half ^ 38)⟩,
       ⟨((-1867331962589 : Dyadic) * half ^ 42),
        ((251317562263 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-789782912935 : Dyadic) * half ^ 42),
        ((143283162655 : Dyadic) * half ^ 42)⟩,
       ⟨((3080949673869 : Dyadic) * half ^ 42),
        ((492569617929 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word40Step57 :
    word40Chunk57.foldl (fun acc a => a.applyPacked acc)
      word40State57 = word40State58 := by decide +kernel

private def word40Chunk58 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word40State59 : PackedMat2 :=
    ⟨⟨⟨((355144725271 : Dyadic) * half ^ 43),
        ((231934006117 : Dyadic) * half ^ 43)⟩,
       ⟨((-5279543336363 : Dyadic) * half ^ 43),
        ((-1320367937251 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((2653157350885 : Dyadic) * half ^ 43),
        ((-841078311537 : Dyadic) * half ^ 41)⟩,
       ⟨((669420876021 : Dyadic) * half ^ 43),
        ((87423631905 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((2653157350885 : Dyadic) * half ^ 43),
        ((-841078311537 : Dyadic) * half ^ 41)⟩,
       ⟨((-669420876021 : Dyadic) * half ^ 43),
        ((-87423631905 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-355144725271 : Dyadic) * half ^ 43),
        ((-231934006117 : Dyadic) * half ^ 43)⟩,
       ⟨((-5279543336363 : Dyadic) * half ^ 43),
        ((-1320367937251 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word40Step58 :
    word40Chunk58.foldl (fun acc a => a.applyPacked acc)
      word40State58 = word40State59 := by decide +kernel

private def word40Chunk59 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word40State60 : PackedMat2 :=
    ⟨⟨⟨((-646276778811 : Dyadic) * half ^ 43),
        ((744512362035 : Dyadic) * half ^ 41)⟩,
       ⟨((-2739765969681 : Dyadic) * half ^ 43),
        ((-6476423086159 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-2533935637593 : Dyadic) * half ^ 43),
        ((740423889759 : Dyadic) * half ^ 44)⟩,
       ⟨((-2265162619209 : Dyadic) * half ^ 42),
        ((331609985323 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((2533935637593 : Dyadic) * half ^ 43),
        ((-740423889759 : Dyadic) * half ^ 44)⟩,
       ⟨((-2265162619209 : Dyadic) * half ^ 42),
        ((331609985323 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-646276778811 : Dyadic) * half ^ 43),
        ((744512362035 : Dyadic) * half ^ 41)⟩,
       ⟨((2739765969681 : Dyadic) * half ^ 43),
        ((6476423086159 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word40Step59 :
    word40Chunk59.foldl (fun acc a => a.applyPacked acc)
      word40State59 = word40State60 := by decide +kernel

private def word40Chunk60 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word40State61 : PackedMat2 :=
    ⟨⟨⟨((-1401217083325 : Dyadic) * half ^ 45),
        ((4893451561853 : Dyadic) * half ^ 44)⟩,
       ⟨((-10143957002587 : Dyadic) * half ^ 45),
        ((-5266693263333 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((8678636531615 : Dyadic) * half ^ 45),
        ((-3733203941279 : Dyadic) * half ^ 43)⟩,
       ⟨((-17695597698559 : Dyadic) * half ^ 45),
        ((-5079508914641 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((17695597698559 : Dyadic) * half ^ 45),
        ((5079508914641 : Dyadic) * half ^ 45)⟩,
       ⟨((-8678636531615 : Dyadic) * half ^ 45),
        ((3733203941279 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-10143957002587 : Dyadic) * half ^ 45),
        ((-5266693263333 : Dyadic) * half ^ 45)⟩,
       ⟨((-1401217083325 : Dyadic) * half ^ 45),
        ((4893451561853 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word40Step60 :
    word40Chunk60.foldl (fun acc a => a.applyPacked acc)
      word40State60 = word40State61 := by decide +kernel

private def word40Chunk61 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word40State62 : PackedMat2 :=
    ⟨⟨⟨((-2187489042005 : Dyadic) * half ^ 46),
        ((36731160424205 : Dyadic) * half ^ 46)⟩,
       ⟨((-14237249122283 : Dyadic) * half ^ 46),
        ((2516813849927 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((11385772394681 : Dyadic) * half ^ 46),
        ((-8050956869225 : Dyadic) * half ^ 46)⟩,
       ⟨((-38032217350849 : Dyadic) * half ^ 46),
        ((-4145766648243 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-240576427261 : Dyadic) * half ^ 46),
        ((-24708994872765 : Dyadic) * half ^ 46)⟩,
       ⟨((-16342490165711 : Dyadic) * half ^ 46),
        ((-3330805619521 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((26663905024497 : Dyadic) * half ^ 46),
        ((6024880040139 : Dyadic) * half ^ 46)⟩,
       ⟨((-46798415823913 : Dyadic) * half ^ 46),
        ((256636533817 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word40Step61 :
    word40Chunk61.foldl (fun acc a => a.applyPacked acc)
      word40State61 = word40State62 := by decide +kernel

private def word40Chunk62 : List Letter := [.s, .t, .h, .s]
private def word40State63 : PackedMat2 :=
    ⟨⟨⟨((45022693720691 : Dyadic) * half ^ 46),
        ((8961182077211 : Dyadic) * half ^ 45)⟩,
       ⟨((18118212268933 : Dyadic) * half ^ 46),
        ((-6405755379241 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((2016298530483 : Dyadic) * half ^ 46),
        ((-1425738363801 : Dyadic) * half ^ 46)⟩,
       ⟨((28439627127719 : Dyadic) * half ^ 46),
        ((-20109853196427 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-2016298530483 : Dyadic) * half ^ 46),
        ((1425738363801 : Dyadic) * half ^ 46)⟩,
       ⟨((28439627127719 : Dyadic) * half ^ 46),
        ((-20109853196427 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((45022693720691 : Dyadic) * half ^ 46),
        ((8961182077211 : Dyadic) * half ^ 45)⟩,
       ⟨((-18118212268933 : Dyadic) * half ^ 46),
        ((6405755379241 : Dyadic) * half ^ 45)⟩⟩⟩
private lemma word40Step62 :
    word40Chunk62.foldl (fun acc a => a.applyPacked acc)
      word40State62 = word40State63 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word40_check : check word40 40 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word40 = word40State63.toMatrix := by
    unfold evalRingPacked
    change ((
      word40Chunk0 ++ word40Chunk1 ++ word40Chunk2 ++ word40Chunk3 ++
      word40Chunk4 ++ word40Chunk5 ++ word40Chunk6 ++ word40Chunk7 ++
      word40Chunk8 ++ word40Chunk9 ++ word40Chunk10 ++ word40Chunk11 ++
      word40Chunk12 ++ word40Chunk13 ++ word40Chunk14 ++ word40Chunk15 ++
      word40Chunk16 ++ word40Chunk17 ++ word40Chunk18 ++ word40Chunk19 ++
      word40Chunk20 ++ word40Chunk21 ++ word40Chunk22 ++ word40Chunk23 ++
      word40Chunk24 ++ word40Chunk25 ++ word40Chunk26 ++ word40Chunk27 ++
      word40Chunk28 ++ word40Chunk29 ++ word40Chunk30 ++ word40Chunk31 ++
      word40Chunk32 ++ word40Chunk33 ++ word40Chunk34 ++ word40Chunk35 ++
      word40Chunk36 ++ word40Chunk37 ++ word40Chunk38 ++ word40Chunk39 ++
      word40Chunk40 ++ word40Chunk41 ++ word40Chunk42 ++ word40Chunk43 ++
      word40Chunk44 ++ word40Chunk45 ++ word40Chunk46 ++ word40Chunk47 ++
      word40Chunk48 ++ word40Chunk49 ++ word40Chunk50 ++ word40Chunk51 ++
      word40Chunk52 ++ word40Chunk53 ++ word40Chunk54 ++ word40Chunk55 ++
      word40Chunk56 ++ word40Chunk57 ++ word40Chunk58 ++ word40Chunk59 ++
      word40Chunk60 ++ word40Chunk61 ++ word40Chunk62
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word40Step0, word40Step1, word40Step2, word40Step3, word40Step4,
      word40Step5, word40Step6, word40Step7, word40Step8, word40Step9,
      word40Step10, word40Step11, word40Step12, word40Step13, word40Step14,
      word40Step15, word40Step16, word40Step17, word40Step18, word40Step19,
      word40Step20, word40Step21, word40Step22, word40Step23, word40Step24,
      word40Step25, word40Step26, word40Step27, word40Step28, word40Step29,
      word40Step30, word40Step31, word40Step32, word40Step33, word40Step34,
      word40Step35, word40Step36, word40Step37, word40Step38, word40Step39,
      word40Step40, word40Step41, word40Step42, word40Step43, word40Step44,
      word40Step45, word40Step46, word40Step47, word40Step48, word40Step49,
      word40Step50, word40Step51, word40Step52, word40Step53, word40Step54,
      word40Step55, word40Step56, word40Step57, word40Step58, word40Step59,
      word40Step60, word40Step61, word40Step62]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
