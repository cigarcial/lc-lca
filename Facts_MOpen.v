(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the definitions for the processes.
*)
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.


From Papercod Require Import Defs_Tactics.
From Papercod Require Import Defs_GeneralGrammar.
From Papercod Require Import Facts_Names.
From Papercod Require Import Facts_Process.




(**
*)
Lemma List_Sk_char :
forall (k : nat)(L : list nat),
(length L) = S k -> 
(exists (x : nat)(L0 : list nat), L = x :: L0 /\ (length L0) = k).
Proof.
  intros.
  destruct L.
  + simpl in H.
    lia.
  + exists n.
    exists L.
    auto.
Qed.
#[global]
Hint Resolve List_Sk_char : Piull.


(**
*)
Ltac ListEasyInduction k L H HL IHk:=
  induction k; intros;
  try rewrite length_zero_iff_nil in H;
    try rewrite H;
   try specialize (List_Sk_char k L H) as HL;
    try destruct HL as [x0 [ L0 [HL HT]]];
    try rewrite HL;
    try simpl;
    try rewrite IHk; auto.


(**
*)
Lemma MOpen_Name_FName :
forall (k x : nat)( L : list nat), 
(length L) = k -> 
MOpen_Name_Rec k L (FName x) = FName x.
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Name_FName : Piull.


(**
*)
Lemma MOpen_Name_BName_Gt :
forall (k i : nat)(L : list nat),
(length L) = k -> k <= i -> 
MOpen_Name_Rec k L (BName i) = (BName i).
Proof.
  intro.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; try lia.
    rewrite Open_Name_BName_Gt; Piauto.
Qed.
#[global]
Hint Resolve MOpen_Name_BName_Gt : Piull.


(**
*)
Lemma MOpen_Name_Result : 
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> lcaName k x -> 
exists (x0 : nat), ( MOpen_Name_Rec k L x) = FName x0.
Proof.
  induction k; intros.
  + apply Lca_Zero_Lc_Name in H0.
    apply length_zero_iff_nil in H.
    rewrite H.
    simpl.
    inversions H0.
    exists x0.
    auto.
  + inversions H0.
    - rewrite MOpen_Name_FName;
       try exists x0; auto.
    - specialize (List_Sk_char k L H) as HL.
      destruct HL as [x [ L0 [HL HT]]].
      rewrite HL.
      simpl.
      assert (HA : k = i \/ i < k). { lia. }
      destruct HA.
      * assert ( HB: k <= i ). { lia. }
        rewrite MOpen_Name_BName_Gt; auto.
        rewrite Open_Name_BName_Eq; auto.
        exists x; auto.
      * assert (Hk : lcaName k ((BName i)) ).
        constructor; auto.
        specialize (IHk L0 (BName i) HT Hk).
        destruct IHk.
        rewrite H3.
        simpl.
        exists x0.
        auto.
Qed.
#[global]
Hint Resolve MOpen_Name_Result : Piull.


(**
*)
Lemma MOpen_Name_Rec_lc :
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> lcaName k x -> 
lcName ( MOpen_Name_Rec k L x).
Proof.
  intros.
  specialize (MOpen_Name_Result k L x H H0) as HA.
  destruct HA as [x0 HA].
  rewrite HA.
  constructor.
Qed.
#[global]
Hint Resolve MOpen_Name_Rec_lc : Piull.


(**
*)
Lemma M2Open_MOpen :
forall (k x : nat)(L : list nat)(P : Process),
(length L) = k -> 
({0 ~> x} M2Open_Rec k L P) = MOpen_Rec (S k) (L ++ (x :: nil)) P.
Proof.
  induction k.
  + intros. 
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite <- IHk; auto.
    rewrite Exchange_Open; auto.
Qed.
#[global]
Hint Resolve M2Open_MOpen : Piull.


(**
*)
Lemma MOpen_PureNames :
forall (k : nat)(L : list nat)(x y : Name),
(length L) = k -> 
MOpen_Rec k L (PureNames x) = (PureNames (MOpen_Name_Rec k L x)).
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_PureNames : Piull.


(**
*)
Lemma MOpen_NComposition :
forall (k : nat)(L : list nat)( x y : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x · P) = (MOpen_Name_Rec k L x) · (MOpen_Rec k L P).
Proof.
  ListEasyInduction k L H HL IHk.
Qed. 
#[global]
Hint Resolve MOpen_NComposition : Piull.


(**
*)
Lemma MOpen_PComposition : 
forall (k : nat)(L : list nat)( P Q : Process),
(length L) = k ->
MOpen_Rec k L (P ↓ Q) = (MOpen_Rec k L P) ↓ (MOpen_Rec k L Q).
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_PComposition : Piull.


(**
*)
Lemma MOpen_Restriction :
forall (k : nat)(L : list nat)(P : Process), 
(length L) = k -> 
MOpen_Rec k L (ν P) = (ν M2Open_Rec k L P).
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Restriction : Piull.


(**
*)
Theorem Lca_Lc_Process_MOpen : 
forall (P : Process)(k : nat)(L : list nat),
(length L) = k -> 
lca k P -> lc (MOpen_Rec k L P).
Proof.
  induction P; intros; inversions H0.
  + rewrite MOpen_PureNames; Piauto.
  + rewrite MOpen_NComposition; auto.
    constructor; Piauto.
  + rewrite MOpen_PComposition; constructor; auto.
  + rewrite MOpen_Restriction; auto.
    constructor.
    intros.
    rewrite M2Open_MOpen; auto.
    apply IHP; auto.
    rewrite app_length; simpl; lia.
Qed.
#[global]
Hint Resolve Lca_Lc_Process_MOpen : Piull.

