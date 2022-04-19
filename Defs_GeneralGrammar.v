From Coq Require Import Nat.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Ensembles.

From Papercod Require Import Defs_Tactics.



(**
  Definition for the names, two types bound or free.
  The definition use natural numbers to represent free names, this can be changed for any datatype that implements equality comparision at syntactic level and boolean level.
*)
Inductive Name : Type := 
  | FName ( x : nat) : Name
  | BName ( i : nat) : Name.
#[global]
Hint Constructors Name : Piull.

Inductive Process : Type  := 
  | PureNames (x : Name) : Process
  | NComposition ( x : Name )(P : Process) : Process
  | PComposition (P Q : Process ) : Process
  (* Processes with bounded names *)
  | Restriction (P : Process ) : Process.
#[global]
Hint Constructors Process : Piull.


(**
  Notation for the processes.
  In most cases the notation is the same, but in others the notation is changed due to conflicts with Coq syntax, e.g. | for ↓.
*)
Notation "x · P " := (NComposition x P ) (at level 60).
Notation "P ↓ Q" :=  (PComposition P Q ) ( at level 60).
Notation " 'ν' P " := (Restriction P ) ( at level 60).



Definition Open_Name ( k z : nat )( N : Name ) : Name := 
match N with 
  | FName x => FName x
  | BName i => if ( k =? i ) then (FName z) else (BName i)
end.
#[global]
Hint Resolve Open_Name : Piull.

Fixpoint Open_Rec (k z : nat)( T : Process ) {struct T} : Process := 
match T with
  | PureNames x => PureNames (Open_Name k z x )
  | NComposition x P => NComposition (Open_Name k z x) (Open_Rec k z P)
  | PComposition P Q => PComposition (Open_Rec k z P) (Open_Rec k z Q)
  | Restriction P => Restriction (Open_Rec (S k) z P)
end.
#[global]
Hint Resolve Open_Rec : Piull.

Notation "{ k ~> z } P " := (Open_Rec k z P)(at level 60).
Definition Open ( z : nat )( T : Process ): Process := Open_Rec 0 z T.
#[global]
Hint Resolve Open : Piull.
Notation "P ^ z" := (Open_Rec 0 z P).


(**
  Definition for the closed functions.
*)
Definition Close_Name ( k z: nat )( N : Name ) : Name := 
match N with
  | FName x => if ( x =? z ) then (BName k) else N
  | BName i => N
end.
#[global]
Hint Resolve Close_Name : Piull.

Fixpoint Close_Rec (k z : nat)( T : Process ) {struct T} : Process := 
match T with
  | PureNames x => PureNames (Close_Name k z x )
  | NComposition x P => NComposition (Close_Name k z x) (Close_Rec k z P)
  | PComposition P Q => PComposition (Close_Rec k z P) (Close_Rec k z Q)
  | Restriction P => Restriction (Close_Rec (S k) z P)
end.
#[global]
Hint Resolve Close_Rec : Piull.


(**
*)
Definition Close ( z : nat )( T : Process ): Process := Close_Rec 0 z T.
#[global]
Hint Resolve Close : Piull.


(**
  Locally closed predicate.
*)
Inductive lcName : Name -> Prop := 
  | lcFName : forall (x : nat), lcName (FName x).
#[global]
Hint Constructors lcName : Piull.

Inductive lc : Process -> Prop :=

  | lcPureName : forall ( x : Name ),
  lcName x -> lc ( PureNames x )

  | lcNComposition : forall ( x : Name )( P : Process ),
    lcName x -> lc P -> lc ( x · P )

  | lcPComposition : forall P Q : Process,
    lc P -> lc Q -> lc ( P ↓ Q )

  | lcRestriction : forall (P : Process),
    ( forall ( x : nat ), lc ( { 0 ~> x }P ) ) -> lc ( ν P ).

#[global]
Hint Constructors lc : Piull.



(**
  Definition of a body.
*)
Inductive Body : Process -> Prop := 
  | isBody : forall (P : Process),
    ( forall (x : nat), lc ({ 0 ~> x}P) ) -> Body(P).
#[global]
Hint Constructors Body : Piull.



(**
  Locally closed at predicate.
*)
Inductive lcaName : nat -> Name -> Prop := 
  | lcaFName : forall ( k x : nat), lcaName k (FName x)
  | lcaBName : forall ( k i : nat), ( i < k ) -> lcaName k (BName i).
#[global]
Hint Constructors lcaName : Piull.

Inductive lca : nat -> Process -> Prop :=

  | lcaPureName : forall ( k : nat )( x : Name ),
    lcaName k x  -> lca k ( PureNames x )

  | lcaNComposition : forall ( k : nat )( x : Name )( P : Process ),
    lcaName k x -> lca k P -> lca k ( x · P )

  | lcaPComposition : forall ( k : nat )( P Q : Process ),
    lca k P -> lca k Q -> lca k ( P ↓ Q )

  | lcaRestriction : forall ( k : nat )(P : Process),
    lca (S k) P -> lca k (ν P).

#[global]
Hint Constructors lca : Piull.


(**
  Require for the MOpen definitions.
*)
From Coq Require Import Lists.List.
Import ListNotations.


(**
  Definition for multiple open function in names
*)
Fixpoint MOpen_Name_Rec (k : nat)(L : list nat)( N : Name ) : Name := 
match L , k with
  | nil , _  => N
  | x :: L0, 0 =>  Open_Name 0 x (MOpen_Name_Rec 0 L0 N)
  | x :: L0, S t =>  Open_Name t x (MOpen_Name_Rec t L0 N)
end.
#[global]
Hint Resolve MOpen_Name_Rec : Piull.

Fixpoint MOpen_Rec (k : nat)(L : list nat)( T : Process ) : Process := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (MOpen_Rec 0 L0 T)
  | x :: L0, S t =>  { t ~> x } (MOpen_Rec t L0 T)
end.
#[global]
Hint Resolve MOpen_Rec : Piull.


(**
  Multiple open at second level.
*)
Fixpoint M2Open_Rec (k : nat)(L : list nat)( T : Process ) : Process := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (M2Open_Rec 0 L0 T)
  | x :: L0, S t =>  { S t ~> x } (M2Open_Rec t L0 T)
end.
#[global]
Hint Resolve M2Open_Rec : Piull.
