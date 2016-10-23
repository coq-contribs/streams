(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*                               Oct 1st 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Streams.v                                 *)
(****************************************************************************)

Require Import Arith.
Require Import Eqdep.


Section Streams_.

Variable U : Set.

Inductive Streams (A : U -> U -> Set) (m : U) : Set :=
    build :
      forall P : U -> Set,
      (forall p : U, P p -> {q : U &  A p q &  P q}) -> P m -> Streams A m.

Variable A : U -> U -> Set.

Let streams := Streams A.

Definition eq_streams := eq_dep U streams.

Lemma eq_streams_intro : forall (m : U) (X : streams m), eq_streams m X m X.
red in |- *; auto with arith.
Qed.
Hint Resolve eq_streams_intro.

Lemma eq_streams_sym :
 forall (m n : U) (X : streams m) (Y : streams n),
 eq_streams m X n Y -> eq_streams n Y m X.
exact (eq_dep_sym U streams).
Qed.
Hint Immediate eq_streams_sym.

Lemma eq_streams_trans :
 forall (m n p : U) (X : streams m) (Y : streams n) (Z : streams p),
 eq_streams m X n Y -> eq_streams n Y p Z -> eq_streams m X p Z.
exact (eq_dep_trans U streams).
Qed.

Lemma out : forall m : U, streams m -> {q : U &  A m q &  streams q}.
simple induction 1; intros P s y.
elim (s m); intros; trivial with arith.
exists x; trivial with arith.
red in |- *; apply build with P; auto with arith.
Defined.

Lemma hd : forall m : U, streams m -> U.
intros; elim (out m H); intros.
exact x.
Defined.

Lemma tail : forall (m : U) (X : streams m), streams (hd m X).
intros; unfold hd in |- *; elim (out m X); auto with arith.
Defined.

Lemma out_hd_tail :
 forall (m : U) (X : streams m),
 {q : U &  A m q &  {Y : streams q | eq_streams q Y (hd m X) (tail m X)}}.
intros; unfold hd, tail in |- *; elim (out m X).
intros x a Y; exists x; trivial with arith.
exists Y; trivial with arith.
Defined.

Lemma hd_nth : nat -> forall m : U, streams m -> U.
simple induction 1; intros.
exact m.
apply (H0 (hd m H1) (tail m H1)).
Defined.

Lemma tail_nth :
 forall (n : nat) (m : U) (X : streams m), streams (hd_nth n m X).
simple induction n; simpl in |- *; intros; trivial with arith.
(***
Induction n; Simpl; Intros; Trivial with arith.
Change (streams (hd_nth y (hd m X) (tail m X))); Trivial with arith.
***)
Defined.

Lemma tail_plus :
 forall (n k : nat) (m : U) (X : streams m),
 eq_streams (hd_nth (n + k) m X) (tail_nth (n + k) m X)
   (hd_nth k (hd_nth n m X) (tail_nth n m X))
   (tail_nth k (hd_nth n m X) (tail_nth n m X)).
simple induction n; simpl in |- *; trivial with arith.
(***
Induction n; Simpl; Trivial with arith.
Intros.
Change (eq_streams (hd_nth (plus y k) (hd m X) (tail m X))
     (tail_nth (plus y k) (hd m X) (tail m X))
     (hd_nth k (hd_nth y (hd m X) (tail m X))
       (tail_nth y (hd m X) (tail m X)))
     (tail_nth k (hd_nth y (hd m X) (tail m X))
       (tail_nth y (hd m X) (tail m X)))); Trivial with arith.
***)
Qed.
Hint Resolve tail_plus.

Lemma specif : forall (m : U) (X : streams m), A m (hd m X).
intros; unfold hd in |- *; elim (out m X); auto with arith.
Qed.


(*******************************************************)
(*   Filter                                            *)
(*******************************************************)

Section Filter_.

(* Load Between. *)

Variable P Q : U -> Prop.

(* R is decidable *)
Hypothesis PQ_dec : forall x : U, {P x} + {Q x}.
Hypothesis PQ_excl : forall x : U, P x -> ~ Q x.

Hint Immediate PQ_excl.

Variable B : U -> U -> Set.
Hypothesis incl : forall x y : U, A x y -> B x y.
Hypothesis trans_ARB : forall x y z : U, A x y -> P y -> B y z -> B x z.
Hint Resolve incl.

Section Stream_X.

Variable x : U.
Variable X : streams x.
Let hdSX (k : nat) := hd_nth (S k) x X.

Let tlSX (n : nat) : streams (hdSX n) := tail_nth (S n) x X.

Definition P_nth_X (k : nat) : Prop := P (hdSX k).

Definition Q_nth_X (k : nat) : Prop := Q (hdSX k).


Inductive filter_specif (q : U) : Set :=
    filter_intro :
      B x q ->
      Q q ->
      forall (Y : streams q) (m : nat),
      eq_streams q Y (hdSX m) (tlSX m) ->
      between P_nth_X 0 m -> filter_specif q.

End Stream_X.

Section Properties.

Variable x q : U.
Variable X : streams x.
Variable Y : streams q.
Hypothesis Y_tlX : eq_streams q Y (hd x X) (tail x X).

Lemma P_nth_X_O : P q -> P_nth_X x X 0.
red in |- *; simpl in |- *; elim Y_tlX; auto with arith.
(***
Red; Change ((P q)->(P (hd x X))); Elim Y_tlX; Auto with arith.
***)
Qed.
Hint Resolve P_nth_X_O.

Lemma Q_nth_X_O : Q_nth_X x X 0 -> Q q.
unfold Q_nth_X in |- *; simpl in |- *; elim Y_tlX; auto with arith.
(***
Unfold Q_nth_X; Change ((Q (hd x X))->(Q q)); Elim Y_tlX; Auto with arith.
***)
Qed.
Hint Resolve Q_nth_X_O.

Lemma event_Q_nth_O : eventually (Q_nth_X x X) 0 -> Q q.
intros; apply Q_nth_X_O; apply event_O; trivial with arith.
Qed.

Lemma P_nth_X_S : forall m : nat, P_nth_X q Y m -> P_nth_X x X (S m).
red in |- *; simpl in |- *; intros.
elim Y_tlX; auto with arith.
(***
Red; Change ((m:nat)
    (P_nth_X q Y m)
     ->(P (hd_nth m (hd (hd x X) (tail x X)) (tail (hd x X) (tail x X))))).
Intros; Elim Y_tlX; Auto with arith.
***)
Qed.
Hint Resolve P_nth_X_S.

Lemma Q_nth_X_S : forall m : nat, Q_nth_X x X (S m) -> Q_nth_X q Y m.
unfold Q_nth_X in |- *; simpl in |- *.
elim Y_tlX; auto with arith.
(***
Unfold Q_nth_X ; Change ((m:nat)
    (Q (hd_nth m (hd (hd x X) (tail x X)) (tail (hd x X) (tail x X))))
     ->(Q (hd_nth m (hd q Y) (tail q Y)))).
Elim Y_tlX; Auto with arith.
***)
Qed.
Hint Resolve Q_nth_X_S.

Lemma event_Q_nth_X_tl :
 forall l : nat,
 ~ Q q -> eventually (Q_nth_X x X) (S l) -> eventually (Q_nth_X q Y) l.
simple induction 2; red in |- *; intro k.
pattern k in |- *; apply nat_case.
intros; absurd (Q q); auto with arith.
intros; exists m; auto with arith.
Qed.

Lemma between_P_nth_X_tl :
 forall l : nat,
 P q -> between (P_nth_X q Y) 0 l -> between (P_nth_X x X) 0 (S l).
simple induction 2; auto with arith.
Qed.

End Properties.

Lemma filter_step :
 forall (n : nat) (x : U) (X : streams x),
 eventually (Q_nth_X x X) n -> {q : U &  filter_specif x X q}.
simple induction n; intros.
(* case n=0 let q::Y = X *)
elim (out_hd_tail x X); intros q Axq HY.
elim HY; intros Y eqY.
(* the solution is (q,Y,O) because 
   (eventually (Q_nth_X x X) O)->(Q q)  *)
exists q; apply filter_intro with Y 0; auto with arith.
apply event_Q_nth_O with x X Y; trivial with arith.
(* case n = (S y), let q::Y = X *)
elim (out_hd_tail x X); intros q Axq HY.
elim HY; intros Y eqY.
(* the solution depends on (P q) or (Q q) *)
elim (PQ_dec q); intro.
(* case (P q), apply inductively the result to (q,Y) *)
elim H with q Y.
(* let q'::Z be the result for Y *)
intros q' f'.
elim f'; intros B' notR Z m eqm betm.
(* the solution is (q',Z,(S m)) *)
exists q'; apply filter_intro with Z (S m); trivial with arith.
(* Proof of (B x q') *)
apply trans_ARB with q; auto with arith.
(* Proof of 
     (eq_streams q' Z (hd_nth (S (S m)) x X) (tail_nth (S (S m)) x X)) *)
change
  (eq_streams q' Z (hd_nth (S m) (hd x X) (tail x X))
     (tail_nth (S m) (hd x X) (tail x X))) in |- *.
elim eqY; trivial with arith.
apply between_P_nth_X_tl with q Y; trivial with arith.
apply event_Q_nth_X_tl with x X; auto with arith.
(* case (Q q), the solution is (q,O,Y) *)
exists q; apply filter_intro with Y 0; auto with arith.
Qed.

Variable x : U.
Variable X : streams x.

Let hdX (k : nat) := hd_nth k x X.

Let tlX (n : nat) : streams (hdX n) := tail_nth n x X.

Hypothesis
  remanent :
    forall n : nat, {p : nat | eventually (Q_nth_X (hdX n) (tlX n)) p}.

Inductive Filter_specif (p q : U) : Set :=
    Filter_intro :
      B p q ->
      Q q ->
      forall n m : nat,
      hdX n = p ->
      hdX (S m) = q -> between (P_nth_X x X) n m -> Filter_specif p q.

Section Lemmes.
Variable p : U.
Variable Y : streams p.
Variable n : nat.
Hypothesis eqY : eq_streams (hdX n) (tlX n) p Y.

Remark hd_nth_tail :
 forall l : nat, hd_nth (S (n + l)) x X = hd_nth (S l) p Y.
elim eqY; intro.
replace (S (n + l)) with (n + S l); auto with arith.
unfold hdX, tlX in |- *; elim (tail_plus n (S l) x X); auto with arith.
Qed.

Remark P_nth_X_tail : forall l : nat, P_nth_X p Y l -> P_nth_X x X (n + l).
unfold P_nth_X in |- *.
intro; elim hd_nth_tail; auto with arith.
Qed.
Hint Resolve P_nth_X_tail.

Lemma between_between_tail :
 forall m : nat, between (P_nth_X p Y) 0 m -> between (P_nth_X x X) n (n + m).
simple induction 1; intros; auto with arith.
replace (n + S l) with (S (n + l)); auto with arith.
Qed.
End Lemmes.

Definition Filter_prop (p : U) :=
  {Y : streams p &  {n : nat | eq_streams (hdX n) (tlX n) p Y}}.

Theorem Filter : Streams Filter_specif x.
apply build with Filter_prop.
simple induction 1; intros Y HY.
elim HY; intros n HYn.
elim (remanent n); intros ln evln.
elim (filter_step ln p Y).
intros q fq; elim fq; intros Bq Rq Z m eqZm betZm.
cut (eq_streams (hdX (n + S m)) (tlX (n + S m)) q Z).
intro eqZ; exists q.
apply Filter_intro with n (n + m); trivial with arith.
elim HYn; trivial with arith.
elim eqZ; replace (S (n + m)) with (n + S m); auto with arith.
apply between_between_tail with p Y; trivial with arith.
red in |- *; exists Z; exists (n + S m); trivial with arith.
apply eq_streams_trans with (hd_nth (S m) p Y) (tail_nth (S m) p Y);
 auto with arith.
elim HYn.
exact (tail_plus n (S m) x X).
elim HYn; trivial with arith.
(* Initial state : X *)
red in |- *; exists X; exists 0; auto with arith.
Qed.

End Filter_.

End Streams_.

(* $Id$ *)