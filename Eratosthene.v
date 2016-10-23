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
(*                              Eratosthene.v                               *)
(****************************************************************************)

(****************************************************************************)
(****************************************************************************)
(*									    *)
(*            SPECIFICATION  ET PREUVE DU CRIBLE D'ERATOSTHENE 		    *)
(*                     DANS LE CALCUL DES CONSTRUCTIONS  		    *)
(*            Francois Leclerc - ENS Lyon - Juin 91                         *)
(*									    *)
(****************************************************************************)
(****************************************************************************)

(*******************************************)
(* Arithmetical lemmas, euclidean division *)
(*******************************************)

Require Import Arith.
Require Import Peano_dec.
Require Import Euclid.

Definition div (b a : nat) : Prop := exists q : nat, a = q * b.

(* Proof of decidability of div *)
Lemma div_mod_O :
 forall a b r q : nat, a = q * b + r -> div b a -> b > r -> 0 = r.
simple induction 2; intros q' Hq'.
replace r with ((q' - q) * b); intros.
elim (mult_O_le b (q' - q)); intros.
rewrite H2; auto with arith.
absurd (b <= (q' - q) * b); auto with arith.
rewrite mult_minus_distr_r.
symmetry  in |- *; apply plus_minus.
elim H; auto with arith.
Qed.

Lemma div_dec : forall p q : nat, 0 < p -> {div p q} + {~ div p q}.
intros; elim modulo with p q; intros; auto with arith.
elim (eq_nat_dec 0 x); intro y0.
left; elim p0; intros q0 Hq0.
red in |- *; exists q0.
elim Hq0; intros.
rewrite H0.
elim y0; auto with arith.
right; red in |- *; intro; absurd (0 = x); trivial with arith.
elim p0; simple induction 1; intros.
apply div_mod_O with q p x0; auto with arith.
Qed.

(***************************************************************************)
(* DEFINITION INDUCTIVE							   *)
(* divinf(p,q): il existe r entier, 1<r<=q, tel que r divise p 		   *)
(***************************************************************************)

Inductive divinf (p q : nat) : Prop :=
    Bs : forall r : nat, 2 <= r -> r <= q -> div r p -> divinf p q.


(***************************************************************************)
(* DEFINITION INDUCTIVE							   *)
(* nondivinf(p,1) :pas de diviseur de p inferieur ou egal a 1		   *)
(* si nondivinf(p,q) et si Sq ne divise pas p alors nondivinf(p,Sq)	   *)
(* si nondivinf(p,q) et si existe 1<r<q, r divise Sq alors nondivinf(p,Sq) *) 	
(***************************************************************************)

Inductive nondivinf (p : nat) : nat -> Prop :=
  | Base : nondivinf p 1
  | Step1 :
      forall q : nat, nondivinf p q -> ~ div (S q) p -> nondivinf p (S q)
  | Step2 :
      forall q : nat, nondivinf p q -> divinf (S q) q -> nondivinf p (S q).

Hint Resolve Base Step1 Step2.

(***************************************************************************)
(* DEFINITION INDUCTIVE "a la CAML" (type concret mais dependant)	   *)
(* natext(p,n) s'il n'existe pas de diviseur de n <= p 			   *)
(* natext(p,n) s'il existe un diviseur de n <= p			   *)
(***************************************************************************)

Inductive natext (p n : nat) : Set :=
  | Nondiv : nondivinf n p -> natext p n
  | Div : divinf n p -> natext p n.

Hint Resolve Nondiv Div.

(***************************************************************************)
(* DEFINITION 								   *)
(* pour n et p donne, il existe P de type nat->Set telle que 		   *)
(* - on ait une preuve de P(n)						   *)
(* - pour tout q une preuve de P(q) donne une preuve de de P(Sq)	   *)
(* - pour tout q une preuve de P(q) donne une preuve de natext(p,q)	   *)
(*   i.e une preuve de l'existence ou non d'un diviseur de q dans [1...p]  *) 
(***************************************************************************)
Definition Filtre (p n : nat) :=
  forall C : Set,
  (forall P : nat -> Set,
   (forall q : nat, P q -> natext p q) ->
   (forall q : nat, P q -> P (S q)) -> P n -> C) -> C.

(***************************************************************************)
(* Fitrebuild: construction d'une preuve de Filtre(p,n)  		   *)
(***************************************************************************)
Lemma Filtrebuild :
 forall (p n : nat) (P : nat -> Set),
 (forall q : nat, P q -> natext p q) ->
 (forall q : nat, P q -> P (S q)) -> P n -> Filtre p n.
intros.
red in |- *.
intros.
apply (H2 P); trivial with arith.
Qed.

(***************************************************************************)
(* Filtrehd: construction d'une preuve de natext(p,n) a partir d'une 	   *)
(* preuve de Filtre(n,p)						   *)
(***************************************************************************)
Lemma Filtrehd : forall p n : nat, Filtre p n -> natext p n.
intros.
apply H.
auto with arith.
Qed.
Hint Immediate Filtrehd.

(***************************************************************************)
(* Filtre: construction d'une preuve de Filtre(p,Sn)	 a partir d'une	   *)
(* preuve de Filtre(p,n)						   *)
(***************************************************************************)
Lemma Filtretl : forall p n : nat, Filtre p n -> Filtre p (S n).
intros.
apply H.
intros.
apply Filtrebuild with P; auto with arith.
Qed.
Hint Resolve Filtretl.


(***************************************************************************)
(* LEMME1: s'il existe r, 1<r<=q tq r divise p				   *)
(*	   alors il existe aussi r', 1<r'<=Sq tq r' divise p (par ex r'=r) *)
(***************************************************************************)
Lemma lemme1 : forall q p : nat, divinf p q -> divinf p (S q).
simple induction 1; intros.
apply Bs with r; auto with arith.
Qed.
Hint Resolve lemme1.


(***************************************************************************)
(* SPECIFICATION DE Sift					   *)
(* Pour tous n et p tels que p>=1, a partir d'une preuve de Filtre(p,n)	   *)
(* on veut construire une preuve de Filtre(Sp,n)			   *)
(***************************************************************************)

Lemma Sift : forall p n : nat, 1 <= p -> Filtre p n -> Filtre (S p) n.
intros.
apply Filtrebuild with (Filtre p); auto with arith.
intros; elim (Filtrehd p q); intros; auto with arith.
elim (div_dec (S p) q); auto with arith.
intros; apply Div.
apply Bs with (S p); auto with arith.
Qed.


(***************************************************************************)
(* SPECIFICATION DU CRIBLE D'ERATOSTHENE				   *)
(* Il existe une propriete P de type nat->Set telle que:		   *)
(* - on ait une preuve de P(1)						   *)
(* - pour tout q une preuve de P(q) donne une preuve de P(Sq)		   *)
(* - pour tout q une preuve de P(q) donne une preuve de natext(q,Sq) i.e   *)
(*   une preuve de l'existence ou non d'un diviseur de Sq dans [1...q]	   *)
(***************************************************************************)
Definition Eratosthene :=
  forall C : Set,
  (forall P : nat -> Set,
   (forall q : nat, P q -> natext q (S q)) ->
   (forall q : nat, P q -> P (S q)) -> P 1 -> C) -> C.


Lemma Eratobuild :
 forall P : nat -> Set,
 (forall q : nat, P q -> natext q (S q)) ->
 (forall q : nat, P q -> P (S q)) -> P 1 -> Eratosthene.
red in |- *; intros.
apply (H2 P); auto with arith.
Qed.


(***************************************************************************)
(* LEMME2: pour tout q et r, une preuve de l'existence d'un diviseur de Sq *)
(*	   dans [1...q] et une preuve de l'existence ou non d'un diviseur  *)
(*         de r dans [1...q]  donne une preuve de l'existence ou non de r  *)
(*	   dans [1...Sq]  (preuve du lemme par cas)			   *)
(***************************************************************************)

Lemma lemme2 :
 forall q r : nat, divinf (S q) q -> natext q r -> natext (S q) r.
simple induction 2; auto with arith.
Qed.
Hint Resolve lemme2.


(***************************************************************************)
(* DEFINITION INDUCTIVE							   *)
(* Pred(q) propriete de tout q>=1 dont on a une preuve de Filtre(q,Sq)	   *)
(***************************************************************************)
Inductive Pred (q : nat) : Set :=
    Predintro : 1 <= q -> Filtre q (S q) -> Pred q.
Hint Resolve Predintro.


(***************************************************************************)
(* PREUVE DE LA SPECIFICATION DU CRIBLE D'ERATOSTHENE			   *)
(* le terme correspondant a la preuve est le terme de F-OMEGA realisant la *)
(* specification							   *)
(***************************************************************************)

Theorem Crible : Eratosthene.
apply Eratobuild with Pred.  (* Elimination du "il existe" ds Eratobuild *)
intros; apply Filtrehd.
elim H; trivial with arith.
intros; elim H; intros.
apply Predintro; auto with arith.
elim (Filtrehd q (S q) f); intro.
apply Filtretl.
apply Sift; auto with arith.
apply f; intros.
apply Filtrebuild with P; auto with arith. 
apply Predintro; auto with arith.
apply Filtrebuild with (natext 1); auto with arith.
Qed.


(* $Id$ *)