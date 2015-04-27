(**************************************************************************)
(*                                                                        *)
(*     CoqParam                                                           *)
(*     Copyright (C) 2012                                                 *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*     Marc Lasson                                                        *)
(*                                                                        *)
(*     INRIA - École Polytechnique - ÉNS de Lyon                          *)
(*                                                                        *)
(*   This file is distributed under the terms of the GNU Lesser General   *)
(*   Public License                                                       *)
(*                                                                        *)
(**************************************************************************)


Add LoadPath "..".


(* This commands loads the Coq plugin *)

Declare ML Module "abstraction".


(* We define the type of Church numerals *)

Definition church := (forall α:Set, (α -> α) -> α -> α).


(* We use the vernacular command to compute the relation associated to
   this type. *)

Abstraction church church_R'.
Definition church_R := Eval compute in church_R'.
Print church_R.


(* Iterating k times a function *)

Fixpoint iter k (α : Set) f z : α :=
  match k with
    | 0 => z
    | S p => f (iter p α f z)
  end.


(* The proof that any term of type church satisfying the relation is an
   iterator *)

Lemma church_exists :
  forall f, church_R f f -> exists k:nat,
    forall (α : Set) (g : α -> α) z,
      iter k α g z = f α g z.
Proof.
  intros f H.
  exists (f nat S O).
  intros; apply (H α nat).
  intros x y H0; simpl; rewrite H0; reflexivity.
  reflexivity.
Qed.
