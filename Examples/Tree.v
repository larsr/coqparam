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


(* The type of binary trees *)

Inductive Tree (α : Set) : Type  :=
| η : α -> Tree α
| node : Tree α -> Tree α -> Tree α.


(* Mapping function on trees *)

Definition map (α : Set) (a : Tree α) : forall (α' : Set), (α -> α') -> Tree α'.
Proof.
  induction a as [x|]; intros α' f.
  apply η; apply f; assumption.
  apply node.
  apply IHa1; assumption.
  apply IHa2; assumption.
Defined.


(* The parametricity relation induced by the type of trees *)

Inductive Tree_R (α α' : Set) (α_R : α -> α' -> Prop) : Tree α -> Tree α' -> Prop :=
| η_R : forall x x', α_R x x' -> Tree_R α α' α_R (η α x) (η α' x')
| app_R : forall x x', Tree_R α α' α_R x x' ->
  forall y y', Tree_R α α' α_R y y' -> Tree_R α α' α_R (node α x y) (node α' x' y').


(* Some lemmas *)

Lemma Tree_R_map1 :
  forall (α α' : Set) (f : α -> α'),
    forall (a : Tree α) (a' : Tree α'),
      forall R,
        Tree_R α α' R a a' ->
        R = (fun x x' => f x = x') ->
        map α a α' f = a'.
Proof.
  do 7 intro.
  induction H; intro; subst.
  simpl.
  rewrite H.
  reflexivity.
  simpl.
  rewrite IHTree_R1.
  rewrite IHTree_R2.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Lemma Tree_R_map2 :
  forall (α : Set) (a : Tree α) (α' : Set)
    (f : α -> α') (a' : Tree α'),
    map α a α' f = a' ->
    Tree_R α α' (fun x x' => f x = x')  a a'.
Proof.
  induction a; intros;
    subst; simpl; constructor; eauto.
Qed.


(* The flattening function on trees *)

Definition mu_R (α α':Set) (α_R:α -> α' -> Prop)
  (μ : Tree (Tree α) -> Tree α)
  (μ' : Tree (Tree α') -> Tree α') :=
  forall (a:Tree (Tree α))(a':Tree (Tree α')),
    Tree_R (Tree α) (Tree α')
    (Tree_R α α' α_R) a a' ->
    Tree_R α α' α_R (μ a) (μ' a').


(* The proof that, if it satisfies the relation induced by its type, the
   flattening function commutes with map *)

Lemma mu_map :
  forall
    (μ : forall α:Set, Tree (Tree α) -> Tree α),
    (forall α α' α_R,
      mu_R α α' α_R (μ α) (μ α')) ->
    forall  (α α' : Set) (f : α -> α')
      (z : Tree (Tree α)),
      μ α' (map (Tree α) z (Tree α')
        (fun x => map α x α' f))
      = map α (μ α z) α' f.
Proof.
  intros.
  symmetry.
  eapply Tree_R_map1; [|reflexivity].
  apply H.
  induction z; simpl; constructor; auto.
  apply Tree_R_map2.
  reflexivity.
Qed.
