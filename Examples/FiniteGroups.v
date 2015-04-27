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


(* Standard coercion from bool to Prop *)

Coercion is_true b := b = true.


(* We take a group *)

Section GroupTheory.

  Variable α : Set.
  Variable eq_dec : forall (x y : α), {x = y} + {x <> y}.
  Variable op : α -> α -> α.
  Variable inv : α -> α.
  Variable e : α.

  Infix "≡" := (eq_dec) (at level 50).
  Infix "·" := (op) (at level 35).

  Variable assoc :
    forall x y z, x · (y · z) = (x·y)·z.
  Variable neutral_left :
    forall x, e · x = x.
  Variable inverse :
    forall x, (inv x) · x = e.

  Lemma left_cancel :
    forall x y a, a · x = a · y -> x = y.
    intros.
    assert (inv a · (a · x) = inv a · (a · y)).
    rewrite H.
    reflexivity.
    do 2 rewrite assoc in H0.
    rewrite inverse in H0.
    do 2 rewrite neutral_left in H0.
    assumption.
  Qed.

  Lemma neutral_right :
    forall x, x · e = x.
  Proof.
    intro x. apply (left_cancel _ _ (inv x)). rewrite assoc, inverse, neutral_left. reflexivity.
  Qed.

  Lemma right_inverse :
    forall x, x · (inv x) = e.
    intro x.
    apply left_cancel with (inv x).
    rewrite assoc.
    rewrite inverse.
    rewrite neutral_left.
    rewrite neutral_right.
    reflexivity.
  Qed.

  Lemma inv_inv :
    forall x, inv (inv x) = x.
    intros.
    apply left_cancel with (inv x).
    rewrite right_inverse.
    rewrite inverse.
    reflexivity.
  Qed.

  Lemma inv_inj :
    forall x y, inv x = inv y -> x = y.
    intros.
    apply left_cancel with (inv x).
    rewrite inverse.
    rewrite H.
    rewrite inverse.
    reflexivity.
  Qed.

  Require Import Setoid.
  Lemma inv_morph :
    forall x y, inv (x · y) = inv y · inv x.
    intros.
    apply left_cancel with (x · y).
    rewrite right_inverse.
    replace ((x · y) · (inv y · inv x)) with (x · (y · inv y) · inv x).
    rewrite right_inverse.
    rewrite neutral_right.
    rewrite right_inverse.
    reflexivity.
    rewrite-> assoc.
    rewrite-> assoc.
    reflexivity.
  Qed.

  Lemma inv_e : inv e = e.
  Proof. rewrite <- (neutral_right (inv e)), inverse. reflexivity. Qed.

  Require Import List.

  Inductive In x : list α -> Prop :=
  | In_cons : forall l, In x (x :: l)
  | In_tail : forall l y, In x l -> In x (y::l).

  Infix "∈" := (In) (at level 60).


  (* Finite subgroups *)

  Structure fingrp := Fingrp {
    elements :> list α;
    e_comp : e ∈ elements;
    op_comp : forall x y, x ∈ elements -> y ∈ elements -> x·y ∈ elements;
      inv_comp : forall x, x ∈ elements -> inv x ∈ elements
  }.


  (* Binary relations on them *)

  Section BinaryRelations.

    Variable R : α -> α -> Prop.

    Inductive list_R : list α -> list α -> Prop :=
    | nil_R : list_R nil nil
    | cons_R : forall x x' l l', R x x' -> list_R l l' -> list_R (x :: l) (x' :: l').
    Check list_R_ind.

    Scheme new_scheme :=  Induction for list_R Sort Prop.


    Inductive In_R x x' (a : R x x') : forall l l', list_R l l' ->
      (In x l) -> (In x' l') -> Prop :=
    | In_cons_R : forall l l' (h : list_R l l'),
      In_R x x' a (x :: l) (x' :: l') (cons_R x x' l l' a h) (In_cons x l) (In_cons x' l')
    | In_tail_R : forall l l' (h : list_R l l') y y' (b : R y y')
      (p : In x l) (p' : In x' l'),
      In_R x x' a l l' h p p' ->
      In_R x x' a (y::l) (y'::l') (cons_R y y' l l' b h) (In_tail x l y p) (In_tail x' l' y' p').

    Inductive In_RW x x' (a : R x x') : forall l l', list_R l l' -> Prop :=
    | In_cons_RW : forall l l' (h : list_R l l'),
      In_RW x x' a (x :: l) (x' :: l') (cons_R x x' l l' a h)
    | In_tail_RW : forall l l' (h : list_R l l') y y' (b : R y y')
      (p : In x l) (p' : In x' l'),
      In_RW x x' a l l' h ->
      In_RW x x' a (y::l) (y'::l') (cons_R y y' l l' b h).

    Axiom PI : forall (P:Prop)(h h' : P),  h = h'.
    Lemma In_R_RW :
      forall x x' x_R l l' l_R, In_RW x x' x_R l l' l_R -> forall p p',
        In_R x x' x_R l l' l_R p p'.
      do 7 intro.
      induction H.
      intros.
      replace p with (In_cons x l).
      replace p' with (In_cons x' l').
      constructor.
      apply PI.
      apply PI.
      intros q q'.
      replace q with (In_tail x l y p).
      replace q' with (In_tail x' l' y' p').
      constructor.
      apply IHIn_RW.
      apply PI.
      apply PI.
    Qed.

    Print list_R.
    Inductive In2 x x' : list α -> list α -> Prop :=
    | In2_cons : forall l l', In2 x x' (x :: l) (x' :: l')
    | In2_tail : forall l l' y y', In2 x x' l l' -> In2 x x' (y :: l) (y' :: l').

    Lemma In2_In :
      forall x x' l l', In2 x x' l l' -> In x l /\ In x' l'.
      intros x x' l l' H.
      induction H; split; constructor; intuition.
    Qed.

    Lemma In_InR :
      forall l l' (l_R : list_R l l') x x' (x_R : R x x'), In2 x x' l l' -> In_RW x x' x_R l l' l_R.
      induction l_R using new_scheme; intuition.
      inversion H.
      inversion H; subst.
      replace r with x_R.
      constructor 1.
      apply PI.
      constructor 2.
      eelim In2_In.
      intros HIn1 HIn2; eexact HIn1.
      eassumption.
      eelim In2_In.
      intros HIn1 HIn2; eexact HIn2.
      eassumption.
      eapply IHl_R.
      eassumption.
    Qed.

    Variable R_e : R e e.
    Variable R_op : forall x x' y y', R x x' -> R y y' -> R (x·y) (x'·y').
    Variable R_inv : forall x x', R x x' -> R (inv x) (inv x').

    Structure fingrp_R (G G' : fingrp) := Fingrp_R {
      elements_R : list_R G G';
      e_comp_R : In_R e e R_e G G' elements_R (e_comp G) (e_comp G');
      op_comp_R : forall x x' (x_R : R x x') y y' (y_R : R y y')
        (p : x ∈ G) (p' : x' ∈ G'), In_R x x' x_R G G' elements_R p p' ->
        forall (q : y ∈ G) (q' : y' ∈ G'), In_R y y' y_R G G' elements_R q q' ->
          In_R (x·y) (x'·y') (R_op x x' y y' x_R y_R) G G' elements_R (op_comp G x y p q) (op_comp G' x' y' p' q');
          inv_comp_R : forall x x' (x_R : R x x') (p : x ∈ G) (p' : x' ∈ G'),
            In_R x x' x_R G G' elements_R p p' ->
            In_R (inv x) (inv x') (R_inv x x' x_R) G G' elements_R (inv_comp G x p) (inv_comp G' x' p')
    }.

  End BinaryRelations.


  (* We take a term of type fingrp -> fingrp which is parametric *)

  Section Parametricity.
    Variable Z : fingrp -> fingrp.
    Hypothesis Z_param : forall R R_e R_op R_inv G G',
      fingrp_R R R_e R_op R_inv G G' -> fingrp_R R R_e R_op R_inv (Z G) (Z G').


    (* We prove that Z commutes with every morphism *)

    Section Automorphism.

      Variable G : fingrp.

      Variable f : α -> α.
      Hypothesis op_s : forall x y, (f x)·(f y) = f (x · y).

      Local Hint Immediate (e_comp G).
      Local Hint Resolve (op_comp G).
      Local Hint Resolve (inv_comp G).
      Local Hint Resolve op_s.

      Lemma e_s : f e = e.
      Proof.
        rewrite <- (neutral_left (f e)). rewrite <- (inverse (f e)) at 1. rewrite <- assoc, op_s; auto. rewrite neutral_right, inverse. reflexivity.
      Qed.

      Local Hint Immediate e_s.

      Lemma inv_s : forall x, inv (f x) = f (inv x).
      Proof.
        intros x. rewrite <- (neutral_left (inv (f x))). rewrite <- e_s. rewrite <- (inverse x). rewrite <- op_s; auto. rewrite <- assoc, right_inverse, neutral_right. reflexivity.
      Qed.

      Local Hint Resolve inv_s.

      Let R : α -> α -> Prop := fun x y => f x = y.

      Definition R_e : R e e := e_s.

      Lemma R_op : forall x x' y y', R x x' -> R y y' -> R (x·y) (x'·y').
      Proof. unfold R. intros x x' y y' H1 H2. subst x' y'. symmetry. auto. Qed.

      Lemma R_inv : forall x x', R x x' -> R (inv x) (inv x').
      Proof. unfold R. intros x x' H. subst x'. symmetry. auto. Qed.

      Local Notation list_R := (list_R R).
      Local Notation fingrp_R := (fingrp_R _ R_e R_op R_inv).
      Local Notation Fingrp_R := (Fingrp_R _ R_e R_op R_inv).
      Local Notation elements_R := (elements_R _ R_e R_op R_inv).
      Local Notation In_R := (In_R R).

      Let Z_param' := Z_param R R_e R_op R_inv.

      Lemma aux_map : forall g y l,
        y ∈ (map g l) <-> exists x, x ∈ l /\ y = g x.
      Proof.
        intros g y. induction l; simpl; split.
        inversion 1.
        intros [x [H _]]. inversion H.
        intro H. inversion H.
        exists a. split.
        constructor 1. auto.
        rewrite IHl in H1. destruct H1 as [x [H3 H4]]. exists x. split; auto.
        constructor 2. auto.
        intros [x [H1 H2]]. inversion H1.
        rewrite H2, H0. constructor 1.
        constructor 2. rewrite IHl. exists x. split; auto.
      Qed.

      Let G'_elements := map f G.

      Lemma In2_G_G' : forall x l, In x l -> In2 x (f x) l (map f l).
        induction l; intros H; inversion H; subst; simpl; constructor.
        apply IHl.
        assumption.
      Qed.


      Lemma G'_e_comp : e ∈ G'_elements.
      Proof.
        unfold G'_elements. rewrite aux_map. exists e. split; auto. rewrite R_e. auto.
      Qed.
      Lemma G'_op_comp : forall x y : α,
        x ∈ G'_elements -> y ∈ G'_elements -> x · y ∈ G'_elements.
        intros x y. unfold G'_elements. rewrite !aux_map. intros [x1 [H1 H2]] [x2 [H3 H4]]. exists (x1·x2). split; auto.
        rewrite H2, H4; auto.
      Qed.
      Lemma G'_inv_comp : forall x : α, x ∈ G'_elements -> inv x ∈ G'_elements.
      Proof.
        intro x. unfold G'_elements. rewrite !aux_map. intros [y [H1 H2]]. exists (inv y). split; auto.
        rewrite H2; auto.
      Qed.
      Let G' := Fingrp G'_elements G'_e_comp G'_op_comp G'_inv_comp.


      (* In fact, if f is bijective on G, then G' is a permutation of G *)
      Section Permutation.

        Hypothesis endo : forall x, x ∈ G -> f x ∈ G.
        Hypothesis f_surj : forall y, y ∈ G -> exists x, x ∈ G /\ y = f x.

        Definition perm l l' := forall x, x ∈ l <-> x ∈ l'.

        Lemma G_G'_perm : perm G G'.
        Proof.
          change (perm G G'_elements). unfold G'_elements, perm. intro x. rewrite aux_map. split.
          apply f_surj.
          intros [y [H1 H2]]. rewrite H2. apply endo. auto.
        Qed.

      End Permutation.


      Lemma G_elements_R : list_R G G'.
      Proof.
        assert (H : forall l, list_R l (map f l)).
        induction l; simpl; constructor; auto.
        unfold R. auto.
        apply H.
      Qed.

      Lemma G_e_comp_R : In_R e e R_e G G' G_elements_R (e_comp G) (e_comp G').
      Proof.
        apply In_R_RW.
        apply In_InR.
        rewrite<- e_s at 2.
        simpl.
        unfold G'_elements.
        apply In2_G_G'.
        apply e_comp.
      Qed.

      Lemma G_op_comp_R : forall x x' (x_R : R x x') y y' (y_R : R y y')
        (p : x ∈ G) (p' : x' ∈ G'), In_R x x' x_R G G' G_elements_R p p' ->
        forall (q : y ∈ G) (q' : y' ∈ G'), In_R y y' y_R G G' G_elements_R q q' ->
          In_R (x·y) (x'·y') (R_op x x' y y' x_R y_R) G G' G_elements_R (op_comp G x y p q) (op_comp G' x' y' p' q').
      Proof.
        intros. apply In_R_RW. apply In_InR. unfold R in x_R, y_R. subst x' y'. rewrite op_s. simpl. unfold G'_elements. apply In2_G_G'. auto.
      Qed.

      Lemma G_inv_comp_R : forall x x' (x_R : R x x') (p : x ∈ G) (p' : x' ∈ G'),
        In_R x x' x_R G G' G_elements_R p p' ->
        In_R (inv x) (inv x') (R_inv x x' x_R) G G' G_elements_R (inv_comp G x p) (inv_comp G' x' p').
      Proof.
        intros. apply In_R_RW. apply In_InR. unfold R in x_R. subst x'. rewrite inv_s. simpl. unfold G'_elements. apply In2_G_G'. auto.
      Qed.

      Definition G_fingrp_R := Fingrp_R G G' G_elements_R G_e_comp_R G_op_comp_R G_inv_comp_R.

      Theorem comm : elements (Z G') = map f (Z G).
      (* Which means that (Z G) is stable by f *)
      Proof.
        generalize (elements_R (Z G) (Z G') (Z_param' _ _ G_fingrp_R)).
        assert (H : forall l l', list_R l l' -> l' = map f l).
        induction l; simpl.
        intros l. inversion 1. auto.
        intros l'. inversion 1. unfold R in H2. rewrite <- H2. rewrite (IHl _ H4). auto.
        apply H.
      Qed.
    End Automorphism.

  End Parametricity.


  (* We now define unary relations *)

  Section UnaryRelations.

    Variable UR : α -> Prop.

    Inductive list_UR : list α  -> Prop :=
    | nil_UR : list_UR nil
    | cons_UR : forall x l, UR x -> list_UR l -> list_UR (x :: l).
    Check list_UR_ind.

    Scheme new_scheme2 :=  Induction for list_UR Sort Prop.


    Inductive In_UR x (a : UR x) : forall l, list_UR l ->
      (In x l) -> Prop :=
    | In_cons_UR : forall l (h : list_UR l),
      In_UR x a (x :: l) (cons_UR x l a h) (In_cons x l)
    | In_tail_UR : forall l (h : list_UR l) y (b : UR y) (p : In x l),
      In_UR x a l h p -> In_UR x a (y::l) (cons_UR y l b h) (In_tail x l y p).

    Inductive In_URW x (a : UR x) : forall l, list_UR l -> Prop :=
    | In_cons_URW : forall l (h : list_UR l),
      In_URW x a (x :: l) (cons_UR x l a h)
    | In_tail_URW : forall l (h : list_UR l) y (b : UR y) (p : In x l),
      In_URW x a l h -> In_URW x a (y::l) (cons_UR y l b h).

    Lemma In_UR_URW :
      forall x x_UR l l_UR, In_URW x x_UR l l_UR -> forall p,
        In_UR x x_UR l l_UR p.
      do 5 intro.
      induction H.
      intros.
      replace p with (In_cons x l).
      constructor.
      apply PI.
      intros q.
      replace q with (In_tail x l y p).
      constructor.
      apply IHIn_URW.
      apply PI.
    Qed.

    Lemma In_InUR :
      forall l (l_UR : list_UR l) x (x_UR : UR x), In x l -> In_URW x x_UR l l_UR.
      induction l_UR using new_scheme2; intuition.
      inversion H.
      inversion H; subst.
      replace u with x_UR.
      constructor 1.
      apply PI.
      constructor 2; auto.
    Qed.

    Variable UR_e : UR e.
    Variable UR_op : forall x y, UR x -> UR y -> UR (x·y).
    Variable UR_inv : forall x, UR x -> UR (inv x).


    Structure fingrp_UR (G : fingrp) := Fingrp_UR {
      elements_UR : list_UR G;
      e_comp_UR : In_UR e UR_e G elements_UR (e_comp G);
      op_comp_UR : forall x (x_UR : UR x) y (y_UR : UR y),
        forall (p : x ∈ G), In_UR x x_UR G elements_UR p ->
        forall (q : y ∈ G), In_UR y y_UR G elements_UR q ->
          In_UR (x·y) (UR_op x y x_UR y_UR) G elements_UR (op_comp G x y p q);
      inv_comp_UR : forall x (x_UR : UR x) (p : x ∈ G),
        In_UR x x_UR G elements_UR p ->
        In_UR (inv x) (UR_inv x x_UR) G elements_UR (inv_comp G x p)
    }.

  End UnaryRelations.


  (* We take a term of type fingrp -> fingrp which is parametric *)

  Section Parametricity2.
    Variable Z : fingrp -> fingrp.
    Hypothesis Z_param : forall UR UR_e UR_op UR_inv G,
      fingrp_UR UR UR_e UR_op UR_inv G -> fingrp_UR UR UR_e UR_op UR_inv (Z G).


    (* We prove that Z G ⊂ G *)

    Section Inclusion.

      Variable G : fingrp.

      Local Hint Immediate (e_comp G).
      Local Hint Resolve (op_comp G).
      Local Hint Resolve (inv_comp G).

      Let UR (x:α) := x ∈ G.
      Let UR_e : UR e := e_comp G.
      Let UR_op : forall x y, UR x -> UR y -> UR (x·y) := op_comp G.
      Let UR_inv : forall x, UR x -> UR (inv x) := inv_comp G.

      Local Notation fingrp_UR := (fingrp_UR _ UR_e UR_op UR_inv).
      Local Notation Fingrp_UR := (Fingrp_UR _ UR_e UR_op UR_inv).
      Local Notation Z_param' := (Z_param UR UR_e UR_op UR_inv).
      Local Notation list_UR := (list_UR UR).
      Local Notation In_UR := (In_UR UR).

      Fixpoint elements_UR_l l : (forall x, x ∈ l -> x ∈ G) -> list_UR l :=
        match l as l' return (forall x, x ∈ l' -> x ∈ G) -> list_UR l' with
          | nil => fun _ => nil_UR UR
          | a::l => fun H => cons_UR UR a l (H a (In_cons a l)) (elements_UR_l l (fun x H1 => H x (In_tail x l a H1)))
        end.

      Let elements_UR_G : list_UR G := elements_UR_l G (fun x H => H).


      Lemma e_comp_UR_l : forall l (p: e ∈ l),
        forall (H: forall x, x ∈ l -> x ∈ G), In_UR e (H e p) l (elements_UR_l l H) p.
      Proof.
        induction l as [ |a l IHl].
        intro p; inversion p.
        intro p. generalize (eq_refl (a::l)). refine (match p as q in In _ l' return l' = a::l -> forall H : forall x : α, x ∈ l' -> x ∈ G, In_UR e (H e q) l' (elements_UR_l l' H) q with | In_cons l' => _ | In_tail l' y q => _ end); simpl.
        intros _ H. constructor 1.
        intro Heq. inversion Heq. subst y l'. clear Heq. intro H. constructor 2. exact (IHl q (fun (x : α) (H1 : x ∈ l) => H x (In_tail x l a H1))).
      Qed.

      Let e_comp_UR_G : In_UR e UR_e G elements_UR_G (e_comp G) :=
        e_comp_UR_l G (e_comp G) (fun x H => H).


      Lemma op_comp_UR_G : forall x (x_UR : UR x) y (y_UR : UR y),
        forall (p : x ∈ G), In_UR x x_UR G elements_UR_G p ->
        forall (q : y ∈ G), In_UR y y_UR G elements_UR_G q ->
          In_UR (x·y) (UR_op x y x_UR y_UR) G elements_UR_G (op_comp G x y p q).
      Proof.
        intros x x_UR y y_UR p _ q _. apply In_UR_URW. apply In_InUR. auto.
      Qed.


      Lemma inv_comp_UR_G : forall x (x_UR : UR x) (p : x ∈ G),
        In_UR x x_UR G elements_UR_G p ->
        In_UR (inv x) (UR_inv x x_UR) G elements_UR_G (inv_comp G x p).
      Proof.
        intros x x_UR p _. apply In_UR_URW. apply In_InUR. auto.
      Qed.


      Let fingrp_UR_G := Fingrp_UR G elements_UR_G e_comp_UR_G op_comp_UR_G inv_comp_UR_G.
      Let fingrp_UR_ZG := Z_param' G fingrp_UR_G.


      Lemma subgroup_l : forall l, list_UR l -> forall x, x ∈ l -> x ∈ G.
      Proof.
        induction l as [ |a l IHl].
        intros _ x H; inversion H.
        intro H. inversion H. subst. intros x H1. inversion H1; subst; auto.
      Qed.

      Theorem subgroup : forall x, x ∈ (Z G) -> x ∈ G.
      Proof.
        generalize (elements_UR UR UR_e UR_op UR_inv (Z G) fingrp_UR_ZG). apply subgroup_l.
      Qed.

    End Inclusion.

  End Parametricity2.

End GroupTheory.
