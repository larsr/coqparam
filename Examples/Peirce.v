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


(* Peirce's law *)

Definition peirce := (forall (X:Prop) (Y : Prop), ((X -> Y) -> X) -> X).


(* We use our command to compute the parametricity relation associated
   to peirce *)

Abstraction peirce peirce_R.


(* We prove it is not parametric *)

Lemma peirce_not_parametric : forall h1 h2, ~(peirce_R h1 h2).
Proof.
  intros h1 h2 H.
  apply (H True True (fun _ _ => False)
    True False (fun _ _ => True)); auto.
Qed.
