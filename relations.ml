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


open Term
open Names

let relations = ref Cmap.empty 

let add_relation (c : constant) (c_R : constant) = 
  relations := Cmap.add c c_R !relations

let get_relation c = 
  Cmap.find c !relations

let freeze () = !relations 

let unfreeze rels =
    relations := rels

let init () =
    relations:= Cmap.empty

let _ =
    Summary.declare_summary "parametricity"
        { Summary.freeze_function = freeze;
          Summary.unfreeze_function = unfreeze;
          Summary.init_function = init }


