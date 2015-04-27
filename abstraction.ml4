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


VERNAC COMMAND EXTEND Abstraction
| [ "Abstraction" constr(a) ne_preident_list(names) ] ->
  [
    Translation.top_abstraction a names
  ] 
| [ "Abstraction" constr(a) ] ->
  [
    Translation.top_abstraction a []
  ] 
END


TACTIC EXTEND param
| [ "param" constr(a) "as" ident(name) ] -> [ Translation.tactic_name a name ]
| [ "param" constr(a) ] -> [ Translation.tactic a ]
END
