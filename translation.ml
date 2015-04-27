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
open Entries
open Declare
open Decl_kinds
open Declarations
open Environ
open Inductive
open Termops
open Reduction


(* Get the content of a constant *)

let unfold_constant cst =  
  let cb = Global.lookup_constant cst in
  let body = match cb.const_body with 
    | None -> failwith "Translation.unfold: cannot translate an assumption"
    | Some lazy_body -> force lazy_body 
  in 
  body


(* Get the content and the type of a constant *)

let unfold_constant_with_type cst = 
  let cb = Global.lookup_constant cst in
  let body = match cb.const_body with 
    | None -> failwith "Translation.unfold_with_types: cannot translate an assumption"
    | Some lazy_body -> force lazy_body 
  in 
  let bodytype = match cb.const_type with 
    | NonPolymorphicType types -> types 
    | PolymorphicArity  (rel_context, p) -> failwith "Translation.translation_constant: PolymorphicArity wtf ?"
  in 
  body, bodytype


(* Deal with some exceptions *)

let on_failure f g = try f () with Failure "nth" -> g ()

let default i = 
  Util.errorlabstrm "abstraction" 
   (Pp.str (Printf.sprintf "abstraction: unable to translate variable '%d'" i))


(* Given A, compute A, A' and ⟦A⟧ *)

let rec first f e c =
  match kind_of_term c with
    | Rel i -> on_failure 
                 (fun () -> mkRel (List.nth e (i-1)))
                 (fun () -> 
                   let k = List.length e in 
                   lift k (f (i - k)))           
    | Var n ->  failwith (Printf.sprintf "Translation.first: Var (%s) not implemented" (string_of_id n))
    | Meta _ -> failwith "Translation.first: Meta not implemented"
    | Evar _ -> failwith "Translation.first: Evar not implemented"
    | Sort s -> mkSort s
    | Cast _ -> failwith "Translation.first: Cast not implemented"
    | Prod (x,a,b) ->
      let x' =
        match x with
          | Name y -> Name (id_of_string ((string_of_id y)^"'"))
          | Anonymous -> Anonymous in
      mkProd (x', first f e a, first f (1::(List.map (fun i -> i+1) e)) b)
    | Lambda (x,a,m) ->
      let x' =
        match x with
          | Name y -> Name (id_of_string ((string_of_id y)^"'"))
          | Anonymous -> Anonymous in
      mkLambda (x', first f e a, first f (1::(List.map (fun i -> i+1) e)) m)
    | LetIn _ -> failwith "Translation.first: LetIn not implemented"
    | App (g,args) -> mkApp (first f e g, Array.map (first f e) args)
    | Const _ -> c
    | Ind _ -> failwith "Translation.first: Ind not implemented"
    | Construct _ -> failwith "Translation.first: Construct not implemented"
    | Case _ -> failwith "Translation.first: Case not implemented"
    | Fix _ -> failwith "Translation.first: Fix not implemented"
    | CoFix _ -> failwith "Translation.first: CoFix not implemented"


let prime = first  (* prime is alpha-convertible to first *)


let translation f f' fR e e' eR c =
  let rec aux depth e e' eR c = match kind_of_term c with
    | Rel i -> on_failure 
                 (fun () -> mkRel (List.nth eR (i-1)))
                 (fun () -> 
                   let k = List.length eR in 
                   lift depth (fR (i - k)))           
    | Var n ->  failwith (Printf.sprintf "Translation.translation: Var (%s) not implemented" (string_of_id n))
    | Meta _ -> failwith "Translation.translation: Meta not implemented"
    | Evar _ -> failwith "Translation.translation: Evar not implemented"

    | Sort s -> mkLambda (Anonymous, mkSort s, mkLambda (Anonymous, mkSort s, mkArrow (mkRel 2) (mkArrow (mkRel 2) mkProp)))

    | Cast _ -> failwith "Translation.translation: Cast not implemented"

    | Prod (x,a,b) ->
      let (x',xR) =
        match x with
          | Name z ->
            let y = string_of_id z in
            let x' = Name (id_of_string (y^"'")) in
            let xR = Name (id_of_string (y^"_R")) in
            (x',xR)
          | Anonymous -> (Anonymous, Anonymous) in
      let g = Anonymous in
      let g' = Anonymous in

      let e1 = 3::(List.map (fun i -> i+5) e) in
      let e'1 = 2::(List.map (fun i -> i+5) e') in
      let eR1 = 1::(List.map (fun i -> i+5) eR) in

      let r5 = mkApp (aux (depth + 5) e1 e'1 eR1 b, [|mkApp (mkRel 5, [|mkRel 3|]); mkApp (mkRel 4, [|mkRel 2|])|]) in
      let r4 = mkProd (xR, mkApp (aux (depth + 4) (List.map (fun i -> i+4) e) (List.map (fun i -> i+4) e') (List.map (fun i -> i+4) eR) a, [|mkRel 2; mkRel 1|]), r5) in
      let r3 = mkProd (x', prime f' (List.map (fun i -> i+3) e') a, r4) in
      let r2 = mkProd (x, first f (List.map (fun i -> i+2) e) a, r3) in
      let r1 = mkLambda (g', prime f' (List.map (fun i -> i+1) e') c, r2) in
      mkLambda (g, first f e c, r1)

    | Lambda (x,a,m) ->
      let (x',xR) =
        match x with
          | Name z ->
            let y = string_of_id z in
            let x' = Name (id_of_string (y^"'")) in
            let xR = Name (id_of_string (y^"_R")) in
            (x',xR)
          | Anonymous -> (Anonymous, Anonymous) in

      let e1 = 3::(List.map (fun i -> i+3) e) in
      let e'1 = 2::(List.map (fun i -> i+3) e') in
      let eR1 = 1::(List.map (fun i -> i+3) eR) in

      let r3 = aux (depth + 3) e1 e'1 eR1 m in
      let r2 = mkLambda (xR, mkApp (aux (depth + 2) (List.map (fun i -> i+2) e) (List.map (fun i -> i+2) e') (List.map (fun i -> i+2) eR) a, [|mkRel 2; mkRel 1|]), r3) in
      let r1 = mkLambda (x', prime f' (List.map (fun i -> i+1) e') a, r2) in
      mkLambda (x, first f e a, r1)

    | LetIn _ -> failwith "Translation.translation: LetIn not implemented"
    | App (g,args) ->
      Array.fold_left (fun g x -> mkApp (g, [|first f e x; prime f' e' x;
      aux depth e e' eR x|])) (aux depth e e' eR g) args
    (* when we translate a constant if the constant has a registered relation, 
     * then we use it for its translation. Otherwise we translate the unfolded
     * constant.
     * *)
    (* On pourrait peut-être faire un [let ... in ...] ? *)
    | Const c ->  begin try 
         mkConst (Relations.get_relation c)
      with Not_found -> 
         aux 0 [] [] [] (unfold_constant c)
      end 
    | Ind _ -> failwith "Translation.translation: Ind not implemented"
    | Construct _ -> failwith "Translation.translation: Construct not implemented"
    | Case _ -> failwith "Translation.translation: Case not implemented"
    | Fix _ -> failwith "Translation.translation: Fix not implemented"
    | CoFix _ -> failwith "Translation.translation: CoFix not implemented"
  in aux 0 e e' eR c 


(* Utilities *)

let translation_identifier n = 
  id_of_string ((string_of_id n)^"_R")

let prime_identifier n = 
  id_of_string ((string_of_id n)^"'")


(* Translation of inductive definitions *)

let compute_length inds =
  let rec compute_length acc = function
    | [] -> acc
    | ind::q ->
      let (_,mip) = Global.lookup_inductive ind in
      compute_length ((Array.length mip.mind_consnames)+1+acc) q in
  compute_length 0 inds


let translation_inductive (ind : inductive) allnames = 
  let nnames = ref allnames in  (* pas beau *)
  let translation_one_inductive ind = 
    let (sp, tyi) = ind in
    let (mib,mip) = Global.lookup_inductive ind in
    let typename = mip.mind_typename in
    let typename_R =
      match !nnames with
        | [] -> translation_identifier typename
        | t::q -> nnames := q; id_of_string t in
    let params = mib.mind_params_ctxt in
    let args = extended_rel_list 0 params in
    let env = Global.env() in
    let fullarity = match mip.mind_arity with
      | Monomorphic ar -> ar.mind_user_arity
      | Polymorphic ar ->
        it_mkProd_or_LetIn 
          (mkSort (Type ar.poly_level))
          mip.mind_arity_ctxt 
    in
    let arity = hnf_prod_applist env fullarity args in
    let arity_R = 
      mkApp ((translation default default default [] [] [] arity),
             [|mkInd ind; mkInd ind|])
    in 
    let consnames = mip.mind_consnames in 
    let consnames_R =
      List.map (fun n ->
        match !nnames with
          | [] -> translation_identifier n
          | t::q -> nnames := q; id_of_string t)
        (Array.to_list consnames)
    in 
    let lc = mip.mind_user_lc in 
    let first_ind i = 
      (*
        Pp.msgnl (Pp.str (Printf.sprintf "inductive index : %d" i));
      *)
      mkInd (sp, i-1)
    in 
    let identity i = mkRel i in 
    let lc_R = 
      Array.to_list 
        (Array.mapi (fun n ct ->
          let c = mkConstruct (ind, n+1) in 
          let r =  mkApp 
            ((translation first_ind first_ind identity [] [] [] ct),
                  [|c;c|])
          in nf_betaiota r) lc)
    in 
    Pp.msgnl (Printer.pr_constr arity_R);
    Array.iter (fun x -> Pp.msgnl (Printer.pr_constr x)) lc;
    List.iter (fun x -> Pp.msgnl (Printer.pr_constr x)) lc_R;
    {
      mind_entry_typename = typename_R;
      mind_entry_arity = arity_R; 
      mind_entry_consnames = consnames_R;
      mind_entry_lc = lc_R
    }
  in
  let rec translate_context acc acc' accR = function 
      [] -> []
    | (Name x, None, t)::tl -> 
        let x' = prime_identifier x in 
        let xR = translation_identifier x in 
        let a = first default acc t in 
        let a' = prime default acc' t in 
        let aR = mkApp
          (translation default default default acc acc' accR t, 
           [|a;a'|])
        in 
        let acc = List.map (fun i -> i+3) acc in 
        let acc' = List.map (fun i -> i+3) acc' in 
        let accR = List.map (fun i -> i+3) accR in 
        (x, LocalAssum a)::(x', LocalAssum a')::(xR,LocalAssum aR)
                    ::(translate_context acc acc' accR tl)
    | _ -> failwith "param not implemented yet"
  in 
  let translation_mutual_inductive sp = 
    let (mib, _) = Global.lookup_inductive (sp,0) in
    let mipv = mib.mind_packets in
    let names = Util.list_tabulate (fun x -> (sp,x)) (Array.length mipv) in

    let namesl = compute_length names in
    let allnamesl = List.length allnames in
    if (allnamesl = 0) || (allnamesl = namesl) then
      let record_R = mib.mind_record in
      let finite_R = mib.mind_finite in
      let params = mib.mind_params_ctxt in
      let params_R = translate_context [] [] [] params in
      let inds_R = List.map translation_one_inductive names in {
        mind_entry_record = record_R;
        mind_entry_finite = finite_R;
        mind_entry_params = params_R;
        mind_entry_inds = inds_R
      }
    else
      let i = string_of_int namesl in
      failwith ("In the case of this inductive, Abstraction expects 0 or "^i^" identifiers")
  in 
  declare_mind UserVerbose (translation_mutual_inductive (fst ind))


(** Adds the definition name := ⟦a⟧ : ⟦b⟧ a a. *)

let declare_abstraction a b name =
  let c = translation default default default [] [] [] a in
  let d = mkApp (translation default default default [] [] [] b, [|a;a|]) in
  let ce =
    { const_entry_body = c;
      const_entry_type = Some (Reduction.nf_betaiota d);
      const_entry_opaque = false;
      const_entry_boxed = false} in
  declare_constant name (DefinitionEntry ce, IsDefinition Definition)


(** Declare [name : ⟦a⟧]. If [a] is a constant, add it to the set of
    known relations. *)

let top_abstraction a names = 
  let constr_of_constr_expr c =
    Constrintern.interp_constr Evd.empty (Global.env ()) c
  in 
  let a = constr_of_constr_expr a in
  match kind_of_term a with
    | Const c ->
      let name =
        match names with
          | [] -> translation_identifier (snd (Libnames.decode_con c))
          | [name] -> id_of_string name
          | _ -> failwith "In the case of a constant, Abstraction expects 0 or 1 identifier." in
      let a, b = unfold_constant_with_type c in
      let c_R = declare_abstraction a b name in
      Relations.add_relation c c_R
    | Ind i -> ignore (translation_inductive i names)
    | _ ->
      let name =
        match names with
          | [name] -> id_of_string name
          | _ -> failwith "In the case of a term, Abstraction expects 1 identifier" in
      let b = Retyping.get_type_of (Global.env ()) Evd.empty a in
      let _ = declare_abstraction a b name in
      ()


(* A tactic on top of this *)

let tactic_name a name gl =
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let b = Retyping.get_type_of env sigma a in
  let c = translation default default default [] [] [] a in
  let d = mkApp (translation default default default [] [] [] b, [|a;a|]) in
  Tactics.letin_tac None (Name name) c (Some (Reduction.nf_betaiota d)) Tacticals.onConcl gl


let tactic a =
  let name = id_of_string "H" in
  tactic_name a name
