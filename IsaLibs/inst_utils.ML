(*  Title:      Discovery/inst_utils.ML
    ID:         $Id: inst_utils.ML,v 1.010 2010/01/20 15:22:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   University of Edinburgh 2010

Instantiation of propositional and definitional schemes.
*)

signature INST_UTILS =
sig
  (* Instantiation support *)
  val dummyTvfy                      : term -> term
  val compatible_arguments           : Proof.context -> term -> term list -> term list -> (term * term list) list
  val vars_ordered                   : Proof.context -> thm -> (string * term * term list)
  val combine                        : Proof.context -> thm -> (term -> 'a -> 'a) -> term -> (term * term list) list -> 'a -> 'a
  val arity_of_schemes               : term list -> int list
end

structure DB_Inst_Utils
(* : INST_UTILS *)
= struct

(* Inserts dummyT on every free and var type variable to assist type unification *)
fun dummyTvfy t = t |> Term.map_types (map_type_tfree (fn _ => dummyT))
                    |> Term.map_types (map_type_tvar (fn _ => dummyT))

(* Selects those arguments in "args" whose type could be unified with each type
   in the scheme's arguments to reduce the numbers of possible instantiations. *)
fun compatible_arguments ctxt scheme_lhs args vars = 
    let fun test t v h = 
            t |> Term.subst_free [(v,h)]
              |> try (Syntax.check_term ctxt)
              |> is_some
    in map (fn v => (v,filter (test scheme_lhs v) args)) vars end

(* transform a term s of type t1 => .. => tn => t0 to (s x1 .. xn) of type t0 *)
fun expand_scheme ctxt thm = 
    let
      val t = thm |> Thm.full_prop_of
                  |> Logic.unvarify_global
                  |> (fst o Logic.dest_equals)
                  |> (fst o Term.strip_comb)
      val scheme_name = (fst o Term.dest_Const) t
      val typs = t |> Term.fastype_of |> Term.strip_type |> fst
      val frees = [] |> Term.add_frees t |> map fst
      fun apply vars (typ :: typs) t = 
          let val name = singleton (Name.variant_list vars) "x"
          in apply (name :: vars) typs (t $ (Free (name, typ)))
          end
        | apply _ [] t = (*dummyTvfy*) t
      val expanded = apply frees typs t
    in
      (* FIXME: reverse the variables *)
      (scheme_name, dummyTvfy expanded,
       Utils.normalise_term (empty_simpset ctxt) [thm] expanded,
       [] |> Term.add_frees (dummyTvfy expanded) |> map Free |> rev)
    end

fun vars_ordered ctxt thm =
    let
      fun var_depth (Abs(_,_,t)) name = 1 + (var_depth t name)
        | var_depth (f$t) name = 1 + Int.min(var_depth f name, var_depth t name)
        | var_depth (Free (v,_)) name = (if v = name then 0 else 10000)
        | var_depth _ _ = 10000
      val (scheme_name,scheme_lhs,scheme_rhs,vars) = expand_scheme ctxt thm
    in
      (scheme_name, scheme_lhs,
       vars |> map (fn (Free (name,ty)) => ([var_depth scheme_rhs name],(Free (name,ty)))
                      | _ => raise ERROR "")
            |> sort (list_ord int_ord o apply2 fst)
            |> map snd)
    end


(* Performs the instantiation over schemes automatically *)
fun combine ctxt def process_method t l store = 
    case l of
      (v,(h::[])) :: [] => t |> Term.subst_free [(v,h)]
                             |> try (Syntax.check_term ctxt)
                             |> (fn si => case si of SOME i => process_method i store | NONE => store)
    | (v,(h::t1)) :: [] => t |> Term.subst_free [(v,h)]
                             |> try (Syntax.check_term ctxt)
                             |> (fn r => case r of SOME x => combine ctxt def process_method t [(v,t1)] (process_method x store)
				                                         | NONE => combine ctxt def process_method t [(v,t1)] store)
    | (v,(h::t1)) :: t2 => 
      let val x = Term.subst_free [(v,h)] t in
        x |> try (Syntax.check_term ctxt)
          |> (fn r => case r of 
                        SOME t' => 
                        let 
                          val unfolded = Utils.normalise_term (empty_simpset ctxt) [def] t'
                          val frees = Term.add_frees unfolded []
                          val t2' = filter (fn (Free (name,_),_) => exists (fn (name',_) => name = name') frees
                                              | _ => raise ERROR "") t2
                        in
                          store |> combine ctxt def process_method x t2'
                                |> combine ctxt def process_method t ((v,t1) :: t2)
                        end
				              | NONE => combine ctxt def process_method t (append [(v,t1)] t2) store) end
    | _ => store

fun arity_of_schemes prop_schemes = 
    prop_schemes |> map (snd o Term.dest_Const o fst o Term.strip_comb)
                 |> maps (fn ty => ty |> (fst o Term.strip_type)
                                      |> map (length o fst o Term.strip_type)
                                      |> distinct (op =))
                 |> distinct (op =)

end

structure Inst_Utils : INST_UTILS = DB_Inst_Utils
