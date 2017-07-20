(*  Title:      def_utils.ML
    ID:         $Id: def_utils.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Automatic extraction of rewrite rules and constants from definitions.
*)

signature DEF_UTILS =
sig

  val get_rewrites             : theory -> string -> thm list
  val definitional_dependencies  : theory -> ((string * typ) list * term) -> (string * typ) list

end

structure DB_Def_Utils
(* : DEF_UTILS *)
= struct

fun get_rewrites thy cons_name =
  let val simps = Utils.safe_eval "" [] (Global_Theory.get_thms thy)
                                        (cons_name ^ ".simps")
  in simps end

fun definitional_dependencies thy (consts : (string * typ) list, term) =
  let val thy_consts = Sign.consts_of thy
      fun dependencies (consts, cname) =
        let val deps = cname |> get_rewrites thy
                             |> map Thm.full_prop_of
                             |> pair consts
                             |> Library.foldl (fn (consts, t) =>
                                 Term.add_const_names t consts)
        in if length consts = length deps 
           then consts
           else Library.foldl dependencies (deps, deps)
        end
  in
    consts |> map fst
           |> Term.add_const_names term
           |> (fn consts => (consts, consts))
           |> Library.foldl dependencies
           |> map (fn cname => (cname, Consts.the_constraint thy_consts cname))
  end

(*
  val consts =  Sign.consts_of @{theory}
  val r = Consts.the_constraint consts "Groups.plus_class.plus"
*)

end

structure Def_Utils : DEF_UTILS = DB_Def_Utils

