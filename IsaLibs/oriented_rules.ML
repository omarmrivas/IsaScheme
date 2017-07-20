(*  Title:      util/oriented_rules.ML
    ID:         $Id: oriented_rules.ML,v 1.00 2015/15/09 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

User suplied orientations for specific rule shapes.
*)

signature ORIENTED_RULES =
sig
(*  val get_orientation_schemes : unit -> term list*)
end

structure DB_Oriented_Rules
(* : ORIENTED_RULES *)
= struct

(*val parser = Args.context -- Scan.lift Args.name_inner_syntax*)
val parser = Args.embedded_inner_syntax

(*structure Term_Tab = Table(type key = term val ord = Term_Ord.term_ord)

val rules_var = Synchronized.var "oriented_rules"
                                 (Term_Tab.empty : unit Term_Tab.table)

fun get_orientation_schemes () = 
  rules_var |> Synchronized.value
            |> Term_Tab.dest
            |> map fst*)

fun memoized_rules rule =
  Utils.memoize_function Term_Tab.lookup Term_Tab.update Utils.oriented_rules_var
                         (fn _ => ()) rule

fun map_contexts f =
  Local_Theory.background_theory
        (Context.theory_map f) #>
        Local_Theory.target (Context.proof_map f) #>
        Context.proof_map f

val _ =
  let
    fun term_pat str ctxt =
     str |> Proof_Context.read_term_pattern ctxt
         |> memoized_rules
         |> (fn _ => ctxt)
  in Outer_Syntax.local_theory
         @{command_keyword "orient_rules"}
         "User suplied orientations for specific rule shapes."
         (parser >> term_pat)
  end

end

structure Oriented_Rules : ORIENTED_RULES = DB_Oriented_Rules

