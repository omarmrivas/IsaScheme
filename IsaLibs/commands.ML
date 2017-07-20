(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature COMMANDS =
sig
end

structure DB_Commands
(* : COMMANDS *)
= struct

val complete_parser =
      Parse.prop

fun map_contexts f =
  Local_Theory.background_theory
        (Context.theory_map f) #>
        Local_Theory.target (Context.proof_map f) #>
        Context.proof_map f

val _ =
  let
    fun goal_prop str ctxt =
      let val limit = Config.get ctxt Proof_Tools.max_depth_in_meta_induction
          val conjecture = Syntax.read_prop ctxt str
      in case Utils.timing_wrapper (Proof_Tools.meta_induction Proof_Tools.find_lemmas ctxt limit) conjecture of
              SOME (additions, deletions) =>
                    (ctxt, additions)
                      |> tap (fn (_, thms) => tracing ("Additions: " ^ Utils.str_of_thms thms))
                      |> Library.foldl (fn (ctxt, thm) => map_contexts (Completion_Rules.add_thm thm) ctxt)
                      |> rpair deletions
                      |> tap (fn (_, thms) => tracing ("Deletions: " ^ Utils.str_of_thms thms))
                      |> Library.foldl (fn (ctxt, thm) => map_contexts (Completion_Rules.del_thm thm) ctxt)
            | NONE => ctxt
      end
  in Outer_Syntax.local_theory
         @{command_keyword "rec_complete"}
         "Proves a new equational lemma and performs ground completion."
         (complete_parser >> goal_prop)
  end


val _ =
      let fun goal_prop str ctxt =
            let
              val prop = Syntax.read_prop ctxt str
              fun after_qed thms ctxt = 
                let val rule = thms |> (hd o flat)
                                    |> Utils.obj_to_meta
                    val terminates = Aprove.memoized_terminates ctxt
                    val TRS = (Thm.full_prop_of rule) |> global_lemmas ctxt
                                                      |> map Utils.obj_to_meta
                    val (additions, deletions) =
                            rule |> Ground_Completion.run_completion' [] ctxt terminates TRS
                                 |> apply2 (map Utils.meta_to_obj)
                in (ctxt, additions)
                      |> tap (fn (_, thms) => tracing ("Additions: " ^ Utils.str_of_thms thms))
                      |> Library.foldl (fn (ctxt, thm) => map_contexts (Completion_Rules.add_thm thm) ctxt)
                      |> rpair deletions
                      |> tap (fn (_, thms) => tracing ("Deletions: " ^ Utils.str_of_thms thms))
                      |> Library.foldl (fn (ctxt, thm) => map_contexts (Completion_Rules.del_thm thm) ctxt)
                end
            in
              Proof.theorem NONE (after_qed) [[(prop, [])]] ctxt
            end
      in Outer_Syntax.local_theory_to_proof
      @{command_keyword "complete"}
         "Proves a new equational lemma and performs ground completion."
         (complete_parser >> goal_prop) end

end

structure Commands : COMMANDS = DB_Commands

