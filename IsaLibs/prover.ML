(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature PROVER =
sig

  val max_time_in_proof  : int Config.T

  val prove              : local_theory -> thm list option -> Method.text_range -> 
                           term -> int -> thm option

  val prove_schematic_from_method : Proof.context -> thm list option ->
                                    Method.text_range -> term -> term option

  val cheat_prover       : Proof.context -> term -> thm
  val induct_auto_method : Proof.context -> Method.text_range
  val prove_from_tactic  : local_theory -> thm list option -> (Proof.context -> tactic) ->
                           term -> int -> thm option
end

structure DB_Prover
(* : COMMANDS *)
= struct

val (max_time_in_proof, setup_max_time_in_proof) = Attrib.config_int @{binding "max_time_in_proof"} (K 10)

val method_setup =
    Method.setup (Binding.name "spass_auto")
                 (Scan.succeed (fn ctxt => 
                                   SIMPLE_METHOD (Sledgehammer_Tactics.sledgehammer_with_metis_tac
                                                    ctxt [("timeout",Int.toString (Config.get ctxt max_time_in_proof))]
                                                    Sledgehammer_Fact.no_fact_override [] 1)))
                 "interleave spass and ..."

val _ = Context.>> (Context.map_theory method_setup)

fun sledgehammer_method ctxt = Utils.parse ctxt (Method.parser 1) "spass_auto" |> fst
fun induct_auto_method ctxt = Utils.parse ctxt (Method.parser 1) "induct_auto" |> fst

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun parse_schematic_goal ctxt = Utils.parse ctxt (long_statement || short_statement)

fun prove_from_method ctxt0 (SOME simps) method conjecture =
  let (* for rewriting methods *)
      val ctxt = ctxt0 addsimps simps
      (* for non-rewriting methods *)
      (* FIXME: for some reason this is not perceived by sledgehammer *)
(*      val (_, ctxt) = Proof_Context.note_thmss "" [((Binding.empty,[]), [(simps,[])])] ctxt*)
      (*val ctxt = ctxt0 |> Context.Proof
                       |> Simplifier.map_ss (fn simpset => simpset addsimps simps)
                       |> Context.the_proof*)
(*                       |> tap (fn _ => tracing ("Using: " ^ Utils.str_of_thms simps))*)
(*      val ctxt = put_simpset HOL_basic_ss ctxt0 addsimps simps*)
  in prove_from_method ctxt NONE method conjecture end
| prove_from_method ctxt0 NONE method conjecture =
  let val frees = [] |> Term.add_frees conjecture |> map fst
(*      val _ = tracing ("Proving: " ^ (Syntax.string_of_term ctxt0 conjecture))*)
  in Utils.safe_eval "Not Proved!" NONE
     (fn ctxt0 =>
      ctxt0|> Variable.add_fixes frees
           |> snd
           |> Proof.theorem NONE (K I) [[(conjecture, [])]]
           |> Proof.apply method
(*           |> Seq.hd*)
           |> (Seq.hd o Seq.filter_results)
           |> `Proof.goal
           ||> Proof.global_done_proof
           (* FIXME: facts should be used in a locale or type class context! *)
           |> (fn ({goal,...},ctxt) => 
                  if 0 = Thm.nprems_of goal 
                  then goal |> Goal.finish ctxt
(*                               |> Thm.check_shyps (Variable.sorts_of ctxt)*)
                            |> Assumption.export false ctxt ctxt0
                            |> single
                            |> Variable.export ctxt ctxt0
                            |> hd
                            |> Drule.zero_var_indexes
(*                            |> tap (fn th => tracing ("Proved!: " ^ Utils.str_of_thms [th]))*)
                            |> SOME
                  else ((*tracing ("Not proved!");*) NONE))) ctxt0
      end

fun prove_schematic_from_method ctxt0 (SOME simps) method conjecture =
  let val ctxt = ctxt0 addsimps simps
  in prove_schematic_from_method ctxt NONE method conjecture end
| prove_schematic_from_method ctxt0 NONE method conjecture =
  let val (long, binding, includes, elems, concl) = 
                conjecture |> Utils.string_of_term' ctxt0
                           |> enclose "\"" "\""
                           |> parse_schematic_goal ctxt0
                           |> fst
     (* FIXME: Make it work for more than one schematic variables *)
      fun dest_conjecture (Const _ $ (Const (conj, _) $ _ $ conjecture)) =
            if conj = Const_Names.schematic_and
            then SOME conjecture
            else NONE
        | dest_conjecture _ = NONE
  in Utils.safe_eval "" NONE
     (fn ctxt0 =>
      ctxt0|> Specification.schematic_theorem_cmd long Thm.theoremK NONE (K I) binding includes elems concl false
           |> Proof.apply method
           |> (Seq.hd o Seq.filter_results)
           |> `Proof.goal
           ||> Proof.global_done_proof
           (* FIXME: facts should be used in a locale or type class context! *)
           |> (fn ({goal,...},_) =>
                  if 0 = Thm.nprems_of goal
                    then goal |> Thm.full_prop_of
(*                              |> SOME*)
                              |> dest_conjecture
                  else NONE)) ctxt0
      end

fun prove_from_spass ctxt0 args conjecture = 
  prove_from_method ctxt0 args (sledgehammer_method ctxt0) conjecture

fun prove ctxt args method conjecture timeOut = 
  let fun prove' ctxt args method conjecture timeOut = 
  (conjecture
    |> Utils.apply_timeout1 (Time.fromSeconds timeOut)
                           (fn conj => prove_from_method ctxt args method conj
                                      handle  Utils.TIMEOUT1 _ => NONE
                                    | Utils.TIMEOUT2 _ => NONE
                                    | Timeout.TIMEOUT _ => NONE))
      handle Utils.TIMEOUT1 _ => NONE
  in if can Local_Theory.target_of ctxt
     then let val ctxt = Local_Theory.target_of ctxt
          in prove' ctxt args method conjecture timeOut end
     else prove' ctxt args method conjecture timeOut
  end

(*fun prove_schematic ctxt args method conjecture timeOut =
  let fun prove' ctxt args method conjecture timeOut = 
  (conjecture
    |> Timeout.apply (Time.fromSeconds timeOut)
                           (prove_schematic_from_method ctxt args method))
      handle Timeout.TIMEOUT _ => NONE
  in if can Local_Theory.target_of ctxt
     then let val ctxt = Local_Theory.target_of ctxt
          in prove' ctxt args method conjecture timeOut end
     else prove' ctxt args method conjecture timeOut
  end*)

fun prove_from_tactic ctxt args tactic conjecture timeOut = 
  prove ctxt args (Method.Basic (fn ctxt => SIMPLE_METHOD (tactic ctxt)), Position.no_range) conjecture timeOut

fun cheat_prover ctxt prop =
  (K (Skip_Proof.cheat_tac ctxt 1))
    |> Goal.prove ctxt [] [] prop


end

structure Prover : PROVER = DB_Prover



