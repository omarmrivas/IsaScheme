(*  Title:      util/induct_tacs.ML
    ID:         $Id: induct_tacs.ML,v 1.010 2015/15/01 14:33:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

An inductive decision procedure using Isabelle's tactics.
This tactic behaves more nicely w.r.t. equivalent proofs.
e.g. F x1 ... xn = G x1 ... xn. It also considers variables
quantified at the meta level ("!!") and searches for a proof
using A* where the heuristic is: pending goals + depth of search.
*)

infix 0 INTERLEAVE INTERLEAVE'

signature INDUCTIVE_TACS =
sig
  datatype result = Theorem of thm | Failure of term list

  (* Utilery tactics *)

  val INTERLEAVE  : ('a -> 'b Seq.seq) * ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq
  val INTERLEAVE' : ('a -> 'b -> 'c Seq.seq) * ('a -> 'b -> 'c Seq.seq) -> 'a -> 'b -> 'c Seq.seq
  val astar_ind_auto_tac : Proof.context -> tactic
  val iter_dep_ind_auto_tac : Proof.context -> tactic
  val inductive_prover_tactic: Proof.context -> int -> tactic
(*  val induct_auto_tac             : term_set Unsynchronized.ref -> Proof.context -> int -> tactic
  val bef_induct_auto_tac         : term_set Unsynchronized.ref -> Proof.context -> tactic*)
end

structure DB_InductiveTacs
(* : INDUCTIVE_TACS *)
= struct

fun (tac1 INTERLEAVE tac2) st =
  Seq.interleave (tac1 st, Seq.make (fn()=> Seq.pull (tac2 st)))

fun (tac1 INTERLEAVE' tac2) x =
  tac1 x INTERLEAVE tac2 x

fun TRY' tac x = 
  TRY (tac x)

fun vars_in_concl goal =
  goal |> Utils.binder_elimination Const_Names.meta_forall []
       |> fst
       |> Logic.strip_imp_concl
       |> (fn t => Term.add_frees t [])

fun frees_in_concl goal =
  goal |> Term.strip_all_body
       |> Logic.strip_imp_concl
       |> (fn t => Term.add_frees t [])

(* Function that returns valid computational induction applications *)
fun inductive_applications thy prop =
  let
    val prop = prop |> Utils.binder_elimination Const_Names.meta_forall []
                    |> fst
                    |> Logic.strip_imp_concl
    fun inductive_apps thy prop =
      let
        val (t,args) = Term.strip_comb prop
      in
        case t of
           Const _ =>
           (t |> (fst o Term.dest_Const)
              |> (fn name => name ^ ".induct")
              |> (fn name => (args, Global_Theory.get_thm thy name))
              |> (fn rule => rule :: maps (inductive_apps thy) args)
              handle ERROR _ => maps (inductive_apps thy) args
                    | TERM _ => maps (inductive_apps thy) args)
         | Abs (n, T, _) => betapply (t, Free (n, T))
                              |> inductive_apps thy
                              |> (fn res => res @ maps (inductive_apps thy) args)
         | _ =>  maps (inductive_apps thy) args
      end
    val transform = map (fn Free (n, _) => SOME n
                           | _ => NONE)
  in
    prop |> inductive_apps thy
         (* Applications with smaller arguments are considered first *)
         |> sort (fn args =>
                    args |> apply2 fst
                         |> apply2 (map Term.size_of_term)
                         |> apply2 (fn l => Library.foldl (op +) (0, l))
                         |> int_ord)
(*         |> tap (map (fn (y, z) => y |> map (Syntax.string_of_term_global thy)
                                     |> (fn str => str @ [Utils.str_of_thms [z]])
                                     |> space_implode ", "
                                     |> tracing))*)
         |> map (fn (y, z) => (transform y, z))
  end

fun computation_induction_tac ctxt thy (goal, i) =
    let val vs_inducts = inductive_applications thy goal
    in (no_tac, vs_inducts)
         |> Library.foldl (fn (thms,(vs,th)) =>
             (fn thh => DETERM (Induct_Tacs.induct_tac ctxt [vs] (SOME [th]) i) thh
                        handle ERROR err => (tracing (err ^ " : " ^ Syntax.string_of_term ctxt goal); raise ERROR err))
             APPEND thms)
    end

fun cases_tac ctxt =
   SUBGOAL (fn (goal, i) =>
     let val frees = goal |> frees_in_concl
                          |> map fst
     in
         List.foldl (op THEN_ALL_NEW) (fn _ => all_tac)
                    (List.map (fn n => Induct_Tacs.case_tac ctxt n [] NONE) frees) i
     end)

(* Split technique *)
local
 fun fold_atyps' f (Type (n, Ts)) a = fold (fold_atyps' f) Ts (f (Type (n, Ts)) a)
   | fold_atyps' f T a = f T a
 val add_type_namesT = fold_atyps' (fn Type (xi, _) => insert (op =) xi | _ => I)
 fun get_split thy name = Global_Theory.get_thms thy (name ^ ".splits")
                           handle ERROR _ => []
 fun get_all_splits thy vars =
  vars |> map snd
       |> pair []
       |> Library.foldl (fn (names, ty) => add_type_namesT ty names)
       |> maps (get_split thy)
in
fun split_tactic ctxt thy vars (_, i) =
     (no_tac, get_all_splits thy vars)
      |> Library.foldl (fn (tac,split) => (DETERM (Splitter.split_tac ctxt [split] i)) APPEND tac)
end

fun cases_tac' ctxt frees_str (_, i) =
     List.foldl (op THEN_ALL_NEW) (fn _ => all_tac)
                (List.map (fn n => Induct_Tacs.case_tac ctxt n [] NONE) frees_str) i

fun arbitrary_tac ctxt =
   SUBGOAL (fn (goal, i) =>
     let val frees = frees_in_concl goal
     in
        Induct.arbitrary_tac ctxt 0 frees i
     end)

fun arbitrary_tac' ctxt (goal, i)  =
     let val frees = frees_in_concl goal
     in
        Induct.arbitrary_tac ctxt 0 frees i
     end

fun structural_induction_tac ctxt frees fixes (goal, i) =
  let val var_sets = (frees @ fixes)
                        |> distinct (op =)
                        (* Select only inductive vars *)
                        |> map_filter (fn (s, T) =>
                              let val ind_rules = Induct.find_inductT ctxt T
                              in if null ind_rules
                                 then NONE
                                 else SOME ((s, T), ind_rules)
                              end)
                        (* Group sets of vars with the same type *)
                        |> Library.partition_eq (is_equal o Term_Ord.typ_ord o (apply2 (snd o fst)))
                        |> maps (fn l => let val rules = (single o hd o snd o hd) l
                                             val vs = map (SOME o fst o fst) l
(*                                             val vss = Utils.subsets vs*)
                                             val vs_rules = map_product pair vs rules
                                         in vs_rules end)
  in
    (no_tac, var_sets)
      |> Library.foldl (fn (thms,(v,th)) =>
           (fn thh => DETERM (Induct_Tacs.induct_tac ctxt [[v]] (SOME [th]) i) thh
                            handle ERROR err => (tracing (err ^ " : " ^ Syntax.string_of_term ctxt goal);
                                               tracing "Frees: ";
                                               map (tracing o (Syntax.string_of_term ctxt) o Free) frees;
                                               tracing "Fixes: ";
                                               map (tracing o (Syntax.string_of_term ctxt) o Free) fixes;
                                               raise ERROR err))
              APPEND thms)
  end

(* simple auto tac *)
fun auto_clasimpset_tac ctxt (_:int) =
  CHANGED (auto_tac ctxt)

fun only_structural_induction_tac ctxt (goal, i) =
  let val frees = frees_in_concl goal
      val vars = vars_in_concl goal
      val fixes = subtract (op =) frees vars
(*      val _ = (tracing "Frees: ";
               map (tracing o (Syntax.string_of_term ctxt) o Free) frees;
               tracing "Vars: ";
               map (tracing o (Syntax.string_of_term ctxt) o Free) vars;
               tracing "Fixes: ";
               map (tracing o (Syntax.string_of_term ctxt) o Free) fixes)*)
  in structural_induction_tac ctxt frees fixes (goal, i) end

fun primitive_induction ctxt (goal, i) =
  let val thy = Proof_Context.theory_of ctxt
      val frees = frees_in_concl goal
      val vars = vars_in_concl goal
      val fixes = subtract (op =) frees vars
      val tac' = (structural_induction_tac ctxt frees fixes (goal, i) APPEND
                  computation_induction_tac ctxt thy (goal, i) APPEND
                  split_tactic ctxt thy vars (goal, i))
      val tac = tac' THEN (TRY (auto_clasimpset_tac ctxt i))
  in tac(*tac ORELSE tac'*)
  end

(* Failure analysis *)
fun check_fail_proof_state sts ctxt =
  fn (goal, _) =>
  let val thy = Proof_Context.theory_of ctxt
      val _ = sts := Net.insert_term_safe (Pattern.equiv thy) (goal,goal) (!sts)
  in no_tac end

fun ind_auto_tac ctxt =
    (CHANGED o ALLGOALS)
       (SUBGOAL (primitive_induction ctxt))

(*fun ind_auto_tac' sts ctxt =
    SOLVE ((CHANGED o ALLGOALS)
       (SUBGOAL ((primitive_induction ctxt) THEN' (TRY' (check_fail_proof_state sts ctxt)))))*)

fun ind_auto_failure sts ctxt =
    SOLVE ((CHANGED o ALLGOALS)
       ((SUBGOAL (primitive_induction ctxt)) THEN'
        (TRY' (SUBGOAL(check_fail_proof_state sts ctxt)))))

(*(* Performs induction and rewriting then stores remaining subgoals in fails *)
fun induct_auto_tac' set fails ctxt = 
        SOLVE ((CHANGED o ALLGOALS)
           (((EVERY' [SUBGOAL (choose_induct_tac set ctxt),
                        auto_clasimpset_tac ctxt]) APPEND' (auto_clasimpset_tac ctxt))
      THEN' (TRY' (check_fail_proof_state fails ctxt))))*)

(* Probably there is a better way to know if we have proved the theorem *)
(* this function won't work in goals with spurious premises *)
fun theorem_proved' thm = Thm.no_prems thm

fun theorem_proved timeout timer thm = 
  if Thm.no_prems thm
  then true
  else let val t_end = timer |> Timing.result
                             |> #elapsed
                             |> Time.toSeconds
       in t_end >= timeout end

(* Our heuristic is simply the number of premises (in our interpretation... the pending goals)
   plus the depth in search (shorter proofs are preferred). *)
fun theorem_heuristic i thm = Thm.nprems_of thm + i

(* A* search: similar to BEST_FIRST but current level of search is taken into account *)
fun bfirst_ind_auto_tac (ctxt : Proof.context) thm =
  let val timeout = Prover.max_time_in_proof
                      |> Config.get ctxt
      val _ = thm |> ((Utils.latex_string_of_term ctxt) o (Thm.concl_of))
                  |> (fn str => tracing ("Latex: " ^ str))
  in
    Timeout.apply (Time.fromSeconds timeout) (BEST_FIRST (theorem_proved',theorem_heuristic 0) (ind_auto_tac ctxt)) thm
      handle Timeout.TIMEOUT _ => Seq.empty
  end
(* A* search: similar to BEST_FIRST but current level of search is taken into account *)
fun astar_ind_auto_tac (ctxt : Proof.context) thm =
  let val timeout = Prover.max_time_in_proof
                      |> Config.get ctxt
      val _ = thm |> ((Utils.latex_string_of_term ctxt) o (Thm.concl_of))
                  |> (fn str => tracing ("Latex: " ^ str))
  in
    Timeout.apply (Time.fromSeconds timeout) (ASTAR (theorem_proved',theorem_heuristic) (ind_auto_tac ctxt)) thm
      handle Timeout.TIMEOUT _ => Seq.empty
  end

fun iter_dep_ind_auto_tac (ctxt : Proof.context) thm =
  let val timeout = Prover.max_time_in_proof
                      |> Config.get ctxt
      val _ = thm |> ((Utils.latex_string_of_term ctxt) o (Thm.concl_of))
                  |> (fn str => tracing ("Latex: " ^ str))
  in
    Timeout.apply (Time.fromSeconds timeout) (ITER_DEEPEN 10 theorem_proved' (fn _ => ind_auto_tac ctxt)) thm
      handle Timeout.TIMEOUT _ => Seq.empty
  end

fun dep_ind_auto_tac (ctxt : Proof.context) thm =
  let val timeout = Prover.max_time_in_proof
                      |> Config.get ctxt
      val _ = thm |> ((Utils.latex_string_of_term ctxt) o (Thm.concl_of))
                  |> (fn str => tracing ("Latex: " ^ str))
  in
    Timeout.apply (Time.fromSeconds timeout) (DEPTH_FIRST theorem_proved' (ind_auto_tac ctxt)) thm
      handle Timeout.TIMEOUT _ => Seq.empty
  end

fun breadth_first_ind_auto_tac (ctxt : Proof.context) thm =
  let val timeout = Prover.max_time_in_proof
                      |> Config.get ctxt
      val _ = thm |> ((Utils.latex_string_of_term ctxt) o (Thm.concl_of))
                  |> (fn str => tracing ("Latex: " ^ str))
  in
    Timeout.apply (Time.fromSeconds timeout) (BREADTH_FIRST theorem_proved' (ind_auto_tac ctxt)) thm
      handle Timeout.TIMEOUT _ => Seq.empty
  end

val method_setup_comp =
  Method.setup (Binding.name "computational_induct")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD ((CHANGED o ALLGOALS) (SUBGOAL (computation_induction_tac ctxt (Proof_Context.theory_of ctxt))))))
    "interleave induction and auto"

val method_setup_struct =
  Method.setup (Binding.name "structural_induct")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD ((CHANGED o ALLGOALS) (SUBGOAL (only_structural_induction_tac ctxt)))))
    "interleave induction and auto"

val method_setup_arbitrary =
  Method.setup (Binding.name "arbitrary_tac")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD ((CHANGED o ALLGOALS) (arbitrary_tac ctxt))))
    "interleave induction and auto"

val method_setup_astar =
  Method.setup (Binding.name "induct_auto_astar")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (astar_ind_auto_tac ctxt)))
    "interleave induction and auto"

val method_setup_best =
  Method.setup (Binding.name "induct_auto_best")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (bfirst_ind_auto_tac ctxt)))
    "interleave induction and auto"

val method_setup_iter_dep =
  Method.setup (Binding.name "induct_auto_iter_dep")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (iter_dep_ind_auto_tac ctxt)))
    "interleave induction and auto"

val method_setup_dep_first =
  Method.setup (Binding.name "induct_auto_dep_first")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (dep_ind_auto_tac ctxt)))
    "interleave induction and auto"

val method_setup_breadth_first =
  Method.setup (Binding.name "induct_auto_breadth_first")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (breadth_first_ind_auto_tac ctxt)))
    "interleave induction and auto"

val _ = Context.>> (Context.map_theory method_setup_comp)
val _ = Context.>> (Context.map_theory method_setup_struct)
val _ = Context.>> (Context.map_theory method_setup_arbitrary)
val _ = Context.>> (Context.map_theory method_setup_astar)
val _ = Context.>> (Context.map_theory method_setup_best)
val _ = Context.>> (Context.map_theory method_setup_iter_dep)
val _ = Context.>> (Context.map_theory method_setup_dep_first)
val _ = Context.>> (Context.map_theory method_setup_breadth_first)

datatype result = Theorem of thm | Failure of term list

(*datatype rtype =
  Equation
  | Rule
  | Conditional
  | Other

datatype conjecture_type =
  Main of term (* Main goal *)
  | Equation of string * term (* An equation *)
  | Rule of string * term (* A rule *)
  | ConditionalEquation of string * term (* A conditional equation *)
  | ConditionalRule of string * term (* A conditional rule *)*)

type conjecture_store =
  {laws : (string * term) Seq.seq,
   tx : (string * term) Seq.seq,
   heuristics : (string * term) list}

fun mk_conjecture_store (schemes, tx, heuristics) : conjecture_store =
  {laws = schemes,
   tx = tx,
   heuristics = heuristics}

fun pull_conjecture thy foo gen {laws, tx, heuristics} =
  case Seq.pull laws of
    SOME (law, laws) => SOME (law, mk_conjecture_store (laws, tx, heuristics))
  | NONE =>
  let fun pull_heuristic conjecture heuristics =
        case gen conjecture of
           conjecture :: gens => 
               (gens @ heuristics)
                    |> Utils.make_term_set_by' thy snd
                    |> Utils.sort_by_general' thy snd
                    |> (fn heuristics => (laws, tx, heuristics))
                    |> mk_conjecture_store
                    |> pair conjecture
                    |> SOME
        | [] => raise ERROR "error"
  in if foo
     then case Seq.pull tx of
           SOME (conjecture, tx) => SOME (conjecture, mk_conjecture_store (laws, tx, heuristics))
           | NONE => (case heuristics of
                       conjecture :: heuristics =>  pull_heuristic conjecture heuristics
                     | [] => NONE)
     else case heuristics of
             conjecture :: heuristics => pull_heuristic conjecture heuristics
           | [] => (case Seq.pull tx of
                       SOME (conjecture, tx) => SOME (conjecture, mk_conjecture_store (laws, tx, heuristics))
                       | NONE => NONE)
  end

fun add_heuristics thy {laws, tx, heuristics} heuristics' =
  heuristics'
    |> Seq.list_of
    |> (fn heuristics' => heuristics @ heuristics')
    |> Utils.make_term_set_by' thy snd
    |> Utils.sort_by_general' thy snd
    |> (fn heuristics => (laws, tx, heuristics))
    |> mk_conjecture_store

(*
  Having a conjecture of the form ?f ?x = ?f ?y, construct the conjecture
  ?x = ?y.
*)
fun arg_cong_equation thy eq =
    if can HOLogic.dest_eq eq
    then let val x = Var (("x", 0), @{typ_pat "?'b"})
             val y = Var (("y", 0), @{typ_pat "?'b"})
             val f = Var (("f", 0), @{typ_pat "?'b \<Rightarrow> ?'a"})
             val pattern = HOLogic.mk_eq (f $ x, f $ y)
         in case try (Pattern.match thy (pattern, eq)) (Vartab.empty, Vartab.empty) of
              SOME (tyenv, tenv) => let val env = Envir.Envir {maxidx = 1, tenv = tenv, tyenv = tyenv}
                                        val lhs = Envir.norm_term env x
                                        val rhs = Envir.norm_term env y
                                    in SOME (HOLogic.mk_eq (lhs, rhs)) end
            | NONE => NONE
             end
    else NONE

fun arg_cong_equation' thy eq =
  if can HOLogic.dest_Trueprop eq
  then case arg_cong_equation thy (HOLogic.dest_Trueprop eq) of
        SOME eq => HOLogic.mk_Trueprop eq
        | NONE => eq
  else eq

(*fun equation_from_subgoals ctxt timeOut failures subsumed =*)
fun equation_from_subgoals ctxt size n table typsub failures subsumed =
  let val thy = Proof_Context.theory_of ctxt
  in
  failures |> maps (Utils.equations thy)
           |> map (Utils.orient_eq thy LESS)
           |> Utils.make_term_set' thy
           |> (fn eqs => eqs @ map_filter (arg_cong_equation thy) eqs)
           |> map HOLogic.mk_Trueprop
           |> filter (fn eq => let val eq' = (HOLogic.mk_Trueprop o Utils.swap_eq o HOLogic.dest_Trueprop) eq
                               in not (subsumed eq orelse subsumed eq') end)
           |> Utils.sort_by_general thy
           |> Seq.of_list
           |> Seq.filter (not o EQ_Terms.counter_example ctxt size n table typsub [])
  end

fun generalized_eq ctxt timeOut size n gn table typsub lemmas subsumed failures subgoals =
  let val thy =  Proof_Context.theory_of ctxt
  in
    subgoals @ failures
      |> Utils.generalizations thy gn
(*      |> (fn eqs => eqs @ map_filter (arg_cong_equation thy) eqs)*)
(*      |> maps (EQ_Terms.generalize thy (table, typsub) gn)*)
      |> Utils.make_term_set' thy
      |> Utils.sort_by_general thy
(*      |> tap (fn _ => tracing "Generalizations")
      |> tap (tracing o Utils.str_of_terms ctxt)
      |> tap (fn _ => tracing "#Generalizations")*)
      |> EQ_Terms.equation ctxt timeOut size n table typsub lemmas subsumed
(*      |> tap (print_some ctxt "generalized_eq: ")*)
  end

fun inductive_prover ctxt tactic timeOut prop =
  let val start = Timing.start ()
      val thy = Proof_Context.theory_of ctxt
(*      val log_file = Context.theory_name thy ^ ".log"
      val path_file = Path.explode log_file
      val _ = if File.exists path_file
              then File.rm path_file
              else ()
      val tracing = Utils.trace_log path_file*)
      val _ = tracing "Getting definitional rewrites..."
      val def_lemmas = Utils.get_definitional_rewrites thy prop
      val _ = tracing "Done"
      val lemmas_ref = Unsynchronized.ref def_lemmas
      val ctxt_nodefs = (Local_Theory.target_of ctxt) delsimps def_lemmas
      val lthy_nodefs = ctxt delsimps def_lemmas
      val _ = tracing "Latex Goal: "
      val _ = tracing (Utils.latex_string_of_term ctxt prop)
      val _ = tracing "Goal: "
      val _ = tracing (Utils.string_of_term ctxt prop)
      val size = Config.get ctxt Random_Terms.max_lambda_size
      val n = Config.get ctxt EQ_Terms.max_random_terms
(*      fun print_some ctxt msj sconj =
        case sconj of
          SOME conj => tracing (msj ^ (Utils.string_of_term' ctxt conj))
        | NONE => ()*)
      val _ = tracing "Preprocessing conjecture..."
      val (table, typsub) =
          DB_EQ_Terms.preprocess_conjecture ctxt size n prop
      val _ = tracing "Done"
(*      val _ = tracing ("Substitutions: " ^string_of_int (length tsubsts))*)
      fun try_prove simps conj =
        let val failures = Unsynchronized.ref (Net.empty : term Net.net)
            val _ = tracing ("Proving: " ^ Utils.string_of_term' ctxt conj)
        in case Prover.prove_from_tactic ctxt_nodefs (SOME simps) (tactic failures) conj timeOut of
          SOME thm => (tracing ("Proved!: " ^ Utils.str_of_terms ctxt [conj]);Theorem thm)
        | NONE => (!failures) |> Net.content
                              |> Failure
        end
      fun orient_scheme eq =
        let val schemes = Utils.get_orientation_schemes ()
            val eq =  HOLogic.dest_Trueprop eq
            val eq' = (HOLogic.mk_eq o swap o HOLogic.dest_eq) eq
        in case get_first (fn scheme => 
              if Pattern.matchess thy ([scheme], [eq])
              then SOME (HOLogic.mk_Trueprop eq)
              else if Pattern.matchess thy ([scheme], [eq'])
                   then SOME (HOLogic.mk_Trueprop eq')
                   else NONE) schemes of
              SOME eq => eq
            | NONE => HOLogic.mk_Trueprop eq
        end
      fun orient eq =
        if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) eq
        then
            let val eq' = HOLogic.dest_Trueprop eq
            in if Utils.definitional_orientation thy eq' andalso
                  not (Utils.bad_equation' thy eq')
               then orient_scheme eq
               else (orient_scheme o HOLogic.mk_Trueprop o HOLogic.mk_eq o swap o HOLogic.dest_eq) eq'
            end
        else eq
      fun add_term_to_net net t =
          t |> Logic.varify_global
            |> Term_Subst.zero_var_indexes
            |> (fn t => Net.insert_term_safe (Pattern.equiv thy) (t, t) net)
      fun add_thm_to_net net thm =
            thm |> Thm.full_prop_of
                |> (fn t => Net.insert_term_safe (Pattern.equiv thy) (t, t) net)
      fun add_thms_to_net net thms =
          Library.foldl (fn (net, thm) => add_thm_to_net net thm) (net, thms)
      fun subsumed_in_net net t =
            t |> Net.match_term net
(*            t |> Net.unify_term net*)
              |> exists (fn t' => Pattern.matches thy (t', t))
(*      fun next_subgoal simps subgoals =
        case subgoals of
          goal :: subgoals => let val _ = tracing ("Normalising: " ^ Utils.string_of_term' ctxt goal)
                                  val goal' = Utils.normalise_term lthy_nodefs simps goal
                                                |> arg_cong_equation' thy
                              in if goal' = @{prop "True"}
                                 then next_subgoal simps subgoals 
                                 else if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) goal'
                                      then SOME (orient goal', subgoals)
                                      else SOME (goal', subgoals)
                              end
        | [] => NONE*)
      fun next_subgoal simps subgoals =
        let val subgoals' = 
          subgoals |> map (arg_cong_equation' thy o Utils.normalise_term lthy_nodefs simps)
                   |> filter (fn conj => conj <> @{prop "True"})
                   |> map (fn conj => if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) conj
                                      then orient conj
                                      else conj)
                   |> Utils.make_term_set' thy
                   |> Utils.sort_by_general thy
        in if null subgoals'
           then NONE
           else case Par_List.get_some (fn conj =>
                        case try_prove simps conj of
                          Theorem _ => SOME (conj, remove (op =) conj subgoals')
                          | _ => NONE) subgoals' of
                   SOME (conj, subgoals) => SOME (conj, subgoals)
                 | NONE => SOME (hd subgoals', tl subgoals')
        end
      fun next_conjecture thy foo gen simps net store =
        case pull_conjecture thy foo gen store of
            SOME ((meth, conjecture), store) =>
              let val _ = tracing ("Normalising (" ^ meth ^ "): " ^ Utils.string_of_term' ctxt conjecture)
                  val conjecture = Utils.normalise_term lthy_nodefs simps conjecture
              in if conjecture = @{prop "True"} orelse
                    subsumed_in_net net conjecture
                 then (tracing "subsumed"; next_conjecture thy foo gen simps net store)
                 else if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) conjecture
                      then let val conjecture' = (HOLogic.mk_Trueprop o Utils.swap_eq o HOLogic.dest_Trueprop) conjecture
                           in if subsumed_in_net net conjecture'
                              then (tracing "subsumed"; next_conjecture thy foo gen simps net store)
                              else SOME (orient conjecture, store)
                           end
                      else SOME (conjecture, store)
              end
          | NONE => NONE
      val terminates = Aprove.memoized_terminates ctxt_nodefs
      fun build_trs lemmas rule =
          if can Utils.dest_object_equation rule
          then let val TRS = map Utils.obj_to_meta lemmas
                   val e = Utils.obj_to_meta rule
               in e |> Ground_Completion.run_completion [] ctxt_nodefs terminates TRS
                    |> map Utils.meta_to_obj end
               (*if Ground_Completion.ac_termination_obj ctxt lemmas rule
               then (lemmas,rule)
               else let val rule' = Utils.commute_obj_eq rule
                    in if Ground_Completion.ac_termination_obj ctxt lemmas rule'
                       then (lemmas,rule')
                       else raise ERROR "Non-terminating rewrite system"
                    end*)
          else raise ERROR "Not equation"
      val lambda_size = Config.get ctxt Random_Terms.max_lambda_size
      val _ = tracing "Calculating equational theory exploration sequence..."
      val eq_tx = DB_EQ_Terms.equational_theory_exploration ctxt_nodefs (table, typsub) size n lambda_size lemmas_ref prop
                  |> Seq.map (pair "EQ_TX")
      val _ = tracing "Done"
      val _ = tracing "Calculating known equational laws sequence..."
      val known_laws = DB_EQ_Terms.known_eq_laws ctxt_nodefs (table, typsub) size n lemmas_ref prop
                  |> Seq.map (pair "EQ_KNOWN")
      val _ = tracing "Done"
      val conj_store = mk_conjecture_store (known_laws, eq_tx, [])
      fun recursive_prover foo store net subgoals lemmas conj =
        case try_prove lemmas conj of
          Theorem thm =>(let val lemmas = build_trs lemmas thm
                             val _ = lemmas_ref := lemmas
                             val net = add_thms_to_net net lemmas
                         in case (tracing "next_subgoal"; next_subgoal lemmas subgoals) of
                          SOME (goal, subgoals) => recursive_prover (not foo) store net subgoals lemmas goal
                        | NONE => SOME (build_trs lemmas thm) end)
        | Failure trms =>
            let val net = add_term_to_net net conj
                val lemmas' = lemmas |> map Thm.full_prop_of
                                     |> map Logic.unvarify_global
                val eq_from_goals =
                       (subsumed_in_net net)
                          |> equation_from_subgoals (lthy_nodefs addsimps lemmas) size n table typsub trms
                          |> Seq.map (pair "eq_from_goals")
                val walsh =
                       (subgoals@lemmas')
                          |> Seq.of_list
                          |> Seq.maps (fn subgoal =>
                                    [subgoal, conj] |> map HOLogic.dest_Trueprop
                                                    |> Divergence.walsh_critic ctxt_nodefs lemmas
                                                    |> Seq.filter (not o EQ_Terms.counter_example lthy_nodefs size n table typsub lemmas))
                          |> Seq.map (pair "Walsh")
                val transverse =
                      (subgoals@lemmas')
                          |> Seq.of_list
                          |> Seq.maps (fn subgoal =>
                                    [subgoal, conj] |> map HOLogic.dest_Trueprop
                                                    |> Divergence.transverse_critic lthy_nodefs lemmas
                                                    |> Seq.map_filter (Prover.prove_schematic_from_method
                                                                      lthy_nodefs (SOME lemmas)
                                                                      (Method.Basic (fn ctxt =>
                                                                        Method.SIMPLE_METHOD
                                                                          (tactic (Unsynchronized.ref Net.empty) ctxt)),
                                                                        (Position.none, Position.none))))
                          |> Seq.map (pair "Transverse")
                val new_store =
                      eq_from_goals
                         |> Seq.append walsh
                         |> Seq.append transverse
                         |> add_heuristics thy store
                fun generalization (meth, conj) =
                      conj |> DB_EQ_Terms.equation' lthy_nodefs (table, typsub) size n lemmas (subsumed_in_net net)
                           |> DB_EQ_Terms.generalize_eq 1 lthy_nodefs size n (table, typsub) lemmas (subsumed_in_net net)
                           |> Utils.sort_by_general thy o map orient
                           |> map (pair meth)
(*                val generalisation =
                       (conj::subgoals @ walsh @ transverse)
                          |> generalized_eq ctxt timeOut size n gn table typsub lemmas (subsumed_in_net net) trms*)
            in case (tracing "next_conjecture"; next_conjecture thy foo generalization lemmas net new_store) of
                SOME (conjecture, store) => recursive_prover (not foo) store (add_term_to_net net conj) (conj :: subgoals) lemmas conjecture
              | NONE => NONE
(*               then NONE
               else conjectures
                      |> map orient
                      |> Utils.sort_by_general thy
                      |> hd
                      |> DB_EQ_Terms.equation' lthy_nodefs (table, typsub) size n lemmas (subsumed_in_net net)
                      |> tap (print_some ctxt "DB_EQ_Terms.equation': " o SOME)
                      |> DB_EQ_Terms.generalize_eq 1 lthy_nodefs size n (table, typsub) lemmas (subsumed_in_net net)
                      |> map orient
                      |> Utils.sort_by_general thy
                      |> hd
                      |> tap (print_some ctxt "DB_EQ_Terms.generalize_eq: " o SOME)
                      |> recursive_prover Seq.empty (add_term_to_net net conj) (conj :: subgoals) lemmas*)
            end
      val result = case recursive_prover true conj_store Net.empty [] def_lemmas prop of
                      SOME thms => (tracing "Latex Simpset: ";
                                    tracing (Utils.latex_str_of_thms thms);
                                    tracing "Simpset: ";
                                    tracing (Utils.str_of_thms thms);
                                    SOME thms)
                    | NONE => (tracing "No simpset!"; NONE)
      val elapsed = start |> Timing.result
                          |> #elapsed
                          |> Time.toReal
      val _ = tracing ("Elapsed time: " ^ string_of_real elapsed)
  in (lthy_nodefs, result) end

(* Failure analysis *)
fun inductive_prover_tactic' ctxt =
  fn (goal, i) =>
    case inductive_prover ctxt ind_auto_failure (Config.get ctxt Prover.max_time_in_proof) goal of
      (ctxt,SOME simps) => (tracing "Proved original goal!"; simp_tac (ctxt addsimps simps) i)
    | (_,NONE) => (tracing "Not proved!"; no_tac)

fun inductive_prover_tactic ctxt =
  SUBGOAL (inductive_prover_tactic' ctxt)

val method_setup_inductive_prover =
  Method.setup (Binding.name "inductive_prover")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (inductive_prover_tactic ctxt 1)))
    "Recursive prover with failure analysis. Interleaves induction and auto and check failures."

val _ = Context.>> (Context.map_theory method_setup_inductive_prover)

end

structure InductiveTacs : INDUCTIVE_TACS = DB_InductiveTacs
