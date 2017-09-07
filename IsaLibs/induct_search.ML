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
  (* Utilery tactics *)

  val INTERLEAVE  : ('a -> 'b Seq.seq) * ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq
  val INTERLEAVE' : ('a -> 'b -> 'c Seq.seq) * ('a -> 'b -> 'c Seq.seq) -> 'a -> 'b -> 'c Seq.seq
  val astar_ind_auto_tac : Proof.context -> tactic
  val iter_dep_ind_auto_tac : Proof.context -> tactic
  val ind_auto_failure : term Net.net Unsynchronized.ref -> thm list Unsynchronized.ref 
                                      -> Proof.context -> tactic
  val ind_auto_sledgehammer_failure : term Net.net Unsynchronized.ref -> thm list Unsynchronized.ref 
                                      -> Proof.context -> tactic
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

fun inductive_applications' thy prop =
  let
    fun inductive_apps thy prop =
      let
        val (t,args) = Term.strip_comb prop
      in
        case t of
           Const _ =>
           (t |> (fst o Term.dest_Const)
              |> (fn name => name ^ ".induct")
              |> (fn name => (args, Global_Theory.get_thm thy name))
              |> (fn (args, rule) => if exists (exists_subterm is_Bound) args
                                     then maps (inductive_apps thy) args
                                     else (args, rule) :: maps (inductive_apps thy) args)
              handle ERROR _ => maps (inductive_apps thy) args
                    | TERM _ => maps (inductive_apps thy) args)
         | Abs (n, T, _) => betapply (t, Free (n, T))
                              |> inductive_apps thy
                              |> (fn res => res @ maps (inductive_apps thy) args)
         | _ =>  maps (inductive_apps thy) args
      end
    val transform = map (fn arg => SOME (NONE, (arg, false)))
  in
    prop |> inductive_apps thy
         (* Applications with smaller arguments are considered first *)
         |> sort (fn args =>
                    args |> apply2 fst
                         |> apply2 (map Term.size_of_term)
                         |> apply2 (fn l => Library.foldl (op +) (0, l))
                         |> int_ord)
         |> map (fn (y, z) => (transform y, z))
  end

fun computation_induction_tac' ctxt thy (goal, i) =
    case inductive_applications' thy goal of
          (args, induction) :: _ => 
            DETERM (Induction.induction_tac ctxt true [args] [] [] (SOME [induction]) [] i)
         | [] => no_tac

fun structural_induction_tac' ctxt (goal, i) =
  let val frees = Term.add_frees goal []
                    |> map_filter (fn (s, T) =>
                              let val ind_rules = Induct.find_inductT ctxt T
                              in if null ind_rules
                                 then NONE
                                 else SOME ((s, T), ind_rules) end)
  in case frees of
      ((s,T), induction) :: _ => 
          DETERM (Induction.induction_tac ctxt true [[SOME (NONE, (Free (s,T), false))]] [] [] (SOME induction) [] i)
       | [] => no_tac
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
                                             val vs = map fst l
(*                                             val vss = Utils.subsets vs*)
                                             val vs_rules = map_product pair vs rules
                                         in vs_rules end)
  in
    (no_tac, var_sets)
      |> Library.foldl (fn (thms,((v,ty),th)) =>
           let val _ = ()(*tracing ("Structural on: " ^ v)*)
           in (*(fn thh => DETERM (Induct_Tacs.induct_tac ctxt [[SOME v]] (SOME [th]) i) thh
                            handle ERROR err => (tracing (err ^ " : " ^ Syntax.string_of_term ctxt goal);
                                               tracing "Frees: ";
                                               map (tracing o (Syntax.string_of_term ctxt) o Free) frees;
                                               tracing "Fixes: ";
                                               map (tracing o (Syntax.string_of_term ctxt) o Free) fixes;
                                               raise ERROR err)) APPEND*)
(*  val induction_tac: Proof.context -> bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> tactic *)
              (fn thh => DETERM (Induction.induction_tac ctxt true [[SOME (NONE, (Free (v, ty), false))]] [] [] NONE [] i) thh
                            handle ERROR err => (tracing (err ^ " : " ^ Syntax.string_of_term ctxt goal);
                                               tracing "Frees: ";
                                               map (tracing o (Syntax.string_of_term ctxt) o Free) frees;
                                               tracing "Fixes: ";
                                               map (tracing o (Syntax.string_of_term ctxt) o Free) fixes;
                                               raise ERROR err))
              APPEND thms end)
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

fun primitive_induction_sledgehammer ctxt lemmas (goal, i) =
  let val thy = Proof_Context.theory_of ctxt
      val frees = frees_in_concl goal
      val vars = vars_in_concl goal
      val fixes = subtract (op =) frees vars
      val tac' = (structural_induction_tac ctxt frees fixes (goal, i) APPEND
                  computation_induction_tac ctxt thy (goal, i) APPEND
                  split_tactic ctxt thy vars (goal, i))
      val tac = 
          (Sledgehammer_Tactics.sledgehammer_with_metis_tac
                  ctxt []
                  Sledgehammer_Fact.no_fact_override (!lemmas) i) ORELSE
          (tac' THEN (TRY (auto_clasimpset_tac ctxt i)))
  in tac(*tac ORELSE tac'*)
  end

fun primitive_induction' ctxt (goal, i) =
  let val apps = inductive_applications' (Proof_Context.theory_of ctxt) goal
      val _ = if null apps
              then tracing ("structural induction on: " ^ Syntax.string_of_term ctxt goal)
              else tracing ("computation induction on: " ^ Syntax.string_of_term ctxt goal)
  in if null apps
     then structural_induction_tac' ctxt (goal, i)
     else computation_induction_tac' ctxt (Proof_Context.theory_of ctxt) (goal, i) end

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

fun ind_auto_failure sts lemmas ctxt =
    SOLVE ((CHANGED o ALLGOALS)
       ((SUBGOAL (primitive_induction ctxt)) THEN'
        (TRY' (SUBGOAL(check_fail_proof_state sts ctxt)))))

fun ind_auto_sledgehammer_failure sts lemmas ctxt =
    SOLVE ((CHANGED o ALLGOALS)
       ((SUBGOAL (primitive_induction_sledgehammer ctxt lemmas)) THEN'
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

end

structure InductiveTacs : INDUCTIVE_TACS = DB_InductiveTacs
