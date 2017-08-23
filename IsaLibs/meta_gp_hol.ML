(*  Title:      util/gp.ML
    ID:         $Id: gp.ML,v 1.00 2015/15/10 12:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Genetic Programming algorithm for Simply-typed lambda calculus.
*)

signature GP =
sig
  val max_time_in_fitness  : int Config.T

  type subst = (typ * typ) list * (term * term) list
  type individual = {ctxt  : Proof.context,
                     genome: term list,
                     subst : subst,
                     norm  : term,
                     fit   : Rat.rat option}

  type gp_statistic = {
      best_individual : individual,
      average_size : real,
      average_error : real,
      equals : int
      }

  datatype gp_result =
    Solved of individual * gp_statistic list
  | Unsolved of gp_statistic list

  val timeout_error : Proof.context -> term -> unit

  val term_count   : (string -> unit) -> Proof.context -> thm -> int -> (int * int) list list
  val well_defined : local_theory -> term -> Proof.context option
  val fnames_of    : Proof.context -> (string * typ) list

  val evolve : bool -> bool -> bool -> string -> thm -> term list -> int -> Rat.rat ->
    Proof.context ->
    (Proof.context -> term list -> Rat.rat) ->
    (individual -> bool) ->
    int -> int -> int -> int -> int -> real -> gp_result

  val latex_solutions : Proof.context -> gp_result list -> string list list
end

structure DB_GP
(* : GP *)
= struct

val (max_time_in_fitness, setup_max_time_in_fitness) = Attrib.config_int @{binding "max_time_in_fitness"} (K 30)

type subst = (typ * typ) list * (term * term) list
type individual = {ctxt  : Proof.context,
                   genome: term list,
                   subst : subst,
                   norm  : term,
                   fit   : Rat.rat option}

type gp_data = { scheme : thm,
                 terminating_closures : thm list,
                 simps_of_closures : thm list list,
                 term_size : int,
                 max_term_size : int,
                 recursive_calls : int,
                 population_size : int,
                 bests : int,
                 mutation_prob : real,
                 fitness : Proof.context -> term list -> Rat.rat,
                 bad_fitness : Rat.rat,
                 finish : individual -> bool,
                 term_count : (int * int) list list,
                 simps : thm list,
                 debug : bool,
                 parallel : bool,
                 empty_simpset : bool,
                 timeout : Time.time,
                 logfile : Path.T,
                 ctxt : Proof.context}

type gp_statistic = {
    best_individual : individual,
    average_size : real,
    average_error : real,
    equals : int
 }

datatype gp_result =
    Solved of individual * gp_statistic list
  | Unsolved of gp_statistic list

exception DONE of individual

fun timeout_error ctxt t =
  tracing ("The induced functions by the term " ^ Syntax.string_of_term ctxt t ^ " are terminating but the fitness function timed out.")

fun mk_individual ctxt trms subst t fit : individual = 
  {ctxt = ctxt,
   genome = trms,
   subst = subst,
   norm = t,
   fit = fit}

fun mk_statistic best_individual average_size average_error equals : gp_statistic =
   {best_individual = best_individual,
    average_size = average_size,
    average_error = average_error,
    equals = equals}

fun calculate_statistic data equals pool =
  let val tracing = Utils.trace_log (#logfile data)
      fun size_of_terms trms = Library.foldl (fn (s, t) => s + size_of_term t) (0, trms)
      val av_size =
            pool |> map (size_of_terms o #genome)
                 |> pair 0
                 |> Library.foldl (op +)
                 |> (fn x => real x / real (#population_size data))
      val av_error =
            pool |> map (the o #fit)
                 |> pair (Rat.of_int 0)
                 |> Library.foldl (op +)
                 |> (fn x => x / Rat.of_int (#population_size data))
      val bst_individual =
            pool |> Metis_Useful.minimum (Rat.ord o apply2 (the o #fit))
                 |> fst
      val _ = tracing ("Average size: " ^ string_of_real av_size)
      val _ = tracing ("Average error: " ^ Rat.string_of_rat av_error ^ " (" ^ (string_of_real o Utils.rat_to_float) av_error ^ ")")
      val _ = tracing ("Best error: " ^ Rat.string_of_rat ((the o #fit) bst_individual))
      val _ = tracing ("Normal Form: " ^ Utils.string_of_term (#ctxt data) (#norm bst_individual))
      val _ = tracing ("Genome: " ^ Utils.str_of_terms (#ctxt data) (#genome bst_individual))
    in mk_statistic bst_individual av_size (Utils.rat_to_float av_error) equals end

(* FIXME: No type mapping *)
fun mk_subst vars trms =
  trms |> map2 (fn v => fn t => (Var v, t)) vars
       |> (fn r => ([], r))

fun prepare (data : gp_data) ((typs, terms) : subst) =
  (map (fn (ty, ty') => (dest_TVar ty, Thm.ctyp_of (#ctxt data) ty')) typs,
   map (fn (t, t') => (dest_Var t, Thm.cterm_of (#ctxt data) t')) terms)
    |> (fn csubst => Drule.instantiate_normalize csubst (#scheme data))
(*    |> tap (tracing o Utils.str_of_thms o single)*)
    |> (fn thm => if (#empty_simpset data)
                  then let val clear_ctxt = (clear_simpset (#ctxt data)) addsimps (#simps data)
                           val timeOut = Config.get clear_ctxt Utils.max_time_normalization
                       in Timeout.apply 
                                  (Time.fromSeconds timeOut)
                                  (simplify clear_ctxt)
                                  thm
                       end
                  else let val ctxt = (#ctxt data) addsimps (#simps data)
                           val timeOut = Config.get ctxt Utils.max_time_normalization
                       in Timeout.apply 
                                  (Time.fromSeconds timeOut)
                                  (simplify ctxt)
                                  thm
                       end)
(*    |> tap (tracing o Utils.str_of_thms o single)*)
    |> snd o Logic.dest_equals o Thm.full_prop_of

fun prepare_closure (data : gp_data) simp ((typs, terms) : subst) =
  (map (fn (ty, ty') => (dest_TVar ty, Thm.ctyp_of (#ctxt data) ty')) typs,
   map (fn (t, t') => (dest_Var t, Thm.cterm_of (#ctxt data) t')) terms)
    |> (fn csubst => Drule.instantiate_normalize csubst simp)
    |> Thm.full_prop_of
    |> HOLogic.dest_Trueprop
    |> HOLogic.dest_eq
    |> strip_comb o fst
    |> apsnd (take (length terms))
    |> list_comb

fun count_rcalls (data : gp_data) f simp ((typs, terms) : subst) =
  (map (fn (ty, ty') => (dest_TVar ty, Thm.ctyp_of (#ctxt data) ty')) typs,
   map (fn (t, t') => (dest_Var t, Thm.cterm_of (#ctxt data) t')) terms)
    |> (fn csubst => Drule.instantiate_normalize csubst simp)
    |> Thm.full_prop_of
    |> HOLogic.dest_Trueprop
    |> HOLogic.dest_eq
    |> snd
    |> (fn t => fold_aterms (fn t => fn c => if t = f
                                             then c + 1
                                             else c) t 0)

fun recursive_calls_ok (data : gp_data) fs ((typs, terms) : subst) =
  let fun get_f t = t |> strip_comb
                      |> fst
      val simps = flat (#simps_of_closures data)
  in fs |> map (fn simp => (get_f simp, simps))
(*        |> tap (map (fn (f, simps) => tracing (Syntax.string_of_term (#ctxt data) f ^ ":" ^  Utils.str_of_thms simps)))*)
        |> forall (fn (f, simps) =>
                      forall (fn simp => count_rcalls data f simp (typs, terms)
                                          <= (#recursive_calls data)) simps)
  end

fun individual_ok (data : gp_data) (individual : individual) =
  (#norm individual)
    |> Utils.binder_elimination Const_Names.hol_exists []
    |> snd
    |> (fn l => length l = length (#terminating_closures data))

val fun_config =
  Function_Common.FunctionConfig { sequential=true, default= NONE (*FIXME dynamic scoping*),
    domintros=false, partials=false}

fun mutual_function lthy (names,eqns) =
    let val naming = map (fn x => ((Binding.qualified_name x), NONE, NoSyn)) names
    in
      Function_Fun.add_fun naming
                           (map (fn t => (((Binding.empty, []), t),[],[])) eqns)
                           fun_config
                           lthy
    end

fun defining_equations scheme =
  let fun feqns t =
        t |> Utils.binder_elimination Const_Names.hol_exists []
          |> fst
          |> Utils.binder_elimination Const_Names.hol_forall []
          |> HOLogic.dest_conj o fst
          |> (fn eqs => case eqs of
                         [x] => [x]
                       | _ => maps feqns eqs)
      val eqns = feqns scheme
      val names = eqns |> map (Term.head_of o fst o HOLogic.dest_eq)
                       |> map (fn Free (n, _) => n
                                | _ => raise ERROR "Ilegal functional scheme!")
                       |> distinct (is_equal o string_ord)
  in (names, map HOLogic.mk_Trueprop eqns) end

fun fname_of ctxt = 
  let val thy = Proof_Context.theory_of ctxt
  in
    (fn (name, typ) => (Context.theory_name thy ^ "." ^ name, typ)) o dest_Free o fst o strip_comb o fst o HOLogic.dest_eq o
    HOLogic.dest_Trueprop o Logic.strip_imp_concl o snd o Function_Lib.dest_all_all
  end

fun fnames_of ctxt =
  case Function_Common.import_last_function ctxt of
    SOME info => (case #simps info of
                    SOME simps => simps |> map Thm.full_prop_of
(*                                        |> tap (map (fn t => tracing (Syntax.string_of_term ctxt t)))*)
                                        |> map (fname_of ctxt)
                                        |> distinct (op =)
                  | NONE => raise ERROR "simps of function not found!")
  | NONE => raise ERROR "Info of function not found!"

fun is_partial elims =
  elims |> flat
        |> map Thm.full_prop_of
        |> exists (Term.exists_Const (fn (name, _) => name = Const_Names.undefined_name))

fun well_defined lthy t =
  (t(*|> tap (tracing o (Syntax.string_of_term lthy))*)
    |> defining_equations
(*    |> tap (fn (_, eqns) => (tracing o string_of_int o length) eqns)*)
    |> try (mutual_function lthy)
    |> (fn res => case res of
                   SOME ctxt => (case Function_Common.import_last_function ctxt of
                                   SOME info => (case #elims info of
                                                   SOME elims =>
                                                   (if is_partial elims
                                                    then NONE
                                                    else SOME ctxt)
                                                 | NONE => NONE)
                                 | NONE => raise ERROR "Info of function not found!")
                | NONE => NONE))
    handle TERM _ => NONE
         | ERROR _ => NONE

fun worst_fitness (data : gp_data) population =
  population |> filter (is_some o #fit)
             |> (fn l => if null l
                         then #bad_fitness data
                         else l |> Metis_Useful.maximum (Rat.ord o apply2 (the o #fit))
                                |> fst
                                |> (the o #fit))

fun initial_population (data : gp_data) =
   let val tracing = Utils.trace_log (#logfile data)
       val parallel = #parallel data
       val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       fun prep_closure trms thm = trms |> mk_subst vars
                                        |> prepare_closure data thm
       fun calls_ok fs trms = trms |> mk_subst vars
                                   |> recursive_calls_ok data fs
       fun new_individual () =
          let val trms = vars |> map2 (fn tc => fn (_, typ) =>
                                        tc |> Utils.weighted_choose
                                           |> Random_Terms.random_lambda_term typ
                                           |> the) (#term_count data)
              val t' = prep trms
          in (trms, t') end
      (* Slow part *)
      fun lookup i ctxt trms =
         let val closures = map (prep_closure trms) (#terminating_closures data)
(*             val _ = tracing "Closures: "
             val _ = map (tracing o (Syntax.string_of_term ctxt)) closures*)
             val rat = if calls_ok closures trms
                       then let (*val time = Date.toString (Date.fromTimeLocal (Time.now ()))
                                val _ = tracing (time ^ " (ok) " ^ Syntax.string_of_term ctxt i)*)
                            in (SOME (Timeout.apply (#timeout data) ((#fitness data) ctxt) closures)
                                  handle Timeout.TIMEOUT _ => (tracing ("Timeout in: " ^ Utils.str_of_terms ctxt trms);
                                                               NONE)
                                        | unknown => (tracing ("Unknown error(genome): " ^ Utils.str_of_terms ctxt trms);
                                                      tracing ("Unknown error(norm): " ^ Utils.string_of_term ctxt i);
                                                      raise unknown)) end
                       else let (*val time = Date.toString (Date.fromTimeLocal (Time.now ()))
                                val _ = tracing (time ^ " (bad) " ^ Syntax.string_of_term ctxt i)*)
                            in NONE end
             val ind = mk_individual ctxt trms
                                     (mk_subst vars trms)
                                     i
                                     rat
         in if (#finish data) ind
            then raise DONE ind
            else ind
         end
       val all = 1 upto (#population_size data)
                    |> (if parallel then Par_List.map else map)
                          (fn _ => new_individual ())
       val global =
          (Term_Tab.empty, all)
            |> Library.foldl (fn (net, (trms, i)) =>
                                Term_Tab.update (i, trms) net)
            |> Term_Tab.dest
            |> (if parallel then Par_List.map else map)
                (fn (i, trms) => (i, lookup i (#ctxt data) trms))
            |> pair Term_Tab.empty
            |> Library.foldl (fn (net, (i, ind)) =>
                                Term_Tab.update (i, ind) net)
       val equal_ind = length all - length (Term_Tab.dest global)
       val population =
          all
          |> map (fn  (trms, i) =>
                  let val ind = the (Term_Tab.lookup global i)
                  in mk_individual (#ctxt data)
                                   trms
                                   (mk_subst vars trms)
                                   i
                                   (#fit ind)
                  end)
      val worst = worst_fitness data population
   in
      population
        |> map (fn ind => case #fit ind of
                            SOME _ => ind
                          | NONE => mk_individual (#ctxt data)
                                                  (#genome ind)
                                                  (#subst ind)
                                                  (#norm ind)
                                                  (SOME worst))
        |> sort ((prod_ord (option_ord Rat.ord) Term_Ord.term_ord) o apply2 (fn ind => (#fit ind, #norm ind)))
        |> pair global
        |> (fn (global, pool) => (calculate_statistic data equal_ind pool, (global, pool)))
   end

(*Substitute new for free occurrences of old in a term*)
fun subst [] = I
  | subst pairs =
      let fun substf i u =
            case AList.lookup (op aconv) pairs u of
                SOME (Bound j) => Bound (i + j)
              | SOME _ => raise ERROR "subst must map frees to bounds"
              | NONE => (case u of Abs(a,T,t) => Abs(a, T, substf (i+1) t)
                                 | t$u' => substf i t $ substf i u'
                                 | _ => u)
      in substf 0 end

fun cross s t =
    let val s = Envir.eta_long [] s
        val t = Envir.eta_long [] t
        val ps = Utils.positions s
        val qs = Utils.positions t
        fun test dom cod =
          forall (fn (_, ty1) => exists (fn (_, ty2) => ty1 = ty2) cod) dom
        fun count (_, _, p) =
          let val qs' = qs |> map (fn (t_q, _, _) =>
                                        let val dom = Term.add_frees t_q []
                                            val cod = Utils.bounds_at_position s p
                                            val sigmas =
                                              dom |> map (fn (_, ty) =>
                                              cod |> filter (fn (_, ty') => ty = ty')
                                                  |> length)
                                        in case sigmas of
                                              [] => 1
                                            | _ :: _ => Library.foldl (op * ) (1, sigmas)
                                        end)
          in Library.foldl (op +) (0, qs') end
          val ps_weighted = ps |> map (fn (t, ty, pos) =>
                                        ((t, ty, pos), count (t, ty, pos)))
                               |> filter (fn (_, i) => i > 0)
        fun select ps_weighted =
          let
              val (s_p, tao, p) = Utils.weighted_choose ps_weighted
              val qs' = qs |> filter (fn (t_q, ty, _) =>
                                        let val dom = Term.add_frees t_q []
                                            val cod = Utils.bounds_at_position s p
                                        in ty = tao andalso
                                           test dom cod
                                        end)
          in if null qs'
             then select (remove (op = o apply2 fst) ((s_p, tao, p), 0) ps_weighted)
             else qs' |> map (fn x => (x, 1))
                      |> Utils.weighted_choose
                      |> pair (s_p, tao, p)
          end
        val ((_, _, p), (t_q, _, q)) = select ps_weighted
        val dom = Term.add_frees t_q []
        val cod = p |> Utils.bounds_at_position s
                    |> rev
                    |> map_index (fn (i, x) => (x, Bound i))
        val sigma = map (fn (s, ty) => cod |> filter (fn ((_, ty'), _) => ty = ty')
                                           |> map (fn x => (x, 1))
                                           |> Utils.weighted_choose
(*                                           |> tap (fn (x, _) => tracing (s ^ "\<longrightarrow>" ^ Syntax.string_of_term @{context} (Free x)))*)
                                           |> snd
                                           |> pair (Free (s, ty))) dom
    in (Utils.substitute (subst sigma t_q, p) s, p, q) end

fun print_pos pos =
  pos |> map string_of_int
      |> space_implode ", "
      |> enclose "[" "]"

fun crossover s t =
  let val (r, _, _) = cross s t
(*  let val (r, p1, p2) = cross s t
      val _ = tracing (print_pos p1)
      val _ = tracing (print_pos p2)*)
  in Envir.beta_eta_contract r end

fun Crossover (data : gp_data) ss tt =
  let val (i, (s, t)) =
                   ss |> map2 pair tt
                      |> map_index (fn x => x)
                      |> map (fn (i, (s, t)) => ((i, (s, t)), size_of_term s + size_of_term t))
                      |> Utils.weighted_choose
       val prefix = take i ss
       val suffix = drop (i + 1) ss
       fun retry i =
          if i > 50
          then s
          else let val c = crossover s t
               in if size_of_term c > #max_term_size data
                  then retry (i + 1)
                  else c
               end
       val nn = prefix @ [retry 0] @ suffix
  in nn
  end

fun small s =
    let val t = s
        val s = Envir.eta_long [] s
        val t = Envir.eta_long [] t
        val ps = Utils.positions s
        val qs = Utils.positions t
        fun test dom cod =
          forall (fn (_, ty1) => exists (fn (_, ty2) => ty1 = ty2) cod) dom
        fun count (_, _, p) =
          let val qs' = qs |> map (fn (t_q, _, q) =>
                                        let val dom = Term.add_frees t_q []
                                            val cod = Utils.bounds_at_position s p
                                            val sigmas =
                                              if is_prefix (op =) p q
                                              then SOME (dom |> map (fn (_, ty) =>
                                                            cod |> filter (fn (_, ty') => ty = ty')
                                                                |> length))
                                              else NONE
                                        in case sigmas of
                                              NONE => 0
                                            | SOME [] => 1
                                            | SOME sigmas => Library.foldl (op * ) (1, sigmas)
                                        end)
          in Library.foldl (op +) (0, qs') end
          val ps_weighted = ps |> map (fn (t, ty, pos) =>
                                        ((t, ty, pos), count (t, ty, pos)))
                               |> filter (fn (_, i) => i > 0)
        fun select ps_weighted =
          let
              val (s_p, tao, p) = Utils.weighted_choose ps_weighted
              val qs' = qs |> filter (fn (t_q, ty, q) =>
                                        let val dom = Term.add_frees t_q []
                                            val cod = Utils.bounds_at_position s p
                                        in ty = tao andalso
                                           test dom cod andalso
                                           is_prefix (op =) p q
                                        end)
          in if null qs'
             then select (remove (op = o apply2 fst) ((s_p, tao, p), 0) ps_weighted)
             else qs' |> map (fn x => (x, 1))
                      |> Utils.weighted_choose
                      |> pair (s_p, tao, p)
          end
        val ((_, _, p), (t_q, _, _)) = select ps_weighted
        val dom = Term.add_frees t_q []
        val cod = p |> Utils.bounds_at_position s
                    |> rev
                    |> map_index (fn (i, x) => (x, Bound i))
        val sigma = map (fn (s, ty) => cod |> filter (fn ((_, ty'), _) => ty = ty')
                                           |> map (fn x => (x, 1))
                                           |> Utils.weighted_choose
(*                                           |> tap (fn (x, _) => tracing (s ^ "\<longrightarrow>" ^ Syntax.string_of_term @{context} (Free x)))*)
                                           |> snd
                                           |> pair (Free (s, ty))) dom
(*    in (Utils.substitute (subst_atomic sigma t_q, p) s, p, q) end*)
    in s |> Utils.substitute (subst sigma t_q, p)
         |> Envir.beta_eta_contract end
(*         |> tap (fn s' => if size_of_term s' < size_of_term s
                          then tracing "smaller"
                          else tracing "equal") end*)

fun Small (data : gp_data) ss =
  let  val tt = ss
       val (i, (s, _)) =
                   ss |> map2 pair tt
                      |> map_index (fn x => x)
                      |> map (fn (i, (s, t)) => ((i, (s, t)), size_of_term s + size_of_term t))
                      |> Utils.weighted_choose
       val prefix = take i ss
       val suffix = drop (i + 1) ss
       val c = small s
       val nn = prefix @ [c] @ suffix
  in nn
  end

fun mutation (data : gp_data) t =
  let val t = Envir.eta_long [] t
      val (_, ty, q) =
              t |> Utils.positions
                |> map (rpair 1)
                |> Utils.weighted_choose
      fun s_fun () =
        let val bounds = q |> Utils.bounds_at_position t
                           |> rev
                           |> map_index (fn (i, x) => (x, Bound i))
            val target_typ = bounds |> map (snd o fst)
                              |> (fn typs => typs ---> ty)
            val term_count = 1 upto (#term_size data)
                          |> map (fn i => (i, Random_Terms.count_lambda_terms target_typ i))
                          |> filter (fn (_, c) => c > 0)
(*                          |> tap (map (fn (i, c) => tracing (string_of_int i ^ " : " ^ string_of_int c)))*)
            val s = term_count |> Utils.weighted_choose
                               |> Random_Terms.random_lambda_term target_typ
                               |> the
                               |> rpair (map snd bounds)
                               |> Envir.beta_eta_contract o list_comb
        in s end
      val s = case Random_Terms.random_datatype (#ctxt data) 5 ty of
                SOME s => if Utils.random () < 0.5
                          then (Utils.trace_log (#logfile data) (Syntax.string_of_term (#ctxt data) s); s)
                          else s_fun ()
              | NONE => s_fun ()
  in Utils.substitute (s, q) t end

fun Mutation (data : gp_data) ss =
  if Utils.random () <= (#mutation_prob data)
  then
  let val (i, s) = ss |> map_index (fn x => x)
                      |> map (fn (i, s) => ((i, s), size_of_term s))
                      |> Utils.weighted_choose
       val prefix = take i ss
       val suffix = drop (i + 1) ss
(*       val c = mutation data s*)
       fun retry i =
          if i > 50
          then s
          else let val c = mutation data s
               in if size_of_term c > #max_term_size data
                  then retry (i + 1)
                  else c
               end
       val nn = prefix @ [retry 0] @ suffix
  in nn
  end
  else ss

fun print_pool (pool : individual list) =
  pool |> map (fn ind => 
          tracing (Syntax.string_of_term (#ctxt ind) (#norm ind) ^ " : " ^ (string_of_real o Utils.rat_to_float) ((the o #fit) ind)))

fun print_pool' ctxt (pool : (individual * int) list) =
  pool |> map (fn (ind, i) => 
          (tracing (Syntax.string_of_term ctxt (#norm ind));
           tracing (string_of_int i)))
(*          tracing (Syntax.string_of_term ctxt t ^ " : " ^ string_of_int i))*)

fun next_generation (data : gp_data)
                    (global : individual Term_Tab.table, pool : individual list) =
  let (*val _ = print_pool pool*)
      val tracing = Utils.trace_log (#logfile data)
      val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
      fun prep trms = trms |> mk_subst vars
                           |> prepare data
      fun prep_closure trms thm = trms |> mk_subst vars
                                       |> prepare_closure data thm
      fun calls_ok fs trms = trms |> mk_subst vars
                                  |> recursive_calls_ok data fs
      val pool' = pool |> filter (individual_ok data)
                       |> map (fn {ctxt, genome,
                           subst, norm,
                           fit} => fit |> (Rat.inv o the)
                                       |> SOME
                                       |> mk_individual ctxt genome subst norm)
      val lcm = Library.foldl (fn (lcm, ind) =>
              ind |> (the o #fit)
                  |> (snd o Rat.dest)
                  |> Integer.lcm lcm) (1, pool')
                  |> rpair 1
                  |> Rat.make
      val pool' = pool' |> map (fn {ctxt, genome,
                                    subst, norm,
                                    fit} => lcm * (the fit)
                                              |> SOME
                                              |> mk_individual ctxt genome subst norm)
                        |> map (fn ind => (ind, (fst o Rat.dest o the) (#fit ind)))
      val minv = pool' |> Utils.minby int_ord snd
                       |> snd
      val  pool' = map (fn (t, i) => (t, i div minv)) pool'
      val _ = if (#debug data)
              then print_pool' (#ctxt data) pool' 
                     |> (fn _ => ())
              else ()
      fun new_ind () =
          let val i1 = pool' |> Utils.weighted_choose
                             |> #genome
              val i2 = pool' |> Utils.weighted_choose
                             |> #genome
          in i2 |> Crossover data i1
                |> Mutation data end
      fun new_small () =
          let val i = pool' |> Utils.weighted_choose
                            |> #genome
          in Small data i end
      (* Slow part *)
      fun lookup (ctxt, trms) =
        let val i' = prep trms
        in
        case Term_Tab.lookup global i' of
            SOME ind => mk_individual ctxt trms (mk_subst vars trms)
                                      i' (#fit ind)
          | NONE   => let val closures = map (prep_closure trms) (#terminating_closures data)
(*                          val rat = (#fitness data) ctxt closures*)
                          val rat = if calls_ok closures trms
                                    then let (*val time = Date.toString (Date.fromTimeLocal (Time.now ()))
                                             val _ = tracing (time ^ " (ok) " ^ Syntax.string_of_term ctxt i')*)
                                         in (Timeout.apply (#timeout data) ((#fitness data) ctxt) closures
                                           handle Timeout.TIMEOUT _ => (tracing ("Timeout in: " ^ Utils.str_of_terms ctxt trms);
                                                                        (#bad_fitness data))
                                                | unknown => (tracing ("Unknown error(genome): " ^ Utils.str_of_terms ctxt trms);
                                                              tracing ("Unknown error(norm): " ^ Utils.string_of_term ctxt i');
                                                              raise unknown))
                                              |> SOME end
(*                                         in (#fitness data) ctxt closures end*)
                                    else let (*val time = Date.toString (Date.fromTimeLocal (Time.now ()))
                                             val _ = tracing (time ^ " (bad) " ^ Syntax.string_of_term ctxt i')*)
                                         in NONE end
                          val ind = mk_individual ctxt trms
                                                  (mk_subst vars trms)
                                                  i' rat
                      in if (#finish data) ind
                         then raise DONE ind
                         else ind
                      end
        end
      val parallel = #parallel data
      (* new mode *)
      val rest =
        1 upto (#population_size data) - (#bests data) - (#bests data)
          |> (if parallel then Par_List.map else map)
                (fn _ => let val trms = new_ind ()
                         in (prep trms, trms) end)
      val smaller =
        1 upto (#bests data)
          |> (if parallel then Par_List.map else map)
                (fn _ => let val trms = new_small ()
                         in (prep trms, trms) end)
      val not_evaluated_ref = Unsynchronized.ref 0
      val rest_map =
        (Term_Tab.empty, smaller @ rest)
          |> Library.foldl (fn (net, (i, trms)) =>
            Term_Tab.update (i, trms) net)
          |> Term_Tab.dest
          |> (fn uniques => let val (evaluated, not_evaluated) = List.partition (Term_Tab.defined global o fst) uniques
                                val _ = not_evaluated_ref := length not_evaluated
                                val mmap = if parallel then Par_List.map else map
                                val f = (fn (i, trms) => (i, lookup ((#ctxt data), trms)))
                            in mmap f evaluated @ mmap f not_evaluated end)
          |> pair global
          |>  Library.foldl (fn (net, (i, ind)) =>
            Term_Tab.update (i, ind) net)
      val equal_ind = length (smaller @ rest) - !not_evaluated_ref
      val rest_ind =
        smaller @ rest
          |> map (fn (i, trms) =>
                  let val ind = the (Term_Tab.lookup rest_map i)
                  in mk_individual (#ctxt data)
                                   trms
                                   (mk_subst vars trms)
                                   i (#fit ind) end)
      val bests = take (#bests data) pool
      val population = bests @ rest_ind
      val worst = worst_fitness data population
   in population
        |> map (fn ind => case #fit ind of
                            SOME _ => ind
                          | NONE => mk_individual (#ctxt data)
                                                  (#genome ind)
                                                  (#subst ind)
                                                  (#norm ind)
                                                  (SOME worst))
        |> sort ((prod_ord (option_ord Rat.ord) Term_Ord.term_ord) o apply2 (fn ind => (#fit ind, #norm ind)))
        |> pair global
        |> (fn (global, pool) => (calculate_statistic data equal_ind pool, (global, pool))) end

fun term_count tracing ctxt scheme term_size =
  let val vars = scheme
                   |> Thm.full_prop_of
                   |> (fn t => Term.add_vars t [])
  in vars |> 
       map (fn (_, typ) => 
         1 upto term_size
           |> tap (fn _ => tracing ("Precalculating the inhabitants of type: " ^
                                    Utils.string_of_typ ctxt typ))
           |> Par_List.map (fn i => (i, Random_Terms.count_lambda_terms typ i))
           |> filter (fn (_, c) => c > 0)
           |> tap (map (fn (i, c) => tracing (string_of_int i ^ " : " ^ string_of_int c))))
  end

fun evolve parallel dbg empty_simpset log scheme terminating_closures recursive_calls bad_fitness ctxt fitness finish term_size max_term_size population_size generations bests mut_prob =
 (let val path = Path.explode log
      val tracing = Utils.trace_log path
      val _ = Utils.create_log path
      val _ = tracing "Building initial population..."
      val term_count = term_count tracing ctxt scheme term_size
      val thy = Proof_Context.theory_of ctxt
      val simps_of_closures = map (fn Const (n, _) => Utils.get_rewrites thy n
                                  | _ => raise ERROR "Not ") terminating_closures
      val data : gp_data =
               { scheme = scheme,
                 simps_of_closures = simps_of_closures,
                 terminating_closures = map hd simps_of_closures,
                 term_size = term_size,
                 max_term_size = max_term_size,
                 recursive_calls = recursive_calls,
                 bad_fitness = bad_fitness,
                 population_size = population_size,
                 bests = bests,
                 mutation_prob = mut_prob,
                 fitness = fitness,
                 finish = finish,
                 term_count = term_count,
                 ctxt = ctxt,
                 debug = dbg,
                 parallel = parallel,
                 empty_simpset = empty_simpset,
                 logfile = path,
                 timeout = max_time_in_fitness |> Config.get ctxt
                                               |> Time.fromSeconds,
                 simps = scheme |> Thm.full_prop_of
                                |> global_simps ctxt
                                |> Utils.make_theorem_set
                                |> tap (fn _ => tracing "Simplification rules: ")
                                |> tap (tracing o Utils.str_of_thms)}
      fun loop i statistics global_pool =
        let val _ = tracing ("Generation: " ^ string_of_int i)
        in if i <= generations
           then (let val (statistic, next) = next_generation data global_pool
                 in loop (i+1) (statistic :: statistics) next end)
                 handle DONE ind => let val _ = tracing ("Solution: " ^ Utils.string_of_term (#ctxt ind) (#norm ind))
                                    in Solved (ind, rev statistics) end
           else Unsolved (rev statistics)
        end
  in data |> initial_population
          |> (fn (statistic, global_pool) => loop 1 [statistic] global_pool) end)
  handle DONE ind => let val _ = tracing ("Solution: " ^ Utils.string_of_term (#ctxt ind) (#norm ind))
                     in Solved (ind, []) end

fun different_solutions results =
  results |> map_filter (fn r => case r of
                              Solved (s, _) => SOME (#norm s, (snd o #subst) s)
                             | _ => NONE)
          |> (fn entries => fold Term_Tab.update entries Term_Tab.empty)
          |> Term_Tab.dest

fun latex_solutions ctxt results =
  let val results = different_solutions results
      val to_latex = Utils.latex_string_of_term ctxt
      fun to_latexs substs =
          substs |> map (fn (v, lam) => to_latex v ^ " \\mapsto " ^
                                        to_latex lam)
                           |> commas
                           |> enclose "$" "$"
  in results |> map_index (fn (i, (norm, subst)) => 
                            [string_of_int i, to_latex norm, to_latexs subst]) end

end

structure GP : GP = DB_GP

