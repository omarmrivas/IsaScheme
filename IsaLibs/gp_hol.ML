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
                     fit   : Rat.rat}

  type gp_statistic = {
      best_individual : individual,
      average_size : real,
      average_error : real,
      non_terminating : int,
      equals : int
      }

  datatype gp_result =
    Solved of individual * gp_statistic list * (int * int) option
  | Unsolved of gp_statistic list * (int * int) option

  val timeout_error : Proof.context -> term -> unit

  val term_count   : Proof.context -> thm -> int -> (int * int) list list
  val well_defined : local_theory -> term -> Proof.context option
  val fnames_of    : Proof.context -> (string * typ) list

  val evolve : bool -> bool -> thm ->
    Proof.context ->
    (Proof.context -> (string * typ) list -> Rat.rat) ->
    (individual -> bool) ->
    int -> int -> int -> int -> real -> gp_result

end

structure DB_GP
(* : GP *)
= struct

val (max_time_in_fitness, setup_max_time_in_fitness) = Attrib.config_int @{binding "max_time_in_fitness"} (K 30)

val big_rational = Rat.rat_of_int 1000000

type subst = (typ * typ) list * (term * term) list
  type individual = {ctxt  : Proof.context,
                     genome: term list,
                     subst : subst,
                     norm  : term,
                     fit   : Rat.rat}

type gp_data = { scheme : thm,
                 term_size : int,
                 population_size : int,
                 bests : int,
                 mutation_prob : real,
                 fitness : Proof.context -> (string * typ) list -> Rat.rat,
                 finish : individual -> bool,
                 term_count : (int * int) list list,
                 simps : thm list,
                 debug : bool,
                 parallel : bool,
                 timeout : Time.time,
                 ctxt : Proof.context}

type gp_statistic = {
    best_individual : individual,
    average_size : real,
    average_error : real,
    non_terminating : int,
    equals : int
 }

datatype gp_result =
    Solved of individual * gp_statistic list * (int * int) option
  | Unsolved of gp_statistic list * (int * int) option

exception DONE of individual

fun timeout_error ctxt t =
  tracing ("The induced functions by the term " ^ Syntax.string_of_term ctxt t ^ " are terminating but the fitness function timed out.")

fun mk_individual ctxt trms subst t fit : individual = 
  {ctxt = ctxt,
   genome = trms,
   subst = subst,
   norm = t,
   fit = fit}

fun mk_statistic best_individual average_size average_error non_terminating equals : gp_statistic =
   {best_individual = best_individual,
    average_size = average_size,
    average_error = average_error,
    non_terminating = non_terminating,
    equals = equals}

(*fun normalise ctxt simps t =
  if can HOLogic.dest_Trueprop t
  then Proof_Tools.normalise_conjecture ctxt simps t
  else let val typ = type_of t
           val prop = Logic.mk_equals (t, Free ("x", typ))
       in prop |> Proof_Tools.normalise_conjecture ctxt simps
               |> Logic.dest_equals
               |> fst
       end

fun prepare ctxt simps function_set lam =
  lam |> rpair function_set
      |> Envir.beta_eta_contract o list_comb
      |> normalise ctxt simps*)

(* FIXME: No type mapping *)
fun mk_subst vars trms =
  trms |> map2 (fn v => fn t => (Var v, t)) vars
       |> (fn r => ([], r))

fun prepare (data : gp_data) ((typs, terms) : subst) =
  (map (apply2 (Thm.ctyp_of (#ctxt data))) typs,
   map (apply2 (Thm.cterm_of (#ctxt data))) terms)
    |> (fn csubst => Drule.instantiate_normalize csubst (#scheme data))
(*    |> tap (tracing o Utils.str_of_thms o single)*)
    |> Proof_Tools.normalise_thm (#ctxt data) (#simps data)
(*    |> tap (tracing o Utils.str_of_thms o single)*)
    |> snd o Logic.dest_equals o Thm.full_prop_of

val fun_config =
  Function_Common.FunctionConfig { sequential=true, default= NONE (*FIXME dynamic scoping*),
    domintros=false, partials=false}

fun mutual_function lthy (names,eqns) =
    let val naming = map (fn x => ((Binding.qualified_name x), NONE, NoSyn)) names
    in
      Function_Fun.add_fun naming
                           (map (fn t => ((Binding.empty, []), t)) eqns)
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

fun initial_population' (data : gp_data) =
   let val parallel = #parallel data
       val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       fun new_individual i (set, unique, repeated) =
          let val trms = vars |> map2 (fn tc => fn (_, typ) =>
                                        tc |> Utils.weighted_choose
                                           |> Random_Terms.random_term typ
                                           |> the) (#term_count data)
              val t' = prep trms
          in if i < (#population_size data)
             then (if Term_Tab.defined set t'
                   then new_individual (i+1) (set, unique, repeated)
                   else let val wd = well_defined (#ctxt data) t'
                        in case wd of
                            SOME ctxt => let val _ = if (#debug data)
                                                     then tracing (".."^ string_of_int i)
                                                     else ()
                                         in (Term_Tab.update (t', wd) set, (ctxt, trms) :: unique, repeated) end
                          | NONE => new_individual (i+1) (Term_Tab.update (t', wd) set, unique, repeated)
                        end)
             else (if Term_Tab.defined set t'
                   then let val wd = the (Term_Tab.lookup set t')
                        in case wd of
                            SOME ctxt => (set, unique, (ctxt, trms) :: repeated)
                          | NONE =>  new_individual (i+1) (set, unique, repeated)
                        end
                   else let val wd = well_defined (#ctxt data) t'
                        in case wd of
                            SOME ctxt => (Term_Tab.update (t', wd) set, (ctxt, trms) :: unique, repeated)
                          | NONE => new_individual (i+1) (Term_Tab.update (t', wd) set, unique, repeated)
                        end)
          end
       fun new_individual' ((set, unique, repeated), _) =
         if parallel
         then
          1 upto Multithreading.max_threads_value ()
            |> Par_List.get_some (fn _ => SOME (new_individual 0 (set, unique, repeated)))
            |> the
         else new_individual 0 (set, unique, repeated)
   in 1 upto (#population_size data)
        |> pair (Term_Tab.empty, [], [])
        |> Library.foldl new_individual'
        |> (fn (set, unique, repeated) =>
                let val uniques = 
                      unique |> (if parallel then Par_List.map else map)
                                  (fn (ctxt, trms) =>
                                        let val rat = (TimeLimit.timeLimit
                                                        (#timeout data)
                                                        ((#fitness data) ctxt) (fnames_of ctxt))
                                                        handle TimeLimit.TimeOut => (if #debug data
                                                                                     then timeout_error ctxt (prep trms)
                                                                                     else ();
                                                                                     big_rational)
                                            val ind = mk_individual ctxt
                                                                    trms
                                                                    (mk_subst vars trms)
                                                                    (prep trms)
                                                                    rat
                                        in if (#finish data) ind
                                           then raise DONE ind
                                           else ind
                                        end)
                    val tab = Library.foldl (fn (tab, ind) =>
                                                  Term_Tab.update (#norm ind, #fit ind) tab)
                                            (Term_Tab.empty, uniques)
                in (set, uniques @ map (fn (ctxt, trms) =>
                                          let val rat = trms |> prep
                                                             |> Term_Tab.lookup tab
                                                             |> the
                                          in mk_individual ctxt
                                                           trms
                                                           (mk_subst vars trms)
                                                           (prep trms)
                                                           (rat)
                                          end) repeated)
                end)
        |> (fn (set, L) => 
              (Term_Tab.empty, L) 
                |> Library.foldl (fn (g, ind) => Term_Tab.update (#norm ind, SOME ind) g)
                |> rpair (Term_Tab.keys set)
                |> Library.foldl (fn (g, t) => case Term_Tab.lookup set t of
                                                   SOME (SOME _) => g
                                                 | NONE => g
                                                 | SOME NONE => Term_Tab.update (t, NONE) g)
                |> rpair L)
        |> apsnd (sort ((prod_ord Rat.ord Term_Ord.term_ord) o apply2 (fn ind => (#fit ind, #norm ind))))
(*        |> apsnd (sort ((prod_ord Rat.ord int_ord) o apply2 (fn ind => (#fit ind, #norm ind))))*)
   end

fun initial_population (data : gp_data) =
   let val parallel = #parallel data
       val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       fun new_individual set =
          let val trms = vars |> map2 (fn tc => fn (_, typ) =>
                                        tc |> Utils.weighted_choose
                                           |> Random_Terms.random_term typ
                                           |> the) (#term_count data)
              val t' = prep trms
              val wd = well_defined (#ctxt data) t'
          in case wd of
             SOME ctxt => let val _ = if #debug data
                                      then ()(*tracing (Syntax.string_of_term ctxt t')*)
                                      else ()
                          in (set, ctxt, trms, t') end
           | NONE => let val _ = if #debug data
                                      then ()(*tracing ("bad: " ^ Syntax.string_of_term (#ctxt data) t')*)
                                      else ()
                     in new_individual (Term_Tab.update (t', NONE) set) end
          end
      (* Slow part *)
      fun lookup i ctxt trms =
         let val rat = (TimeLimit.timeLimit (#timeout data)
                                            ((#fitness data) ctxt) (fnames_of ctxt))
                       handle TimeLimit.TimeOut => (if #debug data
                                                    then timeout_error ctxt (prep trms)
                                                    else ();
                                                    big_rational)
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
                          (fn _ => new_individual Term_Tab.empty)
       val all_map =
          (Term_Tab.empty, all)
            |> Library.foldl (fn (net, (set, ctxt, trms, i)) =>
                                Term_Tab.update (i, (set, ctxt, trms)) net)
            |> Term_Tab.dest
            |> (if parallel then Par_List.map else map)
                (fn (i, (tab, ctxt, trms)) => (i, tab, lookup i ctxt trms))
            |> pair Term_Tab.empty
            |> Library.foldl (fn (net, (i, tab, ind)) =>
                                Term_Tab.update (i, (tab, ind)) net)
       val equal_ind = length all - length (Term_Tab.dest all_map)
       val population =
          all
          |> map (fn  (_, ctxt, trms, i) =>
                  let val (_, ind) = the (Term_Tab.lookup all_map i)
                  in mk_individual ctxt
                                   trms
                                   (mk_subst vars trms)
                                   i
                                   (#fit ind)
                  end)
       val global =
            (Term_Tab.empty, Term_Tab.dest all_map)
              |> Library.foldl (fn (g, (i, (_, ind))) =>
                        Term_Tab.update (i, SOME ind) g)
       val (non_terminating, global) =
            ((0,global), all)
               |>  Library.foldl (fn ((i,g), (tab, _, _, _)) =>
                      tab |> Term_Tab.keys
                          |> pair (i,g)
                          |> Library.foldl (fn ((i,g), t) =>
                              (i+1,Term_Tab.update (t, NONE) g)))
   in
      population
        |> sort ((prod_ord Rat.ord Term_Ord.term_ord) o apply2 (fn ind => (#fit ind, #norm ind)))
        |> pair global
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
(*    in (Utils.substitute (subst_atomic sigma t_q, p) s, p, q) end*)
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

fun Crossover (global : individual option Term_Tab.table) (data : gp_data) tab ss tt =
  let val (i, (s, t)) =
                   ss |> map2 pair tt
                      |> map_index (fn x => x)
                      |> map (fn (i, (s, t)) => ((i, (s, t)), size_of_term s + size_of_term t))
                      |> Utils.weighted_choose
       val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       val prefix = take i ss
       val suffix = drop (i + 1) ss
       fun f tab = let val c = crossover s t
                      val nn = prefix @ [c] @ suffix
                      val t' = prep nn
                   in case Term_Tab.lookup global t' of
                        SOME (SOME ind) => (tab, #ctxt ind, nn)
                      | SOME NONE => f tab
                      | NONE => (case Term_Tab.lookup tab t' of
                                      SOME _ => f tab
                                    | NONE => (case well_defined (#ctxt data) t' of
                                                SOME ctxt => (tab, ctxt, nn)
                                              | NONE => f (Term_Tab.update (t', ()) tab)))
                  end
  in f tab
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

fun Small (global : individual option Term_Tab.table) (data : gp_data) tab ss =
  let  val tt = ss
       val (i, (s, _)) =
                   ss |> map2 pair tt
                      |> map_index (fn x => x)
                      |> map (fn (i, (s, t)) => ((i, (s, t)), size_of_term s + size_of_term t))
                      |> Utils.weighted_choose
       val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       val prefix = take i ss
       val suffix = drop (i + 1) ss
       fun f tab = let val c = small s
                      val nn = prefix @ [c] @ suffix
                      val t' = prep nn
                   in case Term_Tab.lookup global t' of
                        SOME (SOME ind) => (tab, #ctxt ind, nn)
                      | SOME NONE => f tab
                      | NONE => (case Term_Tab.lookup tab t' of
                                      SOME _ => f tab
                                    | NONE => (case well_defined (#ctxt data) t' of
                                                SOME ctxt => (tab, ctxt, nn)
                                              | NONE => f (Term_Tab.update (t', ()) tab)))
                  end
  in f tab
  end

(*
fun mutation prob t =
  if Random.random () <= prob
  then crossover t t
  else t*)

fun mutation (data : gp_data) t =
  let val t = Envir.eta_long [] t
      val (_, ty, q) =
              t |> Utils.positions
                |> map (rpair 1)
                |> Utils.weighted_choose
      val bounds = q |> Utils.bounds_at_position t
                     |> rev
                     |> map_index (fn (i, x) => (x, Bound i))
      val target_typ = bounds |> map (snd o fst)
                              |> (fn typs => typs ---> ty)
      val term_count = 1 upto (#term_size data)
                          |> map (fn i => (i, Random_Terms.count_terms target_typ i))
                          |> filter (fn (_, c) => c > 0)
(*                          |> tap (map (fn (i, c) => tracing (string_of_int i ^ " : " ^ string_of_int c)))*)
      val s = term_count |> Utils.weighted_choose
                         |> Random_Terms.random_term target_typ
                         |> the
                         |> rpair (map snd bounds)
                         |> Envir.beta_eta_contract o list_comb
  in Utils.substitute (s, q) t end

fun Mutation (global : individual option Term_Tab.table)
             (data : gp_data) (tab, ctxt, ss) =
  if Random.random () <= (#mutation_prob data)
  then
  let val (i, s) = ss |> map_index (fn x => x)
                      |> map (fn (i, s) => ((i, s), size_of_term s))
                      |> Utils.weighted_choose
       val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       val prefix = take i ss
       val suffix = drop (i + 1) ss
       fun f tab = let val c = mutation data s
                       val nn = prefix @ [c] @ suffix
                       val t' = prep nn
                   in case Term_Tab.lookup global t' of
                        SOME (SOME ind) => (tab, #ctxt ind, nn)
                      | SOME NONE => f tab
                      | NONE => (case Term_Tab.lookup tab t' of
                                      SOME _ => f tab
                                    | NONE => (case well_defined (#ctxt data) t' of
                                                SOME ctxt => (tab, ctxt, nn)
                                              | NONE => f (Term_Tab.update (t', ()) tab)))
                  end
  in f tab
  end
  else (tab, ctxt, ss)

fun print_pool (pool : individual list) =
  pool |> map (fn ind => 
          tracing (Syntax.string_of_term (#ctxt ind) (#norm ind) ^ " : " ^ (string_of_real o Utils.rat_to_float) (#fit ind)))

fun print_pool' ctxt (pool : (individual * int) list) =
  pool |> map (fn (ind, i) => 
          (tracing (Syntax.string_of_term ctxt (#norm ind));
           tracing (string_of_int i)))
(*          tracing (Syntax.string_of_term ctxt t ^ " : " ^ string_of_int i))*)

fun next_generation (data : gp_data)
                    (global : individual option Term_Tab.table, pool : individual list) =
  let (*val _ = print_pool pool*)
      val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
      fun prep trms = trms |> mk_subst vars
                           |> prepare data
      fun size_of_terms trms = Library.foldl (fn (s, t) => s + size_of_term t) (0, trms)
      val av_size =
            pool |> map (size_of_terms o #genome)
                 |> pair 0
                 |> Library.foldl (op +)
                 |> (fn x => real x / real (#population_size data))
      val av_error =
            pool |> map #fit
                 |> pair Rat.zero
                 |> Library.foldl (op +/)
                 |> (fn x => x // Rat.rat_of_int (#population_size data))
      val bst_individual =
            pool |> Metis_Useful.minimum (Rat.ord o apply2 #fit)
                 |> fst
      val _ = tracing ("Average size: " ^ string_of_real av_size)
      val _ = tracing ("Average error: " ^ Rat.string_of_rat av_error ^ " (" ^ (string_of_real o Utils.rat_to_float) av_error ^ ")")
      val _ = tracing ("Best error: " ^ Rat.string_of_rat (#fit bst_individual))
(*      val _ = tracing ("Best Individual: " ^ Syntax.string_of_term (#ctxt data) (#norm bst_individual))*)
      val _ = tracing ("Normal Form: " ^ Syntax.string_of_term (#ctxt data) (#norm bst_individual))
      val pool' = map (fn {ctxt, genome,
                           subst, norm,
                           fit} => fit |> Rat.inv
                                       |> mk_individual ctxt genome subst norm) pool
      val lcm = Library.foldl (fn (lcm, ind) =>
              ind |> #fit
                  |> (snd o Rat.quotient_of_rat)
                  |> Integer.lcm lcm) (1, pool')
                  |> rpair 1
                  |> Rat.rat_of_quotient
      val pool' = pool' |> map (fn {ctxt, genome,
                                    subst, norm,
                                    fit} => lcm */ fit
                                              |> mk_individual ctxt genome subst norm)
                        |> map (fn ind => (ind, (fst o Rat.quotient_of_rat) (#fit ind)))
      val minv = pool' |> Utils.minby int_ord snd
                       |> snd
      val  pool' = map (fn (t, i) => (t, i div minv)) pool'
      val _ = if (#debug data)
              then print_pool' (#ctxt data) pool' 
                     |> (fn _ => ())
              else ()
      fun new_ind global =
          let val i1 = pool' |> Utils.weighted_choose
                             |> #genome
              val i2 = pool' |> Utils.weighted_choose
                             |> #genome
          in i2 |> Crossover global data Term_Tab.empty i1
                |> Mutation global data end
      fun new_small global =
          let val i = pool' |> Utils.weighted_choose
                            |> #genome
          in Small global data Term_Tab.empty i end
      (* Slow part *)
      fun lookup (ctxt, trms) =
        let val i' = prep trms
        in
        case Term_Tab.lookup global i' of
            SOME (SOME ind) => mk_individual ctxt trms (mk_subst vars trms) 
                                             i' (#fit ind)
          | SOME NONE => raise ERROR "Ilegal individual!"
          | NONE   => let val rat = (TimeLimit.timeLimit
                                                        (#timeout data)
                                                        ((#fitness data) ctxt) (fnames_of ctxt))
                                                        handle TimeLimit.TimeOut => (if #debug data
                                                                                     then timeout_error ctxt (prep trms)
                                                                                     else ();
                                                                                     big_rational)
                          val ind = mk_individual ctxt
                                                  trms
                                                  (mk_subst vars trms)
                                                  i'
                                                  rat
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
                (fn _ => let val (tab, ctxt, trms) = new_ind global
                         in (tab, ctxt,  prep trms, trms) end)
      val smaller =
        1 upto (#bests data)
          |> (if parallel then Par_List.map else map)
                (fn _ => let val (tab, ctxt, trms) = new_small global
                         in (tab, ctxt, prep trms, trms) end)
      val rest_map =
        (Term_Tab.empty, smaller @ rest)
          |> Library.foldl (fn (net, (tab, ctxt, i, trms)) =>
            Term_Tab.update (i, (tab, ctxt, trms)) net)
          |> Term_Tab.dest
          |> (if parallel then Par_List.map else map)
              (fn (i, (tab, ctxt, trms)) => (i, tab, lookup (ctxt, trms)))
          |> pair Term_Tab.empty
          |>  Library.foldl (fn (net, (i, tab, ind)) =>
            Term_Tab.update (i, (tab, ind)) net)
      val global =
            (global, Term_Tab.dest rest_map)
              |> Library.foldl (fn (g, (i, (_, ind))) =>
                        Term_Tab.update (i, SOME ind) g)
      val equal_ind = length (smaller @ rest) - length (Term_Tab.dest rest_map)
      val rest_ind =
        smaller @ rest
          |> map (fn (tab, ctxt, i, trms) =>
                  let val (_, ind) = the (Term_Tab.lookup rest_map i)
                  in (tab, mk_individual ctxt
                                         trms
                                         (mk_subst vars trms)
                                         i
                                         (#fit ind))
                                         end)
      val bests = take (#bests data) pool
      val (non_terminating, global) =
            ((0,global), rest @ smaller)
               |>  Library.foldl (fn ((i,g), (tab, _, _, _)) => 
                      tab |> Term_Tab.keys
                          |> pair (i,g)
                          |> Library.foldl (fn ((i,g), t) => 
                              (i+1,Term_Tab.update (t, NONE) g)))
  in bests @ map snd rest_ind
      |> sort ((prod_ord Rat.ord Term_Ord.term_ord) o apply2 (fn ind => (#fit ind, #norm ind)))
      |> pair global
      |> pair (mk_statistic bst_individual av_size (Utils.rat_to_float av_error)
                            non_terminating equal_ind) end
      (* new mode *)
(*      val rest =
        1 upto (#population_size data) - (#bests data) - (#bests data)
          |> (if parallel then Par_List.map else map)
                (fn _ => let val (tab, ctxt, trms) = new_ind global
             in (tab, lookup (ctxt, trms)) end)
      val smaller =
        1 upto (#bests data)
          |> (if parallel then Par_List.map else map)
                (fn _ => let val (tab, ctxt, trms) = new_small global
             in (tab, lookup (ctxt, trms)) end)
      val bests = take (#bests data) pool
      val global = 
            (global, rest)
               |>  Library.foldl (fn (g, (tab, _)) => tab |> Term_Tab.keys
                                                          |> pair g
                                                          |> Library.foldl (fn (g, t) => 
                                                              Term_Tab.update (t, NONE) g))
               |> rpair smaller
               |>  Library.foldl (fn (g, (tab, _)) => tab |> Term_Tab.keys
                                                          |> pair g
                                                          |> Library.foldl (fn (g, t) => 
                                                              Term_Tab.update (t, NONE) g))
  in bests @ map snd smaller @ map snd rest
      |> sort ((prod_ord Rat.ord Term_Ord.term_ord) o apply2 (fn ind => (#fit ind, #norm ind)))
      |> pair global end*)

fun next_generation_uniques (data : gp_data)
                    (global : individual option Term_Tab.table, pool : individual list) =
  let (*val _ = print_pool pool*)
      val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
      fun prep trms = trms |> mk_subst vars
                           |> prepare data
      fun size_of_terms trms = Library.foldl (fn (s, t) => s + size_of_term t) (0, trms)
      val av_size =
            pool |> map (size_of_terms o #genome)
                 |> pair 0
                 |> Library.foldl (op +)
                 |> (fn x => real x / real (#population_size data))
      val av_error =
            pool |> map #fit
                 |> pair Rat.zero
                 |> Library.foldl (op +/)
                 |> (fn x => x // Rat.rat_of_int (#population_size data))
      val bst_individual =
            pool |> Metis_Useful.minimum (Rat.ord o apply2 #fit)
                 |> fst
      val _ = tracing ("Average size: " ^ string_of_real av_size)
      val _ = tracing ("Average error: " ^ Rat.string_of_rat av_error ^ " (" ^ (string_of_real o Utils.rat_to_float) av_error ^ ")")
      val _ = tracing ("Best error: " ^ Rat.string_of_rat (#fit bst_individual))
(*      val _ = tracing ("Best Individual: " ^ Syntax.string_of_term (#ctxt data) (#norm bst_individual))*)
      val _ = tracing ("Normal Form: " ^ Syntax.string_of_term (#ctxt data) (#norm bst_individual))
      val pool' = map (fn {ctxt, genome,
                           subst, norm,
                           fit} => fit |> Rat.inv
                                       |> mk_individual ctxt genome subst norm) pool
      val lcm = Library.foldl (fn (lcm, ind) =>
              ind |> #fit
                  |> (snd o Rat.quotient_of_rat)
                  |> Integer.lcm lcm) (1, pool')
                  |> rpair 1
                  |> Rat.rat_of_quotient
      val pool' = pool' |> map (fn {ctxt, genome,
                                    subst, norm,
                                    fit} => lcm */ fit
                                              |> mk_individual ctxt genome subst norm)
                        |> map (fn ind => (ind, (fst o Rat.quotient_of_rat) (#fit ind)))
      val minv = pool' |> Utils.minby int_ord snd
                       |> snd
      val  pool' = map (fn (t, i) => (t, i div minv)) pool'
      val _ = if (#debug data)
              then print_pool' (#ctxt data) pool' 
                     |> (fn _ => ())
              else ()
      fun new_ind global tab =
          let val i1 = pool' |> Utils.weighted_choose
                             |> #genome
              val i2 = pool' |> Utils.weighted_choose
                             |> #genome
          in i2 |> Crossover global data tab i1
                |> Mutation global data end
      fun new_ind' global tab i =
        let val (set, ctxt, trms) = new_ind global tab
        in
          if i < #population_size data
          then if Term_Tab.defined global (prep trms)
               then new_ind' global set (i + 1)
               else (set, ctxt, trms)
          else (set, ctxt, trms)
        end
      fun new_individual global =
          1 upto Multithreading.max_threads_value ()
            |> Par_List.get_some (fn _ => SOME (new_ind' global Term_Tab.empty 0))
            |> the
      (* Slow part *)
      fun lookup (ctxt, trms) =
        let val i' = prep trms
        in
        case Term_Tab.lookup global i' of
            SOME (SOME ind) => mk_individual ctxt trms (mk_subst vars trms) 
                                             i' (#fit ind)
          | SOME NONE => raise ERROR "Ilegal individual!"
          | NONE   => let val rat = (TimeLimit.timeLimit
                                                        (#timeout data)
                                                        ((#fitness data) ctxt) (fnames_of ctxt))
                                                        handle TimeLimit.TimeOut => (if #debug data
                                                                                     then timeout_error ctxt (prep trms)
                                                                                     else ();
                                                                                     big_rational)
                          val ind = mk_individual ctxt
                                                  trms
                                                  (mk_subst vars trms)
                                                  i'
                                                  rat
                        in if (#finish data) ind
                           then raise DONE ind
                           else ind
                        end
        end
      val (global', rest) =
        1 upto (#population_size data) - (#bests data)
          |> pair (Term_Tab.empty, [])
          |> Library.foldl (fn ((global, pool), _) => 
                let val (tab, ctxt, trms) = new_individual global
                    val global =  tab |> Term_Tab.keys
                                      |> pair global
                                      |> Library.foldl (fn (g, t) =>
                                            Term_Tab.update (t, NONE) g)
                in (global, lookup (ctxt, trms) :: pool) end)
      val global = Term_Tab.keys global'
                     |> pair global
                     |> Library.foldl (fn (g, t) => Term_Tab.update (t, the (Term_Tab.lookup global' t)) g)
      val bests = take (#bests data) pool
  in bests @ rest
(*      |> sort (Rat.ord o apply2 #fit)*)
      |> sort ((prod_ord Rat.ord Term_Ord.term_ord) o apply2 (fn ind => (#fit ind, #norm ind)))
      |> pair global end

fun term_count ctxt scheme term_size =
  let val vars = scheme
                   |> Thm.full_prop_of
                   |> (fn t => Term.add_vars t [])
  in vars |> 
       map (fn (_, typ) => 
         1 upto term_size
           |> tap (fn _ => tracing ("Precalculating the inhabitants of type: " ^
                                    Syntax.string_of_typ ctxt typ))
           |> Par_List.map (fn i => (i, Random_Terms.count_terms typ i))
           |> filter (fn (_, c) => c > 0)
           |> tap (map (fn (i, c) => tracing (string_of_int i ^ " : " ^ string_of_int c))))
  end

fun non_terminating m =
  let fun count (_, NONE) (n,d) = (n + 1, d + 1)
        | count (_, SOME _) (n,d) = (n, d + 1)
  in
    Term_Tab.fold count m (0, 0)
  end

fun evolve parallel dbg scheme ctxt fitness finish term_size population_size generations bests mut_prob =
 (let val _ = tracing "Building initial population..."
      val term_count = term_count ctxt scheme term_size
      val data : gp_data =
               { scheme = scheme,
                 term_size = term_size,
                 population_size = population_size,
                 bests = bests,
                 mutation_prob = mut_prob,
                 fitness = fitness,
                 finish = finish,
                 term_count = term_count,
                 ctxt = ctxt,
                 debug = dbg,
                 parallel = parallel,
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
                 handle DONE ind => let val _ = tracing ("Solution: " ^ Syntax.string_of_term (#ctxt ind) (#norm ind))
                                        val (nt, all) = non_terminating (fst global_pool)
                                        val _ = tracing ("(" ^ string_of_int nt ^ "," ^ string_of_int all ^ ")")
                                    in Solved (ind, rev statistics, SOME (nt, all)) end
           else let val (nt, all) = non_terminating (fst global_pool)
                    val _ = tracing ("(" ^ string_of_int nt ^ "," ^ string_of_int all ^ ")")
                in Unsolved (rev statistics, SOME (nt, all)) end
        end
  in data |> initial_population
          |> loop 1 [] end)
  handle DONE ind => let val _ = tracing ("Solution: " ^ Syntax.string_of_term (#ctxt ind) (#norm ind))
                     in Solved (ind, [], NONE) end

end

structure GP : GP = DB_GP

