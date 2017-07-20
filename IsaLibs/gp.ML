(*  Title:      util/gp.ML
    ID:         $Id: gp.ML,v 1.00 2015/15/10 12:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Genetic Programming algorithm for Simply-typed lambda calculus.
*)

signature GP =
sig
  type individual = term * Rat.rat

  val evolve : term list ->
    typ ->
    Proof.context ->
    (term -> Rat.rat) ->
    (term * Rat.rat -> bool) ->
    int -> int -> int -> int -> real -> (individual * term) option
end

structure DB_GP
(* : GP *)
= struct

type individual = term * Rat.rat

type gp_data = { function_set : term list,
                 term_size : int,
                 population_size : int,
                 bests : int,
                 target_typ : typ,
                 mutation_prob : real,
                 fitness : term -> Rat.rat,
                 finish : (term * Rat.rat) -> bool,
                 term_count : (int * int) list,
                 simps : thm list,
                 ctxt : Proof.context}

exception DONE of individual * term

fun normalise ctxt simps t =
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
      |> normalise ctxt simps

fun initial_population {function_set,
                 population_size,
                 target_typ,
                 fitness,
                 finish,
                 term_count, ctxt, simps, ...} =
   let val typ = map type_of function_set ---> target_typ
       val prep = prepare ctxt simps function_set
       fun new_individual i (set, set', list) =
          let val t = term_count |> Utils.weighted_choose
                                 |> Random_Terms.random_term typ
                                 |> the
(*                                 |> rpair function_set
                                 |> Envir.beta_eta_contract o list_comb
                                 |> normalise ctxt simps*)
              val t' = prep t
          in if i < population_size
             then (if Term_Tab.defined set t'
                   then new_individual (i+1) (set, set', list)
                   else (Term_Tab.update (t', ()) set, t :: set', list))
             else (set, set', t :: list)
          end
       fun new_individual' ((set, set', list), _) =
          1 upto Multithreading.max_threads_value ()
            |> Par_List.get_some (fn _ => SOME (new_individual 0 (set, set', list)))
            |> the
   in 1 upto population_size
        |> pair (Term_Tab.empty, [], [])
        |> Library.foldl new_individual'
(*        |> Library.foldl (fn ((set, list), _) => new_individual 0 (set, list))*)
        |> (fn (_, set', list) => let val uniques =
(*                                        Term_Tab.keys set*)
                                          set'
                                          |> Par_List.map (fn t => let val t' = prep t
                                                                       val rat = fitness t'
                                                        in if finish (t, rat)
                                                           then raise DONE ((t, rat), t')
                                                           else (t, rat)
                                                        end)
                                  val tab = Library.foldl (fn (tab, (t, rat)) =>
                                                          t |> prep
                                                            |> (fn t => Term_Tab.update (t, rat) tab))
                                                          (Term_Tab.empty, uniques)
                              in uniques @ map (fn t => (t, t |> prep
                                                              |> Term_Tab.lookup tab
                                                              |> the)) list end)
        |> sort (Rat.ord o apply2 snd)
   end

(*fun cross s t =
    let val s = Envir.eta_long [] s
        val t = Envir.eta_long [] t
        val ps = Utils.positions s
        val qs = Utils.positions t
        fun test dom cod =
          forall (fn (_, ty1) => exists (fn (_, ty2) => ty1 = ty2) cod) dom
        fun update (tab, (_, ty, _)) =
            case Type_Tab.lookup tab ty of
              SOME i => Type_Tab.update (ty, i+1) tab
            | NONE   => Type_Tab.update (ty, 1) tab
        val qs_hash = Library.foldl update (Type_Tab.empty, qs)
        fun select ps =
          let val ps_weighted = ps |> map (fn (t, ty, pos) =>
                                      case Type_Tab.lookup qs_hash ty of
                                        SOME i => ((t, ty, pos), i)
                                      | NONE => ((t, ty, pos), 0))
              val (s_p, tao, p) = Utils.weighted_choose ps_weighted
              val qs' = qs |> filter (fn (t_q, ty, _) =>
                                        let val dom = Term.add_frees t_q []
                                            val cod = Utils.bounds_at_position s p
                                        in ty = tao andalso
                                           test dom cod
                                        end)
          in if null qs'
             then select (remove (op =) (s_p, tao, p) ps)
             else qs' |> map (fn x => (x, 1))
                      |> Utils.weighted_choose
                      |> pair (s_p, tao, p)
          end
        val ((_, _, p), (t_q, _, q)) = select ps
        val dom = Term.add_frees t_q []
        val cod = p |> Utils.bounds_at_position s
                    |> rev
                    |> map_index (fn (i, x) => (x, Bound i))
        val sigma = map (fn (s, ty) => cod |> filter (fn ((_, ty'), _) => ty = ty')
                                           |> map (fn x => (x, 1))
                                           |> Utils.weighted_choose
                                           |> snd
                                           |> pair (Free (s, ty))) dom
    in (Utils.substitute (subst_atomic sigma t_q, p) s, p, q) end*)

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

fun cross' s t =
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
                                            | _ :: _ => Library.foldl (op *) (1, sigmas)
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
                                           |> tap (fn (x, _) => tracing (s ^ "\<longrightarrow>" ^ Syntax.string_of_term @{context} (Free x)))
                                           |> snd
                                           |> pair (Free (s, ty))) dom
(*    in (Utils.substitute (subst_atomic sigma t_q, p) s, p, q) end*)
    in (Utils.substitute (subst sigma t_q, p) s, p, q) end

fun print_pos pos =
  pos |> map string_of_int
      |> space_implode ", "
      |> enclose "[" "]"

fun crossover s t =
(*  let val (r, _, _) = cross' s t*)
  let val (r, p1, p2) = cross' s t
      val _ = tracing (print_pos p1)
      val _ = tracing (print_pos p2)
  in Envir.beta_eta_contract r end

fun mutation prob t =
  if Random.random () <= prob
  then crossover t t
  else t

fun mutation' ({term_size, ...} : gp_data) t =
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
      val term_count = 1 upto term_size
                          |> Par_List.map (fn i => (i, Random_Terms.count_terms target_typ i))
                          |> filter (fn (_, c) => c > 0)
(*                          |> tap (map (fn (i, c) => tracing (string_of_int i ^ " : " ^ string_of_int c)))*)
      val s = term_count |> Utils.weighted_choose
                         |> Random_Terms.random_term target_typ
                         |> the
                         |> rpair (map snd bounds)
                         |> Envir.beta_eta_contract o list_comb
  in Utils.substitute (s, q) t end

val rat_to_float = op / o apply2 real o Rat.quotient_of_rat

fun print_pool ctxt pool =
  pool |> map (fn (t, rat) => 
          tracing (Syntax.string_of_term ctxt t ^ " : " ^ (string_of_real o rat_to_float) rat))

fun print_pool' ctxt pool =
  pool |> map (fn (t, i) => 
          (tracing (Syntax.string_of_term ctxt t);
           tracing (string_of_int i)))
(*          tracing (Syntax.string_of_term ctxt t ^ " : " ^ string_of_int i))*)

fun next_generation (gp_data as {
                 bests,
                 population_size,
                 function_set,
                 fitness,
                 finish, ctxt, simps, ...} : gp_data)
                 tab (pool : individual list) =
  let (*val _ = print_pool ctxt pool*)
      val prep = prepare ctxt simps function_set
      val av_size =
            pool |> map (size_of_term  o fst)
                 |> pair 0
                 |> Library.foldl (op +)
                 |> (fn x => real x / real population_size)
      val av_error =
            pool |> map snd
                 |> pair Rat.zero
                 |> Library.foldl (op +/)
                 |> (fn x => x // Rat.rat_of_int population_size)
      val (bst_individual, bst_error) =
            pool |> Metis_Useful.minimum (Rat.ord o apply2 snd)
                 |> fst
      val _ = tracing ("Average size: " ^ string_of_real av_size)
      val _ = tracing ("Average error: " ^ Rat.string_of_rat av_error ^ " (" ^ (string_of_real o rat_to_float) av_error ^ ")")
      val _ = tracing ("Best error: " ^ Rat.string_of_rat bst_error)
      val _ = tracing ("Best Individual: " ^ Syntax.string_of_term ctxt bst_individual)
      val _ = tracing ("Normal Form: " ^ Syntax.string_of_term ctxt (prep bst_individual))
      val pool' = map (apsnd Rat.inv) pool
      val lcm = Library.foldl (fn (lcm, (_, r)) =>
                r |> (snd o Rat.quotient_of_rat)
                  |> Integer.lcm lcm) (1, pool')
                  |> rpair 1
                  |> Rat.rat_of_quotient
      val pool' = pool' |> map (fn (t, r) => (t, lcm */ r))
                        |> map (apsnd (fst o Rat.quotient_of_rat))
      val minv = pool' |> Utils.minby int_ord snd
                       |> snd
      val  pool' = map (fn (t, i) => (t, i div minv)) pool'
(*      val _ = print_pool' ctxt pool'*)
      fun new_individual i (set, set', list) =
          let val i1 = Utils.weighted_choose pool'
              val i2 = Utils.weighted_choose pool'
(*              val _ = tracing ("i1: " ^ Syntax.string_of_term ctxt i1)
              val _ = tracing ("i2: " ^ Syntax.string_of_term ctxt i2)*)
              val t = i2 |> crossover i1
                         |> mutation' gp_data
(*                         |> mutation (#mutation_prob gp_data)*)
                         |> Envir.beta_eta_contract
(*                         |> normalise ctxt simps*)
              val t' = prep t
          in if i < population_size
             then (if Term_Tab.defined set t'
                   then new_individual (i+1) (set, set', list)
                   else (Term_Tab.update (t', ()) set, t :: set', list))
             else (set, set', t :: list)
          end
      fun new_individual' ((set, set', list), _) =
          1 upto Multithreading.max_threads_value ()
(*          1 upto 1*)
            |> Par_List.get_some (fn _ => SOME (new_individual 0 (set, set', list)))
            |> the
      (* Slow part *)
      fun lookup i =
        let val i' = prep i
        in
        case Term_Tab.lookup tab i' of
            SOME rat => (i, rat)
            | NONE   => let val rat = fitness i'
                        in if finish (i, rat)
                           then raise DONE ((i, rat), i')
                           else (i, rat)
                        end
        end
      fun lookup' i =
          let fun msg () =
              "Individual: " ^ Syntax.string_of_term ctxt i ^ "\n" ^
              "Normalized: " ^ Syntax.string_of_term ctxt (prep i)
              fun check time = Time.toReal (#elapsed time) > 2.0
          in Utils.timing_wrapper' check msg lookup i end
      val rest =
        1 upto population_size - bests
        |> pair (Term_Tab.empty, [], [])
        |> Library.foldl new_individual'
        |> (fn (_, set', list) => let val uniques =
(*                                        Term_Tab.keys set*)
                                          set'
                                          |> sort Term_Ord.term_ord
                                          (* Slow part *)
                                          |> Par_List.map lookup'
                                          (* Slow part *)
                                  val tab = Library.foldl (fn (tab, (t, rat)) =>
                                                          t |> prep
                                                            |> (fn t => Term_Tab.update (t, rat) tab))
                                                          (Term_Tab.empty, uniques)
                              in uniques @ map (fn t => (t, t |> prep
                                                              |> Term_Tab.lookup tab
                                                              |> the)) list end)
(*      val rest = 1 upto population_size - bests
                  |> Par_List.map (fn _ =>
                      let val i1 = Utils.weighted_choose pool'
                          val i2 = Utils.weighted_choose pool'
                          val i = i2 |> crossover i1
                                     |> mutation' gp_data
                                     |> normalise ctxt simps
                      in case Term_Tab.lookup tab i of
                            SOME rat => (i, rat)
                            | NONE   => let val rat = fitness i
                                        in if finish (i, rat)
                                           then raise DONE (i, rat)
                                           else (i, rat) end
                      end)*)
      val bests = take bests pool
  in bests @ rest
      |> sort (Rat.ord o apply2 snd) end

fun evolve function_set target_typ ctxt fitness finish term_size population_size generations bests mut_prob =
  (let val tab = Term_Tab.empty
      val _ = tracing "Building initial population..."
      val typ = map type_of function_set ---> target_typ
      val term_count = 1 upto term_size
                          |> Par_List.map (fn i => (i, Random_Terms.count_terms typ i))
                          |> filter (fn (_, c) => c > 0)
                          |> tap (map (fn (i, c) => tracing (string_of_int i ^ " : " ^ string_of_int c)))
      val gp_data : gp_data =
               { function_set = function_set,
                 term_size = term_size,
                 population_size = population_size,
                 bests = bests,
                 target_typ = target_typ,
                 mutation_prob = mut_prob,
                 fitness = fitness,
                 finish = finish,
                 term_count = term_count,
                 ctxt = ctxt,
                 simps = function_set |> map (global_simps ctxt)
                                      |> flat
                                      |> Utils.make_theorem_set
                                      |> tap (fn _ => tracing "Simplification rules: ")
                                      |> tap (tracing o Utils.str_of_thms)}
      val prep = prepare ctxt (#simps gp_data) function_set
      val pool = initial_population gp_data
      fun loop i pool =
        let val _ = tracing ("Generation: " ^ string_of_int i)
            val tab = Library.foldl (fn (tab, (t, rat)) => Term_Tab.update (prep t, rat) tab) (tab, pool)
        in if i < generations
           then loop (i+1) (next_generation gp_data tab pool)
           else NONE
        end
  in loop 1 pool end)
  handle DONE ((i, rat), i') => SOME ((i, rat), i')

end

structure GP : GP = DB_GP

