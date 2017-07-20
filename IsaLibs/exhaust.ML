(*  Title:      util/gp.ML
    ID:         $Id: gp.ML,v 1.00 2015/15/10 12:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Genetic Programming algorithm for Simply-typed lambda calculus.
*)

signature EXHAUST =
sig

end

structure DB_EXHAUST
(* : GP *)
= struct

type subst = (typ * typ) list * (term * term) list

datatype result =
    Solution of Proof.context * term * term list
  | Table of unit Term_Tab.table

fun mk_subst vars trms =
  trms |> map2 (fn v => fn t => (Var v, t)) vars
       |> (fn r => ([], r))

fun prepare ctxt scheme simps ((typs, terms) : subst) =
  (map (fn (ty, ty') => (dest_TVar ty, Thm.ctyp_of ctxt ty')) typs,
   map (fn (t, t') => (dest_Var t, Thm.cterm_of ctxt t')) terms)
    |> (fn csubst => Drule.instantiate_normalize csubst scheme)
    |> Proof_Tools.normalise_thm ctxt simps
    |> snd o Logic.dest_equals o Thm.full_prop_of

val block_size = 1000

fun calculate_search_space scheme term_size =
  let val ctxt = scheme |> Thm.theory_of_thm
                        |> Context.Theory
                        |> Context.proof_of
      val term_count = GP.term_count tracing ctxt scheme term_size
      fun states f =
        case f () of
          SOME v => v :: states f
        | NONE => []
      fun sum l = Library.foldl (op +) (0, l)
      fun mul l = Library.foldl (op *) (1, l)
      val sts = term_count |> Utils.lazy_one_of_each
                           |> states
                           |> sort (int_ord o apply2 (sum o map fst))
      val sts1 = map (fn l => ((sum o map fst) l, (mul o map snd) l)) sts
      val sts2 = ([], sts1) |> Library.foldl (fn (((size, terms)::xs)::ys, (size', terms')) =>
                                  if size = size'
                                  then ((size', terms')::(size, terms)::xs)::ys
                                  else [(size', terms')]::((size, terms)::xs)::ys
                                | (_, (size', terms')) => [[(size', terms')]])
                            |> rev
                            |> map (fn ((size, trms)::xs) => (size, (mul o map snd) ((size, trms)::xs))
                                   |_ => raise ERROR "Invalid list" )
  in sts2 end

fun exhaust debug ctxt scheme term_size simps test =
  let val vars = scheme
                   |> Thm.full_prop_of
                   |> (fn t => Term.add_vars t [])
      val typs = map snd vars
      val term_count = GP.term_count tracing ctxt scheme term_size
      val timeout =  GP.max_time_in_fitness |> Config.get ctxt
                                            |> Time.fromSeconds
      fun prep trms = trms |> mk_subst vars
                           |> prepare ctxt scheme simps
      fun states f =
        case f () of
          SOME v => v :: states f
        | NONE => []
      fun get_states global i f set =
        if i > 0
        then case f () of
              SOME v => let val t = prep v
                        in
                          if Term_Tab.defined global t orelse
                             Term_Tab.defined set t
                          then get_states global i f set
                          else get_states global (i - 1) f (Term_Tab.update (t, v) set)
                        end
            | NONE => Term_Tab.dest set
        else Term_Tab.dest set
      fun sum l = Library.foldl (op +) (0, l)
      fun mul l = Library.foldl (op *) (1, l)
      val sts = term_count |> Utils.lazy_one_of_each
                           |> states
                           |> sort (int_ord o apply2 (sum o map fst))
      fun print v (i, j) =
        "<" ^ Syntax.string_of_term ctxt (Var v) ^ " : (" ^ string_of_int i ^ ", " ^ string_of_int j ^ ")>"
      fun print_state vars l =
        let val s = (sum o (map fst)) l
            val t = (mul o (map snd)) l
        in
        l |> map2 print vars
          |> space_implode ", "
          |> (fn str => tracing (str ^ " (" ^ string_of_int s ^ " - " ^ string_of_int t ^ ")")) end
      fun test' global (count : (int * int) list) =
        let val _ = if debug then print_state vars count
                        else ()
            val trms = count |> map fst
                             |> map2 pair typs
                             |> Par_List.map (fn (x, y) => Random_Terms.enumerate_lambda_terms x y)
            fun check (t, trms) =
              case GP.well_defined ctxt t of
                SOME ctxt => if Timeout.apply timeout (test ctxt) (GP.fnames_of ctxt)
                                handle Timeout.TIMEOUT _ => (GP.timeout_error ctxt t;
                                                             false)
                             then SOME (ctxt, t, trms)
                             else NONE
              | NONE => NONE
            fun prop global f =
              case get_states global block_size f Term_Tab.empty of
                [] => Table global
              | l => let val _ = if debug then tracing ("Diff: " ^ string_of_int (length l))
                                 else ()
                     in (case Par_List.get_some check l of
                         SOME r => Solution r
                       | NONE => let val global =
                                      (global, l)
                                        |> Library.foldl (fn (g, (t,_)) => Term_Tab.update (t, ()) g)
                                 in prop global f end) end
        in trms |> Utils.lazy_one_of_each
                |> prop global end
    val global_ref = Unsynchronized.ref Term_Tab.empty
    fun travel (x :: xs) =
      let val global = !global_ref
      in
      (case test' global x of
        Solution r => SOME r
      | Table global => let val _ = global_ref := global
                        in travel xs end) end
      | travel [] = NONE
  in travel sts end


end

structure Exhaust : EXHAUST = DB_EXHAUST

