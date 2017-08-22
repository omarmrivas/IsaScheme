(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature DIVERGENCE =
sig

val walsh_critic      : Proof.context -> thm list -> term list -> term Seq.seq
val transverse_critic : Proof.context -> thm list -> term list -> term Seq.seq

end

structure DB_Divergence
(* : DIVERGENCE *)
= struct

fun conditional critic ctxt simps props =
  let val eqs = map (HOLogic.dest_Trueprop o Logic.strip_imp_concl) props
      val prems = map (Logic.strip_imp_prems) props
      val prem = hd prems
      fun prems_equals [] = true
        | prems_equals [_] = true
        | prems_equals (x :: y :: prems) = x = y andalso prems_equals (y :: prems)
  in if prems_equals prems
     then eqs |> critic ctxt simps
              |> Seq.map (Logic.list_implies o pair prem)
     else Seq.empty
  end

(* Preconditions of Walsh's divergence critic *)
fun precondictions_divergence_critic thy eqs =
    let fun pairs (h :: l) =
              l |> map SOME
                |> zip_options (h :: l)
               | pairs [] = []
             val H = Var (("H", 0), @{typ_pat "?'b\<Rightarrow>?'b"})
             val G = Var (("G", 0), @{typ_pat "?'b\<Rightarrow>?'a"})
             fun non_trivial env =
                  [H,G] |> map (Envir.norm_term env)
                          |> forall (fn (Abs (_, _, Bound _)) => false
                                      | _ => true)
    in eqs |> pairs
           |> map_index (fn (i, (eq,eq')) =>
                 let val s = (fst o HOLogic.dest_eq) eq
                     val s' = (fst o HOLogic.dest_eq) eq'
                     val U = Var (("U" ^ string_of_int i, 0), @{typ_pat "?'b"})
                 in [(G $ (H $ U), s'), (G $ U, s)] end)
           |> maps I
           |> (fn pairs => 
                 (Unify.unifiers (Context.Theory thy,(Envir.empty 1),pairs)
                           handle ListPair.UnequalLengths => Seq.empty
                                | TERM _ => Seq.empty))
           |> Seq.map fst
           |> Seq.take 20
(*                |> Seq.filter non_trivial*)
    end

(* Postconditions of Walsh's divergence critic *)
fun postconditions_divergence_critic ctxt envs =
  let val U0 = Var (("U0", 0), @{typ_pat "?'b"})
      val H = Var (("H", 0), @{typ_pat "?'b\<Rightarrow>?'b"})
      val G = Var (("G", 0), @{typ_pat "?'b\<Rightarrow>?'a"})
      fun mk_eqs env =
        let val lhs = Envir.norm_term env (G $ (H $ U0))
            val rhs1 = Envir.norm_term env (G $ U0)
            val eqs1 = [H, G] |> map (Envir.norm_term env)
                              |> map (fn F => F $ rhs1)
                              |> filter (can (Syntax.check_term ctxt))
                              |> map (fn rhs1 => HOLogic.mk_eq (lhs, rhs1))
(*                              |> Seq.of_list*)
        in eqs1 end
  in envs |> Seq.list_of
          |> maps mk_eqs end

fun walsh_critic' ctxt thy simps eqs =
  eqs |> precondictions_divergence_critic thy
      |> postconditions_divergence_critic ctxt
      |> map (Utils.normalise_term ctxt simps)
      |> filter (fn eq => eq <> @{term "True"} andalso
                          eq <> @{term "False"})
      |> Utils.make_term_set thy

fun walsh_critic ctxt simps eqs =
  let val thy = Proof_Context.theory_of ctxt
  in
  if forall (can HOLogic.dest_eq) eqs
  then (walsh_critic' ctxt thy simps eqs) @
       (walsh_critic' ctxt thy simps (map Utils.swap_eq eqs))
        |> Utils.make_term_set thy
        |> map HOLogic.mk_Trueprop
        |> Seq.of_list
  else Seq.empty
  end

val conditional_walsh_critic = conditional walsh_critic

(* Preconditions of transverse wave rules *)
fun precondictions_transverse thy eqs =
  let fun pairs (h :: l) =
         l |> map SOME
           |> zip_options (h :: l)
        | pairs [] = []
      val H = Var (("H", 0), @{typ_pat "?'a \<Rightarrow> ?'a"})
      val G = Var (("G", 0), @{typ_pat "?'a \<Rightarrow> ?'b \<Rightarrow> ?'c"})
      val Acc = Var (("Acc", 0), @{typ_pat "?'b"})
      fun non_trivial env =
           [H,G] |> map (Envir.norm_term env)
                 |> forall (fn (Abs (_, _, Bound _)) => false
                             | _ => true)
  in eqs |> pairs
         |> map_index (fn (i, (eq,eq')) =>
               let val s = (fst o HOLogic.dest_eq) eq
                   val s' = (fst o HOLogic.dest_eq) eq'
                   val U = Var (("U" ^ string_of_int i, 0), @{typ_pat "?'a"})
               in [((G $ (H $ U)) $ Acc, s'), ((G $ U) $ Acc, s)] end)
         |> maps I
         |> (fn pairs => 
               (Unify.unifiers (Context.Theory thy,(Envir.empty 1),pairs)
                         handle ListPair.UnequalLengths => Seq.empty
                              | TERM _ => Seq.empty))
         |> Seq.map fst
         |> Seq.take 40
   end

(* Postconditions of transverse wave rules *)
fun postconditions_transverse thy envs =
  let val H = Var (("H", 0), @{typ_pat "?'a \<Rightarrow> ?'a"})
      val G = Var (("G", 0), @{typ_pat "?'a \<Rightarrow> ?'b \<Rightarrow> ?'c"})
      val Acc = Var (("Acc", 0), @{typ_pat "?'b"})
      val U0 = Var (("U0", 0), @{typ_pat "?'a"})
      fun mk_eq env =
        let val lhs = Envir.norm_term env ((G $ (H $ U0)) $ Acc)
            val rhs1 = Envir.norm_term env (G $ U0)
            val acc = Envir.norm_term env Acc
            val typ = acc |> Envir.norm_term env
                          |> type_of
            val F = Var (("F", 0), typ --> typ)
            val eqs1 = HOLogic.mk_eq (lhs, rhs1 $ (F $ acc))
                              |> HOLogic.mk_Trueprop
        in eqs1 end
  in envs |> Seq.map mk_eq
          |> Seq.list_of
          |> Utils.make_term_set thy
  end

fun transverse_critic' ctxt thy simps eqs =
  eqs |> precondictions_transverse thy
      |> postconditions_transverse thy
      |> map (Utils.normalise_term ctxt simps)
      |> filter (fn eq => eq <> @{prop "True"} andalso
                          eq <> @{prop "False"} andalso
                          exists_subterm (fn Var _ => true
                                            | _ => false) eq)

fun transverse_critic ctxt simps eqs =
  let val thy = Proof_Context.theory_of ctxt
  in
    if forall (can HOLogic.dest_eq) eqs
    then (transverse_critic' ctxt thy simps eqs) @
         (transverse_critic' ctxt thy simps (map Utils.swap_eq eqs))
         |> Utils.make_term_set thy
         |> Seq.of_list
    else Seq.empty
  end

val conditional_transverse_critic = conditional transverse_critic

end

structure Divergence : DIVERGENCE = DB_Divergence

