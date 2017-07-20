(*  Title:      util/counting_terms.ML
    ID:         $Id: counting_terms.ML,v 1.00 2017/03/06 11:47:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2017

Fixpoint technique for counting terms in typed \<lamda>-calculus.
From Marek Zaionc's 1995 paper.
*)

signature COUNTING_TERMS =
sig

end

structure DB_Counting_Terms
= struct

fun surjections domain codomain =
  let val stack = [[]]
      fun goal state = forall (fn y => exists (fn (_, y') => y = y') state) codomain andalso
                       forall (fn x => exists (fn (x', _) => x = x') state) domain
      fun successors state =
        case find_first (fn x => forall (fn (x', _) => x <> x') state) domain of
          SOME x => map (fn y => (x, y) :: state) codomain
          | NONE => []
      fun all_surjections stack = 
        case Utils.dfs stack goal successors of
          SOME (state, stack) => state :: all_surjections stack
        | NONE => []
  in all_surjections stack end

fun equivalent p q =
  if p = q then true
  else (can range_type p andalso
        equivalent (range_type p) q) orelse
       (can range_type q andalso
        equivalent p (range_type q))

fun embeddable p q =
  let val (ps, _) = strip_type p
      val (qs, _) = strip_type q
      val surs = surjections ps qs
  in equivalent p q andalso exists (fn f => forall (fn (x,y) => x = y) f) surs end

fun direct_prolongation p q =
  let val (ps, ph) = strip_type p
      val (qs, _) = strip_type q
      val args_ok = length qs <= length ps andalso
                    qs |> map_index (fn (i, t) => (nth ps i, t))
                       |> forall (fn (p, q) => p = q)
(*                       |> tap (tracing o PolyML.makestring)*)
      fun head_ok ty = 
        exists (fn u_i => equivalent u_i q andalso
                          u_i |> strip_type
                              |> fst
                              |> exists (fn u_i_p => u_i_p = ty)) qs
  in args_ok andalso
     ps |> drop (length qs)
        |> (fn ps' => ps' ---> ph)
        |> head_ok end

end

structure Counting_Terms : COUNTING_TERMS = DB_Counting_Terms

