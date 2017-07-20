(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature ORDERS =
sig

val map_term_to_int :  ((string * 'a) * int) list * (((string * 'b) * 'c) * int) list -> term -> int
val extend_ord      : (('a * int) list -> bool) -> ('a * int) list -> 'a list -> ('a * int) list list
val extend_ord_eval : (('a * int) list -> bool) -> ('a * int) list -> 'a list -> bool
val extract_compatible_orders_rpo : ((term * int) list -> term * term -> bool) ->
    thm -> term list * (term * int) list list
val lpo_g : (term * int) list -> term * term -> bool

end

structure DB_Orders
(* : ORDERS *)
= struct

fun map_term_to_int (const_map, _) (Const (n,_)) = 
    const_map |> get_first (fn ((n',_),i) => if n = n' then SOME i
                                                   else NONE)
              |> the_default ~1
  | map_term_to_int (_, var_map) (Var ((n, _),_)) =
    var_map |> get_first (fn (((n', _),_),i) => if n = n' then SOME i
                                               else NONE)
            |> the_default ~1
  | map_term_to_int (_, _) _ = ~1

fun extend_ord _ [] [] = []
  | extend_ord P ord_index [] = if P ord_index 
                                then [ord_index]
                                else []
  | extend_ord P [] (v :: V) = extend_ord P [(v,0)] V
  | extend_ord P ord_index (v :: V) =
    ((0, ~1, []), ord_index)
      |> Library.foldl (fn ((i, indx, result), _) =>
                           let
                             val (O1,O2) = chop i ord_index
                             val ((v',i') :: O2) = O2
                           in if indx = i' then (i+1, indx, result)
                              else (i+1, indx+1,
                                    (O1 @ [(v,indx+1), (v',i'+1)] @
                                     (map (fn (a,i) => (a,i+1)) O2)) ::
                                    ((O1 @ [(v,indx+1), (v',i')] @ O2) :: result)) end)
      |> (fn (_, indx, x) => x @ [ord_index @ [(v,indx+1)]])
      |> maps (fn ord_index => extend_ord P ord_index V)

fun extend_ord_eval P [] [] = P []
  | extend_ord_eval P ord_index [] = P ord_index
  | extend_ord_eval P [] (v :: V) = extend_ord_eval P [(v,0)] V
  | extend_ord_eval P ord_index (v :: V) =
    ((0, ~1, []), ord_index)
      |> Library.foldl (fn ((i, indx, result), _) =>
                           let
                             val (O1,O2) = chop i ord_index
                             val ((v',i') :: O2) = O2
                           in if indx = i' then (i+1, indx, result)
                              else (i+1, indx+1,
                                    (O1 @ [(v,indx+1), (v',i'+1)] @
                                     (map (fn (a,i) => (a,i+1)) O2)) ::
                                    ((O1 @ [(v,indx+1), (v',i')] @ O2) :: result)) end)
      |> (fn (_, indx, x) => x @ [ord_index @ [(v,indx+1)]])
      |> forall (fn ord_index => extend_ord_eval P ord_index V)


fun lpo_g f_ord (s, t) =
    let val consts = [] |> Term.add_consts s
                        |> Term.add_consts t
                        |> map Const
        val f_ord = if null f_ord then f_ord
                    else f_ord |> filter (fn (Const (n, _), _) => exists (fn Const (n', _) => n = n' | _ => raise ERROR "lpo_g") consts | _ => raise ERROR "lpo_g")
                               |> sort (int_ord o (apply2 snd))
                               (* Normalize filtered consts *)
                               |> (fn l =>
                                      if null l
                                      then l
                                      else l
                                             |> (fn l => ((0, (snd o hd) l, []), l))
                                             |> Library.foldl (fn ((indx,a,l), (t, i)) => if i <> a then (indx + 1, i, l @ [(t, indx + 1)])
                                                                                          else (indx, i, l @ [(t, indx)]))
                                             |> (fn (_,_,l) => l))
    in
      [] |> Term.add_vars s
         |> Term.add_vars t
         |> map Var
         |> tap (fn Vs => if length Vs >= 4 andalso
                             length consts >= 4 andalso
                             length Vs * length consts >= 28
                          then tracing "A potential memory explosion!! "(*raise MemoryExplosion (s, t)*)
                          else ())
         |> extend_ord_eval (fn ord => 
                                ord |> pair ([],[])
                                    |> Library.foldl (fn ((consts_map, vars_map), (Var V, I)) => (consts_map, (V, I) :: vars_map)
                                                       | ((consts_map, vars_map), (Const C, I)) => ((C, I) :: consts_map, vars_map)
                                                       | ((consts_map, vars_map), (_, _)) => (consts_map, vars_map))
                                    |> map_term_to_int
                                    |> Term_Ord.term_lpo
                                    |> (fn t_ord => t_ord (s, t) = GREATER)) f_ord
    end

fun extract_compatible_orders_rpo lpo th =
    let
      val (s,t) = Utils.dest_equation th
(*      val _ = tracing ("Computing orders: " ^ Syntax.string_of_term_global (Thm.theory_of_thm th) (Thm.full_prop_of th))*)
      val consts = [] |> Term.add_consts s
                      |> Term.add_consts t
                      |> distinct (fn ((n,_),(m,_)) => n = m)
                      |> filter_out (fn (cname, _) => "==" = cname)
                      |> map Const
      val _ = if length consts > 5
              then tracing ("extract_compatible_orders_rpo Consts: " ^ (string_of_int (length consts)))
              else ()
      val consts_orders = extend_ord (fn order => lpo order (s,t)) [] consts
    in (consts, consts_orders) end

end

structure Orders : ORDERS = DB_Orders

