(*  Title:      sat_interface.ML
    ID:         $Id: sat_interface.ML,v 1.000 2013/01/16 11:40:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   Universidad Politecnica de San Luis Potosi.

    Interface to external solvers 
*)

signature SAT_INTERFACE =
sig
  val mk_conj_balanced :  term list -> term
  val mk_disj_balanced :  term list -> term
  val ord_to_term_rpo  : (term * (string * 'a)) list -> (term * int) list list -> term
  val find_orders      : term -> (term * int) list Seq.seq
(*  val find_model   : bool -> int -> string list -> term -> (string * int) list list option*)
end

structure DB_SAT_Interface
(* : SAT_INTERFACE *)
= struct

(* a \<longleftrightarrow> b *)
fun bit_equal a b =
  HOLogic.mk_conj (
  HOLogic.mk_disj ((HOLogic.mk_not a), b),
  HOLogic.mk_disj (a, (HOLogic.mk_not b)))

(* \<not>a \<and> b *)
fun bit_less a b =
  HOLogic.mk_conj ((HOLogic.mk_not a), b)

fun bits_equal (aa, bb) = 
  let fun bits_equal_aux t (a :: aa) (b :: bb) =
        bits_equal_aux (HOLogic.mk_conj (t, bit_equal a b)) aa bb
        | bits_equal_aux t _ _ = t
  in bits_equal_aux @{term "True"} aa bb end

fun bits_less (aa, bb) =
  let fun bits_less_aux t aa' bb' (a :: aa) (b :: bb) =
        let val t = HOLogic.mk_disj (t, HOLogic.mk_conj (bits_equal (aa', bb'), bit_less a b))
        in bits_less_aux t (a :: aa') (b :: bb') aa bb end
        | bits_less_aux t _ _ _ _ = t
  in bits_less_aux @{term "False"} [] [] aa bb end

fun bits_of_var bits (Free (a, _)) =
  (0 upto bits) |> map ((fn sbit => Free (a ^ sbit, @{typ "bool"})) o string_of_int)
                |> rev
  | bits_of_var _ _ = raise ERROR "bits_of_var"

fun vars_equal bits A B =
    bits_equal (apply2 (bits_of_var bits) (A, B))

fun vars_less bits A B =
    bits_less (apply2 (bits_of_var bits) (A, B))

fun term_to_sat_prop t =
  let val bits = [] |> Term.add_frees t
                    |> length
                    |> (fn n => ceil (Math.ln (real n) / Math.ln 2.0) - 1)
      fun term_to_sat_aux (t $ u) =
          (case Term.strip_comb (t $ u) of
              (Const (n, _), [A, B]) =>
                if n = Const_Names.hol_eq then vars_equal bits A B
                else if n = Const_Names.hol_less then vars_less bits A B
                else if n = Const_Names.hol_conj then HOLogic.mk_conj (apply2 term_to_sat_aux (A, B))
                else if n = Const_Names.hol_disj then HOLogic.mk_disj (apply2 term_to_sat_aux (A, B))
                else (t $ u)
            | (Const (n, _), [A]) =>
                if n = Const_Names.hol_not then HOLogic.mk_not (term_to_sat_aux A)
                else (t $ u)
            | _ => (t $ u))
        | term_to_sat_aux t = t
  in (bits, term_to_sat_aux t) end

fun binary_to_int cs =
  let
    fun scan (num, []) = (num, [])
      | scan (num, c :: cs) =
            scan (2 * num + c, cs)
  in (fst o scan) (0, cs) end

fun value_of_var bits tab sigma v =
  v |> bits_of_var bits
    |> map (fn v => sigma (the (Termtab.lookup tab v)))
    |> map (fn SOME true => 1
             | SOME false => 0
             | _ => raise ERROR "value_of_var")
    |> binary_to_int

fun normalize_values l =
  let val l = sort (int_ord o apply2 snd) l
  in if null l
     then l
     else l |> (fn l => ((0, (snd o hd) l, []), l))
            |> Library.foldl (fn ((indx,a,l), (t, i)) => if i <> a then (indx + 1, i, l @ [(t, indx + 1)])
                                                                   else (indx, i, l @ [(t, indx)]))
            |> (fn (_,_,l) => l)
  end

fun ord_of_vars bits tab sigma vs =
  vs |> map (fn v => (v, value_of_var bits tab sigma v))
     |> normalize_values

fun ord_to_sat_prop _ [] = @{term "True"}
  | ord_to_sat_prop bits (ord :: orders) =
    ((ord, @{term "True"}), orders)
      |> Library.foldl (fn (((v, i), t), (v', i')) =>
                          if i < i' then ((v', i'), HOLogic.mk_conj (t, vars_less bits v v'))
                          else if i = i' then ((v', i'), HOLogic.mk_conj (t, vars_equal bits v v'))
                          else ((v', i'), HOLogic.mk_conj (t, vars_less bits v' v)))
      |> snd

fun make_less v v' =
  (@{term "op < :: nat \<Rightarrow> nat \<Rightarrow> bool"} $ Free (v,@{typ "nat"})) $ Free (v',@{typ "nat"})

fun ord_to_term [] = @{term "True"}
  | ord_to_term (ord :: orders) =
    ((ord, @{term "True"}), orders)
      |> Library.foldl (fn (((v, i), t), (v', i')) =>
                          if i < i' then ((v', i'), HOLogic.mk_conj (t, make_less v v'))
                          else if i = i' then ((v', i'), HOLogic.mk_conj (t, HOLogic.mk_eq (Free (v, @{typ "nat"}), Free (v', @{typ "nat"}))))
                          else ((v', i'), HOLogic.mk_conj (t, make_less v' v)))
      |> snd

fun from_to (a, b) =
  let fun next i = Seq.make(fn () => if i <= b then SOME (i, next (i + 1)) else NONE)
  in next a end

fun find_orders t =
  let val (bits, t_sat) = term_to_sat_prop t
      val vars = [] |> Term.add_frees t
                    |> map Free
      fun next t = Seq.make(fn () => 
          let val (pform, table) = Prop_Logic.prop_formula_of_term t Termtab.empty
          in case SAT_Solver.invoke_solver "auto" pform of
              SAT_Solver.SATISFIABLE sigma =>
                  let val ord = ord_of_vars bits table sigma vars
                      val t = HOLogic.mk_conj (t, HOLogic.mk_not (ord_to_sat_prop bits ord))
                  in SOME (ord, next t) end
            | _ => NONE
          end)
  in next t_sat end

fun mk_conj_balanced [] = @{term "False"}
  | mk_conj_balanced ts = Balanced_Tree.make HOLogic.mk_conj ts

fun mk_disj_balanced [] = @{term "False"}
  | mk_disj_balanced ts = Balanced_Tree.make HOLogic.mk_disj ts

fun ord_to_term_rpo consts_map ords =
    let
      fun const_to_name (Const (n, _)) =
            consts_map |> get_first (fn (Const (n',_),(name,_)) =>
                                        if n = n' then SOME name
                                        else NONE
                                        | _ => raise ERROR "ord_to_term_rpo")
                       |> the_default ""
        | const_to_name _ = raise ERROR "ord_to_term"
      fun X_ord_to_terms to_name to =
          to |> map (apfst to_name)
             |> ord_to_term
    in ords |> map (fn c => X_ord_to_terms const_to_name c)
            |> mk_disj_balanced end

end

structure SAT_Interface : SAT_INTERFACE = DB_SAT_Interface
