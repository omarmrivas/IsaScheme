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

fun mk_fun ((i,j) :: xs) x =
  if i = x
  then j
  else mk_fun xs x
  | mk_fun [] x = x

val arg = length o fst o strip_type

fun rank typ =
  let val (args, _) = strip_type typ
      fun max xs = fold (fn x => fn m => Int.max (x,m)) xs 0
  in case args of
        [] => 0
      |  _ => args |> map (fn ty => 1 + rank ty)
                   |> max
  end

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
  (snd o strip_type) p = (snd o strip_type) q
(*  if p = q then true
  else (can range_type p andalso
        equivalent (range_type p) q) orelse
       (can range_type q andalso
        equivalent p (range_type q))*)


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

fun direct_prolongations mu =
  let val muis = (fst o strip_type) mu
  in muis |> maps (fn mui => if equivalent mu mui
                             then mui |> fst o strip_type
                                      |> map (fn muip => muis ---> muip)
                             else [])
  end

datatype etree = 
    TerminalExtension of typ * typ list
  | TerminalProlongation of typ * typ list
  | NonTerminal of typ * typ list * etree list

fun extensions mu =
  let fun ext tks ti =
            ti |> direct_prolongations
               |> List.partition (fn ti_prol => forall (not o embeddable ti_prol) (ti :: tks))
               |> (fn (exts, dps) => 
                      case (exts, dps) of
                       ([], []) => TerminalExtension (ti, tks)
                     | ([], dps) => NonTerminal (ti, tks, map (TerminalProlongation o rpair (ti :: tks)) dps)
                     | (exts, []) => NonTerminal (ti, tks, map (ext (ti :: tks)) exts)
                     | (exts, dps) => NonTerminal (ti, tks, map (ext (ti :: tks)) exts @
                                                            map (TerminalProlongation o rpair (ti :: tks)) dps))
  in ext [] mu end

(* the number of closed terms *)

local
fun ST f typ =
  typ |> fst o strip_type
      |> map_index I
      |> filter (fn (_, ty) => equivalent typ ty andalso f ty)
in
val S = ST (fn ty => rank ty >= 1)
val T = ST (fn ty => rank ty = 0)
end

datatype polynomial =
        Val of int
      | Var of typ
      | Add of polynomial * polynomial
      | Mul of polynomial * polynomial

fun fold_apoly f (Add (t, u)) = fold_apoly f t #> fold_apoly f u
  | fold_apoly f (Mul (t, u)) = fold_apoly f t #> fold_apoly f u
  | fold_apoly f a = f a

val add_vars = fold_apoly (fn Var v => insert (op =) v | _ => I)

fun eval_poly (Val i) _ = i
  | eval_poly (Var v) s = the (Type_Tab.lookup s v)
  | eval_poly (Add (e1, e2)) s = eval_poly e1 s + eval_poly e2 s
  | eval_poly (Mul (e1, e2)) s = eval_poly e1 s * eval_poly e2 s

fun empty_state polys =
  [] |> fold (fn (poly, _) => fn s => add_vars poly s) polys
     |> map (fn ty => (ty, 0))
     |> Type_Tab.make

fun next_state polys s =
  fold (fn (Var v, poly) => (fn st =>
          Type_Tab.update (v, eval_poly poly s) st)
         | _ => raise ERROR "Polynomial not Var") polys s

fun eq_states s1 s2 =
  (s1, s2) |> apply2 (sort (prod_ord Term_Ord.typ_ord int_ord) o Type_Tab.dest)
           |> op =

fun construct_polynomial ctxt tree =
  let fun mul tao_args taoi =
          fold (fn taoip => fn aexp => Mul (aexp, Var (tao_args ---> taoip)))
               ((fst o strip_type) taoi)
               (Val 1)
      fun add tao =
          fold (fn (_, taoi) => fn aexp => Add (aexp, mul ((fst o strip_type) tao) taoi))
               (S tao)
               (Val 0)
  in case tree of
     NonTerminal (ty, _, _) => (Var ty, Add (Val (length (T ty)), add ty))
   | TerminalExtension (ty, _) => (Var ty, Val (length (T ty)))
   | TerminalProlongation (ty, tks) =>
        (case find_first (fn taos => embeddable ty taos) tks of
          SOME taos => (Var ty, Var taos)
        | NONE => error ("not embeddable: \n" ^ Utils.str_of_typs ctxt [ty] ^ " :: \n " ^ Utils.str_of_typs ctxt tks))
    
  end

fun construct_polynomials ctxt tree =
  case tree of
    NonTerminal (ty, tks, xs) =>
        construct_polynomial ctxt (NonTerminal (ty, tks, xs)) :: maps (construct_polynomials ctxt) xs
  | TerminalExtension (ty, tks) =>
        [construct_polynomial ctxt (TerminalExtension (ty, tks))]
  | TerminalProlongation (ty, tks) =>
        [construct_polynomial ctxt (TerminalProlongation (ty, tks))]

fun simplify_polynomials polys =
  let val f = polys |> filter (fn (Var _ , Var _) => true | _ => false)
                    |> mk_fun
      fun simplify (Val i) = Val i
        | simplify (Var v) = f (Var v)
        | simplify (Mul (Val 1, e)) = simplify e
        | simplify (Mul (e, Val 1)) = simplify e
        | simplify (Add (Val 0, e)) = simplify e
        | simplify (Add (e, Val 0)) = simplify e
        | simplify (Mul (e1, e2)) = Mul (simplify e1, simplify e2)
        | simplify (Add (e1, e2)) = Add (simplify e1, simplify e2)
      fun full_simplify e =
          let val e' = simplify e
          in if e = e' 
             then e
             else full_simplify e'
          end
      val polys' = map (apply2 full_simplify) polys
  in filter (fn (p1, p2) => if p1 = p2
                            then false
                            else true) polys'
  end

  fun polynomials ctxt = distinct (op =) o simplify_polynomials o
                         construct_polynomials ctxt o extensions
  
  fun count_beta_eta_long ctxt size mu =
    let val polys = polynomials ctxt mu
        fun fixpoint n s =
            if n <= 0
            then the (Type_Tab.lookup s mu)
            else
              let val _ = tracing (string_of_int (the (Type_Tab.lookup s mu)))
                  val s' = next_state polys s
              in if eq_states s s'
                 then the (Type_Tab.lookup s mu)
                 else fixpoint (n-1) s'
              end
    in polys |> empty_state
             |> fixpoint size
    end

end

structure Counting_Terms : COUNTING_TERMS = DB_Counting_Terms

