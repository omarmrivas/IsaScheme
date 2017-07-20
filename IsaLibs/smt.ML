(*  Title:      util/smt.ML
    ID:         $Id: smt.ML,v 1.00 2016/24/08 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

SMT-LIB file reader/converter.
*)

signature SMT_CONVERTER =
sig

val get_smt2_files : string -> string -> string list

val smt2_to_isabelle : Proof.context -> bool ->
      string ->
        string ->
          string -> string list -> string -> string list

val smt2bash_to_isabelle : Proof.context ->
      string ->
        string -> string ->
          string ->
            string list -> (string * (bool * string)) list

end

structure DB_SMT_Converter
(* : SMT_READER *)
= struct

open SMTLIB

val smt_keywords =
  ["declare-datatypes",
   "define-fun-rec",
   "define-funs-rec",
   "define-fun",
   "assert-not",
   "check-sat",
   "distinct",
   "forall",
   "case",
   "Bool",
   "Int",
   "true",
   "let",
   "not",
   "and",
   "or",
   "ite",
   "false",
   "match",
   "par",
   "=",
   "=>",
   "<=",
   ">=",
   ">",
   "<",
   "+",
   "-",
   "*",
   "@"]

val isabelle_term_translations =
  [("=>", "-->"),
   ("true", "True"),
   ("false", "False"),
   ("distinct", "\<noteq>"),
   ("<=", "\<le>"),
   (">=", "\<ge>"),
   ("not", "\<not>"),
   ("and", "\<and>"),
   ("or", "\<or>")]

val isabelle_binary_operators =
  ["=",
   "=>",
   "distinct",
   "<=",
   ">",
   "<",
   "+",
   "-",
   "*",
   "and",
   "or",
   ">="]

val isabelle_type_translations =
  [("Bool", "bool"),
   ("Int", "int")]

fun map_isabelle_types str =
    case find_first (fn (smt_typ, _) => smt_typ = str) isabelle_type_translations of
      SOME ((_, isabelle_typ)) => isabelle_typ
      | NONE => str
           
fun map_isabelle_terms str =
    case find_first (fn (smt_term, _) => smt_term = str) isabelle_term_translations of
      SOME ((_, isabelle_term)) => isabelle_term
      | NONE => str

fun available_var ctxt name =
  if exists (fn cmd => cmd = name) smt_keywords
  then true
  else case try (Syntax.read_term ctxt) name of
         SOME (Free _) => true
        | _ => false

fun syms_of_tree _ tab (Num _) = tab
  | syms_of_tree _ tab (Dec _) = tab
  | syms_of_tree _ tab (Str _) = tab
  | syms_of_tree _ tab (Key _) = tab
  | syms_of_tree ctxt tab (Sym s) =
    if Str_Tab.defined tab s
    then tab
    else if available_var ctxt s
         then Str_Tab.update (s, s) tab
         else let fun find_name i names =
                  if i > length (Str_Tab.keys tab)
                  then let val s = "n"
                           val name = singleton (Name.variant_list names) s
                       in
                        if available_var ctxt name
                        then name
                        else find_name 0 (name :: names)
                       end
                  else
                  let val name = singleton (Name.variant_list names) s
                  in
                    if available_var ctxt name
                    then name
                    else find_name (i+1) (name :: names)
                  end
              in Str_Tab.update (s, find_name 0 (Str_Tab.keys tab @ (map snd o Str_Tab.dest) tab)) tab
              end
  | syms_of_tree ctxt tab (S l) =
      (tab, l)
      |> Library.foldl (fn (tab, e) => syms_of_tree ctxt tab e)

fun sanitize_tree (_, (Num i)) = Num i
  | sanitize_tree (_, (Dec i)) = Dec i
  | sanitize_tree (_, (Str s)) = Str s
  | sanitize_tree (_, (Key s)) = Key s
  | sanitize_tree (tab, (Sym s)) = Sym ((the o Str_Tab.lookup tab) s)
  | sanitize_tree (tab, (S l)) =
      l |> map (fn e => sanitize_tree (tab, e))
        |> S

(*fun change_default i (Num n) = (i, Num n)
  | change_default i (Dec n) = (i, Dec n)
  | change_default i (Str s) = (i, Str s)
  | change_default i (Key s) = (i, Key s)
  | change_default i (Sym "default") = (i+1, Sym ("default" ^ string_of_int i))
  | change_default i (Sym s) = (i, Sym s)
  | change_default i (S l) =
    ((i, []), l) |> Library.foldl (fn ((i, l), s) => 
                      let val (j, t) = change_default i s
                      in (j, t :: l) end)
                 |> (fn (i, l) => (i, S (rev l)))*)

fun s_expressions ctxt str =
  let fun clean_comments str =
          str |> space_explode "\n"
              |> map_filter (fn line => let val i = line |> String.explode
                                                         |> find_index (fn c => c = #";")
                                        in
                                        if i = ~1
                                        then SOME line
                                        else NONE end)
              |> space_implode "\n"
      fun scan [] _ _ s_exps =
            s_exps |> rev
                   |> pair (Str_Tab.empty, [])
                   |> Library.foldl
                        (fn ((tab, trees), expr) =>
                            let val (tab, e) = ((fn e => let val tab = syms_of_tree ctxt
                                                                              tab
                                                                              e
                                                   in (tab, e) end) o
(*                                                   SMTLIB.parse o *)
(*                                                   (snd o change_default 0) o*)
                                                   (fn x => SMTLIB.parse x handle PARSE (i, str) => (tracing ("Error on expression: " ^ hd x); raise (PARSE (i, str)))) o 
                                                   single o
(*                                                   (fn s => (tracing s; s)) o*)
(*                                                   clean_comments o*)
                                                   String.implode) expr
                                val tree = sanitize_tree (tab, e)
                            in (tab, tree :: trees) end)
                   |> rev o snd
        | scan (c :: chars) stack s s_exps =
          case c of
            #"(" => scan chars (#"(" :: stack) (#"(" :: s) s_exps
          | #")" => let val stack = case stack of
                                     _ :: stack => stack
                                   | [] => raise ERROR "Malformed s expression"
                    in if length stack = 0
                       then scan chars stack [] ((rev (#")" :: s)) :: s_exps)
                       else scan chars stack (#")" :: s) s_exps
                    end
          | _ => scan chars stack (c :: s) s_exps
  in scan (String.explode (clean_comments str)) [] [] [] end

(*
(declare-datatypes (a) ((list (nil) (cons (head a) (tail (list a))))))
*)

datatype smt_type =
  SMTty_name of string |
  SMTty_params_name of (smt_type * string) |
  SMTty_fun of smt_type * smt_type |
  SMTty_times of smt_type list

(* (tail (list a) *)
datatype smt_type_argument =
  SMTty_arg1 of smt_type |
  SMTty_arg2 of (string * smt_type)

datatype smt_type_constructor =
  SMTty_const of (string * smt_type_argument list)

datatype smt_datatype =
  SMTty of (string * string list * smt_type_constructor list)

(* ### smt_datatype to Isabelle/HOL ### *)

(*fun parametrize meta_params params =
  if null params orelse exists (fn str => str = hd params) meta_params
  then
      params |> map (fn str => if exists (fn s => s = str) meta_params
                               then "'" ^ str
                               else str)
             |> space_implode ","
             |> (fn str => if str = ""
                           then ""
                           else if exists_string (fn "," => true
                                                  | _ => false) str
                           then enclose "(" ")" str
                           else str)
  else let val head = hd params
           val pars = tl params
       in parametrize meta_params pars ^ " " ^ head
            |> enclose "(" ")"
       end*)

fun smt_type_to_isabelle params (SMTty_name name) =
    if exists (fn s => s = name) params
    then "'" ^ name
    else map_isabelle_types name
  | smt_type_to_isabelle params (SMTty_params_name (params', name)) = 
      smt_type_to_isabelle params params' ^ " " ^ name
  | smt_type_to_isabelle params (SMTty_fun (a, b)) = 
      "(" ^ smt_type_to_isabelle params a ^ " => " ^ smt_type_to_isabelle params b ^ ")"
  | smt_type_to_isabelle params (SMTty_times typs) =
      typs |> map (smt_type_to_isabelle params)
           |> space_implode ","
           |> enclose "(" ")"

fun smt_type_argument_to_isabelle params (SMTty_arg1 typ) =
  smt_type_to_isabelle params typ
  | smt_type_argument_to_isabelle params (SMTty_arg2 (dest, typ)) =
  "(" ^ dest ^ ": \"" ^ smt_type_to_isabelle params typ ^ "\")"

fun smt_type_argument_to_isabelle2 params (SMTty_arg1 typ) =
  smt_type_to_isabelle params typ
  | smt_type_argument_to_isabelle2 params (SMTty_arg2 (dest, typ)) =
  "(" ^ dest ^ "::" ^ smt_type_to_isabelle params typ ^ ")"

(* (cons (head a) (tail (list a))) *)
fun smt_type_constructor_to_isabelle params (SMTty_const (c, args)) =
  args |> map (smt_type_argument_to_isabelle params)
       |> space_implode " "
       |> (fn cs => if null args
                    then c
                    else c ^ " " ^ cs)

fun  smt_datatype_to_isabelle (SMTty (name, params, cs)) =
  let val body = cs |> map (smt_type_constructor_to_isabelle params)
                    |> space_implode " | "
      val params_typ = params |> map SMTty_name
                              |> SMTty_times
  in if null params
     then "datatype " ^
          name ^ " = " ^ body
     else "datatype " ^ smt_type_to_isabelle params params_typ ^ " " ^
          name ^ " = " ^ body end

(* ### smt_datatype to Isabelle/HOL ### *)

fun dest_sym (Sym n) = n
  | dest_sym x = raise ERROR ("Not Sym expression: " ^ (str_of x))

fun smt_type_fn (S [Sym name]) = SMTty_name name
  | smt_type_fn (S [Sym name, typ]) = SMTty_params_name (smt_type_fn typ, name)
(*  | smt_type_fn (S [Sym name, S ps]) = 
      SMTty_params_name (map dest_sym ps, name)*)
  | smt_type_fn (Sym name) = SMTty_name name
  | smt_type_fn (S [Sym "=>", a, b]) = SMTty_fun (smt_type_fn a, smt_type_fn b)
  | smt_type_fn (S (Sym name :: ps)) = SMTty_params_name (smt_type_params_fn ps, name)
  | smt_type_fn x = raise ERROR ("Malformed s expression on type declaration: "
                                            ^ (str_of x)) and
    smt_type_params_fn ps =
  ps |> map smt_type_fn
     |> SMTty_times

fun smt_params_fn (S ps) = map dest_sym ps
  | smt_params_fn x  = raise ERROR ("Not (S Syms) expression: " ^ (str_of x))

(* (tail (list a)) *)
fun smt_type_argument_fn (S [Sym name, typ]) =
  SMTty_arg2 (name, smt_type_fn typ)
  | smt_type_argument_fn x = raise ERROR ("Not (S [Sym name, typ]) expression: " ^ (str_of x))

(* (cons (head a) (tail (list a))) *)
fun smt_type_constructor_fn (S (Sym name :: args)) =
  SMTty_const (name, map smt_type_argument_fn args)
  | smt_type_constructor_fn x = raise ERROR ("Not (S (Sym name :: args)) expression: " ^ (str_of x))

(* (declare-datatypes (a) ((list (nil) (cons (head a) (tail (list a)))))) *)
fun smt_datatype_fn (S (Sym "declare-datatypes" :: (params :: [S [S ((Sym name) :: cs)]]))) = 
  SMTty (name, smt_params_fn params, map smt_type_constructor_fn cs)
  | smt_datatype_fn x = raise ERROR ("Not (S (Sym \"declare-datatypes\" :: (params :: [S [S ((Sym name) :: cs)]]))) expression: " ^ (str_of x))

(* (define-fun-rec last ((x (list Nat))) Nat (match x (case nil Z) (case (cons y z) (match z (case nil y) (case (cons x2 x3) (last z)))))) *)

datatype smt_term =
  SMTvar of string |
  SMTnum of int |
  SMTapp of smt_term * smt_term list |
  SMTlet of (smt_term * smt_term) list * smt_term |
  SMTmatch of smt_term * (smt_term * smt_term) list |
  SMTas of smt_term * smt_type |
  SMTlambda of smt_type_argument list * smt_term

fun exists_subterm s (SMTvar v) = s = SMTvar v
  | exists_subterm s (SMTapp (u, vs)) = s = SMTapp (u, vs) orelse
                                        s = u orelse
                                        exists (exists_subterm s) vs
  | exists_subterm s (SMTas (u, _)) = s = u
  | exists_subterm _ _ = false

(* FIXME: consider SMTas and SMTlambda *)
fun subst x y (SMTvar v) =
      (case y of
        SMTvar y => if String.isPrefix "default" y
                    then (SMTvar v)
                    else
                    (if x = (SMTvar v)
                     then SMTvar y
                     else (SMTvar v))
     | y => (if x = (SMTvar v)
             then y
             else (SMTvar v)))
  | subst x y (SMTapp (s, ts)) =
      SMTapp (subst x y s, map (subst x y) ts)
  | subst x y (SMTlet (vars, t)) =
      let val (foo, vars) = ((false, []), vars)
                      |> Library.foldl (fn ((foo, vars), (var, value)) =>
                              let val foo' = foo orelse
                                            (case var of
                                              SMTvar v => x = SMTvar v
                                            | _ => false)
                              in
                                if foo
                                then (foo', (var, value) :: vars)
                                else (foo', (var, subst x y value) :: vars)
                              end)
      in
        if foo
        then SMTlet (rev vars, t)
        else SMTlet (rev vars, subst x y t)
      end
  | subst x y (SMTmatch (t, cases)) =
      let (*val _ = tracing (PolyML.makestring x)
          val _ = tracing (PolyML.makestring y)
          val _ = tracing (PolyML.makestring t)
          val _ = tracing (PolyML.makestring cases)*)
          val cases = map (fn (u, v) => if exists_subterm x u
                                        then (u, v)
                                        else (subst x y u, subst x y v)) cases
      in SMTmatch (subst x y t, cases) end
  | subst x y (SMTas (t, ty)) = SMTas (subst x y t, ty)
  | subst x y (SMTlambda (vars, t)) = 
      if exists (fn SMTty_arg2 (s, _) => x = SMTvar s
                  | _ => raise ERROR "Lambda error") vars
      then SMTlambda (vars, t)
      else SMTlambda (vars, subst x y t)
  | subst _ _ z = z

datatype fun_rec = 
  SMTfun of string * string list * smt_type_argument list * smt_type * smt_term

fun smt_term_fn (Sym n) = SMTvar n
  | smt_term_fn (S (Sym "match" :: x :: xs)) =
    xs |> map smt_term_case
       |> (fn (SMTvar def, t) :: xs => if String.isPrefix "default" def
                                       then xs @ [(SMTvar def, t)]
                                       else (SMTvar def, t) :: xs
          | xs => xs)
       |> pair (smt_term_fn x)
       |> SMTmatch
(*    SMTmatch (smt_term_fn x, map smt_term_case xs)*)
  | smt_term_fn (S [Sym "as", x, typ]) = SMTas (smt_term_fn x, smt_type_fn typ)
  | smt_term_fn (S (Sym "@" :: Sym f :: xs)) =
      SMTapp (SMTvar f, map smt_term_fn xs)
  | smt_term_fn (S [Sym "lambda", S vars, t]) =
      SMTlambda (map smt_type_argument_fn vars, smt_term_fn t)
  | smt_term_fn (S [Sym "let", S ls, t]) =
      SMTlet (map smt_term_let ls, smt_term_fn t)
  | smt_term_fn (S (Sym f :: xs)) =
      SMTapp (SMTvar f, map smt_term_fn xs)
  | smt_term_fn (Num n) = SMTnum n
  | smt_term_fn x = raise ERROR ("Not smt_term expression: " ^ (str_of x)) and
    smt_term_case (S [Sym "case", x, t]) =
      (smt_term_fn x, smt_term_fn t)
  | smt_term_case x = raise ERROR ("Not smt_term_case expression: " ^ (str_of x)) and
    smt_term_let (S [var, t]) = (smt_term_fn var, smt_term_fn t)
  | smt_term_let x = raise ERROR ("Not smt_term_let expression: " ^ (str_of x))

fun fun_rec_fn (S [Sym "define-fun-rec", Sym name, S args, typ, def]) =
  SMTfun (name, [], map smt_type_argument_fn args, smt_type_fn typ, smt_term_fn def)
  | fun_rec_fn (S [Sym "define-fun-rec", S [Sym "par", params, S [Sym name, S args, typ, def]]]) = 
  SMTfun (name, smt_params_fn params, map smt_type_argument_fn args, smt_type_fn typ, smt_term_fn def)
  | fun_rec_fn (S [Sym "define-fun", Sym name, S args, typ, def]) =
  SMTfun (name, [], map smt_type_argument_fn args, smt_type_fn typ, smt_term_fn def)
  | fun_rec_fn (S [Sym "define-fun", S [Sym "par", params, S [Sym name, S args, typ, def]]]) = 
  SMTfun (name, smt_params_fn params, map smt_type_argument_fn args, smt_type_fn typ, smt_term_fn def)
  | fun_rec_fn x = raise ERROR ("Error on function definition: " ^ str_of x)

fun funs_rec_fn (S [Sym "define-funs-rec", S L, S defs]) =
  defs |> map2 (fn S [Sym "par", params, S [Sym name, args, typ]] => (fn def => (S [Sym "define-fun-rec", S [Sym "par", params, S [Sym name, args, typ, def]]]))
                 | S [Sym name, args, typ] => (fn def => (S [Sym "define-fun-rec", Sym name, args, typ, def]))
                 | x => raise ERROR ("Error on one mutual function definition: " ^ str_of x)) L
       |> map fun_rec_fn
  | funs_rec_fn x = raise ERROR ("Error on mutual function definition: " ^ str_of x)

fun dest_smt_type_argument (SMTty_arg2 (v, ty)) = (v,ty)
  | dest_smt_type_argument _ = raise ERROR "not (SMTty_arg2 x) pattern: "

fun fun_rec_eqs (SMTfun (name, params, args, typ, def)) =
  let val args' = map (smt_term_fn o Sym o fst o dest_smt_type_argument) args
      fun eqs s args (SMTmatch (t, L)) =
        if exists (exists_subterm t) args
        then
        maps (fn (exp, t') =>
                  let val args' = map (subst t exp o s) args
                  in eqs (subst t exp o s) args' t' end) L
        else [(args, s (SMTmatch (t, L)))]
        | eqs s args t = [(args, s t)]
  in (name, params, args, typ, eqs I args' def)
  end

fun smt_term_to_isabelle _ (SMTvar n) = map_isabelle_terms n
  | smt_term_to_isabelle _ (SMTnum n) = string_of_int n
  | smt_term_to_isabelle params (SMTapp (SMTvar oop, [a, b])) =
    if exists (fn s => s = oop) isabelle_binary_operators
    then (smt_term_to_isabelle params a ^ " " ^ map_isabelle_terms oop ^ " " ^ smt_term_to_isabelle params b)
          |> enclose "(" ")"
    else map_isabelle_terms oop ^ " " ^ smt_term_to_isabelle params a ^ " " ^ smt_term_to_isabelle params b
          |> enclose "(" ")"
(*  | smt_term_to_isabelle params (SMTapp (SMTvar "let", [a, b, c])) = *)
  | smt_term_to_isabelle params (SMTapp (SMTvar "ite", [a, b, c])) =
    "(if " ^ smt_term_to_isabelle params a ^
    " then " ^ smt_term_to_isabelle params b ^
    " else " ^  smt_term_to_isabelle params c ^ ")"
  | smt_term_to_isabelle params (SMTapp (s, ts)) =
    ts |> map (smt_term_to_isabelle params)
       |> space_implode " "
       |> (fn apps => smt_term_to_isabelle params s ^ " " ^ apps)
       |> enclose "(" ")"
  | smt_term_to_isabelle params (SMTlet (lets, t)) =
    lets |> map (fn (var, v) => "let " ^ smt_term_to_isabelle params var ^ " = " ^
                                         smt_term_to_isabelle params v)
         |> space_implode " in "
         |> prefix "("
         |> (fn lets => lets ^ " in " ^ smt_term_to_isabelle params t ^ ")")
  | smt_term_to_isabelle params (SMTas (x, typ)) =
    smt_term_to_isabelle params x ^ " :: " ^ smt_type_to_isabelle params typ
       |> enclose "(" ")"
  | smt_term_to_isabelle params (SMTlambda (vars, term)) =
    vars |> map (smt_type_argument_to_isabelle2 params)
         |> space_implode " "
         |> (fn vars => "% " ^ vars ^ " . " ^ smt_term_to_isabelle params term)
         |> enclose "(" ")"
  | smt_term_to_isabelle params (SMTmatch (s, ts)) =
    ts |> map (fn (s,t) => smt_term_to_isabelle params s ^ " => " ^
                           smt_term_to_isabelle params t)
       |> space_implode " | "
       |> (fn cases => "case " ^ smt_term_to_isabelle params s ^
                       " of " ^ cases)
       |> enclose "(" ")"

fun fun_rec_strings (name, params, args, typ, eqs) =
  let val fun_type = if null args
                     then smt_type_to_isabelle params typ
                     else
                      args |> map (snd o dest_smt_type_argument)
                           |> map (smt_type_to_isabelle params)
                           |> space_implode " => "
                           |> (fn ty => ty ^ " => " ^ 
                                 smt_type_to_isabelle params typ)
      fun lhs args = smt_term_to_isabelle params (SMTapp (SMTvar name, args))
      fun eq (args, rhs) = lhs args ^ " = " ^ smt_term_to_isabelle params rhs
      val body = if null args
                 then eqs |> map (prefix "[simp]: " o (enclose "\"" "\"") o eq)
                          |> space_implode "|\n"
                 else eqs |> map ((enclose "\"" "\"") o eq)
                          |> space_implode "|\n"
  in ((name ^ " :: \"" ^ fun_type ^ "\"", body), null args) end

fun fun_rec_to_isabelle (name, params, args, typ, eqs) =
  let val ((name_typ, body), null_params) = fun_rec_strings (name, params, args, typ, eqs)
  in if null_params
     then "definition " ^ name_typ ^ " where\n" ^ body
     else "fun " ^ name_typ ^ " where\n" ^ body end

fun funs_rec_to_isabelle Fs =
  let val strings = map fun_rec_strings Fs
      val head = strings |> map (fst o fst)
                         |> space_implode " and "
      val bodies = strings |> map (snd o fst)
                           |> space_implode "|\n"
  in "fun " ^ head ^ " where\n" ^ bodies  end

datatype assert_not =
  SMTassert of (string list * smt_type_argument list * smt_term)

(*
(assert-not
  (forall ((u S) (v S)) (=> (= (linS u) (linS v)) (= u v))))
*)

fun assert_not_fn (S [Sym "assert-not", S [Sym "par", params, S [Sym "forall", S vars, conjecture]]]) =
      SMTassert (smt_params_fn params,  map smt_type_argument_fn vars, smt_term_fn conjecture)
  | assert_not_fn (S [Sym "assert-not", S [Sym "forall", S vars, conjecture]]) =
      SMTassert ([],  map smt_type_argument_fn vars, smt_term_fn conjecture)
  | assert_not_fn x = raise ERROR ("Malformed assert-not: " ^ str_of x)

fun assert_not_to_isabelle prover (SMTassert (params, vars, conjecture)) =
    let val vars = vars |> map (smt_type_argument_to_isabelle2 params)
                        |> space_implode " "
        val conj = smt_term_to_isabelle params conjecture
    in "theorem " ^ "\"" ^ conj ^ "\"\n   " ^ prover end
(*    in "theorem " ^ "\"!! " ^ vars ^ " . " ^ conj ^ "\"\n   " ^ prover end*)

fun s_expression_to_isabelle _ (S (Sym "declare-datatypes" :: xs)) =
      (smt_datatype_to_isabelle o smt_datatype_fn) (S (Sym "declare-datatypes" :: xs))
  | s_expression_to_isabelle _ (S (Sym "define-fun-rec" :: xs)) =
      (fun_rec_to_isabelle o fun_rec_eqs o fun_rec_fn) (S (Sym "define-fun-rec" :: xs))
  | s_expression_to_isabelle _ (S (Sym "define-fun" :: xs)) =
      (fun_rec_to_isabelle o fun_rec_eqs o fun_rec_fn) (S (Sym "define-fun" :: xs))
  | s_expression_to_isabelle _ (S (Sym "define-funs-rec" :: xs)) =
      (funs_rec_to_isabelle o map fun_rec_eqs o funs_rec_fn) (S (Sym "define-funs-rec" :: xs))
  | s_expression_to_isabelle prover (S (Sym "assert-not" :: xs)) =
      (assert_not_to_isabelle prover o assert_not_fn) (S (Sym "assert-not" :: xs))
  | s_expression_to_isabelle _ _ = ""

fun s_expression_to_isabelle' _ (S (Sym "assert-not" :: _)) = ""
  | s_expression_to_isabelle' prover s = s_expression_to_isabelle prover s

fun smt2_to_isabelle ctxt test destiny import prover names smt2_file =
    (let
        val source = File.read (Path.explode smt2_file)
        val expressions = Timeout.apply (Time.fromSeconds 10) (s_expressions ctxt) source
                              handle Timeout.TIMEOUT t => 
                                (tracing ("Timeout processing: " ^ smt2_file); raise Timeout.TIMEOUT t)
        val body = if test
                   then expressions |> map (s_expression_to_isabelle' prover)
                                    |> space_implode "\n\n"
                   else expressions |> map (s_expression_to_isabelle prover)
                                    |> space_implode "\n\n"
        val thy_name = smt2_file |> Utils.extract_filename'
                                 |> singleton (Name.variant_list names)
        val full_content = "theory " ^ thy_name ^ "\n" ^
                           "imports " ^ import ^ "\n" ^
                           "begin\n\n" ^
                           body ^ "\n\n" ^
                           "end"
(*        val _ = tracing full_content*)
        val _ = File.write (Path.explode (destiny ^ "/" ^ thy_name ^ ".thy")) full_content
    in thy_name :: names end) handle PARSE (i, str) => (tracing ("Error on file: " ^ smt2_file); raise (PARSE (i, str)))

fun check_fun str =
  not (String.isSubstring "TOPLEVEL_ERROR raised" str orelse
       String.isSubstring "Could not find lexicographic termination order" str orelse
       String.isSubstring "Function has no arguments" str orelse
       String.isSubstring "Failed to parse term" str orelse
       String.isSubstring "Failed to parse type" str orelse
       String.isSubstring "occurs on right hand side only" str)

fun test_thy thy_file import import_dir prover =
    (" ./proof_call_thy " ^ thy_file ^ " " ^ import ^ " " ^ import_dir ^ " 2>&1")
      |> tap (fn _ => Isabelle_System.bash_output ("sed -i '.bak' \"s/" ^ prover ^ "/oops/g\" " ^ thy_file))
      |> Isabelle_System.bash_output
      |> tap (fn _ => Isabelle_System.bash_output ("sed -i '.bak' \"s/oops/" ^ prover ^ "/g\" " ^ thy_file))
      |> fst
(*      |> tap (fn _ => tracing "SALIDA:")
      |> tap tracing*)
      |> check_fun

(*fun smt2bash_to_isabelle ctxt destiny import prover smt_files =
   ([], smt_files) |> Library.foldl (fn (names, smt2_file) => 
                            let val names' = map snd names
                                val ns = smt2_to_isabelle ctxt true destiny import prover names' smt2_file
                                val name = hd ns
                                val ok = test_thy (destiny ^ "/" ^ name ^ ".thy") import
                                val _ = smt2_to_isabelle ctxt false destiny import prover names' smt2_file
                            in (ok, name) :: names end)
                   |> map2 (fn smt_file => fn thy_file => (smt_file, thy_file)) smt_files*)

fun smt2bash_to_isabelle ctxt destiny import import_dir prover smt_files =
   ([], smt_files) |> Library.foldl (fn (names, smt2_file) => 
                            let val thy_name = smt2_file |> Utils.extract_filename'
                                                         |> singleton (Name.variant_list names)
                            in thy_name :: names end)
                   |> rev
                   |> (fn names => map_index (fn (i,smt_file) => (take i names, smt_file)) smt_files)
                   |> Par_List.map (fn (names, smt_file) =>
                            let val _ = tracing ("Processing file: " ^ smt_file)
                                val ns = smt2_to_isabelle ctxt true destiny import prover names smt_file
                                            handle ERROR x => (tracing ("SMT file: " ^ smt_file); raise (ERROR x))
                                val name = hd ns
                                val ok = test_thy (destiny ^ "/" ^ name ^ ".thy") import import_dir prover
                                val _ = smt2_to_isabelle ctxt false destiny import prover names smt_file
                                            handle ERROR x => (tracing ("SMT file: " ^ smt_file); raise (ERROR x))
                            in (smt_file, (ok, name)) end)

fun get_smt2_files temp_dir dir =
    "find \"" ^ dir ^ "\" -iname '*.smt2'"
      |> Isabelle_System.bash_output
      |> fst
      |> space_explode "\n"
      |> filter (fn "" => false
                | _ => true)
      |> pair ([],[])
      |> Library.foldl (fn ((names,filenames), smt2_file) => 
            if String.isSubstring "'" smt2_file
            then let val smt2_file' = String.translate (fn #"'" => "" | c => String.implode [c]) smt2_file
                     val name = smt2_file' |> Utils.extract_filename'
                                           |> singleton (Name.variant_list names)
                     val new_smt2_file = temp_dir ^ "/" ^ name ^ ".smt2"
                     val _ = Isabelle_System.bash_output ("cp \"" ^ smt2_file ^ "\" \"" ^ new_smt2_file ^ "\"")
                 in (name :: names, new_smt2_file :: filenames) end
            else (names, smt2_file :: filenames))
      |> rev o snd


end

structure SMT_Converter : SMT_CONVERTER = DB_SMT_Converter

