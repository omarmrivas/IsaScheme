(*  Title:      src/enumerated_terms.ML
    ID:         $Id: enumerated_terms.ML,v 1.000 2012/07/19 18:08:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Politecnica de San Luis Potosi
    Copyright   Universidad Politecnica de San Luis Potosi 2012

Enumeration of random terms in beta normal form.
*)

signature ENUMERATED_TERMS =
sig
  type type_context

  val gen_terms          : theory -> int -> int Synchronized.var -> Type.tyenv * int -> typ * type_context -> term list
  val generate_terms     : theory -> typ -> int -> term list
  val generate_terms'    : theory -> typ -> int -> term list
end

structure DB_Enumerated_Terms
(* : ENUMERATED_TERMS *)
= struct

structure ContextSet = Table(
  type key = string * typ
  val ord = prod_ord string_ord Term_Ord.typ_ord)
type type_context = unit ContextSet.table

(*number of atoms and abstractions in a term*)
fun size_of_term tm =
  let
    fun add_size (t $ u) n = add_size t (add_size u n + 1)
      | add_size (Abs (_ ,_, t)) n = add_size t (n + 1)
      | add_size _ n = n + 1;
  in add_size tm 0 end;


fun valid_head_var_type_set thy typ_env A Env =
  let fun check_heads name Result Bis typ =
    (case try (Sign.typ_unify thy (typ, A)) typ_env of
      SOME typ_env => 
      ((let val Bis' = map (Envir.norm_type (fst typ_env)) Bis
            val typ' = Envir.norm_type (fst typ_env) typ
        in check_heads name ((name, Bis', typ', typ_env) :: Result)
                            (Bis @ [domain_type typ]) (range_type typ)
                            handle General.Match => (name, Bis', typ', typ_env) :: Result
        end) handle TYPE _ => check_heads name Result (Bis @ [domain_type typ])
                                                       (range_type typ)
                                    handle General.Match => Result)
     | NONE => check_heads name Result (Bis @ [domain_type typ]) (range_type typ)
                handle General.Match => Result)
  in ContextSet.fold (fn ((name, typ), _) => fn Biss =>
      let val heads = check_heads name [] [] typ
      in heads @ Biss end) Env [] end

fun gen_terms thy size indx typ_env (A, Env) =
    if size < 1 then []
    else
      let
        (* Case 1 *)
        (* L(A;T) ==> x L(B1;T) ... L(Bn;T), if (x:B->A) *)
        fun applications () = 
          Env |> valid_head_var_type_set thy typ_env A
              |> (fn heads => maps (gen_terms_aux thy size indx Env) heads)
        (* Case 2 *)
        (* L(A->B;T) ==> Lam (x:A). L(B;T,(x:A)) *)
        fun abstractions () = 
          case try range_type A of
            SOME B => let val indx_ref = Unsynchronized.ref 0
                          val _ = Synchronized.change indx (fn indx => let val _ = indx_ref := indx
                                                                       in indx + 1 end)
                          val v = "x" ^ string_of_int (!indx_ref)
                          in
                            (B, ContextSet.update ((v, domain_type A), ()) Env)
                              |> gen_terms thy (size - 1) indx typ_env
                              |> map (fn t => Abs (v, domain_type A, t))
                          end
          | NONE => []
        val result = (map (fn f => f ()) [applications, abstractions])
(*        val result = (Par_List.map (fn f => f ()) [applications, abstractions])*)
                       |> flat
(*                       |> filter (fn t => size_of_term t <= size)*)
      in result
      end
and gen_terms_aux thy size indx Env (name, Bis, typ, typ_env) =
    if null Bis then [Free (name, typ)]
    else
      let val args = map (fn Bi => gen_terms thy (size - 1) indx typ_env (Bi, Env)) Bis
(*      let val args = Par_List.map (fn Bi => gen_terms thy (size - 1) indx typ_env (Bi, Env)) Bis*)
          val iterator = Utils.lazy_one_of_each args
          fun valid_args valid = case iterator () of
                                   SOME args => valid_args (args :: valid)
                                 | NONE => valid
      in [] |> valid_args
            |> map (fn args => list_comb (Free (name, Bis ---> typ), args))
      end

fun dummyTvfy t = t |> Term.map_types (map_type_tfree (fn _ => dummyT))
                    |> Term.map_types (map_type_tvar (fn _ => dummyT))

(* maps  (x1,...,xn)t   to   [x1, ..., xn]  *)
fun my_strip_abs_vars (Abs(a,T,t))  =  (a,T) :: my_strip_abs_vars t
  | my_strip_abs_vars (u $ v)  =  my_strip_abs_vars u @ my_strip_abs_vars v
  | my_strip_abs_vars _  =  [] : (string*typ) list

fun normalize_typs thy t =
  let val frees = Term.add_frees t []
      val abs = my_strip_abs_vars t
      val typ_env = Library.foldl (fn (typ_env, (fname, fT)) => 
            Library.foldl (fn (typ_env, (aname, aT)) => 
                if fname = aname
                then Sign.typ_unify thy (fT, aT) typ_env
                else typ_env) (typ_env, abs)) ((Vartab.empty, 0), frees)
      val env = 0 |> Envir.empty 
                  |> (fn Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = _} =>
                         Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = fst typ_env})
  in Envir.norm_term env t
  end

fun normalize_term (Abs (name, T, t)) =
    let val t' = normalize_term t
    in absfree (name, T) t' end
  | normalize_term (p $ q) = (normalize_term p) $ (normalize_term q)
  | normalize_term t = t

fun normalize_names i t =
  case t of
   Abs (_, T, t) => 
      let val (i', t') = normalize_names (i + 1) t
      in (i', Abs ("x" ^ string_of_int i, T, t')) end
  | p $ q => let val (i, p) = normalize_names i p
                 val (i, q) = normalize_names i q
             in (i, p $ q) end
  | t => (i, t)

fun generate_terms thy A size =
  (A, ContextSet.empty)
    |> gen_terms thy size (Synchronized.var "abstraction" 0) (Vartab.empty, 0)
    |> map_filter (try (normalize_typs thy))
    |> map (snd o (normalize_names 0) o normalize_term)
    |> map_filter (try Envir.eta_contract)
    |> map_filter (fn lambda => if can type_of lambda
                                then SOME lambda
                                else NONE)
    |> Utils.make_term_set thy

fun generate_terms' thy A size =
   size |> generate_terms thy A
(*        |> filter (fn t => size_of_term t = size)*)


end

structure Enumerated_Terms : ENUMERATED_TERMS = DB_Enumerated_Terms
