(*  Title:      papers/abc-theory-repair/abc.ML
    Author:     Omar Montano Rivas

An extension of IsaScheme with the fault diagnosis and the repair operations of
the ABC system (A. Bundy, "The ABC System for Repairing Faulty Logical
Theories", section 5).

A theory is a list of Horn clauses written in Isabelle's syntax. Unlike Datalog,
terms may contain function symbols, so proofs by selected literal resolution
are searched up to a depth limit, as section 8 of the chapter suggests for
richer logics. A preferred structure is a true set and a false set of atoms.
An incompatibility is an atom of the false set that is a theorem, and an
insufficiency is an atom of the true set that is not. Incompatibilities are
repaired by blocking a step of a proof and insufficiencies by unblocking a
failed step, with the operations of Definitions 5.2 and 5.3.
*)

signature ABC =
sig
  datatype fterm = V of indexname | F of string * fterm list
  type clause = {body : fterm list, head : fterm option}
  type preferred = {true_set : fterm list, false_set : fterm list}
  type step = {goal : fterm, origin : (int * int) option, clause : int}
  type dead_end = {goal : fterm, origin : (int * int) option}
  datatype fault = Incompatibility of fterm * step list list
                 | Insufficiency of fterm * dead_end list
  type repair = {name : string, detail : string, theory : clause list}

  val max_depth : int Config.T
  val max_proofs : int Config.T
  val max_repairs : int Config.T
  val max_solutions : int Config.T

  val read_clause : Proof.context -> string -> clause
  val read_atom : Proof.context -> string -> fterm
  val string_of_fterm : fterm -> string
  val string_of_clause : clause -> string

  val prove : Proof.context -> clause list -> fterm -> step list list * dead_end list
  val faults : Proof.context -> clause list -> preferred -> fault list
  val repairs : Proof.context -> clause list -> fault -> repair list
  val search_levels : Proof.context -> clause list -> preferred -> (int * (repair list * clause list) list) list
  val search : Proof.context -> clause list -> preferred -> (int * (repair list * clause list) list) option

  val faults_report : Proof.context -> clause list -> preferred -> string
  val repair_report : Proof.context -> clause list -> preferred -> string
end

structure ABC : ABC =
struct

(** Terms, atoms and clauses **)

(* variables are V (name, index); constants are function symbols without arguments *)
datatype fterm = V of indexname | F of string * fterm list

type clause = {body : fterm list, head : fterm option}
type preferred = {true_set : fterm list, false_set : fterm list}

val eq_sym = "="
val neq_sym = "\<noteq>"

val max_depth = Attrib.setup_config_int @{binding abc_max_depth} (K 30)
val max_proofs = Attrib.setup_config_int @{binding abc_max_proofs} (K 5)
val max_repairs = Attrib.setup_config_int @{binding abc_max_repairs} (K 2)
val max_solutions = Attrib.setup_config_int @{binding abc_max_solutions} (K 10)

fun ground (V _) = false
  | ground (F (_, ts)) = forall ground ts

fun add_symbols (V _) = I
  | add_symbols (F (f, ts)) = insert (op =) f #> fold add_symbols ts

fun add_vars (V v) = insert (op =) v
  | add_vars (F (_, ts)) = fold add_vars ts

fun clause_atoms ({body, head} : clause) = body @ the_list head

fun theory_symbols T = fold (fold add_symbols o clause_atoms) T []

fun clause_vars c = fold add_vars (clause_atoms c) []

fun map_clause f ({body, head} : clause) = {body = map f body, head = Option.map f head}


(** Reading clauses written in Isabelle's syntax **)

(* The text is parsed but not type-checked, so that the names of the chapter
   (sum, add, ...) do not clash with the constants of HOL.  Following ABC,
   undeclared names that start with an upper-case letter are variables and the
   other ones are constants. *)

fun strip_constraints (Const ("_type_constraint_", _) $ t) = strip_constraints t
  | strip_constraints (t $ u) = strip_constraints t $ strip_constraints u
  | strip_constraints (Abs (x, T, t)) = Abs (x, T, strip_constraints t)
  | strip_constraints t = t

fun dest_num (Const ("Num.num.One", _)) = 1
  | dest_num (Const ("Num.num.Bit0", _) $ n) = 2 * dest_num n
  | dest_num (Const ("Num.num.Bit1", _) $ n) = 2 * dest_num n + 1
  | dest_num t = raise TERM ("ABC: bad numeral", [t])

fun is_upper_name x = x <> "" andalso Char.isUpper (String.sub (x, 0))

fun fterm_of (Const ("HOL.eq", _) $ a $ b) = F (eq_sym, [fterm_of a, fterm_of b])
  | fterm_of (Const ("HOL.not_equal", _) $ a $ b) = F (neq_sym, [fterm_of a, fterm_of b])
  | fterm_of (Const ("HOL.Not", _) $ (Const ("HOL.eq", _) $ a $ b)) =
      F (neq_sym, [fterm_of a, fterm_of b])
  | fterm_of (Const ("Groups.zero_class.zero", _)) = F ("0", [])
  | fterm_of (Const ("Groups.one_class.one", _)) = F ("1", [])
  | fterm_of (Const ("Num.numeral_class.numeral", _) $ n) = F (string_of_int (dest_num n), [])
  | fterm_of t =
      (case strip_comb t of
         (Const (c, _), args) => F (Long_Name.base_name c, map fterm_of args)
       | (Free (x, _), []) => if is_upper_name x then V (x, 0) else F (x, [])
       | (Free (x, _), args) => F (x, map fterm_of args)
       | _ => raise TERM ("ABC: unsupported term", [t]))

fun dest_conjs (Const ("HOL.conj", _) $ a $ b) = dest_conjs a @ dest_conjs b
  | dest_conjs t = [t]

fun dest_trueprop (Const ("HOL.Trueprop", _) $ t) = t
  | dest_trueprop t = t

fun clause_of_term t =
  let val t = strip_constraints t
      val prems = Logic.strip_imp_prems t |> map dest_trueprop |> maps dest_conjs
      val concl = dest_trueprop (Logic.strip_imp_concl t)
      val (prems, concl) =
        case concl of
          Const ("HOL.implies", _) $ a $ b => (prems @ dest_conjs a, b)
        | _ => (prems, concl)
      val head = case concl of Const ("HOL.False", _) => NONE | _ => SOME (fterm_of concl)
  in {body = map fterm_of prems, head = head} end

fun read_clause ctxt s = clause_of_term (Syntax.parse_prop ctxt s)

fun read_atom ctxt s =
  case read_clause ctxt s of
    {body = [], head = SOME a} => a
  | _ => error ("ABC: expected an atom, not " ^ quote s)


(** Printing, in the notation of the chapter **)

fun list_elems (F ("Cons", [x, xs])) = Option.map (cons x) (list_elems xs)
  | list_elems (F ("Nil", [])) = SOME []
  | list_elems _ = NONE

fun string_of_fterm (V (x, 0)) = x
  | string_of_fterm (V (x, i)) = x ^ "_" ^ string_of_int i
  | string_of_fterm (t as F (f, args)) =
      (case list_elems t of
         SOME ts => "[" ^ commas (map string_of_fterm ts) ^ "]"
       | NONE =>
           if (f = eq_sym orelse f = neq_sym) andalso length args = 2
           then string_of_fterm (nth args 0) ^ " " ^ f ^ " " ^ string_of_fterm (nth args 1)
           else if null args then f
           else f ^ "(" ^ commas (map string_of_fterm args) ^ ")")

fun string_of_clause ({body, head} : clause) =
  let val b = space_implode " \<and> " (map string_of_fterm body)
  in case (body, head) of
       ([], SOME h) => "\<Longrightarrow> " ^ string_of_fterm h
     | (_, SOME h) => b ^ " \<Longrightarrow> " ^ string_of_fterm h
     | (_, NONE) => b ^ " \<Longrightarrow>"
  end


(** Unification **)

fun walk s (V v) = (case Vartab.lookup s v of SOME t => walk s t | NONE => V v)
  | walk _ t = t

fun occurs s v t =
  case walk s t of
    V w => v = w
  | F (_, ts) => exists (occurs s v) ts

fun unify (t, u) s =
  case (walk s t, walk s u) of
    (V v, V w) => if v = w then SOME s else SOME (Vartab.update (v, V w) s)
  | (V v, u') => if occurs s v u' then NONE else SOME (Vartab.update (v, u') s)
  | (t', V w) => if occurs s w t' then NONE else SOME (Vartab.update (w, t') s)
  | (F (f, ts), F (g, us)) =>
      if f = g andalso length ts = length us then unify_list (ts, us) s else NONE
and unify_list ([], []) s = SOME s
  | unify_list (t :: ts, u :: us) s =
      (case unify (t, u) s of SOME s' => unify_list (ts, us) s' | NONE => NONE)
  | unify_list _ _ = NONE

fun unifiable t u = is_some (unify (t, u) Vartab.empty)

fun subst_term s t =
  case walk s t of
    V v => V v
  | F (f, ts) => F (f, map (subst_term s) ts)

fun rename n (V (x, _)) = V (x, n)
  | rename n (F (f, ts)) = F (f, map (rename n) ts)


(** Selected literal resolution **)

(* origin: the clause and the position in its body of the atom that created a
   goal, NONE for the conjecture itself *)
type step = {goal : fterm, origin : (int * int) option, clause : int}
type dead_end = {goal : fterm, origin : (int * int) option}

(* the clause ~1 stands for the built-in equality and disequality: t = t, and
   c \<noteq> d for distinct ground terms (closed world assumption) *)
fun prove ctxt (T : clause list) atom =
  let val depth_limit = Config.get ctxt max_depth
      val proof_limit = Config.get ctxt max_proofs
      val proofs = Unsynchronized.ref ([] : step list list)
      val dead_ends = Unsynchronized.ref ([] : dead_end list)
      val counter = Unsynchronized.ref 0
      fun fresh () = (counter := !counter + 1; !counter)
      fun enough () = length (!proofs) >= proof_limit
      fun search [] _ steps _ = proofs := rev steps :: !proofs
        | search (({atom, origin} : {atom : fterm, origin : (int * int) option}) :: rest) s steps depth =
            if enough () orelse depth >= depth_limit then ()
            else
              let val a = subst_term s atom
                  val step = {goal = a, origin = origin, clause = ~1}
                  val builtin =
                    case a of
                      F (f, [x, y]) =>
                        if f = eq_sym then
                          (case unify (x, y) s of
                             SOME s' => (search rest s' (step :: steps) (depth + 1); true)
                           | NONE => false)
                        else if f = neq_sym then
                          let val x' = subst_term s x
                              val y' = subst_term s y
                          in if ground x' andalso ground y' andalso x' <> y'
                             then (search rest s (step :: steps) (depth + 1); true)
                             else false
                          end
                        else false
                    | _ => false
                  fun try_clause (k, {body, head = SOME h}) found =
                        if enough () then found
                        else
                          let val n = fresh ()
                          in case unify (a, rename n h) s of
                               SOME s' =>
                                 let val goals = map_index (fn (j, b) =>
                                       {atom = rename n b, origin = SOME (k, j)}) body
                                 in search (goals @ rest) s'
                                      ({goal = a, origin = origin, clause = k} :: steps) (depth + 1);
                                    true
                                 end
                             | NONE => found
                          end
                    | try_clause _ found = found
                  val found = fold try_clause (map_index I T) builtin
              in if found then () else dead_ends := {goal = a, origin = origin} :: !dead_ends end
  in search [{atom = atom, origin = NONE}] Vartab.empty [] 0;
     (rev (!proofs), rev (!dead_ends))
  end


(** Faults (Definition 5.1) **)

datatype fault = Incompatibility of fterm * step list list
               | Insufficiency of fterm * dead_end list

fun faults ctxt T ({true_set, false_set} : preferred) =
  let fun insufficiency a =
        case prove ctxt T a of
          ([], dead_ends) => SOME (Insufficiency (a, dead_ends))
        | _ => NONE
      fun incompatibility a =
        case prove ctxt T a of
          ([], _) => NONE
        | (proofs, _) => SOME (Incompatibility (a, proofs))
  in map_filter insufficiency true_set @ map_filter incompatibility false_set end


(** Repair operations (Definitions 5.2 and 5.3) **)

type repair = {name : string, detail : string, theory : clause list}

fun fresh_symbol used base =
  let fun try s = if member (op =) used s then try (s ^ "'") else s
  in try (base ^ "'") end

fun fresh_dummies used n =
  let fun go _ 0 acc = rev acc
        | go i k acc =
            let val s = "dum" ^ string_of_int i
            in if member (op =) used s orelse member (op =) acc s then go (i + 1) k acc
               else go (i + 1) (k - 1) (s :: acc)
            end
  in go 1 n [] end

fun fresh_var c base =
  let val used = map fst (clause_vars c)
      fun try i = let val x = base ^ (if i = 0 then "" else string_of_int i)
                  in if member (op =) used x then try (i + 1) else x end
  in V (try 0, 0) end

fun pred_of (F (p, args)) = SOME (p, length args)
  | pred_of _ = NONE

fun same_pred p n (F (q, args)) = p = q andalso length args = n
  | same_pred _ _ _ = false

fun builtin_pred p = p = eq_sym orelse p = neq_sym

fun replace_nth i x xs = map_index (fn (j, y) => if i = j then x else y) xs

fun remove_nth i xs = map_index I xs |> filter (fn (j, _) => j <> i) |> map snd

fun rename_symbol _ _ (V v) = V v
  | rename_symbol old new (F (f, ts)) =
      F (if f = old then new else f, map (rename_symbol old new) ts)

(* variables of a dead-end goal become ordinary clause variables *)
fun generalize t =
  case t of
    V (x, 0) => V (x, 0)
  | V (x, i) => V (x ^ string_of_int i, 0)
  | F (f, ts) => F (f, map generalize ts)

fun pretty_clause T k = string_of_clause (nth T k)

(* Belief Revision 1-2 and Reformation 1-3, for a proof step whose goal
   P(s1,...,sn) resolves with the head P(t1,...,tn) of clause k *)
fun incompatibility_repairs T ({goal, origin, clause = k} : step) =
  if k < 0 then []
  else
    let val c = nth T k
        val used = theory_symbols T
        val clause_str = string_of_clause c
        val head = the (#head c)
        val (p, n) = the (pred_of head)
        val (_, ss) = case goal of F x => x | V _ => ("", [])
        val (_, ts) = case head of F x => x | V _ => ("", [])
        val br1 = {name = "Belief Revision 1", detail = "delete " ^ clause_str,
                   theory = nth_drop k T}
        val dum = hd (fresh_dummies used 1)
        val pre = F (dum, map V (fold add_vars [head] []))
        val br2 = {name = "Belief Revision 2",
                   detail = "add the unprovable precondition " ^ string_of_fterm pre ^
                            " to " ^ clause_str,
                   theory = nth_map k (fn {body, head} => {body = body @ [pre], head = head}) T}
        val p' = fresh_symbol used p
        val ref1 = {name = "Reformation 1",
                    detail = "rename " ^ p ^ " to " ^ p' ^ " in " ^ clause_str,
                    theory = nth_map k (fn {body, head} =>
                               {body = body, head = Option.map (fn F (_, args) => F (p', args)
                                                                 | t => t) head}) T}
        (* Reformation 2: every occurrence of P gets a new argument.  The
           targeted head and the atom that created the goal get distinct new
           constants, other facts get distinct new constants too, and the
           other clauses get a new variable shared by their occurrences of P. *)
        val ref2 =
          let val occurrences = T |> map (fn c => length (filter (same_pred p n) (clause_atoms c)))
              val needed = fold (fn x => fn acc => x + acc) occurrences 0 + 1
              val dums = fresh_dummies used needed
              val counter = Unsynchronized.ref 0
              fun next () = (counter := !counter + 1; F (nth dums (!counter - 1), []))
              val src_clause = case origin of SOME (i, _) => i | NONE => ~1
              fun extend arg t = case t of F (q, args) => F (q, args @ [arg]) | V _ => t
              fun change i (c as {body, head}) =
                if i = k then
                  {body = map (fn b => if same_pred p n b then extend (fresh_var c "Dum") b else b) body,
                   head = Option.map (fn h => if same_pred p n h then extend (next ()) h else h) head}
                else if i = src_clause then
                  let val others = length (filter (same_pred p n) (clause_atoms c)) > 1
                      val shared = if others then fresh_var c "Dum" else next ()
                  in {body = map (fn b => if same_pred p n b then extend shared b else b) body,
                      head = Option.map (fn h => if same_pred p n h then extend shared h else h) head}
                  end
                else if null (clause_vars c) then map_clause (fn a => if same_pred p n a then extend (next ()) a else a) c
                else let val v = fresh_var c "Dum"
                     in map_clause (fn a => if same_pred p n a then extend v a else a) c end
          in {name = "Reformation 2",
              detail = "increase the arity of " ^ p ^ " by one, blocking " ^ string_of_fterm goal ^
                       " against " ^ clause_str,
              theory = map_index (fn (i, c) => change i c) T}
          end
        val ref3 =
          map_index I (ss ~~ ts)
          |> map_filter (fn (i, (s, t)) =>
               case (s, t) of
                 (F (cs, []), F (ct, [])) =>
                   if cs = ct then
                     let val c' = fresh_symbol used ct
                     in SOME {name = "Reformation 3",
                              detail = "change " ^ ct ^ " to " ^ c' ^ " in " ^ clause_str,
                              theory = nth_map k (fn {body, head} =>
                                         {body = body,
                                          head = Option.map (fn F (q, args) =>
                                                   F (q, replace_nth i (F (c', [])) args) | h => h) head}) T}
                     end
                   else NONE
               | _ => NONE)
    in [br1, br2] @ (if builtin_pred p then [] else [ref1, ref2]) @ ref3 end

(* Abduction 1-2 and Reformation 4-6, for a goal P(s1,...,sm) that no clause
   head unifies with *)
fun insufficiency_repairs T ({goal, origin} : dead_end) =
  let val goal_str = string_of_fterm goal
      val (p, ss) = case goal of F x => x | V _ => ("", [])
      val m = length ss
      val abd1 = {name = "Abduction 1", detail = "add \<Longrightarrow> " ^ string_of_fterm (generalize goal),
                  theory = T @ [{body = [], head = SOME (generalize goal)}]}
      val abd2 =
        case origin of
          SOME (k, j) =>
            [{name = "Abduction 2",
              detail = "delete " ^ string_of_fterm (nth (#body (nth T k)) j) ^ " from " ^ pretty_clause T k,
              theory = nth_map k (fn {body, head} => {body = nth_drop j body, head = head}) T}]
        | NONE => []
      (* near misses: heads with the same predicate that fail on some
         arguments (only those with the fewest failing arguments), and heads
         with another predicate whose arguments unify *)
      val heads = map_index I T |> map_filter (fn (k, c) =>
                    case #head c of SOME (F (q, ts)) => SOME (k, q, ts) | _ => NONE)
      val same = heads |> filter (fn (_, q, ts) => q = p andalso length ts = m)
                       |> map (fn (k, q, ts) =>
                            (k, ts, map_index I (ss ~~ ts)
                                    |> filter (fn (_, (s, t)) => not (unifiable s t))
                                    |> map fst))
                       |> filter (fn (_, _, bad) => not (null bad))
      val fewest = fold (fn (_, _, bad) => fn n => Int.min (n, length bad)) same 1000
      val nearest = filter (fn (_, _, bad) => length bad = fewest) same
      val ref5 =
        (if builtin_pred p then [] else nearest) |> maps (fn (_, _, bad) => bad) |> distinct (op =)
        |> map (fn i =>
             let fun drop_atom (a as F (q, args)) =
                       if q = p andalso length args = m then F (q, remove_nth i args) else a
                   | drop_atom a = a
             in {name = "Reformation 5",
                 detail = "remove argument " ^ string_of_int (i + 1) ^ " of " ^ p ^
                          " (" ^ goal_str ^ " fails against it)",
                 theory = map (map_clause drop_atom) T}
             end)
      val ref6 =
        nearest |> maps (fn (k, ts, bad) =>
          bad |> maps (fn i =>
            case (nth ss i, nth ts i) of
              (F (c, []), F (c', [])) =>
                [{name = "Reformation 6",
                  detail = "rename " ^ c' ^ " to " ^ c ^ " in all axioms",
                  theory = map (map_clause (rename_symbol c' c)) T},
                 {name = "Reformation 6",
                  detail = "replace " ^ c' ^ " by a new variable in " ^ pretty_clause T k,
                  theory = nth_map k (fn cl as {body, head} =>
                             {body = body,
                              head = Option.map (fn F (q, args) =>
                                       F (q, replace_nth i (fresh_var cl "V") args) | h => h) head}) T}]
            | _ => []))
      val other = heads |> filter (fn (_, q, ts) => q <> p andalso length ts = m andalso
                                                   not (builtin_pred p) andalso not (builtin_pred q) andalso
                                                   is_some (unify_list (ss, ts) Vartab.empty))
      val ref4 =
        other |> maps (fn (k, q, _) =>
          [{name = "Reformation 4",
            detail = "replace " ^ q ^ " by " ^ p ^ " in " ^ pretty_clause T k,
            theory = nth_map k (fn {body, head} =>
                       {body = body, head = Option.map (fn F (_, args) => F (p, args) | h => h) head}) T},
           {name = "Reformation 4",
            detail = "merge " ^ p ^ " into " ^ q ^ " in all axioms",
            theory = map (map_clause (rename_symbol p q)) T}])
  in [abd1] @ abd2 @ ref4 @ ref5 @ ref6 end

fun repairs _ T (Incompatibility (_, proofs)) =
      (case proofs of
         proof :: _ => maps (incompatibility_repairs T) proof
       | [] => [])
  | repairs _ T (Insufficiency (_, dead_ends)) =
      dead_ends
      |> distinct (fn (d1 : dead_end, d2) => #goal d1 = #goal d2 andalso #origin d1 = #origin d2)
      |> take 10
      |> maps (insufficiency_repairs T)


(** Search for repairs, breadth first.  The result lists, for each number of
    operations up to abc_max_repairs, the fault-free theories found with that
    many operations; a fault-free theory is not repaired further. **)

fun theory_key T = cat_lines (map string_of_clause T)

fun search_levels ctxt T ps =
  let val limit = Config.get ctxt max_repairs
      fun level n frontier seen found =
        if n > limit orelse null frontier then rev found
        else
          let val (children, seen') =
                fold (fn (T, ops) => fn (acc, seen) =>
                        case faults ctxt T ps of
                          [] => (acc, seen)
                        | fault :: _ =>
                            fold (fn (r : repair) => fn (acc, seen) =>
                                    let val key = theory_key (#theory r)
                                    in if Symtab.defined seen key then (acc, seen)
                                       else ((#theory r, ops @ [r]) :: acc, Symtab.update (key, ()) seen)
                                    end) (repairs ctxt T fault) (acc, seen))
                     frontier ([], seen)
              val (solutions, rest) =
                List.partition (fn (T, _) => null (faults ctxt T ps)) (rev children)
              val found = if null solutions then found
                          else (n, map (fn (T, ops) => (ops, T)) solutions) :: found
          in level (n + 1) rest seen' found end
  in level 1 [(T, [])] (Symtab.make [(theory_key T, ())]) [] end


(* the first level with fault-free theories; SOME (0, []) if T has no faults *)
fun search ctxt T ps =
  if null (faults ctxt T ps) then SOME (0, [])
  else case search_levels ctxt T ps of
         [] => NONE
       | levels => SOME (hd levels)


(** Reports **)

fun indent n s = implode (replicate n " ") ^ s

fun string_of_step T ({goal, clause, ...} : step) =
  string_of_fterm goal ^ "  by  " ^
    (if clause < 0 then "the built-in " ^ (case goal of F (f, _) => f | _ => "") else string_of_clause (nth T clause))

fun string_of_fault T (Incompatibility (a, proofs)) =
      [indent 2 ("Incompatibility: " ^ string_of_fterm a ^ " is in the false set but is a theorem."),
       indent 4 "Proof:"] @ map (indent 6 o string_of_step T) (hd proofs) @
      (if length proofs > 1 then [indent 4 ("(" ^ string_of_int (length proofs) ^ " proofs found)")] else [])
  | string_of_fault _ (Insufficiency (a, dead_ends)) =
      [indent 2 ("Insufficiency: " ^ string_of_fterm a ^ " is in the true set but is not a theorem."),
       indent 4 ("Failed goals: " ^ commas (distinct (op =) (map (string_of_fterm o #goal) dead_ends)))]

fun faults_report ctxt T ps =
  case faults ctxt T ps of
    [] => "The theory has no faults."
  | fs => cat_lines ("Faults:" :: maps (string_of_fault T) fs)

(* the clauses deleted (-) and added (+) by a repair, rules before facts *)
fun diff T T' =
  let fun strings T = map (fn c => (null (#body c), string_of_clause c)) T
      val old = strings T
      val new = strings T'
      val removed = filter_out (fn (_, c) => exists (fn (_, c') => c = c') new) old
      val added = filter_out (fn (_, c) => exists (fn (_, c') => c = c') old) new
      fun rules xs = filter_out fst xs
      fun facts xs = filter fst xs
      val lines = map (fn (_, c) => "- " ^ c) (rules removed) @ map (fn (_, c) => "+ " ^ c) (rules added) @
                  map (fn (_, c) => "- " ^ c) (facts removed) @ map (fn (_, c) => "+ " ^ c) (facts added)
      val shown = take 6 lines
  in shown @ (if length lines > 6 then ["... (" ^ string_of_int (length lines - 6) ^ " more changes)"] else []) end

fun repair_report ctxt T ps =
  let val faults_text = faults_report ctxt T ps
      fun group (n, solutions) =
        let val shown = take (Config.get ctxt max_solutions) solutions
            val header = string_of_int (length solutions) ^ " fault-free theories with " ^
                         string_of_int n ^ (if n = 1 then " operation" else " operations") ^
                         (if length shown < length solutions
                          then ", showing " ^ string_of_int (length shown) ^ ":" else ":")
        in "" :: header ::
           flat (map_index (fn (i, (ops, T')) =>
             indent 2 (string_of_int (i + 1) ^ ".") ::
             map (fn (r : repair) => indent 5 (#name r ^ ": " ^ #detail r)) ops @
             map (indent 7) (diff T T')) shown)
        end
      val result =
        if null (faults ctxt T ps) then []
        else case search_levels ctxt T ps of
               [] => ["", "No repair found with at most " ^ string_of_int (Config.get ctxt max_repairs) ^
                      " operations (option abc_max_repairs)."]
             | levels => maps group levels
  in cat_lines (faults_text :: result) end


(** Isar commands **)

val parse_spec =
  (Parse.$$$ "axioms" |-- Scan.repeat1 Parse.term) --
  Scan.optional (Parse.$$$ "true" |-- Scan.repeat1 Parse.term) [] --
  Scan.optional (Parse.$$$ "false" |-- Scan.repeat1 Parse.term) []

fun read_spec ctxt ((axioms, trues), falses) =
  (map (read_clause ctxt) axioms,
   {true_set = map (read_atom ctxt) trues, false_set = map (read_atom ctxt) falses})

fun command keyword comment report =
  Outer_Syntax.command keyword comment
    (parse_spec >> (fn spec => Toplevel.keep (fn st =>
      let val ctxt = Toplevel.context_of st
          val (T, ps) = read_spec ctxt spec
      in writeln (report ctxt T ps) end)))

val _ = command @{command_keyword abc_faults}
          "diagnose the faults of a Horn theory with respect to a preferred structure (ABC)"
          faults_report

val _ = command @{command_keyword abc_repair}
          "repair a faulty Horn theory with the operations of ABC"
          repair_report

end
