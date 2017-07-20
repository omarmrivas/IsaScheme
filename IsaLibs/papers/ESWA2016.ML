(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature ESWA2016 =
sig

end

structure DB_ESWA2016
(* : CONST_NAMES *)
= struct

fun write_simpset () = 
  let
  val simps = Utils.rules_in_simpset
    [@{term "op +"}, @{term "if x then y else z"}, @{term "[]"},
     @{term "hd"}, @{term "tl"}, @{term "Suc"}, @{term "op #"}, @{term "op -"}]
  val l = length simps
  val content = simps |> map ((Utils.latex_string_of_term @{context}) o (Thm.full_prop_of))
                      |> distinct (op =)
                      |> map single
                      |> map_index (fn (i,e) => string_of_int i :: e)
  val table = Utils.html_table "" (["<b>No.</b>", "<b>Rule</b>"] :: content)
  val begin = HTML.begin_document HTML.no_symbols "Rewrite Rules"
  val ed = HTML.end_document
  val _ = Utils.write_to_file "rewrite_set.html" (begin ^ table ^ ed)
  in () end

  fun extract_filename str =
    (str |> String.explode
        |> rev
        |> find_index (fn c => c = #"/")
        |> (fn i => String.extract (str, String.size str - i, NONE)))
        handle Subscript => (tracing ("Error extracting filename: " ^ str); str)

  fun get_smt2_files dir =
    "find \"" ^ dir ^ "\" -iname '*.smt2'"
      |> Isabelle_System.bash_output
      |> fst
      |> space_explode "\n"

  fun get_thy_files dir =
    "find \"" ^ dir ^ "\" -iname '*.thy'"
      |> Isabelle_System.bash_output
      |> fst
      |> space_explode "\n"

  fun conjecture_proved elapsed str =
    if elapsed >= 80.0 then false
    else if str = "" then false
    else not (String.isSubstring "Failed to finish proof" str orelse
              String.isSubstring "Failed to apply initial proof method" str)

  val timeout = Prover.max_time_in_proof
                      |> Config.get @{context}
                      |> (fn timeout => 3 * timeout)

  val path = Path.explode "experiments/inductive_proofs/errors.log"
  val ps_log = Path.explode "experiments/inductive_proofs/ps_log.log"

  fun get_goal file str =
    str |> first_field "HTML:"
        |> (fn r => case r of
                    SOME (_, str) => str
                  | NONE => "BAD")
        |> first_field "HTML:"
        |> (fn r => case r of
                    SOME (_, str) => str
                  | NONE => "BAD")
        |> String.implode o rev o String.explode
        |> first_field ((String.implode o rev o String.explode) "</span>")
        |> (fn r => case r of
                    SOME (_, str) => (String.implode o rev o String.explode) str ^ "</span>"
                  | NONE => (tracing ("BAD! " ^ file); 
                              Utils.trace_log path ("Unknown error (" ^ file ^ "): " ^ str);
                              "BAD"))

  fun proof_call smt_file thy prover =
  let val start = Timing.start ()
  in
    ("timeout -t " ^ (string_of_int timeout) ^ " ./proof_call " ^ smt_file ^ " " ^ thy ^ " " ^ prover)
      |> Isabelle_System.bash_output
      |> (fn (out, _) => let val elapsed = start |> Timing.result
                                     |> #elapsed
                                     |> Time.toReal
                         in (conjecture_proved elapsed out, elapsed, get_goal out) end)
  end

  fun proof_call_thy smt_file thy prover =
  let val start = Timing.start ()
  in
(*    ("timeout -t " ^ (string_of_int timeout) ^ " ./proof_call_thy " ^ smt_file)*)
    (" ./proof_call_thy " ^ smt_file ^ " " ^ thy)
      |> Isabelle_System.bash_output
      |> (fn (out, _) => let val elapsed = start |> Timing.result
                                             |> #elapsed
                                             |> Time.toReal
                             val file = extract_filename smt_file
                         in (conjecture_proved elapsed out, elapsed, get_goal file out, file) end)
      |> tap (fn (bool, real, _, file) => Utils.trace_log ps_log (file ^ ": " ^ (if bool then "Yes" else "No") ^ " - " ^ string_of_real real))
  end

  val process_ref = Synchronized.var "process_ref" false
  fun clean_processes PID =
  let val ps_command = "ps aux -A | grep poly"
    fun get_time str =
    str |> space_explode ":"
        |> map (fn str => perhaps (try (unsuffix "0")) str)
        |> map (fn str => perhaps (try (unprefix "0")) str)
        |> (fn [min, sec] =>  Time.fromString (string_of_int (Utils.int_of_string min) ^ "." ^ Real.toString (60.0 / the (Real.fromString sec))) 
                                | _ => Time.fromString "0")
        |> the
    fun get_time_safe str =
      (case try get_time str of
        SOME time => time
        | NONE => the (Time.fromString "0"))
    val max_time = get_time "3:30.0"
    val result = ps_command |> Isabelle_System.bash_output
                          |> fst
                          |> space_explode "\n"
                          |> filter (fn line => "" <> line)
                          |> map (filter (fn line => "" <> line) o space_explode " ")
                          |> map (fn lines => nth lines 1)
                          |> map (fn pid_str => (pid_str, fst (Isabelle_System.bash_output ("ps -p " ^ pid_str ^ " -o etime="))))
                          |> map (fn (pid_str, time_str) => (Utils.int_of_string pid_str, get_time_safe time_str))
(*                          |> map (fn lines => (Utils.int_of_string (nth lines 1), get_time_safe (nth lines 9)))*)
                          |> filter (fn (pid, time) => time > max_time andalso PID <> pid)
                          |> tap (map (Utils.trace_log ps_log o (fn pid => "Killing PID: " ^ pid) o string_of_int o fst))
  in map (fn (pid, _) =>  Isabelle_System.bash_output ("kill -KILL " ^ string_of_int pid)) result end
  fun clean_loop PID () =
  if not (Synchronized.value process_ref)
  then
  let 
      val _ = clean_processes PID
      val _ = OS.Process.sleep (seconds 5.0)
  in clean_loop PID () end
  else ()

fun doit () = 
  let
(*  val smt_files = "/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks"
                    |> get_smt2_files*)
  val smt_files = "/Users/omarmrivas/Programs/IsaLibs/experiments/inductive_proofs"
                    |> get_thy_files
(*                    |> single o hd*)
  val _ = tracing ("Problems: " ^ (string_of_int o length) smt_files)
  val thy = "IsaLibs"
  val prover = "induct_auto_dep_first"
  fun check foo = if foo then "&#x2713;" else "&#x2717;"
  val params = ({name="clener", stack_limit=NONE, interrupts=false} : Standard_Thread.params)
  val PID = 27820
  val thread = Standard_Thread.fork params (clean_loop PID)
  val _ = tracing ("Is active: " ^ (if Thread.isActive thread then "yes" else "no"))
  val results = smt_files |> map_index I
                          |> Par_List.map (fn (i, file) => (Utils.trace_log ps_log (string_of_int i ^ ": " ^ file); (i, proof_call_thy file thy prover)))
                          |> map_filter (fn (i, (x, y, goal, z)) => if goal = "BAD" then NONE else SOME (i, (x, y, goal, z)))
                          |> map (fn (i, (proved, time, conjecture, file)) => [string_of_int i, conjecture, file, check proved, if time > 60.0 then "60.0" else string_of_real time])
  val theorems_proved = Library.foldl (fn (c, [_, _, _, proved, _]) => if "&#x2713;" = proved then c + 1 else c | (c,_) => c) (0, results)
  val theorems_not_proved = length results - theorems_proved
  val theorems_proved_percent = ((Real.fromInt) theorems_proved) / ((Real.fromInt o length) results) * 100.0
  val theorems_not_proved_percent = ((Real.fromInt) theorems_not_proved) / ((Real.fromInt o length) results) * 100.0
  val average_cpu_time = (0.0, results) |> Library.foldl (fn (time, [_, _, _, _, t]) => time + (the o Real.fromString) t | (time,_) => time)
                                        |> (fn v => v / ((Real.fromInt o length) results))
  val average_cpu_time_proved = ((0,0.0), results) |> Library.foldl (fn ((c,time), [_, _, _, proved, t]) => if "&#x2713;" = proved 
                                                                                                            then (c+1,time + (the o Real.fromString) t)
                                                                                                            else (c,time) | ((c,time), _) => (c,time))
                                                   |> (fn (c,time) => time / ((Real.fromInt) c))
  val average_cpu_time_not_proved = ((0,0.0), results) |> Library.foldl (fn ((c,time), [_, _, _, proved, t]) => if "&#x2717;" = proved 
                                                                                                            then (c+1,time + (the o Real.fromString) t)
                                                                                                            else (c,time) | ((c,time), _) => (c,time))
                                                       |> (fn (c,time) => time / ((Real.fromInt) c))
  val table = Utils.html_table "alldata" (["<b>No.</b>", "<b>Conjecture</b>", "<b>File</b>", "<b>Proved</b>", "<b>Time</b>"] :: results)
  val header_content = [["<b>Proved</b>", "<b>Not proved</b>", "<b>Proved &#37;</b>", "<b>Not proved &#37;</b>", "<b>Avg cpu time</b>", "<b>Avg proved</b>", "<b>Avg not proved</b>"],
                        [string_of_int theorems_proved, 
                         string_of_int theorems_not_proved, 
                         string_of_real theorems_proved_percent ^ "&#37;", 
                         string_of_real theorems_not_proved_percent ^ "&#37;", 
                         string_of_real average_cpu_time ^ "s", 
                         string_of_real average_cpu_time_proved ^ "s", 
                         string_of_real average_cpu_time_not_proved ^ "s"]]
  val table_header = Utils.html_table "statistics" header_content
  val begin = HTML.begin_document HTML.no_symbols ("Results for " ^ prover)
  val ed = HTML.end_document
  val _ = Utils.write_to_file ("experiments/inductive_proofs/Isabelle2016/" ^ prover ^ ".html") (begin ^ table_header ^ table ^ ed)
  val _ = OS.Process.sleep (seconds 6.0)
  val _ = Synchronized.change process_ref (fn _ => true)
  val _ = Standard_Thread.join thread
  in () end

end

structure ESWA_2016 : ESWA2016 = DB_ESWA2016

