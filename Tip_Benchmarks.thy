theory Tip_Benchmarks 
imports IsaLibs
begin
  
ML {*
  val smt2_dir = "/Users/omarmrivas/Programs/benchmarks"
  val destiny = "experiments/inductive_proofs"
  val smt2_files = smt2_dir |> SMT_Converter.get_smt2_files destiny
                            |> filter (fn "" => false
                                      | _ => true)
(*  val smt2_files = ["/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/isaplanner/prop_41.smt2"]*)
(*  val smt2_files = ["/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/list_Interleave.smt2"]*)
(*  val smt2_files = ["/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortIsSort.smt2"]*)
  val names = SMT_Converter.smt2bash_to_isabelle @{context} destiny "IsaLibs" "../../IsaLibs" "by inductive_provers" smt2_files
*}
  
ML {*
  val path_t = Path.explode "Tip_Benchmarks_Log.lol"
  val res = map (fn (smt2, (foo, thy)) => 
        if not foo then NONE
        else let val thy_file = destiny ^ "/" ^ thy ^ ".thy"
                 val _ = tracing ("Processing " ^ thy_file)
                 val _ = Utils.trace_log path_t ("Processing " ^ thy_file)
                 val command = " ./isabelle_build " ^ thy_file ^ " IsaLibs ../../../IsaLibs/IsaLibs 2>&1"
                 val (output, _) = Isabelle_System.bash_output command
                 val _ = Utils.trace_log path_t output
             in SOME (smt2, (output, thy)) end) names
*}
  
  
ML {*
  res |> map_filter I
      |> (fst o snd o hd)
      |> tracing
(*  |> map_filter (fn (_, (out, thy)) =>
    if String.isSubstring "Latex Simpset:" out
    then SOME thy
    else NONE)*)
*}
  
  
(* tests *)  
  
  