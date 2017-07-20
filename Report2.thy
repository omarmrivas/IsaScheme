theory Report2
imports "IsaLibs/IsaLibs"
begin

ML {*
(*  val nitpick_params = Nitpick_Commands.default_params @{theory} []
  val conjecture = @{prop "\<not>(x = 0) \<Longrightarrow> \<not>(x = 1)\<Longrightarrow>P (x::nat)"}
  val state = @{context}
       |> Proof.theorem NONE (K I) [[(conjecture, [])]]
  val r = Nitpick.pick_nits_in_subgoal state nitpick_params Nitpick.Normal 1 0
  val rr = Quickcheck.quickcheck [] 1 state*)
  val v = Quickcheck.active_testers @{context}
  val h = hd v
  val hh = h
*}

lemma "\<not>(x = 0) \<Longrightarrow> \<not>(x = 1)\<Longrightarrow>P (x::real)"
nitpick

local_setup {*
  fn lthy =>.
  let
  val dest = MySQL.get_last_experiments lthy 20 "AccuteDest"
  val consts = MySQL.get_last_experiments lthy 20 "AccuteConsts"
  val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals 500 dest
  val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals 500 consts
  val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
  val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
  val _ = GNU_Plot.gp_statistics_to_error_plot ("AccuteDest"^ string_of_int 500) "(b) Best-of-generation error for Acute (destructive)" 500 dest
  val _ = GNU_Plot.gp_statistics_to_error_plot ("AccuteConsts"^ string_of_int 500) "(a) Best-of-generation error for Acute (constructive)" 500 consts
  val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot ("Accute"^ string_of_int 500) "(a) Cumulative Probability of Success for Acute" 500 consts dest
  val begin = HTML.begin_document HTML.no_symbols "Acute Solutions"
  val ed = HTML.end_document
  val path = Path.explode "Acute_results.html"
  val _ = Utils.create_log path
  val html_solutions_dest = Utils.html_table "Destructor style solutions" (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} dest)
  val _ = Utils.trace_log path begin
  val _ = Utils.trace_log path ("<h3>Destructor style solutions</h3>\n" ^ html_solutions_dest)
  val html_solutions_const = Utils.html_table "Contructor style solutions" (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} consts)
  val _ = Utils.trace_log path ("<h3>Contructor style solutions</h3>\n" ^ html_solutions_const)
  val _ = Utils.trace_log path ed
  in lthy end
*}

end