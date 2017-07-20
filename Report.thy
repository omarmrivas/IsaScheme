theory Report
imports "IsaLibs/IsaLibs"
begin

local_setup {*
  fn lthy =>
  let
  val dest = MySQL.get_last_experiments lthy 20 "SumDest"
  val consts = MySQL.get_last_experiments lthy 20 "SumConsts"
  val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals 500 dest
  val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals 500 consts
  val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
  val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
  val _ = GNU_Plot.gp_statistics_to_error_plot ("SumDest"^ string_of_int 500) "(b) Best-of-generation error for Sum (destructive)" 500 dest
  val _ = GNU_Plot.gp_statistics_to_error_plot ("SumConsts"^ string_of_int 500) "(a) Best-of-generation error for Sum (constructive)" 500 consts
  val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot ("Sum"^ string_of_int 500) "(a) Cumulative Probability of Success for Sum" 500 consts dest
  val begin = HTML.begin_document "Sum Solutions"
  val ed = HTML.end_document
  val path = Path.explode "Sum_results.html"
  val _ = Utils.create_log path
  val html_solutions_dest = Utils.html_table (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} dest)
  val _ = Utils.trace_log path begin
  val _ = Utils.trace_log path ("<h3>Destructor style solutions</h3>\n" ^ html_solutions_dest)
  val html_solutions_const = Utils.html_table (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} consts)
  val _ = Utils.trace_log path ("<h3>Contructor style solutions</h3>\n" ^ html_solutions_const)
  val _ = Utils.trace_log path ed
  in lthy end
*}

local_setup {*
  fn lthy =>
  let
  val dest = MySQL.get_last_experiments lthy 20 "MultiplicationDest"
  val consts = MySQL.get_last_experiments lthy 20 "MultiplicationConsts"
  val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals 500 dest
  val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals 500 consts
  val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
  val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
  val _ = GNU_Plot.gp_statistics_to_error_plot ("MultiplicationDest"^ string_of_int 500) "(d) Best-of-generation error for Multiplication (destructive)" 500 dest
  val _ = GNU_Plot.gp_statistics_to_error_plot ("MultiplicationConsts"^ string_of_int 500) "(c) Best-of-generation error for Multiplication (constructive)" 500 consts
  val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot ("Multiplication"^ string_of_int 500) "(b) Cumulative Probability of Success for Multiplication" 500 consts dest
  val begin = HTML.begin_document "Multiplication Solutions"
  val ed = HTML.end_document
  val path = Path.explode "Multiplication_results.html"
  val _ = Utils.create_log path
  val html_solutions_dest = Utils.html_table (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} dest)
  val _ = Utils.trace_log path begin
  val _ = Utils.trace_log path ("<h3>Destructor style solutions</h3>\n" ^ html_solutions_dest)
  val html_solutions_const = Utils.html_table (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} consts)
  val _ = Utils.trace_log path ("<h3>Contructor style solutions</h3>\n" ^ html_solutions_const)
  val _ = Utils.trace_log path ed
  in lthy end
*}

local_setup {*
  fn lthy =>
  let
  val dest = MySQL.get_last_experiments lthy 20 "EvenOddDest"
  val consts = MySQL.get_last_experiments lthy 20 "EvenOddConsts"
  val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals 500 dest
  val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals 500 consts
  val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
  val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
  val _ = GNU_Plot.gp_statistics_to_error_plot ("EvenOddDest"^ string_of_int 500) "(f) Best-of-generation error for Even/Odd (destructive)" 500 dest
  val _ = GNU_Plot.gp_statistics_to_error_plot ("EvenOddConsts"^ string_of_int 500) "(e) Best-of-generation error for Even/Odd (constructive)" 500 consts
  val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot ("EvenOdd"^ string_of_int 500) "(c) Cumulative Probability of Success for Even/Odd" 500 consts dest
  val begin = HTML.begin_document "Even/Odd Solutions"
  val ed = HTML.end_document
  val path = Path.explode "EvenOdd_results.html"
  val _ = Utils.create_log path
  val html_solutions_dest = Utils.html_table (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} dest)
  val _ = Utils.trace_log path begin
  val _ = Utils.trace_log path ("<h3>Destructor style solutions</h3>\n" ^ html_solutions_dest)
  val html_solutions_const = Utils.html_table (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} consts)
  val _ = Utils.trace_log path ("<h3>Contructor style solutions</h3>\n" ^ html_solutions_const)
  val _ = Utils.trace_log path ed
  in lthy end
*}

local_setup {*
  fn lthy =>
  let
  val dest = MySQL.get_last_experiments lthy 20 "AckermannDest"
  val consts = MySQL.get_last_experiments lthy 20 "AckermannConsts"
  val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals 500 dest
  val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals 500 consts
  val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
  val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
  val _ = GNU_Plot.gp_statistics_to_error_plot ("AckermannDest"^ string_of_int 500) "(h) Best-of-generation error for Ackermann (destructive)" 500 dest
  val _ = GNU_Plot.gp_statistics_to_error_plot ("AckermannConsts"^ string_of_int 500) "(g) Best-of-generation error for Ackermann (constructive)" 500 consts
  val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot ("Ackermann"^ string_of_int 500) "(d) Cumulative Probability of Success for Ackermann" 500 consts dest
  val begin = HTML.begin_document "Ackermann Solutions"
  val ed = HTML.end_document
  val path = Path.explode "Ackermann_results.html"
  val _ = Utils.create_log path
  val html_solutions_dest = Utils.html_table (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} dest)
  val _ = Utils.trace_log path begin
  val _ = Utils.trace_log path ("<h3>Destructor style solutions</h3>\n" ^ html_solutions_dest)
  val html_solutions_const = Utils.html_table (["<b>No.</b>", "<b>Individual</b>", "<b>Schematic Substitution</b>"] :: GP.html_solutions @{context} consts)
  val _ = Utils.trace_log path ("<h3>Contructor style solutions</h3>\n" ^ html_solutions_const)
  val _ = Utils.trace_log path ed
  in lthy end
*}

end