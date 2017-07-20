theory Scratch
imports Complex_Main
begin

export_code log in SML

ML {*
  val t = @{term "42 / (12 :: rat) - (7 / 2) = 0"}
  val t' = Value.value @{context} t
  val _ = tracing (Syntax.string_of_term @{context} t')
*}

end