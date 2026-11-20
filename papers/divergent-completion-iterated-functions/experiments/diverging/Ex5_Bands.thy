(* Example 5: bands, i.e. idempotent semigroups (Dershowitz, 1989).  The
   infinite families are not towers of a unary symbol, so the critic does not
   apply and completion does not terminate.  Open this theory in jEdit and
   interrupt it. *)
theory Ex5_Bands
  imports IsaLibs
begin

typedecl T
consts m :: "T \<Rightarrow> T \<Rightarrow> T"
axiomatization where
  assoc: "m (m x y) z = m x (m y z)" and
  idem: "m x x = x"

declare [[generate_cps = true]]

complete "m (m x y) z = m x (m y z)" by (rule assoc)
complete "m x x = x" by (rule idem)

end
