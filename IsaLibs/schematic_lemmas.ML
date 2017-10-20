(*  Title:      util/schematic_lemmas.ML
    ID:         $Id: schematic_lemmas.ML,v 1.00 2017/26/06 16:23:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2017

User suplied schematic lemmas for theory exploration.
*)

signature SCHEMATIC_LEMMAS =
sig

end

structure DB_Schematic_Lemmas
(* : SCHEMATIC_LEMMAS *)
= struct

val parser = Args.embedded_inner_syntax

fun memoized_rules rule =
  Utils.memoize_function Term_Tab.lookup Term_Tab.update I Utils.schematic_lemmas_var
                         (fn _ => ()) rule

fun map_contexts f =
  Local_Theory.background_theory
        (Context.theory_map f) #>
        Local_Theory.target (Context.proof_map f) #>
        Context.proof_map f

val _ =
  let
    fun term_pat str ctxt =
     str |> Proof_Context.read_term_pattern ctxt
         |> memoized_rules
         |> (fn _ => ctxt)
  in Outer_Syntax.local_theory
         @{command_keyword "schematic_lemma"}
         "User suplied orientations for specific rule shapes."
         (parser >> term_pat)
  end

end

structure Schematic_Lemmas : SCHEMATIC_LEMMAS = DB_Schematic_Lemmas

