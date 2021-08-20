theory Common
  imports Main "HOL-ZF.MainZF" "HOL-Library.LaTeXsugar" 
begin

(* hiding set *)
translations
  "xs" <= "CONST set xs"

(* hiding numeric conversions - embeddings only *)
translations
  "n" <= "CONST of_nat n"
  "n" <= "CONST int n"

(* append *)
syntax (latex output)
  "_appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<^latex>\<open>\\isacharat\<close>" 65)
translations
  "_appendL xs ys" <= "xs @ ys" 
  "_appendL (_appendL xs ys) zs" <= "_appendL xs (_appendL ys zs)"


(* Let *)
translations 
  "_bind (p, CONST DUMMY) e" <= "_bind p (CONST fst e)"
  "_bind (CONST DUMMY, p) e" <= "_bind p (CONST snd e)"

  "_tuple_args x (_tuple_args y z)" ==
    "_tuple_args x (_tuple_arg (_tuple y z))"

  "_bind (CONST Some p) e" <= "_bind p (CONST the e)"
  "_bind (p # CONST DUMMY) e" <= "_bind p (CONST hd e)"
  "_bind (CONST DUMMY # p) e" <= "_bind p (CONST tl e)"

(* type constraints with spacing *)
no_syntax (output)
  "_constrain" :: "logic => type => logic"  ("_::_" [4, 0] 3)
  "_constrain" :: "prop' => type => prop'"  ("_::_" [4, 0] 3)

syntax (output)
  "_constrain" :: "logic => type => logic"  ("_ :: _" [4, 0] 3)
  "_constrain" :: "prop' => type => prop'"  ("_ :: _" [4, 0] 3)


(* sorts as intersections *)

syntax (output)
  "_topsort" :: "sort"  ("\<top>" 1000)
  "_sort" :: "classes => sort"  ("'(_')" 1000)
  "_classes" :: "id => classes => classes"  ("_ \<inter> _" 1000)
  "_classes" :: "longid => classes => classes"  ("_ \<inter> _" 1000)


setup \<open>
  Thy_Output.antiquotation_pretty_source_embedded \<^binding>\<open>myterm_type\<close>
    (Term_Style.parse -- Args.term)
    (fn ctx => fn (_,t) => 
        Pretty.block [Thy_Output.pretty_term ctx t, Pretty.str " \<Colon>",
            Pretty.brk 1, Syntax.pretty_typ ctx (fastype_of t)])

 \<close>

setup \<open>
 let
   fun proc_loc_name (ctxt, (name, pos)) = 
      Locale.check (Proof_Context.theory_of ctxt) (name, pos) ;
   fun output_locale {context = ctxt, source = src, argument = loc_name : string} : Latex.text =
    let
      val thy = Proof_Context.theory_of ctxt ;
      val loc_hyp_spec = Locale.hyp_spec_of thy loc_name ;
      fun filter_assumption (Element.Assumes x) = let val ((b,(t,_)::_)::_) = x in SOME (b,t) end
          | filter_assumption _                 = NONE
      val assumptions = List.mapPartial filter_assumption loc_hyp_spec
      val assms_latex = assumptions |>
            map (fn (b,prop) =>
                [ 
                  prop |> Thy_Output.pretty_term ctxt |> Thy_Output.pretty ctxt ,
                  Latex.string "(",
                  "" |> Attrib.pretty_binding ctxt b |> Pretty.block |> Thy_Output.pretty ctxt,
                  Latex.string ")\n\n" 
                ]
            ) |> List.concat
    in
      Latex.environment_block "locale" (
       [Latex.string "\\localename{", Latex.string loc_name, Latex.string "}\n"] @
       [Latex.environment_block "localeassms" assms_latex]
      )
 
    end
 in
   Document_Antiquotation.setup_embedded \<^binding>\<open>locale_full\<close>
    (Args.context -- Scan.lift Args.embedded_position >> proc_loc_name)
    output_locale
  end

\<close>

setup \<open>
  Document_Antiquotation.setup_embedded \<^binding>\<open>thm_name\<close>
      (Scan.lift Args.embedded_position -- Attrib.thms)
      (fn {argument = ((name,pos),thm), context = ctxt, source = src} => 
          let
             val ctxt1 = Config.put Name_Space.names_short true ctxt 
          in
            Proof_Context.markup_extern_fact ctxt1 name |> Pretty.marks_str |> Thy_Output.pretty ctxt1
          end)
\<close>

bundle all_trace = [[simp_trace, linarith_trace, metis_trace, smt_trace]]

sledgehammer_params [timeout=60,provers= cvc4 vampire z3 e spass]

end
