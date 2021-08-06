text_raw \<open>\section[Theory of Particulars]{Theory of Particulars\isalabel{sec:particulars}}\<close>

theory \<^marker>\<open>tag aponly\<close> Particulars
  imports Inherence QualifiedParticulars Towardness
begin \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> ufo_particular_theory_sig =
    inherence_sig where  Typ\<^sub>p = \<open>Typ\<^sub>p\<close> +
    qualified_particulars_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    towardness_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> 
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> 

locale \<^marker>\<open>tag aponly\<close> ufo_particular_theory =
    ufo_particular_theory_sig where  Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    inherence_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> +
    qualified_particulars where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
    towardness where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> 
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> +
  assumes
    qualified_particulars_are_not_bearers: \<open>x \<in> \<P>\<^sub>q \<Longrightarrow> \<not> y \<triangleleft> x\<close> 
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
The simplified theory of UFO particulars presented in this chapter has its
signature, given by the locale @{locale ufo_particular_theory_sig}, as
the merge of the @{locale inherence_sig}, @{locale qualified_particulars_sig}, and
@{locale towardness_sig} signature locales.

The axioms of the theory @{locale ufo_particular_theory} consist in those
of the theory @{locale qualified_particulars} plus those of the theory
@{locale towardness}, with the addition of a single axiom meant to
simplify the theory further to facilitate the logical analysis that shall
be done in the next chapters:

\begin{axiom}[$@{thm_name qualified_particulars_are_not_bearers}$]
Qualified moments cannot bear other moments:
\[ @{thm qualified_particulars_are_not_bearers} \]
\end{axiom}
\<close>
text_raw\<open>\par\<close>
lemmas \<^marker>\<open>tag aponly\<close> just_ufo_particular_theory_axioms =
  qualified_particulars_are_not_bearers

lemmas \<^marker>\<open>tag aponly\<close> all_ufo_particular_theory_axioms =
      just_ufo_particular_theory_axioms
      all_inherence_axioms
      all_qualified_particulars_axioms
      all_towardness_axioms
    
end \<^marker>\<open>tag aponly\<close>

end \<^marker>\<open>tag aponly\<close>