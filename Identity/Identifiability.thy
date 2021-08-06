text_raw \<open>\subsection[Identifiable Particulars ]{Identifiable Particulars \isalabel{subsec:identifiable-particulars}}\<close>

theory Identifiability
  imports IdentityPredicate
begin

text \<^marker>\<open>tag bodyonly\<close> \<open> 
  With the definition of an identity predicate, we can define
  the concept of an \emph{identifiable particular} of a
  particular structure as being one for which an identifying
  predicate exists:
\<close>

context ufo_particular_theory_sig
begin

definition identifiables (\<open>\<P>\<^sub>=\<close>) where
  \<open>\<P>\<^sub>= \<equiv> { x | x P . x \<in> \<P> \<and> identity_pred \<Gamma> P x }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> identifiables_I[intro]:
  assumes \<open>x \<in> \<P>\<close> \<open>identity_pred \<Gamma> P x\<close>
  shows \<open>x \<in> \<P>\<^sub>=\<close>
  using assms by (auto simp: identifiables_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> identifiables_E[elim!]:
  assumes \<open>x \<in> \<P>\<^sub>=\<close>
  obtains P where \<open>x \<in> \<P>\<close> \<open>identity_pred \<Gamma> P x\<close>
  using assms by (auto simp: identifiables_def)

end

text \<^marker>\<open>tag bodyonly\<close> \<open>
  If we take Isabelle/HOL to be an example of a formal logic with 
  the power to express any common-sensical identifying predicate
  using UFO particular properties and formal relations, then
  we can consider the definition of identifiable particulars as a
  definition for what a \emph{particular with identity} is, using
  an approach that requires the existence of a predicate.  
\<close>

end