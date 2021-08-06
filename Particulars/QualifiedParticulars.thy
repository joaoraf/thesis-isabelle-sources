text_raw \<open>\section[Qualified Particulars ]{Qualified Particulars \isalabel{sec:qualified-moments}}\<close>

theory \<^marker>\<open>tag aponly\<close> QualifiedParticulars
  imports \<^marker>\<open>tag aponly\<close> Inherence QualitySpaces
begin \<^marker>\<open>tag aponly\<close>


text \<^marker>\<open>tag bodyonly\<close> \<open>
  Some of the properties an object might have can be
  properties that are associated with measurements,
  degrees, forms, and other abstract forms.

  For example the property ``John's car having a certain reddish 
  color'' is associated with a certain color measurement
  which correspond to the exact tone of color it represents.

  Another example is ``John's height being 1.80m in length''. In this
  case, the property is associated with the length measurement ``1.80 m''.
  
  As was explained in \autoref{sec:quality-spaces}, we represent
  such abstract spaces using the concept of \emph{quality spaces}, 
  axiomatized in the @{locale quality_space} locale. In this section,
  we introduce the notion of qualified moments as those particulars
  which are associated with elements of a quality space.     
\<close>
text_raw \<open>\par\<close>
locale \<^marker>\<open>tag aponly\<close> qualified_particulars_sig =
  inherence_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> +
  quality_space_sig where Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for Typ\<^sub>p :: \<open>'p itself\<close> and Typ\<^sub>q :: \<open>'q itself\<close> +
  fixes assoc_quale :: \<open>'p \<Rightarrow> 'q \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<close> 75)
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>To determine whose moments are qualified moments, we extend 
 the signatures @{locale inherence_sig} and @{locale quality_space_sig}
 with the symbol @{term_type \<open>assoc_quale\<close>}, calling the resulting
 signature @{locale qualified_particulars_sig}.
 
 The proposition \<open>assoc_quale m q\<close>, written as \<open>m \<leadsto> q\<close>, is true just in case
 \<open>m\<close> is a moment, \<open>q\<close> is a quale and \<open>m\<close> is associated to \<open>q\<close>.\<close>


text \<^marker>\<open>tag bodyonly\<close> \<open>
  We call the the set of qualified particulars (\<open>\<P>\<^sub>q\<close>) the set of
  moments associated to some quale:
\<close>
text_raw \<open>\par\<close>
definition qualifiedParticulars (\<open>\<P>\<^sub>q\<close>) where
  \<open>\<P>\<^sub>q \<equiv> { x | x q . x \<leadsto> q }\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The quale associated to a qualified particular is given by the
  \<open>qOf\<close> function, where \<open>qOf m\<close> is equal to the associated quale,
  if \<open>m\<close> is a qualified particular. If \<open>m\<close> is  not a qualified 
  particulars, then the value of \<open>qOf\<close> is undefined:
\<close>
text_raw \<open>\par\<close>
definition quale_of (\<open>qOf\<close>) where \<open>qOf x \<equiv> THE q. x \<leadsto> q\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Similarly, the quality space indirectly associated with a qualified
  particular is given by the \<open>qsOf\<close> function, which associates a 
  qualified particular to the quality space which its associated
  quale is a point of. If \<open>x\<close> is not a qualified particular, then 
  \<open>qsOf x\<close> is the empty set:
\<close>
text_raw \<open>\par\<close>
definition qsOf where
  \<open>qsOf x \<equiv> 
     if x \<in> \<P>\<^sub>q then THE Q. Q \<in> \<Q>\<S> \<and> (\<forall>q. x \<leadsto> q \<longrightarrow> q \<in> Q) else \<emptyset>\<close>

end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> qualified_particulars = 
  inherence where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> +
  quality_space where Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
  qualified_particulars_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for Typ\<^sub>p :: \<open>'p itself\<close> and Typ\<^sub>q :: \<open>'q itself\<close> +
  assumes
    assoc_quale_scope: \<open>x \<leadsto> q \<Longrightarrow> x \<in> \<M> \<and> q \<in> \<Q>\<close> and   
    assoc_quale_unique: \<open>\<lbrakk>x \<leadsto> q\<^sub>1 ; x \<leadsto> q\<^sub>2\<rbrakk> \<Longrightarrow> q\<^sub>1 = q\<^sub>2\<close> and
    quality_moment_unique_by_quality_space:
      \<open>\<lbrakk> w \<in> \<W> ; y\<^sub>1 \<in> w ; y\<^sub>2 \<in> w ; y\<^sub>1 \<triangleleft> x ; y\<^sub>2 \<triangleleft> x ; 
         y\<^sub>1 \<leadsto> q\<^sub>1 ; y\<^sub>2 \<leadsto> q\<^sub>2 ; q\<^sub>1 \<in> Q ; q\<^sub>2 \<in> Q ; Q \<in> \<Q>\<S> \<rbrakk> 
         \<Longrightarrow> y\<^sub>1 = y\<^sub>2\<close> and
    every_quality_space_is_used: \<open>Q \<in> \<Q>\<S> \<Longrightarrow> \<exists>x. \<exists>q \<in> Q.  x \<leadsto> q\<close> and
    quale_determines_moment: 
      \<open>\<lbrakk>y\<^sub>1 \<triangleleft> x ; y\<^sub>2 \<triangleleft> x ; y\<^sub>1 \<leadsto> q ; y\<^sub>2 \<leadsto> q\<rbrakk> \<Longrightarrow> y\<^sub>1 = y\<^sub>2\<close>

begin \<^marker>\<open>tag aponly\<close>
text \<^marker>\<open>tag bodyonly\<close> \<open>
  \todo{João P. questions why the \<open>assoc_quale\<close> function is not world-indexed: it is not by
   choice, because quale association is taken to be constant.}The \<open>assoc_quale\<close> predicate is constrained by the following axioms:

  \begin{axiom}[$@{thm_name assoc_quale_scope}$]
  The \<open>assoc_quale\<close> function associates moments to quales:
  \[ @{thm assoc_quale_scope} \]
  \end{axiom}

  \begin{axiom}[$@{thm_name assoc_quale_unique}$]
  The \<open>assoc_quale\<close> function associates a moment to at most one quale:
  \[ @{thm assoc_quale_unique} \]
  \end{axiom}

  \begin{axiom}[$@{thm_name quality_moment_unique_by_quality_space }$]
  In every possible world \<open>w\<close>, for every endurant \<open>x\<close>, there can by only
  one moment inhering in \<open>x\<close> for each quality space:
  \begin{align*}
    & \llbracket @{thm (prem 1) quality_moment_unique_by_quality_space} 
      ; @{thm (prem 2) quality_moment_unique_by_quality_space} 
      ; @{thm (prem 3) quality_moment_unique_by_quality_space} \\
    & ; @{thm (prem 4) quality_moment_unique_by_quality_space} 
      ; @{thm (prem 5) quality_moment_unique_by_quality_space} 
      ; @{thm (prem 6) quality_moment_unique_by_quality_space} \\
    & ; @{thm (prem 7) quality_moment_unique_by_quality_space} 
      ; @{thm (prem 8) quality_moment_unique_by_quality_space} 
      ; @{thm (prem 9) quality_moment_unique_by_quality_space} \\
    & ; @{thm (prem 10) quality_moment_unique_by_quality_space} 
      \rrbracket \Longrightarrow 
      @{thm (concl) quality_moment_unique_by_quality_space} \\
  \end{align*}
  
  \end{axiom}

  \begin{axiom}[$@{thm_name every_quality_space_is_used}$]
  Every quality space in the family of quality spaces must be associated
  to at least one moment:
  \[ @{thm every_quality_space_is_used} \]
  \end{axiom}  

  \begin{axiom}[$@{thm_name quale_determines_moment}$]
  Given a bearer \<open>x\<close> and a quale \<open>q\<close>, there can be only one moment inhering in 
  \<open>x\<close> associated with \<open>q\<close>:
  \[ @{thm quale_determines_moment} \]
  \end{axiom}
\<close>
text_raw \<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> qualified_particulars_sig
begin \<^marker>\<open>tag aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> qualifiedParticularsI[intro]: 
  assumes \<open>x \<leadsto> q\<close> 
  shows \<open>x \<in> \<P>\<^sub>q\<close>
  using assms
  by (auto simp: qualifiedParticulars_def)

lemma \<^marker>\<open>tag (proof) aponly\<close>qualifiedParticularsE[elim]: 
  assumes \<open>x \<in> \<P>\<^sub>q\<close>
  obtains q where \<open>x \<leadsto> q\<close> 
  using assms
  by (auto simp: qualifiedParticulars_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> qualifiedParticulars_iff: \<open>x \<in> \<P>\<^sub>q \<longleftrightarrow> (\<exists>q. x \<leadsto> q)\<close>
  by blast  

lemma \<^marker>\<open>tag (proof) aponly\<close> qOf_eq_I1: 
  assumes \<open>x \<leadsto> q\<close> \<open>\<exists>!q. x \<leadsto> q\<close> 
  shows \<open>qOf x = q\<close> 
  by (simp add: quale_of_def ; intro the1_equality assms)

lemma \<^marker>\<open>tag (proof) aponly\<close> qOf_I1: 
  assumes \<open>\<exists>!q. x \<leadsto> q\<close> 
  shows \<open>x \<leadsto> qOf x\<close> 
  by (simp add: quale_of_def ; rule the1I2 ; simp add: assms)

lemma \<^marker>\<open>tag (proof) aponly\<close> qsOf_eq_I1:
  assumes \<open>\<exists>!Q. Q \<in> \<Q>\<S> \<and> (\<forall>q. x \<leadsto> q \<longrightarrow> q \<in> Q)\<close> \<open>x \<in> \<P>\<^sub>q\<close> \<open>Q \<in> \<Q>\<S>\<close> 
          \<open>\<And>q. x \<leadsto> q \<Longrightarrow> q \<in> Q\<close>   
  shows \<open>qsOf x = Q\<close>
proof -
  show \<open>?thesis\<close>
    apply (simp only: qsOf_def assms(2) if_True)
    apply (intro the1_equality assms(1,2,3) conjI allI impI)
    by (frule assms(4) ; simp)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> qsOf_I1:
  assumes \<open>\<exists>!Q. Q \<in> \<Q>\<S> \<and> (\<forall>q. x \<leadsto> q \<longrightarrow> q \<in> Q)\<close> \<open>x \<in> \<P>\<^sub>q\<close> 
  obtains \<open>qsOf x \<in> \<Q>\<S>\<close> \<open>\<And>q w. x \<leadsto> q \<Longrightarrow> q \<in> qsOf x\<close>
proof -
  have R1: \<open>qsOf x \<in> \<Q>\<S>\<close>
    apply (simp only: qsOf_def assms(2) if_True)
    by (rule the1I2 ; (intro assms(1))? ; simp)
  have R2: \<open>q \<in> qsOf x\<close> if as: \<open>x \<leadsto> q\<close> for q  
    apply (simp only: qsOf_def assms(2) if_True)
    apply (rule the1I2 ; (intro assms(1))? ; clarsimp)
    using as by blast
  show \<open>?thesis\<close>
    using R1 R2 that by metis
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> qsOf_non_qual_particular[simp]:
  assumes \<open>x \<notin> \<P>\<^sub>q\<close>
  shows \<open>qsOf x = \<emptyset>\<close>
  using assms by (auto simp: qsOf_def)

end

context \<^marker>\<open>tag (proof) aponly\<close> qualified_particulars
begin \<^marker>\<open>tag (proof) aponly\<close>

lemmas \<^marker>\<open>tag (proof) aponly\<close> just_qualified_particulars_axioms = 
    assoc_quale_scope
    assoc_quale_unique

lemmas \<^marker>\<open>tag (proof) aponly\<close> all_qualified_particulars_axioms =
    all_possible_worlds_axioms 
    all_quality_space_axioms 
    just_qualified_particulars_axioms

lemma \<^marker>\<open>tag (proof) aponly\<close> assoc_quale_scopeD:
  assumes \<open>x \<leadsto> q\<close>
  shows \<open>x \<in> \<E>\<close>  \<open>q \<in> \<Q>\<close> \<open>x \<in> \<M>\<close>
  using assms assoc_quale_scope by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> assoc_quale_exI1[intro!]: \<open>m \<in> \<P>\<^sub>q \<Longrightarrow> \<exists>!q. m \<leadsto> q\<close>
  using assoc_quale_unique
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> qOf_eq_I[intro!]: 
  assumes \<open>x \<leadsto> q\<close>
  shows \<open>qOf x = q\<close>
  apply (intro qOf_eq_I1 assms)  
  using assoc_quale_exI1 assoc_quale_scope assms by blast
  

lemma \<^marker>\<open>tag (proof) aponly\<close> qOf_assoc_quale_I[intro!]: \<open>x \<in> \<P>\<^sub>q  \<Longrightarrow> x \<leadsto> qOf x\<close>
  using qOf_I1 assoc_quale_exI1  
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> qsOf_ex1[intro!]:
  assumes \<open>x \<in> \<P>\<^sub>q\<close>
  shows \<open>\<exists>!Q. Q \<in> \<Q>\<S> \<and> (\<forall>q. x \<leadsto> q \<longrightarrow> q \<in> Q)\<close> 
proof -
  obtain q where A: \<open>x \<leadsto> q\<close> using assms by blast
  then obtain B:  \<open>q \<in> \<Q>\<close> using assoc_quale_scope by blast
  then obtain Q where C: \<open>Q \<in> \<Q>\<S>\<close> \<open>q \<in> Q\<close> by blast
  then have D: \<open>Q = Q'\<close> if as: \<open>x \<leadsto> q'\<close> \<open>q' \<in> Q'\<close> \<open>Q' \<in> \<Q>\<S>\<close> for q' Q'
    using assoc_quale_unique A as by (metis qspace_eq_I)  
  have E: \<open>\<forall>q. x \<leadsto> q \<longrightarrow> q \<in> Q\<close> by (metis D \<Q>_E assoc_quale_scope)
  show \<open>?thesis\<close> by (metis A D E C(1))
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> qsOf_I[intro!]: 
  assumes \<open>x \<in> \<P>\<^sub>q\<close>
  shows \<open>qsOf x \<in> \<Q>\<S>\<close> 
  using assms qsOf_I1[OF qsOf_ex1,of \<open>x\<close>] by metis  

lemma \<^marker>\<open>tag (proof) aponly\<close> qsOf_memb[dest]:
  assumes \<open>x \<in> \<P>\<^sub>q\<close> \<open>x \<leadsto> q\<close>
  shows \<open>q \<in> qsOf x\<close>
  using assms qsOf_I1[OF qsOf_ex1,of \<open>x\<close>] 
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> qspace_qOf_eq_qsOf[simp]:
  assumes \<open>x \<in> \<P>\<^sub>q\<close> \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close>
  shows \<open>qspace (qOf x) = qsOf x\<close>
  using qsOf_memb assoc_quale_scope assms by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> qsOf_eq_I:
  assumes \<open>x \<leadsto> q\<close> \<open>q \<in> Q\<close> \<open>Q \<in> \<Q>\<S>\<close> 
  shows \<open>qsOf x = Q\<close>  
  using assms qsOf_I qsOf_memb qualifiedParticularsI   
  by (metis qspace_eq_I) 

lemma \<^marker>\<open>tag (proof) aponly\<close> qualified_particulars_are_moments: \<open>\<P>\<^sub>q \<subseteq> \<M>\<close>   
  using assoc_quale_scopeD(3) by blast

end \<^marker>\<open>tag (proof) aponly\<close> 

end \<^marker>\<open>tag (proof) aponly\<close> 