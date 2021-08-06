text_raw \<open>\section[Universals and Instantiation]{Universals and Instantiation\isalabel{sec:universals}}\<close>

theory \<^marker>\<open>tag aponly\<close> Universals
  imports \<^marker>\<open>tag aponly\<close> "../Particulars/Particulars"
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  This section presents a brief theory of Universals and Instantiation based on
  the original theory presented in \cite{UFO}.  

  A universal, in UFO, is the object in the theory that represents a concept.
  For example, the concepts \emph{Car}, \emph{Human Being}, \emph{Red Colored}
  which could stand for, respectively, cars, human beings, and things that have
  a red color, are represent in UFO as Universals. A particular is called an 
  \emph{instance of} any universal whenever it 
  satisfies the conditions that characterize the later. For example, one of
  the instances of the \emph{Human Being} universal is this thesis author
  himself.
\<close>
text_raw\<open>\par\<close>
locale \<^marker>\<open>tag aponly\<close> instantiation_sig =
    ufo_particular_theory_sig where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q 
  for iof :: \<open>'p \<Rightarrow> 'p set \<Rightarrow> 'u \<Rightarrow> bool\<close> (\<open>_ \<Colon>\<^bsub>_\<^esub> _\<close> [74,1,74] 75) 
  and Typ\<^sub>p :: \<open>'p itself\<close> and Typ\<^sub>q :: \<open>'q itself\<close> and Typ\<^sub>u :: \<open>'u itself\<close>
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The instantiation relation between particulars and universals is represented
  formally through the @{term_type \<open>iof\<close>} symbol. The expression \<open>m \<Colon>\<^bsub>w\<^esub> U\<close> 
  means that in the possible world \<open>w\<close>, the particular \<open>m\<close> instantiates \<open>U\<close>.

  As the signature of the \<open>iof\<close> symbol hints, instantiation is a contingent relationship,
  i.e. a particular that instantiates a universal \<open>U\<close> in a possible world (e.g. in the
  actual world) may not instantiate it in another possible world. For example, in one
  possible world, the author of this thesis may instantiate the \emph{Anxious} and
  \emph{PhD Candidate} universals, but in another possible world, the author might
  instante the \emph{Happy} and \emph{PhD} universals instead.
  
  The locale @{locale instantiation_sig} consists in the signature of the simplified
  particulars theory, given by the locale @{locale ufo_particular_theory_sig}, extended with
  the symbol @{term_type \<open>iof\<close>}.
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Given an interpretation for the \<open>iof\<close> function, the set of universals are exactly those entities that are instantiated by some particular in some possible world: 
\<close>
text_raw\<open>\par\<close>
definition \<open>\<U> \<equiv> { u | x w u . x \<Colon>\<^bsub>w\<^esub> u}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  This means that we do not accept impossible universals, i.e. those that cannot possibly have an instance. We say that a universal \<open>u\<^sub>1\<close> \emph{subsumes} a universal \<open>u\<^sub>2\<close> (written as 
  \<open>u\<^sub>1 \<sqsubseteq> u\<^sub>2\<close>) just in case in every possible world, every instance of \<open>u\<^sub>1\<close>
  is also an instance of \<open>u\<^sub>2\<close>:
\<close>
text_raw\<open>\par\<close>
definition subsumes (infix \<open>\<sqsubseteq>\<close> 75) where
  \<open>u\<^sub>1 \<sqsubseteq> u\<^sub>2 \<longleftrightarrow> u\<^sub>1 \<in> \<U> \<and> (\<forall>x w. x \<Colon>\<^bsub>w\<^esub> u\<^sub>1 \<longrightarrow> x \<Colon>\<^bsub>w\<^esub> u\<^sub>2)\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  For example, the universal \<open>Dog\<close> subsumes the universal \<open>Animal\<close> which
  instantiates the universal \<open>Living Being\<close>.
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We say that a universal \<open>U\<close> is characterized by another universal \<open>u\<close> 
  just in case, in every possible world \<open>w\<close>, every instance of \<open>U\<close> bears
  a moments that instantiates the universal \<open>u\<close>.
\<close>
text_raw\<open>\par\<close>
definition char_by where
  \<open>char_by U u \<longleftrightarrow> U \<in> \<U> \<and> (\<forall>x w. x \<Colon>\<^bsub>w\<^esub> U \<longrightarrow> (\<exists>y. y \<triangleleft> x \<and> y \<Colon>\<^bsub>w\<^esub> u))\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of instances of a universal \<open>U\<close> is given by the function
  \<open>Insts\<close> and consists in all instances that \<open>U\<close> has in all possible
  worlds:
\<close>
text_raw\<open>\par\<close>
definition Insts :: \<open>'u \<Rightarrow> 'p set\<close> where \<open>Insts U \<equiv> { x | x w . x \<Colon>\<^bsub>w\<^esub> U }\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of \emph{substantial universals} consists in all
  universals that have a substantial as an instance:
\<close>
text_raw\<open>\par\<close>
definition \<open>\<U>\<^sub>\<S> \<equiv> { u | x w u . x \<Colon>\<^bsub>w\<^esub> u \<and> x \<in> \<S>}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Likewise, the set of \emph{moment universals} consists in all
  universals that have a moment as an instance:
\<close>
text_raw\<open>\par\<close>
definition \<open>\<U>\<^sub>\<M> \<equiv> { u | x w u . x \<Colon>\<^bsub>w\<^esub> u \<and> x \<in> \<M>}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open> 
  A universal \<open>u\<close> is considered \emph{rigid} if and only if every
  instance of \<open>u\<close> always instantiates it in all possible worlds in which
  they exist:
\<close>
text_raw\<open>\par\<close>
definition rigid :: \<open>'u \<Rightarrow> bool\<close> where
  \<open>rigid u \<equiv> u \<in> \<U> \<and> (\<forall>x w\<^sub>1 w\<^sub>2. x \<Colon>\<^bsub>w\<^sub>1\<^esub> u \<and> w\<^sub>2 \<in> \<W> \<and> x \<in> w\<^sub>2 \<longrightarrow> x \<Colon>\<^bsub>w\<^sub>2\<^esub> u)\<close>

end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> instantiation_thy =
    instantiation_sig where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>u = Typ\<^sub>u +
    ufo_particular_theory where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q 
  for Typ\<^sub>p :: \<open>'p itself\<close> and
      Typ\<^sub>q :: \<open>'q itself\<close> and
      Typ\<^sub>u :: \<open>'u itself\<close> +
  assumes iof_imp_existence: \<open>x \<Colon>\<^bsub>w\<^esub> U \<Longrightarrow> w \<in> \<W> \<and> x \<in> w\<close> 
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The basic theory of instantiation, described in the locale @{locale instantiation_thy},
  extends the @{locale ufo_particular_theory} locale with the @{locale instantiation_sig} 
  signature and with the following axiom:

  \begin{axiom}[$@{thm_name iof_imp_existence}$]
    If a particular \<open>x\<close> instantiates some universal in a possible world \<open>w\<close>, then 
    then \<open>x\<close> must exist in \<open>w\<close>:
   \[ @{thm iof_imp_existence} \]
  \end{axiom}
\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> universals = 
    instantiation_thy where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>u = Typ\<^sub>u     
  for Typ\<^sub>p :: \<open>'p itself\<close> and
      Typ\<^sub>q :: \<open>'q itself\<close> and
      Typ\<^sub>u :: \<open>'u itself\<close> +
  assumes substantial_moment_univs_separate: \<open>\<U>\<^sub>\<S> \<inter> \<U>\<^sub>\<M> = \<emptyset>\<close> and
          moment_universals_are_rigid: \<open>u \<in> \<U>\<^sub>\<M> \<Longrightarrow> rigid u\<close>
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The theory of UFO universals further extend the theory of instantiation with
  the following axioms:

 \begin{axiom}[$@{thm_name substantial_moment_univs_separate}$]
  Universals are either Substantial Universals or Moment Universals, i.e.,
  instantiation does not cross categories. In other words, a universal 
  can either have only moments or substantials as instances:
  \[ @{thm substantial_moment_univs_separate} \]
 \end{axiom}

 \begin{axiom}[$@{thm_name moment_universals_are_rigid}$]
  In the original UFO theory of universals moment universals are not considered necessarily
  rigid, but here we make this assumption to simplifiy the formal analysis:
  \[ @{thm moment_universals_are_rigid} \]
 \end{axiom}
\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> instantiation_sig
begin  \<^marker>\<open>tag aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> \<U>_I[intro]: \<open>x \<Colon>\<^bsub>w\<^esub> u \<Longrightarrow> u \<in> \<U>\<close>
  by (auto simp: \<U>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close>\<U>_E[elim]:
  assumes \<open>u \<in> \<U>\<close>
  obtains x w where \<open>x \<Colon>\<^bsub>w\<^esub> u\<close>
  using assms by (auto simp: \<U>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> \<U>_iff: \<open>u \<in> \<U> \<longleftrightarrow> (\<exists>x w. x \<Colon>\<^bsub>w\<^esub> u)\<close>
  by (auto simp: \<U>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> subsumesI[intro!]:
  assumes \<open>u\<^sub>1 \<in> \<U>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> u\<^sub>1 \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> u\<^sub>2\<close>
  shows \<open>u\<^sub>1 \<sqsubseteq> u\<^sub>2\<close>
  using assms by (auto simp: subsumes_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> subsumesE[elim]:
  assumes \<open>u\<^sub>1 \<sqsubseteq> u\<^sub>2\<close>
  obtains \<open>u\<^sub>1 \<in> \<U>\<close> \<open>u\<^sub>2 \<in> \<U>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> u\<^sub>1 \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> u\<^sub>2\<close>
  using assms apply (auto simp: subsumes_def)
  using \<U>_I  \<U>_E by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> subsumes_refl[intro!]:
  assumes \<open>u \<in> \<U>\<close>
  shows \<open>u \<sqsubseteq> u\<close>
  using assms by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> subsumes_trans[trans]:
  assumes \<open>u\<^sub>1 \<sqsubseteq> u\<^sub>2\<close> \<open>u\<^sub>2 \<sqsubseteq> u\<^sub>1\<close>
  shows \<open>u\<^sub>2 \<sqsubseteq> u\<^sub>1\<close>
  using assms by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> subsumes_D:
  assumes \<open>u\<^sub>1 \<sqsubseteq> u\<^sub>2\<close>
  shows \<open>u\<^sub>1 \<in> \<U>\<close> \<open>u\<^sub>2 \<in> \<U>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> u\<^sub>1 \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> u\<^sub>2\<close>
  using assms by blast+

lemma \<^marker>\<open>tag (proof) aponly\<close> char_by_I[intro!]:
  assumes \<open>U \<in> \<U>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> U \<Longrightarrow> \<exists>y. y \<triangleleft> x \<and> y \<Colon>\<^bsub>w\<^esub> u\<close>
  shows \<open>char_by U u\<close>
  using assms by (auto simp: char_by_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> char_by_E[elim]:
  assumes \<open>char_by U u\<close>
  obtains \<open>U \<in> \<U>\<close> \<open>u \<in> \<U>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> U \<Longrightarrow> \<exists>y. y \<triangleleft> x \<and> y \<Colon>\<^bsub>w\<^esub> u\<close>
  using assms 
  apply (auto simp: char_by_def)
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> char_by_D[elim]:
  assumes \<open>char_by U u\<close>
  shows \<open>U \<in> \<U>\<close> \<open>u \<in> \<U>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> U \<Longrightarrow> \<exists>y. y \<triangleleft> x \<and> y \<Colon>\<^bsub>w\<^esub> u\<close>
  using assms by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> char_by_mono:
  assumes \<open>U\<^sub>2 \<sqsubseteq> U\<^sub>1\<close> \<open>u\<^sub>1 \<sqsubseteq> u\<^sub>2\<close> \<open>char_by U\<^sub>1 u\<^sub>1\<close>
  shows \<open>char_by U\<^sub>2 u\<^sub>2\<close>
  using assms by (meson char_by_E subsumesE char_by_I)

lemma \<^marker>\<open>tag (proof) aponly\<close> InstsI[intro]:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  shows \<open>x \<in> Insts U\<close>
  using assms by (auto simp: Insts_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> InstsE[elim!]:
  assumes \<open>x \<in> Insts U\<close>
  obtains w where \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  using assms by (auto simp: Insts_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> Insts_iff: \<open>x \<in> Insts U \<longleftrightarrow> (\<exists>w. x \<Colon>\<^bsub>w\<^esub> U)\<close>
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> Insts_mono[intro]: 
  assumes \<open>u\<^sub>1 \<sqsubseteq> u\<^sub>2\<close>
  shows \<open>Insts u\<^sub>1 \<subseteq> Insts u\<^sub>2\<close>  
  using assms by fastforce

lemma \<^marker>\<open>tag (proof) aponly\<close> rigidI[intro!]:
  assumes \<open>u \<in> \<U>\<close> \<open>\<And>x w\<^sub>1 w\<^sub>2. \<lbrakk> x \<Colon>\<^bsub>w\<^sub>1\<^esub> u ; w\<^sub>2 \<in> \<W> ; x \<in> w\<^sub>2 \<rbrakk> \<Longrightarrow> x \<Colon>\<^bsub>w\<^sub>2\<^esub> u\<close>
  shows \<open>rigid u\<close>
  using assms by (auto simp: rigid_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> rigidE[elim!]:
  assumes \<open>rigid u\<close>
  obtains \<open>u \<in> \<U>\<close> \<open>\<And>x w\<^sub>1 w\<^sub>2. \<lbrakk> x \<Colon>\<^bsub>w\<^sub>1\<^esub> u ; w\<^sub>2 \<in> \<W> ; x \<in> w\<^sub>2 \<rbrakk> \<Longrightarrow> x \<Colon>\<^bsub>w\<^sub>2\<^esub> u\<close>
  using assms by (auto simp: rigid_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> \<U>\<^sub>\<M>_I[intro]:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> u\<close> \<open>x \<in> \<M>\<close>
  shows \<open>u \<in> \<U>\<^sub>\<M>\<close>
  using assms by (auto simp: \<U>\<^sub>\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<M>_E[elim]:
  assumes \<open>u \<in> \<U>\<^sub>\<M>\<close>
  obtains x w where \<open>x \<Colon>\<^bsub>w\<^esub> u\<close> \<open>x \<in> \<M>\<close>
  using assms by (auto simp: \<U>\<^sub>\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<M>_\<U>: \<open>u \<in> \<U>\<^sub>\<M> \<Longrightarrow> u \<in> \<U>\<close> by auto

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<M>_subset_\<U>: \<open>\<U>\<^sub>\<M> \<subseteq> \<U>\<close> by auto

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<M>_iff:  \<open>u \<in> \<U>\<^sub>\<M> \<longleftrightarrow> (\<exists>x w. x \<Colon>\<^bsub>w\<^esub> u \<and> x \<in> \<M>)\<close>
  by (auto simp: \<U>\<^sub>\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<S>_I[intro]:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> u\<close> \<open>x \<in> \<S>\<close>
  shows \<open>u \<in> \<U>\<^sub>\<S>\<close>
  using assms by (auto simp: \<U>\<^sub>\<S>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<S>_E[elim]:
  assumes \<open>u \<in> \<U>\<^sub>\<S>\<close>
  obtains x w where \<open>x \<Colon>\<^bsub>w\<^esub> u\<close> \<open>x \<in> \<S>\<close>
  using assms by (auto simp: \<U>\<^sub>\<S>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<S>_\<U>: \<open>u \<in> \<U>\<^sub>\<S> \<Longrightarrow> u \<in> \<U>\<close> by auto

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<S>_subset_\<U>: \<open>\<U>\<^sub>\<S> \<subseteq> \<U>\<close> by auto

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<S>_iff:  \<open>u \<in> \<U>\<^sub>\<S> \<longleftrightarrow> (\<exists>x w. x \<Colon>\<^bsub>w\<^esub> u \<and> x \<in> \<S>)\<close>
  by (auto simp: \<U>\<^sub>\<S>_def)

end  \<^marker>\<open>tag aponly\<close>

context instantiation_thy  \<^marker>\<open>tag aponly\<close>
begin  \<^marker>\<open>tag aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> iof_scope_E:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  obtains \<open>x \<in> \<P>\<close> \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close> \<open>U \<in> \<U>\<close>
  using assms iof_imp_existence worlds_are_made_of_particulars by blast

lemma \<^marker>\<open>tag (proof) aponly\<close>  iof_scope:
  assumes \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  shows \<open>x \<in> \<P>\<close> \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close> \<open>U \<in> \<U>\<close> 
  using assms iof_scope_E by metis+ 

end  \<^marker>\<open>tag aponly\<close>

context  \<^marker>\<open>tag aponly\<close> universals
begin \<^marker>\<open>tag aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<S>_insts[intro]:
  assumes \<open>U \<in> \<U>\<^sub>\<S>\<close> \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  shows \<open>x \<in> \<S>\<close>
proof -
  have A: \<open>x \<in> \<E>\<close> using assms(2) using iof_scope(1) by auto
  have B: \<open>x \<notin> \<M>\<close> 
    using \<U>\<^sub>\<M>_I substantial_moment_univs_separate
          assms substantial_moment_univs_separate 
    by blast
  then show ?thesis using A by blast
qed

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<U>\<^sub>\<M>_insts[intro]:
  assumes \<open>U \<in> \<U>\<^sub>\<M>\<close> \<open>x \<Colon>\<^bsub>w\<^esub> U\<close>
  shows \<open>x \<in> \<M>\<close>
proof -
  have A: \<open>x \<in> \<E>\<close> using assms(2) iof_scope(1) by auto
  have B: \<open>x \<notin> \<S>\<close> 
    using \<U>\<^sub>\<S>_I substantial_moment_univs_separate
          assms substantial_moment_univs_separate 
    by blast
  then show ?thesis using A by blast
qed

lemma \<^marker>\<open>tag (proof) aponly\<close>  endurant_universal_subsumption_cases: 
  assumes \<open>U\<^sub>1 \<sqsubseteq> U\<^sub>2\<close>
  obtains (substantial_universals) \<open>U\<^sub>1 \<in> \<U>\<^sub>\<S>\<close> \<open>U\<^sub>2 \<in> \<U>\<^sub>\<S>\<close> 
        | (moment_universals) \<open>U\<^sub>1 \<in> \<U>\<^sub>\<M>\<close> \<open>U\<^sub>2 \<in> \<U>\<^sub>\<M>\<close> 
proof -
  obtain A: \<open>U\<^sub>1 \<in> \<U>\<close> \<open>U\<^sub>2 \<in> \<U>\<close> \<open>\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> U\<^sub>2\<close>
    using assms subsumesE by blast
  obtain x w where B: \<open>x \<Colon>\<^bsub>w\<^esub> U\<^sub>1\<close> \<open>x \<Colon>\<^bsub>w\<^esub> U\<^sub>2\<close> using A(1,3) by blast
  then have \<open>x \<in> \<E>\<close> using iof_scope by metis
  then show ?thesis
    apply (cases x rule: endurant_cases)        
    subgoal using B substantial_universals by blast
    using B moment_universals by blast
qed

lemma \<^marker>\<open>tag (proof) aponly\<close>  substantial_universal_subsumes[iff]:
  assumes \<open>U\<^sub>1 \<sqsubseteq> U\<^sub>2\<close>
  shows \<open>U\<^sub>1 \<in> \<U>\<^sub>\<S> \<longleftrightarrow> U\<^sub>2 \<in> \<U>\<^sub>\<S>\<close> (is \<open>?A\<close>) \<open>U\<^sub>1 \<in> \<U>\<^sub>\<M> \<longleftrightarrow> U\<^sub>2 \<in> \<U>\<^sub>\<M>\<close> (is \<open>?B\<close>)
proof -  
  show ?A
    using assms 
    apply (cases rule: endurant_universal_subsumption_cases ; simp?)
    using substantial_moment_univs_separate by blast
  show ?B
    using assms 
    apply (cases rule: endurant_universal_subsumption_cases ; simp?)
    using substantial_moment_univs_separate by blast
qed

end  \<^marker>\<open>tag aponly\<close>

end  \<^marker>\<open>tag aponly\<close>
