theory CollapsibleParticulars
  imports ParticularStructureMorphisms
begin

context ufo_particular_theory_sig
begin

text_raw \<open>\subsection[Collapsability]{Collapsability\isalabel{subsec:collapsability}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  While in \autoref{subsec:permutability}, we defined the notion of a permutable
  particular as being one that can, in a sense, be ``seen'' as another, through 
  an endomorphism, we here introduce the stronger notion of a collapsible particulars.

  A particular \<open>x\<close> of a particular structure \<open>\<Gamma>\<close> is considered to be collapsible if
  and only if there is at least one other particular \<open>y\<close> of \<open>\<Gamma>\<close> and at least one 
  \<open>\<Gamma>\<close>-endomorphism that maps \<open>x\<close> and \<open>y\<close> to the same particular.

  This notion captures the idea of a plurality of particulars that can be seen
  as being essentially the same, with respect to \<open>\<Gamma>\<close>'s structure.

  Formally, we define a collapsible particular as follows:
\<close>

definition collapsible :: \<open>'p \<Rightarrow> bool\<close>  where
  \<open>collapsible x \<equiv> x \<in> \<P> \<and> (\<exists>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>.\<exists>y \<in> \<P>. x \<noteq> y \<and> \<phi> x = \<phi> y)\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> collapsibleI[intro]:
  assumes \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close> \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> \<open>x \<noteq> y\<close> \<open>\<phi> x = \<phi> y\<close>
  shows \<open>collapsible x\<close>
  using assms by (auto simp: collapsible_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> collapsibleE[elim]:
  assumes \<open>collapsible x\<close>
  obtains \<phi> y where \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close> 
      \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> \<open>x \<noteq> y\<close> \<open>\<phi> x = \<phi> y\<close>  
  using assms by (auto simp: collapsible_def)
  
lemmas \<^marker>\<open>tag (proof) aponly\<close> collapsible_iff[simp] = collapsible_def 

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of non-collapsible particulars of \<open>\<Gamma>\<close> is defined as:
\<close>

definition nonCollapsibleParticulars (\<open>\<P>\<^sub>n\<^sub>c\<close>) where
  \<open>\<P>\<^sub>n\<^sub>c \<equiv> { x . x \<in> \<P> \<and> \<not> collapsible x }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> nonCollapsibleParticularsI[intro!]:
  assumes \<open>x \<in> \<P>\<close> \<open>\<not> collapsible x\<close>
  shows \<open>x \<in> \<P>\<^sub>n\<^sub>c\<close>
  using assms by (auto simp: nonCollapsibleParticulars_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> nonCollapsibleParticularsE[elim!]:
  assumes \<open>x \<in> \<P>\<^sub>n\<^sub>c\<close>
  obtains \<open>x \<in> \<P>\<close> \<open>\<not> collapsible x\<close>
  using assms by (auto simp: nonCollapsibleParticulars_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> nonCollapsibleParticulars_iff[simp]:
  \<open>x \<in> \<P>\<^sub>n\<^sub>c  \<longleftrightarrow> x \<in> \<P> \<and> \<not> collapsible x\<close>
  by (auto simp: nonCollapsibleParticulars_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> nonCollapsibleParticularsAreParticulars: \<open>\<P>\<^sub>n\<^sub>c \<subseteq> \<P>\<close>
  by blast

end

end