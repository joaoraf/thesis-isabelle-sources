text_raw \<open>\subsection[Permutability]{Permutability\isalabel{subsec:permutability}}\<close>

theory Permutability
  imports ParticularStructureMorphisms
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Besides the notion of isomorphically unique particulars, presented in 
  \autoref{subsec:isomorphical-uniqueness}, we can also study the property
  of a particular in a particular structure through the endomorphisms of
  that structure.
\<close>

context ufo_particular_theory_sig
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We say that a particular \<open>x\<close> in a particular structure \<open>\<Gamma>\<close> is permutable 
  just in case there is an endomorphism \<open>\<phi>\<close> such that either \<open>\<phi> x \<noteq> x\<close>,
  i.e. it maps \<open>x\<close> to some other particular, or there is some particular 
  \<open>y \<noteq> x\<close> such that \<open>\<phi> y = x\<close>, i.e. it maps some other particular to \<open>x\<close>.

  Conversely, we call it non-permutable if there is no other particular \<open>y\<close>
  such that \<open>x\<close> can be ``seen'' as \<open>y\<close> or that \<open>y\<close> can be ``seen'' as \<open>x\<close>,
  through an endomorphism. 

  Formally, we define a non-permutable particular as:
\<close>

definition non_permutable :: \<open>'p \<Rightarrow> bool\<close> where
  \<open>non_permutable x \<longleftrightarrow> (\<forall>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>.\<forall>y \<in> \<P>. \<phi> y = x \<longleftrightarrow> y = x)\<close>


lemma \<^marker>\<open>tag (proof) aponly\<close> non_permutable_I[intro!]: 
  assumes \<open>\<And>\<phi> y. \<lbrakk> \<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub> ; y \<in> \<P> \<rbrakk> \<Longrightarrow> \<phi> y = x \<longleftrightarrow> y = x\<close>
  shows \<open>non_permutable x\<close>
  using assms 
  by (auto simp: non_permutable_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> non_permutable_E[elim]: 
  assumes \<open>non_permutable x\<close> \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close> \<open>y \<in> \<P>\<close>
  shows \<open>\<phi> y = x \<longleftrightarrow> y = x\<close>
  using assms 
  by (auto simp: non_permutable_def)

lemmas non_permutable_iff[simp] = non_permutable_def

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The set of non-permutables particulars is defined as:
\<close>

definition non_permutables (\<open>\<P>\<^sub>1\<^sub>!\<close>) where
  \<open>\<P>\<^sub>1\<^sub>! \<equiv> { x . x \<in> \<P> \<and> non_permutable x }\<close> 

lemma \<^marker>\<open>tag (proof) aponly\<close> non_permutables_I[intro!]: 
  assumes \<open>x \<in> \<P>\<close> \<open>non_permutable x\<close>
  shows \<open>x \<in> \<P>\<^sub>1\<^sub>!\<close>
  using assms by (auto simp: non_permutables_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> non_permutables_E[elim!]: 
  assumes \<open>x \<in> \<P>\<^sub>1\<^sub>!\<close>
  obtains \<open>x \<in> \<P>\<close> \<open>non_permutable x\<close>
  using assms by (auto simp: non_permutables_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> non_permutables_iff[simp]:
  \<open>x \<in> \<P>\<^sub>1\<^sub>! \<longleftrightarrow> x \<in> \<P> \<and> non_permutable x\<close>
  by (auto simp: non_permutables_def)

end


end