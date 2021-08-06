text_raw \<open>\subsection[Anchoring Sets]{Anchoring Sets\isalabel{anchoring-sets}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In this section, we describe a series of sets extracted
  from the classes of anchors for a particular, as defined in the
  previous section.
\<close>

theory AnchoringSets
  imports AnchoringClasses
begin

context ufo_particular_theory
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  An anchoring set for a particular \<open>x\<close> in \<open>\<Gamma>\<close> are simply the 
  image (in \<open>\<Gamma>\<close>) of sets of particulars of anchors for \<open>x\<close>.
  They represent the identity neighborhood of \<open>x\<close> in the
  context of the other particulars of the structure. For
  example, if a particular \<open>x\<close> that represents a human can
  be anchored by a structure that contains a substantial
  \<open>y\<close> that anchors \<open>x\<close> and other two substantials, representing
  the parents of \<open>y\<close>, with corresponding relational moments
  representing the parental relationship, we can say that
  the set consisting of the parents of \<open>x\<close> is an anchor set
  for \<open>x\<close>. Formally, we have:   
\<close>

definition anchorSets :: \<open>'p \<Rightarrow> 'p set set\<close> (\<open>\<A>\<^bsub>_\<^esub>\<close> [1] 1000) 
  where 
  \<open>\<A>\<^bsub>x\<^esub> \<equiv> { \<phi> ` particulars \<Gamma>\<^sub>x | \<phi> \<Gamma>\<^sub>x (y :: ZF) . y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x }\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Mirroring the classes defined in the previous section, we have
  the following types of anchor sets, representing finite and
  intrinsic anchors, respectively:
\<close>

definition finiteAnchorSets :: 
  \<open>'p \<Rightarrow> 'p set set\<close> 
  (\<open>\<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>_\<^esub>\<close> [1] 1000)
  where 
    \<open>\<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub> \<equiv> {X . X \<in> \<A>\<^bsub>x\<^esub> \<and> finite X}\<close>

definition intrinsicAnchorSets :: 
  \<open>'p \<Rightarrow> 'p set set\<close> 
  (\<open>\<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>_\<^esub>\<close> [1] 1000)
  where 
    \<open>\<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub> \<equiv> {X . X \<in> \<A>\<^bsub>x\<^esub> \<and> (\<forall>y \<in> X. (\<triangleleft>)\<^sup>*\<^sup>* y x)}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  For example, supposing every human being could be identified
  solely by the DNA sequence, and supposing that we represent
  the association of a human being to a DNA sequence through
  a moment associated with a quale that represents the sequence,
  any human being \<open>x\<close> with DNA sequence \<open>S\<close> could be anchored by
  a particular structure consisting in a substantial and a 
  moment associated with \<open>S\<close>. Thus, \<open>x\<close> and its moment that is
  associated with the DNA sequence \<open>S\<close> are both finite anchor sets
  and intrinsic anchor sets.
\<close>


text \<^marker>\<open>tag bodyonly\<close> \<open>
  We call the \emph{identity core} of \<open>x\<close> the set of particulars
  that appear in all anchor sets of \<open>x\<close>. Such set, if non-empty,
  represent the elements of the domain that are necessary, though
  not always sufficient, to identify \<open>x\<close>. For example, if for
  all human beings in the particular structure, a moment associated
  with a DNA sequence appears in his or hers identity core, then
  we can deduce that the association with a DNA sequence is strictly
  necessary for the identification of human beings (in the particular
  structure). Formally we have:
\<close>
definition identityCore :: 
  \<open>'p \<Rightarrow> 'p set\<close> 
  (\<open>IdCore\<^bsub>_\<^esub>\<close> [1] 999) 
  where
    \<open>IdCore\<^bsub>x\<^esub> \<equiv> \<Inter>\<A>\<^bsub>x\<^esub>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We widen the identity core by intersecting only the anchor sets that
  are intrinsic or finite. These would indicate the particulars that
  are necessary for the identification, if the identification is to
  be done intrisically or in a finite way:
\<close>

definition intrinsicIdentityCore :: 
  \<open>'p \<Rightarrow> 'p set\<close> 
  (\<open>IntIdCore\<^bsub>_\<^esub>\<close> [1] 999) 
  where
    \<open>IntIdCore\<^bsub>x\<^esub> \<equiv> \<Inter>\<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close>

definition finiteIdentityCore :: 
  \<open>'p \<Rightarrow> 'p set\<close> 
  (\<open>FinIdCore\<^bsub>_\<^esub>\<close> [1] 999) 
  where
    \<open>FinIdCore\<^bsub>x\<^esub> \<equiv> \<Inter>\<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close>

definition \<^marker>\<open>tag aponly\<close> identityComplements :: \<open>'p \<Rightarrow> 'p set set\<close> (\<open>IdComps\<^bsub>_\<^esub>\<close> [1] 999) where
  \<open>IdComps\<^bsub>x\<^esub> \<equiv> { X - IdCore\<^bsub>x\<^esub> | X . X \<in> \<A>\<^bsub>x\<^esub>}\<close>

definition \<^marker>\<open>tag aponly\<close> finiteIdentityComplements :: \<open>'p \<Rightarrow> 'p set set\<close> (\<open>FinIdComps\<^bsub>_\<^esub>\<close> [1] 999) where
  \<open>FinIdComps\<^bsub>x\<^esub> \<equiv> { X - FinIdCore\<^bsub>x\<^esub> | X . X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>}\<close>

definition \<^marker>\<open>tag aponly\<close> intrinsicIdentityComplements :: \<open>'p \<Rightarrow> 'p set set\<close> (\<open>IntIdComps\<^bsub>_\<^esub>\<close> [1] 999) where
  \<open>IntIdComps\<^bsub>x\<^esub> \<equiv> { X - IntIdCore\<^bsub>x\<^esub> | X . X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>}\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> anchorSets_I[intro]: \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x \<Longrightarrow> \<phi> ` particulars \<Gamma>\<^sub>x \<in> \<A>\<^bsub>x\<^esub>\<close>
  by (simp only: anchorSets_def mem_Collect_eq ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> anchorSets_E[elim!]: 
  assumes \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close>
  obtains \<phi> \<Gamma>\<^sub>x y  where \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close> \<open>X = \<phi> ` particulars \<Gamma>\<^sub>x\<close>
  using assms
  by (simp only: anchorSets_def mem_Collect_eq ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> anchorSets_iff: 
  \<open>X \<in> \<A>\<^bsub>x\<^esub> \<longleftrightarrow> (\<exists>\<phi> \<Gamma>\<^sub>x y. (y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x \<and> X = \<phi> ` particulars \<Gamma>\<^sub>x)\<close>
  by (simp only: anchorSets_def mem_Collect_eq ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> anchorSets_subset_particulars: \<open>X \<in> \<A>\<^bsub>x\<^esub> \<Longrightarrow> X \<subseteq> \<P>\<close>  
proof (auto) (* generated by sledgehammer *)
  fix \<phi> :: "ZF \<Rightarrow> 'p" and \<Gamma>\<^sub>x :: "(ZF, 'q) particular_struct" and y :: ZF and xa :: ZF
  assume a1: "\<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>"
  assume a2: "xa \<in> particulars \<Gamma>\<^sub>x"
  have f3: "\<forall>z za. possible_worlds_sig.ed (ps_worlds \<Gamma>) (\<phi> z) (\<phi> za) \<or> \<not> possible_worlds_sig.ed (ps_worlds \<Gamma>\<^sub>x) z za"
    using a1 by (meson particular_struct_injection.axioms(1) particular_struct_morphism.morph_reflects_ed_simp possible_worlds_sig.edE)
  have "\<forall>z za. \<not> possible_worlds_sig.indep (ps_worlds \<Gamma>\<^sub>x) z za \<or> possible_worlds_sig.indep (ps_worlds \<Gamma>) (\<phi> z) (\<phi> za)"
    using a1 by (meson particular_struct_injection.axioms(1) particular_struct_morphism.morph_reflects_src_indep_simp possible_worlds_sig.indep_def)
  then show "\<phi> xa \<in> \<E>"
    using f3 a2 by (metis (full_types) \<Gamma>_simps(2) edE possible_worlds_sig.indep_def)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteAnchorSets_I[intro!]:
  assumes \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>finite X\<close>
  shows \<open>X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close>
  using assms 
  by (auto simp: finiteAnchorSets_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteAnchorSets_E[elim!]:
  assumes \<open>X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close>
  obtains \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>finite X\<close>
  using assms 
  by (auto simp: finiteAnchorSets_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteAnchorSets_D:
  assumes \<open>X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close>
  shows \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>finite X\<close>
  using assms 
  by (auto simp: finiteAnchorSets_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteAnchorSets_are_AnchorSets: \<open>\<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub> \<subseteq> \<A>\<^bsub>x\<^esub>\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteAnchorSets_are_Particulars: \<open>X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub> \<Longrightarrow> X \<subseteq> \<P>\<close>
  using anchorSets_subset_particulars  
  by (meson finiteAnchorSets_D(1))

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicAnchorSets_I[intro!]:
  assumes \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>\<And>y. y \<in> X \<Longrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* y x\<close>
  shows \<open>X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close>
  using assms by (auto simp: intrinsicAnchorSets_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicAnchorSets_E[elim!]:
  assumes \<open>X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close>
  obtains \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>\<And>y. y \<in> X \<Longrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* y x\<close>
  using assms by (auto simp: intrinsicAnchorSets_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicAnchorSets_D[elim!]:
  assumes \<open>X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close>
  shows \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>\<And>y. y \<in> X \<Longrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* y x\<close>
  using assms by (auto simp: intrinsicAnchorSets_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicAnchorSets_are_AnchorSets: \<open>\<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub> \<subseteq> \<A>\<^bsub>x\<^esub>\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicAnchorSets_are_Particulars: \<open>X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub> \<Longrightarrow> X \<subseteq> \<P>\<close>  
  by (meson anchorSets_subset_particulars intrinsicAnchorSets_D(1))

lemma \<^marker>\<open>tag (proof) aponly\<close> identityCoreI[intro]: \<open>(\<And>X. X \<in> \<A>\<^bsub>x\<^esub> \<Longrightarrow> y \<in> X) \<Longrightarrow> y \<in> IdCore\<^bsub>x\<^esub>\<close>
  by (auto simp: identityCore_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> identityCoreD[dest]: 
  assumes \<open>y \<in> IdCore\<^bsub>x\<^esub>\<close> \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close>
  shows \<open>y \<in> X\<close>
  using assms by (auto simp: identityCore_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicIdentityCoreI[intro]: \<open>(\<And>X. X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub> \<Longrightarrow> y \<in> X) \<Longrightarrow> y \<in> IntIdCore\<^bsub>x\<^esub>\<close>
  by (auto simp: intrinsicIdentityCore_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicIdentityCoreD[dest]: 
  assumes \<open>y \<in> IntIdCore\<^bsub>x\<^esub>\<close> \<open>X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close>
  shows \<open>y \<in> X\<close>
  using assms by (auto simp: intrinsicIdentityCore_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsic_id_core: \<open>IdCore\<^bsub>x\<^esub> \<subseteq> IntIdCore\<^bsub>x\<^esub>\<close>  
  using identityCore_def intrinsicAnchorSets_D(1) intrinsicIdentityCoreI by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteIdentityCoreI[intro]: \<open>(\<And>X. X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub> \<Longrightarrow> y \<in> X) \<Longrightarrow> y \<in> FinIdCore\<^bsub>x\<^esub>\<close>
  by (auto simp: finiteIdentityCore_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteIdentityCoreD[dest]: 
  assumes \<open>y \<in> FinIdCore\<^bsub>x\<^esub>\<close> \<open>X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close>
  shows \<open>y \<in> X\<close>
  using assms by (auto simp: finiteIdentityCore_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> finite_id_core: \<open>IdCore\<^bsub>x\<^esub> \<subseteq> FinIdCore\<^bsub>x\<^esub>\<close>  
  using identityCore_def finiteAnchorSets_D(1) finiteIdentityCoreI by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> identityComplementsI[intro!]:
  assumes \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>Y = X - IdCore\<^bsub>x\<^esub>\<close>
  shows \<open>Y \<in> IdComps\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: identityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> identityComplementsI1:
  assumes \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> 
  shows \<open>X - IdCore\<^bsub>x\<^esub> \<in> IdComps\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: identityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> identityComplementsE[elim!]:
  assumes \<open>Y \<in> IdComps\<^bsub>x\<^esub>\<close>
  obtains X where \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>Y = X - IdCore\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: identityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> identityComplementsD:
  assumes \<open>Y \<in> IdComps\<^bsub>x\<^esub>\<close> 
  shows \<open>IdCore\<^bsub>x\<^esub> \<inter> Y = \<emptyset>\<close> \<open>IdCore\<^bsub>x\<^esub> \<union> Y \<in> \<A>\<^bsub>x\<^esub>\<close>
  subgoal using assms by (elim identityComplementsE ; simp)
  subgoal 
    using assms 
    apply (elim identityComplementsE ; hypsubst_thin ; simp)    
    by (metis Diff_partition Un_Diff_cancel identityCoreD subset_eq)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> identityComplementsI2:
  assumes \<open>IdCore\<^bsub>x\<^esub> \<inter> Y = \<emptyset>\<close> \<open>IdCore\<^bsub>x\<^esub> \<union> Y \<in> \<A>\<^bsub>x\<^esub>\<close> 
  shows \<open>Y \<in> IdComps\<^bsub>x\<^esub>\<close>
  apply (intro identityComplementsI[OF assms(2)])
  using assms Diff_subset_conv UnI2 
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteIdentityComplementsI[intro!]:
  assumes \<open>X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close> \<open>Y = X - FinIdCore\<^bsub>x\<^esub>\<close>
  shows \<open>Y \<in> FinIdComps\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: finiteIdentityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteIdentityComplementsI1:
  assumes \<open>X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close> 
  shows \<open>X - FinIdCore\<^bsub>x\<^esub> \<in> FinIdComps\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: finiteIdentityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteIdentityComplementsE[elim!]:
  assumes \<open>Y \<in> FinIdComps\<^bsub>x\<^esub>\<close>
  obtains X where \<open>X \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close> \<open>Y = X - FinIdCore\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: finiteIdentityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteIdentityComplementsD:
  assumes \<open>Y \<in> FinIdComps\<^bsub>x\<^esub>\<close> 
  shows \<open>FinIdCore\<^bsub>x\<^esub> \<inter> Y = \<emptyset>\<close> \<open>FinIdCore\<^bsub>x\<^esub> \<union> Y \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close>
  subgoal using assms by (elim finiteIdentityComplementsE ; simp)
  subgoal 
    using assms 
    apply (elim finiteIdentityComplementsE ; hypsubst_thin ; simp)    
    by (metis Diff_partition Un_Diff_cancel finiteIdentityCoreD subset_eq)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> finiteIdentityComplementsI2:
  assumes \<open>FinIdCore\<^bsub>x\<^esub> \<inter> Y = \<emptyset>\<close> \<open>FinIdCore\<^bsub>x\<^esub> \<union> Y \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close> 
  shows \<open>Y \<in> FinIdComps\<^bsub>x\<^esub>\<close>
  apply (intro finiteIdentityComplementsI[OF assms(2)])
  using assms Diff_subset_conv UnI2 
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicIdentityComplementsI[intro!]:
  assumes \<open>X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close> \<open>Y = X - IntIdCore\<^bsub>x\<^esub>\<close>
  shows \<open>Y \<in> IntIdComps\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: intrinsicIdentityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicIdentityComplementsI1:
  assumes \<open>X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close> 
  shows \<open>X - IntIdCore\<^bsub>x\<^esub> \<in> IntIdComps\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: intrinsicIdentityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicIdentityComplementsE[elim!]:
  assumes \<open>Y \<in> IntIdComps\<^bsub>x\<^esub>\<close>
  obtains X where \<open>X \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close> \<open>Y = X - IntIdCore\<^bsub>x\<^esub>\<close>
  using assms 
  apply (simp add: intrinsicIdentityComplements_def)
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicIdentityComplementsD:
  assumes \<open>Y \<in> IntIdComps\<^bsub>x\<^esub>\<close> 
  shows \<open>IntIdCore\<^bsub>x\<^esub> \<inter> Y = \<emptyset>\<close> \<open>IntIdCore\<^bsub>x\<^esub> \<union> Y \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close>
  subgoal using assms by (elim intrinsicIdentityComplementsE ; simp)
  subgoal 
    using assms 
    apply (elim intrinsicIdentityComplementsE ; hypsubst_thin ; simp)    
    by (metis Diff_partition Un_Diff_cancel intrinsicIdentityCoreD subset_eq)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicIdentityComplementsI2:
  assumes \<open>IntIdCore\<^bsub>x\<^esub> \<inter> Y = \<emptyset>\<close> \<open>IntIdCore\<^bsub>x\<^esub> \<union> Y \<in> \<A>\<^sup>i\<^sup>n\<^sup>t\<^bsub>x\<^esub>\<close> 
  shows \<open>Y \<in> IntIdComps\<^bsub>x\<^esub>\<close>
  apply (intro intrinsicIdentityComplementsI[OF assms(2)])
  using assms Diff_subset_conv UnI2 
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> minimallyAnchored_have_an_AnchorSet:  \<open>x \<in> \<P>\<^sub>\<Down> \<longleftrightarrow> \<A>\<^bsub>x\<^esub> \<noteq> \<emptyset>\<close>
proof
  assume A: \<open>x \<in> \<P>\<^sub>\<Down>\<close>
  then obtain y \<Gamma>\<^sub>x \<phi> where 
    B: \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close> 
    using minimallyAnchored_E
    by metis  
  note B[THEN minimallyAnchorsE]    
  then have C: \<open>\<phi> ` particulars \<Gamma>\<^sub>x \<in> \<A>\<^bsub>x\<^esub>\<close>
    using anchorSets_I B by auto    
  then show \<open>\<A>\<^bsub>x\<^esub> \<noteq> \<emptyset>\<close> 
    by (metis emptyE)
next
  assume \<open>\<A>\<^bsub>x\<^esub> \<noteq> \<emptyset>\<close>
  then obtain X where A: \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close>
    using anchorSets_E 
    by (meson all_not_in_conv)
  then obtain \<phi> \<Gamma>\<^sub>x y  where B: 
      \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close> \<open>X = \<phi> ` particulars \<Gamma>\<^sub>x\<close>
    using anchorSets_E by metis  
  show \<open>x \<in> \<P>\<^sub>\<Down>\<close>
    by (intro minimallyAnchored_I[OF B(1)])
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> finitelyAnchored_have_a_finite_AnchorSet:  \<open>x \<in> \<P>\<^sup>f\<^sup>i\<^sup>n\<^sub>\<down> \<longleftrightarrow> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub> \<noteq> \<emptyset>\<close>
proof
  assume A: \<open>x \<in> \<P>\<^sup>f\<^sup>i\<^sup>n\<^sub>\<down>\<close>
  then obtain y \<Gamma>\<^sub>x \<phi> where 
    B: \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close> \<open>finite (particulars \<Gamma>\<^sub>x)\<close>
    by blast
  obtain y\<^sub>1 \<Gamma>\<^sub>x\<^sub>1 \<phi>\<^sub>1 \<sigma> where
    C: \<open>(y\<^sub>1 :: ZF) \<midarrow>\<Gamma>\<^sub>x\<^sub>1,\<phi>\<^sub>1\<rightarrow>\<^sub>\<bottom> x\<close> \<open>\<Gamma>\<^sub>x\<^sub>1 \<lless>\<^bsub>\<sigma>\<^esub> \<Gamma>\<^sub>x\<close>
    using finite_anchors_imp_min_anchor_ex B by metis
  then interpret sigma: particular_struct_injection \<Gamma>\<^sub>x\<^sub>1 \<Gamma>\<^sub>x \<sigma> by simp
  have \<open>finite (particulars \<Gamma>\<^sub>x\<^sub>1)\<close> 
    apply (intro sigma.morph_is_injective[THEN inj_on_finite,OF _ B(2)])
    by blast
  then have \<open>\<phi>\<^sub>1 ` particulars \<Gamma>\<^sub>x\<^sub>1 \<in> \<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub>\<close>
    using C(1) anchorSets_I finiteAnchorSets_I by auto    
  then show \<open>\<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub> \<noteq> \<emptyset>\<close> 
    by (metis emptyE)
next
  assume \<open>\<A>\<^sup>f\<^sup>i\<^sup>n\<^bsub>x\<^esub> \<noteq> \<emptyset>\<close>
  then obtain X where A: \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close> \<open>finite X\<close>
    using finiteAnchorSets_E 
    by (meson all_not_in_conv)
  then obtain \<phi> \<Gamma>\<^sub>x y  where B: 
      \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close> \<open>X = \<phi> ` particulars \<Gamma>\<^sub>x\<close>
    using anchorSets_E by metis
  then interpret phi: particular_struct_injection \<Gamma>\<^sub>x \<Gamma> \<phi> by blast
  have C: \<open>finite (particulars \<Gamma>\<^sub>x)\<close> 
    using phi.morph_is_injective B(2) finite_image_iff A(2) by metis
  obtain D: \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close> using B(1) by blast
  show \<open>x \<in> \<P>\<^sup>f\<^sup>i\<^sup>n\<^sub>\<down>\<close>
    by (intro finitelyAnchored_I[OF D C])
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> minimallyAnchored_to_AnchorSet:  
  assumes \<open>x \<in> \<P>\<^sub>\<Down>\<close>
  obtains X where \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close>
  using assms apply (simp only: minimallyAnchored_have_an_AnchorSet)  
  by (meson all_not_in_conv)

lemma \<^marker>\<open>tag (proof) aponly\<close> AnchorSet_to_minimallyAnchored:  
  assumes \<open>X \<in> \<A>\<^bsub>x\<^esub>\<close>
  shows \<open>x \<in> \<P>\<^sub>\<Down>\<close> 
  using assms apply (simp only: minimallyAnchored_have_an_AnchorSet)    
  by (metis emptyE)


end

end