text_raw \<open>\section[Anchoring Classes and Identification Dependence]{Anchoring Classes and Identification Dependence\isalabel{subsec:identification-dependence}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In this section, we propose a classification of the anchors
  of particulars of a particular structure and a definition
  of some relations that express various degrees of 
  \emph{identity dependence}.
\<close>

text_raw \<open>\subsection[Anchoring Classes]{Anchoring Classes\isalabel{subsec:anchoring-classes}}\<close>

theory AnchoringClasses
  imports "../Identity/Anchoring"
begin

context ufo_particular_theory
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The anchors of particulars of a structure can be classified into
  several classes. The first is a \emph{minimal anchor}: we say
  that an anchor \<open>\<Gamma>\<^sub>x\<close> for \<open>x\<close> in \<open>\<Gamma>\<close> is \emph{minimal} if and only the 
  only other anchors for \<open>x\<close> in \<open>\<Gamma>\<close> that are substructures of \<open>\<Gamma>\<^sub>x\<close>, 
  i.e. that have an injective morphism to \<open>\<Gamma>\<^sub>x\<close>, are those that are
  isomorphical to \<open>\<Gamma>\<^sub>x\<close>. In other words, a minimal anchor represents
  a minimal context for the identification of a particular. Formally:
\<close>

definition minimallyAnchors :: 
  \<open>'p\<^sub>2 \<Rightarrow>  ('p\<^sub>2,'q) particular_struct \<Rightarrow> 
  ('p\<^sub>2 \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> bool\<close> 
  (\<open>_ \<midarrow>_,_\<rightarrow>\<^sub>\<bottom> _\<close> [74,1,1,74] 75) 
  where
  \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x \<equiv> 
    y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x \<and> 
    (\<forall>\<Gamma>' z \<sigma>\<^sub>1 \<sigma>\<^sub>2. 
        \<Gamma>' \<lless>\<^bsub>\<sigma>\<^sub>1\<^esub> \<Gamma>\<^sub>x \<and> z \<midarrow>\<Gamma>',\<sigma>\<^sub>2\<rightarrow>\<^sub>1 x \<longrightarrow> 
        \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>)\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> minimallyAnchorsI[intro!]: 
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close> \<open>\<And>\<Gamma>' z \<sigma>\<^sub>1 \<sigma>\<^sub>2. \<lbrakk> \<Gamma>' \<lless>\<^bsub>\<sigma>\<^sub>1\<^esub> \<Gamma>\<^sub>x ; z \<midarrow>\<Gamma>',\<sigma>\<^sub>2\<rightarrow>\<^sub>1 x \<rbrakk> \<Longrightarrow> \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>\<close>
  shows \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close>
  using assms by (simp only: minimallyAnchors_def ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> minimallyAnchorsE[elim!]: 
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close>
  obtains \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close> \<open>\<And>\<Gamma>' z \<sigma>\<^sub>1 \<sigma>\<^sub>2. \<lbrakk> \<Gamma>' \<lless>\<^bsub>\<sigma>\<^sub>1\<^esub> \<Gamma>\<^sub>x ; z \<midarrow>\<Gamma>',\<sigma>\<^sub>2\<rightarrow>\<^sub>1 x \<rbrakk> \<Longrightarrow> \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>\<close>
  using assms by (simp only: minimallyAnchors_def ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> minimallyAnchorsD: 
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close>
  shows \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close> \<open>\<And>\<Gamma>' z \<sigma>\<^sub>1 \<sigma>\<^sub>2. \<lbrakk> \<Gamma>' \<lless>\<^bsub>\<sigma>\<^sub>1\<^esub> \<Gamma>\<^sub>x ; z \<midarrow>\<Gamma>',\<sigma>\<^sub>2\<rightarrow>\<^sub>1 x \<rbrakk> \<Longrightarrow> \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>\<close>
  using assms by (simp only: minimallyAnchors_def ; metis)+

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We say that a particular is minimally anchored just in case
  there is at least one minimal anchor for it:
\<close>

definition minimallyAnchored :: \<open>'p set\<close> (\<open>\<P>\<^sub>\<Down>\<close>) 
  where
  \<open>\<P>\<^sub>\<Down> \<equiv> { x | x (y :: ZF) \<Gamma>\<^sub>x \<phi> . y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> minimallyAnchored_I[intro]: \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x \<Longrightarrow> x \<in> \<P>\<^sub>\<Down>\<close>
  by (simp only: minimallyAnchored_def mem_Collect_eq ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> minimallyAnchored_E[elim!]: 
  assumes \<open>x \<in> \<P>\<^sub>\<Down>\<close>
  obtains y :: ZF and \<Gamma>\<^sub>x \<phi> where  \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close>
  using assms by (simp only: minimallyAnchored_def mem_Collect_eq ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> minimallyAnchored_are_anchored: \<open>\<P>\<^sub>\<Down> \<subseteq> \<P>\<^sub>\<down>\<close>
  using minimallyAnchored_E 
  by (metis minimallyAnchorsD(1) subsetI ufo_particular_theory_sig.anchored_particulars_I1)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Similarly, we say that a particular is finitely anchored if there is
  at least one finite anchor for it, i.e., an anchor that has a finite
  set of particulars. In other words, the existence of a finite anchor
  for a particular is the evidence that it's possible to identify finitely,
  e.g. using a finite predicate in first-order logic.
\<close>

definition finitelyAnchored :: \<open>'p set\<close> (\<open>\<P>\<^sup>f\<^sup>i\<^sup>n\<^sub>\<down>\<close>) where
  \<open>\<P>\<^sup>f\<^sup>i\<^sup>n\<^sub>\<down> \<equiv> { x | x (y :: ZF) \<Gamma>\<^sub>x \<phi>. y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x \<and> 
                finite (particulars \<Gamma>\<^sub>x) }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> finitelyAnchored_I[intro]: 
  assumes \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close> \<open>finite (particulars \<Gamma>\<^sub>x)\<close>
  shows \<open>x \<in> \<P>\<^sup>f\<^sup>i\<^sup>n\<^sub>\<down>\<close>
  using assms by (simp only: finitelyAnchored_def mem_Collect_eq ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> finitelyAnchored_E[elim!]: 
  assumes  \<open>x \<in> \<P>\<^sup>f\<^sup>i\<^sup>n\<^sub>\<down>\<close>
  obtains y \<Gamma>\<^sub>x \<phi> where \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>1 x\<close> \<open>finite (particulars \<Gamma>\<^sub>x)\<close>
  using assms by (simp only: finitelyAnchored_def mem_Collect_eq ; metis)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We say that a particular is intrinsically anchored if and only
  if it is anchored by at least one anchor that only has a single
  substantial (but which may have many moments directly or indirectly
  inherent to the single substantial). The existence of such an
  anchor is the evidence that the particular can be identified without
  referring to other substantials, i.e., by referring only to its
  intrinsic properties. Formally, we have:
\<close>

definition intrinsicallyAnchored :: \<open>'p set\<close> (\<open>\<P>\<^sup>i\<^sup>n\<^sup>t\<^sub>\<down>\<close>) 
  where
  \<open>\<P>\<^sup>i\<^sup>n\<^sup>t\<^sub>\<down> \<equiv> { x | x (y :: ZF) \<Gamma>\<^sub>x \<phi>. y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x \<and> 
    (\<forall>z \<in> particulars \<Gamma>\<^sub>x. (ps_inheres_in \<Gamma>\<^sub>x)\<^sup>*\<^sup>* z y) }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicallyAnchored_I[intro]: 
  assumes \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close>
        \<open>\<And>z. z \<in> particulars \<Gamma>\<^sub>x \<Longrightarrow> (ps_inheres_in \<Gamma>\<^sub>x)\<^sup>*\<^sup>* z y\<close>
  shows \<open>x \<in> \<P>\<^sup>i\<^sup>n\<^sup>t\<^sub>\<down>\<close>
  using assms by (simp only: intrinsicallyAnchored_def mem_Collect_eq ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicallyAnchored_E[elim!]: 
  assumes  \<open>x \<in> \<P>\<^sup>i\<^sup>n\<^sup>t\<^sub>\<down>\<close>
  obtains y \<Gamma>\<^sub>x \<phi> where \<open>(y :: ZF) \<midarrow>\<Gamma>\<^sub>x,\<phi>\<rightarrow>\<^sub>\<bottom> x\<close> 
        \<open>\<And>z. z \<in> particulars \<Gamma>\<^sub>x \<Longrightarrow> (ps_inheres_in \<Gamma>\<^sub>x)\<^sup>*\<^sup>* z y\<close>
  using assms by (simp only: intrinsicallyAnchored_def mem_Collect_eq ; metis)

lemma \<^marker>\<open>tag (proof) aponly\<close> intrinsicallyAnchored_are_Anchored: \<open>\<P>\<^sup>i\<^sup>n\<^sup>t\<^sub>\<down> \<subseteq> \<P>\<^sub>\<Down>\<close>
  using intrinsicallyAnchored_E   
  by (meson minimallyAnchored_I subsetI)

end

    
context ufo_particular_theory
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> finite_anchors_imp_min_anchor_ex: 
  fixes x and y :: ZF and \<Gamma>\<^sub>x \<phi>\<^sub>x
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<^sub>x\<rightarrow>\<^sub>1 x\<close> \<open>finite (particulars \<Gamma>\<^sub>x)\<close>
  shows \<open>\<exists>(y\<^sub>2 :: ZF) \<Gamma>\<^sub>2 \<sigma>. y\<^sub>2 \<midarrow>\<Gamma>\<^sub>2,\<phi>\<^sub>x \<circ> \<sigma>\<rightarrow>\<^sub>\<bottom> x \<and> \<Gamma>\<^sub>2 \<lless>\<^bsub>\<sigma>\<^esub> \<Gamma>\<^sub>x\<close>
proof - 
  obtain gamma_x: \<open>x \<in> \<P>\<close> \<open>\<Gamma>\<^sub>x \<lless>\<^bsub>\<phi>\<^sub>x\<^esub> \<Gamma>\<close> \<open>y \<in> particulars \<Gamma>\<^sub>x\<close> 
         \<open>\<And>\<phi> z. \<lbrakk> z \<in> particulars \<Gamma>\<^sub>x ; \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> \<phi> z = x \<longleftrightarrow> z = y\<close>
    using anchorsE[OF assms(1)] by metis
  then interpret phi_x: particular_struct_injection \<Gamma>\<^sub>x \<Gamma> \<phi>\<^sub>x \<open>TYPE(ZF)\<close> \<open>TYPE('p)\<close> \<open>TYPE('q)\<close> by simp
  have \<open>\<exists>(z :: ZF) \<Gamma>' \<phi>. z \<midarrow>\<Gamma>',\<phi>\<^sub>x \<circ> \<phi>\<rightarrow>\<^sub>\<bottom> x \<and> \<Gamma>' \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>x\<close>
  proof (rule ccontr; simp)
    assume AA: \<open>\<forall>(z :: ZF) \<Gamma>' \<phi>. z \<midarrow>\<Gamma>',\<phi>\<^sub>x \<circ> \<phi>\<rightarrow>\<^sub>\<bottom> x \<longrightarrow> \<not> \<Gamma>' \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>x \<close>
    have no_min_anchor: \<open>False\<close> if \<open>z \<midarrow>\<Gamma>',\<phi>\<^sub>x \<circ> \<phi>\<rightarrow>\<^sub>\<bottom> x \<close> \<open>\<Gamma>' \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>x\<close> for z :: ZF and \<Gamma>' \<phi>
      using AA[rule_format] that by simp
    define N where \<open>N \<equiv> { card (particulars \<Gamma>') | \<Gamma>' (z :: ZF) \<phi>\<^sub>1 . z \<midarrow>\<Gamma>',\<phi>\<^sub>x \<circ> \<phi>\<^sub>1\<rightarrow>\<^sub>1 x \<and> \<Gamma>'\<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>x \<and> finite (particulars \<Gamma>')}\<close>
    have \<open>N \<noteq> \<emptyset>\<close>
      apply (auto simp: N_def)      
      apply (rule exI[of _ \<Gamma>\<^sub>x] ; rule exI[of _ y]
              ; rule exI[of _ id] ; intro conjI
              ; (simp only: o_id)?)
      subgoal by (simp add: phi_x.src.particular_struct_axioms sub_structure_by_refl)
      subgoal using assms(1) by blast      
      by (simp add: assms(2))

    then obtain n where N: \<open>n \<in> N\<close> \<open>\<And>i. i \<in> N \<Longrightarrow> n \<le> i\<close> 
      by (meson Inf_nat_def1 bdd_below_def bot.extremum cInf_less_iff leI less_imp_neq)
    then obtain \<Gamma>' and z :: ZF and \<phi>'
      where gamma_z: \<open>z \<midarrow>\<Gamma>',\<phi>\<^sub>x \<circ> \<phi>'\<rightarrow>\<^sub>1 x\<close> \<open>\<Gamma>'\<lless>\<^bsub>\<phi>'\<^esub> \<Gamma>\<^sub>x\<close> \<open>finite (particulars \<Gamma>')\<close> 
            \<open>n = card (particulars \<Gamma>')\<close> 
      using N apply (simp add: N_def)
      by blast
    interpret phi_x': particular_struct_injection \<Gamma>' \<Gamma> \<open>\<phi>\<^sub>x \<circ> \<phi>'\<close> using gamma_z(1) by blast
    interpret phi': particular_struct_injection \<Gamma>' \<Gamma>\<^sub>x \<phi>' using gamma_z(2) by blast
      
    have gamma'': \<open>\<not> z' \<midarrow>\<Gamma>'',\<phi>\<^sub>1\<rightarrow>\<^sub>1 x\<close> if \<open>\<Gamma>'' \<lless>\<^bsub>\<phi>\<^sub>2\<^esub> \<Gamma>'\<close> \<open>\<forall>\<phi>. \<not> \<Gamma>' \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>''\<close> for \<Gamma>'' and z' :: ZF and \<phi>\<^sub>1 \<phi>\<^sub>2
    proof (rule ccontr ; simp)
      assume as3: \<open>z' \<midarrow>\<Gamma>'',\<phi>\<^sub>1\<rightarrow>\<^sub>1 x\<close>
      have C1: \<open>\<Gamma>'' \<lless>\<^bsub>\<phi>' \<circ> \<phi>\<^sub>2\<^esub> \<Gamma>\<^sub>x\<close> using that(1) gamma_z(2) sub_structure_by_trans
        by metis
      then have C2: \<open>finite (particulars \<Gamma>'')\<close> 
        using assms(2) finite_card_sub_structure_by_finite by metis
      have C3: \<open>card (particulars \<Gamma>'') < card (particulars \<Gamma>')\<close>
        using that(1,2) by (simp add: finite_card_substruct_lt gamma_z(3))
      have C3_1: \<open>\<exists>z \<phi>\<^sub>1. z \<midarrow>\<Gamma>'',\<phi>\<^sub>x \<circ> \<phi>\<^sub>1\<rightarrow>\<^sub>1 x \<and> \<Gamma>'' \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>x \<and> finite (particulars \<Gamma>'')\<close>
      proof -
        have "\<forall>f p. \<Gamma>'' \<lless>\<^bsub>(f::ZF \<Rightarrow> 'p) \<circ> (\<phi>' \<circ> \<phi>\<^sub>2)\<^esub> p \<or> \<not> \<Gamma>\<^sub>x \<lless>\<^bsub>f\<^esub> p"
          using C1 sub_structure_by_trans by blast
        then have "z' \<midarrow>\<Gamma>'',\<phi>\<^sub>x \<circ> (\<phi>' \<circ> \<phi>\<^sub>2)\<rightarrow>\<^sub>1 x"
          using as3 phi_x.particular_struct_injection_axioms by blast
        then show ?thesis
          by (meson C1 C2)
      qed        

      have C4: \<open>card (particulars \<Gamma>'') \<in> N\<close>
        apply (simp add: N_def)
        apply (intro exI[of _ \<Gamma>''] conjI C1 C2 ; simp?)
        using C3_1 by metis
        
      then have \<open>card (particulars \<Gamma>') \<le> card (particulars \<Gamma>'')\<close>
        using N(2) gamma_z(4) by simp
      then show False using C3 by auto
    qed
    have gamma_1: \<open>\<Gamma>'' \<in> IsoModels\<^bsub>\<Gamma>',TYPE(ZF)\<^esub>\<close> if as3: \<open>\<Gamma>'' \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>'\<close> \<open>z' \<midarrow>\<Gamma>'',\<phi>\<^sub>2\<rightarrow>\<^sub>1 x\<close> for \<Gamma>'' and z' :: ZF and \<phi>\<^sub>1 \<phi>\<^sub>2
    proof -
      have A1: \<open>finite (particulars \<Gamma>'')\<close>
        using finite_card_sub_structure_by_finite gamma_z that by metis
      obtain \<phi>\<^sub>3 where A2: \<open>\<Gamma>' \<lless>\<^bsub>\<phi>\<^sub>3\<^esub> \<Gamma>''\<close>
        using gamma''[OF as3(1),of z' \<phi>\<^sub>2] as3(2) by metis
      have A3: \<open>\<Gamma>'' \<sim>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>'\<close>
        using sub_structure_by_finite_weak_antisym that(1) A2 A1 by metis
      then show ?thesis
      proof -
        have "MorphImg \<phi>\<^sub>1 \<Gamma>'' = \<Gamma>'"
          by (metis A3 particular_struct_bijection_iff_particular_struct_bijection_1)
        then have "\<Gamma>' \<in> {MorphImg f \<Gamma>'' |f. f \<in> Collect (particular_struct_bijection_1 \<Gamma>'')}"
          using A3 particular_struct_bijection_iff_particular_struct_bijection_1 by auto
        then show ?thesis
          by (metis (no_types) isomorphic_models_def isomorphic_models_sym bijections1_def)
      qed
    qed
      
    have ZZ: \<open>z \<midarrow>\<Gamma>',\<phi>\<^sub>x \<circ> \<phi>'\<rightarrow>\<^sub>\<bottom> x\<close>
      apply (intro minimallyAnchorsI gamma_z(1))
      subgoal for \<Gamma>'' z' \<sigma>\<^sub>1 \<sigma>\<^sub>2
        using gamma_1 by metis
      done
    
    show False using AA[rule_format,of z \<Gamma>'] ZZ
        gamma_z(2) by simp
  qed  
  then obtain  z :: ZF and  \<Gamma>' \<phi> 
    where \<open>z \<midarrow>\<Gamma>',\<phi>\<^sub>x \<circ> \<phi>\<rightarrow>\<^sub>\<bottom> x\<close> \<open>\<Gamma>' \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>x\<close>
    using that by metis    
  then show \<open>?thesis\<close> by metis
qed


text \<^marker>\<open>tag bodyonly\<close> \<open>
  Finite anchors imply the existence of minimal anchors, i.e, finitely
  anchored particulars are also minimally anchored ones:
\<close>

lemma finitely_anchored_are_minimally_anchored: \<open>\<P>\<^sup>f\<^sup>i\<^sup>n\<^sub>\<down> \<subseteq> \<P>\<^sub>\<Down>\<close>
proof (intro subsetI ; elim finitelyAnchored_E)
  fix x and y :: ZF and \<Gamma>\<^sub>x \<phi>\<^sub>x 
  assume assms: \<open>y \<midarrow>\<Gamma>\<^sub>x,\<phi>\<^sub>x\<rightarrow>\<^sub>1 x\<close> \<open>finite (particulars \<Gamma>\<^sub>x)\<close>   
  then obtain  z :: ZF and  \<Gamma>' \<phi> where \<open>z \<midarrow>\<Gamma>',\<phi>\<rightarrow>\<^sub>\<bottom> x\<close> 
    using assms finite_anchors_imp_min_anchor_ex   by metis    
  then show \<open>x \<in> \<P>\<^sub>\<Down>\<close>
    using  minimallyAnchored_I[of z \<Gamma>'] by simp
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> min_anchor_to_zf_I:
  fixes y :: 'a
  assumes \<open>y \<midarrow>\<Gamma>\<^sub>x,\<sigma>\<rightarrow>\<^sub>\<bottom> x\<close>
  shows \<open>\<exists>(y\<^sub>1 :: ZF) \<Gamma>\<^sub>1 \<phi>\<^sub>z. y\<^sub>1 \<midarrow>\<Gamma>\<^sub>1,\<phi>\<^sub>z\<rightarrow>\<^sub>\<bottom> x \<and> \<Gamma>\<^sub>1 \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>\<close>
proof -
  obtain A: \<open>y \<midarrow>\<Gamma>\<^sub>x,\<sigma>\<rightarrow>\<^sub>1 x\<close> \<open>\<And>\<Gamma>' z \<sigma>\<^sub>1 \<sigma>\<^sub>2. \<lbrakk> \<Gamma>' \<lless>\<^bsub>\<sigma>\<^sub>1\<^esub> \<Gamma>\<^sub>x ; z \<midarrow>\<Gamma>',\<sigma>\<^sub>2\<rightarrow>\<^sub>1 x \<rbrakk> \<Longrightarrow> \<Gamma>' \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>\<close>
    using minimallyAnchorsE[OF assms] by metis
  obtain y\<^sub>z :: ZF and \<Gamma>\<^sub>z \<phi>\<^sub>z where B: \<open>y\<^sub>z \<midarrow>\<Gamma>\<^sub>z,\<phi>\<^sub>z\<rightarrow>\<^sub>1 x\<close> \<open>\<Gamma>\<^sub>z \<in> IsoModels\<^bsub>\<Gamma>\<^sub>x,TYPE(ZF)\<^esub>\<close> 
    using anchor_to_zf_I[OF A(1)] by blast
  obtain \<phi> where C: \<open>particular_struct_bijection_1 \<Gamma>\<^sub>x \<phi>\<close> \<open>\<Gamma>\<^sub>z = MorphImg \<phi> \<Gamma>\<^sub>x\<close>
    using B(2) by blast
  then interpret phi: particular_struct_bijection_1 \<Gamma>\<^sub>x \<phi> by simp
  have \<open>\<Gamma>\<^sub>x \<sim>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>z\<close>
    by (simp add: C(2) phi.particular_struct_bijection_axioms)
  have D: \<open>\<Gamma>\<^sub>z \<lless>\<^bsub>phi.inv_morph\<^esub> \<Gamma>\<^sub>x\<close>     
    using C(2) phi.inv_is_bijective_morphism by blast
  obtain E: \<open>x \<in> \<E>\<close>
   \<open>\<Gamma>\<^sub>x \<lless>\<^bsub>\<sigma>\<^esub> \<Gamma>\<close>
   \<open>y \<in> phi.src.\<P>\<close>
   \<open>\<And>\<phi> z. \<lbrakk> z \<in> phi.src.endurants; \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>x,\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> \<phi> z = x \<longleftrightarrow> z = y\<close>
    using A(1)[THEN anchorsE] by metis
  obtain F: \<open>\<Gamma>\<^sub>z \<lless>\<^bsub>\<phi>\<^sub>z\<^esub> \<Gamma>\<close>
   \<open>y\<^sub>z \<in> particulars \<Gamma>\<^sub>z\<close>
   \<open>\<And>\<phi> z. \<lbrakk> z \<in> particulars \<Gamma>\<^sub>z ; \<phi> \<in> Morphs\<^bsub>\<Gamma>\<^sub>z,\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> \<phi> z = x \<longleftrightarrow> z = y\<^sub>z\<close>
    using B(1)[THEN anchorsE] by metis
  have G: \<open>\<Gamma>\<^sub>z \<lless>\<^bsub>\<sigma> \<circ> phi.inv_morph\<^esub> \<Gamma>\<close>
    by (intro particular_struct_injection_comp[of _ \<Gamma>\<^sub>x] D E(2))
  have \<open>y\<^sub>z \<midarrow>\<Gamma>\<^sub>z,\<sigma> \<circ> phi.inv_morph\<rightarrow>\<^sub>\<bottom> x\<close>
    apply (intro minimallyAnchorsI anchorsI B E(1) F(2) G F(3) ; assumption?)    
    subgoal premises P for \<Gamma>' z \<sigma>\<^sub>1 \<sigma>\<^sub>2
      supply R = A(2)[OF particular_struct_injection_comp[OF P(1) D] P(2)]      
      by (metis (no_types, hide_lams) R C isomorphic_models_iff isomorphic_models_sym 
          bijections_iff morph_img_comp particular_struct_bijection_1_comp)
    done  
  then show ?thesis using B(2) by metis
qed


end



end