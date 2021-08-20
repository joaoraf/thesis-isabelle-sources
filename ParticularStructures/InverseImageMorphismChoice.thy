text_raw \<open>\subsection[Inverse Images]{Inverse Images\isalabel{subsec:inverse-morphism-image}}\<close>

theory InverseImageMorphismChoice
  imports ParticularStructureMorphisms MorphismImage
begin

context particular_struct_morphism
begin

definition same_image (infix \<open>\<sim>\<close> 75) where
  \<open>x \<sim> y \<equiv> x \<in> src.\<P> \<and> y \<in> src.\<P> \<and> \<phi> x = \<phi> y\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> same_image_I[intro!]:
  assumes \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> \<open>\<phi> x = \<phi> y\<close>
  shows \<open>x \<sim> y\<close>
  using assms by (auto simp: same_image_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> same_image_E[elim!]:
  assumes \<open>x \<sim> y\<close>
  obtains \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> \<open>\<phi> x = \<phi> y\<close>
  using assms by (auto simp: same_image_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> same_image_iff[simp]: \<open>x \<sim> y \<longleftrightarrow> x \<in> src.\<P> \<and> y \<in> src.\<P> \<and> \<phi> x = \<phi> y\<close>
  by (auto simp: same_image_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> same_image_sym[sym]: \<open>x \<sim> y \<Longrightarrow> y \<sim> x\<close> 
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> same_image_trans[trans]: \<open>\<lbrakk> x \<sim> y ; y \<sim> z \<rbrakk> \<Longrightarrow> x \<sim> z\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> same_image_refl[intro!]: \<open>x \<in> src.\<P> \<Longrightarrow> x \<sim> x\<close>
  by auto

definition \<open>eq_class x \<equiv> { y  . x \<sim> y }\<close>
 
lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_I[intro!]: \<open>x \<sim> y \<Longrightarrow> y \<in> eq_class x\<close> 
  by (auto simp: eq_class_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_D[dest!]: \<open>y \<in> eq_class x \<Longrightarrow> x \<sim> y\<close> 
  by (auto simp: eq_class_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_swap[simp]: \<open>y \<in> eq_class x \<longleftrightarrow> x \<in> eq_class y\<close> 
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_unique[simp]: \<open>\<lbrakk> x \<in> eq_class y ; x \<in> eq_class z \<rbrakk> \<Longrightarrow> eq_class x = eq_class z\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_subset_P[intro!]: \<open>eq_class x \<subseteq> src.\<P>\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_endurant_cases[cases set]:
  obtains 
    (eq_class_subst) \<open>eq_class x \<subseteq> src.\<S>\<close> 
  | (eq_class_moment) \<open>eq_class x \<subseteq> src.\<M>\<close>
proof (cases \<open>x \<in> src.\<P>\<close>)
  assume \<open>x \<in> src.\<P>\<close>
  then consider (substantial) \<open>x \<in> src.\<S>\<close>  | (moment) \<open>x \<in> src.\<M>\<close>
    by blast
  then show ?thesis
  proof (cases)
    case substantial
    then show ?thesis
      apply (intro that(1))
      using morph_preserves_substantials \<open>x \<in> src.\<P>\<close> 
      by (metis eq_class_D particular_struct_morphism.same_image_E particular_struct_morphism_axioms subsetI)      
  next
    case moment
    then show ?thesis 
      apply (intro that(2))
      using morph_preserves_moments \<open>x \<in> src.\<P>\<close>       
      by (metis eq_class_D morph_preserves_moments_simp particular_struct_morphism.same_image_E particular_struct_morphism_axioms subsetI)
  qed
next
  assume \<open>x \<notin> src.\<P>\<close>
  then have \<open>eq_class x = \<emptyset>\<close> by auto
  then show ?thesis using that by auto
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_moment[simp]: \<open>eq_class x \<subseteq> src.\<M> \<longleftrightarrow> x \<notin> src.\<S>\<close>
  apply (cases x rule: eq_class_endurant_cases ; safe ; simp add: eq_class_def)
  subgoal by blast
  subgoal by auto
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_substantial[simp]: \<open>eq_class x \<subseteq> src.\<S> \<longleftrightarrow> x \<notin> src.\<M>\<close>
  apply (cases x rule: eq_class_endurant_cases ; safe ; simp add: eq_class_def)
  subgoal by blast
  subgoal by auto  
  by (simp add: subset_iff)


definition \<open>eq_classes \<equiv> { eq_class x | x . x \<in> src.\<P> }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_classes_I[intro]: \<open>\<lbrakk> x \<in> src.\<P> ; X = eq_class x \<rbrakk> \<Longrightarrow> X \<in> eq_classes \<close>
  by (auto simp: eq_classes_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_classes_E[elim!]:
  assumes \<open>X \<in> eq_classes\<close>
  obtains x where \<open>x \<in> src.\<P>\<close> \<open>X = eq_class x\<close>
  using assms by (auto simp: eq_classes_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_classes_disj: \<open>\<lbrakk> X \<in> eq_classes ; Y \<in> eq_classes ; x \<in> X ; x \<in> Y \<rbrakk> \<Longrightarrow> X = Y\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_classes_un: \<open>\<Union> eq_classes = src.\<P>\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_classes_non_empty[dest]: \<open>X \<in> eq_classes \<Longrightarrow> X \<noteq> \<emptyset>\<close>
  by (auto simp: eq_classes_def eq_class_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_non_empty[simp]: \<open>eq_class x \<noteq> \<emptyset> \<longleftrightarrow> x \<in> src.\<P>\<close>
  by (auto simp: eq_class_def)

definition \<open>subst_eq_classes \<equiv> { X . X \<in> eq_classes \<and> X \<subseteq> src.\<S>}\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_classes_I: \<open>\<lbrakk> X \<in> eq_classes ; X \<subseteq> src.\<S> \<rbrakk> \<Longrightarrow> X \<in> subst_eq_classes\<close>
  by (auto simp: subst_eq_classes_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_classes_E: 
  assumes \<open>X \<in> subst_eq_classes\<close>
  obtains \<open>X \<in> eq_classes\<close> \<open>X \<subseteq> src.\<S>\<close>
  using assms by (auto simp: subst_eq_classes_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_classes_E1[elim!]: 
  assumes \<open>X \<in> subst_eq_classes\<close>
  obtains x where \<open>X \<in> eq_classes\<close> \<open>x \<in> X\<close> \<open>\<And>x. x \<in> X \<Longrightarrow> x \<in> src.\<S>\<close>
  using assms by (auto simp: subst_eq_classes_def)


lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_classes_iff: \<open>X \<in> subst_eq_classes \<longleftrightarrow> X \<in> eq_classes \<and> X \<subseteq> src.\<S>\<close>
  by (auto simp: subst_eq_classes_def)  

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_classes_I1[intro]: \<open>\<lbrakk> x \<in> src.\<S> ; X = eq_class x \<rbrakk> \<Longrightarrow> X \<in> subst_eq_classes\<close>
  by (auto simp: subst_eq_classes_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_classes_D1: \<open>\<lbrakk> X \<in> subst_eq_classes ; x \<in> X \<rbrakk> \<Longrightarrow> x \<in> src.\<S>\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_classes_D2: \<open>X \<in> subst_eq_classes \<Longrightarrow> X \<in> eq_classes\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_classes_disj[simp]: 
  \<open>\<lbrakk> X \<in> subst_eq_classes ; Y \<in> subst_eq_classes ; x \<in> X ; x \<in> Y \<rbrakk> \<Longrightarrow> X = Y\<close>
  using subst_eq_classes_D2 eq_classes_disj by metis
  

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_classes_un[simp]: \<open>\<Union> subst_eq_classes = src.\<S>\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_eq_class_non_empty[dest]: \<open>X \<in> subst_eq_classes \<Longrightarrow> X \<noteq> \<emptyset>\<close>
  by auto

end

context particular_struct_morphism_sig
begin


end

locale choice_function =
  fixes f :: \<open>'a set \<Rightarrow> 'a\<close> 
  assumes f_in_X1: \<open>\<forall>X. X \<noteq> \<emptyset> \<longrightarrow> f X \<in> X\<close>

locale particular_struct_morphism_with_choice =
    particular_struct_morphism where Typ\<^sub>p\<^sub>1 = Typ\<^sub>p\<^sub>1 and Typ\<^sub>p\<^sub>2 = Typ\<^sub>p\<^sub>2 and Typ\<^sub>q = Typ\<^sub>q + 
    choice_function f
  for 
    f :: \<open>'p\<^sub>1 set \<Rightarrow> 'p\<^sub>1\<close> and
    Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
    Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> 
begin

inductive_set delta :: \<open>('p\<^sub>2 \<times> 'p\<^sub>1) set\<close> (\<open>\<Delta>\<close>) 
  where
  delta_substantial: \<open>X \<in> subst_eq_classes \<Longrightarrow> (\<phi> (f X), f X) \<in> \<Delta>\<close>   
 | delta_moment: \<open>\<lbrakk> (x\<^sub>1,y\<^sub>1) \<in> \<Delta> ; x\<^sub>2 \<in> src.\<P> ; \<phi> x\<^sub>2 \<triangleleft>\<^sub>t x\<^sub>1 \<rbrakk> \<Longrightarrow> (\<phi> x\<^sub>2,f (eq_class x\<^sub>2)) \<in> \<Delta>\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> f_in_X[simp]: \<open>f X \<in> X \<longleftrightarrow> X \<noteq> \<emptyset>\<close> using f_in_X1 by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> f_eq_class[simp]: \<open>x \<in> src.\<P> \<Longrightarrow> \<phi> (f (eq_class x)) = \<phi> x\<close>  
  by (metis eq_class_def eq_class_non_empty f_in_X1 mem_Collect_eq same_image_E)

lemma \<^marker>\<open>tag (proof) aponly\<close> f_eq_class_in_end[intro!,simp]: \<open>x \<in> src.\<P> \<Longrightarrow> f (eq_class x) \<in> src.\<P>\<close>  
  by (metis eq_class_non_empty eq_class_unique f_in_X1)

lemma \<^marker>\<open>tag (proof) aponly\<close> x_sim_f_eq_class[simp,intro!]: \<open>x \<sim> f (eq_class x)\<close> if \<open>x \<in> src.\<P>\<close> for x
  by (auto simp:  that)

lemma \<^marker>\<open>tag (proof) aponly\<close> delta_dom:
  assumes  \<open>(x,y) \<in> \<Delta>\<close>  
  shows \<open>x \<in> \<phi> ` src.\<P> \<and> y \<in> src.\<P>\<close>
  using assms 
  by (induct rule: delta.induct ; safe? ; simp)

lemma \<^marker>\<open>tag (proof) aponly\<close> delta_domE:
  assumes  \<open>(x,y) \<in> \<Delta>\<close>  
  obtains z where \<open>z \<in> src.\<P>\<close> \<open>x = \<phi> z\<close> \<open>\<phi> z \<in> tgt.\<P>\<close> \<open>y \<in> src.\<P>\<close>
  using assms[THEN delta_dom] 
  by (elim conjE imageE ; simp add: morph_preserves_particulars)
 
lemma \<^marker>\<open>tag (proof) aponly\<close> delta_img: 
  assumes \<open>(x,y) \<in> \<Delta>\<close>
  shows \<open>\<phi> y = x\<close>
proof -          
  show ?thesis          
    using assms by (induct ; hypsubst_thin? ; simp)
qed

declare [[smt_timeout=600]]

lemma \<^marker>\<open>tag (proof) aponly\<close> delta_E1:
  assumes \<open>(x,y) \<in> \<Delta>\<close> 
  obtains x\<^sub>s where \<open>x = \<phi> x\<^sub>s\<close> \<open>y = f (eq_class x\<^sub>s)\<close>
  using assms apply (cases ; simp)  
  using f_eq_class by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> delta_E2:
  assumes \<open>(x,y) \<in> \<Delta>\<close> 
  obtains X where \<open>X \<in> eq_classes\<close> \<open>x = \<phi> y\<close> \<open>y = f X\<close>
  using assms apply (cases ; simp)  
  subgoal by auto
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> delta_single: 
  assumes \<open>(x,y\<^sub>1) \<in> \<Delta>\<close> \<open>(x,y\<^sub>2) \<in> \<Delta>\<close>
  shows \<open>y\<^sub>1 = y\<^sub>2\<close>
  using assms 
proof -
  obtain doms[simp,intro!]: \<open>y\<^sub>1 \<in> src.\<P>\<close> \<open>y\<^sub>2 \<in> src.\<P>\<close> \<open>x \<in> \<phi> ` src.\<P>\<close> 
      and phi_y[simp]: \<open>\<phi> y\<^sub>1 = x\<close> \<open>\<phi> y\<^sub>2 = x\<close>
    using assms 
    by (simp add: delta_dom delta_img)
  
  show ?thesis
    using assms doms phi_y
  proof (induct arbitrary: y\<^sub>2)
    show G1: \<open>f X = y\<^sub>2\<close> 
      if A: \<open>X \<in> subst_eq_classes\<close> \<open>(\<phi> (f X), y\<^sub>2) \<in> \<Delta>\<close>
        and doms: \<open>f X \<in> src.\<P>\<close> \<open>y\<^sub>2 \<in> src.\<P>\<close>
                  \<open>\<phi> (f X) \<in> \<phi> ` src.\<P>\<close>
                  \<open>\<phi> (f X) = \<phi> (f X)\<close>
                  \<open>\<phi> y\<^sub>2 = \<phi> (f X)\<close>
                for X y\<^sub>2
    proof -
      have B: \<open>f X \<in> src.\<S>\<close> using A by blast
      then have C: \<open>\<phi> (f X) \<in> tgt.\<S>\<close> using morph_preserves_substantials by blast
      from doms(2) show \<open>f X = y\<^sub>2\<close>     
      proof (cases y\<^sub>2 rule: src.endurant_cases)
        assume substantial: \<open>y\<^sub>2 \<in> src.\<S>\<close>
        then obtain D: \<open>\<phi> y\<^sub>2 \<in> tgt.\<S>\<close> \<open>\<phi> (f X) \<in> tgt.\<S>\<close>
          using \<open>f X \<in> src.\<S>\<close> by (meson inherence_sig.\<S>_E morph_preserves_substantials)        
        show ?thesis using A(2)
          apply (cases rule: delta.cases)
           subgoal by (metis (mono_tags, lifting) A(1) B doms(2) eq_class_I eq_classes_I f_in_X1 mem_Collect_eq particular_struct_morphism.eq_classes_disj particular_struct_morphism.same_image_I particular_struct_morphism_axioms src.endurantI3 subst_eq_class_non_empty subst_eq_classes_def)
           using C by auto
      next
        assume moment: \<open>y\<^sub>2 \<in> src.\<M>\<close>
        show ?thesis using A(2)
          apply (cases)
          subgoal  using moment by blast        
          by (metis C inherence_sig.\<M>_I inherence_sig.\<S>_E)        
      qed
    qed  

    fix x\<^sub>3 y\<^sub>3 x\<^sub>4 y\<^sub>4
    assume A: \<open>(x\<^sub>3, y\<^sub>3) \<in> \<Delta>\<close> 
              \<open>\<And>y\<^sub>2. \<lbrakk> (x\<^sub>3, y\<^sub>2) \<in> \<Delta> 
                    ;  y\<^sub>3 \<in> src.\<P>
                    ;  y\<^sub>2 \<in> src.\<P>
                    ;  x\<^sub>3 \<in> \<phi> ` src.\<P>
                    ;  \<phi> y\<^sub>3 = x\<^sub>3 
                    ;  \<phi> y\<^sub>2 = x\<^sub>3 \<rbrakk> \<Longrightarrow> y\<^sub>3 = y\<^sub>2\<close>
              \<open>x\<^sub>4 \<in> src.\<P>\<close>
              \<open>\<phi> x\<^sub>4 \<triangleleft>\<^sub>t x\<^sub>3\<close>
              \<open>(\<phi> x\<^sub>4, y\<^sub>4) \<in> \<Delta>\<close>
              \<open>f (eq_class x\<^sub>4) \<in> src.\<P>\<close>
              \<open>y\<^sub>4 \<in> src.endurants\<close>
              \<open>\<phi> x\<^sub>4 \<in> \<phi> ` src.endurants\<close>
              \<open>\<phi> (f (eq_class x\<^sub>4)) = \<phi> x\<^sub>4\<close>
              \<open>\<phi> y\<^sub>4 = \<phi> x\<^sub>4\<close>
    then have \<open>eq_class x\<^sub>4 = eq_class y\<^sub>4\<close> using A(3) A(7) by auto
    obtain Y where Y: \<open>Y \<in> eq_classes\<close> \<open>y\<^sub>4 = f Y\<close> 
      using delta_E2[OF \<open>(\<phi> x\<^sub>4, y\<^sub>4) \<in> \<Delta>\<close>] by metis
    have \<open>Y = eq_class y\<^sub>4\<close>  using Y(1) Y(2) eq_class_unique by blast
    then have \<open>f (eq_class y\<^sub>4) = y\<^sub>4\<close> using Y(2) by simp     
    then show \<open>f (eq_class x\<^sub>4) = y\<^sub>4\<close> 
      using \<open>eq_class x\<^sub>4 = eq_class y\<^sub>4\<close> by simp
  qed
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> delta_range: 
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close>
  shows \<open>\<exists>y. (x,y) \<in> \<Delta>\<close>
  using assms 
  apply (induct x rule: wfP_induct[OF tgt.inherence_is_noetherian] ; simp)
proof -
  fix x
  assume A: \<open>\<forall>y. x \<triangleleft>\<^sub>t y \<longrightarrow> y \<in> \<phi> ` src.\<P> \<longrightarrow> (\<exists>ya. (y, ya) \<in> \<Delta>)\<close>
        \<open>x \<in> \<phi> ` src.\<P>\<close>
  then obtain x\<^sub>s where B[simp]: \<open>x = \<phi> x\<^sub>s\<close> \<open>x\<^sub>s \<in> src.\<P>\<close> using A(2) by blast  
  have D: \<open>eq_class x\<^sub>s \<in> subst_eq_classes\<close> if \<open>x\<^sub>s \<in> src.\<S>\<close>
    using that by auto
  have E: \<open>\<phi> (f (eq_class x\<^sub>s)) = \<phi> x\<^sub>s\<close> using B(2) by simp

  have substantial: \<open>\<exists>y. (\<phi> x\<^sub>s, y) \<in> \<Delta>\<close> if \<open>x\<^sub>s \<in> src.\<S>\<close>
  proof-
    have \<open>(\<phi> x\<^sub>s, f (eq_class x\<^sub>s)) \<in> \<Delta>\<close> if \<open>x\<^sub>s \<in> src.\<S>\<close> 
      using delta.intros(1)[OF D,simplified E,OF that] .  
    then show ?thesis
      using that by blast
  qed

  have moment: \<open>\<exists>y. (\<phi> x\<^sub>s, y) \<in> \<Delta>\<close> if as: \<open>x\<^sub>s \<in> src.\<M>\<close>
  proof-
    obtain y\<^sub>s where F: \<open>x\<^sub>s \<triangleleft>\<^sub>s y\<^sub>s\<close> using as by blast
    then obtain G: \<open>y\<^sub>s \<in> src.\<P>\<close> \<open>\<phi> x\<^sub>s \<triangleleft>\<^sub>t \<phi> y\<^sub>s\<close>
      using morph_reflects_inherence by auto
    then have H: \<open>\<phi> y\<^sub>s \<in> \<phi> ` src.\<P>\<close> by blast
    obtain y where I: \<open>(\<phi> y\<^sub>s,y) \<in> \<Delta>\<close> 
      using A(1)[rule_format,simplified,OF G(2) H]  by blast
    have \<open>(\<phi> x\<^sub>s, f (eq_class x\<^sub>s)) \<in> \<Delta>\<close>
      using delta.intros(2)[OF I B(2) G(2)] by blast
    then show ?thesis by blast
  qed
  
  show \<open>\<exists>y. (x, y) \<in> \<Delta>\<close>
    apply (simp)
    using B(2) apply (cases x\<^sub>s rule: src.endurant_cases)
    using substantial moment by auto
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> delta_inj:
  assumes \<open>(x\<^sub>1,y) \<in> \<Delta>\<close> \<open>(x\<^sub>2,y) \<in> \<Delta>\<close>
  shows \<open>x\<^sub>1 = x\<^sub>2\<close>
  using assms delta_img by auto

definition someInvMorph :: \<open>'p\<^sub>2 \<Rightarrow> 'p\<^sub>1\<close> where
  \<open>someInvMorph x \<equiv> if x \<in> \<phi> ` src.\<P> then THE y. (x,y) \<in> \<Delta> else undefined\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_ex: 
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close>
  shows \<open>\<exists>!y. (x,y) \<in> \<Delta>\<close>
  using assms 
  by (intro ex_ex1I ; simp add: delta_range delta_single)

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_eq_iff:
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close>
  shows \<open>someInvMorph x = y \<longleftrightarrow> (x,y) \<in> \<Delta>\<close>
  apply (simp add: someInvMorph_def assms)
  apply (rule the1I2[OF someInvMorph_ex[OF assms]] ; intro iffI ; simp?)
  using delta_single by simp

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_inj_phi_img: \<open>inj_on someInvMorph (\<phi> ` src.\<P>)\<close>
  apply (intro inj_onI)
  subgoal premises P for x y
    supply S = P(1,2)[THEN someInvMorph_eq_iff,simplified P(3)] 
    using S(1)[simplified S(2)]        
    by (meson P(1) delta_range delta_inj)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_delta_I[intro!]:
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y = someInvMorph x\<close>
  shows \<open>(x,y) \<in> \<Delta>\<close>
  using assms someInvMorph_eq_iff by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_delta_E:
  assumes  \<open>(x,y) \<in> \<Delta>\<close>
  obtains \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y = someInvMorph x\<close>
  using assms 
  by (metis delta_dom someInvMorph_eq_iff)

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_phi_phi[simp]: 
  assumes \<open>x \<in> src.\<P>\<close>
  shows \<open>\<phi> (someInvMorph (\<phi> x)) = \<phi> x\<close>
  apply (simp add: someInvMorph_def imageI[OF assms])
  apply (rule the1I2[of \<open>\<lambda>y. (\<phi> x, y) \<in> \<Delta>\<close>])
  subgoal using assms by (simp add: someInvMorph_ex)
  using assms delta_img by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_as_inv[simp]: \<open>x \<in> \<phi> ` src.\<P> \<Longrightarrow> \<phi> (someInvMorph x) = x\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_delta_simp:  \<open>(x,y) \<in> \<Delta> \<longleftrightarrow> x \<in> \<phi> ` src.\<P> \<and> y = someInvMorph x\<close>  
  using someInvMorph_delta_E by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_image: \<open>someInvMorph ` \<phi> ` src.\<P> \<subseteq> src.\<P>\<close>  
  using delta_dom by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorphImgUnique: 
  assumes \<open>x \<sim> y\<close> \<open>x \<in> someInvMorph ` \<phi> ` src.\<P>\<close> \<open>y \<in> someInvMorph ` \<phi> ` src.\<P>\<close>
  shows \<open>x = y\<close>
  using assms 
  by auto



context
begin

interpretation img: particular_struct_surjection \<Gamma>\<^sub>1 \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> \<phi>  
  by simp

declare img.morph_is_surjective[simp del]

private lemma someInvMorph_undef[simp]: 
  \<open>someInvMorph \<in> extensional img.tgt.endurants\<close>
  apply (simp only: extensional_def ; intro CollectI)
  apply (intro allI impI)
  subgoal for x
    apply (cases \<open>x \<in> \<phi> ` src.\<P>\<close>
        ; simp add: possible_worlds_sig.\<P>_def
        ; simp add: someInvMorph_def ; safe)
    subgoal by blast    
    by (simp add: src.\<P>_def)
  done

interpretation some_inv_to_some_inv_img: particular_struct_bijection_1 \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> someInvMorph \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>1)\<close>
  apply (intro img.tgt.inj_morph_img_isomorphism[simplified morph_image_tgt_struct])
  subgoal using someInvMorph_inj_phi_img img.morph_is_surjective by auto  
  subgoal using src.injection_to_ZF_exist by blast
  subgoal using someInvMorph_undef by simp
  subgoal
    apply (auto simp: possible_worlds_sig.\<P>_def someInvMorph_def)
    by (metis delta_dom morph_image_I morph_image_def someInvMorph_def
        someInvMorph_delta_simp src.\<P>_E src.\<P>_I 
        src.undefined_not_in_particulars)
  done

private lemma \<^marker>\<open>tag (proof) aponly\<close> A1[simp]: \<open>some_inv_to_some_inv_img.tgt.\<Q>\<S> = src.\<Q>\<S>\<close>
  by auto

private lemma \<^marker>\<open>tag (proof) aponly\<close> S1[simp]: \<open>some_inv_to_some_inv_img.tgt.endurants = someInvMorph ` \<phi> ` src.\<P>\<close>
  using img.morph_is_surjective
  by auto

private lemma \<^marker>\<open>tag (proof) aponly\<close> C1: \<open>someInvMorph ` \<phi> ` src.\<P> \<subseteq> src.\<P>\<close>    
    using someInvMorph_image by blast

private lemma \<^marker>\<open>tag (proof) aponly\<close> A2: \<open>x \<in> src.\<P>\<close> if \<open>x \<in> someInvMorph ` \<phi> ` src.\<P>\<close> for x
    using C1 that by blast

private lemma \<^marker>\<open>tag (proof) aponly\<close> A3[simp]: \<open>some_inv_to_some_inv_img.img_inheres_in x y \<longleftrightarrow> 
              (\<exists>x\<^sub>1 y\<^sub>1. img.src_inheres_in x\<^sub>1 y\<^sub>1 \<and> x = someInvMorph (\<phi> x\<^sub>1) \<and> y = someInvMorph(\<phi> y\<^sub>1))\<close> for x y
    apply (intro iffI ; (elim exE conjE)? ; hypsubst_thin?)
    subgoal  by (metis delta_dom morph_image_inheres_in_E morph_reflects_inherence
                  someInvMorph_as_inv someInvMorph_delta_I 
                  some_inv_to_some_inv_img.inv_inheres_in_reflects 
                  some_inv_to_some_inv_img.inv_morph_morph 
                  some_inv_to_some_inv_img.tgt.inherence_scope)
    subgoal for x\<^sub>1 y\<^sub>1      
      by blast      
    done

private lemma \<^marker>\<open>tag (proof) aponly\<close> A4[simp]: \<open>some_inv_to_some_inv_img.img_towards x y \<longleftrightarrow>
      (\<exists>x\<^sub>1 y\<^sub>1. img.src_towards x\<^sub>1 y\<^sub>1 \<and> x = someInvMorph (\<phi> x\<^sub>1) \<and> y = someInvMorph(\<phi> y\<^sub>1))\<close> for x y
    apply (intro iffI ; (elim exE conjE)? ; hypsubst_thin?)
    subgoal  
      by (metis S1 delta_dom img.I_img_eq_tgt_I morph_image_def morph_image_towards_D 
          morph_reflects_towardness someInvMorph_as_inv someInvMorph_delta_I 
          some_inv_to_some_inv_img.inv_morph_morph 
          some_inv_to_some_inv_img.inv_towardness_reflects 
          some_inv_to_some_inv_img.morph_image_towards_D(1,2))
    subgoal for x\<^sub>1 y\<^sub>1      
      apply (simp only: particular_struct_morphism_image_simps)
      by blast
    done

private lemma \<^marker>\<open>tag (proof) aponly\<close> A5[simp]: \<open>some_inv_to_some_inv_img.img_assoc_quale x q \<longleftrightarrow>
      (\<exists>y. img.src_assoc_quale y q \<and> x = someInvMorph (\<phi> y))\<close> for x  q
    apply (intro iffI ; (elim exE conjE)? ; hypsubst_thin?)
    subgoal  
      by (metis delta_E2 delta_dom img.I_img_eq_tgt_I morph_image_def morph_image_dests(9) 
                morph_reflects_quale_assoc someInvMorph_delta_I 
                some_inv_to_some_inv_img.I_img_eq_tgt_I 
                some_inv_to_some_inv_img.morph_image_E 
                some_inv_to_some_inv_img.morph_image_iff 
                some_inv_to_some_inv_img.morph_reflects_quale_assoc 
                some_inv_to_some_inv_img.tgt.assoc_quale_scopeD(1)  
                src.\<P>_def)
    subgoal for x\<^sub>1       
      apply (simp only: particular_struct_morphism_image_simps)
      by blast
    done

private lemma \<^marker>\<open>tag (proof) aponly\<close> ex_simp1: \<open>(\<exists>x \<in> X. y = x) \<longleftrightarrow> y \<in> X\<close> for y :: 'p\<^sub>1 and X by blast

private lemma \<^marker>\<open>tag (proof) aponly\<close> A6: \<open>\<exists>y\<in>someInvMorph ` \<phi> ` src.\<P>. z = y\<close> 
    if as: \<open>x \<in> someInvMorph ` \<phi> ` src.\<P>\<close> \<open>img.src_towards x z\<close> for x z
  proof (simp only: ex_simp1)
    obtain y where Y: \<open>y \<in> src.\<P>\<close> \<open>x = someInvMorph (\<phi> y)\<close>
      using as imageE by blast
    have AA: \<open>img.src_towards (someInvMorph (\<phi> y)) z\<close> using as(2) Y by simp
    then have \<open>img.tgt_towards (\<phi> (someInvMorph (\<phi> y))) (\<phi> z)\<close>
      using Y(1)
      by (meson particular_struct_morphism_image_simps(5))
    then have \<open>img.tgt_towards (\<phi> y) (\<phi> z)\<close>
      using someInvMorph_phi_phi Y by simp 
    then have \<open>some_inv_to_some_inv_img.tgt_towards (someInvMorph (\<phi> y)) (someInvMorph (\<phi> z))\<close>
      apply (simp only: particular_struct_morphism_image_simps ; elim exE conjE)
      by blast
    then have \<open>some_inv_to_some_inv_img.tgt_towards x (someInvMorph (\<phi> z))\<close>
      using Y(2) by simp
    then have BB: \<open>img.src_towards x (someInvMorph (\<phi> z))\<close>
      by (metis A2 Y(2) \<open>some_inv_to_some_inv_img.src_towards (\<phi> (someInvMorph (\<phi> y))) (\<phi> z)\<close> 
            img.I_img_eq_tgt_I img.morph_reflects_towardness morph_image_def 
            morph_image_towards_D(2) someInvMorph_as_inv 
            some_inv_to_some_inv_img.morph_image_towards_D(2) that(1))
    have CC: \<open>someInvMorph (\<phi> z) = z\<close> 
      using src.towardness_single as(2) BB by simp
    then show \<open>z \<in> someInvMorph ` \<phi> ` src.endurants\<close>
      using CC 
      by (metis \<open>some_inv_to_some_inv_img.src_towards (\<phi> y) (\<phi> z)\<close> 
            image_eqI morph_image_towards_E)      
  qed 
  
interpretation some_inv_img_to_src: 
  pre_particular_struct_morphism 
    \<open>MorphImg (someInvMorph \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>) \<Gamma>\<^sub>1\<close> 
    \<Gamma>\<^sub>1 
    \<open>id_on (someInvMorph ` \<phi> ` src.\<P>)\<close> 
    \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>1)\<close>  
proof -      
  let ?P1 = \<open>someInvMorph ` \<phi> ` src.\<P>\<close>
  interpret M: particular_struct_morphism_sig 
                \<open>MorphImg (someInvMorph \<circ>\<^bsub>src.\<P>\<^esub> \<phi>) \<Gamma>\<^sub>1\<close> 
                \<Gamma>\<^sub>1 \<open>id_on ?P1\<close> 
                \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>1)\<close> .
  interpret S: particular_struct \<open>MorphImg (someInvMorph \<circ>\<^bsub>M.tgt.\<P>\<^esub> \<phi>) \<Gamma>\<^sub>1\<close>
  proof (intro_locales)
    show G1: \<open>possible_worlds M.src.\<W>\<close>
      apply (unfold_locales)
      subgoal G1_1 by (simp add: src.injection_to_ZF_exist)
      subgoal G1_2 using some_inv_to_some_inv_img.tgt.at_least_one_possible_world by auto      
      subgoal G1_3 by (simp add: some_inv_to_some_inv_img.tgt.particulars_do_not_exist_in_some_world)            
      by (simp add: some_inv_to_some_inv_img.tgt.undefined_not_in_particulars)
    show G2: \<open>inherence_base_axioms M.src.\<W> M.src_inheres_in\<close>
      apply (unfold_locales)
      subgoal G2_1 using some_inv_to_some_inv_img.tgt.inherence_scope by force
      subgoal G2_2 by (simp add: some_inv_to_some_inv_img.tgt.inherence_imp_ed)      
      by (metis some_inv_to_some_inv_img.tgt.moment_non_migration src.morph_img_comp)
    show G3: \<open>noetherian_inherence_axioms M.src_inheres_in\<close> 
      apply (unfold_locales)      
      by (metis some_inv_to_some_inv_img.tgt.just_noetherian_inherence_axioms src.morph_img_comp)      
    show G4: \<open>inherence_axioms M.src_inheres_in\<close>
      apply (unfold_locales)      
      by (metis some_inv_to_some_inv_img.tgt.just_inherence_axioms src.morph_img_comp)       
    show G5: \<open>quality_space M.src.\<Q>\<S>\<close>
      apply (unfold_locales)
      subgoal G5_1 using src.no_empty_quality_space by auto      
      by (simp add: src.quality_spaces_are_disjoint)      
    show G6: \<open>qualified_particulars_axioms M.src.\<W> M.src_inheres_in M.src.\<Q>\<S> M.src_assoc_quale\<close> 
      apply (unfold_locales)
      subgoal G6_1 
        by (metis some_inv_to_some_inv_img.tgt.assoc_quale_scope src.morph_img_comp)
      subgoal G6_2 
        by (simp add: some_inv_to_some_inv_img.tgt.assoc_quale_unique)
      subgoal G6_3 
        using some_inv_to_some_inv_img.tgt.quality_moment_unique_by_quality_space 
        by force 
      subgoal G6_4 
        using some_inv_to_some_inv_img.tgt.every_quality_space_is_used by force      
      by (metis some_inv_to_some_inv_img.tgt.quale_determines_moment src.morph_img_comp)      
    show G7: \<open>towardness_axioms M.src.\<W> M.src_inheres_in M.src_towards\<close>
      apply (unfold_locales)
      subgoal G7_1 
         by (metis some_inv_to_some_inv_img.tgt.towardness_apply_to_moments
              some_inv_to_some_inv_img.tgt.towardness_scopeD(4) src.morph_img_comp)
      subgoal G7_2 by (simp add: some_inv_to_some_inv_img.tgt.towardness_imp_ed)
      subgoal G7_3 
        by (metis some_inv_to_some_inv_img.tgt.towardness_diff_ultimate_bearers src.morph_img_comp)
      by (metis some_inv_to_some_inv_img.tgt.towardness_single src.morph_img_comp)       
    show G8: \<open>ufo_particular_theory_axioms M.src_inheres_in M.src_assoc_quale\<close>
      apply (unfold_locales)      
      by (metis 
          some_inv_to_some_inv_img.tgt.qualified_particulars_are_not_bearers src.morph_img_comp)      
  qed
  have id_on_simp1[simp]: \<open>id_on ?P1 x = x\<close> if \<open>x \<in> S.\<S>\<close> for x
    apply (rule id_on_eq(1))
    using that by (metis S.endurantI3 S1 src.morph_img_comp)
  have id_on_simp2[simp]: \<open>id_on ?P1 x = x\<close> if \<open>x \<in> S.\<M>\<close> for x
    apply (rule id_on_eq(1))
    using that 
    by (metis S.endurantI1 morph_image_particulars
        some_inv_to_some_inv_img.morph_is_surjective src.morph_img_comp) 
  have id_on_simp3[simp]: \<open>id_on ?P1 x = x\<close> if \<open>x \<in> S.\<P>\<close> for x
    apply (rule id_on_eq(1))
    using that by (metis S1 src.morph_img_comp)
  have id_on_undef[iff]: \<open>id_on ?P1 x = undefined \<longleftrightarrow> x \<notin> ?P1\<close> for x
    apply (cases \<open>x \<in> M.tgt.endurants\<close> ; simp)    
    subgoal 
       by (metis id_on_eq(1) id_on_eq(2) morph_image_particulars 
                some_inv_to_some_inv_img.undefined_not_in_img)
    by (meson A2 id_on_eq(2))
  have lift_world_subset: 
      \<open>someInvMorph ` \<phi> ` M.tgt.endurants \<subseteq> M.tgt.endurants\<close>
    apply (auto)    
    using A2 by blast  
  have S_subset: \<open>some_inv_to_some_inv_img.tgt.\<S> \<subseteq> M.tgt.\<S>\<close>
    apply auto
    subgoal using A2 by blast
    by (metis img.morph_preserves_moments_simp someInvMorph_phi_phi
          some_inv_to_some_inv_img.morph_preserves_moments src.endurantI1)
  have M_subset: \<open>some_inv_to_some_inv_img.tgt.\<M> \<subseteq> M.tgt.\<M>\<close>
    apply auto
    by (metis A2 img.morph_preserves_moments_simp morph_image_particulars 
        someInvMorph_as_inv some_inv_to_some_inv_img.I_img_eq_tgt_I 
        some_inv_to_some_inv_img.morph_image_E 
        some_inv_to_some_inv_img.morph_image_def 
        some_inv_to_some_inv_img.morph_preserves_moments_simp 
        some_inv_to_some_inv_img.tgt.endurantI1)
  show \<open>pre_particular_struct_morphism 
          (MorphImg (someInvMorph \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>) \<Gamma>\<^sub>1) \<Gamma>\<^sub>1 
          (id_on ?P1)\<close>  
    apply (unfold_locales)
    subgoal G1      
      apply (intro id_on_extensional)?
      by (auto simp: S_subset)
    subgoal G2
      apply (intro id_on_extensional)?
      subgoal using S.moments_are_endurants by auto
      by (auto simp: M_subset)
    subgoal G3 by auto      
    subgoal G4 by auto
    subgoal G5 
      apply auto
      subgoal G5_1 by (metis someInvMorph_phi_phi)
      by (metis A2 S1 img.morph_preserves_particulars 
          img.morph_reflects_inherence someInvMorph_phi_phi
          some_inv_to_some_inv_img.morph_preserves_particulars src.inherence_scope) 
    subgoal G6 for x y
      apply (auto)
      subgoal for z t
        apply (rule exI[of _ z] ; rule exI[of _ t] ; simp)
        by (metis morph_reflects_towardness someInvMorph_phi_phi
            src.towardness_scopeD(2) src.towardness_scopeD(3))
      subgoal for z t o p
        by (metis A2 img.I_img_eq_tgt_I img.morph_reflects_towardness 
            morph_image_towards particular_struct_morphism_sig.morph_image_def 
            someInvMorph_phi_phi some_inv_to_some_inv_img.morph_image_I 
            src.towardness_scopeD(2) src.towardness_scopeD(3))
      done
    subgoal G7  by (metis A6 S1 id_on_simp3 src.morph_img_comp)
    subgoal G8 for x q
      apply auto
      by (metis A2 S1 img.morph_preserves_particulars 
          img.morph_reflects_quale_assoc someInvMorph_phi_phi 
          some_inv_to_some_inv_img.morph_preserves_particulars 
          src.assoc_quale_scopeD(1))
    done
qed

private lemma \<^marker>\<open>tag (proof) aponly\<close> A7: \<open>\<exists>w\<^sub>s \<in> src.\<W>. w \<subseteq> w\<^sub>s\<close> if as: \<open>w \<in> some_inv_to_some_inv_img.\<W>\<^sub>\<phi>\<close> for w
  proof (rule ccontr ; simp)
    assume AA: \<open>\<forall>x\<in>src.\<W>. \<not> w \<subseteq> x\<close>
    then have BB: False if \<open>w\<^sub>1 \<in> src.\<W>\<close> \<open>w \<subseteq> w\<^sub>1\<close> for w\<^sub>1 using that by metis
    obtain w\<^sub>2 where CC: \<open>some_inv_to_some_inv_img.world_corresp w\<^sub>2 w\<close> using as by blast
    then obtain DD: \<open>w\<^sub>2 \<in> some_inv_to_some_inv_img.src.\<W>\<close>
                \<open>\<And>x. x \<in> some_inv_to_some_inv_img.src.\<P> \<Longrightarrow> x \<in> w\<^sub>2 \<longleftrightarrow> someInvMorph x \<in> w\<close>
      using some_inv_to_some_inv_img.world_corresp_E[OF CC] by metis
    have EE: \<open>w\<^sub>2 \<in> ((`) \<phi>) ` src.\<W>\<close> using DD(1) by (simp add: morph_image_worlds_src)
    then obtain w\<^sub>3 where FF: \<open>w\<^sub>2 = \<phi> ` w\<^sub>3\<close> \<open>w\<^sub>3 \<in> src.\<W>\<close> by blast
    have GG: \<open>\<And>x. x \<in> \<phi> ` src.\<P> \<Longrightarrow> x \<in> \<phi> ` w\<^sub>3 \<longleftrightarrow> someInvMorph x \<in> w\<close>
      using DD(2) img.morph_is_surjective by (simp only: FF(1) ; simp)
    have HH: \<open>\<And>x. x \<in> \<phi> ` w\<^sub>3 \<Longrightarrow> someInvMorph x \<in> w\<close> 
      using GG src.worlds_are_made_of_particulars FF(2) by blast
    then have II: \<open>\<And>x. x \<in> w\<^sub>3 \<Longrightarrow> someInvMorph (\<phi> x) \<in> w\<close> by blast
    then have JJ: \<open>\<And>x. x \<in> w\<^sub>3 \<Longrightarrow> \<phi> (someInvMorph (\<phi> x)) \<in> \<phi> ` w\<close> by blast    
    then have KK: \<open>\<And>x. x \<in> w\<^sub>3 \<Longrightarrow> (\<phi> x) \<in> \<phi> ` w\<close> 
      using FF(2) src.\<P>_I by auto
    show False
      by (metis A2 BB DD(1) DD(2) img.morph_worlds_correspond_tgt_src 
          img.world_corresp_def morph_image_particulars 
          someInvMorph_as_inv some_inv_to_some_inv_img.I_img_eq_tgt_I 
          some_inv_to_some_inv_img.morph_image_iff 
          some_inv_to_some_inv_img.morph_is_surjective some_inv_to_some_inv_img.tgt.\<P>_I 
          subsetI that)
  qed

private abbreviation srcWorlds (\<open>\<W>\<^sub>A\<close>) where \<open>\<W>\<^sub>A \<equiv> src.\<W>\<close>

private abbreviation srcParticulars (\<open>\<P>\<^sub>A\<close>) where \<open>\<P>\<^sub>A \<equiv> src.\<P>\<close>

private abbreviation srcInheresIn (infix \<open>\<triangleleft>\<^sub>A\<close> 75) where
  \<open>(\<triangleleft>\<^sub>A) \<equiv> src_inheres_in\<close>

private abbreviation srcAssocQuale (infix \<open>\<leadsto>\<^sub>A\<close> 75) where
  \<open>(\<leadsto>\<^sub>A) \<equiv> src_assoc_quale\<close>

private abbreviation srcQualia (\<open>\<Q>\<^sub>A\<close>) where
  \<open>\<Q>\<^sub>A \<equiv> img.\<Q>\<^sub>s\<close>

private abbreviation srcQualitySpaces (\<open>\<Q>\<S>\<^sub>A\<close>) where
  \<open>\<Q>\<S>\<^sub>A \<equiv> some_inv_img_to_src.tgt.\<Q>\<S>\<close>

private abbreviation revImageParticulars (\<open>\<P>\<^sub>R\<close>) where \<open>\<P>\<^sub>R \<equiv> some_inv_to_some_inv_img.tgt.endurants\<close>

private abbreviation revImageInheresIn (infix \<open>\<triangleleft>\<^sub>R\<close> 75) where
  \<open>(\<triangleleft>\<^sub>R) \<equiv> some_inv_img_to_src.src_inheres_in\<close>

private lemma \<^marker>\<open>tag (proof) aponly\<close> some_inv_to_some_inv_img_img_inheres_in_eq: \<open>some_inv_to_some_inv_img.img_inheres_in = (\<triangleleft>\<^sub>R)\<close>
  by (intro ext ; simp)

private abbreviation revImageAssocQuale (infix \<open>\<leadsto>\<^sub>R\<close> 75) where
  \<open>(\<leadsto>\<^sub>R) \<equiv> some_inv_to_some_inv_img.img_assoc_quale\<close>

private abbreviation revImageQualia (\<open>\<Q>\<^sub>R\<close>) where
  \<open>\<Q>\<^sub>R \<equiv> some_inv_img_to_src.\<Q>\<^sub>s\<close>

private abbreviation revImageWorldCorresp (infix \<open>\<Leftrightarrow>\<^sub>R\<close> 75) where
  \<open>(\<Leftrightarrow>\<^sub>R) \<equiv> some_inv_img_to_src.world_corresp\<close>

private abbreviation revImageWorlds (\<open>\<W>\<^sub>R\<close>) where
  \<open>\<W>\<^sub>R \<equiv> some_inv_img_to_src.src.\<W>\<close>

private lemma \<^marker>\<open>tag (proof) aponly\<close> some_inv_to_some_inv_img_\<W>\<^sub>\<phi>: \<open>some_inv_to_some_inv_img.\<W>\<^sub>\<phi> = \<W>\<^sub>R\<close>
  by auto

private abbreviation imageInheresIn (infix \<open>\<triangleleft>\<^sub>I\<close> 75) where
  \<open>(\<triangleleft>\<^sub>I) \<equiv> img.tgt_inheres_in\<close>

private abbreviation imageWorlds (\<open>\<W>\<^sub>I\<close>) where
  \<open>\<W>\<^sub>I \<equiv> img.tgt.\<W>\<close>

private abbreviation imageAssocQuale (infix \<open>\<leadsto>\<^sub>I\<close> 75) where
  \<open>(\<leadsto>\<^sub>I) \<equiv> img.tgt_assoc_quale\<close>

private abbreviation imageQualia (\<open>\<Q>\<^sub>I\<close>) where
  \<open>\<Q>\<^sub>I \<equiv> img.\<Q>\<^sub>t\<close>

private abbreviation imageParticulars (\<open>\<P>\<^sub>I\<close>) where \<open>\<P>\<^sub>I \<equiv> img.tgt.\<P>\<close>

private abbreviation imageWorldCorresp (infix \<open>\<Leftrightarrow>\<^sub>I\<close> 75) where
  \<open>(\<Leftrightarrow>\<^sub>I) \<equiv> img.world_corresp\<close>

private abbreviation someInvMorphAbbrev (\<open>\<phi>\<^sub>\<leftarrow>\<close>) where
  \<open>\<phi>\<^sub>\<leftarrow> \<equiv> someInvMorph\<close>

interpretation some_inv_img_to_src: 
  particular_struct_morphism_sig 
    \<open>MorphImg (someInvMorph \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>) \<Gamma>\<^sub>1\<close> 
    \<Gamma>\<^sub>1 
    \<open>id_on (someInvMorph ` \<phi> ` src.\<P>)\<close> 
    \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>1)\<close> .

interpretation some_inv_img_to_src: 
  particular_struct_morphism 
    \<open>MorphImg (\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>) \<Gamma>\<^sub>1\<close> 
    \<Gamma>\<^sub>1 
    \<open>id_on (\<phi>\<^sub>\<leftarrow> ` \<phi> ` \<P>\<^sub>A)\<close> 
    \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>1)\<close>  
proof (unfold_locales) 
  show \<open>w\<^sub>s \<in> \<W>\<^sub>R \<Longrightarrow> \<exists>w\<^sub>t. w\<^sub>s \<Leftrightarrow>\<^sub>R w\<^sub>t\<close> for w\<^sub>s
    apply (auto ; simp only: particular_struct_morphism_sig.world_corresp_def)
    apply (simp only: particular_struct_morphism_image_simps
                  possible_worlds_sig.\<P>_def id_def ; simp)
    apply (elim exE conjE ; simp)
    subgoal for w\<^sub>1 w\<^sub>2
      apply (intro exI[of _ w\<^sub>2]) (* apply (intro exI[of _ w\<^sub>s]) *)
      apply (intro conjI allI impI ballI iffI ; (elim exE conjE)? ; simp? ; hypsubst_thin?)
      subgoal for _ y _ w\<^sub>4 
        apply (auto)
        subgoal for t u
          apply (cases \<open>\<phi>\<^sub>\<leftarrow> (\<phi> u) \<in> \<phi>\<^sub>\<leftarrow> ` \<phi> ` \<Union> \<W>\<^sub>A\<close> ; simp)
          subgoal 
            by (metis A2 img.morph_worlds_correspond_src_tgt
                img.world_corresp_def someInvMorph_phi_phi src.\<P>_I src.\<P>_def)
          by blast
        done
      subgoal for _ y _ w\<^sub>4 
        apply (auto)
        by (metis id_on_eq(1) image_eqI someInvMorph_phi_phi 
              src.\<P>_I src.\<P>_def)
      done
    done  
  show  \<open>\<exists>w\<^sub>s. w\<^sub>s \<Leftrightarrow>\<^sub>R w\<^sub>t\<close> if as: \<open>w\<^sub>t \<in> \<W>\<^sub>A\<close> for w\<^sub>t
  proof -
    have R1: \<open>w\<^sub>t \<inter> \<phi>\<^sub>\<leftarrow> ` \<phi> ` \<P>\<^sub>A = \<phi>\<^sub>\<leftarrow> ` \<phi> ` w\<^sub>t\<close>
      apply auto
      subgoal for x by (metis image_eqI someInvMorph_phi_phi)
      subgoal 
        by(smt (verit, best) A2 S1 img.morph_preserves_particulars 
            img.morph_worlds_correspond_src_tgt 
            particular_struct_morphism_sig.world_corresp_E someInvMorph_phi_phi 
            some_inv_to_some_inv_img.I_img_eq_tgt_I 
            some_inv_to_some_inv_img.morph_image_I src.\<P>_I that)      
      using that by blast
    show ?thesis
    apply (simp only: some_inv_img_to_src.world_corresp_def[
          of _ w\<^sub>t,simplified as])
      apply (intro exI[of _ \<open>w\<^sub>t \<inter> \<P>\<^sub>R\<close>] ; simp ; simp only: R1)
      using that by blast
  qed
qed


private lemma \<^marker>\<open>tag (proof) aponly\<close> lemma1: 
  \<open>particular_struct_morphism \<Gamma>\<^sub>1  \<Gamma>\<^sub>1 (id_on \<P>\<^sub>R \<circ>\<^bsub>\<P>\<^sub>A\<^esub> (\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>))\<close>
  apply (intro particular_struct_morphism_comp[
      of \<Gamma>\<^sub>1 \<open>MorphImg (\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>) \<Gamma>\<^sub>1\<close> \<open>\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>\<close> \<Gamma>\<^sub>1 
        \<open>id_on \<P>\<^sub>R\<close>])
  subgoal G1    
    using img.particular_struct_morphism_axioms particular_struct_morphism_comp 
          some_inv_to_some_inv_img.particular_struct_morphism_axioms 
    by fastforce  
  using S1 some_inv_img_to_src.particular_struct_morphism_axioms by presburger

interpretation src_to_src: 
  particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>1 
  \<open>\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>\<close> \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>1)\<close>  
proof -
  have R1: \<open>id_on \<P>\<^sub>R \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi> = \<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>\<close>
    apply (intro ext)
    subgoal for x            
      apply (cases \<open>x \<in> \<P>\<^sub>A\<close>)
      subgoal by (simp add: compose_eq)
      by (simp add: compose_def)
    done
  show \<open>particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>1 (\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>)\<close>
    using lemma1 R1 by simp
qed

private lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_to_endomorphism: \<open>particular_struct_endomorphism \<Gamma>\<^sub>1 (\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>)\<close>
  by (intro_locales)

private lemma \<^marker>\<open>tag (proof) aponly\<close> someInvMorph_to_eq_class_choice: 
  \<open>(\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>) x = f (eq_class x)\<close> if \<open>x \<in> \<P>\<^sub>A\<close>
  using that apply (simp only: compose_eq)    
  by (smt delta_E2 delta_dom f_in_X1 img.eq_class_I img.eq_classes_I img.eq_classes_disj 
        img.eq_classes_non_empty morph_image_I morph_image_def 
        particular_struct_morphism.same_image_I particular_struct_morphism_axioms 
        someInvMorph_delta_I)

lemma \<^marker>\<open>tag (proof) aponly\<close> eq_class_choice_inv_morph_ex: 
  \<open>\<exists>\<sigma>. particular_struct_endomorphism \<Gamma>\<^sub>1 \<sigma> \<and> 
    (\<forall>x \<in> src.\<P>. \<sigma> x = f (eq_class x))\<close>
  apply (intro exI[of _ \<open>\<phi>\<^sub>\<leftarrow> \<circ>\<^bsub>\<P>\<^sub>A\<^esub> \<phi>\<close>] conjI ballI
          someInvMorph_to_eq_class_choice ; simp?)  
  by (simp add: someInvMorph_to_endomorphism)

end

lemmas eq_class_choice = eq_class_choice_inv_morph_ex


end

context particular_struct_morphism
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> choice_from_choice_ex:
  assumes \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> \<open>\<phi> x = \<phi> y\<close> 
        \<open>\<exists>(f :: 'p\<^sub>1 set \<Rightarrow> 'p\<^sub>1). particular_struct_morphism_with_choice \<Gamma>\<^sub>1  \<Gamma>\<^sub>2 \<phi> f\<close>
  shows \<open>\<exists>(\<sigma> :: 'p\<^sub>1 \<Rightarrow> 'p\<^sub>1). particular_struct_endomorphism \<Gamma>\<^sub>1  \<sigma> \<and> \<sigma> x = y \<and> \<sigma> y = y\<close>
proof -
  obtain f :: \<open>'p\<^sub>1 set \<Rightarrow> 'p\<^sub>1\<close> where \<open>particular_struct_morphism_with_choice \<Gamma>\<^sub>1  \<Gamma>\<^sub>2 \<phi> f\<close>
    using assms by blast
  then interpret f_choice: particular_struct_morphism_with_choice \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>2\<close> \<open>\<phi>\<close> \<open>f\<close> by simp
  define g where \<open>g X \<equiv> if y \<in> X then y else f X\<close> for X
  interpret g_choice: particular_struct_morphism_with_choice \<open>\<Gamma>\<^sub>1\<close> \<open>\<Gamma>\<^sub>2\<close> \<phi> g
    apply (unfold_locales)
    apply (intro allI impI ; simp only: g_def)
    subgoal for X
      by (cases \<open>y \<in> X\<close> ; simp)
    done
  
  obtain \<sigma> where A: \<open>particular_struct_endomorphism \<Gamma>\<^sub>1 \<sigma>\<close>
          \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> \<sigma> x = g (eq_class x)\<close>
    using g_choice.eq_class_choice  by blast

  have B: \<open>\<sigma> x = y\<close>  by (auto simp: g_def A(2) assms)
  have C: \<open>\<sigma> y = y\<close>  by (auto simp: g_def A(2) assms)
  show ?thesis
    by (intro exI[of _ \<sigma>] conjI A(1) B C)  
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> choice_exists:
  \<open>\<exists>(f :: 'p\<^sub>1 set \<Rightarrow> 'p\<^sub>1). particular_struct_morphism_with_choice \<Gamma>\<^sub>1  \<Gamma>\<^sub>2 \<phi> f\<close>
  apply (intro exI[of _ "\<lambda>X. SOME x. x \<in> X"])
  apply (unfold_locales ; auto)
  subgoal for X x
    using someI[of \<open>\<lambda>x. x \<in> X\<close>,of x] by blast
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> choice: 
  assumes \<open>x \<in> src.\<P>\<close> \<open>y \<in> src.\<P>\<close> \<open>\<phi> x = \<phi> y\<close>        
  shows \<open>\<exists>(\<sigma> :: 'p\<^sub>1 \<Rightarrow> 'p\<^sub>1). particular_struct_endomorphism \<Gamma>\<^sub>1  \<sigma> \<and> \<sigma> x = y \<and> \<sigma> y = y\<close>
  using choice_from_choice_ex[OF assms choice_exists] by blast

end

end

