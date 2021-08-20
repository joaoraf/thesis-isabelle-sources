theory MorphismImage
  imports ParticularStructureMorphisms
begin

context inherence_base
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> moments_eq_particulars_minus_subst: \<open>\<M> = \<P> - \<S>\<close> by blast  

lemma \<^marker>\<open>tag (proof) aponly\<close> substantials_eq_particulars_minus_moments: \<open>\<S> = \<P> - \<M>\<close> by blast  

end

context particular_struct_morphism
begin

abbreviation \<^marker>\<open>tag aponly\<close> \<open>\<W>\<^sub>\<phi> \<equiv> ps_worlds (MorphImg \<phi> \<Gamma>\<^sub>1)\<close>
abbreviation \<^marker>\<open>tag aponly\<close>img_inheres_in (infix \<open>\<triangleleft>\<^sub>\<phi>\<close> 75)
  where \<open>(\<triangleleft>\<^sub>\<phi>) \<equiv> ps_inheres_in (MorphImg \<phi> \<Gamma>\<^sub>1)\<close>
abbreviation \<^marker>\<open>tag aponly\<close>img_assoc_quale (infix \<open>\<leadsto>\<^sub>\<phi>\<close> 75)
  where \<open>(\<leadsto>\<^sub>\<phi>) \<equiv> ps_assoc_quale (MorphImg \<phi> \<Gamma>\<^sub>1)\<close>
abbreviation \<^marker>\<open>tag aponly\<close>img_towards (infix \<open>\<longlongrightarrow>\<^sub>\<phi>\<close> 75)
  where \<open>(\<longlongrightarrow>\<^sub>\<phi>) \<equiv> ps_towards (MorphImg \<phi> \<Gamma>\<^sub>1)\<close>

interpretation \<^marker>\<open>tag aponly\<close> img: ufo_particular_theory_sig \<open>\<W>\<^sub>\<phi>\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<close> src.\<Q>\<S> \<open>(\<leadsto>\<^sub>\<phi>)\<close> \<open>(\<longlongrightarrow>\<^sub>\<phi>)\<close> .

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_particulars(*[simp]*): \<open>img.\<P> = \<phi> ` src.\<P>\<close>
  by (auto simp: possible_worlds_sig.\<P>_def)  

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_worlds_tgt(*[simp]*): 
  \<open>\<W>\<^sub>\<phi> = { w \<inter> \<phi> ` src.\<P> | w . w \<in> tgt.\<W>}\<close>
(* slow *)
proof (auto)
  fix w\<^sub>s
  assume A[simp]: \<open>w\<^sub>s \<in> src.\<W>\<close>
  then obtain w\<^sub>t where B: \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close> using morph_worlds_correspond_src_tgt by metis
  obtain C[simp]: \<open>w\<^sub>t \<in> tgt.\<W>\<close> \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>s \<longleftrightarrow> \<phi> x \<in> w\<^sub>t\<close>
    using world_corresp_E[OF B] by metis
  have \<open>\<phi> ` w\<^sub>s = w\<^sub>t \<inter> \<phi> ` src.endurants\<close>
    apply auto    
    using A C(2) by blast+
  then show \<open>\<exists>w\<^sub>t. \<phi> ` w\<^sub>s = w\<^sub>t \<inter> \<phi> ` src.endurants \<and> w\<^sub>t \<in> tgt.\<W>\<close>
    using C(1) by blast    
next
  fix w\<^sub>t 
  assume A[simp]: \<open>w\<^sub>t \<in> tgt.\<W>\<close> 
  then obtain w\<^sub>s where B: \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t\<close> using morph_worlds_correspond_tgt_src by metis
  obtain C[simp]: \<open>w\<^sub>s \<in> src.\<W>\<close> \<open>\<And>x. x \<in> src.\<P> \<Longrightarrow> x \<in> w\<^sub>s \<longleftrightarrow> \<phi> x \<in> w\<^sub>t\<close>
    using world_corresp_E[OF B] by metis
  have \<open>w\<^sub>t \<inter> \<phi> ` src.endurants = \<phi> ` w\<^sub>s \<and> w\<^sub>s \<in> src.\<W>\<close>
    apply auto    
    using A C by blast+
  then show \<open>\<exists>w\<^sub>s. w\<^sub>t \<inter> \<phi> ` src.endurants = \<phi> ` w\<^sub>s \<and> w\<^sub>s \<in> src.\<W>\<close> by blast
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_worlds_src:\<open>\<W>\<^sub>\<phi> = ((`) \<phi>) ` src.\<W>\<close>
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_ed_tgt(*[simp]*):  \<open>img.ed x y \<longleftrightarrow> x \<in> \<phi> ` src.\<P> \<and> y \<in> \<phi> ` src.\<P> \<and> tgt.ed x y\<close>
proof (intro iffI conjI ; (elim conjE)?)
  assume A: \<open>possible_worlds_sig.ed (ps_worlds (MorphImg \<phi> \<Gamma>\<^sub>1)) x y\<close>
  obtain B[simp]: \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> and C: \<open>\<And>w. w \<in> ps_worlds (MorphImg \<phi> \<Gamma>\<^sub>1) \<Longrightarrow> x \<in> w \<Longrightarrow> y \<in> w\<close>
    using possible_worlds_sig.edE[OF A,simplified morph_image_particulars ] by blast
  show D: \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> by simp_all
  have E: \<open>y \<in> w\<^sub>1\<close> if \<open>w\<^sub>1 = w\<^sub>2 \<inter> \<phi> ` src.\<P>\<close> \<open>w\<^sub>2 \<in> tgt.\<W>\<close> \<open>x \<in> w\<^sub>1\<close> for w\<^sub>1 w\<^sub>2
    using C[simplified morph_image_worlds_tgt, OF CollectI] that by metis
  obtain F[simp]: \<open>x \<in> tgt.\<P>\<close> \<open>y \<in> tgt.\<P>\<close> using D by blast
  show \<open>tgt.ed x y\<close>
  proof (intro tgt.edI F)
    fix w\<^sub>t
    assume AA[simp]: \<open>w\<^sub>t \<in> tgt.\<W>\<close> \<open>x \<in> w\<^sub>t\<close>    
    show \<open>y \<in> w\<^sub>t\<close>
      using E[of \<open>w\<^sub>t \<inter> \<phi> ` src.\<P>\<close> w\<^sub>t,THEN IntD1,simplified] by simp
  qed
next
  assume A: \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>tgt.ed x y\<close>
  then obtain x\<^sub>s y\<^sub>s where B[simp]: \<open>x = \<phi> x\<^sub>s\<close> \<open>y = \<phi> y\<^sub>s\<close> \<open>x\<^sub>s \<in> src.\<P>\<close> \<open>y\<^sub>s \<in> src.\<P>\<close> by blast
  obtain C[simp]: \<open>\<phi> x\<^sub>s \<in> tgt.\<P>\<close> \<open>\<phi> y\<^sub>s \<in> tgt.\<P>\<close> using A B by blast
  have D: \<open>\<phi> y\<^sub>s \<in> w\<close> if \<open>w \<in> tgt.\<W>\<close> \<open>\<phi> x\<^sub>s \<in> w\<close> for w
    using tgt.edE[OF A(3),simplified] that by blast
  obtain E: \<open>\<phi> x\<^sub>s \<in> particulars (MorphImg \<phi> \<Gamma>\<^sub>1)\<close> \<open>\<phi> y\<^sub>s \<in> particulars (MorphImg \<phi> \<Gamma>\<^sub>1)\<close>
    by (simp only: morph_image_particulars A B(1,2)[symmetric])

  show \<open>possible_worlds_sig.ed (ps_worlds (MorphImg \<phi> \<Gamma>\<^sub>1)) x y\<close>
  proof (simp only: B ; intro possible_worlds_sig.edI E ; simp ; elim exE conjE ; simp)    
    fix w :: "'p\<^sub>2 set" and wa :: "'p\<^sub>1 set"
    assume a1: "\<phi> x\<^sub>s \<in> \<phi> ` wa"
    assume a2: "w = \<phi> ` wa"
    assume "wa \<in> src.\<W>"
    then obtain PP :: "'p\<^sub>1 set \<Rightarrow> 'p\<^sub>2 set" where
      f3: "wa \<Leftrightarrow> PP wa"
      by (meson morph_worlds_correspond_src_tgt)
    have "x \<in> w"
      using a2 a1 by fastforce
    then show "\<phi> y\<^sub>s \<in> \<phi> ` wa"
      using f3 a2 A(3) B(2) B(4) by blast
  qed    
qed  

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_edI:
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>tgt.ed x y\<close>
  shows \<open>img.ed x y\<close>
  using assms by (simp only: morph_image_ed_tgt)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_edD:
  assumes \<open>img.ed x y\<close> 
  shows \<open>tgt.ed x y\<close>
  using assms by (simp only: morph_image_ed_tgt)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_edE:
  assumes \<open>img.ed x y\<close>
  obtains \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>tgt.ed x y\<close>
  using assms by (simp only: morph_image_ed_tgt)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_indep_iff: \<open>img.indep x y \<longleftrightarrow> x \<in> \<phi> ` src.\<P> \<and> y \<in> \<phi> ` src.\<P> \<and> tgt.indep x y\<close>
proof (intro iffI conjI ; (elim conjE)?)
  assume A: \<open>img.indep x y\<close>
  obtain B: \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>\<not> img.ed x y\<close> \<open>\<not> img.ed y x\<close>
    using img.indepE[OF A,simplified morph_image_particulars] by metis
  then show \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> by simp+
  obtain C: \<open>x \<in> tgt.\<P>\<close> \<open>y \<in> tgt.\<P>\<close> using B(1,2) by blast
  have D: \<open>\<not> tgt.ed x y\<close>  \<open>\<not> tgt.ed y x\<close>
    using B(3,4)[THEN notE,OF morph_image_edI] B(2,1) by metis+
  then show \<open>tgt.indep x y\<close>
    by (intro tgt.indepI C D)
next
  assume A: \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> and B: \<open>tgt.indep x y\<close>
  show \<open>img.indep x y\<close> 
    apply (intro img.indepI notI ; (elim notE morph_image_edE)?
          ; (simp only: morph_image_particulars A) ; simp)
    using B tgt.indepE by blast+
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_indepI: 
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>tgt.indep x y\<close>
  shows \<open>img.indep x y\<close>
  using assms by (simp only: morph_image_indep_iff)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_indepE: 
  assumes \<open>img.indep x y\<close>
  obtains \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>tgt.indep x y\<close>
  using assms by (simp only: morph_image_indep_iff)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_indepD: 
  assumes \<open>img.indep x y\<close>
  shows \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>tgt.indep x y\<close>
  using assms by (simp only: morph_image_indep_iff)+

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_inheres_in: \<open>x \<triangleleft>\<^sub>\<phi> y \<longleftrightarrow> x \<in> \<phi> ` src.\<P> \<and> y \<in> \<phi> ` src.\<P> \<and> x \<triangleleft>\<^sub>t y\<close>
  apply (auto)
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_inheres_in_I:
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>x \<triangleleft>\<^sub>t y\<close>
  shows \<open>x \<triangleleft>\<^sub>\<phi> y\<close>
  using assms by (simp only: morph_image_inheres_in)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_inheres_in_E:
  assumes \<open>x \<triangleleft>\<^sub>\<phi> y\<close>
  obtains \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>x \<triangleleft>\<^sub>t y\<close>
  using assms by (simp only: morph_image_inheres_in)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_inheres_in_D:
  assumes \<open>x \<triangleleft>\<^sub>\<phi> y\<close>
  shows \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>x \<triangleleft>\<^sub>t y\<close>
  using assms by (simp only: morph_image_inheres_in)+

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_trans_inheres_in:  \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>+\<^sup>+ x y \<longleftrightarrow> x \<in> \<phi> ` src.\<P> \<and> y \<in> \<phi> ` src.\<P> \<and> (\<triangleleft>\<^sub>t)\<^sup>+\<^sup>+ x y\<close>  
proof (intro iffI conjI ; (elim conjE)?)
  assume A: \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>+\<^sup>+ x y\<close>
  show G1: \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close>
  proof -
    obtain x\<^sub>1 where \<open>x \<triangleleft>\<^sub>\<phi> x\<^sub>1\<close> 
      using A tranclp_induct by metis
    obtain y\<^sub>1 where \<open>y\<^sub>1 \<triangleleft>\<^sub>\<phi> y\<close> 
      using A by (metis tranclp.cases)
    then show \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close>
      using \<open>x \<triangleleft>\<^sub>\<phi> x\<^sub>1\<close> morph_image_inheres_in_D(1,2) by metis+
  qed  
  from A 
  show \<open>(\<triangleleft>\<^sub>t)\<^sup>+\<^sup>+ x y\<close>
  proof (induct)
    fix y
    assume AA: \<open>x \<triangleleft>\<^sub>\<phi> y\<close>
    show \<open>(\<triangleleft>\<^sub>t)\<^sup>+\<^sup>+ x y\<close>
      using AA morph_image_inheres_in_D(3) tranclp.intros(1) by metis      
  next
    fix y z
    assume AA:  \<open>y \<triangleleft>\<^sub>\<phi> z\<close> \<open>(\<triangleleft>\<^sub>t)\<^sup>+\<^sup>+ x y\<close>
    then show \<open>(\<triangleleft>\<^sub>t)\<^sup>+\<^sup>+ x z\<close>
      using AA morph_image_inheres_in_D(3) tranclp.intros(2) by metis      
  qed
next
  assume A: \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> and B: \<open>(\<triangleleft>\<^sub>t)\<^sup>+\<^sup>+ x y\<close>
  from B
  show \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>+\<^sup>+ x y\<close>
  proof (induct)
    fix y
    assume AA: \<open>x \<triangleleft>\<^sub>t y\<close>
    then show \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>+\<^sup>+ x y\<close>
      using A morph_image_inheres_in_I tranclp.intros(1)
      by (metis image_iff morph_does_not_add_bearers)
  next
    fix y z
    assume AA: \<open>(\<triangleleft>\<^sub>t)\<^sup>+\<^sup>+ x y\<close> \<open>y \<triangleleft>\<^sub>t z\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>+\<^sup>+ x y\<close>
    have BB: \<open>y \<in> \<phi> ` src.\<P>\<close> 
      by (metis AA(3) converse_tranclp_induct morph_image_inheres_in)
    then have CC: \<open>z \<in> \<phi> ` src.\<P>\<close> using morph_does_not_add_bearers AA(2) by blast
    then have BB: \<open>y \<triangleleft>\<^sub>\<phi> z\<close>
      using morph_image_inheres_in_I BB AA(2) by blast
    then show \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>+\<^sup>+ x z\<close> 
      using AA(3) tranclp.intros(2) by metis      
  qed
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_moments(*[simp]*): \<open>img.\<M> = \<phi> ` src.\<M>\<close>
  by (auto  simp: inherence_sig.\<M>_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_assoc_quale: \<open>x \<leadsto>\<^sub>\<phi> q \<longleftrightarrow> x \<in> \<phi> ` src.\<P> \<and> x \<leadsto>\<^sub>t q\<close>
  apply (auto)
  subgoal by (meson imageI src.assoc_quale_scopeD(1))
  subgoal using morph_reflects_quale_assoc src.assoc_quale_scopeD(1) by blast  
  using morph_reflects_quale_assoc by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_assoc_quale_I:
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>x \<leadsto>\<^sub>t q\<close> 
  shows \<open>x \<leadsto>\<^sub>\<phi> q\<close>
  using assms by (simp only: morph_image_assoc_quale)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_assoc_quale_E:
  assumes\<open>x \<leadsto>\<^sub>\<phi> q\<close>
  obtains \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>x \<leadsto>\<^sub>t q\<close>
  using assms by (simp only: morph_image_assoc_quale)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_assoc_quale_D:
  assumes\<open>x \<leadsto>\<^sub>\<phi> q\<close>
  shows \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>x \<leadsto>\<^sub>t q\<close>
  using assms by (simp only: morph_image_assoc_quale)+


lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_towards(*[simp]*): \<open>x \<longlongrightarrow>\<^sub>\<phi> y \<longleftrightarrow> x \<in> \<phi> ` src.\<P> \<and> y \<in> \<phi> ` src.\<P> \<and> x \<longlongrightarrow>\<^sub>t y\<close>
  apply (auto)
  subgoal G1 using morph_reflects_towardness by blast
  subgoal G2 by blast
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_towards_I:
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>x \<longlongrightarrow>\<^sub>t y\<close>
  shows \<open>x \<longlongrightarrow>\<^sub>\<phi> y\<close>
  using assms by (simp only: morph_image_towards)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_towards_E:
  assumes \<open>x \<longlongrightarrow>\<^sub>\<phi> y\<close>
  obtains \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>x \<longlongrightarrow>\<^sub>t y\<close>
  using assms by (simp only: morph_image_towards)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_towards_D:
  assumes \<open>x \<longlongrightarrow>\<^sub>\<phi> y\<close>
  shows \<open>x \<in> \<phi> ` src.\<P>\<close> \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>x \<longlongrightarrow>\<^sub>t y\<close>
  using assms by (simp only: morph_image_towards)+

interpretation img: possible_worlds \<open>\<W>\<^sub>\<phi>\<close>
  apply (unfold_locales)
  subgoal G1 by (simp add: tgt.injection_to_ZF_exist)
  subgoal G2 by (simp add: src.at_least_one_possible_world)  
proof(simp only: morph_image_particulars ; simp only: morph_image_worlds_src
        ; auto)
  fix xa :: 'p\<^sub>1
  assume a1: "xa \<in> src.endurants"
  then obtain PP :: "'p\<^sub>1 \<Rightarrow> 'p\<^sub>1 set" where
    f2: "PP xa \<in> src.\<W> \<and> xa \<notin> PP xa"
    by (meson src.particulars_do_not_exist_in_some_world)
  then obtain PPa :: "'p\<^sub>1 set \<Rightarrow> 'p\<^sub>2 set" where
    "PP xa \<Leftrightarrow> PPa (PP xa)"
    by (meson morph_worlds_correspond_src_tgt)
  then have f3: "PP xa \<in> src.\<W> \<and> PPa (PP xa) \<in> tgt.\<W> \<and> (\<forall>p. p \<notin> src.endurants \<or> (p \<in> PP xa) = (\<phi> p \<in> PPa (PP xa)))"
    by blast
  have "\<forall>p f P. (p::'p\<^sub>2) \<notin> f ` P \<or> (\<exists>pa. p = f (pa::'p\<^sub>1) \<and> pa \<in> P)"
    by blast
  then show "\<exists>P\<in>src.\<W>. \<phi> xa \<notin> \<phi> ` P"
    using f3 f2 a1 by (metis possible_worlds_sig.\<P>_I)
next
  fix w
  assume as: \<open>w \<in> \<W>\<^sub>\<phi>\<close>
  then show \<open>undefined \<notin> w\<close>     
    using morph_image_particulars undefined_not_in_img by blast
qed
  


interpretation img: inherence_base \<open>\<W>\<^sub>\<phi>\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<close>
  apply (unfold_locales ; (simp only: morph_image_ed_tgt morph_image_particulars)?
        ; elim morph_image_inheres_in_E 
        ; (intro conjI)? ; simp?)
  subgoal by (simp add: tgt.inherence_imp_ed)  
  using tgt.moment_non_migration by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_substantials(*[simp]*): \<open>img.\<S> = \<phi> ` src.\<S>\<close>
  apply (simp only: inherence_sig.\<S>_def morph_image_particulars morph_image_moments)
  apply auto  
  by (metis morph_preserves_moments_simp morph_preserves_moments)

interpretation img: noetherian_inherence \<open>\<W>\<^sub>\<phi>\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<close>
  apply (unfold_locales ; simp)
  apply (rule wf_subset[to_pred,OF tgt.inherence_is_noetherian] ; simp ; rule)
  apply (elim exE conjE )
  using morph_preserves_inherence_1 by metis



interpretation img: inherence \<open>\<W>\<^sub>\<phi>\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<close>
  apply (unfold_locales ; simp)
  apply (rule wf_subset[to_pred,OF tgt.inherence_is_wf] ; rule )
  apply (elim exE conjE )
  using morph_preserves_inherence_1 by metis

interpretation img: quality_space \<open>ps_quality_spaces (MorphImg \<phi> \<Gamma>\<^sub>1)\<close>
  by (simp ; unfold_locales)

interpretation img:  qualified_particulars \<open>\<W>\<^sub>\<phi>\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<close>  \<open>src.\<Q>\<S>\<close> \<open>(\<leadsto>\<^sub>\<phi>)\<close>
  supply   ParticularStructure.particular_struct.simps[simp del]
  apply (unfold_locales ; (simp only: morph_image_moments morph_image_assoc_quale ; simp )?
          ; (elim conjE)?)    
  subgoal G1 by (metis image_eqI  morph_image_def morph_image_iff  morph_reflects_quale_assoc src.assoc_quale_scope)
  subgoal G1 by (simp add: tgt.assoc_quale_unique)
  subgoal G3 premises P for w x\<^sub>1 x\<^sub>2 y q\<^sub>1 q\<^sub>2 Q
    using P
    by (smt image_iff pre_particular_struct_morphism.morph_preserves_inherence_1 
        pre_particular_struct_morphism.morph_reflects_inherence 
        pre_particular_struct_morphism.morph_reflects_quale_assoc 
        pre_particular_struct_morphism_axioms src.\<P>_I src.endurantI2 
        src.quality_moment_unique_by_quality_space)
  subgoal G4 
    by (meson morph_reflects_quale_assoc src.assoc_quale_scopeD(1) src.every_quality_space_is_used)
  subgoal G5
    using src.quale_determines_moment 
    by (metis morph_preserves_inherence_1 tgt.quale_determines_moment)
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> rtranclp_iff_tranclp: \<open>R\<^sup>*\<^sup>* x y \<longleftrightarrow> x = y \<or> (R\<^sup>+\<^sup>+ x y)\<close> for R x y
  apply auto  
  by (meson rtranclpD)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_ultimate_bearer:
  assumes \<open>x \<in> \<phi> ` src.\<P>\<close>
  shows \<open>img.ultimateBearer x = tgt.ultimateBearer x\<close>
  using assms 
proof (induct x rule: wfP_induct[OF tgt.inherence_is_noetherian])
  fix x 
  assume A: \<open>x \<in> \<phi> ` src.\<P>\<close> 
     and B: \<open>\<forall>y. (\<triangleleft>\<^sub>t)\<inverse>\<inverse> y x \<longrightarrow> y \<in> \<phi> ` src.endurants \<longrightarrow> img.ultimateBearer y = tgt.ultimateBearer y\<close>
  have C: \<open>img.ultimateBearer y = tgt.ultimateBearer y\<close> 
    if \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>x \<triangleleft>\<^sub>t y\<close> for y using B that by blast
  have D: \<open>x \<in> tgt.\<P>\<close> using A by blast

  have \<open>\<phi> ` src.\<M> \<subseteq> tgt.\<M>\<close> by blast
  then have E[simp]: \<open>tgt.ultimateBearer x \<notin> \<phi> ` src.\<M>\<close>
    using tgt.ultimate_bearer_is_not_a_moment     
    using D by blast    

  have c_moment: \<open>img.ultimateBearer x = tgt.ultimateBearer x\<close> if as: \<open>x \<in> tgt.\<M>\<close> 
  proof -
    obtain y where \<open>x \<triangleleft>\<^sub>t y\<close> using as by blast
    then have \<open>y \<in> \<phi> ` src.\<P>\<close> using A morph_does_not_add_bearers by blast
    then have AA: \<open>img.ultimateBearer y = tgt.ultimateBearer y\<close> using C \<open>x \<triangleleft>\<^sub>t y\<close> by blast
    then obtain BB: \<open>tgt.ultimateBearer y \<notin> img.\<M>\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>*\<^sup>* y (tgt.ultimateBearer y)\<close>
      using AA[simplified img.ultimate_bearer_eq_simp]
      by (metis \<open>y \<in> \<phi> ` src.endurants\<close> img.noetherian_inherence_axioms 
              img.ultimate_bearer_is_not_a_moment 
              morph_image_particulars noetherian_inherence.ultimate_bearer_eq_simp)
    have \<open>x \<triangleleft>\<^sub>\<phi> y\<close> using A \<open>y \<in> \<phi> ` src.\<P>\<close> \<open>x \<triangleleft>\<^sub>t y\<close> morph_image_inheres_in_I by blast
    then have CC: \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>*\<^sup>* x (tgt.ultimateBearer y)\<close> 
      using BB(2) converse_rtranclp_into_rtranclp by metis
    have \<open>x \<noteq> y\<close> using \<open>x \<triangleleft>\<^sub>\<phi> y\<close> using img.inherence_irrefl by blast
    then have DD: \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>+\<^sup>+ x (tgt.ultimateBearer y)\<close> using CC 
      by (metis \<open>x \<triangleleft>\<^sub>t y\<close> rtranclp_iff_tranclp tgt.inherence_scopeE tgt.ultimate_bearer_is_not_a_moment)         
    then have EE: \<open>x \<noteq> tgt.ultimateBearer y\<close> using img.inherence_is_acyclic by blast
    have FF: \<open>img.ultimateBearer x = tgt.ultimateBearer y\<close>
      by (metis A AA CC \<open>y \<in> \<phi> ` src.endurants\<close> img.ultimate_bearer_eq_simp morph_image_particulars)
    obtain GG: \<open>tgt.ultimateBearer y \<notin> tgt.\<M>\<close> \<open>(\<triangleleft>\<^sub>t)\<^sup>*\<^sup>* y (tgt.ultimateBearer y)\<close> 
      by (meson \<open>x \<triangleleft>\<^sub>t y\<close> tgt.endurantI2 tgt.ultimate_bearer_eq_simp tgt.ultimate_bearer_is_not_a_moment)
    have HH: \<open>(\<triangleleft>\<^sub>t)\<^sup>*\<^sup>* x (tgt.ultimateBearer y)\<close> 
      using \<open>x \<triangleleft>\<^sub>t y\<close> converse_rtranclp_into_rtranclp GG(2) by metis
    then have II: \<open>tgt.ultimateBearer x = tgt.ultimateBearer y\<close>      
      using D \<open>x \<triangleleft>\<^sub>t y\<close> tgt.ultimate_bearer_eq_simp by auto
    show ?thesis
      by (simp only: FF II)
  qed

  have c_substantial: \<open>img.ultimateBearer x = tgt.ultimateBearer x\<close> if as: \<open>x \<in> tgt.\<S>\<close>
  proof -
    have AA: \<open>x \<in> img.\<S>\<close> using as morph_image_substantials A 
      by auto
    then obtain BB: \<open>x \<notin> img.\<M>\<close> \<open>x \<notin> tgt.\<M>\<close> using as by blast
    obtain CC: \<open>(\<triangleleft>\<^sub>\<phi>)\<^sup>*\<^sup>* x x\<close> \<open>(\<triangleleft>\<^sub>t)\<^sup>*\<^sup>* x x\<close> by blast
    have DD1: \<open>img.ultimateBearer x = x\<close> 
        using AA img.ultimate_bearer_eq_simp by blast
      have DD2: \<open>tgt.ultimateBearer x = x\<close> 
        by (simp add: D tgt.ultimate_bearer_eq_simp that)
    show ?thesis
      using DD1 DD2 by simp
  qed

  show \<open>img.ultimateBearer x = tgt.ultimateBearer x\<close>
    using D apply (cases x rule: tgt.endurant_cases)
    subgoal using c_substantial . 
    using c_moment .
qed
  


lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_directed_moments(*[simp]*): \<open>img.directed_moments = \<phi> ` src.directed_moments\<close>
  apply (simp only: towardness_sig.directed_moments_def morph_image_towards )
  apply auto
  subgoal G1 by blast  
  by (meson inherence_base.endurantI1 morph_reflects_towardness src.inherence_base_axioms src.towardness_scopeE)
  

interpretation img: towardness \<open>\<W>\<^sub>\<phi>\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<close> \<open>(\<longlongrightarrow>\<^sub>\<phi>)\<close>
  apply (unfold_locales ; (simp only: morph_image_moments morph_image_towards  
      morph_image_directed_moments)?)
  
  subgoal G1 for x y
    apply (intro conjI ; elim conjE )
    subgoal G1_1 by auto    
    using morph_image_substantials by auto  
  subgoal G2 for x y
    apply (auto simp: possible_worlds_sig.ed_def possible_worlds_sig.\<P>_def)        
    using src.\<P>_I by auto 
  subgoal G2 for x y using morph_image_ultimate_bearer by auto     
  subgoal G3 for x y\<^sub>1 y\<^sub>2 using tgt.towardness_single by blast
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_qualified_particulars(*[simp]*): \<open>img.qualifiedParticulars = \<phi> ` src.qualifiedParticulars\<close>  
  apply (simp only: qualified_particulars_sig.qualifiedParticulars_def morph_image_assoc_quale)
  apply auto
  subgoal G1 by (metis imageI mem_Collect_eq morph_reflects_quale_assoc)
  subgoal G2 by (meson imageI src.assoc_quale_scopeD(1))  
  using morph_reflects_quale_assoc src.assoc_quale_scopeD(1) by blast

interpretation img: ufo_particular_theory \<open>\<W>\<^sub>\<phi>\<close> \<open>(\<triangleleft>\<^sub>\<phi>)\<close> \<open>src.\<Q>\<S>\<close> \<open>(\<leadsto>\<^sub>\<phi>)\<close> \<open>(\<longlongrightarrow>\<^sub>\<phi>)\<close>
  apply (intro_locales)
  apply (unfold_locales ; simp only: morph_image_qualified_particulars morph_image_inheres_in
        ; intro notI ; elim conjE)
  using src.qualified_particulars_are_not_bearers
        tgt.qualified_particulars_are_not_bearers  
  by (metis img.qOf_assoc_quale_I morph_image_assoc_quale morph_image_qualified_particulars tgt.qualifiedParticulars_iff)

interpretation img1: particular_struct \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close>
  supply A = img.ufo_particular_theory_axioms[simplified ufo_particular_theory_def]
  supply B = A[THEN conjunct1] A[THEN conjunct2,THEN conjunct2]
  apply (intro_locales ; (simp only: particular_struct_morphism_image_simps(1))?)
  subgoal using B(1)[simplified qualified_particulars_def] by metis
  using B(2)[simplified qualified_particulars_def] by metis

interpretation src_to_img1_morph: pre_particular_struct_morphism \<Gamma>\<^sub>1 \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> 
(*  by (unfold_locales 
      ; (simp only: morph_image_particulars morph_image_inheres_in morph_image_towards morph_image_assoc_quale)? 
      ; simp ; blast) *)
  apply unfold_locales
  subgoal G1 using morph_image_substantials by auto
  subgoal G2 using morph_image_moments by auto
  subgoal G3 by blast
  subgoal G4 by simp
  subgoal G5 using morph_image_inheres_in by auto
  subgoal G6 using morph_image_towards by auto
  subgoal G7 by (meson morph_does_not_add_towards morph_image_towards)
  subgoal G8 using morph_image_assoc_quale by auto
  done

  

lemma \<^marker>\<open>tag (proof) aponly\<close> src_to_img1_world_corresp: \<open>src_to_img1_morph.world_corresp w\<^sub>s w\<^sub>t \<longleftrightarrow> w\<^sub>s \<in> src.\<W> \<and> w\<^sub>t = \<phi> ` w\<^sub>s\<close>
proof -
  (* generated by slegehammer *)
  have A: \<open>w\<^sub>s \<in> src.\<W> \<Longrightarrow> w\<^sub>t = \<phi> ` w\<^sub>s \<Longrightarrow> \<exists>w. \<phi> ` w\<^sub>s = w \<inter> \<phi> ` src.endurants \<and> w \<in> tgt.\<W>\<close>
  proof -
    assume a1: "w\<^sub>s \<in> src.\<W>"
    assume a2: "w\<^sub>t = \<phi> ` w\<^sub>s"
    then have "w\<^sub>t \<in> {P \<inter> \<phi> ` src.endurants |P. P \<in> tgt.\<W>}"
      using a1 by (metis (no_types) image_iff morph_image_worlds_src morph_image_worlds_tgt)
    then show ?thesis
      using a2 by fastforce
  qed

  (* generated by sledgehammer *)
  have B: \<open>\<And>x. w\<^sub>s \<in> src.\<W> \<Longrightarrow> w\<^sub>t = \<phi> ` w\<^sub>s \<Longrightarrow> x \<in> src.endurants \<Longrightarrow> \<phi> x \<in> \<phi> ` w\<^sub>s \<Longrightarrow> x \<in> w\<^sub>s\<close>
  proof -
    fix x :: 'p\<^sub>1
    assume a1: "x \<in> src.endurants"
    assume a2: "w\<^sub>s \<in> src.\<W>"
    assume a3: "\<phi> x \<in> \<phi> ` w\<^sub>s"
    obtain PP :: "'p\<^sub>1 set \<Rightarrow> 'p\<^sub>2 set" where
      "w\<^sub>s \<Leftrightarrow> PP w\<^sub>s"
      using a2 by (meson morph_worlds_correspond_src_tgt)
    then have "w\<^sub>s \<in> src.\<W> \<and> PP w\<^sub>s \<in> tgt.\<W> \<and> (\<forall>p. p \<notin> src.endurants \<or> (p \<in> w\<^sub>s) = (\<phi> p \<in> PP w\<^sub>s))"
      by blast
    then show "x \<in> w\<^sub>s"
      using a3 a1 by (metis imageE possible_worlds_sig.\<P>_I)
  qed

  show ?thesis
    apply (simp only: src_to_img1_morph.world_corresp_def morph_image_worlds_tgt ; simp)
    apply (intro iffI ; (elim conjE)? ; intro conjI ballI iffI ; (elim exE conjE)? ;
            (intro set_eqI iffI conjI)? ; simp?)
    subgoal G1    by blast
    subgoal G2    by blast
    subgoal G3 using A .
    using B .
qed

interpretation src_to_img1_morph: particular_struct_morphism \<Gamma>\<^sub>1 \<open>MorphImg \<phi> \<Gamma>\<^sub>1\<close> \<phi>
proof -
  (* generated by sledgehammer *)
  have A: \<open>\<exists>w. w\<^sub>t = w \<inter> \<phi> ` src.endurants \<and> w \<in> tgt.\<W> \<Longrightarrow> \<exists>w\<^sub>s. w\<^sub>s \<in> src.\<W> \<and> w\<^sub>t = \<phi> ` w\<^sub>s\<close> for w\<^sub>t
  proof -
    assume "\<exists>w. w\<^sub>t = w \<inter> \<phi> ` src.endurants \<and> w \<in> tgt.\<W>"
    then obtain PP :: "'p\<^sub>2 set" where
      f1: "w\<^sub>t = PP \<inter> \<phi> ` src.endurants \<and> PP \<in> tgt.\<W>"
      by blast
    have "PP \<inter> \<phi> ` src.endurants \<in> {P \<inter> \<phi> ` src.endurants |P. P \<in> tgt.\<W>} \<longrightarrow> (\<exists>P. PP \<inter> \<phi> ` src.endurants = \<phi> ` P \<and> P \<in> src.\<W>)"
      using morph_image_worlds_tgt by auto
    then show ?thesis
      using f1 by blast
  qed  
  show \<open>particular_struct_morphism \<Gamma>\<^sub>1 (MorphImg \<phi> \<Gamma>\<^sub>1) \<phi>\<close>
    apply (unfold_locales
           ; (simp only: morph_image_worlds_tgt 
                         morph_image_inheres_in 
                         morph_image_assoc_quale 
                         morph_image_qualified_particulars
                         src_to_img1_world_corresp)? 
           ; simp?)
    using A .    
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_surjective[intro!,simp]: \<open>particular_struct_surjection \<Gamma>\<^sub>1 (MorphImg \<phi> \<Gamma>\<^sub>1) \<phi>\<close>
  by (unfold_locales ; simp only: morph_image_particulars)

lemma \<^marker>\<open>tag (proof) aponly\<close> morph_image_tgt_struct(*[simp]*): \<open>src_to_img1_morph.tgt.\<Gamma> = MorphImg \<phi> \<Gamma>\<^sub>1\<close>
  by (intro particular_struct_eqI 
      ; simp add: ufo_particular_theory_sig.\<Gamma>_def)

lemmas morph_image_simps = 
    morph_image_particulars
    morph_image_worlds_tgt
    morph_image_worlds_src
    morph_image_ed_tgt
    morph_image_indep_iff
    morph_image_inheres_in
    morph_image_trans_inheres_in
    morph_image_moments
    morph_image_assoc_quale
    morph_image_towards
    morph_image_substantials
    morph_image_ultimate_bearer
    morph_image_directed_moments
    morph_image_qualified_particulars
    src_to_img1_world_corresp
    morph_image_tgt_struct

lemmas morph_image_intros =
    morph_image_edI
    morph_image_indepI
    morph_image_inheres_in_I
    morph_image_assoc_quale_I
    morph_image_towards_I

lemmas morph_image_elims =
    morph_image_edE
    morph_image_indepE
    morph_image_inheres_in_E
    morph_image_assoc_quale_E
    morph_image_towards_E

lemmas morph_image_dests =
    morph_image_edD
    morph_image_indepD
    morph_image_inheres_in_D
    morph_image_assoc_quale_D
    morph_image_towards_D

end


end