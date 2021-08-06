subsection \<^marker>\<open>tag aponly\<close> \<open>Single Non-Empty World Structures\<close>

theory SingleWorldStructure
  imports ParticularStructureMorphisms
begin

locale single_world_particular_struct = 
    particular_struct where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q
  for Typ\<^sub>p :: \<open>'p itself\<close> and Typ\<^sub>q :: \<open>'q itself\<close> +
  assumes
    only_empty_and_another_world: \<open>\<exists>w \<noteq> \<emptyset>. \<W> = {\<emptyset>,w}\<close>
begin

definition \<open>\<w> \<equiv> THE w. w \<noteq> \<emptyset> \<and> w \<in> \<W>\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_non_empty_world_unique: \<open>\<exists>!w. w \<noteq> \<emptyset> \<and> w \<in> \<W>\<close>
  using only_empty_and_another_world 
  by (metis empty_iff insert_iff)

lemma \<^marker>\<open>tag (proof) aponly\<close> single_world[simp,intro!]: \<open>\<w> \<in> \<W>\<close> \<open>\<w> \<noteq> \<emptyset>\<close>
  by (simp only: \<w>_def ; rule the1I2[OF sw_non_empty_world_unique] ; simp)+

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_worlds_case[cases set]:
  assumes \<open>w \<in> \<W>\<close>
  obtains (empty) \<open>w = \<emptyset>\<close> | (single) \<open>w = \<w>\<close>
  using assms only_empty_and_another_world single_world
  by blast 

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_in_worlds[dest!]: \<open>\<lbrakk> w \<in> \<W> ; x \<in> w \<rbrakk> \<Longrightarrow> w = \<w> \<and> x \<in> \<w>\<close>  
  using sw_worlds_case by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_particulars_simp[simp]: \<open>endurants = \<w>\<close>
  apply (simp only: \<P>_def)
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_worlds_simp: \<open>\<W> = {\<emptyset>, \<w>}\<close> 
  using only_empty_and_another_world single_world(2) by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_particulars_I[iff]: \<open>x \<in> \<P> \<longleftrightarrow> x \<in> \<w>\<close> 
  by (simp only: sw_particulars_simp)

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_ed_iff[simp]: \<open>ed x y \<longleftrightarrow> x \<in> \<w> \<and> y \<in> \<w>\<close>
  apply (simp only: ed_def ; intro iffI conjI ballI impI ; simp?)
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_no_indep[simp]: \<open>\<not> indep x y\<close>
  by (simp add: indep_def)


lemma \<^marker>\<open>tag (proof) aponly\<close> sw_empty_world[simp,intro!]: \<open>\<emptyset> \<in> \<W>\<close>   
  by (simp add: sw_worlds_simp)

end

locale single_world_pre_particular_struct_morphism =
   pre_particular_struct_morphism where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
   src: single_world_particular_struct where \<Gamma> = \<open>\<Gamma>\<^sub>1\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> +
   tgt: single_world_particular_struct where \<Gamma> = \<open>\<Gamma>\<^sub>2\<close> and Typ\<^sub>p = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close>
  for
    Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
    Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close>  
begin

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_world_corresp_iff[simp]:
  \<open>w\<^sub>s \<Leftrightarrow> w\<^sub>t \<longleftrightarrow> (w\<^sub>s = \<emptyset> \<and> w\<^sub>t = \<emptyset>) \<or> 
      (w\<^sub>s = src.\<w> \<and> w\<^sub>t = tgt.\<w> \<and> \<phi> ` src.\<w> \<subseteq> tgt.\<w>)\<close>
  apply (intro iffI conjI disjCI 
        ; (elim conjE disjE)?
        ; simp
        ; (elim world_corresp_E)? 
        ; (intro world_corresp_I)?
        ; simp?)
  subgoal by blast
  subgoal by (metis Set.subset_empty  empty_is_image image_subsetI morph_preserves_particulars  
              src.sw_in_worlds src.sw_particulars_simp src.sw_worlds_case 
              tgt.sw_particulars_simp tgt.sw_worlds_case)
  subgoal by blast
  done

lemma \<^marker>\<open>tag (proof) aponly\<close> sw_particular_struct_morphism_iff:
  \<open>particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> \<longleftrightarrow> 
    \<phi> ` src.\<w> \<subseteq> tgt.\<w> \<close>   
    (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume \<open>?P\<close>
  then interpret phi: particular_struct_morphism \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> by simp
  show \<open>?Q\<close>
    apply (intro conjI ballI impI subsetI ; (elim conjE imageE)? ; simp)
    using morph_preserves_particulars by blast
next
  assume A: \<open>?Q\<close>
  show \<open>?P\<close>
    apply (unfold_locales ; simp)
    subgoal G1 for w\<^sub>s
      apply (cases w\<^sub>s rule: src.sw_worlds_case ; simp)
       apply (intro exI[of _ \<emptyset>] ; simp)        
      using A by linarith
    subgoal G2 for w\<^sub>t
      apply (cases w\<^sub>t rule: tgt.sw_worlds_case ; simp)
      apply (intro exI[of _ \<emptyset>] ; simp)
      using A by linarith
    done
qed    

end

locale single_world_particular_struct_morphism =
    single_world_pre_particular_struct_morphism  
      where Typ\<^sub>p\<^sub>1 = \<open>Typ\<^sub>p\<^sub>1\<close> and Typ\<^sub>p\<^sub>2 = \<open>Typ\<^sub>p\<^sub>2\<close> and Typ\<^sub>q = \<open>Typ\<^sub>q\<close> 
  for
    Typ\<^sub>p\<^sub>1 :: \<open>'p\<^sub>1 itself\<close> and
    Typ\<^sub>p\<^sub>2 :: \<open>'p\<^sub>2 itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close>  +
  assumes
    image_subset: \<open>\<phi> ` src.\<w> \<subseteq> tgt.\<w>\<close> and
    morph_closes_quale_assoc_1:
      \<open>\<And>x\<^sub>t y\<^sub>t q. \<lbrakk> x\<^sub>t \<in> \<phi> ` src.\<w> ; y\<^sub>t \<in> tgt.\<w> ; q \<in> \<Q>\<^sub>s ; y\<^sub>t \<triangleleft>\<^sub>t x\<^sub>t ; y\<^sub>t \<leadsto>\<^sub>t q \<rbrakk>
            \<Longrightarrow> y\<^sub>t \<in> \<phi> ` src.\<w>\<close>

sublocale single_world_particular_struct_morphism \<subseteq> particular_struct_morphism
  apply (simp only: sw_particular_struct_morphism_iff)
  using image_subset morph_closes_quale_assoc_1 by metis

end