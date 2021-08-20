text_raw \<open>\subsection[Sub-Structures]{Sub-Structures\isalabel{sec:sub-structures}}\<close>

theory SubStructures
  imports ParticularStructureMorphisms
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  A particular structure \<open>\<Gamma>\<^sub>1\<close> is considered a sub-structure of another
  particular structure \<open>\<Gamma>\<^sub>2\<close> by means of a morphism \<open>\<phi>\<close> if and only if
  the later is an injective morphism between the first and the second:
\<close>
abbreviation sub_structure_by ::
  \<open>('i\<^sub>1,'q) particular_struct \<Rightarrow> ('i\<^sub>1 \<Rightarrow> 'i\<^sub>2) \<Rightarrow> ('i\<^sub>2,'q) particular_struct \<Rightarrow> bool\<close> 
  (\<open>_ \<lless>\<^bsub>_\<^esub> _\<close> [74,1,74] 75) where
  \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2 \<equiv> particular_struct_injection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Every particular structure is a sub-structure of itself, through the identity morphism:
\<close>

lemma sub_structure_by_refl:  
  assumes \<open>particular_struct \<Gamma>\<close>
  shows \<open>\<Gamma> \<lless>\<^bsub>id_on (particulars \<Gamma>)\<^esub> \<Gamma>\<close>
proof -
  interpret I: particular_struct \<Gamma> using assms .  
  have \<Gamma>[simp]: \<open>I.\<Gamma> = \<Gamma>\<close> by auto
  show ?thesis
    by (intro I.id_is_an_injection[simplified]) 
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The sub-structure relation is transitive, through the composition of
  morphisms:
\<close>
lemma sub_structure_by_trans:
  assumes \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>2 \<lless>\<^bsub>\<phi>\<^sub>2\<^esub> \<Gamma>\<^sub>3\<close>
  shows \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>3\<close>
  using  particular_struct_injection_comp[OF assms] by simp

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Two particular structures are considered isomorphic by means of a morphism \<open>\<phi>\<close>
  just in case \<open>\<phi>\<close> is an bijective morphism:
\<close>

abbreviation isomorphic_by ::
  \<open>('i\<^sub>1,'q) particular_struct \<Rightarrow> ('i\<^sub>1 \<Rightarrow> 'i\<^sub>2) \<Rightarrow> ('i\<^sub>2,'q) particular_struct \<Rightarrow> bool\<close> 
  (\<open>_ \<sim>\<^bsub>_\<^esub> _\<close> [74,1,74] 75) where
  \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2 \<equiv> particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Given particular structures \<open>\<Gamma>\<^sub>1\<close> and \<open>\<Gamma>\<^sub>2\<close>, if \<open>\<Gamma>\<^sub>1\<close> is isomorphic to
  \<open>\<Gamma>\<^sub>2\<close> through a morphism \<open>\<phi>\<close>, then \<open>\<Gamma>\<^sub>1\<close> is a sub-structure of \<open>\<Gamma>\<^sub>2\<close> 
  though \<open>\<phi>\<close>:
\<close>

lemma  isomorphic_by_imp_sub_structure[dest]:
  assumes \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close>
  shows \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close>
  using assms 
  by (simp add: particular_struct_bijection.axioms(1))

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Every particular structure is isomorphic to itself through the 
  identity morphism:
\<close>

lemma isomorphic_by_refl: 
  assumes \<open>particular_struct \<Gamma>\<close>
  shows \<open>\<Gamma> \<sim>\<^bsub>id_on (particulars \<Gamma>)\<^esub> \<Gamma>\<close>
proof -
  interpret particular_struct \<Gamma> using assms.
  show ?thesis    
    by (metis \<Gamma>_simps id_is_a_permutation 
          particular_struct_eqI particular_struct_permutation.axioms(2))
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  If \<open>\<Gamma>\<^sub>1\<close> is isomorphic to \<open>\<Gamma>\<^sub>2\<close> through a morphism \<open>\<phi>\<close>, then
  \<open>\<Gamma>\<^sub>2\<close> is isomorphic to \<open>\<Gamma>\<^sub>1\<close> through the inverse of \<open>\<phi>\<close>:
\<close>
lemma isomorphic_by_sym[intro!]:
  assumes \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close>
  shows \<open>\<Gamma>\<^sub>2 \<sim>\<^bsub>particular_struct_morphism_sig.inv_morph \<Gamma>\<^sub>1 \<phi>\<^esub> \<Gamma>\<^sub>1\<close>
  using particular_struct_bijection.inv_is_bijective_morphism assms by metis

text \<^marker>\<open>tag bodyonly\<close> \<open>
  ``Being isomorphic to'' is a transitive relation:
\<close>

lemma isomorphic_by_trans[trans]:
  assumes \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>2 \<sim>\<^bsub>\<phi>\<^sub>2\<^esub> \<Gamma>\<^sub>3\<close>
  shows \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>3\<close>  
  using assms particular_struct_bijection_comp by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_by_sub_structure_transf[simp]:
  assumes \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close>
  shows \<open>\<Gamma> \<lless>\<^bsub>\<phi> \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2 \<and> 
         \<phi>\<^sub>1 \<in>  extensional (particulars \<Gamma>) \<and>
         \<phi>\<^sub>1 ` particulars \<Gamma> \<subseteq> particulars \<Gamma>\<^sub>1 \<longleftrightarrow> \<Gamma> \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>1\<close>
proof -
  interpret I1: particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> using assms .
  interpret I2: particular_struct_bijection_1 \<Gamma>\<^sub>1 \<phi>  
    using assms particular_struct_bijection_iff_particular_struct_bijection_1 
    by blast  

  have A[simp]: \<open>\<Gamma>\<^sub>2 = MorphImg \<phi> \<Gamma>\<^sub>1\<close>
    by (simp add: I1.tgt_is_morph_img)
  have img_subsetE: P if \<open>f ` X \<subseteq> Y\<close> \<open>(\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y) \<Longrightarrow> P\<close> 
    for f :: \<open>'a\<^sub>1 \<Rightarrow> 'a\<^sub>2\<close> and X and Y and P
    using that by auto
  have img_subsetI: \<open>f ` X \<subseteq> Y\<close> if \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y\<close>   
    for f :: \<open>'a\<^sub>1 \<Rightarrow> 'a\<^sub>2\<close> and X and Y 
    using that by auto
  show ?thesis
  proof (intro iffI conjI sub_structure_by_trans[of _ \<Gamma>\<^sub>1]
                img_subsetI
          ; (elim conjE img_subsetE)? ; assumption?)
    show \<open>\<Gamma> \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>1\<close> if 
        as:  \<open>\<Gamma> \<lless>\<^bsub>\<phi> \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close>
             \<open>\<phi>\<^sub>1 \<in> extensional (particulars \<Gamma>)\<close>
             \<open>\<And>x. x \<in> particulars \<Gamma> \<Longrightarrow> \<phi>\<^sub>1 x \<in> I1.src.\<P>\<close>
    proof -
      interpret phi_phi1: particular_struct_injection
          \<Gamma>  \<Gamma>\<^sub>2 \<open>\<phi> \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>1\<close> using as(1) .
      have phi1_undef[simp]: \<open>\<phi>\<^sub>1 x = undefined\<close> if \<open>x \<notin> particulars \<Gamma>\<close> for x
        using as(2) that by (auto simp: extensional_def)
      interpret phi1: particular_struct_morphism_sig \<Gamma> \<Gamma>\<^sub>1 \<phi>\<^sub>1 .
      have R1: \<open>ps_quality_spaces \<Gamma> \<subseteq> ps_quality_spaces \<Gamma>\<^sub>1\<close>
      proof -
        interpret I2_inv: particular_struct_bijection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<open>I2.inv_morph\<close> 
            by simp
        show ?thesis
          using phi_phi1.quality_space_subset
                I2_inv.quality_space_subset by blast
      qed
      interpret phi1: pre_particular_struct_morphism \<Gamma> \<Gamma>\<^sub>1 \<phi>\<^sub>1
        apply (unfold_locales)
        subgoal G1
          apply auto
          subgoal G1_1 by (meson that(3))
          by (metis I1.morph_preserves_moments compose_eq 
                  phi_phi1.morph_preserves_moments_simp)
        subgoal G2
          apply auto
          by (metis I1.morph_preserves_moments_simp compose_eq
              phi_phi1.morph_preserves_moments phi_phi1.src.endurantI1 that(3))
        subgoal G3 by (simp add: that(2))
        subgoal G4 using R1 .
        subgoal G5
          apply auto
          subgoal G5_1 
            by (metis I1.morph_preserves_inherence_1 compose_eq 
                  phi_phi1.morph_reflects_inherence)          
          by (metis I1.tgt_is_morph_img I2.morph_reflects_inherence 
                compose_eq phi_phi1.morph_preserves_inherence_1 that(3))
        subgoal G6
          apply auto
          subgoal G6_1
           by (metis (mono_tags, hide_lams) I1.morph_reflects_towardness 
                compose_eq phi_phi1.morph_reflects_towardness that(3))
         (* slow *)
         by (metis I1.tgt_is_morph_img I2.morph_reflects_towardness 
              compose_eq phi_phi1.morph_reflects_towardness that(3))
        subgoal G7 for x                    
          by (smt (verit, best) I1.morph_reflects_towardness 
              I1.src.towardness_scopeD(3) I1.src.towardness_single compose_eq 
              phi_phi1.morph_does_not_add_towards that(3))
        subgoal G8
          by (auto simp add: compose_eq that(3))
        done

      interpret phi1: particular_struct_morphism \<Gamma> \<Gamma>\<^sub>1 \<phi>\<^sub>1
      proof (unfold_locales)
        fix w\<^sub>s
        assume as: \<open>w\<^sub>s \<in> phi_phi1.src.\<W>\<close>         
        obtain w\<^sub>1 where w1: \<open>phi_phi1.world_corresp w\<^sub>s w\<^sub>1\<close>
          using phi_phi1.morph_worlds_correspond_src_tgt as by metis        
        then obtain w1_W: \<open>w\<^sub>1 \<in> I1.tgt.\<W>\<close> and
          w1_c: \<open>\<And>x. x \<in> phi_phi1.src.\<P> \<Longrightarrow>
                  x \<in> w\<^sub>s \<longleftrightarrow> (\<phi> \<circ>\<^bsub>phi_phi1.src.\<P>\<^esub> \<phi>\<^sub>1) x \<in> w\<^sub>1\<close>
          using phi_phi1.world_corresp_E[OF w1] by metis
                
        interpret I2_inv: particular_struct_bijection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<open>I2.inv_morph\<close> 
          by simp
        obtain w\<^sub>t where wt: \<open>I2_inv.world_corresp w\<^sub>1 w\<^sub>t\<close>
          using I2_inv.morph_worlds_correspond_src_tgt[OF w1_W] by metis
        note I2_inv.world_corresp_E[OF wt]
        then have wt_W: \<open>w\<^sub>t \<in> phi1.tgt.\<W>\<close> 
          using I2_inv.world_corresp_E[OF wt] by metis
        have wt_c: \<open>x \<in> w\<^sub>1 \<longleftrightarrow> I2.inv_morph x \<in> w\<^sub>t\<close> 
          if \<open>x \<in> I2_inv.src.\<P>\<close> for x
          using wt I2_inv.world_corresp_E that by metis
        show \<open>\<exists>w\<^sub>t. phi1.world_corresp w\<^sub>s w\<^sub>t\<close>
        proof (intro exI[of _ w\<^sub>t] phi1.world_corresp_I as(1) wt_W)
          fix x 
          assume as1: \<open>x \<in> phi_phi1.src.\<P>\<close>
          then have \<open>x \<in> w\<^sub>s \<longleftrightarrow> (\<phi> \<circ>\<^bsub>phi_phi1.src.\<P>\<^esub> \<phi>\<^sub>1) x \<in> w\<^sub>1\<close>
            using w1_c by simp
          then have R1: \<open>x \<in> w\<^sub>s \<longleftrightarrow> \<phi> (\<phi>\<^sub>1 x) \<in> w\<^sub>1\<close> 
            using as1 by (simp add: compose_eq)
          have R2: \<open>\<phi> (\<phi>\<^sub>1 x) \<in> I2_inv.src.\<P>\<close> if \<open>x \<in> w\<^sub>s\<close>            
            by (meson I2_inv.src.\<P>_I that w1_W R1)
          have R3: \<open>I2.inv_morph (\<phi> (\<phi>\<^sub>1 x)) \<in> w\<^sub>t\<close> if \<open>x \<in> w\<^sub>s\<close> 
            using wt_c[OF R2,simplified R1[symmetric],simplified] that
            by metis
          have R4: \<open>inv_into phi1.tgt.\<P> \<phi> ` I2.tgt.\<P> = particulars \<Gamma>\<^sub>1\<close>
            apply (auto)
            subgoal for y by (intro inv_into_into ; simp)
            subgoal for y
              apply (intro rev_image_eqI[of \<open>\<phi> y\<close>] ; simp?)              
              by (simp add: I2.morph_preserves_particulars)
            done
          have R5: \<open>I2_inv.inv_morph = \<phi>\<close> 
            apply (intro ext)
            subgoal for x
              apply (cases \<open>x \<in> particulars \<Gamma>\<^sub>1\<close>)
              subgoal premises P
                apply (auto simp: Inv_def R4 P intro!: inv_into_f_eq)                
                using P by blast
              subgoal premises P
                using P 
                by (metis I1.inv_morph_morph 
                      I1.pre_particular_struct_morphism_axioms 
                      I2_inv.I_img_eq_tgt_I 
                      I2_inv.inv_is_bijective_morphism I2_inv.inv_morph_morph 
                      I2_inv.phi_inv_scope 
                      particular_struct_bijection_def 
                      particular_struct_injection_def 
                      particular_struct_morphism_def 
                      pre_particular_struct_morphism.pre_particular_struct_morphism_eqI)
              done
            done

          show \<open>x \<in> w\<^sub>s \<longleftrightarrow> \<phi>\<^sub>1 x \<in> w\<^sub>t\<close>
            using as1 w1_c[OF as1,simplified] wt_c
            apply (auto simp add: R5)            
            subgoal using R3 that(3) by force
            by (metis I1.morph_preserves_particulars I2_inv.inv_morph_morph 
                  R1 R5 phi1.tgt.\<P>_I wt_W wt_c)
        qed
      next
        fix w\<^sub>t
        assume as: \<open>w\<^sub>t \<in> phi1.tgt.\<W>\<close>
        interpret I2_inv: particular_struct_bijection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<open>I2.inv_morph\<close> 
          by simp
        obtain w\<^sub>1 where w1: \<open>I2_inv.world_corresp w\<^sub>1 w\<^sub>t\<close>
          using I2_inv.morph_worlds_correspond_tgt_src as by metis
        then obtain w1_W: \<open>w\<^sub>1 \<in> I2_inv.src.\<W>\<close> and
              w1_c: \<open>\<And>x. x \<in> I2_inv.src.\<P> \<Longrightarrow> x \<in> w\<^sub>1 \<longleftrightarrow> I2.inv_morph x \<in> w\<^sub>t\<close>
          using  I2_inv.world_corresp_E[OF w1] by metis
        obtain w\<^sub>s where w\<^sub>s: \<open>phi_phi1.world_corresp w\<^sub>s w\<^sub>1\<close>
          using phi_phi1.morph_worlds_correspond_tgt_src[OF w1_W]
          by blast  
        then obtain w\<^sub>s_W: \<open>w\<^sub>s \<in> phi_phi1.src.\<W>\<close>
          and w\<^sub>s_c: \<open>\<And>x. x \<in> phi_phi1.src.\<P> \<Longrightarrow>
                x \<in> w\<^sub>s \<longleftrightarrow> (\<phi> \<circ>\<^bsub>phi_phi1.src.\<P>\<^esub> \<phi>\<^sub>1) x \<in> w\<^sub>1\<close>
          using phi_phi1.world_corresp_E by metis
        

        show \<open>\<exists>w\<^sub>s. phi1.world_corresp w\<^sub>s w\<^sub>t\<close>
        proof (intro exI[of _ w\<^sub>s] phi1.world_corresp_I as w\<^sub>s_W)
          fix x
          assume as1: \<open>x \<in> phi_phi1.src.\<P>\<close>
          then have R1: \<open>x \<in> w\<^sub>s \<longleftrightarrow> (\<phi> \<circ>\<^bsub>phi_phi1.src.\<P>\<^esub> \<phi>\<^sub>1) x \<in> w\<^sub>1\<close>
            using w\<^sub>s_c by metis
          then have R2: \<open>x \<in> w\<^sub>s \<longleftrightarrow> \<phi> (\<phi>\<^sub>1 x) \<in> w\<^sub>1\<close> 
            using as1 compose_eq by metis 
          have R3: \<open>\<phi> (\<phi>\<^sub>1 x) \<in> I2_inv.src.\<P>\<close> 
            using as1 by blast
          have R4: \<open>\<phi>\<^sub>1 x \<in> phi1.tgt.\<P>\<close>            
            using as1 by blast
          have R5: \<open>I2.inv_morph (\<phi> (\<phi>\<^sub>1 x)) = \<phi>\<^sub>1 x\<close>
            by (subst Inv_f_eq ; simp add: R4)
          
          show \<open>x \<in> w\<^sub>s \<longleftrightarrow>  \<phi>\<^sub>1 x \<in> w\<^sub>t\<close>
            using w1_c[of \<open>\<phi> (\<phi>\<^sub>1 x)\<close>,OF R3] R5 R2
            by simp                      
      qed
    qed         
    show ?thesis
      apply (unfold_locales)      
      using inj_on_map_comp_imageI2 by blast
  qed
  next
    assume \<open>\<Gamma> \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>1\<close>
    then interpret phi1: particular_struct_injection \<Gamma> \<Gamma>\<^sub>1 \<phi>\<^sub>1 .
    show \<open>\<phi>\<^sub>1 x \<in> I1.src.\<P>\<close> if as: \<open>x \<in> particulars \<Gamma>\<close> for x      
      using that by force      
    show \<open>\<phi>\<^sub>1 \<in> extensional (particulars \<Gamma>)\<close>
      apply (auto simp add: extensional_def)
      by (metis (mono_tags, lifting) extensional_def mem_Collect_eq 
          phi1.morphism_extensional)      
    show \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close>
      by (intro_locales)
  qed
qed



lemma \<^marker>\<open>tag (proof) aponly\<close> finite_card_sub_structure_by_lteq: 
  fixes \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and 
        \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close>
  assumes \<open>finite (particulars \<Gamma>\<^sub>2)\<close> \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close> 
  shows \<open>card (particulars \<Gamma>\<^sub>1) \<le> card (particulars \<Gamma>\<^sub>2)\<close>  
proof -
  interpret phi: particular_struct_injection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('q)\<close> 
    using assms by simp
  have A: \<open>finite (particulars \<Gamma>\<^sub>1)\<close>
    using finite_image_iff[OF phi.morph_is_injective,THEN iffD1,
          OF finite_subset,of \<open>particulars \<Gamma>\<^sub>2\<close>] assms(1) by blast
  show ?thesis
    using A assms(1) phi.morph_is_injective 
    by (metis card_image card_mono phi.morph_image_def phi.morph_scope)  
qed  

lemma \<^marker>\<open>tag (proof) aponly\<close> finite_card_substruct_lt: 
  fixes \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and 
        \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close>
  assumes \<open>finite (particulars \<Gamma>\<^sub>2)\<close> \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close> \<open>\<forall>\<phi>. \<not> \<Gamma>\<^sub>2 \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>1\<close>
  shows \<open>card (particulars \<Gamma>\<^sub>1) < card (particulars \<Gamma>\<^sub>2)\<close>  
proof -
  interpret phi: particular_struct_injection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('q)\<close> 
    using assms by simp
  have A: \<open>finite (particulars \<Gamma>\<^sub>1)\<close>
    using finite_image_iff[OF phi.morph_is_injective,THEN iffD1,
          OF finite_subset,of \<open>particulars \<Gamma>\<^sub>2\<close>] assms(1) by blast
  have B: \<open>card (particulars \<Gamma>\<^sub>1) \<le> card (particulars \<Gamma>\<^sub>2)\<close>
    using A assms(1) phi.morph_is_injective 
    by (metis card_image card_mono phi.morph_image_def phi.morph_scope)
  
  have C: \<open>card (particulars \<Gamma>\<^sub>1) \<noteq> card (particulars \<Gamma>\<^sub>2)\<close>
  proof
    assume AA: \<open>card (particulars \<Gamma>\<^sub>1) = card (particulars \<Gamma>\<^sub>2)\<close>
    then have \<open>bij_betw \<phi> (particulars \<Gamma>\<^sub>1) (particulars \<Gamma>\<^sub>2)\<close>
      using assms(1) A phi.morph_is_injective
      by (metis B card_image card_seteq phi.morph_bij_on_img phi.morph_image_def phi.morph_scope)
    then interpret phi: particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('q)\<close>
      apply unfold_locales      
      by (simp add: bij_betw_def)
    interpret phi_inv:  particular_struct_bijection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<open>phi.inv_morph\<close> \<open>TYPE('p\<^sub>2)\<close> \<open>TYPE('p\<^sub>1)\<close> \<open>TYPE('q)\<close>
      by simp
    show False using assms
      phi_inv.particular_struct_injection_axioms by simp
  qed
  then show ?thesis using B by auto
qed  

lemma \<^marker>\<open>tag (proof) aponly\<close> finite_card_sub_structure_by_finite:
  fixes \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and 
        \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close>
  assumes \<open>finite (particulars \<Gamma>\<^sub>2)\<close> \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close> 
  shows \<open>finite (particulars \<Gamma>\<^sub>1)\<close>
proof -
  interpret phi: particular_struct_injection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> using assms by simp
  show ?thesis
    using assms phi.morph_is_injective 
          finite_image_iff finite_subset phi.morph_scope 
    by fastforce
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_by_sub_structure_transf_inv:
  assumes \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close>
  shows \<open>\<Gamma> \<lless>\<^bsub>invMorph \<Gamma>\<^sub>1 \<phi> \<circ>\<^bsub>particulars \<Gamma>\<^esub> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>1 \<and> 
         \<phi>\<^sub>1 ` particulars \<Gamma> \<subseteq> particulars \<Gamma>\<^sub>2 \<and>
        \<phi>\<^sub>1 \<in> extensional (particulars \<Gamma>) \<longleftrightarrow>
         \<Gamma> \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close>
  using isomorphic_by_sub_structure_transf isomorphic_by_sym assms
  by metis
  

lemma \<^marker>\<open>tag (proof) aponly\<close> sub_structure_by_finite_weak_antisym[intro]:
  fixes \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
        \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close>
  assumes \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>2 \<lless>\<^bsub>\<phi>\<^sub>2\<^esub> \<Gamma>\<^sub>1\<close> \<open>finite (particulars \<Gamma>\<^sub>1)\<close>
  shows \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close>  
proof -
  interpret phi1: particular_struct_injection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1 using assms(1) .
  interpret phi2: particular_struct_injection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<phi>\<^sub>2 using assms(2) .
  have A: \<open>inj_on (\<phi>\<^sub>2 \<circ>\<^bsub>particulars \<Gamma>\<^sub>1\<^esub> \<phi>\<^sub>1) phi1.src.\<P>\<close>    
    by (metis inj_comp_map inj_on_subset 
        particular_struct_morphism_sig.morph_image_def phi1.morph_is_injective 
        phi1.morph_scope phi2.morph_is_injective)
  then have A1: \<open>inj_on \<phi>\<^sub>1 phi1.src.\<P>\<close> by blast    
  have A2: \<open>inj_on \<phi>\<^sub>2 (\<phi>\<^sub>1 ` phi1.src.\<P>)\<close>     
    using inj_on_subset phi1.morph_image_def phi1.morph_scope 
    by auto
  have B: \<open>f ` A = B\<close> if
      \<open>inj_on f A\<close> \<open>finite A\<close> \<open>f ` A \<subseteq> B\<close>
      \<open>inj_on g B\<close>  \<open>g ` B \<subseteq> A\<close>
    for A :: \<open>'p\<^sub>1 set\<close> and B :: \<open>'p\<^sub>2 set\<close> and f g
    using that
    by (metis card_bij_eq card_image card_subset_eq inj_on_finite)
  have bij: \<open>bij_betw \<phi>\<^sub>1 phi1.src.\<P> phi1.tgt.\<P>\<close>
    apply (simp add: bij_betw_def)
    apply (intro B[of _ _ _ \<phi>\<^sub>2] ; simp?)
    using assms(3) by blast+
  then show ?thesis
    apply (unfold_locales)    
    by (simp add: bij_betw_def)
qed

end