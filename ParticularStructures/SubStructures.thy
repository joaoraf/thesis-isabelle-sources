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
  shows \<open>\<Gamma> \<lless>\<^bsub>id\<^esub> \<Gamma>\<close>
proof -
  interpret particular_struct \<Gamma> using assms .
  show ?thesis
    by (metis \<Gamma>_simps particular_struct_eqI particular_struct_bijection_1_def 
          ufo_particular_theory.MorphImg_of_id 
          ufo_particular_theory.id_is_isomorphism ufo_particular_theory_axioms) 
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The sub-structure relation is transitive, through the composition of
  morphisms:
\<close>
lemma sub_structure_by_trans:
  assumes \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>2 \<lless>\<^bsub>\<phi>\<^sub>2\<^esub> \<Gamma>\<^sub>3\<close>
  shows \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>3\<close>
  by (intro particular_struct_injection_comp[OF assms])

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
  shows \<open>\<Gamma> \<sim>\<^bsub>id\<^esub> \<Gamma>\<close>
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
  shows \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>3\<close>
  using assms particular_struct_bijection_comp by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> isomorphic_by_sub_structure_transf[simp]:
  assumes \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^esub> \<Gamma>\<^sub>2\<close>
  shows \<open>\<Gamma> \<lless>\<^bsub>\<phi> \<circ> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2 \<and> \<phi>\<^sub>1 ` particulars \<Gamma> \<subseteq> particulars \<Gamma>\<^sub>1 \<longleftrightarrow> \<Gamma> \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>1\<close>
proof -
  interpret I1: particular_struct_bijection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi> using assms .
  interpret I2: particular_struct_bijection_1 \<Gamma>\<^sub>1 \<phi>  
    using assms particular_struct_bijection_iff_particular_struct_bijection_1 
    by blast  
  have A[simp]: \<open>\<Gamma>\<^sub>2 = MorphImg \<phi> \<Gamma>\<^sub>1\<close>
    by (simp add: I1.tgt_is_morph_img)
  
  show ?thesis
  proof (cases \<open>particular_struct \<Gamma> \<and> inj_on \<phi>\<^sub>1 (particulars \<Gamma>) \<and> \<Gamma> \<lless>\<^bsub>\<phi> \<circ> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2
                  \<and> \<phi>\<^sub>1 ` particulars \<Gamma> \<subseteq> particulars \<Gamma>\<^sub>1\<close>
          ; (elim conjE)?)
    case False
    note AA = this    
    then consider (C1) \<open>\<not> particular_struct \<Gamma>\<close> |
                  (C2) \<open>\<not> inj_on \<phi>\<^sub>1 (particulars \<Gamma>)\<close> |
                  (C3) \<open>\<not> \<Gamma> \<lless>\<^bsub>\<phi> \<circ> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close> |
                  (C4) \<open>\<Gamma> \<lless>\<^bsub>\<phi> \<circ> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close> \<open>\<not> \<phi>\<^sub>1 ` particulars \<Gamma> \<subseteq> particulars \<Gamma>\<^sub>1\<close>
      by metis
    then show ?thesis
    proof cases
      case C1
      then show ?thesis
      by (simp only: particular_struct_injection_def
            particular_struct_morphism_def
            pre_particular_struct_morphism_def ; simp)      
    next
      case C2
      then have B: \<open>\<not> inj_on (\<phi> \<circ> \<phi>\<^sub>1) (particulars \<Gamma>)\<close>      
        using inj_on_imageI2 by blast
      show ?thesis
        by (simp only: particular_struct_injection_def
                particular_struct_injection_axioms_def C2 B ; simp)
    next
      case C3
      then have B: \<open>\<not> \<Gamma> \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>1\<close>
        using I1.particular_struct_injection_axioms
            particular_struct_injection_comp by metis
      show ?thesis
        by (intro iffI conjI ; (elim conjE)? ; (simp only: C3 B)?)
    next
      case C4
      then  interpret phi_phi1: particular_struct_injection \<Gamma> \<Gamma>\<^sub>2 \<open>\<phi> \<circ> \<phi>\<^sub>1\<close> by simp
      have B: \<open>(\<exists>x. x \<in> phi_phi1.src.endurants \<and> \<phi>\<^sub>1 x \<notin> I1.src.endurants)\<close>
        using C4 by blast
      show ?thesis
        by (simp add: C4 particular_struct_injection_def
              particular_struct_morphism_def
              pre_particular_struct_morphism_def
              pre_particular_struct_morphism_axioms_def
              B) 
    qed
  next
    assume assms1: \<open>particular_struct \<Gamma>\<close> 
        \<open>inj_on \<phi>\<^sub>1 (particulars \<Gamma>)\<close> \<open>\<Gamma> \<lless>\<^bsub>\<phi> \<circ> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close>    
        \<open>\<phi>\<^sub>1 ` particulars \<Gamma> \<subseteq> particulars \<Gamma>\<^sub>1\<close>
    interpret gamma: particular_struct \<Gamma> using assms1(1) .
    interpret phi_phi1: particular_struct_injection \<Gamma> \<Gamma>\<^sub>2 \<open>\<phi> \<circ> \<phi>\<^sub>1\<close>
      using assms1(3) .

    have phi1_img[intro!]: \<open>\<phi>\<^sub>1 x \<in>  particulars \<Gamma>\<^sub>1 \<close> if \<open>x \<in> particulars \<Gamma>\<close> for x 
        using assms1(4) that  by blast      
  
    have B[simp]: \<open>\<phi> (\<phi>\<^sub>1 x) = \<phi> (\<phi>\<^sub>1 y) \<longleftrightarrow> x = y\<close> if \<open>x \<in> phi_phi1.src.\<P>\<close> \<open>y \<in> phi_phi1.src.\<P>\<close> for x y
      using phi_phi1.morph_is_injective[THEN inj_onD,OF _ that,simplified] by metis
    have C[simp]: \<open>\<phi>\<^sub>1 x = \<phi>\<^sub>1 y \<longleftrightarrow> x = y\<close> if \<open>x \<in> phi_phi1.src.\<P>\<close> \<open>y \<in> phi_phi1.src.\<P>\<close> for x y
      using assms1(2)[THEN inj_onD,OF _ that,simplified] by metis  
    have D[simp]: \<open>\<phi> x = \<phi> y \<longleftrightarrow> x = y\<close> if \<open>x \<in> \<phi>\<^sub>1 ` phi_phi1.src.\<P>\<close> \<open>y \<in> \<phi>\<^sub>1 ` phi_phi1.src.\<P>\<close> for x y
      using that apply (elim imageE ; hypsubst_thin)
      by simp
    note simps = B C D
    have E: \<open>\<phi>\<^sub>1 x = I2.inv_morph ((\<phi> \<circ> \<phi>\<^sub>1) x)\<close> if \<open>x \<in> phi_phi1.src.\<P>\<close> for x
      using that assms assms1 by auto

    { fix x y z q
      note phi_phi1.morph_reflects_inherence[of x y]  
           phi_phi1.morph_does_not_add_bearers[of x z]
           phi_phi1.morph_reflects_towardness[of x y]
           phi_phi1.morph_does_not_add_towards[of x z]
           phi_phi1.morph_reflects_quale_assoc[of x q] }
    note R1 = this
    { fix x y z q
      note I1.morph_reflects_inherence[of \<open>\<phi>\<^sub>1 x\<close> \<open>\<phi>\<^sub>1 y\<close>]  
           I1.morph_does_not_add_bearers[of \<open>\<phi>\<^sub>1 x\<close> z]
           I1.morph_reflects_towardness[of \<open>\<phi>\<^sub>1 x\<close> \<open>\<phi>\<^sub>1 y\<close>]
           I1.morph_does_not_add_towards[of \<open>\<phi>\<^sub>1 x\<close> z]
           I1.morph_reflects_quale_assoc[of \<open>\<phi>\<^sub>1 x\<close> q] }
    note R2 = this

    interpret phi1: pre_particular_struct_morphism \<Gamma> \<Gamma>\<^sub>1 \<phi>\<^sub>1
      apply (unfold_locales ; simp? ; (simp only: E)?)
      subgoal G1  using phi_phi1.quality_space_subset by auto
      subgoal G2  using assms1 by (simp ; blast)
      subgoal G3 for x y        
        using phi_phi1.morph_preserves_particulars phi_phi1.morph_reflects_inherence by auto          
      subgoal G4 for x z
        by (metis (no_types, lifting) E G2 I1.inv_morph_morph I1.morph_reflects_inherence I1.src.endurantI2 I1.src.moment_non_migration phi_phi1.morph_does_not_add_bearers phi_phi1.morph_preserves_particulars)
      subgoal G5 for x y
        using phi_phi1.morph_preserves_particulars phi_phi1.morph_reflects_towardness by auto
      subgoal G6 for x y
        by (metis E G2 I1.inv_morph_morph I1.morph_reflects_towardness 
              I1.src.towardness_scopeE I2.morph_is_injective 
              phi_phi1.morph_does_not_add_towards 
              phi_phi1.morph_preserves_particulars inj_onD)           
      subgoal for x q
        using G2 by auto
      done

    have phi1_w_c: \<open>phi1.world_corresp w w\<^sub>2 \<longleftrightarrow> phi_phi1.world_corresp w (\<phi> ` w\<^sub>2) \<and> w\<^sub>2 \<in> I1.src.\<W>\<close> for w w\<^sub>2
      apply (simp add: particular_struct_morphism_sig.world_corresp_def
          ; intro iffI conjI impI ballI ; (elim imageE conjE disjE exE)? ; simp?)
      subgoal G1 by blast
      subgoal G2 for x y by (metis I2.morph_is_injective inj_onD phi1.tgt.\<P>_I phi1_img)
      using I2.src_world_corresp_image by blast

    have R4: \<open>phi1.inv_morph ` (w\<^sub>1 \<inter> \<phi>\<^sub>1 ` phi_phi1.src.\<P>) \<in> phi_phi1.src.\<W>\<close>
      if as: \<open>w\<^sub>1 \<in> phi1.tgt.\<W>\<close> for w\<^sub>1
    proof -
      obtain w\<^sub>2 where AA: \<open>I1.world_corresp w\<^sub>1 w\<^sub>2\<close> 
        using as I1.morph_worlds_correspond_src_tgt by metis
      obtain BB: \<open>w\<^sub>2 \<in> I1.tgt.\<W>\<close>
                 \<open>\<And>x. x \<in> phi1.tgt.\<P> \<Longrightarrow> x \<in> w\<^sub>1 \<longleftrightarrow> \<phi> x \<in> w\<^sub>2\<close>
        using I1.world_corresp_E AA by metis
      obtain w\<^sub>3 where CC: \<open>phi_phi1.world_corresp w\<^sub>3 w\<^sub>2\<close>
        using BB phi_phi1.morph_worlds_correspond_tgt_src by metis
      obtain DD: \<open>w\<^sub>3 \<in> phi_phi1.src.\<W>\<close>
          \<open>\<And>x. x \<in> phi_phi1.src.\<P> \<Longrightarrow> x \<in> w\<^sub>3 \<longleftrightarrow>\<phi> (\<phi>\<^sub>1 x) \<in> w\<^sub>2\<close>
        using phi_phi1.world_corresp_E[OF CC] comp_apply by metis
      { fix x
        assume \<open>x \<in> w\<^sub>3\<close>
        then have EE: \<open>x \<in> phi_phi1.src.\<P>\<close> using DD(1) by blast
        then have FF: \<open>\<phi> (\<phi>\<^sub>1 x) \<in> w\<^sub>2 \<longleftrightarrow> x \<in> w\<^sub>3\<close> using DD(2) by simp
        have \<open>\<phi>\<^sub>1 x \<in> phi1.tgt.\<P>\<close> using EE by blast
        then have \<open>\<phi>\<^sub>1 x \<in> w\<^sub>1 \<longleftrightarrow> x \<in> w\<^sub>3\<close> using BB(2) FF by metis }
      note simp1[simp] = this

      { fix x
        assume EE: \<open>x \<in> phi_phi1.src.\<P>\<close> 
        then have FF: \<open>\<phi> (\<phi>\<^sub>1 x) \<in> w\<^sub>2 \<longleftrightarrow> x \<in> w\<^sub>3\<close> using DD(2) by simp
        have \<open>\<phi>\<^sub>1 x \<in> phi1.tgt.\<P>\<close> using EE by blast
        then have \<open>\<phi>\<^sub>1 x \<in> w\<^sub>1 \<longleftrightarrow> x \<in> w\<^sub>3\<close> using BB(2) FF by metis }
      note simp2[simp] = this
  
      have GG: \<open>\<phi>\<^sub>1 ` w\<^sub>3 = w\<^sub>1 \<inter> \<phi>\<^sub>1 ` phi_phi1.src.\<P>\<close>
        apply (auto  ; (intro imageI)? ; simp?)
        using DD(1) by blast
      have HH: \<open>phi1.inv_morph (\<phi>\<^sub>1 x) = x\<close> if \<open>x \<in> phi_phi1.src.\<P>\<close> for x        
        by (simp add: assms1(2) phi1.inv_morph_def that)
      have II: \<open>phi1.inv_morph ` \<phi>\<^sub>1 ` w\<^sub>3 = w\<^sub>3\<close>
        supply T = subsetD[OF phi_phi1.src.worlds_are_made_of_particulars,OF DD(1)]
        using T by (auto simp: image_iff HH)
      show ?thesis
        by (simp add: GG[symmetric] II DD(1))
    qed

    have ex_ex_1: \<open>(\<exists>y\<^sub>1\<in>w\<^sub>s. phi1.src_inheres_in y\<^sub>1 x \<and> \<phi> y = (\<phi> \<circ> \<phi>\<^sub>1) y\<^sub>1)
        \<longleftrightarrow>
          (\<exists>y\<^sub>1\<in>w\<^sub>s. phi1.src_inheres_in y\<^sub>1 x \<and> y = \<phi>\<^sub>1 y\<^sub>1)\<close>
      if \<open>y \<in> w\<^sub>t\<close> \<open>w\<^sub>t \<in> phi1.tgt.\<W>\<close> for y w\<^sub>t w\<^sub>s x
    proof -
      have AA[intro!,simp]: \<open>y \<in> phi1.tgt.\<P>\<close> using that by blast
      
      show ?thesis
        apply (intro iffI ; elim bexE conjE)
        subgoal for y\<^sub>1
          apply (intro bexI[of _ y\<^sub>1] conjI)
          subgoal using that AA by simp
          subgoal using that AA 
            apply simp
            by (meson AA I2.morph_is_injective inj_onD phi1_img phi_phi1.src.inherence_scope)
          subgoal using that AA by simp            
          done
        subgoal for y\<^sub>1
          by (intro bexI[of _ y\<^sub>1] conjI ; simp add: that)
        done
    qed
    

    interpret phi1: particular_struct_morphism \<Gamma> \<Gamma>\<^sub>1 \<phi>\<^sub>1
      apply (unfold_locales ; simp only: phi1_w_c simp_thms)
      subgoal G1 premises P for w\<^sub>1
        using phi_phi1.morph_worlds_correspond_src_tgt[OF P]
        apply (elim exE)
        subgoal premises Q for w\<^sub>2
          apply (rule phi_phi1.world_corresp_E[OF Q])
          subgoal premises T            
            apply (intro exI[of _ \<open>I1.inv_morph ` w\<^sub>2\<close>] conjI)
            subgoal using Q T(2) by simp
            using T(2) by (simp add: I1.world_preserve_inv_img1) 
          done
        done 
      subgoal G2 premises P for w\<^sub>1
        apply (intro exI[of _ \<open>phi1.inv_morph ` (w\<^sub>1 \<inter> \<phi>\<^sub>1 ` phi_phi1.src.\<P>)\<close>] conjI)        
        apply (intro phi1_w_c[THEN iffD1,THEN conjunct1]
                phi1.world_corresp_I P iffI ; simp)
        using P apply auto
        subgoal G2_1 using R4 by blast
        subgoal G2_2 by (simp add: assms1(2) phi1.inv_morph_def)          
        by (metis IntI assms1(2) image_iff inv_into_f_f phi1.inv_morph_def)        
      done

    interpret phi1: particular_struct_injection \<Gamma> \<Gamma>\<^sub>1 \<phi>\<^sub>1
      using assms1(2) by unfold_locales

    show ?thesis
      apply (intro conjI iffI ; (elim conjE)?)
      subgoal using phi1.particular_struct_injection_axioms by blast
      subgoal using phi_phi1.particular_struct_injection_axioms by blast
      by blast
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
  shows \<open>\<Gamma> \<lless>\<^bsub>invMorph \<Gamma>\<^sub>1 \<phi> \<circ> \<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>1 \<and> \<phi>\<^sub>1 ` particulars \<Gamma> \<subseteq> particulars \<Gamma>\<^sub>2 \<longleftrightarrow>
         \<Gamma> \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close>
  using isomorphic_by_sub_structure_transf[OF isomorphic_by_sym] assms by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> sub_structure_by_finite_weak_antisym[intro]:
  fixes \<Gamma>\<^sub>1 :: \<open>('p\<^sub>1,'q) particular_struct\<close> and
        \<Gamma>\<^sub>2 :: \<open>('p\<^sub>2,'q) particular_struct\<close>
  assumes \<open>\<Gamma>\<^sub>1 \<lless>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close> \<open>\<Gamma>\<^sub>2 \<lless>\<^bsub>\<phi>\<^sub>2\<^esub> \<Gamma>\<^sub>1\<close> \<open>finite (particulars \<Gamma>\<^sub>1)\<close>
  shows \<open>\<Gamma>\<^sub>1 \<sim>\<^bsub>\<phi>\<^sub>1\<^esub> \<Gamma>\<^sub>2\<close>  
proof -
  interpret phi1: particular_struct_injection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<phi>\<^sub>1 using assms(1) .
  interpret phi2: particular_struct_injection \<Gamma>\<^sub>2 \<Gamma>\<^sub>1 \<phi>\<^sub>2 using assms(2) .
  have A: \<open>inj_on (\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1) phi1.src.\<P>\<close>
    using comp_inj_on phi1.morph_is_injective phi2.morph_is_injective
      phi1.morph_scope 
    by (metis phi1.morph_image_def subset_inj_on)
  then have A1: \<open>inj_on \<phi>\<^sub>1 phi1.src.\<P>\<close> by blast    
  have A2: \<open>inj_on \<phi>\<^sub>2 (\<phi>\<^sub>1 ` phi1.src.\<P>)\<close> 
    using A A1 inj_on_imageI by blast
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