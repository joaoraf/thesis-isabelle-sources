section \<open>Instantiation in Finite Particular Structures\<close>

theory FiniteInstantiation
  imports FiniteParticularStructure Instantiation Trimming
begin

locale finite_instantiation =
  finite_particulars_with_individuality where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q +
  iso_universals where Typ\<^sub>p = Typ\<^sub>p and Typ\<^sub>q = Typ\<^sub>q and Typ\<^sub>u = Typ\<^sub>u 
  for
    Typ\<^sub>p :: \<open>'p itself\<close> and
    Typ\<^sub>q :: \<open>'q itself\<close> and
    Typ\<^sub>u :: \<open>'u itself\<close> 
begin

context
  fixes \<phi>
  assumes phi: \<open>\<phi> \<in> EndoMorphs\<^bsub>\<Gamma>\<^esub>\<close>
begin

private lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_perm: \<open>\<phi> \<in> Perms\<^bsub>\<Gamma>\<^esub>\<close> 
  using phi all_endomorphisms_are_perms by blast

interpretation phi: particular_struct_permutation \<Gamma> \<phi>
  using phi_perm by blast

interpretation phi_iso: particular_struct_bijection_1 \<Gamma> \<phi>
  by blast

lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_detailingMoments_invariant[simp]: \<open>\<phi> ` \<Delta>\<^bsub>U\<^esub> = \<Delta>\<^bsub>U\<^esub>\<close> 
  using detailingMoments_invariant[
      OF phi_iso.particular_struct_bijection_1_axioms,of U,simplified] 
  by metis

lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_particulars_img[simp]: \<open>\<phi> ` \<P> = \<P>\<close>  
  using phi.morph_is_surjective by auto


lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_detailingMoment_complement_invariant[simp]: \<open>\<phi> ` (\<P> - \<Delta>\<^bsub>U\<^esub>) = \<P> - \<Delta>\<^bsub>U\<^esub>\<close>
  apply (rule inj_on_image_set_diff[OF phi.morph_is_injective,simplified
        ,of \<P> \<open>\<Delta>\<^bsub>U\<^esub>\<close>,simplified])  
  by (metis detailingMoments.cases endurantI1 
      subsetI trans_inheres_in_scope 
      all_ufo_particular_theory_axioms(4))

context
  fixes U :: 'u                  
begin

interpretation sigma: particular_struct_injection \<open>trim U\<close> \<Gamma> id
  by blast

interpretation phi_proj: particular_struct_bijection_1 \<open>trim U\<close> \<phi> 
proof -
  have A: \<open>sigma.src.\<Gamma> = trim U\<close> by auto
  show \<open>particular_struct_bijection_1 (trim U) \<phi>\<close>
    apply (intro sigma.src.inj_morph_img_isomorphism[simplified A])    
    subgoal 
      apply (intro inj_on_subset[OF phi.morph_is_injective])
      by auto
    using sigma.tgt.injection_to_ZF_exist by blast
qed

lemma  \<^marker>\<open>tag (proof) aponly\<close> proj_phi_img[simp]: \<open>MorphImg \<phi> (trim U) = trim U\<close>
  apply (intro particular_struct_eqI ext
      ; simp add: trim_simps trim_worlds_def trim_inheres_in_def 
          trim_assoc_quale_def trim_towards_def
          particular_struct_morphism_image_simps
          ; (intro set_eqI iffI conjI CollectI)?
          ; (elim conjE exE CollectE)?
          ; hypsubst_thin? ; simp?)
  
  subgoal G1 premises P for w
    using phi.morph_worlds_correspond_src_tgt[simplified,OF P] 
    apply (elim exE phi.world_corresp_E ; simp)
    subgoal premises Q for w\<^sub>1
      supply R1 =  Q(1,2,3) Q(1,2)[THEN worlds_are_made_of_particulars,THEN subsetD]
      supply R2 = R1(4,5)[THEN Q(3)]
      apply (intro exI[of _ w\<^sub>1] conjI Q set_eqI iffI DiffI
            ; (elim imageE ; simp ; elim conjE)? ; (elim DiffE)?)
      subgoal G1_1 for x x\<^sub>1
        using R1 R2 
        by blast
      subgoal G1_2 for x x\<^sub>1        
        using R1(4) phi_detailingMoment_complement_invariant by blast
      subgoal G1_3 for x 
        apply (subst inj_on_image_set_diff[of \<phi> \<P> w \<open>\<Delta>\<^bsub>U\<^esub>\<close>] 
              ; (intro DiffI)? ; simp?)
        subgoal using phi_iso.morph_is_injective by auto
        subgoal using P by blast
        subgoal 
          by (metis inherence_scope inherence_sig.\<M>_E
                instantiation_sig.detailingMoments.cases subsetI
                trans_inheres_in_scope)
        subgoal 
          by (metis (mono_tags, lifting) R1(3) R1(5) 
              image_iff phi_particulars_img)
        done
      done
    done
  subgoal G2 premises P for w    
    using phi.morph_worlds_correspond_tgt_src[simplified,OF P] 
    apply (elim exE phi.world_corresp_E ; simp)
    subgoal premises Q for w\<^sub>1      
      supply R1 = Q(1,2,3) 
                  Q(1,2)[THEN worlds_are_made_of_particulars,THEN subsetD]
      supply R2 = R1(4,5)[THEN Q(3)]      
      apply (rule exI[of _ \<open>w\<^sub>1 - \<Delta>\<^bsub>U\<^esub>\<close>] ; intro conjI Q set_eqI iffI DiffI
            ; (elim imageE ; simp ; elim conjE)? ; (elim DiffE imageE ; simp?)?)
      subgoal G1_1 for x
        apply (subst  inj_on_image_set_diff[of \<phi> \<P> w\<^sub>1 \<open>\<Delta>\<^bsub>U\<^esub>\<close>] 
              ; (intro DiffI)? ; simp?)
        subgoal using phi_iso.morph_is_injective by auto
        subgoal using R1(4) by auto
        subgoal 
          by (metis inherence_scope inherence_sig.\<M>_E
                instantiation_sig.detailingMoments.cases 
                subsetI trans_inheres_in_scope)
        by (metis (mono_tags, lifting) R1(3) R1(5) image_iff phi_particulars_img)        
      subgoal G1_2 for x x\<^sub>1 using R2(1) by blast 
      subgoal G1_3 for x y 
        using R1(4) phi_detailingMoment_complement_invariant by blast
      by (intro exI[of _ w\<^sub>1] conjI R1 ; simp )      
    done
  subgoal G3 for x y
    using phi.morph_reflects_inherence[simplified,of x y] inherence_scope[of x y] by metis    
  subgoal G4 using phi_detailingMoment_complement_invariant by blast
  subgoal G5 by (metis G3 G4 instantiation_sig.detailingMoments.intros(2)
                 tranclp.r_into_trancl)
  subgoal G6 for x y
    apply (rule exI[of _ \<open>phi.inv_morph x\<close>] ; rule exI[of _ \<open>phi.inv_morph y\<close>] 
            ; frule inherence_scope ; intro conjI ; (elim conjE)? ; simp?)
    subgoal G6_1 using phi.inv_inheres_in_reflects_on_image by auto
    subgoal G6_2 
      by (metis \<Gamma>_simps(2) image_eqI phi.inv_morph_morph
                phi_detailingMoments_invariant)
    subgoal G6_3 
      by (metis \<Gamma>_simps(2) image_eqI phi.inv_morph_morph 
                phi_detailingMoments_invariant)
    done
  subgoal G7 for x y
    apply (rule phi.morph_reflects_quale_assoc[simplified,THEN iffD1] ; simp?)    
    by (simp add: assoc_quale_scopeD(1))    
  subgoal G8 
    by (metis G4 assoc_quale_scopeD(3) inherence_sig.\<M>_E
        instantiation_sig.detailingMoments.sub_moments 
        tranclp.r_into_trancl)
  subgoal G9 for x q
    apply (rule exI[of _ \<open>phi.inv_morph x\<close>]  
            ; frule assoc_quale_scopeD ; intro conjI ; (elim conjE)? ; simp?)
    subgoal 
      by (smt \<Gamma>_simps(2) imageE particular_struct_endomorphism_def
          particular_struct_injection.inv_morph_morph
          particular_struct_morphism_def
          pre_particular_struct_morphism.morph_reflects_quale_assoc
          phi.particular_struct_endomorphism_axioms
          phi.particular_struct_injection_axioms
          phi_particulars_img ufo_particular_theory_sig.\<Gamma>_simps(4))    
    by (metis \<Gamma>_simps(2) image_eqI phi.inv_morph_morph phi_detailingMoments_invariant)      
  subgoal G10 for x y 
    by (rule phi.morph_reflects_towardness[simplified,THEN iffD2] ; simp?
            ; frule towardness_scopeD ; simp? ; auto)    
  subgoal G11 
    by (meson G4 \<M>_E detailingMoments.sub_moments towardness_apply_to_moments
          tranclp.r_into_trancl)
  subgoal G12 using phi_detailingMoment_complement_invariant by blast
  subgoal G13 for x y
    apply (rule exI[of _ \<open>phi.inv_morph x\<close>] ; rule exI[of _ \<open>phi.inv_morph y\<close>] 
            ; frule towardness_scopeD ; intro conjI ; (elim conjE)? ; simp?)
    subgoal 
      by (metis \<Gamma>_simps(2) phi.inv_towardness_reflects towardness_scopeD(2)
                towardness_scopeD(3) ufo_particular_theory_sig.\<Gamma>_simps(5))
    subgoal 
      by (metis (mono_tags, hide_lams) \<Gamma>_simps(2) image_eqI phi.inv_morph_morph
          phi_detailingMoments_invariant towardness.towardness_scopeE
          towardness_axioms)
    subgoal 
      by (metis (full_types) \<Gamma>_simps(2) image_eqI phi.inv_morph_morph  
            phi_detailingMoments_invariant towardness.towardness_scopeE
            towardness_axioms)
    subgoal by (simp add: endurantI1)    
    by (simp add: towardness_scopeD(3)) 
  done

lemma  \<^marker>\<open>tag (proof) aponly\<close> phi_in_trim_perm: \<open>\<phi> \<in> Perms\<^bsub>trim U\<^esub>\<close>
  apply (intro permutations_I)
  using phi_proj.particular_struct_bijection_axioms[
            simplified, simplified proj_phi_img]
  by (simp add: 
        particular_struct_endomorphism.intro 
        particular_struct_bijection_def
        particular_struct_injection_def 
        particular_struct_permutation.intro 
        sigma.src.particular_struct_axioms)

end

end

end

end
